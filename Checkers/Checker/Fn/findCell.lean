/-
Port of `new/checker/fn/findCell.v`.

`checker.findCell` (checker/match.go): the index of the first not-yet-used
heap cell whose location term is syntactically the given term.

Lean notes:
* Rocq's `u !!! i` (total lookup, default `false`) is `u.getD i false`.
* The pure mirror and its lemmas are outside the proof section.
* The Go function's own counter `i` and the range loop's index are both
  called `i`. Unlike Rocq, Lean's `wp_auto` does not fail: it allocates both,
  and the Go counter's `Loc`/Iris hypothesis become inaccessible
  (`i_ptr✝`, `i✝`); the proof names them with `rename_i gi_ptr` and
  `irename: gi_ptr ↦ _ => gi`.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Fn.termEq

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- Mirrors `findCell`: the first index `i` at which the cell is unused and
its location term is `y`, counting from `i`. -/
def find_cell : List scell → List Bool → term → Nat → Option Nat
  | [], _, _, _ => none
  | c :: cs', u, y, i =>
      if (!(u.getD i false) && decide (cloc c = y)) then some i
      else find_cell cs' u y (i + 1)

/-- What a caller gets out of the mirror: the answer is in range, and names a
free cell whose location term really is `y`. -/
theorem find_cell_lt (cs : List scell) :
    ∀ (u : List Bool) (y : term) (i j : Nat),
      find_cell cs u y i = some j → i ≤ j ∧ j < i + cs.length := by
  induction cs with
  | nil => intro u y i j Hf; simp [find_cell] at Hf
  | cons ce cs' IH =>
    intro u y i j Hf
    simp only [find_cell] at Hf
    split at Hf
    · cases Hf; simp
    · have := IH u y (i + 1) j Hf; simp only [List.length_cons]; omega

theorem find_cell_Some (cs : List scell) :
    ∀ (u : List Bool) (y : term) (i j : Nat),
      find_cell cs u y i = some j →
      ∃ sc, cs[j - i]? = some sc ∧ u.getD j false = false ∧ cloc sc = y := by
  induction cs with
  | nil => intro u y i j Hf; simp [find_cell] at Hf
  | cons ce cs' IH =>
    intro u y i j Hf
    simp only [find_cell] at Hf
    split at Hf
    · rename_i Ht
      cases Hf
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at Ht
      exact ⟨ce, by simp, Ht.1, Ht.2⟩
    · obtain ⟨sc, Hsc, Hu, Hc⟩ := IH u y (i + 1) j Hf
      have Hlt := find_cell_lt cs' u y (i + 1) j Hf
      refine ⟨sc, ?_, Hu, Hc⟩
      rw [show j - i = (j - (i + 1)) + 1 by omega]
      simpa using Hsc

theorem decide_Some (a b : term) : decide (some a = some b) = decide (a = b) := by
  simp

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_findCell (sh su : GoSlice) (cs : List scell) (u : List Bool) (ly : Loc) (y : term) :
    cs.length ≤ u.length →
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_heap sh cs ∗ su ↦* u ∗ is_term ly y }}
      (App (App (App (Val (@! checker.findCell)) (Val #sh)) (Val #su)) (Val #ly))
    {{ (idx : w64) (ok : Bool), RET (PairV #idx #ok);
        is_heap sh cs ∗ su ↦* u ∗
        ⌜ok = decide (find_cell cs u y 0 ≠ none)⌝ ∗
        ⌜∀ j, find_cell cs u y 0 = some j → uint.nat idx = j⌝ }} := by
  intro Hlen
  wp_start as ⟨Hheap, Hu, #Hy⟩
  unfold is_heap
  icases Hheap with ⟨%xs, Hsh, #Hcells⟩
  ihave %Hxlen := BigSepL2.bigSepL2_length $$ Hcells
  ihave %Hlh := ownSlice_len _ _ _ $$ Hsh
  ihave %Hlu := ownSlice_len _ _ _ $$ Hu
  wp_auto
  rename_i gi_ptr
  irename: gi_ptr ↦ (W64 0) => gi
  ihave HI : (∃ (n : w64) (cur : checker.Cell),
      "i" ∷ i_ptr ↦ n ∗ "gi" ∷ gi_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cur ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ cs.length⌝ ∗
      "%Hinv" ∷ ⌜find_cell cs u y 0 = find_cell (cs.drop (sint.nat n)) u y (sint.nat n)⌝ :
        IProp GF) $$ [i gi c]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hn.1, Hif⟩]
    list_elem xs (sint.nat n) as xc
    list_elem cs (sint.nat n) as sc
    ihave #Hcell := BigSepL2.bigSepL2_lookup (Φ := fun _ c sc => is_cell (GF := GF) c sc)
      Hxc_lookup Hsc_lookup $$ Hcells
    wp_apply wp_load_slice_index sh (sint.Z n) xs _ xc Hn.1 $$ [Hsh] with Hsh
    · iframe Hsh; ipureintro; exact Hxc_lookup
    have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z su.len := by
      refine ⟨Hn.1, ?_⟩
      have : sint.nat n < u.length := by
        have := (List.getElem?_eq_some_iff.mp Hsc_lookup).1; omega
      word
    rw [ite_eq_left Hb2]
    list_elem u (sint.nat n) as ub
    wp_apply wp_load_slice_index su (sint.Z n) u _ ub Hn.1 $$ [Hu] with Hu
    · iframe Hu; ipureintro; exact Hub_lookup
    have Hut : u.getD (sint.nat n) false = ub := by simp [List.getD_eq_getElem?_getD, Hub_lookup]
    have Hstep : find_cell (List.drop (sint.nat n) cs) u y (sint.nat n) =
        if (!ub && decide (cloc sc = y)) then some (sint.nat n)
        else find_cell (List.drop (sint.nat (n + W64 1)) cs) u y (sint.nat (n + W64 1)) := by
      have Hlt : sint.nat n < cs.length := (List.getElem?_eq_some_iff.mp Hsc_lookup).1
      rw [List.drop_eq_getElem_cons Hlt, find_cell, Hut,
        show sint.nat (n + W64 1) = sint.nat n + 1 by word]
      have : cs[sint.nat n] = sc := (List.getElem?_eq_some_iff.mp Hsc_lookup).2
      rw [this]
    cases ub
    · -- the cell is free: compare its location with `y`
      unfold is_cell
      icases Hcell with ⟨#Hloc, #Hval⟩
      wp_auto
      wp_apply wp_termEq xc.Loc' ly (some (cloc sc)) (some y) $$ []
      · rw [is_oterm_some, is_oterm_some]; iframe #
      rw [decide_Some]
      by_cases Heq : cloc sc = y
      · rw [decide_eq_true Heq]
        wp_auto
        wp_for_post
        have Hfound : find_cell cs u y 0 = some (sint.nat n) := by
          rw [Hinv, Hstep]; simp [Heq]
        iapply HΦ
        isplitl [Hsh]
        · iexists xs; iframe Hsh Hcells
        iframe Hu
        ipureintro
        rw [Hfound]
        refine ⟨by simp, ?_⟩
        intro j Hj; cases Hj; word
      · rw [decide_eq_false Heq]
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, xc
        iframe
        ipureintro
        refine ⟨by word, ?_⟩
        rw [Hinv, Hstep]; simp [Heq]
    · -- the cell is already claimed by an earlier atom
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, xc
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [Hinv, Hstep]; simp
  · -- the range is exhausted
    have Hdrop : List.drop (sint.nat n) cs = [] := List.drop_eq_nil_of_le (by word)
    rw [Hdrop, find_cell] at Hinv
    iapply HΦ
    isplitl [Hsh]
    · iexists xs; iframe Hsh Hcells
    iframe Hu
    ipureintro
    rw [Hinv]
    exact ⟨by simp, fun j Hj => by cases Hj⟩

end proof

end Checker
end Perennial
