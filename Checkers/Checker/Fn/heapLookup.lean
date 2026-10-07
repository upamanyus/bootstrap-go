/-
Port of `new/checker/fn/heapLookup.v`.

`checker.heapLookup` (checker/exec.go): the value stored at a location
term, found by a linear scan of the symbolic heap.

Lean notes:
* The pure mirror `heap_lookup` and its lemmas are stated before the proof
  section, so that `ExecSpec` (pure reasoning about the heap) needs no
  ghost-state variables to use them.
* Rocq's naming trap (no Rocq variable called `h`, `l` or `c`) does not
  exist in Lean; the names are kept for comparability.
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

/-- The Lean mirror: the first cell whose location term is syntactically
`x`. -/
def heap_lookup : List scell → term → Option term
  | [], _ => none
  | c :: H', x => if cloc c = x then some (cval c) else heap_lookup H' x

theorem heap_lookup_app (H1 H2 : List scell) (x : term) :
    heap_lookup (H1 ++ H2) x =
      match heap_lookup H1 x with | some t => some t | none => heap_lookup H2 x := by
  induction H1 with
  | nil => rfl
  | cons c H1 ih =>
    simp only [List.cons_append, heap_lookup]
    split <;> simp_all

/-- What the loop learns when it reaches a matching cell. -/
theorem heap_lookup_hit (H : List scell) (n : Nat) (sc : scell) (x : term) :
    H[n]? = some sc →
    heap_lookup (H.take n) x = none →
    cloc sc = x →
    heap_lookup H x = some (cval sc) := by
  intro Hn Hmiss Hloc
  have Hlt : n < H.length := (List.getElem?_eq_some_iff.mp Hn).1
  rw [← List.take_append_drop n H, heap_lookup_app, Hmiss,
    List.drop_eq_getElem_cons Hlt]
  have : H[n] = sc := (List.getElem?_eq_some_iff.mp Hn).2
  simp [heap_lookup, this, Hloc]

/-- ... and when it passes a non-matching one. -/
theorem heap_lookup_step (H : List scell) (n : Nat) (sc : scell) (x : term) :
    H[n]? = some sc →
    heap_lookup (H.take n) x = none →
    cloc sc ≠ x →
    heap_lookup (H.take (n + 1)) x = none := by
  intro Hn Hmiss Hloc
  rw [List.take_add_one, Hn, heap_lookup_app, Hmiss]
  simp [heap_lookup, Hloc]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_heapLookup (s : GoSlice) (H : List scell) (lx : Loc) (x : term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_heap s H ∗ is_term lx x }}
      (App (App (Val (@! checker.heapLookup)) (Val #s)) (Val #lx))
    {{ (lv : Loc) (ok : Bool), RET (PairV #lv #ok);
        is_heap s H ∗ ⌜ok = decide (heap_lookup H x ≠ none)⌝ ∗
        is_oterm lv (heap_lookup H x) }} := by
  wp_start as ⟨Hheap, #Hx⟩
  unfold is_heap
  icases Hheap with ⟨%cs, Hs, #Hcs⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hcs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave HI : (∃ (n : w64) (cur : checker.Cell),
      "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cur ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ cs.length⌝ ∗
      "%Hmiss" ∷ ⌜heap_lookup (H.take (sint.nat n)) x = none⌝ : IProp GF) $$ [i c]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hn.1, Hif⟩]
    list_elem cs (sint.nat n) as cur'
    list_elem H (sint.nat n) as sc
    ihave #Hcell := BigSepL2.bigSepL2_lookup (Φ := fun _ c sc => is_cell (GF := GF) c sc)
      Hcur'_lookup Hsc_lookup $$ Hcs
    unfold is_cell
    icases Hcell with ⟨#Hloc, #Hval⟩
    wp_apply wp_load_slice_index s (sint.Z n) cs _ cur' Hn.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Hcur'_lookup
    wp_apply wp_termEq cur'.Loc' lx (some (cloc sc)) (some x) $$ []
    · rw [is_oterm_some, is_oterm_some]; iframe #
    wp_if_destruct
    · -- this cell is the one
      wp_for_post
      have Hhit : heap_lookup H x = some (cval sc) :=
        heap_lookup_hit H _ sc x Hsc_lookup Hmiss (by simpa using Hif)
      iapply HΦ
      rw [Hhit, is_oterm_some]
      iframe Hval
      isplitl [Hs]
      · iexists cs; iframe Hs Hcs
      · ipureintro; simp
    · -- keep scanning
      wp_for_post
      iframe
      iexists n + W64 1, cur'
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
      exact heap_lookup_step H _ sc x Hsc_lookup Hmiss (by simpa using Hif)
  · -- the scan reached the end of the heap
    have Htake : H.take (sint.nat n) = H := List.take_of_length_le (by word)
    rw [Htake] at Hmiss
    iapply HΦ
    rw [Hmiss, is_oterm_none]
    isplitl [Hs]
    · iexists cs; iframe Hs Hcs
    · ipureintro; simp

end proof

end Checker
end Perennial
