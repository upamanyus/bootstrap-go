/-
Port of `new/checker/fn/heapUpdate.v`.

`checker.heapUpdate` (checker/exec.go): a fresh symbolic heap in which the
*first* cell at a location term holds a new value, or failure if the
location is not owned.

Lean notes:
* The pure mirror and its lemmas are stated before the proof section (used
  by `ExecSpec` without the ghost-state variables).
* Rocq needed a separate `wp_heapUpdate_aux` because of its naming trap
  (Go locals `v`, `l`, … clash with Rocq variables under `wp_auto`); Lean has
  no such trap, so `wp_heapUpdate` is proved directly.
* Rocq's `insert0_singleton` (normalising the shape `wp_slice_literal` gave
  in Rocq) is not needed: the Lean `wp_slice_literal` hands back the list
  as given.
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

-- `heap_update`: in LCheck/Fns.lean.

/-- What the loop has built after scanning a prefix: the updated prefix if
the prefix already contained the location, and the prefix itself
otherwise. -/
def heap_updated (H : List scell) (x v : term) : List scell :=
  (heap_update H x v).getD H

theorem heap_update_app_some (H1 H2 : List scell) (x v : term) (P : List scell) :
    heap_update H1 x v = some P → heap_update (H1 ++ H2) x v = some (P ++ H2) := by
  induction H1 generalizing P with
  | nil => intro h; cases h
  | cons c H1 ih =>
    simp only [heap_update, List.cons_append]
    split
    · intro h; cases h; rfl
    · cases Heq : heap_update H1 x v with
      | none => intro h; cases h
      | some P' =>
        intro h; cases h
        simp [ih P' Heq]

theorem heap_update_app_none (H1 H2 : List scell) (x v : term) :
    heap_update H1 x v = none →
    heap_update (H1 ++ H2) x v = (heap_update H2 x v).map (fun r => H1 ++ r) := by
  induction H1 with
  | nil => intro _; simp only [List.nil_append]; cases heap_update H2 x v <;> rfl
  | cons c H1 ih =>
    simp only [heap_update, List.cons_append]
    split
    · intro h; cases h
    · cases Heq : heap_update H1 x v with
      | some _ => intro h; cases h
      | none =>
        intro _
        rw [ih Heq]
        cases heap_update H2 x v <;> rfl

/-- The three ways one more cell can extend the prefix. -/
theorem heap_update_snoc_found (H1 : List scell) (sc : scell) (x v : term) (P : List scell) :
    heap_update H1 x v = some P →
    heap_update (H1 ++ [sc]) x v = some (P ++ [sc]) :=
  heap_update_app_some H1 [sc] x v P

theorem heap_update_snoc_hit (H1 : List scell) (sc : scell) (x v : term) :
    heap_update H1 x v = none → cloc sc = x →
    heap_update (H1 ++ [sc]) x v = some (H1 ++ [mkCell (cloc sc) v]) := by
  intro Hup Hloc
  rw [heap_update_app_none H1 [sc] x v Hup]
  simp [heap_update, Hloc]

theorem heap_update_snoc_miss (H1 : List scell) (sc : scell) (x v : term) :
    heap_update H1 x v = none → cloc sc ≠ x →
    heap_update (H1 ++ [sc]) x v = none := by
  intro Hup Hloc
  rw [heap_update_app_none H1 [sc] x v Hup]
  simp [heap_update, Hloc]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_heapUpdate (s : GoSlice) (H : List scell) (lx lv : Loc) (x v : term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_heap s H ∗ is_term lx x ∗ is_term lv v }}
      (App (App (App (Val (@! checker.heapUpdate)) (Val #s)) (Val #lx)) (Val #lv))
    {{ (s' : GoSlice) (ok : Bool), RET (PairV #s' #ok);
        is_heap s H ∗ ⌜ok = decide (heap_update H x v ≠ none)⌝ ∗
        (if ok then ∃ H', ⌜heap_update H x v = some H'⌝ ∗ is_heap s' H' else True) }} := by
  wp_start as ⟨Hheap, #Hx, #Hv⟩
  unfold is_heap
  icases Hheap with ⟨%cs, Hs, #Hcs⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hcs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave Hnil := ownSlice_nil (GF := GF) (V := checker.Cell) (DFrac.own 1)
  ihave Hnilcap := ownSliceCap_nil (GF := GF) (V := checker.Cell)
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  ihave HI : (∃ (n : w64) (cur : checker.Cell) (fl : Bool) (so : GoSlice)
      (os : List checker.Cell) (Q : List scell),
      "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cur ∗ "found" ∷ found_ptr ↦ fl ∗
      "out" ∷ out_ptr ↦ so ∗ "Hos" ∷ so ↦* os ∗
      "Hcap" ∷ ownSliceCap checker.Cell so (DFrac.own 1) ∗
      "#Hosc" ∷ ([∗list] q;sq ∈ os;Q, is_cell q sq) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ cs.length⌝ ∗
      "%Hfl" ∷ ⌜if fl then heap_update (H.take (sint.nat n)) x v = some Q
                else heap_update (H.take (sint.nat n)) x v = none ∧
                     Q = H.take (sint.nat n)⌝ : IProp GF) $$ [i c found out Hnil Hnilcap]
  · iexists W64 0, _, false, slice.nil, [], []
    iframe i c found out Hnil Hnilcap
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    exact ⟨by word, rfl, rfl⟩
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hn.1, Hif⟩]
    list_elem cs (sint.nat n) as cur'
    list_elem H (sint.nat n) as sc
    ihave #Hcell := BigSepL2.bigSepL2_lookup (Φ := fun _ c sc => is_cell (GF := GF) c sc)
      Hcur'_lookup Hsc_lookup $$ Hcs
    rw [show is_cell cur' sc = iprop(is_term (GF := GF) cur'.Loc' (cloc sc) ∗
      is_term cur'.Val' (cval sc)) from rfl]
    icases Hcell with ⟨#Hloc, #Hval⟩
    wp_apply wp_load_slice_index s (sint.Z n) cs _ cur' Hn.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Hcur'_lookup
    have Htk : H.take (sint.nat n + 1) = H.take (sint.nat n) ++ [sc] := by
      rw [List.take_add_one, Hsc_lookup]; rfl
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    cases fl with
    | true =>
      -- the location was already replaced earlier in the scan
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, _⟩
      wp_auto
      wp_apply wp_slice_append (t := checker.Cell.ty) so os _ [cur'] (DFrac.own 1)
        $$ [Hos Hcap Hsl] as %so' ⟨Hos, Hcap, -⟩
      · iframe Hos Hcap Hsl
      wp_for_post
      iframe
      iexists n + W64 1, cur', true, so', os ++ [cur'], Q ++ [sc]
      iframe
      isplitl []
      · iapply BigSepL2.bigSepL2_snoc.2
        iframe Hosc
        rw [show is_cell cur' sc = iprop(is_term (GF := GF) cur'.Loc' (cloc sc) ∗
          is_term cur'.Val' (cval sc)) from rfl]
        iframe Hloc Hval
      ipureintro
      refine ⟨by word, ?_⟩
      simp only [ite_true] at Hfl ⊢
      rw [Hn1, Htk]
      exact heap_update_snoc_found _ sc x v Q Hfl
    | false =>
      -- still looking: compare this cell's location term
      obtain ⟨Hnone, rfl⟩ := Hfl
      wp_auto
      wp_apply wp_termEq cur'.Loc' lx (some (cloc sc)) (some x) $$ []
      · rw [is_oterm_some, is_oterm_some]; iframe #
      wp_if_destruct
      · -- this is the cell to replace
        have Hhit : cloc sc = x := by simpa using Hif
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, _⟩
        wp_auto
        wp_apply wp_slice_append (t := checker.Cell.ty) so os _ [checker.Cell.mk cur'.Loc' lv]
          (DFrac.own 1) $$ [Hos Hcap Hsl] as %so' ⟨Hos, Hcap, -⟩
        · iframe Hos Hcap Hsl
        wp_for_post
        iframe
        iexists n + W64 1, cur', true, so', os ++ [checker.Cell.mk cur'.Loc' lv],
          H.take (sint.nat n) ++ [mkCell (cloc sc) v]
        iframe
        isplitl []
        · iapply BigSepL2.bigSepL2_snoc.2
          iframe Hosc
          rw [show is_cell (checker.Cell.mk cur'.Loc' lv) (mkCell (cloc sc) v) =
            iprop(is_term (GF := GF) cur'.Loc' (cloc sc) ∗ is_term lv v) from rfl]
          iframe Hloc Hv
        ipureintro
        refine ⟨by word, ?_⟩
        simp only [ite_true]
        rw [Hn1, Htk]
        exact heap_update_snoc_hit _ sc x v Hnone Hhit
      · -- not this cell either
        have Hmiss : cloc sc ≠ x := by simpa using Hif
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, _⟩
        wp_auto
        wp_apply wp_slice_append (t := checker.Cell.ty) so os _ [cur'] (DFrac.own 1)
          $$ [Hos Hcap Hsl] as %so' ⟨Hos, Hcap, -⟩
        · iframe Hos Hcap Hsl
        wp_for_post
        iframe
        iexists n + W64 1, cur', false, so', os ++ [cur'], H.take (sint.nat n) ++ [sc]
        iframe
        isplitl []
        · iapply BigSepL2.bigSepL2_snoc.2
          iframe Hosc
          rw [show is_cell cur' sc = iprop(is_term (GF := GF) cur'.Loc' (cloc sc) ∗
            is_term cur'.Val' (cval sc)) from rfl]
          iframe Hloc Hval
        ipureintro
        refine ⟨by word, ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        rw [Hn1, Htk]
        exact ⟨heap_update_snoc_miss _ sc x v Hnone Hmiss, rfl⟩
  · -- the scan is over
    have Htake : H.take (sint.nat n) = H := List.take_of_length_le (by word)
    rw [Htake] at Hfl
    cases fl with
    | true =>
      -- the location was found
      wp_auto
      iapply HΦ
      isplitl [Hs]
      · iexists cs; iframe Hs Hcs
      simp only [ite_true] at Hfl ⊢
      isplitr
      · ipureintro; simp [Hfl]
      iexists Q
      isplitr
      · ipureintro; exact Hfl
      iexists os; iframe Hos Hosc
    | false =>
      -- no cell at that location
      obtain ⟨Hnone, rfl⟩ := Hfl
      wp_auto
      iapply HΦ
      isplitl [Hs]
      · iexists cs; iframe Hs Hcs
      simp only [Bool.false_eq_true, ite_false]
      isplitl
      · ipureintro; simp [Hnone]
      · itrivial

end proof

end Checker
end Perennial
