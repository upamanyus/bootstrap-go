/-
Port of `new/checker/fn/assnHeap.v`.

`checker.assnHeap` (checker/check.go): the points-to atoms of an
assertion, left to right.

Lean notes:
* Rocq's `wp_append_nil` is `wp_append_nil_cell` here (Lean names are not
  module-qualified, and assnHeap/assnPure/collectDisjuncts each have one).
* The case split is on the mirror before `wp_auto`, so the node's kind is a
  literal and the dispatch is evaluated (Rocq split after the first
  `wp_auto`; the effect is the same).
-/
import Checkers.Checker.Nodes

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

def cassn_heap : cassn → List scell
  | CASep p q => cassn_heap p ++ cassn_heap q
  | CAPointsTo lx ly => [mkCell lx ly]
  | _ => []

def oassn_heap : Option cassn → List scell
  | none => []
  | some x' => cassn_heap x'

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem is_heap_nil : ⊢ is_heap (GF := GF) slice.nil [] := by
  unfold is_heap
  iexists []
  isplitr
  · iapply ownSlice_nil
  · first | iempintro | (simp only [BigSepL2.bigSepL2_nil]; iempintro) | itrivial

/-- Appending onto the nil slice: the Go code starts `out` at nil and appends
to it, and `wp_slice_append`'s two slices are ambiguous enough that framing
picks the wrong one unless both slices are named variables. -/
theorem wp_append_nil_cell (s2 : GoSlice) (vs : List checker.Cell) (Φ : val → IProp GF) :
    s2 ↦* vs ⊢
    (∀ s' : GoSlice, s' ↦* vs ∗ ownSliceCap checker.Cell s' (DFrac.own 1) -∗ Φ #s') -∗
    WP (App (App (Val #(functions go.append [go.GoType.SliceType checker.Cell.ty]))
      (Val #slice.nil)) (Val #s2)) {{ Φ }} := by
  iintro Hs2 HΦ
  ihave Hnil := ownSlice_nil (GF := GF) (V := checker.Cell) (DFrac.own 1)
  ihave Hnilc := ownSliceCap_nil (GF := GF) (V := checker.Cell)
  wp_apply wp_slice_append (t := checker.Cell.ty) slice.nil [] s2 vs (DFrac.own 1) $$ [Hs2]
    as %s' ⟨Hs', Hs'c, -⟩
  · iframe Hs2 Hnil Hnilc
  iapply HΦ
  simp only [List.nil_append]
  iframe Hs' Hs'c

set_option hygiene false in
local macro "empty_heap" : tactic => `(tactic| (
  try wp_auto
  iapply HΦ
  isplitr
  · iapply is_heap_nil
  · iapply ownSliceCap_nil))

theorem wp_assnHeap (l : Loc) (x : Option cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_oassn l x }}
      (App (Val (@! checker.assnHeap)) (Val #l))
    {{ (s : GoSlice), RET #s;
        is_heap s (oassn_heap x) ∗ ownSliceCap checker.Cell s (DFrac.own 1) }} := by
  iloeb as IH generalizing %l %x
  wp_start as #Hx
  ihave %Hn := is_oassn_null _ _ $$ Hx
  wp_auto
  wp_if_destruct
  · -- the argument is nil: the empty heap
    obtain rfl : x = none := Hn.mp rfl
    simp only [oassn_heap]
    empty_heap
  cases x with
  | none => exact absurd (Hn.mpr rfl) Hif
  | some x' =>
  rw [is_oassn_some]
  icases is_assn_node _ _ $$ Hx with ⟨%lL, %lR, %lX, %lY, %Hwf, #Hnode, #HL, #HR, #HX, #HY⟩
  iStructNamed Hnode
  cases x' with
  | CAEmp => simp only [oassn_heap, cassn_heap, assn_code] at *; empty_heap
  | CAOr => simp only [oassn_heap, cassn_heap, assn_code] at *; empty_heap
  | CAExists => simp only [oassn_heap, cassn_heap, assn_code] at *; empty_heap
  | CAPure => simp only [oassn_heap, cassn_heap, assn_code] at *; empty_heap
  | CASep x1 x2 =>
    -- the left heap, then the right one
    simp only [oassn_heap, cassn_heap, assn_code, assn_l, assn_r] at *
    try wp_auto
    wp_apply IH $$ %lL %(some x1) [] as %s1 ⟨Hh1, -⟩
    · iframe #
    unfold is_heap
    icases Hh1 with ⟨%cs1, Hs1, #Hc1⟩
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    wp_apply wp_append_nil_cell $$ Hs1
    iintro %s2 ⟨Hs2, Hs2c⟩
    try wp_auto
    wp_apply IH $$ %lR %(some x2) [] as %s3 ⟨Hh3, -⟩
    · iframe #
    icases Hh3 with ⟨%cs3, Hs3, #Hc3⟩
    wp_apply wp_slice_append (t := checker.Cell.ty) s2 cs1 s3 cs3 (DFrac.own 1) $$ [Hs2 Hs2c Hs3]
      as %s4 ⟨Hs4, Hs4c, -⟩
    · iframe Hs2 Hs2c Hs3
    try wp_auto
    iapply HΦ
    iframe Hs4c
    iexists cs1 ++ cs3
    iframe Hs4
    iapply BigSepL2.bigSepL2_app_wand $$ Hc1 Hc3
  | CAPointsTo x1 x2 =>
    -- the one cell
    simp only [oassn_heap, cassn_heap, assn_code, assn_x, assn_y] at *
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, _⟩
    wp_auto
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    wp_apply wp_append_nil_cell $$ Hsl
    iintro %s2 ⟨Hs2, Hs2c⟩
    try wp_auto
    iapply HΦ
    iframe Hs2c
    unfold is_heap
    iexists _
    iframe Hs2
    iapply BigSepL2.bigSepL2_singleton.2
    unfold is_cell
    rw [is_oterm_some, is_oterm_some]
    iframe HX HY

end proof

end Checker
end Perennial
