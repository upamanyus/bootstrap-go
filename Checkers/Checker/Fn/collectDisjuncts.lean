/-
Port of `new/checker/fn/collectDisjuncts.v`.

`checker.collectDisjuncts` (checker/match.go): the top-level disjunction
of a postcondition, flattened left to right.

An assertion that is not an `AOr` is a single disjunct -- and so is nil,
which the Go code appends unchanged, so the mirror is over
`Option cassn` and returns a list of `Option cassn`.

Lean notes:
* Rocq's `wp_append_nil` is `wp_append_nil_assn` here (Lean names are not
  module-qualified; assnHeap and assnPure have their own).
-/
import Checkers.Checker.Nodes

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

-- `assn_disjuncts`: in LCheck/Fns.lean.

def oassn_disjuncts : Option cassn → List (Option cassn)
  | none => [none]
  | some x' => assn_disjuncts x'

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

/-- The slice of `*Assn` the function returns. -/
def is_assns (s : GoSlice) (xs : List (Option cassn)) : IProp GF :=
  iprop(∃ ls : List Loc, s ↦* ls ∗ ownSliceCap Loc s (DFrac.own 1) ∗
                    [∗list] l;y ∈ ls;xs, is_oassn l y)

/-- Appending onto the nil slice: `out` starts at nil, and
`wp_slice_append`'s two slices are ambiguous enough that framing picks the
wrong one unless both slices are named variables (as in assnHeap). -/
theorem wp_append_nil_assn (s2 : GoSlice) (vs : List Loc) (Φ : val → IProp GF) :
    s2 ↦* vs ⊢
    (∀ s' : GoSlice, s' ↦* vs ∗ ownSliceCap Loc s' (DFrac.own 1) -∗ Φ #s') -∗
    WP (App (App (Val #(functions go.append
        [go.GoType.SliceType (go.GoType.PointerType checker.Assn.ty)]))
      (Val #slice.nil)) (Val #s2)) {{ Φ }} := by
  iintro Hs2 HΦ
  ihave Hnil := ownSlice_nil (GF := GF) (V := Loc) (DFrac.own 1)
  ihave Hnilc := ownSliceCap_nil (GF := GF) (V := Loc)
  wp_apply wp_slice_append (t := go.GoType.PointerType checker.Assn.ty) slice.nil [] s2 vs
    (DFrac.own 1) $$ [Hs2] as %s' ⟨Hs', Hs'c, -⟩
  · iframe Hs2 Hnil Hnilc
  iapply HΦ
  simp only [List.nil_append]
  iframe Hs' Hs'c

set_option hygiene false in
/-- `return append(out, a)`: the one-element answer. -/
local macro "single" : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, _⟩
  try wp_auto
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  wp_apply wp_append_nil_assn $$ Hsl
  iintro %s' ⟨Hs', Hs'c⟩
  try wp_auto
  iapply HΦ
  unfold is_assns
  iexists _
  iframe Hs' Hs'c
  iapply BigSepL2.bigSepL2_singleton.2
  try rw [is_oassn_some]
  iframe Hx))

theorem wp_collectDisjuncts (la : Loc) (x : Option cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_oassn la x }}
      (App (Val (@! checker.collectDisjuncts)) (Val #la))
    {{ (s : GoSlice), RET #s; is_assns s (oassn_disjuncts x) }} := by
  iloeb as IH generalizing %la %x
  wp_start as #Hx
  ihave %Hnull := is_oassn_null _ _ $$ Hx
  wp_auto
  cases x with
  | none =>
    -- nil: the singleton `[nil]`
    obtain rfl : la = null := Hnull.mpr rfl
    simp only [oassn_disjuncts]
    single
  | some x' =>
  have Hnn : la ≠ null := fun h => by simp at Hnull; exact Hnull h
  ihave #Hx' := Hx
  rw [is_oassn_some]
  icases is_assn_node _ _ $$ Hx' with ⟨%lL, %lR, %lX, %lY, %Hwf, #Hnode, #HL, #HR, #HX, #HY⟩
  iStructNamed Hnode
  cases x' with
  | CAOr x1 x2 =>
    -- the left chain, then the right one
    simp only [oassn_disjuncts, assn_disjuncts, assn_code, assn_l, assn_r] at *
    wp_if_destruct
    · exact absurd rfl Hnn
    try wp_auto
    wp_apply IH $$ %lL %(some x1) [] as %s1 Hs1
    · iframe #
    unfold is_assns
    icases Hs1 with ⟨%ls1, Hs1, -, #Hd1⟩
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    wp_apply wp_append_nil_assn $$ Hs1
    iintro %s2 ⟨Hs2, Hs2c⟩
    try wp_auto
    wp_apply IH $$ %lR %(some x2) [] as %s3 Hs3
    · iframe #
    icases Hs3 with ⟨%ls3, Hs3, -, #Hd3⟩
    wp_apply wp_slice_append (t := go.GoType.PointerType checker.Assn.ty) s2 ls1 s3 ls3
      (DFrac.own 1) $$ [Hs2 Hs2c Hs3] as %s4 ⟨Hs4, Hs4c, -⟩
    · iframe Hs2 Hs2c Hs3
    try wp_auto
    iapply HΦ
    iexists ls1 ++ ls3
    iframe Hs4 Hs4c
    iapply BigSepL2.bigSepL2_app_wand $$ Hd1 Hd3
  | _ =>
    simp only [oassn_disjuncts, assn_disjuncts, assn_code] at *
    wp_if_destruct
    · exact absurd rfl Hnn
    single

end proof

end Checker
end Perennial
