/-
Port of `new/checker/fn/assnWellSorted.v`.

`checker.assnWellSorted` (checker/check.go): the sort check of a
precondition. `emp` and `∗` are traversed, the two atoms go to
`atomWellSorted`, and every other form (and nothing else) is rejected.
-/
import Checkers.Checker.Fn.atomWellSorted

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- The mirror. `none` is the nil `*Assn`, which is accepted (as `emp`). -/
def cassn_ws (E : sort_env) : cassn → Bool
  | CAEmp => true
  | CASep p q => cassn_ws E p && cassn_ws E q
  | CAPure t => match sort_of E t with | some SBool => true | _ => false
  | CAPointsTo x v =>
      match sort_of E x, sort_of E v with
      | some SLoc, some _ => true
      | _, _ => false
  | _ => false

def oassn_ws (E : sort_env) : Option cassn → Bool
  | none => true
  | some x' => cassn_ws E x'

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_assnWellSorted (dq : DFrac) (lse la : Loc) (E : sort_env) (oa : Option cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_sortenv dq lse E ∗ is_oassn la oa ∗
        ⌜sort_env_wf E⌝ }}
      (App (App (Val (@! checker.assnWellSorted)) (Val #lse)) (Val #la))
    {{ (lf : Loc), RET #lf;
        is_sortenv dq lse E ∗ ⌜lf = null ↔ oassn_ws E oa = true⌝ }} := by
  iloeb as IH generalizing %la %oa
  wp_start as ⟨Henv, #Hoa, %Hwf⟩
  ihave %Hnull := is_oassn_null _ _ $$ Hoa
  wp_auto
  wp_if_destruct
  · -- nil
    obtain rfl : oa = none := Hnull.mp rfl
    iapply HΦ; iframe; ipureintro; simp [oassn_ws]
  cases oa with
  | none => exact absurd (Hnull.mpr rfl) Hif
  | some aa =>
  rw [is_oassn_some]
  icases is_assn_node _ _ $$ Hoa with ⟨%lL, %lR, %lX, %lY, %Hidx, #Hnode, #HL, #HR, #HX, #HY⟩
  iStructNamed Hnode
  cases aa with
  | CAEmp =>
    simp only [assn_code] at *
    wp_auto
    iapply HΦ; iframe; ipureintro; simp [oassn_ws, cassn_ws]
  | CASep x1 x2 =>
    simp only [assn_code, assn_l, assn_r] at *
    wp_auto
    wp_apply IH $$ %lL %(some x1) [Henv] as %lf1 ⟨Henv, %Hlf1⟩
    · iframe # ∗; ipureintro; exact Hwf
    wp_if_destruct
    · -- the left half passed
      wp_apply IH $$ %lR %(some x2) [Henv] as %lf2 ⟨Henv, %Hlf2⟩
      · iframe # ∗; ipureintro; exact Hwf
      try wp_auto
      iapply HΦ; iframe; ipureintro
      simp only [oassn_ws, cassn_ws] at *
      simp [Hlf1.mp trivial, ← Hlf2]
    · -- the left half failed
      iapply HΦ; iframe; ipureintro
      simp only [oassn_ws, cassn_ws] at *
      cases h : cassn_ws E x1
      · simp [Hif]
      · exact absurd (Hlf1.mpr h) Hif
  | CAOr x1 x2 =>
    simp only [assn_code] at *
    wp_auto
    wp_alloc lf as Hf
    try wp_auto
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hf
    iapply HΦ; iframe; ipureintro; simp [oassn_ws, cassn_ws, Hnn]
  | CAExists n s x1 =>
    simp only [assn_code] at *
    wp_auto
    wp_alloc lf as Hf
    try wp_auto
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hf
    iapply HΦ; iframe; ipureintro; simp [oassn_ws, cassn_ws, Hnn]
  | CAPure x1 =>
    simp only [assn_code] at *
    wp_auto
    wp_apply wp_atomWellSorted dq lse la E (some (CAPure x1)) $$ [Henv] as %lf1 ⟨Henv, %Hlf1⟩
    · rw [is_oassn_some]; iframe # ∗; ipureintro; exact Hwf
    try wp_auto
    iapply HΦ; iframe; ipureintro
    rw [Hlf1]; rfl
  | CAPointsTo x1 x2 =>
    simp only [assn_code] at *
    wp_auto
    wp_apply wp_atomWellSorted dq lse la E (some (CAPointsTo x1 x2)) $$ [Henv]
      as %lf1 ⟨Henv, %Hlf1⟩
    · rw [is_oassn_some]; iframe # ∗; ipureintro; exact Hwf
    try wp_auto
    iapply HΦ; iframe; ipureintro
    rw [Hlf1]; rfl

end proof

end Checker
end Perennial
