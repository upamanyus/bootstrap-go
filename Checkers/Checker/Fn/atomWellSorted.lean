/-
Port of `new/checker/fn/atomWellSorted.v`.

`checker.atomWellSorted` (checker/match.go): the sort check for a single
atom of a postcondition's disjunct.

An atom passes exactly when it is a pure assertion whose term has sort
`SBool`, or a points-to whose location term has sort `SLoc` and whose
value term has a sort at all. Every other kind -- and the nil pointer --
is rejected with a freshly allocated `Failure`; the specification says
nothing about the failure's contents, only that the returned pointer is
non-nil, which is what every caller tests.
-/
import Checkers.Checker.Fn.sortOfEnv

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

-- `atom_well_sorted`: in LCheck/Fns.lean.

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

set_option hygiene false in
/-- A rejection: allocate the `Failure` and return it. -/
local macro "reject" : tactic => `(tactic| (
  try wp_auto
  first
    | wp_alloc lf as Hf
    | (wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_alloc lf as Hf)
    | (wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_alloc lf as Hf)
    | (wp_pures; wp_load; wp_pures; wp_alloc lf as Hf)
  try wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hf
  iapply HΦ
  iframe
  ipureintro
  simp [atom_well_sorted, Hnn]))

theorem wp_atomWellSorted (dq : DFrac) (lse la : Loc) (E : sort_env) (oa : Option cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_sortenv dq lse E ∗ is_oassn la oa ∗
        ⌜sort_env_wf E⌝ }}
      (App (App (Val (@! checker.atomWellSorted)) (Val #lse)) (Val #la))
    {{ (lf : Loc), RET #lf;
        is_sortenv dq lse E ∗ ⌜lf = null ↔ atom_well_sorted E oa = true⌝ }} := by
  wp_start as ⟨Henv, #Hoa, %Hwf⟩
  ihave %Hnull := is_oassn_null _ _ $$ Hoa
  wp_auto
  wp_if_destruct
  · -- the atom pointer is nil
    obtain rfl : oa = none := Hnull.mp rfl
    reject
  cases oa with
  | none => exact absurd (Hnull.mpr rfl) Hif
  | some aa =>
  rw [is_oassn_some]
  icases is_assn_node _ _ $$ Hoa with ⟨%lL, %lR, %lX, %lY, %Hidx, #Hnode, #HL, #HR, #HX, #HY⟩
  iStructNamed Hnode
  cases aa with
  | CAEmp => simp only [assn_code] at *; reject
  | CASep => simp only [assn_code] at *; reject
  | CAOr => simp only [assn_code] at *; reject
  | CAExists => simp only [assn_code] at *; reject
  | CAPure x1 =>
    simp only [assn_code, assn_x, assn_y] at *
    wp_auto
    wp_apply wp_sortOfEnv dq lse lX E (some x1) Hwf $$ [Henv] as Henv
    · iframe # ∗
    simp only [osort_of, atom_well_sorted]
    rcases sort_of E x1 with _ | (_|_|_|_) <;> simp only [osort_code, osort_ok, sort_code]
    all_goals first
      | (wp_auto; iapply HΦ; iframe; ipureintro; simp; done)
      | reject
  | CAPointsTo x1 x2 =>
    simp only [assn_code, assn_x, assn_y] at *
    wp_auto
    wp_apply wp_sortOfEnv dq lse lX E (some x1) Hwf $$ [Henv] as Henv
    · iframe # ∗
    simp only [osort_of, atom_well_sorted]
    rcases sort_of E x1 with _ | (_|_|_|_) <;> simp only [osort_code, osort_ok, sort_code]
    case some.SLoc =>
      wp_auto
      wp_apply wp_sortOfEnv dq lse lY E (some x2) Hwf $$ [Henv] as Henv
      · iframe # ∗
      simp only [osort_of]
      rcases sort_of E x2 with _ | _ <;> simp only [osort_code, osort_ok]
      · reject
      · wp_auto; iapply HΦ; iframe; ipureintro; simp
    all_goals reject

end proof

end Checker
end Perennial
