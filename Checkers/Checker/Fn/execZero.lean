/-
Port of `new/checker/fn/execZero.v`.

`checker.execZero` (checker/exec.go): the zero value of a type
(`typeZero`) is the single path `onePath` builds.

Lean notes:
* Rocq's `wp_execZero_aux` (naming trap) is not needed; `wp_execZero` is
  proved directly.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundA
import Checkers.Checker.ExecSoundB
import Checkers.Checker.Fn.onePath
import Checkers.Checker.Fn.typeZero

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_execZero (t : ctype) : ⊢ exec_like (GF := GF) checker.execZero (CEZero t) := by
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  icases He with ⟨%lty, #Hnode, #Hty⟩
  iStructNamed Hnode
  wp_auto
  wp_apply wp_typeZero lty t $$ [] as %lz #Hlz
  · iframe Hty
  wp_apply wp_onePath lz lst (ctype_zero t) sst $$ [Hst] as %s Hs
  · iframe Hst Hlz
  iapply HΦ
  rw [(exec_post_ok _ _ _ _).to_eq]
  iexists _
  iframe Hs
  ipureintro
  exact ⟨paths_wf_single _ _ _ Hwf (Nat.le_refl _) (vars_below_ctype_zero _ _),
    exec_sound_zero _ _ _⟩

end proof

end Checker
end Perennial
