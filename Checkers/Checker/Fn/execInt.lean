/-
Port of `new/checker/fn/execInt.v`.

`checker.execInt` (checker/exec.go): an integer literal is the single path
`onePath` builds, with the term `TInt` of the literal.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundA
import Checkers.Checker.ExecSoundB
import Checkers.Checker.Fn.onePath

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

theorem wp_execInt (w : w64) : ⊢ exec_like (GF := GF) checker.execInt (CEInt w) := by
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  iStructNamed He
  wp_auto
  ipersist «$a0»
  wp_apply wp_onePath «$a0_ptr» lst (TInt w) sst $$ [Hst] as %s Hs
  · iframe Hst
    simp only [is_term, tnode]
    iExactEq «$a0»; rfl
  iapply HΦ
  rw [(exec_post_ok _ _ _ _).to_eq]
  iexists _
  iframe Hs
  ipureintro
  exact ⟨paths_wf_single _ _ _ Hwf (Nat.le_refl _) trivial, exec_sound_int _ _ _⟩

end proof

end Checker
end Perennial
