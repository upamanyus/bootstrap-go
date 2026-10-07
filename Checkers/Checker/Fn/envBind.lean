/-
Port of `new/checker/fn/envBind.v`.

`checker.envBind` (checker/exec.go): extend the environment with a new
binding.
-/
import Checkers.Checker.Prelude

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

/-- The node is freshly allocated, so its points-to has to be made persistent
before it matches `is_env`, which is stated with `↦□`. -/
theorem wp_envBind (le : Loc) (ρ : List (GoString × term)) (gx : GoString)
    (lt : Loc) (tv : term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_env le ρ ∗ is_term lt tv }}
      (App (App (App (Val (@! checker.envBind)) (Val #le)) (Val #gx)) (Val #lt))
    {{ (le' : Loc), RET #le'; is_env le' ((gx, tv) :: ρ) }} := by
  wp_start as ⟨#He, #Ht⟩
  wp_auto
  wp_alloc lnew as Hnew
  ipersist Hnew
  wp_auto
  iapply HΦ
  simp only [is_env]
  iexists lt, le
  iframe Hnew Ht He

end proof

end Checker
end Perennial
