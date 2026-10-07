/-
Port of `new/checker/fn/TermEq.v`.

`checker.TermEq` (checker/sorts.go): the exported wrapper around
`checker.termEq`.
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

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_TermEq (la lb : Loc) (oa ob : Option term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_oterm la oa ∗ is_oterm lb ob }}
      (App (App (Val (@! checker.TermEq)) (Val #la)) (Val #lb))
    {{ RET #(decide (oa = ob)); True }} := by
  wp_start as ⟨#Hoa, #Hob⟩
  wp_auto
  wp_apply wp_termEq la lb oa ob $$ []
  · iframe #
  iapply HΦ
  itrivial

end proof

end Checker
end Perennial
