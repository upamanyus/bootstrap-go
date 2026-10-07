/- Port of `new/proof/github_com/mit_pdos/perennial/checker/examples/swap.v`.

The specification gocheck checks with

     gocheck -pkg ./checker/examples -pre 'p |-> a ∗ q |-> b' \
       -post 'p ↦ b ∗ q ↦ a' Swap
-/
import Checkers.Checker.Examples.ExamplesInit

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.upamanyus.bootstrap_go.checker.examples

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : examples.Assumptions]

theorem wp_Swap (p q : Loc) (a b : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker.examples ∗ p ↦ a ∗ q ↦ b }}
      (App (App (Val (@! Swap)) (Val #p)) (Val #q))
    {{ RET #(); p ↦ b ∗ q ↦ a }} := by
  wp_start as ⟨Hp, Hq⟩
  wp_auto
  wp_end

end wps

end github_com.upamanyus.bootstrap_go.checker.examples

end Perennial
end
