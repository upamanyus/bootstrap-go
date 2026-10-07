/- Port of `new/proof/github_com/mit_pdos/perennial/checker/examples/max.v`.

The specification gocheck checks with

     gocheck -pkg ./checker/examples \
       -post '(⌜a <u b⌝ ∗ ⌜ret == b⌝) ∨ (⌜a >=u b⌝ ∗ ⌜ret == a⌝)' Max
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

theorem wp_Max (a b : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker.examples }}
      (App (App (Val (@! Max)) (Val #a)) (Val #b))
    {{ (r : w64), RET #r;
        (⌜uint.Z a < uint.Z b⌝ ∗ ⌜r = b⌝) ∨
        (⌜uint.Z b ≤ uint.Z a⌝ ∗ ⌜r = a⌝) }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ; ileft; isplitr <;> ipureintro <;> first | rfl | word
  · iapply HΦ; iright; isplitr <;> ipureintro <;> first | rfl | word

end wps

end github_com.upamanyus.bootstrap_go.checker.examples

end Perennial
end
