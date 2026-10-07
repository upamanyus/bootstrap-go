/- Port of `new/proof/github_com/mit_pdos/perennial/checker/examples/abs.v`.

The specification gocheck checks with

     gocheck -pkg ./checker/examples \
       -post '(⌜x <s 0⌝ ∗ ⌜ret == -x⌝) ∨ (⌜x >=s 0⌝ ∗ ⌜ret == x⌝)' Abs

Lean notes: `word.opp x` is `-x`.
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

theorem wp_Abs (x : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker.examples }}
      (App (Val (@! Abs)) (Val #x))
    {{ (r : w64), RET #r;
        (⌜sint.Z x < 0⌝ ∗ ⌜r = -x⌝) ∨
        (⌜0 ≤ sint.Z x⌝ ∗ ⌜r = x⌝) }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ; ileft; isplitr <;> ipureintro <;> first | rfl | word
  · iapply HΦ; iright; isplitr <;> ipureintro <;> first | rfl | word

end wps

end github_com.upamanyus.bootstrap_go.checker.examples

end Perennial
end
