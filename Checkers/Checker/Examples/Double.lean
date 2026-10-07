/- Port of `new/proof/github_com/mit_pdos/perennial/checker/examples/double.v`.

The specification gocheck checks with

     gocheck -pkg ./checker/examples -pre 'z ↦ z0' \
       -post '(⌜x == 0⌝ ∗ z ↦ 37 + 37) ∨ (⌜x != 0⌝ ∗ z ↦ x + x)' Double

Lean notes: `word.add x x` is `x + x`. Rocq's
`replace (word.add (W64 37) (W64 37)) with (W64 74) by word` is a `rw` of the
goal's `W64 74`.
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

theorem wp_Double (x : w64) (z : Loc) (z0 : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker.examples ∗
        z ↦ z0 }}
      (App (App (Val (@! Double)) (Val #x)) (Val #z))
    {{ RET #();
        (⌜x = W64 0⌝ ∗ z ↦ W64 74) ∨
        (⌜x ≠ W64 0⌝ ∗ z ↦ (x + x)) }} := by
  wp_start as Hz
  wp_auto
  wp_if_destruct
  · -- x = 0: the store wrote 37 + 37
    iapply HΦ
    ileft
    rw [show W64 74 = W64 37 + W64 37 by word]
    iframe Hz
  · -- x ≠ 0: the store wrote x + x
    iapply HΦ
    iright
    iframe Hz
    ipureintro; exact Hif

end wps

end github_com.upamanyus.bootstrap_go.checker.examples

end Perennial
end
