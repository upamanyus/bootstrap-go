/- Port of `new/proof/github_com/mit_pdos/perennial/checker/examples/cond_store.v`.

The specification gocheck checks with

     gocheck -pkg ./checker/examples -pre 'p |-> v0' \
       -post '(⌜!flag⌝ ∗ p ↦ v0 ∗ ⌜ret == false⌝) ∨
              (⌜flag⌝ ∗ p ↦ v ∗ ⌜ret == true⌝)' CondStore

Lean notes: the condition is `!flag`, on which Lean's `wp_if_destruct` does
not split (it needs a `decide` or a Boolean variable), so the proof does
`cases flag` instead of Rocq's `wp_if_destruct`.
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

theorem wp_CondStore (flag : Bool) (p : Loc) (v v0 : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker.examples ∗ p ↦ v0 }}
      (App (App (App (Val (@! CondStore)) (Val #flag)) (Val #p)) (Val #v))
    {{ (r : Bool), RET #r;
        (⌜flag = false⌝ ∗ p ↦ v0 ∗ ⌜r = false⌝) ∨
        (⌜flag = true⌝ ∗ p ↦ v ∗ ⌜r = true⌝) }} := by
  wp_start as Hp
  wp_auto
  cases flag
  · -- !flag: p keeps its old contents
    wp_auto
    iapply HΦ; ileft; iframe Hp; isplitr <;> ipureintro <;> rfl
  · -- flag: the write to p happened
    wp_auto
    iapply HΦ; iright; iframe Hp; isplitr <;> ipureintro <;> rfl

end wps

end github_com.upamanyus.bootstrap_go.checker.examples

end Perennial
end
