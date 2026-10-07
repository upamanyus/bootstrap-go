/- Port of `new/proof/github_com/mit_pdos/perennial/checker/examples/median3.v`.

The specification gocheck checks with

     gocheck -pkg ./checker/examples \
       -post '(⌜b <u a⌝ ∗ ⌜c <u b⌝ ∗ ⌜ret == b⌝) ∨
              (⌜b >=u a⌝ ∗ ⌜c >=u b⌝ ∗ ⌜ret == b⌝) ∨
              (⌜c >=u b⌝ ∗ ⌜c <u a⌝ ∗ ⌜ret == c⌝) ∨
              (⌜c >=u a⌝ ∗ ⌜c <u b⌝ ∗ ⌜ret == c⌝) ∨
              (⌜b <u a⌝ ∗ ⌜c >=u a⌝ ∗ ⌜ret == a⌝) ∨
              (⌜c <u a⌝ ∗ ⌜b >=u a⌝ ∗ ⌜ret == a⌝) ∨
              (⌜b <u a⌝ ∗ ⌜a <u b⌝) ∨
              (⌜b >=u a⌝ ∗ ⌜b <u a⌝)' Median3

   The last two disjuncts are contradictory: they cover the two infeasible
   paths of the sorting network (paths 2 and 6), which the checker, having no
   arithmetic, cannot discard. Here those paths are refuted instead, so the two
   disjuncts are never used, but they are kept so that both tools establish
   the same specification.

Lean notes: Rocq's local `disj n` tactic is a macro `disj n` here.
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

/-- `disj n` proves disjunct `n` of the postcondition, counting from 0. -/
local macro "disj " n:num : tactic => do
  let mut t ← `(tactic| (ileft; repeat' (first | isplitr | ipureintro; first | rfl | word)))
  for _ in [0:n.getNat] do
    t ← `(tactic| (iright; $t))
  return t

theorem wp_Median3 (a b c : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker.examples }}
      (App (App (App (Val (@! Median3)) (Val #a)) (Val #b)) (Val #c))
    {{ (r : w64), RET #r;
        (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z c < uint.Z b⌝ ∗ ⌜r = b⌝) ∨
        (⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜uint.Z b ≤ uint.Z c⌝ ∗ ⌜r = b⌝) ∨
        (⌜uint.Z b ≤ uint.Z c⌝ ∗ ⌜uint.Z c < uint.Z a⌝ ∗ ⌜r = c⌝) ∨
        (⌜uint.Z a ≤ uint.Z c⌝ ∗ ⌜uint.Z c < uint.Z b⌝ ∗ ⌜r = c⌝) ∨
        (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z a ≤ uint.Z c⌝ ∗ ⌜r = a⌝) ∨
        (⌜uint.Z c < uint.Z a⌝ ∗ ⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜r = a⌝) ∨
        (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z a < uint.Z b⌝) ∨
        (⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜uint.Z b < uint.Z a⌝) }} := by
  wp_start
  wp_auto
  -- The three comparators; the eight goals come in the order of gocheck's
  -- paths 0-7.
  repeat' wp_if_destruct
  all_goals (try (exfalso; word))
  all_goals iapply HΦ
  · -- c < b < a
    disj 0
  · -- b <= c < a
    disj 2
  · -- b < a <= c
    disj 4
  · -- c < a <= b
    disj 5
  · -- a <= c < b
    disj 3
  · -- a <= b <= c
    disj 1

end wps

end github_com.upamanyus.bootstrap_go.checker.examples

end Perennial
end
