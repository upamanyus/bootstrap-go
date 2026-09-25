(** The export of two real proof states: the proof of [wp_Median3]
    (checker/examples, see
    [New.proof.github_com.mit_pdos.perennial.checker.examples.median3]) right
    after [wp_auto], an Iris proof mode goal with three typed points-to facts
    and a WP, and one of its eight path goals, whose path condition is in the
    Rocq context.

    Built with the rest of the tree, each goal reports only the size of its
    export. [gocheck/rocqgoal/testdata/regen.sh] prints the exports in full;
    they are the test inputs of the Go package [gocheck/rocqgoal]. *)
From New.proof.github_com.mit_pdos.perennial.checker.examples
  Require Import examples_init.
From New.proof.rocqgoal Require Import export.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma wp_Median3_export (a b c : w64) :
  {{{ is_pkg_init examples }}}
    @! examples.Median3 #a #b #c
  {{{ (r : w64), RET #r;
      (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z c < uint.Z b⌝ ∗ ⌜r = b⌝) ∨
      (⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜uint.Z b ≤ uint.Z c⌝ ∗ ⌜r = b⌝) ∨
      (⌜uint.Z b ≤ uint.Z c⌝ ∗ ⌜uint.Z c < uint.Z a⌝ ∗ ⌜r = c⌝) ∨
      (⌜uint.Z a ≤ uint.Z c⌝ ∗ ⌜uint.Z c < uint.Z b⌝ ∗ ⌜r = c⌝) ∨
      (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z a ≤ uint.Z c⌝ ∗ ⌜r = a⌝) ∨
      (⌜uint.Z c < uint.Z a⌝ ∗ ⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜r = a⌝) ∨
      (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z a < uint.Z b⌝) ∨
      (⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜uint.Z b < uint.Z a⌝) }}}.
Proof.
  wp_start as "_". wp_auto.
  ltac2:(report_goal "median3_wp_auto").
  repeat wp_if_destruct.
  1: ltac2:(report_goal "median3_path").
Abort.

End wps.
