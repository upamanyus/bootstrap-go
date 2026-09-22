(* The specification gocheck checks with

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
   the same specification. *)
From New.proof.github_com.mit_pdos.perennial.checker.examples
  Require Import examples_init.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(* [disj n] proves disjunct n of the postcondition, counting from 0. *)
Local Tactic Notation "disj" integer(n) :=
  do n iRight; iLeft; iPureIntro; split_and!; first [done | word].

Lemma wp_Median3 (a b c : w64) :
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
  (* The three comparators; the eight goals come in the order of gocheck's
     paths 0-7. *)
  repeat wp_if_destruct.
  all: try (exfalso; word).
  all: iApply "HΦ".
  - (* c < b < a *) disj 0.
  - (* b <= c < a *) disj 2.
  - (* b < a <= c *) disj 4.
  - (* c < a <= b *) disj 5.
  - (* a <= c < b *) disj 3.
  - (* a <= b <= c *) disj 1.
Qed.

End wps.
