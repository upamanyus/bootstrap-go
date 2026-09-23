(* The specification gocheck checks with

     gocheck -pkg ./checker/examples \
       -post '(⌜x <s 0⌝ ∗ ⌜ret == -x⌝) ∨ (⌜x >=s 0⌝ ∗ ⌜ret == x⌝)' Abs

   Proved by reflection: [wp_symex] (new/proof/symex/) runs a symbolic
   executor over the whole body in one [vm_compute] and leaves one goal per
   path. Compare the hand-written proof of the same lemma in ../abs.v. *)
From New.proof.github_com.mit_pdos.perennial.checker.examples
  Require Import examples_init.
From New.proof.symex Require Import tactic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma wp_Abs (x : w64) :
  {{{ is_pkg_init examples }}}
    @! examples.Abs #x
  {{{ (r : w64), RET #r;
      (⌜sint.Z x < 0⌝ ∗ ⌜r = word.opp x⌝) ∨
      (⌜0 ≤ sint.Z x⌝ ∗ ⌜r = x⌝) }}}.
Proof.
  wp_start as "_". wp_symex.
  - symex_intros. iApply "HΦ". iLeft. iPureIntro. split; [word|done].
  - symex_intros. iApply "HΦ". iRight. iPureIntro. split; [word|done].
Qed.

End wps.
