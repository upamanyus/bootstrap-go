(* The specification gocheck checks with

     gocheck -pkg ./checker/examples \
       -post '(⌜a <u b⌝ ∗ ⌜ret == b⌝) ∨ (⌜a >=u b⌝ ∗ ⌜ret == a⌝)' Max

   Proved by reflection: [wp_symex] (new/proof/symex/) runs a symbolic
   executor over the whole body in one [vm_compute] and leaves one goal per
   path. Compare the hand-written proof of the same lemma in ../max.v. *)
From New.proof.github_com.mit_pdos.perennial.checker.examples
  Require Import examples_init.
From New.proof.symex Require Import tactic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma wp_Max (a b : w64) :
  {{{ is_pkg_init examples }}}
    @! examples.Max #a #b
  {{{ (r : w64), RET #r;
      (⌜uint.Z a < uint.Z b⌝ ∗ ⌜r = b⌝) ∨
      (⌜uint.Z b ≤ uint.Z a⌝ ∗ ⌜r = a⌝) }}}.
Proof.
  wp_start as "_". wp_symex.
  - symex_intros. iApply "HΦ". iLeft. by iPureIntro.
  - symex_intros. iApply "HΦ". iRight. by iPureIntro.
Qed.

End wps.
