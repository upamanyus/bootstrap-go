(* The specification gocheck checks with

     gocheck -pkg ./checker/examples -pre 'p |-> a ∗ q |-> b' \
       -post 'p ↦ b ∗ q ↦ a' Swap

   Proved by reflection: [wp_symex] (new/proof/symex/) runs a symbolic
   executor over the whole body in one [vm_compute] and leaves one goal per
   path. Compare the hand-written proof of the same lemma in ../swap.v. *)
From New.proof.github_com.mit_pdos.perennial.checker.examples
  Require Import examples_init.
From New.proof.symex Require Import tactic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma wp_Swap (p q : loc) (a b : w64) :
  {{{ is_pkg_init examples ∗ p ↦ a ∗ q ↦ b }}}
    @! examples.Swap #p #q
  {{{ RET #(); p ↦ b ∗ q ↦ a }}}.
Proof.
  wp_start as "[Hp Hq]". wp_symex.
  symex_intros. iApply "HΦ". iFrame.
Qed.

End wps.
