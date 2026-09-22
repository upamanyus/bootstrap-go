(* The specification gocheck checks with

     gocheck -pkg ./checker/examples -pre 'p |-> a ∗ q |-> b' \
       -post 'p ↦ b ∗ q ↦ a' Swap *)
From New.proof.github_com.mit_pdos.perennial.checker.examples
  Require Import examples_init.

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
  wp_start as "[Hp Hq]". wp_auto.
  wp_end.
Qed.

End wps.
