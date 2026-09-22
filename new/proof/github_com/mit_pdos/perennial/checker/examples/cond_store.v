(* The specification gocheck checks with

     gocheck -pkg ./checker/examples -pre 'p |-> v0' \
       -post '(⌜!flag⌝ ∗ p ↦ v0 ∗ ⌜ret == false⌝) ∨
              (⌜flag⌝ ∗ p ↦ v ∗ ⌜ret == true⌝)' CondStore *)
From New.proof.github_com.mit_pdos.perennial.checker.examples
  Require Import examples_init.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma wp_CondStore (flag : bool) (p : loc) (v v0 : w64) :
  {{{ is_pkg_init examples ∗ p ↦ v0 }}}
    @! examples.CondStore #flag #p #v
  {{{ (r : bool), RET #r;
      (⌜flag = false⌝ ∗ p ↦ v0 ∗ ⌜r = false⌝) ∨
      (⌜flag = true⌝ ∗ p ↦ v ∗ ⌜r = true⌝) }}}.
Proof.
  wp_start as "Hp". wp_auto.
  wp_if_destruct.
  - (* flag: the write to p happened *)
    iApply "HΦ". iRight. iFrame. done.
  - (* !flag: p keeps its old contents *)
    iApply "HΦ". iLeft. iFrame. done.
Qed.

End wps.
