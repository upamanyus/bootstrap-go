(* The specification gocheck checks with

     gocheck -pkg ./checker/examples -pre 'z |-> z0' \
       -post '(⌜x == 0⌝ ∗ z ↦ 37 + 37) ∨ (⌜x != 0⌝ ∗ z ↦ x + x)' Double

   Proved by reflection: [wp_symex] (new/proof/symex/) runs a symbolic
   executor over the whole body in one [vm_compute] and leaves one goal per
   path. Compare the hand-written proof of the same lemma in ../double.v. *)
From New.proof.github_com.mit_pdos.perennial.checker.examples
  Require Import examples_init.
From New.proof.symex Require Import tactic.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Lemma wp_Double (x : w64) (z : loc) (z0 : w64) :
  {{{ is_pkg_init examples ∗ z ↦ z0 }}}
    @! examples.Double #x #z
  {{{ RET #();
      (⌜x = W64 0⌝ ∗ z ↦ W64 74) ∨
      (⌜x ≠ W64 0⌝ ∗ z ↦ word.add x x) }}}.
Proof.
  wp_start as "Hz". wp_symex.
  - (* x = 0: the store wrote 37 + 37 *)
    symex_intros. iApply "HΦ". iLeft.
    replace (word.add (W64 37) (W64 37)) with (W64 74) by word.
    by iFrame.
  - (* x ≠ 0: the store wrote x + x *)
    symex_intros. iApply "HΦ". iRight. by iFrame.
Qed.

End wps.
