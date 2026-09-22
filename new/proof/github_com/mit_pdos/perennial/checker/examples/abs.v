(* The specification gocheck checks with

     gocheck -pkg ./checker/examples \
       -post '(⌜x <s 0⌝ ∗ ⌜ret == -x⌝) ∨ (⌜x >=s 0⌝ ∗ ⌜ret == x⌝)' Abs *)
From New.proof.github_com.mit_pdos.perennial.checker.examples
  Require Import examples_init.

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
  wp_start as "_". wp_auto.
  wp_if_destruct.
  - iApply "HΦ". iLeft. iSplit; iPureIntro; [word|done].
  - iApply "HΦ". iRight. iSplit; iPureIntro; [word|done].
Qed.

End wps.
