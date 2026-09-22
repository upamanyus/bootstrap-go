(** [checker.TermEq] (checker/sorts.go): the exported wrapper around
    [checker.termEq]. *)
From New.checker Require Import prelude.
From New.checker.fn Require Import termEq.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_TermEq (la lb : loc) (oa ob : option term) :
  {{{ is_pkg_init checker ∗ is_oterm la oa ∗ is_oterm lb ob }}}
    @! checker.TermEq #la #lb
  {{{ RET #(bool_decide (oa = ob)); True }}}.
Proof.
  wp_start as "[#Hoa #Hob]".
  wp_auto.
  wp_apply (wp_termEq la lb oa ob with "[$]").
  by iApply "HΦ".
Qed.

End proof.
