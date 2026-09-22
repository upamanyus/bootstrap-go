(** [checker.typeZero] (checker/sorts.go): the term for the zero value.

    Note on naming: no Rocq variable here may be called [t], [s] or [ok],
    the names of the Go function's own locals, because [wp_auto] derives Rocq
    identifiers from the Go names. *)
From New.checker Require Import prelude.
From New.checker.fn Require Import TypeSort.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_typeZero (lt : loc) (t : ctype) :
  {{{ is_pkg_init checker ∗ is_type lt t }}}
    @! checker.typeZero #lt
  {{{ (lz : loc), RET (#lz, #true); is_term lz (ctype_zero t) }}}.
Proof.
  wp_start as "#Ht".
  iApply wp_fupd.
  wp_auto.
  wp_apply (wp_TypeSort lt (Some t) with "[$]").
  destruct t; simpl; wp_auto;
    wp_alloc lz as "Hz"; iPersist "Hz"; wp_auto;
    iModIntro; iApply "HΦ"; iFrame "Hz".
Qed.

End proof.
