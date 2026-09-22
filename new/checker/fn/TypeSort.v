(** [checker.TypeSort] (checker/sorts.go): the sort of a supported type.

    Note on naming: no Rocq variable here may be called [t], [s] or [ok],
    because those are the names of the Go function's own locals and [wp_auto]
    derives Rocq identifiers from them. *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** Every [ctype] is supported, so the [bool] result is [true] at every
    [Some]; the [None] case is the nil pointer, where the Go code answers
    [(SortInt, false)]. *)
Definition octype_sort (t : option ctype) : sort * bool :=
  match t with None => (SInt, false) | Some t' => (ctype_sort t', true) end.

Lemma wp_TypeSort (lt : loc) (ot : option ctype) :
  {{{ is_pkg_init checker ∗ is_otype lt ot }}}
    @! checker.TypeSort #lt
  {{{ RET (#(sort_code (octype_sort ot).1), #((octype_sort ot).2)); True }}}.
Proof.
  iLöb as "IH" forall (lt ot).
  wp_start as "#Hot".
  iDestruct (is_otype_null with "Hot") as %Hn.
  wp_auto.
  wp_if_destruct.
  - (* the argument is nil *)
    assert (ot = None) as -> by naive_solver.
    by iApply "HΦ".
  - destruct ot as [ty|]; last naive_solver.
    iDestruct (is_type_node with "Hot") as (le) "[#Hnode #Helem]".
    destruct ty; simpl.
    + wp_auto. by iApply "HΦ".
    + wp_auto. by iApply "HΦ".
    + wp_auto. by iApply "HΦ".
    + wp_auto. by iApply "HΦ".
    + wp_auto.
      wp_apply ("IH" $! le (Some ty) with "[$]").
      by iApply "HΦ".
Qed.

End proof.
