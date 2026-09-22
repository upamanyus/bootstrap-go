(** [checker.TypeEq] (checker/sorts.go): structural equality of two types.

    Note on naming: no Rocq variable here may be called [a] or [b], because
    those are the names of the Go function's own locals and [wp_auto] derives
    Rocq identifiers from them. *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The recursion runs into the [Elem] field, which is [null] at every type
    but a pointer, so the specification has to talk about a possibly absent
    type. *)
Lemma wp_TypeEq (oa : option ctype) (la lb : loc) (ob : option ctype) :
  {{{ is_pkg_init checker ∗ is_otype la oa ∗ is_otype lb ob }}}
    @! checker.TypeEq #la #lb
  {{{ RET #(bool_decide (oa = ob)); True }}}.
Proof.
  iLöb as "IH" forall (oa la lb ob).
  wp_start as "[#Hoa #Hob]".
  iDestruct (is_otype_null with "Hoa") as %Hna.
  iDestruct (is_otype_null with "Hob") as %Hnb.
  wp_auto.
  wp_if_destruct.
  - (* the first argument is nil *)
    assert (oa = None) as -> by naive_solver.
    try wp_auto.
    destruct ob as [tb|]; simpl.
    + iDestruct (is_type_not_null with "Hob") as %?.
      rewrite bool_decide_eq_false_2; last done.
      by iApply "HΦ".
    + iDestruct "Hob" as %->.
      rewrite bool_decide_eq_true_2 //.
      by iApply "HΦ".
  - destruct oa as [ta|]; last naive_solver.
    try wp_auto. wp_if_destruct.
    + (* the second argument is nil *)
      assert (ob = None) as -> by naive_solver.
      rewrite bool_decide_eq_false_2; last done.
      by iApply "HΦ".
    + destruct ob as [tb|]; last naive_solver.
      iDestruct (is_type_node with "Hoa") as (lea) "[#Hna #Hea]".
      iDestruct (is_type_node with "Hob") as (leb) "[#Hnb2 #Heb]".
      try wp_auto.
      wp_if_destruct.
      * (* the kind codes agree: recurse into the element types *)
        wp_apply ("IH" $! (ctype_elem ta) lea leb (ctype_elem tb) with "[$]").
        assert (ctype_elem ta = ctype_elem tb ↔ Some ta = Some tb) as Hiff.
        { split.
          - intros He'. f_equal. apply ctype_eq_iff. split; done.
          - intros [= ->]. done. }
        rewrite (bool_decide_ext _ _ Hiff). by iApply "HΦ".
      * (* the kind codes differ *)
        rewrite (bool_decide_eq_false_2 (Some ta = Some tb));
          last by intros [= ->].
        by iApply "HΦ".
Qed.

End proof.
