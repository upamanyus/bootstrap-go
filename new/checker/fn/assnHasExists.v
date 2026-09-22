(** [checker.assnHasExists] (checker/check.go): does an existential occur
    anywhere in an assertion?

    Note on naming: no Rocq variable here may be called [a], the name of the
    Go function's own local, because [wp_auto] derives Rocq identifiers from
    the Go names. *)
From New.checker Require Import prelude nodes.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The Gallina mirror. As in [assnHasOr] the Go code recurses into [L] and
    [R] only ([assn_l] and [assn_r]); an [AExists] answers [true] without
    looking at its body. *)
Fixpoint cassn_has_exists (x : cassn) : bool :=
  match x with
  | CAEmp => false
  | CASep p q => cassn_has_exists p || cassn_has_exists q
  | CAOr p q => cassn_has_exists p || cassn_has_exists q
  | CAExists _ _ _ => true
  | CAPure _ => false
  | CAPointsTo _ _ => false
  end.

Definition oassn_has_exists (x : option cassn) : bool :=
  match x with None => false | Some x' => cassn_has_exists x' end.

Lemma oassn_has_exists_exists (x : cassn) :
  assn_code x = W64 4 → oassn_has_exists (Some x) = true.
Proof. destruct x; simpl; intros H; try (exfalso; revert H; by vm_compute); done. Qed.

Lemma oassn_has_exists_children (x : cassn) :
  assn_code x ≠ W64 4 →
  oassn_has_exists (Some x) = oassn_has_exists (assn_l x) || oassn_has_exists (assn_r x).
Proof.
  destruct x; simpl; intros Hne; rewrite ?orb_false_r; try done; by destruct Hne.
Qed.

Lemma wp_assnHasExists (l : loc) (x : option cassn) :
  {{{ is_pkg_init checker ∗ is_oassn l x }}}
    @! checker.assnHasExists #l
  {{{ RET #(oassn_has_exists x); True }}}.
Proof.
  iLöb as "IH" forall (l x).
  wp_start as "#Hx".
  iDestruct (is_oassn_null with "Hx") as %Hn.
  wp_auto.
  wp_if_destruct.
  - (* the argument is nil *)
    assert (x = None) as -> by naive_solver.
    by iApply "HΦ".
  - destruct x as [x'|]; last naive_solver.
    iDestruct (is_assn_node with "Hx") as (lL lR lX lY) "(%Hwf & #Hnode & #HL & #HR & _)".
    try wp_auto.
    wp_if_destruct.
    + (* an AExists right here *)
      rewrite (oassn_has_exists_exists x') //.
      by iApply "HΦ".
    + (* otherwise recurse into L, then into R *)
      rewrite (oassn_has_exists_children x') //.
      try wp_auto.
      wp_apply ("IH" $! lL (assn_l x') with "[$]").
      destruct (oassn_has_exists (assn_l x')); simpl.
      * try wp_auto. by iApply "HΦ".
      * try wp_auto.
        wp_apply ("IH" $! lR (assn_r x') with "[$]").
        by iApply "HΦ".
Qed.

End proof.
