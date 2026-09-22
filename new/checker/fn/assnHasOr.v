(** [checker.assnHasOr] (checker/check.go): does a disjunction occur anywhere
    in an assertion?

    Note on naming: no Rocq variable here may be called [a], the name of the
    Go function's own local, because [wp_auto] derives Rocq identifiers from
    the Go names. *)
From New.checker Require Import prelude nodes.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The Gallina mirror. The Go code recurses into [L] and [R] only, which is
    exactly [assn_l] and [assn_r]: an existential's body is its [L], and the
    atoms have no children at all. *)
Fixpoint cassn_has_or (x : cassn) : bool :=
  match x with
  | CAEmp => false
  | CASep p q => cassn_has_or p || cassn_has_or q
  | CAOr _ _ => true
  | CAExists _ _ p => cassn_has_or p
  | CAPure _ => false
  | CAPointsTo _ _ => false
  end.

Definition oassn_has_or (x : option cassn) : bool :=
  match x with None => false | Some x' => cassn_has_or x' end.

(** The two facts the proof needs about the mirror: an [AOr] node answers
    [true] outright, and every other node is the disjunction of its two
    children's answers. *)
Lemma oassn_has_or_or (x : cassn) : assn_code x = W64 3 → oassn_has_or (Some x) = true.
Proof. destruct x; simpl; intros H; try (exfalso; revert H; by vm_compute); done. Qed.

Lemma oassn_has_or_children (x : cassn) :
  assn_code x ≠ W64 3 →
  oassn_has_or (Some x) = oassn_has_or (assn_l x) || oassn_has_or (assn_r x).
Proof.
  destruct x; simpl; intros Hne; rewrite ?orb_false_r; try done; by destruct Hne.
Qed.

Lemma wp_assnHasOr (l : loc) (x : option cassn) :
  {{{ is_pkg_init checker ∗ is_oassn l x }}}
    @! checker.assnHasOr #l
  {{{ RET #(oassn_has_or x); True }}}.
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
    + (* an AOr right here *)
      rewrite (oassn_has_or_or x') //.
      by iApply "HΦ".
    + (* otherwise recurse into L, then into R *)
      rewrite (oassn_has_or_children x') //.
      try wp_auto.
      wp_apply ("IH" $! lL (assn_l x') with "[$]").
      destruct (oassn_has_or (assn_l x')); simpl.
      * try wp_auto. by iApply "HΦ".
      * try wp_auto.
        wp_apply ("IH" $! lR (assn_r x') with "[$]").
        by iApply "HΦ".
Qed.

End proof.
