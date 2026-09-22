(** [checker.negate] (checker/exec.go): logical negation of a term, with the
    double negation cancelled.

    Note on naming: the Go function's only local is called [t], and [wp_auto]
    derives its identifiers from the Go name, so the Rocq variable holding the
    term is called [tm] here (see NOTES.md). *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The kind code [W64 17] belongs to [TNot] alone. *)
Lemma term_code_TNot (u : term) :
  term_code u = W64 17 → ∃ x, u = TNot x.
Proof.
  destruct u; simpl; try (intros ?; by eauto);
    try destruct signed; intros Hc; exfalso; revert Hc; by vm_compute.
Qed.

(** ... so every other node is negated by wrapping it. *)
Lemma negate_not_TNot (u : term) :
  term_code u ≠ W64 17 → negate u = TNot u.
Proof. destruct u; simpl; try done. Qed.

Lemma wp_negate (lt : loc) (t : term) :
  {{{ is_pkg_init checker ∗ is_term lt t }}}
    @! checker.negate #lt
  {{{ (l : loc), RET #l; is_term l (negate t) }}}.
Proof.
  rename t into tm.
  wp_start as "#Ht".
  iDestruct (is_term_node with "Ht") as (la lb lc) "(%Hwf & #Hn & #Ha & #Hb & #Hc)".
  wp_auto.
  wp_if_destruct.
  - (* [tm] is already a negation: the [A] child is returned as is *)
    destruct (term_code_TNot _ e) as [x ->]; simpl.
    iApply "HΦ". iFrame "Ha".
  - (* any other node: allocate a fresh [TNot] wrapper *)
    rewrite (negate_not_TNot _ n).
    iApply wp_fupd.
    wp_alloc l as "Hl".
    wp_auto.
    iPersist "Hl".
    iModIntro. iApply "HΦ". simpl. iFrame "Hl Ht".
Qed.

End proof.
