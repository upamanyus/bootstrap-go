(** [checker.termEq] (checker/term.go): structural equality of two terms. *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma term_eq_iff ta tb :
  term_idx_wf ta → term_idx_wf tb →
  (ta = tb ↔ term_code ta = term_code tb ∧ term_num ta = term_num tb ∧
             term_a ta = term_a tb ∧ term_b ta = term_b tb ∧ term_c ta = term_c tb).
Proof.
  intros Hwa Hwb. split; first by intros ->.
  destruct ta, tb; simpl in *;
    repeat match goal with b : bool |- _ => destruct b end;
    intros (Hc & Hn & Ha & Hb & Hc2);
    try (exfalso; revert Hc; by vm_compute);
    try (exfalso; revert Hn; by vm_compute);
    try congruence.
Qed.

End proof.
