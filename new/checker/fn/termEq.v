(** [checker.termEq] (checker/term.go): structural equality of two terms. *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All - package_sem".

(** The kind code as a [nat], so that the 18x18 case analysis below can
    discharge the impossible cases with [discriminate] instead of a [w64]
    computation. *)
Local Definition tcode (t : term) : nat :=
  match t with
  | TVar _ => 1 | TPat _ => 2 | TResult => 3 | TInt _ => 4
  | TBool _ => 5 | TUnit => 6 | TNull => 7
  | TPlus _ _ => 8 | TMinus _ _ => 9 | TMul _ _ => 10
  | TNeg _ => 11 | TEq _ _ => 12
  | TLt sg _ _ => (if sg then 13 else 14)%nat
  | TLe sg _ _ => (if sg then 15 else 16)%nat
  | TNot _ => 17 | TIte _ _ _ => 18 | TExec => 19 | TRet _ => 20
  end.

Local Definition ucode (w : w64) : nat := uint.nat w.

Local Lemma tcode_term_code t : ucode (term_code t) = tcode t.
Proof. destruct t; simpl; try (by vm_compute); destruct signed; by vm_compute. Qed.

Lemma term_eq_iff ta tb :
  term_idx_wf ta → term_idx_wf tb →
  (ta = tb ↔ term_code ta = term_code tb ∧ term_num ta = term_num tb ∧
             term_a ta = term_a tb ∧ term_b ta = term_b tb ∧ term_c ta = term_c tb).
Proof.
  intros Hwa Hwb. split; first by intros ->.
  intros (Hc & Hn & Ha & Hb & Hc2).
  apply (f_equal ucode) in Hc. rewrite !tcode_term_code in Hc.
  destruct ta, tb;
    repeat match goal with sg : bool |- _ => destruct sg end;
    simpl in *; try discriminate; try congruence.
Qed.

(** The recursion runs into the [A]/[B]/[C] fields, which are [null] wherever
    the constructor has no child there, so the specification has to talk about
    a possibly absent term.

    Note on naming: no Rocq variable here may be called [a] or [b], because
    those are the names of the Go function's own locals and [wp_auto] derives
    Rocq identifiers from them. *)
Lemma wp_termEq (la lb : loc) (oa ob : option term) :
  {{{ is_pkg_init checker ∗ is_oterm la oa ∗ is_oterm lb ob }}}
    @! checker.termEq #la #lb
  {{{ RET #(bool_decide (oa = ob)); True }}}.
Proof using All.
  iLöb as "IH" forall (la lb oa ob).
  wp_start as "[#Hoa #Hob]".
  iDestruct (is_oterm_null with "Hoa") as %Hna.
  iDestruct (is_oterm_null with "Hob") as %Hnb.
  wp_auto.
  wp_if_destruct.
  - (* the first argument is nil *)
    assert (oa = None) as -> by naive_solver.
    try wp_auto.
    destruct ob as [tb|]; simpl.
    + iDestruct (is_term_not_null with "Hob") as %?.
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
      iDestruct (is_term_node with "Hoa") as (laa lab lac) "(%Hwa & #Hn1 & #Haa & #Hab & #Hac)".
      iDestruct (is_term_node with "Hob") as (lba lbb lbc) "(%Hwb & #Hn2 & #Hba & #Hbb & #Hbc)".
      try wp_auto.
      wp_if_destruct.
      * (* the kind codes agree *)
        try wp_auto. wp_if_destruct.
        ** (* the [Num] fields agree: recurse into the three children *)
           wp_apply ("IH" $! laa lba (term_a ta) (term_a tb) with "[$]").
           wp_if_destruct.
           *** wp_apply ("IH" $! lab lbb (term_b ta) (term_b tb) with "[$]").
               wp_if_destruct.
               **** wp_apply ("IH" $! lac lbc (term_c ta) (term_c tb) with "[$]").
                    assert (term_c ta = term_c tb ↔ Some ta = Some tb) as Hiff.
                    { split.
                      - intros Hcc. f_equal. apply term_eq_iff; done.
                      - intros [= ->]. done. }
                    rewrite (bool_decide_ext _ _ Hiff). by iApply "HΦ".
               **** rewrite (bool_decide_eq_false_2 (Some ta = Some tb));
                      last by intros [= ->].
                    by iApply "HΦ".
           *** rewrite (bool_decide_eq_false_2 (Some ta = Some tb));
                 last by intros [= ->].
               by iApply "HΦ".
        ** (* the [Num] fields differ *)
           rewrite (bool_decide_eq_false_2 (Some ta = Some tb));
             last by intros [= ->].
           by iApply "HΦ".
      * (* the kind codes differ *)
        rewrite (bool_decide_eq_false_2 (Some ta = Some tb));
          last by intros [= ->].
        by iApply "HΦ".
Qed.

End proof.
