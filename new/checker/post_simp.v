(** Reading an interpreted assertion as an ordinary Iris assertion, by
    computation.

    [assn_interp V a] (defs.v) evaluates the checker's terms: a pure atom
    [⌜t⌝] becomes [⌜teval V t = bval true⌝]. [assn_interp_simp] is the same
    interpretation with each atom read directly as the proposition it stands
    for ([pure_meaning]): [x <u y] as [uint.Z x < uint.Z y], [¬ (y <u x)] as
    [uint.Z x ≤ uint.Z y], [t == t'] as an equation, and so on.
    [assn_interp_simp_eq] says the two agree, once and for all. So a proof
    that has [assn_interp V a] for a concrete [a] and a concrete valuation
    rewrites with [assn_interp_simp_eq] and lets [simpl] compute the ordinary
    statement, with no case analysis and no arithmetic. *)
From New.checker Require Import prelude.

Section pure_meaning.
Context {ext : ffi_syntax}.

(** [P x y], if [v1] and [v2] are the integers [x] and [y]. *)
Definition int_rel (v1 v2 : val) (P : w64 → w64 → Prop) : Prop :=
  match v1, v2 with
  | LitV (LitInt x), LitV (LitInt y) => P x y
  | _, _ => False
  end.

(** What [teval V t = bval true] says, for the atoms the checker's surface
    syntax produces; anything else is left as it is. *)
Definition pure_meaning (V : valuation) (t : term) : Prop :=
  match t with
  | TLt sg a b => int_rel (teval V a) (teval V b)
      (λ x y, if sg then sint.Z x < sint.Z y else uint.Z x < uint.Z y)
  | TLe sg a b => int_rel (teval V a) (teval V b)
      (λ x y, if sg then sint.Z x ≤ sint.Z y else uint.Z x ≤ uint.Z y)
  | TNot (TLt sg a b) => int_rel (teval V a) (teval V b)
      (λ x y, if sg then sint.Z y ≤ sint.Z x else uint.Z y ≤ uint.Z x)
  | TNot (TLe sg a b) => int_rel (teval V a) (teval V b)
      (λ x y, if sg then sint.Z y < sint.Z x else uint.Z y < uint.Z x)
  | TEq a b => teval V a = teval V b
  | TBool b => b = true
  | _ => teval V t = bval true
  end.

Lemma bval_eq_true (x : bool) : bval x = bval true ↔ x = true.
Proof. split; [by intros [= ->]|by intros ->]. Qed.

Lemma teval_lt_true V sg a b :
  teval V (TLt sg a b) = bval true ↔ pure_meaning V (TLt sg a b).
Proof.
  cbn [teval pure_meaning]; rewrite /int_rel.
  destruct (teval V a) as [la| | | | | | | | | | |]; try (split; [discriminate|done]);
    destruct la; try (split; [discriminate|done]);
  destruct (teval V b) as [lb| | | | | | | | | | |]; try (split; [discriminate|done]);
    destruct lb; try (split; [discriminate|done]).
  rewrite bval_eq_true. destruct sg; apply bool_decide_eq_true.
Qed.

Lemma teval_le_true V sg a b :
  teval V (TLe sg a b) = bval true ↔ pure_meaning V (TLe sg a b).
Proof.
  cbn [teval pure_meaning]; rewrite /int_rel.
  destruct (teval V a) as [la| | | | | | | | | | |]; try (split; [discriminate|done]);
    destruct la; try (split; [discriminate|done]);
  destruct (teval V b) as [lb| | | | | | | | | | |]; try (split; [discriminate|done]);
    destruct lb; try (split; [discriminate|done]).
  rewrite bval_eq_true. destruct sg; apply bool_decide_eq_true.
Qed.

Lemma teval_not_lt_true V sg a b :
  teval V (TNot (TLt sg a b)) = bval true ↔ pure_meaning V (TNot (TLt sg a b)).
Proof.
  cbn [teval pure_meaning]; rewrite /int_rel.
  destruct (teval V a) as [la| | | | | | | | | | |]; try (split; [discriminate|done]);
    destruct la; try (split; [discriminate|done]);
  destruct (teval V b) as [lb| | | | | | | | | | |]; try (split; [discriminate|done]);
    destruct lb; try (split; [discriminate|done]).
  rewrite /= bval_eq_true negb_true_iff. destruct sg; rewrite /cmp_lt bool_decide_eq_false; lia.
Qed.

Lemma teval_not_le_true V sg a b :
  teval V (TNot (TLe sg a b)) = bval true ↔ pure_meaning V (TNot (TLe sg a b)).
Proof.
  cbn [teval pure_meaning]; rewrite /int_rel.
  destruct (teval V a) as [la| | | | | | | | | | |]; try (split; [discriminate|done]);
    destruct la; try (split; [discriminate|done]);
  destruct (teval V b) as [lb| | | | | | | | | | |]; try (split; [discriminate|done]);
    destruct lb; try (split; [discriminate|done]).
  rewrite /= bval_eq_true negb_true_iff. destruct sg; rewrite /cmp_le bool_decide_eq_false; lia.
Qed.

Lemma pure_meaning_iff V t : teval V t = bval true ↔ pure_meaning V t.
Proof.
  destruct t as [| | | |b| | | | | | |a b|sg a b|sg a b|t| | |]; try reflexivity.
  - apply bval_eq_true.
  - rewrite /= bval_eq_true. apply bool_decide_eq_true.
  - apply teval_lt_true.
  - apply teval_le_true.
  - destruct t; try reflexivity; [apply teval_not_lt_true|apply teval_not_le_true].
Qed.

End pure_meaning.

Section assn_interp_simp.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Fixpoint assn_interp_simp (V : valuation) (a : cassn) : iProp Σ :=
  match a with
  | CAEmp => True
  | CASep p q => assn_interp_simp V p ∗ assn_interp_simp V q
  | CAOr p q => assn_interp_simp V p ∨ assn_interp_simp V q
  | CAExists n s p => ∃ w : val, ⌜has_sort w s⌝ ∗ assn_interp_simp (upd_pat V n w) p
  | CAPure t => ⌜pure_meaning V t⌝
  | CAPointsTo l v => ∃ lo : loc, ⌜teval V l = lval lo⌝ ∗ heap_pointsto lo (DfracOwn 1) (teval V v)
  end%I.

Lemma assn_interp_simp_eq V a : assn_interp V a ⊣⊢ assn_interp_simp V a.
Proof.
  revert V. induction a as [|p IHp q IHq|p IHp q IHq|n s p IHp|t|l v]; intros V; simpl.
  - done.
  - by rewrite IHp IHq.
  - by rewrite IHp IHq.
  - by setoid_rewrite IHp.
  - apply bi.pure_proper, pure_meaning_iff.
  - done.
Qed.

End assn_interp_simp.
