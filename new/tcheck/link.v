(** * Tactics for proving a table's rules valid

    A rule's validity, [rule_valid D r], computes to the Hoare triple it
    stands for, in the form [{{{ P }}} e {{{ x .. y, RET v; Q }}}] unfolds
    to.  [tc_simp] performs exactly that computation and nothing else: it
    unfolds the checker's denotation (this library) but not the Gallina the
    table's denotation maps symbols to, so the goal ends up stated in the
    vocabulary of the lemma the rule is linked to.  A generated table file
    defines [<table>_unfold], which unfolds its own definitions first.

    [rule_start] then introduces the ambient setting, the package
    assumptions and the rule's variables. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.tcheck Require Export observe.

Ltac tc_simp :=
  lazy beta iota zeta delta [rule_valid fact_valid preds_valid spec_valid every_ambient
       forall_sorts bi_forall_sorts triple_at val_den type_den as_val teval vals_of sym_apply
       cast nat_cast atom_den assn_den pat_den lookup_sym lookup_pred sd_args sd_res pd_args
       pd_pers d_at d_pkg d_sort d_sym d_pred List.map List.nth_error app pers_obl pers_ok
       srt_den arrows sym_ty pred_ty r_vars r_lhs r_pre r_ex r_ret r_post f_vars f_lhs f_rhs
       projT1 projT2 sp_vars sp_args sp_pre sp_ex sp_ret sp_post apply_vals foldl].

Ltac tc_simp_in H :=
  lazy beta iota zeta delta [rule_valid fact_valid preds_valid spec_valid every_ambient
       forall_sorts bi_forall_sorts triple_at val_den type_den as_val teval vals_of sym_apply
       cast nat_cast atom_den assn_den pat_den lookup_sym lookup_pred sd_args sd_res pd_args
       pd_pers d_at d_pkg d_sort d_sym d_pred List.map List.nth_error app pers_obl pers_ok
       srt_den arrows sym_ty pred_ty r_vars r_lhs r_pre r_ex r_ret r_post f_vars f_lhs f_rhs
       projT1 projT2 sp_vars sp_args sp_pre sp_ex sp_ret sp_post apply_vals foldl] in H.

(** Introduce everything up to the triple; [unf] unfolds the table. *)
Ltac rule_start unf :=
  unf; tc_simp;
  intros ext ffi ffi_interp0 Σ hG ffi_semantics0 sem package_sem;
  intros.

(** A pure step, by [wp_pures]. *)
Ltac rule_pure :=
  iIntros "_ HΦ"; wp_pures; by iApply "HΦ".

(** The persistence obligations, by instance search. *)
Ltac preds_persistent :=
  repeat match goal with
         | |- _ ∧ _ => split
         | |- True => exact I
         | |- ∀ _, _ => intros
         | |- _ => apply _
         end.

(** [Forall P l], each element by [tac]. *)
Ltac forall_by tac :=
  lazymatch goal with
  | |- Forall ?P ?l =>
      let l' := eval hnf in l in
      lazymatch l' with
      | [] => apply Forall_nil_2
      | _ :: _ => change (Forall P l'); apply Forall_cons_2; [tac | forall_by tac]
      end
  end.

(** [table_valid D rs fs], given the persistence obligations [pers]: every
    rule and fact by [tac] (typically [auto with] the hint database of the
    table's link, which also sees the context, e.g. the rules for
    callees). *)
Ltac table_valid_by pers tac :=
  split; [forall_by tac | split; [forall_by tac | exact pers]].

(** From the checker's triple, about [impl #r a b], to a method call
    [r @! T @! m a b]: one rewrite and one β-step with [impl] abstract, so
    that the method's body is never unfolded. *)
Lemma wp_method_call_2 `{hG: heapGS Σ, !ffi_semantics _ _} {sem : go.Semantics}
    (T : go.type) (m : go_string) (impl : val) `{!MethodUnfold T m impl} (r : loc) (a b : val) Φ :
  WP App (App (App (Val impl) (Val #r)) (Val a)) (Val b) {{ Φ }} ⊢
  WP App (App (Val #(methods T m #r)) (Val a)) (Val b) {{ Φ }}.
Proof. iIntros "H". rewrite method_unfold. wp_pure. iExact "H". Qed.
