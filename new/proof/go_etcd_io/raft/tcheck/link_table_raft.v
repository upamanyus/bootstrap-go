(** * The raft table's rules, linked to the lemmas they come from

    One lemma per rule and fact of raft.tbl (except the rules for callees,
    [reset] and [traceBecomeFollower], which are linked to the postulates of
    the proof that uses them; see proof_raft__becomeFollower.v), plus the
    persistence of the predicates the table declares persistent.  Each goal,
    after [rule_start], is the Hoare triple the rule stands for, stated
    exactly as the lemma it is linked to. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.proof.go_etcd_io.raft.tcheck Require Export table_raft.

(** ** Locals *)

Lemma raft_rule_alloc_loc_ok : rule_valid raft_den raft_rule_alloc_loc.
Proof. rule_start raft_unfold. iIntros "_ HΦ". wp_apply wp_alloc. iIntros (l) "Hl". by iApply "HΦ". Qed.
Lemma raft_rule_alloc_w64_ok : rule_valid raft_den raft_rule_alloc_w64.
Proof. rule_start raft_unfold. iIntros "_ HΦ". wp_apply wp_alloc. iIntros (l) "Hl". by iApply "HΦ". Qed.
Lemma raft_rule_load_loc_ok : rule_valid raft_den raft_rule_load_loc.
Proof. rule_start raft_unfold. iIntros "Hl HΦ". wp_apply (wp_load with "Hl"). iIntros "Hl". by iApply "HΦ". Qed.
Lemma raft_rule_load_w64_ok : rule_valid raft_den raft_rule_load_w64.
Proof. rule_start raft_unfold. iIntros "Hl HΦ". wp_apply (wp_load with "Hl"). iIntros "Hl". by iApply "HΦ". Qed.

(** ** Pure steps *)

Lemma raft_rule_sfr_step_ok : rule_valid raft_den raft_rule_sfr_step.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_sfr_tick_ok : rule_valid raft_den raft_rule_sfr_tick.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_sfr_lead_ok : rule_valid raft_den raft_rule_sfr_lead.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_sfr_state_ok : rule_valid raft_den raft_rule_sfr_state.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_sfr_id_ok : rule_valid raft_den raft_rule_sfr_id.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_sfr_Term_ok : rule_valid raft_den raft_rule_sfr_Term.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_sfr_logger_ok : rule_valid raft_den raft_rule_sfr_logger.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_fr_stepFollower_ok : rule_valid raft_den raft_rule_fr_stepFollower.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_fr_traceBecomeFollower_ok : rule_valid raft_den raft_rule_fr_traceBecomeFollower.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_mr_reset_ok : rule_valid raft_den raft_rule_mr_reset.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_mr_tickElection_ok : rule_valid raft_den raft_rule_mr_tickElection.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_mr_Infof_ok : rule_valid raft_den raft_rule_mr_Infof.
Proof. rule_start raft_unfold. rule_pure. Qed.
Lemma raft_rule_conv_u64_iface_ok : rule_valid raft_den raft_rule_conv_u64_iface.
Proof. rule_start raft_unfold. rule_pure. Qed.

(** ** Fields of the raft struct (election_proof/inv_raft_phys.v) *)

Lemma raft_rule_store_step_ok : rule_valid raft_den raft_rule_store_step.
Proof. rule_start raft_unfold. apply wp_raft_store_step. Qed.
Lemma raft_rule_store_tick_ok : rule_valid raft_den raft_rule_store_tick.
Proof. rule_start raft_unfold. apply wp_raft_store_tick. Qed.
Lemma raft_rule_store_lead_ok : rule_valid raft_den raft_rule_store_lead.
Proof. rule_start raft_unfold. apply wp_raft_store_lead. Qed.
Lemma raft_rule_store_state_Follower_ok : rule_valid raft_den raft_rule_store_state_Follower.
Proof. rule_start raft_unfold. apply (wp_raft_store_state _ _ _ _ role.Follower). Qed.
Lemma raft_rule_load_id_ok : rule_valid raft_den raft_rule_load_id.
Proof. rule_start raft_unfold. apply wp_raft_load_id. Qed.
Lemma raft_rule_load_Term_ok : rule_valid raft_den raft_rule_load_Term.
Proof. rule_start raft_unfold. apply wp_raft_load_Term. Qed.
Lemma raft_rule_load_logger_ok : rule_valid raft_den raft_rule_load_logger.
Proof. rule_start raft_unfold. apply wp_raft_load_logger. Qed.

(** ** Logging (election_proof/inv_logger.v) *)

Lemma raft_rule_slice_lit_u64_u64_ok : rule_valid raft_den raft_rule_slice_lit_u64_u64.
Proof.
  rule_start raft_unfold. iIntros "_ HΦ".
  wp_apply wp_slice_literal. iSplitR; [done|]. iIntros (sl_ptr) "_". by iApply "HΦ".
Qed.
Lemma raft_rule_logf_Infof_becomeFollower_ok : rule_valid raft_den raft_rule_logf_Infof_becomeFollower.
Proof. rule_start raft_unfold. apply wp_Logger__logf. solve_log_method. Qed.

(** ** Facts *)

(** [become_follower] is the stores of [becomeFollower], in their order;
    as in the hand-written proof, by [destruct s] (and never [simpl]). *)
Lemma raft_fact_become_follower_ok : fact_valid raft_den raft_fact_become_follower.
Proof. rule_start raft_unfold. by destruct x. Qed.

(** ** Persistent predicates *)

Lemma raft_preds_ok : preds_valid raft_den.
Proof. rule_start raft_unfold. preds_persistent. Qed.

(** For [auto] when assembling [table_valid] for a function. *)
#[export] Hint Resolve
  raft_rule_alloc_loc_ok
  raft_rule_alloc_w64_ok
  raft_rule_load_loc_ok
  raft_rule_load_w64_ok
  raft_rule_sfr_step_ok
  raft_rule_sfr_tick_ok
  raft_rule_sfr_lead_ok
  raft_rule_sfr_state_ok
  raft_rule_sfr_id_ok
  raft_rule_sfr_Term_ok
  raft_rule_sfr_logger_ok
  raft_rule_fr_stepFollower_ok
  raft_rule_fr_traceBecomeFollower_ok
  raft_rule_mr_reset_ok
  raft_rule_mr_tickElection_ok
  raft_rule_mr_Infof_ok
  raft_rule_conv_u64_iface_ok
  raft_rule_store_step_ok
  raft_rule_store_tick_ok
  raft_rule_store_lead_ok
  raft_rule_store_state_Follower_ok
  raft_rule_load_id_ok
  raft_rule_load_Term_ok
  raft_rule_load_logger_ok
  raft_rule_slice_lit_u64_u64_ok
  raft_rule_logf_Infof_becomeFollower_ok
  raft_fact_become_follower_ok
  : raft_rules.
