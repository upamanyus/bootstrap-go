(** * [becomeFollower], from one observed run of the table-driven checker

    The Go checker (tcheck/) ran on [becomeFollower] with the rules of
    raft.tbl; observed_raft__becomeFollower.v records that run
    (OBSERVE-EXECUTION) and concludes [input_holds] of it.

    - [BecomeFollowerObserved] turns the run into the rule callers use,
      [raft_rule_becomeFollower] (the call [r @! raft @! "becomeFollower"],
      table_raft.v): it supplies the validity of the rules the run used
      (the shared ones from link_table_raft.v, the callees' from the
      postulates) and applies [spec_rule_valid], which is proved once for
      every function.  A caller checked by tcheck uses the rule as is.
    - [BecomeFollowerOfRule] gives back the hand-written [BECOMEFOLLOWER]
      statement, by conversion alone, for callers proved by hand.

    Trusted beyond the hand-written proof (election_proof/): [check_adequate]
    (the checker's soundness, new/tcheck/observe.v, not yet proved) and the
    observation [becomeFollower_check_run]. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeFollower.
From New.proof.go_etcd_io.raft.tcheck Require Import link_table_raft observed_raft__becomeFollower.

Module BecomeFollowerObserved (P : BECOMEFOLLOWER_POSTULATES) : RAFT_RULE_BECOMEFOLLOWER.
Import P.

  (** The rules for callees, from the postulates. *)
  Lemma raft_rule_reset_ok : rule_valid raft_den raft_rule_reset.
  Proof. rule_start raft_unfold. apply P.wp_raft__reset. Qed.
  Lemma raft_rule_traceBecomeFollower_ok : rule_valid raft_den raft_rule_traceBecomeFollower.
  Proof. rule_start raft_unfold. apply P.wp_traceBecomeFollower. Qed.

  Lemma table_ok : table_valid raft_den becomeFollower_rules becomeFollower_facts.
  Proof.
    pose proof raft_rule_reset_ok. pose proof raft_rule_traceBecomeFollower_ok.
    table_valid_by raft_preds_ok ltac:(solve [auto with raft_rules]).
  Qed.

  (** The run, read as the rule callers use. *)
  Lemma raft_rule_becomeFollower_ok : rule_valid raft_den raft_rule_becomeFollower.
  Proof. exact (spec_rule_valid _ _ _ _ (becomeFollower_holds raft_den table_ok) becomeFollower_call_ok). Qed.

End BecomeFollowerObserved.

(** The rule gives the hand-written statement back, for code that still
    depends on [BECOMEFOLLOWER]. *)
Module BecomeFollowerOfRule (R : RAFT_RULE_BECOMEFOLLOWER) : BECOMEFOLLOWER.
  Lemma wp_raft__becomeFollower : wp_raft__becomeFollower_body.
  Proof.
    intros_ambient. intros cfg r id s term lead.
    exact (R.raft_rule_becomeFollower_ok ext ffi ffi_interp0 Σ hG ffi_semantics0 sem package_sem
             cfg r id s term lead).
  Qed.
End BecomeFollowerOfRule.
