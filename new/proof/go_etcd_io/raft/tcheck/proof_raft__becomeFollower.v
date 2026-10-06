(** * [becomeFollower], from one observed run of the table-driven checker

    A drop-in alternative to election_proof/proof_raft__becomeFollower.v:
    the same functor signature ([BECOMEFOLLOWER_POSTULATES] to
    [BECOMEFOLLOWER]), so the same specification, established differently.
    The Go checker (tcheck/) ran on [becomeFollower] with the rules of
    raft.tbl; observed_raft__becomeFollower.v records that run
    (OBSERVE-EXECUTION) and concludes [input_holds].  What is left here is
    to supply the rules' validity -- the shared rules from
    link_table_raft.v, the two callee rules from the postulates -- and to
    read the specification off the run: one method-call step, and the
    checker's function shown to be Goose's by [reflexivity].

    Trusted beyond the hand-written proof: [check_adequate] (the checker's
    soundness, new/tcheck/observe.v, not yet proved) and the observation
    [becomeFollower_check_run]. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeFollower.
From New.proof.go_etcd_io.raft.tcheck Require Import link_table_raft observed_raft__becomeFollower.

Module BecomeFollowerObserved (P : BECOMEFOLLOWER_POSTULATES) : BECOMEFOLLOWER.
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

  (** The checker's function is Goose's. *)
  Lemma becomeFollower_func_val (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
      (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
      (sem : go.Semantics) (pkg : raft.Assumptions) :
    func_val (raft_den.(d_at) ext ffi ffi_interp0 Σ hG ffi_semantics0 sem pkg) becomeFollower_func =
      raft.raft__becomeFollowerⁱᵐᵖˡ.
  Proof.
    vm_compute. reflexivity.
  Qed.

  Lemma wp_raft__becomeFollower : wp_raft__becomeFollower_body.
  Proof.
    intros_ambient. intros cfg r id s term lead.
    have H := becomeFollower_holds raft_den table_ok.
    specialize (H ext ffi ffi_interp0 Σ hG ffi_semantics0 sem package_sem).
    cbv beta in H. rewrite becomeFollower_func_val in H.
    unfold becomeFollower_input, becomeFollower_spec in H. cbn [in_func in_spec] in H.
    unfold raft_den, raft_sym, raft_sort, raft_pred, raft_syms, raft_preds in H. tc_simp_in H.
    specialize (H cfg r id s term lead).
    iIntros (Φ) "Hpre HΦ".
    iApply wp_method_call_2.
    iApply (H with "Hpre"). iModIntro. iExact "HΦ".
  Qed.

End BecomeFollowerObserved.
