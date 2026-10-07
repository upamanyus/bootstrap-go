/-
Port of `new/proof/go_etcd_io/raft/tcheck/proof_raft__becomeFollower.v`.

# `becomeFollower`, from one observed run of the table-driven checker

The Go checker (tcheck/) ran on `becomeFollower` with the rules of
raft.tbl; `Observed/raft__becomeFollower.lean` records that run
(OBSERVE-EXECUTION) and concludes `input_holds` of it.

`raft.becomeFollower.wp_proof` establishes etcdGrove's own statement,
`raft.becomeFollower.spec` (`EtcdGrove/Raft/ElectionProof/Spec/
raft__becomeFollower.lean`, imported, not restated), from that run, with the
callees' specs as hypotheses (etcdGrove's notes/decisions.md, "The Rocq
module discipline, in Lean"): it supplies the validity of the rules the run
used (the shared ones from `LinkTableRaft.lean`, the callees' from the
hypotheses), applies `spec_rule_valid` (`Link.lean`, proved once for every
function) to get the rule callers use, `raft_rule_becomeFollower`, and that
rule *is* the spec, by conversion.

Trusted beyond the hand-written proofs: `check_adequate` (the checker's
soundness, `Checkers/TCheck/Observe.lean`, not yet proved) and the
observation `becomeFollower_check_run`.

Lean notes: Rocq's two functors (`BecomeFollowerObserved`, from the
postulates to the rule; `BecomeFollowerOfRule`, from the rule to the
hand-written `BECOMEFOLLOWER`) are one theorem, since the spec is the rule
up to unfolding; `raft_rule_becomeFollower_ok` is kept, for callers checked
by tcheck. The callee hypotheses are etcdGrove's `raft.reset.spec` and
`traceBecomeFollower.spec`, the two `Include`s of Rocq's
`BECOMEFOLLOWER_POSTULATES`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.raft__becomeFollower
import EtcdGrove.Raft.ElectionProof.Spec.raft__reset
import EtcdGrove.Raft.ElectionProof.Spec.traceBecomeFollower
import Checkers.TCheck.Raft.LinkTableRaft
import Checkers.TCheck.Raft.Observed.raft__becomeFollower

noncomputable section

namespace Perennial
namespace TCheck

open Iris Iris.BI EtcdGrove go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The rules the run used, valid: the shared ones from the link file, the
callees' from their specs (each the rule's statement, up to unfolding). -/
theorem becomeFollower_table_ok
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeFollower : traceBecomeFollower.spec (GF := GF) (hG := hG)) :
    table_valid (raft_den (hG := hG)) becomeFollower_rules becomeFollower_facts :=
  ⟨⟨raft_rule_alloc_loc_ok, raft_rule_alloc_w64_ok, raft_rule_load_loc_ok, raft_rule_load_w64_ok,
    raft_rule_sfr_step_ok, raft_rule_sfr_tick_ok, raft_rule_sfr_lead_ok, raft_rule_sfr_state_ok,
    raft_rule_sfr_id_ok, raft_rule_sfr_Term_ok, raft_rule_sfr_logger_ok,
    raft_rule_fr_stepFollower_ok, raft_rule_fr_traceBecomeFollower_ok, raft_rule_mr_reset_ok,
    raft_rule_mr_tickElection_ok, raft_rule_mr_Infof_ok, raft_rule_conv_u64_iface_ok,
    raft_rule_store_step_ok, raft_rule_store_tick_ok, raft_rule_store_lead_ok,
    raft_rule_store_state_Follower_ok, raft_rule_load_id_ok, raft_rule_load_Term_ok,
    raft_rule_load_logger_ok, raft_rule_slice_lit_u64_u64_ok,
    raft_rule_logf_Infof_becomeFollower_ok,
    (wp_raft_reset : rule_valid (raft_den (hG := hG)) raft_rule_reset),
    (wp_traceBecomeFollower : rule_valid (raft_den (hG := hG)) raft_rule_traceBecomeFollower),
    trivial⟩,
   ⟨raft_fact_become_follower_ok, trivial⟩,
   raft_preds_ok⟩

/-- The run, read as the rule callers use. -/
theorem raft_rule_becomeFollower_ok
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeFollower : traceBecomeFollower.spec (GF := GF) (hG := hG)) :
    rule_valid (raft_den (hG := hG)) raft_rule_becomeFollower :=
  spec_rule_valid _ _ _ _
    (becomeFollower_holds (raft_den (hG := hG))
      (becomeFollower_table_ok wp_raft_reset wp_traceBecomeFollower))
    becomeFollower_call_ok

/-- etcdGrove's specification of `becomeFollower`: the rule, by conversion. -/
theorem raft.becomeFollower.wp_proof
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeFollower : traceBecomeFollower.spec (GF := GF) (hG := hG)) :
    raft.becomeFollower.spec (GF := GF) (hG := hG) :=
  raft_rule_becomeFollower_ok wp_raft_reset wp_traceBecomeFollower

end proof

end TCheck
end Perennial
