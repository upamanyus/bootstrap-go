/-
Port of `new/proof/go_etcd_io/raft/tcheck/link_table_raft.v`.

# The raft table's rules, linked to the lemmas they come from

One theorem per rule and fact of raft.tbl (except the rules for callees,
`reset` and `traceBecomeFollower`, which are linked to the callee specs the
proof that uses them takes as hypotheses; see
`Proof/raft__becomeFollower.lean`), plus the persistence of the predicates
the table declares persistent.  A rule's validity is, up to unfolding, the
Hoare triple it stands for, stated exactly as the lemma it is linked to, so
a link is the lemma's name.

Lean notes: the links to lemmas are terms (`:= raft.wp_store_step`),
checked by definitional unfolding of the rule's validity; there is no
`rule_start` before them, as Rocq needed. The locals are linked to
`IntoValTyped.wp_alloc`/`wp_load` (Rocq proved them with `wp_alloc`/`wp_load`
inline); the pure steps are `raft_rule_start; rule_pure` (`wp_auto`), and
the slice literal is proved with `wp_slice_literal`, as in Rocq. The
persistence obligations are an anonymous constructor of the two instances
(Rocq `preds_persistent`). The `reset` rule has the second conjunct of
etcdGrove's `raft.reset.spec` (predicate `reset_matched`), so that it is
that spec exactly.
-/
import Checkers.TCheck.Raft.TableRaft

noncomputable section

namespace Perennial
namespace TCheck

open Iris Iris.BI Iris.ProofMode EtcdGrove go_etcd_io.raft.v3

section link
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## Locals -/

theorem raft_rule_alloc_loc_ok : rule_valid (raft_den (hG := hG)) raft_rule_alloc_loc :=
  IntoValTyped.wp_alloc (t := go.GoType.PointerType raft.ty)
theorem raft_rule_alloc_w64_ok : rule_valid (raft_den (hG := hG)) raft_rule_alloc_w64 :=
  IntoValTyped.wp_alloc (t := go.uint64)
theorem raft_rule_load_loc_ok : rule_valid (raft_den (hG := hG)) raft_rule_load_loc :=
  fun l v => IntoValTyped.wp_load (t := go.GoType.PointerType raft.ty) l (DFrac.own 1) v
theorem raft_rule_load_w64_ok : rule_valid (raft_den (hG := hG)) raft_rule_load_w64 :=
  fun l v => IntoValTyped.wp_load (t := go.uint64) l (DFrac.own 1) v

/-! ## Pure steps -/

theorem raft_rule_sfr_step_ok : rule_valid (raft_den (hG := hG)) raft_rule_sfr_step := by
  raft_rule_start; rule_pure
theorem raft_rule_sfr_tick_ok : rule_valid (raft_den (hG := hG)) raft_rule_sfr_tick := by
  raft_rule_start; rule_pure
theorem raft_rule_sfr_lead_ok : rule_valid (raft_den (hG := hG)) raft_rule_sfr_lead := by
  raft_rule_start; rule_pure
theorem raft_rule_sfr_state_ok : rule_valid (raft_den (hG := hG)) raft_rule_sfr_state := by
  raft_rule_start; rule_pure
theorem raft_rule_sfr_id_ok : rule_valid (raft_den (hG := hG)) raft_rule_sfr_id := by
  raft_rule_start; rule_pure
theorem raft_rule_sfr_Term_ok : rule_valid (raft_den (hG := hG)) raft_rule_sfr_Term := by
  raft_rule_start; rule_pure
theorem raft_rule_sfr_logger_ok : rule_valid (raft_den (hG := hG)) raft_rule_sfr_logger := by
  raft_rule_start; rule_pure
theorem raft_rule_fr_stepFollower_ok :
    rule_valid (raft_den (hG := hG)) raft_rule_fr_stepFollower := by
  raft_rule_start; rule_pure
theorem raft_rule_fr_traceBecomeFollower_ok :
    rule_valid (raft_den (hG := hG)) raft_rule_fr_traceBecomeFollower := by
  raft_rule_start; rule_pure
theorem raft_rule_mr_reset_ok : rule_valid (raft_den (hG := hG)) raft_rule_mr_reset := by
  raft_rule_start; rule_pure
theorem raft_rule_mr_tickElection_ok :
    rule_valid (raft_den (hG := hG)) raft_rule_mr_tickElection := by
  raft_rule_start; rule_pure
theorem raft_rule_mr_Infof_ok : rule_valid (raft_den (hG := hG)) raft_rule_mr_Infof := by
  raft_rule_start; rule_pure
theorem raft_rule_conv_u64_iface_ok :
    rule_valid (raft_den (hG := hG)) raft_rule_conv_u64_iface := by
  raft_rule_start; rule_pure

/-! ## Fields of the raft struct (`InvRaftPhys.lean`) -/

theorem raft_rule_store_step_ok : rule_valid (raft_den (hG := hG)) raft_rule_store_step :=
  raft.wp_store_step
theorem raft_rule_store_tick_ok : rule_valid (raft_den (hG := hG)) raft_rule_store_tick :=
  raft.wp_store_tick
theorem raft_rule_store_lead_ok : rule_valid (raft_den (hG := hG)) raft_rule_store_lead :=
  raft.wp_store_lead
theorem raft_rule_store_state_Follower_ok :
    rule_valid (raft_den (hG := hG)) raft_rule_store_state_Follower :=
  fun cfg r id s => raft.wp_store_state cfg r id s .follower
theorem raft_rule_load_id_ok : rule_valid (raft_den (hG := hG)) raft_rule_load_id :=
  raft.wp_load_id
theorem raft_rule_load_Term_ok : rule_valid (raft_den (hG := hG)) raft_rule_load_Term :=
  raft.wp_load_Term
theorem raft_rule_load_logger_ok : rule_valid (raft_den (hG := hG)) raft_rule_load_logger :=
  raft.wp_load_logger

/-! ## Logging (`InvLogger.lean`) -/

theorem raft_rule_slice_lit_u64_u64_ok :
    rule_valid (raft_den (hG := hG)) raft_rule_slice_lit_u64_u64 := by
  raft_tc_simp
  intro a b
  iintro %Φ - HΦ
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType [])
    [interface.mkOk go.uint64 #a, interface.mkOk go.uint64 #b]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr -
  iapply HΦ
  itrivial

theorem raft_rule_logf_Infof_becomeFollower_ok :
    rule_valid (raft_den (hG := hG)) raft_rule_logf_Infof_becomeFollower :=
  fun l sl => Logger.wp_logf l go!"Infof" go!"%x became follower at term %d" sl (by simp [logMethods])

/-! ## Facts -/

/-- `becomeFollower` is the stores of `becomeFollower`, in their order. -/
theorem raft_fact_become_follower_ok : fact_valid (raft_den (hG := hG)) raft_fact_become_follower :=
  fun _ _ _ _ => rfl

/-! ## Persistent predicates -/

theorem raft_preds_ok : preds_valid (raft_den (hG := hG)) :=
  ⟨inferInstanceAs (Persistent (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3)),
   trivial, trivial, trivial, fun l => isLogger_persistent l, trivial, trivial⟩

end link

end TCheck
end Perennial
