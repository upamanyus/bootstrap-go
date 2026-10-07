/-
# `becomeFollower`, by the Lean table checker (reflection)

The same specification as `Proof/raft__becomeFollower.lean` -- etcdGrove's
own `raft.becomeFollower.spec`, with the callee specs as hypotheses -- but
with the table-driven checker run in Lean (`ltcheck`, LCheck/TCheck/Check.lean)
on the same input, instead of observing a run of the Go checker. Its
soundness is a theorem (`ltcheck_sound`, Checkers/TCheck/Reflect/Sound.lean),
so neither the observation `becomeFollower_check_run` nor the Go checker's
soundness axiom `check_adequate` is used:

* `becomeFollower_holds_kernel`: `input_holds`, with `ltcheck` evaluated by
  the kernel (`decide +kernel`); nothing is trusted beyond Lean's kernel;
* `becomeFollower_holds_native`: the same, with `ltcheck` evaluated by
  `native_decide` (compiled code: `LCheck` is precompiled), at the cost of
  the axiom `native_decide` adds.

`raft.becomeFollower.wp_proof_reflect` is etcdGrove's specification from the
kernel version; `#print axioms` lists etcdGrove's and Perennial's own and
Lean's three, and no axiom of this repository.

The input (`becomeFollower_input`), its fidelity check (`becomeFollower_func_val`,
by `rfl`), `becomeFollower_call_ok` and the rules' validity
(`becomeFollower_table_ok`) are the observed proof's, reused: only the axiom
`becomeFollower_check_run` of `Observed/raft__becomeFollower.lean` is left
out. `gocheck/tcheck/reflect_bench.sh` times the two against it.
-/
import Checkers.TCheck.Reflect.Sound
import Checkers.TCheck.Raft.Proof.raft__becomeFollower

noncomputable section

namespace Perennial
namespace TCheck

open Iris Iris.BI EtcdGrove go_etcd_io.raft.v3

theorem becomeFollower_holds_kernel : input_holds becomeFollower_input :=
  LC.ltcheck_sound _ (by decide +kernel)

theorem becomeFollower_holds_native : input_holds becomeFollower_input :=
  LC.ltcheck_sound _ (by native_decide)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The rule callers use, from the Lean checker's run. -/
theorem raft_rule_becomeFollower_ok_reflect
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeFollower : traceBecomeFollower.spec (GF := GF) (hG := hG)) :
    rule_valid (raft_den (hG := hG)) raft_rule_becomeFollower :=
  spec_rule_valid _ _ _ _
    (becomeFollower_holds_kernel (raft_den (hG := hG))
      (becomeFollower_table_ok wp_raft_reset wp_traceBecomeFollower))
    becomeFollower_call_ok

/-- etcdGrove's specification of `becomeFollower`, by reflection. -/
theorem raft.becomeFollower.wp_proof_reflect
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeFollower : traceBecomeFollower.spec (GF := GF) (hG := hG)) :
    raft.becomeFollower.spec (GF := GF) (hG := hG) :=
  raft_rule_becomeFollower_ok_reflect wp_raft_reset wp_traceBecomeFollower

end proof

end TCheck
end Perennial
