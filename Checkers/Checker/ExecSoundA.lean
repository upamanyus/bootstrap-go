/-
Port of `new/checker/exec_sound_a.v`.

Semantic lemmas for the value, conversion and exception-monad cases of
`exec` (fn/execInt.v, ..., fn/execExcSeq.v), in the style of
exec_spec.v: `exec_sound_at_convert`, `exec_sound_at_exc_seq`, and the
well-formedness of the singleton path list `onePath` returns.

Lean notes:
* The compound proofs use `exec_bind`/`exec_run` (ExecSpec.lean) in place
  of Rocq's inlined bind-and-compose steps.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic

/-- The kind codes `W64 19` and `W64 20` belong to `TExec` and `TRet`
alone; the monad cases dispatch on them without destructing the term. -/
theorem term_code_TExec (u : term) : term_code u = W64 19 → u = TExec := by
  intro Hc
  have H := congrArg BitVec.toNat Hc
  rw [tcode_term_code] at H
  cases u <;> simp only [tcode] at H <;> (try split at H) <;> first | rfl | (simp at H) | omega

theorem term_code_TRet (u : term) : term_code u = W64 20 → ∃ x, u = TRet x := by
  intro Hc
  have H := congrArg BitVec.toNat Hc
  rw [tcode_term_code] at H
  cases u <;> simp only [tcode] at H <;> (try split at H) <;>
    first | exact ⟨_, rfl⟩ | (simp at H) | omega

/-! ## The singleton path list -/
theorem paths_wf_single (k : Nat) (x : term) (sst : sstate) :
    wf_state sst → k ≤ (svars sst).length → vars_below (svars sst).length x →
    paths_wf k [mkPath x sst] := by
  intro Hwf Hk Hx
  refine ⟨?_, ?_, ?_⟩ <;> intro q Hq <;> rw [List.mem_singleton.mp Hq]
  · exact Hwf
  · exact Hk
  · exact Hx

theorem vars_below_ctype_zero (k : Nat) (cty : ctype) : vars_below k (ctype_zero cty) := by
  cases cty <;> trivial

section exec_sound_a
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## Conversion

The checker only accepts a conversion between equal types, which is the
identity. -/
theorem exec_sound_at_convert (cty : ctype) (ce : cexpr) ρ sst (ps : List spath) :
    exec_sound_at (GF := GF) ce ρ sst ps →
    exec_sound_at (GF := GF) (CEConvert cty cty ce) ρ sst ps := by
  intro He Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.AppRCtx _] ce ρ sst ps V _ He Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  iintro Hheap'
  iapply wp_convert cty
  unfold paths_post
  iexists p, V'
  iframe Hheap'
  ipureintro
  exact ⟨Hin, Hag, rfl, Hsat'⟩

/-! ## Exception sequencing

On a path that ended in `execute`, the second statement runs from that
path's state; on a path that ended in a `return`, the second statement is
skipped and the path itself is a result. -/
theorem exec_sound_at_exc_seq (ce1 ce2 : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) ce1 ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps →
       (pret p = TExec ∧ ∃ qs, qs ⊆ out ∧ exec_sound_at (GF := GF) ce2 ρ (pst p) qs) ∨
       ((∃ x, pret p = TRet x) ∧ p ∈ out)) →
    exec_sound_at (GF := GF) (CEExcSeq ce1 ce2) ρ sst out := by
  intro He1 Hwfps Hcont Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.AppRCtx _] ce1 ρ sst ps V _ He1 Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  rcases Hcont p Hin with ⟨Hex, qs, Hsub, Hqs⟩ | ⟨⟨x, Hrx⟩, Hout⟩
  · have Hwfp := Hwfps.paths_wf_state p Hin
    have Hgrow := Hwfps.paths_wf_grow p Hin
    have Hbp : env_below (svars (pst p)).length ρ := env_below_mono _ _ _ Hgrow Hρ
    rw [Hex]
    refine Entails.trans ?_ (wp_exc_seq_exec _ _)
    rw [env_interp_agree _ V V' ρ Hag Hρ]
    exact exec_run ce2 ρ (pst p) qs out _ V V' Hqs Hwfp Hbp Hsat' Hsub Hgrow Hag
  · rw [Hrx]; simp only [teval]
    iintro Hheap'
    iapply wp_exc_seq_ret (teval V' x)
    unfold paths_post
    iexists p, V'
    iframe Hheap'
    ipureintro
    exact ⟨Hout, Hag, by rw [Hrx]; rfl, Hsat'⟩

end exec_sound_a

/-! ## The ghost-state-independent layer (see exec_spec.v) -/
section exec_uniform_a

theorem exec_sound_convert (cty : ctype) (ce : cexpr) ρ sst (ps : List spath) :
    exec_sound ce ρ sst ps → exec_sound (CEConvert cty cty ce) ρ sst ps :=
  fun H ext ffi fi fs gc hlc GF hG sem =>
    exec_sound_at_convert (GF := GF) _ _ _ _ _ (H ext ffi fi fs gc hlc GF hG sem)

theorem exec_sound_exc_seq (ce1 ce2 : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce1 ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps →
       (pret p = TExec ∧ ∃ qs, qs ⊆ out ∧ exec_sound ce2 ρ (pst p) qs) ∨
       ((∃ x, pret p = TRet x) ∧ p ∈ out)) →
    exec_sound (CEExcSeq ce1 ce2) ρ sst out :=
  fun He Hwf Hc ext ffi fi fs gc hlc GF hG sem =>
    exec_sound_at_exc_seq (GF := GF) _ _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hwf
      (fun p Hp => match Hc p Hp with
        | .inl ⟨Hex, qs, Hs, Hq⟩ => .inl ⟨Hex, qs, Hs, Hq ext ffi fi fs gc hlc GF hG sem⟩
        | .inr H => .inr H)

end exec_uniform_a

end Checker
end Perennial
