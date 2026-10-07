/-
Port of `new/checker/exec_sound_c.v`.

Semantic lemmas for the `if`, allocation and store cases of `exec`
(checker/exec.go): the shapes `execIfs`, `execAlloc` and `execStore`
actually produce.

- `exec_sound_at_if_gen` generalizes `exec_sound_at_if` (exec_spec.v) to what
  `execIf` does per path: a *literal* condition takes one branch with the
  state unchanged, anything else forks with the condition (resp. its
  negation) assumed.
- `exec_sound_at_store` is the store case, which exec_spec.v does not have.
- `paths_wf_alloc` / `paths_wf_store` are the well-formedness of the
  result lists `execAlloc` and `storeAll` build.

Lean notes:
* The compound proofs use `exec_bind`/`exec_run` (ExecSpec.lean) and
  `fill_two` (ExecSoundB.lean) in place of Rocq's inlined bind steps.
* Rocq's `alloc_path <$> ps` is `ps.map alloc_path`.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecSoundB
import Checkers.Checker.Fn.heapUpdate

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic

section pure
variable [ext : FfiSyntax]

/-! ## Well-formedness of the result lists -/

/-- The path `execAlloc` produces from a path of its operand. -/
def alloc_path (p : spath) : spath :=
  mkPath (TVar (svars (pst p)).length) (st_alloc (pst p) (pret p))

theorem paths_wf_alloc (k : Nat) (ps : List spath) :
    paths_wf k ps → paths_wf k (ps.map alloc_path) := by
  intro Hwf
  refine ⟨?_, ?_, ?_⟩ <;> intro p' Hp' <;> obtain ⟨p, Hp, rfl⟩ := List.mem_map.mp Hp'
  · exact wf_state_alloc _ _ (Hwf.paths_wf_state p Hp) (Hwf.paths_wf_ret p Hp)
  · simp only [alloc_path, st_alloc, List.length_append, List.length_singleton]
    have := Hwf.paths_wf_grow p Hp
    omega
  · simp only [alloc_path, st_alloc, List.length_append, List.length_singleton, vars_below]
    omega

/-- The state `storeAll` produces: only the heap changes. -/
def st_heap (sst : sstate) (H : List scell) : sstate :=
  mkState H (spc sst) (svars sst)

theorem heap_update_below (k : Nat) (H : List scell) (x y : term) (H' : List scell) :
    heap_below k H → vars_below k y → heap_update H x y = some H' → heap_below k H' := by
  induction H generalizing H' with
  | nil => intro _ _ h; cases h
  | cons c H ih =>
    intro Hb Hy
    simp only [heap_update]
    split
    · intro h; cases h
      intro c' Hc'
      rcases List.mem_cons.mp Hc' with rfl | Hc'
      · exact ⟨(Hb c (List.mem_cons_self ..)).1, Hy⟩
      · exact Hb c' (List.mem_cons_of_mem _ Hc')
    · cases Hup : heap_update H x y with
      | none => intro h; cases h
      | some H'' =>
        intro h; cases h
        intro c' Hc'
        rcases List.mem_cons.mp Hc' with rfl | Hc'
        · exact Hb c' (List.mem_cons_self ..)
        · exact ih H'' (fun c'' Hc'' => Hb c'' (List.mem_cons_of_mem _ Hc'')) Hy Hup c' Hc'

theorem wf_state_heap (sst : sstate) (x y : term) (H' : List scell) :
    wf_state sst → vars_below (svars sst).length y →
    heap_update (sheap sst) x y = some H' → wf_state (st_heap sst H') := by
  intro ⟨Hh, Hpc⟩ Hy Hup
  exact ⟨heap_update_below _ _ _ _ _ Hh Hy Hup, Hpc⟩

end pure

section exec_sound_c
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## `if`

What `execIf` establishes for one path `p` of the condition, with result
list `qs`. -/
def if_ok_at (ct cf : cexpr) (ρ : List (GoString × term)) (p : spath) (qs : List spath) : Prop :=
  (∃ b, pret p = TBool b ∧ exec_sound_at (GF := GF) (if b then ct else cf) ρ (pst p) qs) ∨
  (exec_sound_at (GF := GF) ct ρ (st_assume (pst p) (pret p)) qs ∧
   exec_sound_at (GF := GF) cf ρ (st_assume (pst p) (negate (pret p))) qs)

theorem if_ok_at_mono (ct cf : cexpr) ρ (p : spath) (qs qs' : List spath) :
    qs ⊆ qs' → if_ok_at (GF := GF) ct cf ρ p qs → if_ok_at (GF := GF) ct cf ρ p qs' := by
  intro Hsub H
  rcases H with ⟨b, Hb, Hs⟩ | ⟨H1, H2⟩
  · exact .inl ⟨b, Hb, exec_sound_at_mono _ _ _ _ _ Hsub Hs⟩
  · exact .inr ⟨exec_sound_at_mono _ _ _ _ _ Hsub H1, exec_sound_at_mono _ _ _ _ _ Hsub H2⟩

theorem exec_sound_at_if_gen (cc ct cf : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) cc ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → sort_of_vars (svars (pst p)) (pret p) = some SBool) →
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧ if_ok_at (GF := GF) ct cf ρ p qs) →
    exec_sound_at (GF := GF) (CEIf cc ct cf) ρ sst out := by
  intro Hc Hwfps Hsort Hbr Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.IfCtx _ _] cc ρ sst ps V _ Hc Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  have Hwfp := Hwfps.paths_wf_state p Hin
  have Hgrow := Hwfps.paths_wf_grow p Hin
  have Hbret := Hwfps.paths_wf_ret p Hin
  have Hbp : env_below (svars (pst p)).length ρ := env_below_mono _ _ _ Hgrow Hρ
  obtain ⟨b, Hb⟩ := sort_of_vars_sound V' _ _ _ Hsat'.1 (Hsort p Hin)
  obtain ⟨qs, Hsub, Hok⟩ := Hbr p Hin
  rw [Hb, env_interp_agree _ V V' ρ Hag Hρ]
  refine Entails.trans ?_ (wp_if_bval b _ _ _)
  rcases Hok with ⟨b', Hlit, Hqs⟩ | ⟨Hqt, Hqf⟩
  · -- a literal condition: one branch, state unchanged
    obtain rfl : b' = b := by
      rw [Hlit] at Hb
      exact bval_inj _ _ Hb
    cases b' <;>
      exact exec_run _ ρ (pst p) qs out _ V V' Hqs Hwfp Hbp Hsat' Hsub Hgrow Hag
  · cases b
    · exact exec_run cf ρ (st_assume (pst p) (negate (pret p))) qs out _ V V' Hqf
        (wf_state_assume _ _ Hwfp (vars_below_negate _ _ Hbret)) Hbp
        (st_sat_assume _ _ _ Hsat' (teval_negate V' (pret p) false Hb)) Hsub Hgrow Hag
    · exact exec_run ct ρ (st_assume (pst p) (pret p)) qs out _ V V' Hqt
        (wf_state_assume _ _ Hwfp Hbret) Hbp (st_sat_assume _ _ _ Hsat' Hb) Hsub Hgrow Hag

/-! ## Store -/

/-- Like `heap_interp_update`, but the location comes out of the matching
cell rather than being supplied: the operand of a store is only known to
be a location because a cell of the heap is at it. -/
theorem heap_interp_update_ex (V : valuation) (H H' : List scell) (x y : term) :
    heap_update H x y = some H' →
    heap_interp (GF := GF) V H ⊢
      ∃ (lo : Loc) (z : term), ⌜teval V x = lval lo⌝ ∗
        heapPointsto lo (DFrac.own 1) (teval V z) ∗
        (heapPointsto lo (DFrac.own 1) (teval V y) -∗ heap_interp V H') := by
  induction H generalizing H' with
  | nil => intro h; cases h
  | cons c H ih =>
    simp only [heap_update]
    rw [(heap_interp_cons V c H).to_eq]
    split
    · rename_i Heq
      intro Hh
      cases Hh
      iintro ⟨⟨%lo, %Hl, Hp⟩, HH⟩
      iexists lo, cval c
      rw [Heq] at Hl
      iframe Hp
      isplitr
      · ipureintro; exact Hl
      iintro Hp
      rw [(heap_interp_cons V _ H).to_eq]
      iframe HH
      iexists lo
      iframe Hp
      ipureintro; rw [Heq]; exact Hl
    · cases Hup : heap_update H x y with
      | none => intro h; cases h
      | some H'' =>
        intro Hh
        cases Hh
        iintro ⟨Hc, HH⟩
        icases ih H'' Hup $$ HH with ⟨%lo, %z, %Hl, Hp, Hback⟩
        iexists lo, z
        iframe Hp
        isplitr
        · ipureintro; exact Hl
        iintro Hp
        rw [(heap_interp_cons V c H'').to_eq]
        iframe Hc
        iapply Hback $$ Hp

end exec_sound_c

section pure2
variable [ext : FfiSyntax]

/-- What `storeAll` establishes for the paths `qs` of the stored value, at
location term `x`, with result list `out`. -/
def store_ok (x : term) (qs out : List spath) : Prop :=
  ∀ q, q ∈ qs → ∃ H', heap_update (sheap (pst q)) x (pret q) = some H' ∧
                      mkPath TUnit (st_heap (pst q) H') ∈ out

end pure2

section exec_sound_c2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem exec_sound_at_store (cty : ctype) (ce1 ce2 : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) ce1 ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → ∃ qs, exec_sound_at (GF := GF) ce2 ρ (pst p) qs ∧
                         paths_wf (svars (pst p)).length qs ∧
                         store_ok (pret p) qs out) →
    exec_sound_at (GF := GF) (CEStore cty ce1 ce2) ρ sst out := by
  intro He1 Hwfps Hcont Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.PairLCtx _, EctxItem.AppRCtx _] ce1 ρ sst ps V _ He1 Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_two, fillItem]
  obtain ⟨qs, Hqs, Hwfqs, Hst⟩ := Hcont p Hin
  have Hwfp := Hwfps.paths_wf_state p Hin
  have Hgrow := Hwfps.paths_wf_grow p Hin
  have Hbret := Hwfps.paths_wf_ret p Hin
  have Hbp : env_below (svars (pst p)).length ρ := env_below_mono _ _ _ Hgrow Hρ
  rw [env_interp_agree _ V V' ρ Hag Hρ]
  refine exec_bind [EctxItem.PairRCtx (teval V' (pret p)), EctxItem.AppRCtx _] ce2 ρ (pst p) qs
    V' _ Hqs Hwfp Hbp Hsat' ?_
  intro q V'' Hinq Hag2 Hsat''
  simp only [fill_two, fillItem]
  obtain ⟨H', Hup, Hout⟩ := Hst q Hinq
  iintro Hheap''
  icases heap_interp_update_ex V'' _ _ _ _ Hup $$ Hheap'' with ⟨%lo, %z, %Hl, Hp, Hback⟩
  have Hw : teval V' (pret p) = lval lo := by
    rw [← Hl]; exact teval_agree _ V' V'' (pret p) Hag2 Hbret
  rw [Hw, ← lval_eq]
  wp_pure
  wp_apply wp_ctype_store_any cty lo (teval V'' z) (teval V'' (pret q)) $$ Hp as Hp
  unfold paths_post
  iexists mkPath TUnit (st_heap (pst q) H'), V''
  isplitr
  · ipureintro; exact Hout
  isplitr
  · ipureintro
    exact agree_below_trans _ _ _ _ Hag (agree_below_weaken _ _ _ _ Hgrow Hag2)
  isplitr
  · ipureintro; rw [uval_eq]; rfl
  isplitr
  · ipureintro; exact ⟨Hsat''.1, Hsat''.2⟩
  simp only [st_heap]
  iapply Hback $$ Hp

end exec_sound_c2

/-! ## The ghost-state-independent layer (see exec_spec.v) -/
section exec_uniform_c

def if_ok (ct cf : cexpr) (ρ : List (GoString × term)) (p : spath) (qs : List spath) : Prop :=
  (∃ b, pret p = TBool b ∧ exec_sound (if b then ct else cf) ρ (pst p) qs) ∨
  (exec_sound ct ρ (st_assume (pst p) (pret p)) qs ∧
   exec_sound cf ρ (st_assume (pst p) (negate (pret p))) qs)

theorem if_ok_at_of [ext : FfiSyntax] [ffi : FfiModel] [ffi_interp0 : FfiInterp ffi]
    [ffi_sem : FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {hlc : HasLC}
    {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]
    (ct cf : cexpr) ρ (p : spath) (qs : List spath) :
    if_ok ct cf ρ p qs → if_ok_at (GF := GF) ct cf ρ p qs := by
  intro H
  rcases H with ⟨b, Hb, Hs⟩ | ⟨H1, H2⟩
  · exact .inl ⟨b, Hb, Hs ext ffi ffi_interp0 ffi_sem go_gctx hlc GF hG sem⟩
  · exact .inr ⟨H1 ext ffi ffi_interp0 ffi_sem go_gctx hlc GF hG sem,
      H2 ext ffi ffi_interp0 ffi_sem go_gctx hlc GF hG sem⟩

theorem if_ok_mono (ct cf : cexpr) ρ (p : spath) (qs qs' : List spath) :
    qs ⊆ qs' → if_ok ct cf ρ p qs → if_ok ct cf ρ p qs' := by
  intro Hsub H
  rcases H with ⟨b, Hb, Hs⟩ | ⟨Ht, Hf⟩
  · exact .inl ⟨b, Hb, exec_sound_mono _ _ _ _ _ Hsub Hs⟩
  · exact .inr ⟨exec_sound_mono _ _ _ _ _ Hsub Ht, exec_sound_mono _ _ _ _ _ Hsub Hf⟩

theorem exec_sound_if_gen (cc ct cf : cexpr) ρ sst (ps out : List spath) :
    exec_sound cc ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → sort_of_vars (svars (pst p)) (pret p) = some SBool) →
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧ if_ok ct cf ρ p qs) →
    exec_sound (CEIf cc ct cf) ρ sst out :=
  fun Hc Hwf Hb Hbr ext ffi fi fs gc hlc GF hG sem =>
    exec_sound_at_if_gen (GF := GF) _ _ _ _ _ _ _ (Hc ext ffi fi fs gc hlc GF hG sem) Hwf Hb
      (fun p Hp => let ⟨qs, Hqs, Hok⟩ := Hbr p Hp; ⟨qs, Hqs, if_ok_at_of _ _ _ _ _ Hok⟩)

theorem exec_sound_store (cty : ctype) (ce1 ce2 : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce1 ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → ∃ qs, exec_sound ce2 ρ (pst p) qs ∧
                         paths_wf (svars (pst p)).length qs ∧
                         store_ok (pret p) qs out) →
    exec_sound (CEStore cty ce1 ce2) ρ sst out :=
  fun He Hwf Hc ext ffi fi fs gc hlc GF hG sem =>
    exec_sound_at_store (GF := GF) _ _ _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hwf
      (fun p Hp => let ⟨qs, Hq, Hw, Hs⟩ := Hc p Hp;
        ⟨qs, Hq ext ffi fi fs gc hlc GF hG sem, Hw, Hs⟩)

end exec_uniform_c

end Checker
end Perennial
