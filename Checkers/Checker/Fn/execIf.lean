/-
Port of `new/checker/fn/execIf.v`.

`checker.execIf` (checker/exec.go): one path of an `if`.

`c` is the condition term reached on the path and `st` its state. The
condition must be boolean-sorted (`SortOf`). A literal condition takes the
corresponding branch with the state unchanged; otherwise the state is
cloned twice, the `then` branch runs with `c` added to the path condition
and the `else` branch with `negate c`, and the result is the
concatenation.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundA
import Checkers.Checker.ExecSoundB
import Checkers.Checker.ExecSoundC
import Checkers.Checker.Fn.SortOf
import Checkers.Checker.Fn.sortOfEnv
import Checkers.Checker.Fn.negate
import Checkers.Checker.Fn.State__clone

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- The kind test `c.Kind == TBool`, without destructing the term. -/
theorem term_kind_tbool (tc : term) : (∃ b, tc = TBool b) ∨ term_code tc ≠ W64 5 := by
  cases tc <;> first
    | exact .inl ⟨_, rfl⟩
    | (right; simp only [term_code]; (try split) <;> decide)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

def execIf_post (ct cf : cexpr) (ρ : List (GoString × term)) (tc : term) (sst : sstate)
    (sr : GoSlice) (lf : Loc) : IProp GF :=
  if lf = null then
    iprop(∃ qvs, is_paths sr qvs ∗ ⌜paths_wf (svars sst).length qvs⌝ ∗
           ⌜sort_of_vars (svars sst) tc = some SBool⌝ ∗
           ⌜if_ok ct cf ρ (mkPath tc sst) qvs⌝)
  else iprop(True)

theorem wp_execIf (le lρ lc lst : Loc) (cc ct cf : cexpr) (tc : term)
    (ρ : List (GoString × term)) (sst : sstate) :
    (⊢ exec_like (GF := GF) checker.exec ct) → (⊢ exec_like (GF := GF) checker.exec cf) →
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_expr le (CEIf cc ct cf) ∗ is_env lρ ρ ∗
        is_term lc tc ∗ is_state lst sst ∗
        ⌜wf_state sst⌝ ∗ ⌜env_below (svars sst).length ρ⌝ ∗
        ⌜vars_below (svars sst).length tc⌝ }}
      (App (App (App (App (Val (@! checker.execIf)) (Val #le)) (Val #lρ)) (Val #lc)) (Val #lst))
    {{ (sr : GoSlice) (lf : Loc), RET (PairV #sr #lf); execIf_post ct cf ρ tc sst sr lf }} := by
  intro Hext Hexf
  wp_start as ⟨#He, #Hρ, #Htc, Hst, %Hwf, %Hρb, %Htb⟩
  simp only [is_expr]
  icases He with ⟨%lcc, %la, %lb, #Hn, #Hc, #Ha, #Hb⟩
  simp only [enode0] at *
  iStructNamed Hn
  unfold is_state
  icases Hst with ⟨%hs, %cs, %vs, Hl, Hh, Hcond, #Hv⟩
  wp_auto
  rw [show is_vars (GF := GF) vs (svars sst) = iprop(vs ↦*□ (svars sst).map sort_code) from rfl]
  wp_apply wp_SortOf vs lc (svars sst) (some tc) $$ []
  · rw [is_oterm_some]
    iframe Htc Hv
  rw [show osort_of (vars_env (svars sst)) (some tc) = sort_of_vars (svars sst) tc from rfl]
  cases Hsrt : sort_of_vars (svars sst) tc with
  | none =>
    -- no sort
    simp only [osort_ok, osort_code]
    wp_auto
    wp_alloc lfail as Hf
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hf
    wp_auto
    iapply HΦ
    unfold execIf_post
    rw [ite_eq_right Hnn]
    itrivial
  | some srt =>
  simp only [osort_ok, osort_code]
  by_cases Hnb : srt = SBool
  case neg =>
    -- the wrong sort
    cases srt <;> simp only [sort_code, checker.SortBool] at Hnb ⊢ <;> try contradiction
    all_goals
      wp_auto
      wp_alloc lfail as Hf
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hf
      wp_auto
      iapply HΦ
      unfold execIf_post
      rw [ite_eq_right Hnn]
      itrivial
  subst Hnb
  simp only [sort_code, checker.SortBool]
  wp_auto
  icases is_term_node _ _ $$ Htc with ⟨%ta, %tb, %tcc, %Hiw, #Hnode, -, -, -⟩
  iStructNamedSuffix Hnode "_c"
  ihave Hst : is_state (GF := GF) lst sst $$ [Hl Hh Hcond]
  · unfold is_state is_vars; iexists hs, cs, vs; iframe Hl Hh Hcond Hv
  rcases term_kind_tbool tc with ⟨b, rfl⟩ | Hnk
  · -- a literal condition
    simp only [term_code, term_num, tnode, checker.TBool]
    wp_auto
    cases b
    · rw [show decide (bool_code false = W64 1) = false from by decide]
      wp_auto
      wp_apply exec_like_triple _ _ Hexf lb lρ lst ρ sst $$ [Hst] as %sr %lf Hpost
      · iframe Hst Hb Hρ; ipureintro; exact ⟨Hwf, Hρb⟩
      iapply HΦ
      unfold execIf_post exec_post
      split
      · icases Hpost with ⟨%qvs, Hq, %Hq1, %Hq2⟩
        iexists qvs
        iframe Hq
        ipureintro
        exact ⟨Hq1, Hsrt, .inl ⟨false, rfl, Hq2⟩⟩
      · itrivial
    · rw [show decide (bool_code true = W64 1) = true from by decide]
      wp_auto
      wp_apply exec_like_triple _ _ Hext la lρ lst ρ sst $$ [Hst] as %sr %lf Hpost
      · iframe Hst Ha Hρ; ipureintro; exact ⟨Hwf, Hρb⟩
      iapply HΦ
      unfold execIf_post exec_post
      split
      · icases Hpost with ⟨%qvs, Hq, %Hq1, %Hq2⟩
        iexists qvs
        iframe Hq
        ipureintro
        exact ⟨Hq1, Hsrt, .inl ⟨true, rfl, Hq2⟩⟩
      · itrivial

  · simp only [tnode, checker.TBool]
    wp_auto
    rw [show decide (term_code tc = W64 5) = false from decide_eq_false Hnk]
    wp_auto
    -- the `then` state
    wp_apply wp_State__clone $$ [Hst] as %lst1 ⟨Hst, Hfr⟩
    · iframe Hst
    unfold is_state_fresh is_cond
    icases Hfr with ⟨%hs1, %cs1, %vs1, Hl1, Hh1, Hhcap1, ⟨%ls1, Hls1, #Hls1p⟩, Hccap1, Hv1, Hvcap1⟩
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, _⟩
    wp_auto
    wp_apply wp_slice_append (t := checker.Term.ty.PointerType) cs1 ls1 _ [lc]
      (DFrac.own 1) $$ [Hls1 Hccap1 Hsl1] as %cs1' ⟨Hls1, Hccap1, -⟩
    · iframe Hls1 Hccap1 Hsl1
    ihave Hfr : is_state_fresh (GF := GF) lst1 (st_assume sst tc)
      $$ [Hl1 Hh1 Hhcap1 Hls1 Hccap1 Hv1 Hvcap1]
    · unfold is_state_fresh is_cond
      simp only [st_assume]
      iexists hs1, cs1', vs1
      iframe Hh1 Hhcap1 Hccap1 Hv1 Hvcap1
      isplitl [Hl1]
      · iexact Hl1
      iexists ls1 ++ [lc]
      iframe Hls1
      iapply BigSepL2.bigSepL2_snoc.2
      iframe Hls1p Htc
    imod is_state_fresh_publish _ _ $$ Hfr with Hst1
    wp_apply exec_like_triple _ _ Hext la lρ lst1 ρ (st_assume sst tc) $$ [Hst1]
      as %sps1 %lfl1 Hpost1
    · iframe Hst1 Ha Hρ; ipureintro; exact ⟨wf_state_assume _ _ Hwf Htb, Hρb⟩
    wp_if_destruct
    rotate_left
    · iapply HΦ
      unfold execIf_post
      rw [ite_eq_right Hif]
      itrivial
    rw [(exec_post_ok _ _ _ _).to_eq]
    icases Hpost1 with ⟨%qv1, Hq1, %Hwfq1, %Hsndq1⟩
    -- the `else` state
    wp_apply wp_State__clone $$ [Hst] as %lst2 ⟨-, Hfr⟩
    · iframe Hst
    unfold is_state_fresh is_cond
    icases Hfr with ⟨%hs2, %cs2, %vs2, Hl2, Hh2, Hhcap2, ⟨%ls2, Hls2, #Hls2p⟩, Hccap2, Hv2, Hvcap2⟩
    wp_auto
    wp_apply wp_negate lc tc $$ [] as %lneg #Hneg
    · iframe Htc
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, _⟩
    wp_auto
    wp_apply wp_slice_append (t := checker.Term.ty.PointerType) cs2 ls2 _ [lneg]
      (DFrac.own 1) $$ [Hls2 Hccap2 Hsl2] as %cs2' ⟨Hls2, Hccap2, -⟩
    · iframe Hls2 Hccap2 Hsl2
    ihave Hfr : is_state_fresh (GF := GF) lst2 (st_assume sst (negate tc))
      $$ [Hl2 Hh2 Hhcap2 Hls2 Hccap2 Hv2 Hvcap2]
    · unfold is_state_fresh is_cond
      simp only [st_assume]
      iexists hs2, cs2', vs2
      iframe Hh2 Hhcap2 Hccap2 Hv2 Hvcap2
      isplitl [Hl2]
      · iexact Hl2
      iexists ls2 ++ [lneg]
      iframe Hls2
      iapply BigSepL2.bigSepL2_snoc.2
      iframe Hls2p Hneg
    imod is_state_fresh_publish _ _ $$ Hfr with Hst2
    wp_apply exec_like_triple _ _ Hexf lb lρ lst2 ρ (st_assume sst (negate tc)) $$ [Hst2]
      as %sps2 %lfl2 Hpost2
    · iframe Hst2 Hb Hρ
      ipureintro
      exact ⟨wf_state_assume _ _ Hwf (vars_below_negate _ _ Htb), Hρb⟩
    wp_if_destruct
    rotate_left
    · iapply HΦ
      unfold execIf_post
      rw [ite_eq_right Hif]
      itrivial
    rw [(exec_post_ok _ _ _ _).to_eq]
    icases Hpost2 with ⟨%qv2, Hq2, %Hwfq2, %Hsndq2⟩
    unfold is_paths
    icases Hq1 with ⟨%ys1, Hys1, Hys1p⟩
    icases Hq2 with ⟨%ys2, Hys2, Hys2p⟩
    ihave Hnil := ownSlice_nil (GF := GF) (V := checker.Path) (DFrac.own 1)
    ihave Hnilcap := ownSliceCap_nil (GF := GF) (V := checker.Path)
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    wp_apply wp_slice_append (t := checker.Path.ty) slice.nil [] sps1 ys1 (DFrac.own 1)
      $$ [Hnil Hnilcap Hys1] as %so1 ⟨Hso1, Hso1cap, -⟩
    · iframe Hnil Hnilcap Hys1
    wp_apply wp_slice_append (t := checker.Path.ty) so1 ([] ++ ys1) sps2 ys2 (DFrac.own 1)
      $$ [Hso1 Hso1cap Hys2] as %so2 ⟨Hso2, -, -⟩
    · iframe Hso1 Hso1cap Hys2
    iapply HΦ
    unfold execIf_post
    rw [ite_eq_left rfl]
    iexists qv1 ++ qv2
    ihave %Hl1 := BigSepL2.bigSepL2_length $$ Hys1p
    isplitl
    · unfold is_paths
      iexists ([] ++ ys1) ++ ys2
      iframe Hso2
      rw [List.nil_append]
      iapply (BigSepL2.bigSepL2_append (Or.inl Hl1)).2
      iframe Hys1p Hys2p
    ipureintro
    exact ⟨paths_wf_app _ _ _ Hwfq1 Hwfq2, Hsrt,
      .inr ⟨exec_sound_app_l _ _ _ _ _ Hsndq1, exec_sound_app_r _ _ _ _ _ Hsndq2⟩⟩

end proof

end Checker
end Perennial
