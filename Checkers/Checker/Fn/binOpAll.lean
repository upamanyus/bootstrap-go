/-
Port of `new/checker/fn/binOpAll.v`.

`checker.binOpAll` (checker/exec.go): apply the operator of an `EBinOp`
node, with left operand `a`, to each of the paths the right operand
reached. Each result path keeps the state of its input path and returns
the term `applyBinOp` built (which checks both operands' sorts against
that state's sort table); an ill-sorted operand makes the whole call
fail.

Lean notes:
* Rocq's `Forall2` is Batteries' `List.Forall₂`.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundB
import Checkers.Checker.Fn.applyBinOp

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- How an input path and its output path are related. -/
def binop_path (o : cop) (cty : ctype) (ta : term) (sq sp : spath) : Prop :=
  ∃ r, sort_of_vars (svars (pst sq)) ta = some (ctype_sort cty) ∧
       sort_of_vars (svars (pst sq)) (pret sq) = some (ctype_sort cty) ∧
       apply_binop o cty ta (pret sq) = some r ∧ sp = mkPath r (pst sq)

theorem binop_result_some (o : cop) (cty : ctype) (vl : List sort) (u w r : term) :
    binop_result o cty vl (some u) (some w) = some r →
    sort_of_vars vl u = some (ctype_sort cty) ∧ sort_of_vars vl w = some (ctype_sort cty) ∧
    apply_binop o cty u w = some r := by
  simp only [binop_result]
  split
  · rename_i h; intro Hr; exact ⟨h.1, h.2, Hr⟩
  · intro h; cases h

section pure
variable [ext : FfiSyntax]

/-- Every input path has its result among the outputs. -/
theorem binop_paths_in (o : cop) (cty : ctype) (ta : term) (qs outs big : List spath) :
    List.Forall₂ (binop_path o cty ta) qs outs → outs ⊆ big →
    ∀ sq, sq ∈ qs → ∃ r,
      sort_of_vars (svars (pst sq)) ta = some (ctype_sort cty) ∧
      sort_of_vars (svars (pst sq)) (pret sq) = some (ctype_sort cty) ∧
      apply_binop o cty ta (pret sq) = some r ∧ mkPath r (pst sq) ∈ big := by
  intro HF
  induction HF with
  | nil => intro _ sq h; cases h
  | cons Hab _ ih =>
    intro Hsub sq Hin
    rcases List.mem_cons.mp Hin with rfl | Hin
    · obtain ⟨r, H1, H2, H3, rfl⟩ := Hab
      exact ⟨r, H1, H2, H3, Hsub (List.mem_cons_self ..)⟩
    · exact ih (fun _ h => Hsub (List.mem_cons_of_mem _ h)) sq Hin

/-- The outputs are well formed, given that the inputs are and the left
operand is scoped by the state it was computed in. -/
theorem binop_paths_wf (o : cop) (cty : ctype) (ta : term) (qs outs : List spath) (k k' : Nat) :
    k ≤ k' → vars_below k' ta → paths_wf k' qs →
    List.Forall₂ (binop_path o cty ta) qs outs → paths_wf k outs := by
  intro Hle Hta Hwf HF
  have Hback : ∀ sp, sp ∈ outs → ∃ sq, sq ∈ qs ∧ binop_path o cty ta sq sp := by
    clear Hwf
    induction HF with
    | nil => intro _ h; cases h
    | cons Hab _ ih =>
      intro sp Hin
      rcases List.mem_cons.mp Hin with rfl | Hin
      · exact ⟨_, List.mem_cons_self .., Hab⟩
      · obtain ⟨sq, Hsq, H⟩ := ih sp Hin
        exact ⟨sq, List.mem_cons_of_mem _ Hsq, H⟩
  refine ⟨?_, ?_, ?_⟩ <;> intro sp Hin <;> obtain ⟨sq, Hsq, r, _, _, Hr, rfl⟩ := Hback sp Hin
  · exact Hwf.paths_wf_state sq Hsq
  · exact Nat.le_trans Hle (Hwf.paths_wf_grow sq Hsq)
  · exact apply_binop_below _ _ _ _ _ _ Hr
      (vars_below_mono _ _ _ (Hwf.paths_wf_grow sq Hsq) Hta) (Hwf.paths_wf_ret sq Hsq)

end pure

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_binOpAll (le lta : Loc) (o : cop) (cty : ctype) (ce1 ce2 : cexpr)
    (ta : term) (s : GoSlice) (qs0 : List spath) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_expr le (CEBinOp o cty ce1 ce2) ∗
        is_term lta ta ∗ is_paths s qs0 }}
      (App (App (App (Val (@! checker.binOpAll)) (Val #le)) (Val #lta)) (Val #s))
    {{ (s' : GoSlice) (lf : Loc), RET (PairV #s' #lf);
        if lf = null then
          iprop(∃ outs, is_paths s' outs ∗ ⌜List.Forall₂ (binop_path o cty ta) qs0 outs⌝)
        else iprop(True) }} := by
  wp_start as ⟨#He, #Hta, Hps⟩
  simp only [is_expr]
  icases He with ⟨%lty, %la, %lb, #Hnode, #Hty, -, -⟩
  iStructNamed Hnode
  unfold is_paths
  icases Hps with ⟨%xs, Hs, Hxs⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hxs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave Hnil := ownSlice_nil (GF := GF) (V := checker.Path) (DFrac.own 1)
  ihave Hnilcap := ownSliceCap_nil (GF := GF) (V := checker.Path)
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  ihave HI : (∃ (n : w64) (cur : checker.Path) (so : GoSlice) (ys : List checker.Path)
      (outs : List spath),
      "i" ∷ i_ptr ↦ n ∗ "q" ∷ q_ptr ↦ cur ∗ "out" ∷ out_ptr ↦ so ∗
      "Hys" ∷ so ↦* ys ∗ "Hcap" ∷ ownSliceCap checker.Path so (DFrac.own 1) ∗
      "Hysp" ∷ ([∗list] y;sp ∈ ys;outs, is_path y sp) ∗
      "Hrest" ∷ ([∗list] x;sq ∈ xs.drop (sint.nat n);qs0.drop (sint.nat n), is_path x sq) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ xs.length⌝ ∗
      "%HF" ∷ ⌜List.Forall₂ (binop_path o cty ta) (qs0.take (sint.nat n)) outs⌝ : IProp GF)
      $$ [i q out Hxs Hnil Hnilcap]
  · iexists W64 0, _, slice.nil, [], []
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero, List.drop_zero]
    iframe i q out Hxs Hnil Hnilcap
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro
    exact ⟨by word, .nil⟩
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hn.1, Hif⟩]
    list_elem xs (sint.nat n) as xp
    list_elem qs0 (sint.nat n) as sq
    wp_apply wp_load_slice_index s (sint.Z n) xs _ xp Hn.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Hxp_lookup
    rw [drop_cons_of_getElem? _ _ _ Hxp_lookup, drop_cons_of_getElem? _ _ _ Hsq_lookup]
    icases (BigSepL2.bigSepL2_cons (Φ := fun _ y o => is_path (GF := GF) y o)).1 $$ Hrest
      with ⟨Hp0, Hrest⟩
    rw [show is_path xp sq = iprop(is_term (GF := GF) xp.Ret' (pret sq) ∗ is_state xp.St' (pst sq))
      from rfl]
    icases Hp0 with ⟨#Hret, Hst'⟩
    unfold is_state
    icases Hst' with ⟨%hs, %cs, %vs, Hstl, Hheap, Hcond, #Hvars⟩
    rw [show is_vars (GF := GF) vs (svars (pst sq)) =
      iprop(vs ↦*□ (svars (pst sq)).map sort_code) from rfl]
    wp_auto
    wp_apply wp_applyBinOp o lty cty vs (svars (pst sq)) lta xp.Ret' (some ta) (some (pret sq))
      $$ [] as %lv %okb ⟨%Hok, #Hlv⟩
    · rw [is_oterm_some, is_oterm_some]; iframe Hty Hvars Hta Hret
    cases Hbr : binop_result o cty (svars (pst sq)) (some ta) (some (pret sq)) with
    | none =>
      -- ill-sorted
      rw [Hbr] at Hok
      simp only [oterm_ok] at Hok
      subst Hok
      wp_auto
      wp_alloc lfail as Hlf
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hlf
      wp_auto
      wp_for_post
      iapply HΦ
      rw [ite_eq_right Hnn]
      itrivial
    | some y =>
      rw [Hbr] at Hok
      simp only [oterm_ok] at Hok
      subst Hok
      rw [is_oterm_some]
      obtain ⟨Hs1, Hs2, Hr⟩ := binop_result_some _ _ _ _ _ _ Hbr
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, _⟩
      wp_auto
      wp_apply wp_slice_append (t := checker.Path.ty) so ys _ [checker.Path.mk lv xp.St']
        (DFrac.own 1) $$ [Hys Hcap Hsl] as %so' ⟨Hys, Hcap, -⟩
      · iframe Hys Hcap Hsl
      wp_for_post
      iframe HΦ Hs a e
      iexists n + W64 1, xp, so', ys ++ [checker.Path.mk lv xp.St'], outs ++ [mkPath y (pst sq)]
      have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [Hn1]
      iframe i q out Hys Hcap Hrest
      isplitl [Hysp Hstl Hheap Hcond]
      · iapply BigSepL2.bigSepL2_snoc.2
        iframe Hysp
        rw [show is_path (checker.Path.mk lv xp.St') (mkPath y (pst sq)) =
          iprop(is_term (GF := GF) lv y ∗ is_state xp.St' (pst sq)) from rfl]
        iframe Hlv
        unfold is_state is_vars
        iexists hs, cs, vs
        iframe Hstl Hheap Hcond Hvars
      ipureintro
      refine ⟨by word, ?_⟩
      rw [take_snoc_of_getElem? _ _ _ Hsq_lookup]
      exact forall2_snoc _ _ _ _ _ HF ⟨y, Hs1, Hs2, Hr, rfl⟩
  · -- the loop is over
    have Htake : qs0.take (sint.nat n) = qs0 := List.take_of_length_le (by word)
    rw [Htake] at HF
    iapply HΦ
    rw [ite_eq_left rfl]
    iexists outs
    isplitl
    · iexists ys; iframe Hys Hysp
    · ipureintro; exact HF

end proof

end Checker
end Perennial
