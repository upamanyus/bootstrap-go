/-
Port of `new/checker/fn/execUnOp.v`.

`checker.execUnOp` (checker/exec.go): a unary operator. Runs the operand;
on each path `applyUnOp` builds the result term (checking the operand's
sort against the path's sort table), and the path keeps its state.

Lean notes:
* Rocq's `wp_execUnOp_aux` (naming trap) is not needed; `wp_execUnOp` is
  proved directly.
* The kind dispatch is on `term_code (pret q)` with `term_code_TExec` /
  `term_code_TRet`, as in Rocq (the term is not destructed).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundA
import Checkers.Checker.ExecSoundB
import Checkers.Checker.Fn.applyUnOp
import Checkers.Checker.Fn.TypeSort

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

theorem unop_result_some (o : cop) (cty : ctype) (vl : List sort) (u r : term) :
    unop_result o cty vl (some u) = some r →
    sort_of_vars vl u = some (ctype_sort cty) ∧ apply_unop o cty u = some r := by
  simp only [unop_result]
  split
  · rename_i h; intro Hr; exact ⟨h, Hr⟩
  · intro h; cases h

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_execUnOp (o : cop) (t : ctype) (e : cexpr) :
    (⊢ exec_like (GF := GF) checker.exec e) →
    ⊢ exec_like (GF := GF) checker.execUnOp (CEUnOp o t e) := by
  intro Hex1
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  icases He with ⟨%lt, %la, #Hnode, #Ht, #Ha⟩
  iStructNamed Hnode
  wp_auto
  wp_apply wp_TypeSort lt (some t) $$ []
  · rw [is_otype_some]; iframe Ht
  wp_apply exec_like_triple _ _ Hex1 la lρ lst ρ sst $$ [Hst] as %s %lf Hpost
  · iframe Hst Ha Hρ; ipureintro; exact ⟨Hwf, Hρb⟩
  wp_if_destruct
  · rw [(exec_post_ok _ _ _ _).to_eq]
    icases Hpost with ⟨%ps0, Hps, %Hwf0, %Hsnd0⟩
    unfold is_paths
    icases Hps with ⟨%xs, Hs, Hxs⟩
    ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hxs
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    ihave Hnil := ownSlice_nil (GF := GF) (V := checker.Path) (DFrac.own 1)
    ihave Hnilcap := ownSliceCap_nil (GF := GF) (V := checker.Path)
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    ihave HI : (∃ (n : w64) (cur : checker.Path) (so : GoSlice) (ys : List checker.Path)
        (outs : List spath),
        "i" ∷ i_ptr ↦ n ∗ "p" ∷ p_ptr ↦ cur ∗ "out" ∷ out_ptr ↦ so ∗
        "Hys" ∷ so ↦* ys ∗ "Hcap" ∷ ownSliceCap checker.Path so (DFrac.own 1) ∗
        "Hysp" ∷ ([∗list] y;q ∈ ys;outs, is_path y q) ∗
        "Hrest" ∷ ([∗list] x;q ∈ xs.drop (sint.nat n);ps0.drop (sint.nat n), is_path x q) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ xs.length⌝ ∗
        "%Hwfo" ∷ ⌜paths_wf (svars sst).length outs⌝ ∗
        "%Hdone" ∷ ⌜∀ q, q ∈ ps0.take (sint.nat n) →
                     ∃ r, sort_of_vars (svars (pst q)) (pret q) = some (ctype_sort t) ∧
                          apply_unop o t (pret q) = some r ∧
                          mkPath r (pst q) ∈ outs⌝ : IProp GF)
        $$ [i p out Hxs Hnil Hnilcap]
    · iexists W64 0, _, slice.nil, [], []
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero, List.drop_zero]
      iframe i p out Hxs Hnil Hnilcap
      isplitr
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
      ipureintro
      exact ⟨by word, paths_wf_nil _, fun _ h => nomatch h⟩
    wp_for HI
    wp_if_destruct
    · rw [ite_eq_left ⟨Hn.1, Hif⟩]
      list_elem xs (sint.nat n) as xp
      list_elem ps0 (sint.nat n) as q
      wp_apply wp_load_slice_index s (sint.Z n) xs _ xp Hn.1 $$ [Hs] with Hs
      · iframe Hs; ipureintro; exact Hxp_lookup
      rw [drop_cons_of_getElem? _ _ _ Hxp_lookup, drop_cons_of_getElem? _ _ _ Hq_lookup]
      icases (BigSepL2.bigSepL2_cons (Φ := fun _ y o => is_path (GF := GF) y o)).1 $$ Hrest
        with ⟨Hp0, Hrest⟩
      rw [show is_path xp q = iprop(is_term (GF := GF) xp.Ret' (pret q) ∗ is_state xp.St' (pst q))
        from rfl]
      icases Hp0 with ⟨#Hret, Hst'⟩
      have Hq : q ∈ ps0 := List.mem_of_getElem? Hq_lookup
      unfold is_state
      icases Hst' with ⟨%hs, %cs, %vs, Hstl, Hheap, Hcond, #Hvars⟩
      rw [show is_vars (GF := GF) vs (svars (pst q)) =
        iprop(vs ↦*□ (svars (pst q)).map sort_code) from rfl]
      wp_auto
      wp_apply wp_applyUnOp o lt t vs (svars (pst q)) xp.Ret' (some (pret q))
        $$ [] as %lv %okb ⟨%Hok, #Hlv⟩
      · rw [is_oterm_some]; iframe Ht Hvars Hret
      cases Hur : unop_result o t (svars (pst q)) (some (pret q)) with
      | none =>
        -- ill-sorted
        rw [Hur] at Hok
        simp only [oterm_ok] at Hok
        subst Hok
        wp_auto
        wp_alloc lfail as Hlf
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hlf
        wp_auto
        wp_for_post
        iapply HΦ
        iapply exec_post_fail _ _ _ _ _ Hnn
      | some y =>
        rw [Hur] at Hok
        simp only [oterm_ok] at Hok
        subst Hok
        rw [is_oterm_some]
        obtain ⟨Hs1, Hr⟩ := unop_result_some _ _ _ _ _ Hur
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
        iframe HΦ Hs e
        iexists n + W64 1, xp, so', ys ++ [checker.Path.mk lv xp.St'], outs ++ [mkPath y (pst q)]
        have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        rw [Hn1]
        iframe i p out Hys Hcap Hrest
        isplitl [Hysp Hstl Hheap Hcond]
        · iapply BigSepL2.bigSepL2_snoc.2
          iframe Hysp
          rw [show is_path (checker.Path.mk lv xp.St') (mkPath y (pst q)) =
            iprop(is_term (GF := GF) lv y ∗ is_state xp.St' (pst q)) from rfl]
          iframe Hlv
          unfold is_state is_vars
          iexists hs, cs, vs
          iframe Hstl Hheap Hcond Hvars
        have Hwfq := Hwf0.paths_wf_state q Hq
        ipureintro
        refine ⟨by word, paths_wf_app _ _ _ Hwfo ⟨?_, ?_, ?_⟩, ?_⟩
        · intro q' Hq'; rw [List.mem_singleton.mp Hq']; exact Hwfq
        · intro q' Hq'; rw [List.mem_singleton.mp Hq']; exact Hwf0.paths_wf_grow q Hq
        · intro q' Hq'; rw [List.mem_singleton.mp Hq']
          exact apply_unop_below _ _ _ _ _ Hr (Hwf0.paths_wf_ret q Hq)
        intro q' Hq'
        rw [take_snoc_of_getElem? _ _ _ Hq_lookup] at Hq'
        rcases List.mem_append.mp Hq' with Hq' | Hq'
        · obtain ⟨r', H1, H2, H3⟩ := Hdone q' Hq'
          exact ⟨r', H1, H2, List.mem_append_left _ H3⟩
        · rw [List.mem_singleton.mp Hq']
          exact ⟨y, Hs1, Hr, List.mem_append_right _ (List.mem_singleton_self _)⟩
    · -- the loop is over
      have Htake : ps0.take (sint.nat n) = ps0 := List.take_of_length_le (by word)
      rw [Htake] at Hdone
      iapply HΦ
      rw [(exec_post_ok _ _ _ _).to_eq]
      iexists outs
      isplitl
      · unfold is_paths; iexists ys; iframe Hys Hysp
      · ipureintro; exact ⟨Hwfo, exec_sound_unop _ _ _ _ _ _ _ Hsnd0 Hdone⟩
  · iapply HΦ
    iapply exec_post_fail _ _ _ _ _ Hif

end proof

end Checker
end Perennial
