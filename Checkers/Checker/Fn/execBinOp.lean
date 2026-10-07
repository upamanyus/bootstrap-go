/-
Port of `new/checker/fn/execBinOp.v`.

`checker.execBinOp` (checker/exec.go): a binary operator. Runs `e1`, then
`e2` from each of its paths, then `binOpAll` with the left operand's term
on the paths of `e2`.
* The kind dispatch is on `term_code (pret q)` with `term_code_TExec` /
  `term_code_TRet`, as in Rocq (the term is not destructed).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundA
import Checkers.Checker.ExecSoundB
import Checkers.Checker.Fn.binOpAll
import Checkers.Checker.Fn.TypeSort

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_execBinOp (op : cop) (t : ctype) (e1 e2 : cexpr) :
    (⊢ exec_like (GF := GF) checker.exec e1) →
    (⊢ exec_like (GF := GF) checker.exec e2) →
    ⊢ exec_like (GF := GF) checker.execBinOp (CEBinOp op t e1 e2) := by
  intro Hex1 Hex2
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  icases He with ⟨%lty, %la, %lb, #Hnode, #Hty, #Ha, #Hb⟩
  iStructNamed Hnode
  wp_auto
  wp_apply wp_TypeSort lty (some t) $$ []
  · rw [is_otype_some]; iframe Hty
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
                     ∃ rs, exec_sound e2 ρ (pst q) rs ∧
                       ∀ sq, sq ∈ rs → ∃ r,
                         sort_of_vars (svars (pst sq)) (pret q) = some (ctype_sort t) ∧
                         sort_of_vars (svars (pst sq)) (pret sq) = some (ctype_sort t) ∧
                         apply_binop op t (pret q) (pret sq) = some r ∧
                         mkPath r (pst sq) ∈ outs⌝ : IProp GF)
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
      wp_apply exec_like_triple _ _ Hex2 lb lρ xp.St' ρ (pst q) $$ [Hst']
        as %s2 %lf2 Hpost2
      · iframe Hst' Hb Hρ
        ipureintro
        exact ⟨Hwf0.paths_wf_state q Hq, env_below_mono _ _ _ (Hwf0.paths_wf_grow q Hq) Hρb⟩
      wp_if_destruct
      · rw [(exec_post_ok _ _ _ _).to_eq]
        icases Hpost2 with ⟨%rs0, Hps2, %Hwf2, %Hsnd2⟩
        wp_apply wp_binOpAll le xp.Ret' op t e1 e2 (pret q) s2 rs0 $$ [Hps2] as %s3 %lf3 Hpost3
        · iframe Hret Hps2
          simp only [is_expr]
          iexists lty, la, lb
          iframe Hnode Hty Ha Hb
        wp_if_destruct
        · icases Hpost3 with ⟨%outs3, Hps3, %HF⟩
          unfold is_paths
          icases Hps3 with ⟨%zs, Hzs, Hzsp⟩
          wp_apply wp_slice_append (t := checker.Path.ty) so ys s3 zs (DFrac.own 1)
            $$ [Hys Hcap Hzs] as %so' ⟨Hys, Hcap, -⟩
          · iframe Hys Hcap Hzs
          wp_for_post
          iframe HΦ Hs e en
          iexists n + W64 1, xp, so', ys ++ zs, outs ++ outs3
          have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
          rw [Hn1]
          iframe i p out Hys Hcap Hrest
          ihave %Hlen2' := BigSepL2.bigSepL2_length $$ Hysp
          isplitl [Hysp Hzsp]
          · iapply (BigSepL2.bigSepL2_append (Or.inl Hlen2')).2
            iframe Hysp Hzsp
          ipureintro
          refine ⟨by word, paths_wf_app _ _ _ Hwfo
            (binop_paths_wf _ _ _ _ _ _ _ (Hwf0.paths_wf_grow q Hq) (Hwf0.paths_wf_ret q Hq) Hwf2 HF),
            ?_⟩
          intro q' Hq'
          rw [take_snoc_of_getElem? _ _ _ Hq_lookup] at Hq'
          rcases List.mem_append.mp Hq' with Hq' | Hq'
          · obtain ⟨rs, Hrs, Hin⟩ := Hdone q' Hq'
            refine ⟨rs, Hrs, fun sq Hsq => ?_⟩
            obtain ⟨r, H1, H2, H3, H4⟩ := Hin sq Hsq
            exact ⟨r, H1, H2, H3, List.mem_append_left _ H4⟩
          · rw [List.mem_singleton.mp Hq']
            exact ⟨rs0, Hsnd2, binop_paths_in _ _ _ _ _ _ HF (fun _ h => List.mem_append_right _ h)⟩
        · wp_for_post
          iapply HΦ
          iapply exec_post_fail _ _ _ _ _ Hif
      · wp_for_post
        iapply HΦ
        iapply exec_post_fail _ _ _ _ _ Hif
    · -- the loop is over
      have Htake : ps0.take (sint.nat n) = ps0 := List.take_of_length_le (by word)
      rw [Htake] at Hdone
      iapply HΦ
      rw [(exec_post_ok _ _ _ _).to_eq]
      iexists outs
      isplitl
      · unfold is_paths; iexists ys; iframe Hys Hysp
      · ipureintro; exact ⟨Hwfo, exec_sound_binop _ _ _ _ _ _ _ _ Hsnd0 Hwf0 Hdone⟩
  · iapply HΦ
    iapply exec_post_fail _ _ _ _ _ Hif

end proof

end Checker
end Perennial
