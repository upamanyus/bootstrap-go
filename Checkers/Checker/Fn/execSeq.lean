/-
Port of `new/checker/fn/execSeq.v`.

`checker.execSeq` (checker/exec.go): `e1 ;; e2`. Runs `e1`, then `e2` from
each of its paths in the caller's environment.
* The kind dispatch is on `term_code (pret q)` with `term_code_TExec` /
  `term_code_TRet`, as in Rocq (the term is not destructed).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundA
import Checkers.Checker.ExecSoundB

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

theorem wp_execSeq (e1 e2 : cexpr) :
    (⊢ exec_like (GF := GF) checker.exec e1) →
    (⊢ exec_like (GF := GF) checker.exec e2) →
    ⊢ exec_like (GF := GF) checker.execSeq (CESeq e1 e2) := by
  intro Hex1 Hex2
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  icases He with ⟨%la, %lb, #Hnode, #Ha, #Hb⟩
  simp only [enode0] at *
  iStructNamed Hnode
  wp_auto
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
                     ∃ qs, qs ⊆ outs ∧ exec_sound e2 ρ (pst q) qs⌝ : IProp GF)
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
        icases Hpost2 with ⟨%qs2, Hps2, %Hwf2, %Hsnd2⟩
        unfold is_paths
        icases Hps2 with ⟨%zs, Hzs, Hzsp⟩
        wp_apply wp_slice_append (t := checker.Path.ty) so ys s2 zs (DFrac.own 1)
          $$ [Hys Hcap Hzs] as %so' ⟨Hys, Hcap, -⟩
        · iframe Hys Hcap Hzs
        wp_for_post
        iframe HΦ Hs e en
        iexists n + W64 1, xp, so', ys ++ zs, outs ++ qs2
        have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        rw [Hn1]
        iframe i p out Hys Hcap Hrest
        ihave %Hlen2' := BigSepL2.bigSepL2_length $$ Hysp
        isplitl [Hysp Hzsp]
        · iapply (BigSepL2.bigSepL2_append (Or.inl Hlen2')).2
          iframe Hysp Hzsp
        ipureintro
        refine ⟨by word, paths_wf_app _ _ _ Hwfo
          (paths_wf_mono _ _ _ (Hwf0.paths_wf_grow q Hq) Hwf2), ?_⟩
        intro q' Hq'
        rw [take_snoc_of_getElem? _ _ _ Hq_lookup] at Hq'
        rcases List.mem_append.mp Hq' with Hq' | Hq'
        · obtain ⟨qs, H2, H3⟩ := Hdone q' Hq'
          exact ⟨qs, fun _ h => List.mem_append_left _ (H2 h), H3⟩
        · rw [List.mem_singleton.mp Hq']
          exact ⟨qs2, fun _ h => List.mem_append_right _ h, Hsnd2⟩
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
      · ipureintro; exact ⟨Hwfo, exec_sound_seq _ _ _ _ _ _ Hsnd0 Hwf0 Hdone⟩
  · iapply HΦ
    iapply exec_post_fail _ _ _ _ _ Hif

end proof

end Checker
end Perennial
