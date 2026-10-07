/-
Port of `new/checker/fn/execDo.v`.

`checker.execDo` (checker/exec.go): `do: e`. Runs `e`, then replaces the
return term of each of its paths by `TExec`, keeping the state.

Lean notes:
* Rocq's `wp_execDo_aux` (naming trap) is not needed; `wp_execDo` is
  proved directly.
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

theorem wp_execDo (e : cexpr) :
    (⊢ exec_like (GF := GF) checker.exec e) →
    ⊢ exec_like (GF := GF) checker.execDo (CEDo e) := by
  intro Hex1
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  icases He with ⟨%la, #Hnode, #Ha⟩
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
        "%Hdone" ∷ ⌜∀ q, q ∈ ps0.take (sint.nat n) → mkPath TExec (pst q) ∈ outs⌝ : IProp GF)
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
      ipersist «$v0»
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, _⟩
      wp_auto
      wp_apply wp_slice_append (t := checker.Path.ty) so ys _ [checker.Path.mk «$v0_ptr» xp.St']
        (DFrac.own 1) $$ [Hys Hcap Hsl] as %so' ⟨Hys, Hcap, -⟩
      · iframe Hys Hcap Hsl
      wp_for_post
      iframe HΦ Hs
      iexists n + W64 1, xp, so', ys ++ [checker.Path.mk «$v0_ptr» xp.St'],
        outs ++ [mkPath TExec (pst q)]
      have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [Hn1]
      iframe i p out Hys Hcap Hrest
      isplitl [Hysp Hst']
      · iapply BigSepL2.bigSepL2_snoc.2
        iframe Hysp
        rw [show is_path (checker.Path.mk «$v0_ptr» xp.St') (mkPath TExec (pst q)) =
          iprop(is_term (GF := GF) «$v0_ptr» TExec ∗ is_state xp.St' (pst q)) from rfl]
        iframe Hst'
        simp only [is_term, tnode]
        iExactEq «$v0»; rfl
      ipureintro
      refine ⟨by word, paths_wf_app _ _ _ Hwfo
        (paths_wf_single _ _ _ (Hwf0.paths_wf_state q Hq) (Hwf0.paths_wf_grow q Hq) trivial), ?_⟩
      intro q' Hq'
      rw [take_snoc_of_getElem? _ _ _ Hq_lookup] at Hq'
      rcases List.mem_append.mp Hq' with Hq' | Hq'
      · exact List.mem_append_left _ (Hdone q' Hq')
      · rw [List.mem_singleton.mp Hq']; exact List.mem_append_right _ (List.mem_singleton_self _)
    · -- the loop is over
      have Htake : ps0.take (sint.nat n) = ps0 := List.take_of_length_le (by word)
      rw [Htake] at Hdone
      iapply HΦ
      rw [(exec_post_ok _ _ _ _).to_eq]
      iexists outs
      isplitl
      · unfold is_paths; iexists ys; iframe Hys Hysp
      · ipureintro; exact ⟨Hwfo, exec_sound_do _ _ _ _ _ Hsnd0 Hdone⟩
  · iapply HΦ
    iapply exec_post_fail _ _ _ _ _ Hif

end proof

end Checker
end Perennial
