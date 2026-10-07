/-
Port of `new/checker/fn/execStore.v`.

`checker.execStore` (checker/exec.go): `e1 <-[t] e2`. Runs `e1` (the
location), then `e2` from each of its paths, then `storeAll` on the
location term and the value's paths.

Lean notes:
* Rocq's `wp_execStore_aux` (naming trap) is not needed; `wp_execStore` is
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
import Checkers.Checker.ExecSoundC
import Checkers.Checker.Fn.storeAll
import Checkers.Checker.Fn.TypeSort

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

theorem store_ok_mono [FfiSyntax] (x : term) (qvs outs outs' : List spath) :
    outs ⊆ outs' → store_ok x qvs outs → store_ok x qvs outs' := by
  intro Hsub Hok qv Hin
  obtain ⟨H', Hup, Hout⟩ := Hok qv Hin
  exact ⟨H', Hup, Hsub Hout⟩

/-- What the loop has established for a prefix of the operand's paths. -/
def store_done [FfiSyntax] (ce2 : cexpr) (ρ : List (GoString × term)) (done : List spath)
    (outs : List spath) : Prop :=
  ∀ p1, p1 ∈ done → ∃ qvs, exec_sound ce2 ρ (pst p1) qvs ∧
                          paths_wf (svars (pst p1)).length qvs ∧
                          store_ok (pret p1) qvs outs

theorem store_done_snoc [FfiSyntax] (ce2 : cexpr) ρ (dn outs : List spath) (p1 : spath)
    (qvs outs2 : List spath) :
    store_done ce2 ρ dn outs →
    exec_sound ce2 ρ (pst p1) qvs →
    paths_wf (svars (pst p1)).length qvs →
    store_rel (pret p1) qvs outs2 →
    store_done ce2 ρ (dn ++ [p1]) (outs ++ outs2) := by
  intro Hdn Hs Hwf Hrel p2 Hin
  rcases List.mem_append.mp Hin with Hin | Hin
  · obtain ⟨qv, H1, H2, H3⟩ := Hdn p2 Hin
    exact ⟨qv, H1, H2, store_ok_mono _ _ _ _ (fun _ h => List.mem_append_left _ h) H3⟩
  · rw [List.mem_singleton.mp Hin]
    exact ⟨qvs, Hs, Hwf, store_ok_mono _ _ _ _ (fun _ h => List.mem_append_right _ h)
      (store_rel_ok _ _ _ Hrel)⟩

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_execStore (t : ctype) (e1 e2 : cexpr) :
    (⊢ exec_like (GF := GF) checker.exec e1) →
    (⊢ exec_like (GF := GF) checker.exec e2) →
    ⊢ exec_like (GF := GF) checker.execStore (CEStore t e1 e2) := by
  intro Hex1 Hex2
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  icases He with ⟨%lt, %la, %lb, #Hnode, #Ht, #Ha, #Hb⟩
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
    ihave HI : (∃ (k : w64) (pcur : checker.Path) (so : GoSlice) (os : List checker.Path)
        (outs : List spath),
        "i" ∷ i_ptr ↦ k ∗ "p" ∷ p_ptr ↦ pcur ∗ "out" ∷ out_ptr ↦ so ∗
        "Hos" ∷ so ↦* os ∗ "Hcap" ∷ ownSliceCap checker.Path so (DFrac.own 1) ∗
        "Hosp" ∷ ([∗list] y;o ∈ os;outs, is_path y o) ∗
        "Hrest" ∷ ([∗list] y;o ∈ xs.drop (sint.nat k);ps0.drop (sint.nat k), is_path y o) ∗
        "%Hdone" ∷ ⌜store_done e2 ρ (ps0.take (sint.nat k)) outs⌝ ∗
        "%Hwfo" ∷ ⌜paths_wf (svars sst).length outs⌝ ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ xs.length⌝ : IProp GF)
        $$ [i p out Hxs Hnil Hnilcap]
    · iexists W64 0, _, slice.nil, [], []
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero, List.drop_zero]
      iframe i p out Hxs Hnil Hnilcap
      isplitr
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
      ipureintro
      refine ⟨?_, paths_wf_nil _, ?_⟩
      · intro _ h; cases h
      · word
    wp_for HI
    wp_if_destruct
    · rw [ite_eq_left ⟨Hk.1, Hif⟩]
      list_elem xs (sint.nat k) as x0
      list_elem ps0 (sint.nat k) as p0
      wp_apply wp_load_slice_index s (sint.Z k) xs _ x0 Hk.1 $$ [Hs] with Hs
      · iframe Hs; ipureintro; exact Hx0_lookup
      rw [drop_cons_of_getElem? _ _ _ Hx0_lookup, drop_cons_of_getElem? _ _ _ Hp0_lookup]
      icases (BigSepL2.bigSepL2_cons (Φ := fun _ y o => is_path (GF := GF) y o)).1 $$ Hrest
        with ⟨Hpp, Hrest⟩
      rw [show is_path x0 p0 = iprop(is_term (GF := GF) x0.Ret' (pret p0) ∗ is_state x0.St' (pst p0))
        from rfl]
      icases Hpp with ⟨#Hret, Hst0⟩
      have Hp0in : p0 ∈ ps0 := List.mem_of_getElem? Hp0_lookup
      wp_apply exec_like_triple _ _ Hex2 lb lρ x0.St' ρ (pst p0) $$ [Hst0] as %s2 %lf2 Hpost2
      · iframe Hst0 Hb Hρ
        ipureintro
        exact ⟨Hwf0.paths_wf_state p0 Hp0in, env_below_mono _ _ _ (Hwf0.paths_wf_grow p0 Hp0in) Hρb⟩
      wp_if_destruct
      · rw [(exec_post_ok _ _ _ _).to_eq]
        icases Hpost2 with ⟨%qvs, Hqvs, %Hwfq, %Hsndq⟩
        wp_apply wp_storeAll le x0.Ret' s2 (pret p0) qvs $$ [Hqvs] as %sqs %lf3 Hpost3
        · iframe Hqvs Hret
        wp_if_destruct
        · icases Hpost3 with ⟨%outs2, Hout2, %Hrel⟩
          unfold is_paths
          icases Hout2 with ⟨%ys, Hys, Hysp⟩
          wp_apply wp_slice_append (t := checker.Path.ty) so os sqs ys (DFrac.own 1)
            $$ [Hos Hcap Hys] as %so' ⟨Hos, Hcap, -⟩
          · iframe Hos Hcap Hys
          wp_for_post
          iframe HΦ Hs e en
          iexists k + W64 1, x0, so', os ++ ys, outs ++ outs2
          have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
          rw [Hk1]
          iframe i p out Hos Hcap Hrest
          ihave %Hlen2' := BigSepL2.bigSepL2_length $$ Hosp
          isplitl [Hosp Hysp]
          · iapply (BigSepL2.bigSepL2_append (Or.inl Hlen2')).2
            iframe Hosp Hysp
          ipureintro
          refine ⟨?_, paths_wf_app _ _ _ Hwfo (paths_wf_mono _ _ _ (Hwf0.paths_wf_grow p0 Hp0in)
            (store_rel_wf _ _ _ _ Hwfq Hrel)), by word⟩
          rw [take_snoc_of_getElem? _ _ _ Hp0_lookup]
          exact store_done_snoc _ _ _ _ _ _ _ Hdone Hsndq Hwfq Hrel
        · wp_for_post
          iapply HΦ
          iapply exec_post_fail _ _ _ _ _ Hif
      · wp_for_post
        iapply HΦ
        iapply exec_post_fail _ _ _ _ _ Hif
    · -- the loop is over
      have Htake : ps0.take (sint.nat k) = ps0 := List.take_of_length_le (by word)
      rw [Htake] at Hdone
      iapply HΦ
      rw [(exec_post_ok _ _ _ _).to_eq]
      iexists outs
      isplitl
      · unfold is_paths; iexists os; iframe Hos Hosp
      · ipureintro
        exact ⟨Hwfo, exec_sound_store _ _ _ _ _ _ _ Hsnd0 Hwf0 Hdone⟩
  · iapply HΦ
    iapply exec_post_fail _ _ _ _ _ Hif

end proof

end Checker
end Perennial
