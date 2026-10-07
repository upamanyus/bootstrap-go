/-
Port of `new/checker/fn/execIfs.v`.

`checker.execIfs` (checker/exec.go): `if: c then e1 else e2`. Runs the
condition, then `execIf` on each of its paths, concatenating the results.

Lean notes:
* Rocq's `wp_execIfs_aux` (naming trap) is not needed; `wp_execIfs` is
  proved directly.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundA
import Checkers.Checker.ExecSoundB
import Checkers.Checker.ExecSoundC
import Checkers.Checker.Fn.execIf

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- What the loop has established for a prefix of the condition's paths. -/
def ifs_done [FfiSyntax] (ct cf : cexpr) (ρ : List (GoString × term)) (dn outs : List spath) :
    Prop :=
  ∀ p1, p1 ∈ dn → sort_of_vars (svars (pst p1)) (pret p1) = some SBool ∧
                  ∃ qvs, qvs ⊆ outs ∧ if_ok ct cf ρ p1 qvs

theorem ifs_done_snoc [FfiSyntax] (ct cf : cexpr) ρ (dn outs : List spath) (p1 : spath)
    (qvs : List spath) :
    ifs_done ct cf ρ dn outs →
    sort_of_vars (svars (pst p1)) (pret p1) = some SBool →
    if_ok ct cf ρ p1 qvs →
    ifs_done ct cf ρ (dn ++ [p1]) (outs ++ qvs) := by
  intro Hdn Hs Hok p2 Hin
  rcases List.mem_append.mp Hin with Hin | Hin
  · obtain ⟨Hs2, qv, Hsub, Hok2⟩ := Hdn p2 Hin
    exact ⟨Hs2, qv, fun _ h => List.mem_append_left _ (Hsub h), Hok2⟩
  · rw [List.mem_singleton.mp Hin]
    exact ⟨Hs, qvs, fun _ h => List.mem_append_right _ h, Hok⟩

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_execIfs (cc ct cf : cexpr) :
    (⊢ exec_like (GF := GF) checker.exec cc) → (⊢ exec_like (GF := GF) checker.exec ct) →
    (⊢ exec_like (GF := GF) checker.exec cf) →
    ⊢ exec_like (GF := GF) checker.execIfs (CEIf cc ct cf) := by
  intro Hex1 Hext Hexf
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  icases He with ⟨%lcc, %la, %lb, #Hnode, #Hc, #Ha, #Hb⟩
  ihave #He' : is_expr (GF := GF) le (CEIf cc ct cf) $$ []
  · simp only [is_expr]; iexists lcc, la, lb; iframe Hnode Hc Ha Hb
  simp only [enode0] at *
  iStructNamed Hnode
  wp_auto
  wp_apply exec_like_triple _ _ Hex1 lcc lρ lst ρ sst $$ [Hst] as %s %lf Hpost
  · iframe Hst Hc Hρ; ipureintro; exact ⟨Hwf, Hρb⟩
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
        "%Hdone" ∷ ⌜ifs_done ct cf ρ (ps0.take (sint.nat k)) outs⌝ ∗
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
      wp_apply wp_execIf le lρ x0.Ret' x0.St' cc ct cf (pret p0) ρ (pst p0) Hext Hexf $$ [Hst0]
        as %sps2 %lfl2 Hpost2
      · iframe Hst0 He' Hρ Hret
        ipureintro
        exact ⟨Hwf0.paths_wf_state p0 Hp0in,
          env_below_mono _ _ _ (Hwf0.paths_wf_grow p0 Hp0in) Hρb, Hwf0.paths_wf_ret p0 Hp0in⟩
      wp_if_destruct
      · unfold execIf_post
        rw [ite_eq_left rfl]
        icases Hpost2 with ⟨%qvs, Hq, %Hwfq, %Hsort, %Hok⟩
        unfold is_paths
        icases Hq with ⟨%ys, Hys, Hysp⟩
        wp_apply wp_slice_append (t := checker.Path.ty) so os sps2 ys (DFrac.own 1)
          $$ [Hos Hcap Hys] as %so' ⟨Hos, Hcap, -⟩
        · iframe Hos Hcap Hys
        wp_for_post
        iframe HΦ Hs e en
        iexists k + W64 1, x0, so', os ++ ys, outs ++ qvs
        have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        rw [Hk1]
        iframe i p out Hos Hcap Hrest
        ihave %Hlen2' := BigSepL2.bigSepL2_length $$ Hosp
        isplitl [Hosp Hysp]
        · iapply (BigSepL2.bigSepL2_append (Or.inl Hlen2')).2
          iframe Hosp Hysp
        ipureintro
        refine ⟨?_, paths_wf_app _ _ _ Hwfo (paths_wf_mono _ _ _ (Hwf0.paths_wf_grow p0 Hp0in) Hwfq),
          by word⟩
        rw [take_snoc_of_getElem? _ _ _ Hp0_lookup]
        exact ifs_done_snoc _ _ _ _ _ _ _ Hdone Hsort Hok
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
        exact ⟨Hwfo, exec_sound_if_gen _ _ _ _ _ _ _ Hsnd0 Hwf0 (fun p1 Hp1 => (Hdone p1 Hp1).1)
          (fun p1 Hp1 => (Hdone p1 Hp1).2)⟩
  · iapply HΦ
    iapply exec_post_fail _ _ _ _ _ Hif

end proof

end Checker
end Perennial
