/-
Port of `new/checker/fn/execExcDo.v`.

`checker.execExcDo` (checker/exec.go): `exception_do e`. Runs `e`; a path
that ended in `execute` returns unit, a path that ended in `return x`
returns `x`, and any other return term is a failure.

Lean notes:
* Rocq's `wp_execExcDo_aux` (naming trap) is not needed; `wp_execExcDo` is
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

theorem wp_execExcDo (e : cexpr) :
    (⊢ exec_like (GF := GF) checker.exec e) →
    ⊢ exec_like (GF := GF) checker.execExcDo (CEExcDo e) := by
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
        "%Hdone" ∷ ⌜∀ q, q ∈ ps0.take (sint.nat n) →
                     (pret q = TExec ∧ mkPath TUnit (pst q) ∈ outs) ∨
                     (∃ x, pret q = TRet x ∧ mkPath x (pst q) ∈ outs)⌝ : IProp GF)
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
      ihave %Hnn0 := is_term_not_null _ _ $$ Hret
      icases is_term_node _ _ $$ Hret with ⟨%ta, %tb, %tc, %Hidx, #Hnode', #Hta, -, -⟩
      iStructNamedSuffix Hnode' "_r"
      rw [show decide (xp.Ret' = null) = false from decide_eq_false Hnn0]
      wp_auto
      by_cases Hc19 : term_code (pret q) = W64 19
      · rw [show decide (term_code (pret q) = W64 19) = true from decide_eq_true Hc19]
        have Hc19 := term_code_TExec _ Hc19
        wp_auto
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
        iframe HΦ Hs e
        iexists n + W64 1, xp, so', ys ++ [checker.Path.mk «$v0_ptr» xp.St'], outs ++ [mkPath TUnit (pst q)]
        have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        rw [Hn1]
        iframe i p out Hys Hcap Hrest
        isplitl [Hysp Hst']
        · iapply BigSepL2.bigSepL2_snoc.2
          iframe Hysp
          rw [show is_path (checker.Path.mk «$v0_ptr» xp.St') (mkPath TUnit (pst q)) =
            iprop(is_term (GF := GF) «$v0_ptr» TUnit ∗ is_state xp.St' (pst q)) from rfl]
          iframe Hst'
          simp only [is_term, tnode]
          iExactEq «$v0»; rfl
        ipureintro
        refine ⟨by word, paths_wf_app _ _ _ Hwfo
          (paths_wf_single _ _ _ (Hwf0.paths_wf_state q Hq) (Hwf0.paths_wf_grow q Hq) trivial), ?_⟩
        intro q' Hq'
        rw [take_snoc_of_getElem? _ _ _ Hq_lookup] at Hq'
        rcases List.mem_append.mp Hq' with Hq' | Hq'
        · rcases Hdone q' Hq' with ⟨H1, H2⟩ | ⟨x', H1, H2⟩
          · exact .inl ⟨H1, List.mem_append_left _ H2⟩
          · exact .inr ⟨x', H1, List.mem_append_left _ H2⟩
        · rw [List.mem_singleton.mp Hq']
          exact .inl ⟨Hc19, List.mem_append_right _ (List.mem_singleton_self _)⟩

      rw [show decide (term_code (pret q) = W64 19) = false from decide_eq_false Hc19]
      wp_auto
      by_cases Hc20 : term_code (pret q) = W64 20
      · rw [show decide (term_code (pret q) = W64 20) = true from decide_eq_true Hc20]
        obtain ⟨xr, Hxr⟩ := term_code_TRet _ Hc20
        rw [Hxr, show term_a (TRet xr) = some xr from rfl, is_oterm_some]
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, _⟩
        wp_auto
        wp_apply wp_slice_append (t := checker.Path.ty) so ys _ [checker.Path.mk ta xp.St']
          (DFrac.own 1) $$ [Hys Hcap Hsl] as %so' ⟨Hys, Hcap, -⟩
        · iframe Hys Hcap Hsl
        wp_for_post
        iframe HΦ Hs e
        iexists n + W64 1, xp, so', ys ++ [checker.Path.mk ta xp.St'], outs ++ [mkPath xr (pst q)]
        have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        rw [Hn1]
        iframe i p out Hys Hcap Hrest
        isplitl [Hysp Hst']
        · iapply BigSepL2.bigSepL2_snoc.2
          iframe Hysp
          rw [show is_path (checker.Path.mk ta xp.St') (mkPath xr (pst q)) =
            iprop(is_term (GF := GF) ta xr ∗ is_state xp.St' (pst q)) from rfl]
          iframe Hst' Hta
        ipureintro
        refine ⟨by word, paths_wf_app _ _ _ Hwfo
          (paths_wf_single _ _ _ (Hwf0.paths_wf_state q Hq) (Hwf0.paths_wf_grow q Hq) (by have := Hwf0.paths_wf_ret q Hq; rw [Hxr] at this; exact this)), ?_⟩
        intro q' Hq'
        rw [take_snoc_of_getElem? _ _ _ Hq_lookup] at Hq'
        rcases List.mem_append.mp Hq' with Hq' | Hq'
        · rcases Hdone q' Hq' with ⟨H1, H2⟩ | ⟨x', H1, H2⟩
          · exact .inl ⟨H1, List.mem_append_left _ H2⟩
          · exact .inr ⟨x', H1, List.mem_append_left _ H2⟩
        · rw [List.mem_singleton.mp Hq']
          exact .inr ⟨xr, Hxr, List.mem_append_right _ (List.mem_singleton_self _)⟩

      rw [show decide (term_code (pret q) = W64 20) = false from decide_eq_false Hc20]
      wp_auto
      wp_alloc lfail as Hlf
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hlf
      wp_auto
      wp_for_post
      iapply HΦ
      iapply exec_post_fail _ _ _ _ _ Hnn
    · -- the loop is over
      have Htake : ps0.take (sint.nat n) = ps0 := List.take_of_length_le (by word)
      rw [Htake] at Hdone
      iapply HΦ
      rw [(exec_post_ok _ _ _ _).to_eq]
      iexists outs
      isplitl
      · unfold is_paths; iexists ys; iframe Hys Hysp
      · ipureintro; exact ⟨Hwfo, exec_sound_exc_do _ _ _ _ _ Hsnd0 Hdone⟩
  · iapply HΦ
    iapply exec_post_fail _ _ _ _ _ Hif

end proof

end Checker
end Perennial
