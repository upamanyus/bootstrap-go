/-
Port of `new/checker/fn/matchTerm.v`.

`checker.matchTerm` (checker/match.go): match a pattern term against a
path term, binding pattern variables into `subst`. What a `nil` result
establishes is `match_rel` (MatchSound.lean); a failure is a freshly
allocated `Failure` the caller owns (matchAtom writes its `Atom` field).

Lean notes:
* `<[m := Some t0]> σ` is `σ.set m (some t0)`.
* `is_disjunct_ro_open` (an extra helper, not in Rocq) unfolds
  `is_disjunct_ro` for one hypothesis, so the Löb hypothesis keeps its
  folded precondition.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.MatchSound
import Checkers.Checker.Fn.instantiate
import Checkers.Checker.Fn.termEq
import Checkers.Checker.Fn.sortOfEnv
import Checkers.Checker.Fn.SortOf

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

theorem is_tpat_inv (x : term) : is_tpat x = true → ∃ n, x = TPat n := by
  cases x <;> simp [is_tpat]
theorem is_tresult_inv (x : term) : is_tresult x = true → x = TResult := by
  cases x <;> simp [is_tresult]

section proof0
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem is_disjunct_ro_open (l : Loc) (dj : cdisjunct) :
    is_disjunct_ro (GF := GF) l dj ⊢ ∃ (sp sok sa : GoSlice) (lf : Loc) (las : List Loc),
      l ↦□ checker.disjunct.mk sp sok sa lf ∗
      sp ↦*□ ((d_pats dj).map sort_code) ∗
      sok ↦*□ d_pat_ok dj ∗
      sa ↦*□ las ∗
      ([∗list] la;x ∈ las;d_atoms dj, is_assn la x) ∗
      ⌜(d_pats dj).length = (d_pat_ok dj).length⌝ ∗
      ⌜lf = null ↔ d_fail dj = false⌝ := by
  unfold is_disjunct_ro; exact .rfl

end proof0

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

def match_post (ss : GoSlice) (σ : List (Option term)) (pats : List sort)
    (pok : List Bool) (PV : List sort) (r : term) (op oa : Option term) (lf : Loc) : IProp GF :=
  iprop(∃ σ', is_subst ss σ' ∗ ⌜σ'.length = σ.length⌝ ∗
    (⌜lf = null ∧ match_rel pats pok PV r op oa σ σ'⌝ ∨ ∃ fv : checker.Failure, lf ↦ fv))

theorem wp_matchTerm (lp lq : Loc) (op oa : Option term) (ss : GoSlice)
    (σ : List (Option term)) (ld : Loc) (dj : cdisjunct) (sv : GoSlice)
    (PV : List sort) (lr : Loc) (r : term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_oterm lp op ∗ is_oterm lq oa ∗
        is_subst ss σ ∗ ⌜σ.length = (d_pats dj).length⌝ ∗ is_disjunct_ro ld dj ∗
        sv ↦*□ (PV.map sort_code) ∗ is_term lr r }}
      (App (App (App (App (App (App (Val (@! checker.matchTerm)) (Val #lp)) (Val #lq))
        (Val #ss)) (Val #ld)) (Val #sv)) (Val #lr))
    {{ (lf : Loc), RET #lf; match_post ss σ (d_pats dj) (d_pat_ok dj) PV r op oa lf }} := by
  iloeb as IH generalizing %lp %lq %op %oa %σ
  wp_start as ⟨#Hop, #Hoa, Hsub, %Hlσ, #Hdj, #Hsv, #Hr⟩
  ihave %Hnp := is_oterm_null _ _ $$ Hop
  ihave %Hna := is_oterm_null _ _ $$ Hoa
  wp_auto
  wp_if_destruct
  · -- `pat` is nil
    obtain rfl : op = none := Hnp.mp rfl
    wp_if_destruct
    · obtain rfl : oa = none := Hna.mp rfl
      iapply HΦ
      unfold match_post; iexists σ; iframe Hsub
      isplitr
      · ipureintro; rfl
      · ileft; ipureintro; exact ⟨rfl, MR_nil σ⟩
    · wp_alloc lf as Hf
      wp_auto
      iapply HΦ
      unfold match_post; iexists σ; iframe Hsub
      isplitr
      · ipureintro; rfl
      · iright; iexists _; iexact Hf
  · cases op with
    | none => exact absurd (Hnp.mpr rfl) Hif
    | some x =>
    rw [is_oterm_some]
    icases is_term_node _ _ $$ Hop with ⟨%lxa, %lxb, %lxc, %Hwx, #Hxn, #Hxa, #Hxb, #Hxc⟩
    icases is_disjunct_ro_open _ _ $$ Hdj with
      ⟨%sp, %sok, %sa, %lfl, %las, #Hld, #Hsp, #Hsok, #Hsa, #Has, %Hpl, %Hfail⟩
    iStructNamedSuffix Hxn "_x"
    iStructNamedSuffix Hld "_d"
    wp_auto
    rw [is_tpat_code]
    cases Hpx : is_tpat x
    · wp_auto
      rw [is_tresult_code]
      cases Hrx : is_tresult x
      · wp_auto
        wp_if_destruct
        · -- `act` is nil
          wp_alloc lf as Hf
          wp_auto
          iapply HΦ
          unfold match_post; iexists σ; iframe Hsub
          isplitr
          · ipureintro; rfl
          · iright; iexists _; iexact Hf
        cases oa with
        | none => exact absurd (Hna.mpr rfl) Hif
        | some y =>
        rw [is_oterm_some]
        icases is_term_node _ _ $$ Hoa with ⟨%lya, %lyb, %lyc, %Hwy, #Hyn, #Hya, #Hyb, #Hyc⟩
        iStructNamedSuffix Hyn "_y"
        wp_auto
        by_cases Hc : term_code x = term_code y
        rotate_left
        · rw [decide_eq_false Hc]
          wp_auto
          wp_alloc lf as Hf
          wp_auto
          iapply HΦ
          unfold match_post; iexists σ; iframe Hsub
          isplitr
          · ipureintro; rfl
          · iright; iexists _; iexact Hf
        rw [decide_eq_true Hc]
        wp_auto
        by_cases Hn : term_num x = term_num y
        rotate_left
        · rw [decide_eq_false Hn]
          wp_auto
          wp_alloc lf as Hf
          wp_auto
          iapply HΦ
          unfold match_post; iexists σ; iframe Hsub
          isplitr
          · ipureintro; rfl
          · iright; iexists _; iexact Hf
        rw [decide_eq_true Hn]
        wp_auto
        -- the three children, left to right
        wp_apply IH $$ %lxa %lya %(term_a x) %(term_a y) %σ [Hsub] as %lf1 Hp1
        · iframe Hsub; iframe #; ipureintro; exact Hlσ
        unfold match_post
        icases Hp1 with ⟨%σ1, Hsub, %Hl1, (⟨%Hn1, %Hm1⟩ | ⟨%fv1, Hf1⟩)⟩
        rotate_left
        · ihave %Hnn := typedPointsto_not_null $$ Hf1
          wp_if_destruct
          · exact absurd rfl Hnn
          iapply HΦ
          iexists σ1; iframe Hsub
          isplitr
          · ipureintro; exact Hl1
          · iright; iexists _; iexact Hf1
        subst Hn1
        wp_auto
        wp_apply IH $$ %lxb %lyb %(term_b x) %(term_b y) %σ1 [Hsub] as %lf2 Hp2
        · iframe Hsub; iframe #; ipureintro; omega
        icases Hp2 with ⟨%σ2, Hsub, %Hl2, (⟨%Hn2, %Hm2⟩ | ⟨%fv2, Hf2⟩)⟩
        rotate_left
        · ihave %Hnn := typedPointsto_not_null $$ Hf2
          wp_if_destruct
          · exact absurd rfl Hnn
          iapply HΦ
          iexists σ2; iframe Hsub
          isplitr
          · ipureintro; omega
          · iright; iexists _; iexact Hf2
        subst Hn2
        wp_auto
        wp_apply IH $$ %lxc %lyc %(term_c x) %(term_c y) %σ2 [Hsub] as %lf3 Hp3
        · iframe Hsub; iframe #; ipureintro; omega
        iapply HΦ
        icases Hp3 with ⟨%σ3, Hsub, %Hl3, (⟨%Hn3, %Hm3⟩ | Hf3)⟩
        · iexists σ3; iframe Hsub
          isplitr
          · ipureintro; omega
          · ileft; ipureintro
            exact ⟨Hn3, MR_node x y σ σ1 σ2 σ3 Hpx Hrx Hc Hn Hwx Hwy Hm1 Hm2 Hm3⟩
        · iexists σ3; iframe Hsub
          isplitr
          · ipureintro; omega
          · iright; iexact Hf3
      · -- `pat` is `ret`: match the return term instead
        obtain rfl := is_tresult_inv _ Hrx
        wp_auto
        wp_apply IH $$ %lr %lq %(some r) %oa %σ [Hsub] as %lf Hpost
        · rw [is_oterm_some]; iframe Hsub; iframe #; ipureintro; exact Hlσ
        iapply HΦ
        unfold match_post
        icases Hpost with ⟨%σ', Hs, %Hl, Hor⟩
        iexists σ'; iframe Hs
        isplitr
        · ipureintro; exact Hl
        icases Hor with (⟨%Hn, %Hm⟩ | Hf)
        · ileft; ipureintro; exact ⟨Hn, MR_result _ _ _ Hm⟩
        · iright; iexact Hf
    · -- `pat` is a pattern variable
      obtain ⟨m, rfl⟩ := is_tpat_inv _ Hpx
      simp only [term_num, term_idx_wf, idx_wf] at Hwx ⊢
      unfold is_subst
      icases Hsub with ⟨%ls, Hs, #Hls⟩
      ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hls
      ihave %Hlen := ownSlice_len _ _ _ $$ Hs
      ihave %Hlenok := ownSlice_len _ _ _ $$ Hsok
      ihave %Hlenp := ownSlice_len _ _ _ $$ Hsp
      wp_auto
      wp_if_destruct
      · -- out of range
        wp_alloc lf as Hf
        wp_auto
        iapply HΦ
        unfold match_post; iexists σ
        isplitl [Hs]
        · unfold is_subst; iexists ls; iframe Hs Hls
        isplitr
        · ipureintro; rfl
        · iright; iexists _; iexact Hf
      have Hm : m < σ.length := by word
      have Hb : 0 ≤ sint.Z (W64 m) ∧ sint.Z (W64 m) < sint.Z sok.len := by word
      have Hsn : sint.nat (W64 m) = m := by word
      list_elem (d_pat_ok dj) m as okm
      rw [ite_eq_left Hb]
      wp_apply wp_load_slice_index sok (sint.Z (W64 m)) _ _ okm Hb.1 $$ [] as _
      · iframe Hsok; ipureintro; rw [show (sint.Z (W64 m)).toNat = m by word]; exact Hokm_lookup
      cases okm
      · -- not a declared pattern variable
        wp_auto
        wp_alloc lf as Hf
        wp_auto
        iapply HΦ
        unfold match_post; iexists σ
        isplitl [Hs]
        · unfold is_subst; iexists ls; iframe Hs Hls
        isplitr
        · ipureintro; rfl
        · iright; iexists _; iexact Hf
      wp_auto
      have Hbs : 0 ≤ sint.Z (W64 m) ∧ sint.Z (W64 m) < sint.Z ss.len := by word
      have Hmz : (sint.Z (W64 m)).toNat = m := by word
      list_elem ls m as li
      list_elem σ m as oi
      ihave #Hli := BigSepL2.bigSepL2_lookup (Φ := fun _ li oi => is_oterm (GF := GF) li oi)
        Hli_lookup Hoi_lookup $$ Hls
      ihave %Hlin := is_oterm_null _ _ $$ Hli
      rw [ite_eq_left Hbs]
      wp_apply wp_load_slice_index ss (sint.Z (W64 m)) ls _ li Hbs.1 $$ [Hs] with Hs
      · iframe Hs; ipureintro; rw [Hmz]; exact Hli_lookup
      wp_if_destruct
      · -- unbound so far: bind it, if the sorts agree
        obtain rfl : oi = none := Hlin.mp rfl
        wp_apply wp_SortOf sv lq PV oa $$ []
        · iframe #
        cases Hso : osort_of (vars_env PV) oa with
        | none =>
          simp only [osort_ok, osort_code]
          wp_auto
          wp_alloc lf as Hf
          wp_auto
          iapply HΦ
          unfold match_post; iexists σ
          isplitl [Hs]
          · unfold is_subst; iexists ls; iframe Hs Hls
          isplitr
          · ipureintro; rfl
          · iright; iexists _; iexact Hf
        | some s0 =>
        cases oa with
        | none => simp [osort_of] at Hso
        | some t0 =>
        simp only [osort_of] at Hso
        simp only [osort_ok, osort_code]
        list_elem (d_pats dj) m as pm
        wp_auto
        have Hbp : 0 ≤ sint.Z (W64 m) ∧ sint.Z (W64 m) < sint.Z sp.len := by
          simp only [List.length_map] at Hlenp; word
        rw [ite_eq_left Hbp]
        wp_apply wp_load_slice_index sp (sint.Z (W64 m)) _ _ (sort_code pm) Hbp.1 $$ [] as _
        · iframe Hsp; ipureintro; rw [Hmz, List.getElem?_map, Hpm_lookup]; rfl
        by_cases Hsc : s0 = pm
        · subst Hsc
          rw [decide_eq_true rfl]
          wp_auto
          rw [ite_eq_left Hbs]
          wp_apply wp_store_slice_index ss (sint.Z (W64 m)) ls lq $$ [Hs] as Hs
          · iframe Hs; ipureintro; omega
          rw [Hmz]
          iapply HΦ
          unfold match_post; iexists σ.set m (some t0)
          isplitl [Hs]
          · unfold is_subst; iexists ls.set m lq; iframe Hs
            icases BigSepL2.bigSepL2_insert_acc (Φ := fun _ li oi => is_oterm (GF := GF) li oi)
              Hli_lookup Hoi_lookup $$ Hls with ⟨-, Hins⟩
            iapply Hins
            iexact Hoa
          isplitr
          · ipureintro; exact List.length_set
          · ileft; ipureintro
            exact ⟨rfl, MR_pat_new m t0 s0 σ Hoi_lookup Hokm_lookup Hpm_lookup Hso⟩
        · rw [decide_eq_false (fun h => Hsc (sort_code_inj _ _ h))]
          wp_auto
          wp_alloc lf as Hf
          wp_auto
          iapply HΦ
          unfold match_post; iexists σ
          isplitl [Hs]
          · unfold is_subst; iexists ls; iframe Hs Hls
          isplitr
          · ipureintro; rfl
          · iright; iexists _; iexact Hf
      · -- already bound: the two terms must agree
        cases oi with
        | none => exact absurd (Hlin.mpr rfl) Hif
        | some y =>
        rw [ite_eq_left Hbs]
        wp_apply wp_load_slice_index ss (sint.Z (W64 m)) ls _ li Hbs.1 $$ [Hs] with Hs
        · iframe Hs; ipureintro; rw [Hmz]; exact Hli_lookup
        wp_apply wp_termEq li lq (some y) oa $$ []
        · iframe #
        by_cases Hy : some y = oa
        · subst Hy
          rw [decide_eq_true rfl]
          wp_auto
          iapply HΦ
          unfold match_post; iexists σ
          isplitl [Hs]
          · unfold is_subst; iexists ls; iframe Hs Hls
          isplitr
          · ipureintro; rfl
          · ileft; ipureintro
            refine ⟨rfl, MR_pat_old m y σ ?_ Hokm_lookup⟩
            exact Hoi_lookup
        · rw [decide_eq_false Hy]
          wp_auto
          rw [ite_eq_left Hbs]
          wp_apply wp_load_slice_index ss (sint.Z (W64 m)) ls _ li Hbs.1 $$ [Hs] with Hs
          · iframe Hs; ipureintro; rw [Hmz]; exact Hli_lookup
          wp_alloc lf as Hf
          wp_auto
          iapply HΦ
          unfold match_post; iexists σ
          isplitl [Hs]
          · unfold is_subst; iexists ls; iframe Hs Hls
          isplitr
          · ipureintro; rfl
          · iright; iexists _; iexact Hf

end proof

end Checker
end Perennial
