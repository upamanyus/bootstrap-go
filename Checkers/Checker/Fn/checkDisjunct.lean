/-
Port of `new/checker/fn/checkDisjunct.v`.

`checker.checkDisjunct` (checker/match.go): does path `p` satisfy the
parsed disjunct `d`? Phase 0 (`checkSorts`), phase 1 (`matchHeap`) and
phase 2 (`checkPure`); a `nil` answer gives `path_sat_dj` through
`match_path_sat` (MatchSound.lean).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.VerifyDef
import Checkers.Checker.MatchSound
import Checkers.Checker.Fn.instantiate
import Checkers.Checker.Fn.checkSorts
import Checkers.Checker.Fn.matchHeap
import Checkers.Checker.Fn.checkPure

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

theorem is_subst_replicate_None (k : Nat) :
    ⊢ [∗list] li;oi ∈ List.replicate k null;List.replicate k (none : Option term),
        is_oterm (GF := GF) li oi := by
  induction k with
  | zero => exact BigSepL2.bigSepL2_nil.2
  | succ k ih =>
    simp only [List.replicate_succ]
    iapply BigSepL2.bigSepL2_cons.2
    isplitl []
    · simp only [is_oterm]; ipureintro; trivial
    · iapply ih

theorem wp_checkDisjunct (pth : checker.Path) (sp : spath) (ld : Loc) (dj : cdisjunct)
    (sv : GoSlice) (vl : List sort) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗
        is_sorts sv vl }}
      (App (App (App (Val (@! checker.checkDisjunct)) (Val #pth)) (Val #ld)) (Val #sv))
    {{ (lf : Loc), RET #lf;
        is_path pth sp ∗ ⌜lf = null → d_fail dj = false ∧ path_sat_dj vl sp dj⌝ }} := by
  wp_start as ⟨Hpath, #Hdj, #Hsv⟩
  icases is_disjunct_ro_open _ _ $$ Hdj with
    ⟨%sp', %sok, %sa, %lfl, %las, #Hld, #Hsp, #Hsok, #Hsa, #Has, %Hpl, %Hfail⟩
  ihave %Hlenp := ownSlice_len _ _ _ $$ Hsp
  rw [List.length_map] at Hlenp
  iStructNamed Hld
  unfold is_path
  icases Hpath with ⟨#Hret, Hst⟩
  unfold is_state
  icases Hst with ⟨%hs, %cs, %vs, Hstl, Hheap, Hcond, #Hvars⟩
  ihave %Hstnn := typedPointsto_not_null $$ Hstl
  ihave Hpath : is_path pth sp $$ [Hstl Hheap Hcond]
  · unfold is_path is_state
    iframe Hret
    iexists hs, cs, vs
    iframe Hstl Hheap Hcond Hvars
  wp_auto
  wp_if_destruct
  · have Hdf : d_fail dj = false := Hfail.mp rfl
    rw [decide_eq_false Hstnn]
    wp_auto
    wp_apply wp_checkSorts pth sp ld dj sv vl $$ [Hpath] as %lf1 ⟨Hpath, %Hsc⟩
    · iframe Hpath Hdj Hsv
    wp_if_destruct
    · have Hsc' := Hsc rfl
      wp_apply wp_slice_make2 as %ss ⟨Hss, -⟩
      · ipureintro; word
      ihave Hsub : is_subst ss (List.replicate (d_pats dj).length none) $$ [Hss]
      · unfold is_subst
        iexists List.replicate (d_pats dj).length null
        rw [show sint.nat sp'.len = (d_pats dj).length by omega,
          show (zero_val Loc) = null from rfl]
        iframe Hss
        iapply is_subst_replicate_None
      wp_apply wp_matchHeap pth sp ld dj ss $$ [Hpath Hsub] as %lf2 ⟨Hpath, %σ, Hsub, %Hm⟩
      · iframe Hpath Hsub Hdj
      wp_if_destruct
      · obtain ⟨us, dn, Hinv, Hund⟩ := Hm rfl
        wp_apply wp_checkPure pth sp ld dj ss σ $$ [Hpath Hsub] as %lf3 ⟨Hpath, Hsub, %Hpure⟩
        · iframe Hpath Hsub Hdj
        iapply HΦ
        isplitl [Hpath]
        · unfold is_path is_state; iexact Hpath
        ipureintro
        intro Hnull
        refine ⟨Hdf, ?_⟩
        intro ext' ffi' fi' fs' gctx' hlc' GF' hG' sem'
        exact match_path_sat (GF := GF') vl sp dj σ us dn Hpl Hsc' Hinv Hund (Hpure Hnull)
      · -- phase 1 failed
        iapply HΦ
        isplitl [Hpath]
        · unfold is_path is_state; iexact Hpath
        ipureintro; intro h; exact absurd h Hif
    · -- ill-sorted
      iapply HΦ
      isplitl [Hpath]
      · unfold is_path is_state; iexact Hpath
      ipureintro; intro h; exact absurd h Hif
  · -- the disjunct is malformed
    iapply HΦ
    isplitl [Hpath]
    · unfold is_path is_state; iexact Hpath
    ipureintro; intro h; exact absurd h Hif

end proof

end Checker
end Perennial
