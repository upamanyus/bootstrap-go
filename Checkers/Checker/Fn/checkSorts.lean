/-
Port of `new/checker/fn/checkSorts.v`.

`checker.checkSorts` (checker/match.go): phase 0 of `checkDisjunct`.
Every atom must be well-sorted under the *declared* logical variables
`vars`, the disjunct's pattern variables, and the sort of the path's
return term (computed under the path's own variables). What the proof
needs from it is `atom_scoped` (MatchSound.lean): the atoms name no logical
variable beyond `vars`, so the caller's valuation and the path's agree on
them.

Lean notes:
* `is_sortenv_discard_persistent` (not in Rocq, where `apply _` finds it).
* Rocq's `default SInt os` is `os.getD SInt`.
* The Go local `at` is a Lean keyword: its points-to is `Hat` in the loop
  invariant.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.DisjunctRo
import Checkers.Checker.MatchSound
import Checkers.Checker.Fn.sortOfEnv
import Checkers.Checker.Fn.SortOf
import Checkers.Checker.Fn.atomWellSorted

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

theorem sort_code_default (os : Option sort) : sort_code (os.getD SInt) = osort_code os := by
  cases os <;> rfl

theorem atom_well_sorted_scoped (E : sort_env) (a : cassn) :
    atom_well_sorted E (some a) = true → atom_scoped (se_vars E).length a := by
  cases a with
  | CAPure x =>
    simp only [atom_well_sorted, atom_scoped]
    split
    · rename_i h; intro _; exact sort_of_pvars E x _ h
    · intro h; cases h
  | CAPointsTo x v =>
    simp only [atom_well_sorted, atom_scoped]
    split
    · rename_i h1 h2; intro _; exact ⟨sort_of_pvars E x _ h1, sort_of_pvars E v _ h2⟩
    · intro h; cases h
  | _ => simp [atom_well_sorted]

theorem scoped_step (k0 : Nat) (atms : List cassn) (k : Nat) (acur : cassn) :
    atms[k]? = some acur →
    (∀ j a, j < k → atms[j]? = some a → atom_scoped k0 a) →
    atom_scoped k0 acur →
    (∀ j a, j < k + 1 → atms[j]? = some a → atom_scoped k0 a) := by
  intro Hk Hpre Hcur j a Hj Ha
  by_cases Hjk : j = k
  · subst Hjk; rw [Hk] at Ha; cases Ha; exact Hcur
  · exact Hpre j a (by omega) Ha

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

instance is_sortenv_discard_persistent (l : Loc) (E : sort_env) :
    Persistent (is_sortenv (GF := GF) DFrac.discard l E) := by
  unfold is_sortenv; infer_instance

theorem wp_checkSorts (pth : checker.Path) (sp : spath) (ld : Loc) (dj : cdisjunct)
    (sv : GoSlice) (vl : List sort) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗
        is_sorts sv vl }}
      (App (App (App (Val (@! checker.checkSorts)) (Val #pth)) (Val #ld)) (Val #sv))
    {{ (lf : Loc), RET #lf;
        is_path pth sp ∗ ⌜lf = null → ∀ a, a ∈ d_atoms dj → atom_scoped vl.length a⌝ }} := by
  wp_start as ⟨Hpath, #Hdj, #Hsv⟩
  unfold is_path
  icases Hpath with ⟨#Hret, Hst⟩
  unfold is_state
  icases Hst with ⟨%hs, %cs, %vs, Hstl, Hheap, Hcond, #Hvars⟩
  unfold is_disjunct_ro
  icases Hdj with ⟨%sp', %sok, %sa, %lfl, %las, #Hld, #Hsp, #Hsok, #Hsa, #Has, %Hpl, %Hfail⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Has
  ihave %Hlena := ownSlice_len _ _ _ $$ Hsa
  iStructNamed Hld
  wp_auto
  wp_apply wp_SortOf vs pth.Ret' (svars (pst sp)) (some (pret sp)) $$ []
  · unfold is_vars; rw [is_oterm_some]; iframe #
  ipersist «$r0»
  generalize hos : osort_of (vars_env (svars (pst sp))) (some (pret sp)) = os
  let E := disjunct_env vl dj (os.getD SInt) (osort_ok os)
  ihave #Henv : is_sortenv DFrac.discard «$r0_ptr» E $$ []
  · unfold is_sortenv
    iexists sv, sp', sok
    simp only [E, disjunct_env, sort_code_default]
    unfold is_sorts at *
    iframe #
  have HE : sort_env_wf E := Hpl
  ihave HI : (∃ (k : w64) (lcur : Loc),
      "i" ∷ i_ptr ↦ k ∗ "Hat" ∷ at_ptr ↦ lcur ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ las.length⌝ ∗
      "%Hpre" ∷ ⌜∀ j a, j < sint.nat k → (d_atoms dj)[j]? = some a →
                  atom_scoped vl.length a⌝ : IProp GF) $$ [i «at»]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    intro j a Hj; rw [show sint.nat (W64 0) = 0 from rfl] at Hj; omega
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hk.1, Hif⟩]
    list_elem las (sint.nat k) as lcur'
    list_elem (d_atoms dj) (sint.nat k) as acur
    have Hklt : sint.nat k < las.length := (List.getElem?_eq_some_iff.mp Hlcur'_lookup).1
    ihave #Hcur := BigSepL2.bigSepL2_lookup (Φ := fun _ l a => is_assn (GF := GF) l a)
      Hlcur'_lookup Hacur_lookup $$ Has
    wp_apply wp_load_slice_index sa (sint.Z k) las _ lcur' Hk.1 $$ [] with -
    · iframe Hsa; ipureintro; exact Hlcur'_lookup
    wp_apply wp_atomWellSorted DFrac.discard «$r0_ptr» lcur' E (some acur) $$ []
      as %lf ⟨_, %Hlf⟩
    · rw [is_oassn_some]; iframe #; ipureintro; exact HE
    wp_if_destruct
    · -- the atom is well-sorted
      have Hws := Hlf.mp rfl
      have Hsc : atom_scoped vl.length acur := atom_well_sorted_scoped E acur Hws
      wp_for_post
      iframe
      iexists k + W64 1, lcur'
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
      exact scoped_step _ _ _ acur Hacur_lookup Hpre Hsc
    · wp_for_post
      iapply HΦ
      iframe Hret
      isplitl
      · iexists hs, cs, vs; iframe Hstl Hheap Hcond Hvars
      · ipureintro; intro h; exact absurd h Hif
  · iapply HΦ
    iframe Hret
    isplitl
    · iexists hs, cs, vs; iframe Hstl Hheap Hcond Hvars
    · ipureintro
      intro _ a Ha
      obtain ⟨j, Hj⟩ := List.getElem?_of_mem Ha
      exact Hpre j a (by have := (List.getElem?_eq_some_iff.mp Hj).1; word) Hj

end proof

end Checker
end Perennial
