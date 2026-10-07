/-
Port of `new/checker/fn/envLookup.v`.

`checker.envLookup` (checker/exec.go): the first binding of a name in the
environment linked list.
-/
import Checkers.Checker.Prelude

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

/-- The recursion runs down the `next` chain, so the induction is on the
environment with the head location universally quantified. -/
theorem wp_envLookup (le : Loc) (ρ : List (GoString × term)) (gx : GoString) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_env le ρ }}
      (App (App (Val (@! checker.envLookup)) (Val #le)) (Val #gx))
    {{ (lt : Loc) (ok : Bool), RET (PairV #lt #ok);
        ⌜ok = decide (env_lookup ρ gx ≠ none)⌝ ∗ is_oterm lt (env_lookup ρ gx) }} := by
  induction ρ generalizing le with
  | nil =>
    -- the empty environment is the nil pointer
    wp_start as He
    simp only [is_env]
    icases He with %Hle
    subst Hle
    wp_auto
    iapply HΦ
    simp only [env_lookup, is_oterm_none]
    isplit <;> ipureintro <;> simp
  | cons yt ρ IH =>
    obtain ⟨gy, ty⟩ := yt
    wp_start as He
    simp only [is_env]
    icases He with ⟨%ltm, %lnx, #Hnode, #Ht, #Hrest⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hnode
    iStructNamed Hnode
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    try wp_auto
    wp_if_destruct
    · -- the head binds the name
      subst Hif
      iapply HΦ
      simp only [env_lookup, ↓reduceIte, is_oterm_some]
      isplit
      · ipureintro; simp
      · iexact Ht
    · -- look further down the chain
      wp_apply IH lnx $$ [] as %lt %ok ⟨%Hok, #Hres⟩
      · iframe #
      iapply HΦ
      simp only [env_lookup, Hif, ↓reduceIte]
      isplit
      · ipureintro; exact Hok
      · iexact Hres

end proof

end Checker
end Perennial
