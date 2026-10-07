/-
Port of `new/checker/fn/execVar.v`.

`checker.execVar` (checker/exec.go): a variable is looked up in the
environment (`envLookup`); an unbound one is a failure, a bound one is the
single path `onePath` builds with the bound term.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundA
import Checkers.Checker.ExecSoundB
import Checkers.Checker.Fn.onePath
import Checkers.Checker.Fn.envLookup

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

theorem wp_execVar (x : GoString) : ⊢ exec_like (GF := GF) checker.execVar (CEVar x) := by
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  iStructNamed He
  wp_auto
  wp_apply wp_envLookup lρ ρ x $$ [] as %lt %okb ⟨%Hok, #Hlt⟩
  · iframe Hρ
  cases Hlk : env_lookup ρ x with
  | none =>
    -- unbound
    obtain rfl : okb = false := by simp [Hok, Hlk]
    wp_auto
    wp_alloc lfail as Hlf
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hlf
    wp_auto
    iapply HΦ
    iapply exec_post_fail _ _ _ _ _ Hnn
  | some xt =>
    obtain rfl : okb = true := by simp [Hok, Hlk]
    rw [is_oterm_some]
    wp_auto
    wp_apply wp_onePath lt lst xt sst $$ [Hst] as %s Hs
    · iframe Hst Hlt
    have Hb : vars_below (svars sst).length xt := env_below_lookup _ _ _ _ Hρb Hlk
    iapply HΦ
    rw [(exec_post_ok _ _ _ _).to_eq]
    iexists _
    iframe Hs
    ipureintro
    exact ⟨paths_wf_single _ _ _ Hwf (Nat.le_refl _) Hb, exec_sound_var _ _ _ _ Hlk Hb⟩

end proof

end Checker
end Perennial
