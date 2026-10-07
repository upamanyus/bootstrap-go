/-
Port of `new/checker/fn/execConvert.v`.

`checker.execConvert` (checker/exec.go): a conversion is accepted only
between a supported type (`TypeSort`) and itself (`TypeEq`), where it is
the identity; the result is then that of the operand, by a tail call to
`exec`.

Lean notes:
* Rocq's `wp_execConvert_aux` (naming trap) is not needed; `wp_execConvert`
  is proved directly.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.ExecSoundA
import Checkers.Checker.ExecSoundB
import Checkers.Checker.Fn.TypeSort
import Checkers.Checker.Fn.TypeEq

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

theorem wp_execConvert (t1 t2 : ctype) (e : cexpr) :
    (⊢ exec_like (GF := GF) checker.exec e) →
    ⊢ exec_like (GF := GF) checker.execConvert (CEConvert t1 t2 e) := by
  intro Hex1
  apply exec_like_intro
  intro le lρ lst ρ sst
  wp_start as ⟨#He, #Hρ, Hst, %Hwf, %Hρb⟩
  simp only [is_expr]
  icases He with ⟨%lt1, %lt2, %la, #Hnode, #Ht1, #Ht2, #Ha⟩
  iStructNamed Hnode
  wp_auto
  wp_apply wp_TypeSort lt1 (some t1) $$ []
  · rw [is_otype_some]; iframe Ht1
  wp_apply wp_TypeEq (some t1) lt1 lt2 (some t2) $$ []
  · rw [is_otype_some, is_otype_some]; iframe Ht1 Ht2
  by_cases Hty : t1 = t2
  · subst Hty
    rw [show decide (some t1 = some t1) = true from decide_eq_true rfl]
    wp_auto
    wp_apply exec_like_triple _ _ Hex1 la lρ lst ρ sst $$ [Hst] as %s %lf Hpost
    · iframe Hst Ha Hρ; ipureintro; exact ⟨Hwf, Hρb⟩
    iapply HΦ
    unfold exec_post
    split
    · icases Hpost with ⟨%ps0, Hps, %Hwf0, %Hsnd0⟩
      iexists ps0
      iframe Hps
      ipureintro
      exact ⟨Hwf0, exec_sound_convert _ _ _ _ _ Hsnd0⟩
    · itrivial
  · rw [show decide (some t1 = some t2) = false from decide_eq_false (by simpa using Hty)]
    wp_auto
    wp_alloc lfail as Hlf
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hlf
    wp_auto
    iapply HΦ
    iapply exec_post_fail _ _ _ _ _ Hnn

end proof

end Checker
end Perennial
