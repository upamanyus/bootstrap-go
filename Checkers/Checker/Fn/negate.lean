/-
Port of `new/checker/fn/negate.v`.

`checker.negate` (checker/exec.go): logical negation of a term, with the
double negation cancelled.
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

/-- The kind code `W64 17` belongs to `TNot` alone. -/
theorem term_code_TNot (u : term) : term_code u = W64 17 → ∃ x, u = TNot x := by
  cases u <;> (try (rename_i sg _ _; cases sg)) <;>
    simp only [term_code, ↓reduceIte, Bool.false_eq_true] <;> intro Hc <;>
    first | exact ⟨_, rfl⟩ | exact absurd Hc (by decide)

/-- ... so every other node is negated by wrapping it. -/
theorem negate_not_TNot (u : term) : term_code u ≠ W64 17 → negate u = TNot u := by
  cases u <;> simp [term_code, negate]

theorem wp_negate (lt : Loc) (tm : term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_term lt tm }}
      (App (Val (@! checker.negate)) (Val #lt))
    {{ (l : Loc), RET #l; is_term l (negate tm) }} := by
  wp_start as #Ht
  ihave ⟨%la, %lb, %lc, %Hwf, #Hn, #Ha, #Hb, #Hc⟩ := is_term_node _ _ $$ Ht
  iStructNamed Hn
  wp_auto
  wp_if_destruct
  · -- `tm` is already a negation: the `A` child is returned as is
    obtain ⟨x, rfl⟩ := term_code_TNot _ Hif
    simp only [negate, term_a, is_oterm_some]
    iapply HΦ
    iexact Ha
  · -- any other node: allocate a fresh `TNot` wrapper
    rw [negate_not_TNot _ Hif]
    wp_alloc l as Hl
    ipersist Hl
    wp_auto
    iapply HΦ
    simp only [is_term]
    iexists lt
    isplitl [Hl]
    · iExactEq Hl
      rfl
    · iexact Ht

end proof

end Checker
end Perennial
