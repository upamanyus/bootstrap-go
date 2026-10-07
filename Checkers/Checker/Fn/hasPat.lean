/-
Port of `new/checker/fn/hasPat.v`.

`checker.hasPat` (checker/match.go): does a term still mention a pattern
variable?

Lean notes:
* The mirror `has_pat`, `ohas_pat`, `is_tpat` and the pure lemmas are outside
  the proof section, so match_sound can use `has_pat_node` directly (Rocq
  had to re-prove it there).
* Iris has a global notation `a || b || c` (three-way disjointness), so a
  chain of Boolean `||` must be parenthesised: `(a || b) || c`.
* `is_tpat`/`is_tpat_code` live here only; Fn/instantiate.lean imports this
  file instead of redefining them (Rocq has a copy in each file).
-/
import Checkers.Checker.Prelude

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- Mirrors `hasPat`: `TPat` anywhere below, reached through the `A`, `B` and
`C` fields, which is exactly `term_a`/`term_b`/`term_c`. -/
def has_pat : term → Bool
  | TPat _ => true
  | TPlus p q | TMinus p q | TMul p q | TEq p q | TLt _ p q | TLe _ p q =>
      has_pat p || has_pat q
  | TNeg p | TNot p | TRet p => has_pat p
  | TIte p q r => (has_pat p || has_pat q) || has_pat r
  | _ => false

def ohas_pat : Option term → Bool
  | none => false
  | some x' => has_pat x'

def is_tpat : term → Bool
  | TPat _ => true
  | _ => false

/-- The Go code walks the three child fields, so the mirror has to agree with
that view of a node. -/
theorem has_pat_node (x : term) :
    has_pat x = (((is_tpat x || ohas_pat (term_a x)) || ohas_pat (term_b x))
                 || ohas_pat (term_c x)) := by
  cases x <;> simp [has_pat, is_tpat, ohas_pat, term_a, term_b, term_c, Bool.or_assoc]

theorem is_tpat_code (x : term) : decide (term_code x = W64 2) = is_tpat x := by
  cases x <;> simp only [term_code, is_tpat] <;> (try split) <;> rfl

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_hasPat (l : Loc) (ox : Option term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_oterm l ox }}
      (App (Val (@! checker.hasPat)) (Val #l))
    {{ RET #(ohas_pat ox); True }} := by
  iloeb as IH generalizing %l %ox
  wp_start as #Hox
  ihave %Hnull := is_oterm_null _ _ $$ Hox
  wp_auto
  wp_if_destruct
  · obtain rfl : ox = none := Hnull.mp rfl
    rw [show (#false : val) = #(ohas_pat none) from rfl]
    iapply HΦ; itrivial
  · cases ox with
    | none => exact absurd (Hnull.mpr rfl) Hif
    | some x =>
    rw [is_oterm_some]
    icases is_term_node _ _ $$ Hox with ⟨%la, %lb, %lc, %Hw, #Hn, #Ha, #Hb, #Hc⟩
    iStructNamed Hn
    wp_auto
    rw [show ohas_pat (some x) = has_pat x from rfl, has_pat_node]
    wp_if_destruct
    · -- the kind code says `TPat`
      have Hp : is_tpat x = true := by rw [← is_tpat_code]; simp [Hif]
      simp only [Hp, Bool.true_or]
      iapply HΦ; itrivial
    · have Hp : is_tpat x = false := by rw [← is_tpat_code]; exact decide_eq_false Hif
      rw [Hp]
      -- the three children, each guarded by `if <recursive call> { return true }`
      wp_apply IH $$ %la %(term_a x) []
      · iframe #
      cases ohas_pat (term_a x)
      · wp_auto
        wp_apply IH $$ %lb %(term_b x) []
        · iframe #
        cases ohas_pat (term_b x)
        · wp_auto
          wp_apply IH $$ %lc %(term_c x) []
          · iframe #
          simp only [Bool.false_or]
          iapply HΦ; itrivial
        · wp_auto
          simp only [Bool.false_or, Bool.true_or]
          iapply HΦ; itrivial
      · wp_auto
        simp only [Bool.false_or, Bool.true_or]
        iapply HΦ; itrivial

end proof

end Checker
end Perennial
