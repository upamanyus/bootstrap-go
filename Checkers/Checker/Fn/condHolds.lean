/-
Port of `new/checker/fn/condHolds.v`.

`checker.condHolds` (checker/match.go): does the path condition
syntactically justify a term?

Lean notes:
* The mirror and its pure lemmas are outside the proof section (match_sound
  uses `cond_holds`).
* Iris's `a || b || c` notation forces parenthesised Boolean chains.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Fn.termEq

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- What the `range` loop decides: `t` is non-nil and is one of the recorded
facts. `termEq c t` is `decide (some c = ox)`, and every cell of `is_cond`
is a real term, so a nil `t` never matches. -/
def cond_mem (pc : List term) : Option term → Bool
  | none => false
  | some y => decide (y ∈ pc)

/-- ... and what it checks afterwards. -/
def cond_refl : term → Bool
  | TEq p q => decide (p = q)
  | TBool b => b
  | _ => false

def cond_holds (pc : List term) : Option term → Bool
  | none => false
  | some y => decide (y ∈ pc) || cond_refl y

theorem cond_mem_holds (pc : List term) (ox : Option term) :
    cond_mem pc ox = true → cond_holds pc ox = true := by
  cases ox <;> simp_all [cond_mem, cond_holds]

/-- The loop hits a matching fact ... -/
theorem cond_holds_hit (pc : List term) (n : Nat) (y : term) (ox : Option term) :
    pc[n]? = some y → ox = some y → cond_holds pc ox = true := by
  intro Hn Ho; subst Ho
  simp [cond_holds, List.mem_of_getElem? Hn]

/-- ... or passes it. -/
theorem cond_mem_step (pc : List term) (n : Nat) (y : term) (ox : Option term) :
    pc[n]? = some y → cond_mem (pc.take n) ox = false → ox ≠ some y →
    cond_mem (pc.take (n + 1)) ox = false := by
  intro Hn Hmiss Hne
  cases ox with
  | none => rfl
  | some z =>
    simp only [cond_mem, decide_eq_false_iff_not] at Hmiss ⊢
    rw [List.take_add_one, Hn]
    simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
    exact ⟨Hmiss, fun h => Hne (h ▸ rfl)⟩

/-- The kind tests, in the node view the Go code uses. -/
def is_teq : term → Bool
  | TEq _ _ => true
  | _ => false
def is_tbool : term → Bool
  | TBool _ => true
  | _ => false

theorem is_teq_code (x : term) : decide (term_code x = W64 12) = is_teq x := by
  cases x <;> simp only [term_code, is_teq] <;> (try split) <;> rfl

theorem is_tbool_code (x : term) : decide (term_code x = W64 5) = is_tbool x := by
  cases x <;> simp only [term_code, is_tbool] <;> (try split) <;> rfl

theorem cond_refl_teq (y : term) :
    is_teq y = true → cond_refl y = decide (term_a y = term_b y) := by
  cases y <;> simp [is_teq, cond_refl, term_a, term_b]

theorem cond_refl_tbool (y : term) :
    is_tbool y = true → cond_refl y = decide (term_num y = W64 1) := by
  cases y <;> simp only [is_tbool, cond_refl, term_num, bool_code] <;> intro h <;>
    first | exact absurd h (by decide) | (rename_i b; cases b <;> rfl)

theorem cond_refl_other (y : term) :
    is_teq y = false → is_tbool y = false → cond_refl y = false := by
  cases y <;> simp [is_teq, is_tbool, cond_refl]

theorem is_teq_tbool (y : term) : is_teq y = true → is_tbool y = false := by
  cases y <;> simp [is_teq, is_tbool]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_condHolds (s : GoSlice) (pc : List term) (lx : Loc) (ox : Option term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_cond s pc ∗ is_oterm lx ox }}
      (App (App (Val (@! checker.condHolds)) (Val #s)) (Val #lx))
    {{ RET #(cond_holds pc ox); is_cond s pc }} := by
  wp_start as ⟨Hcond, #Hox⟩
  unfold is_cond
  icases Hcond with ⟨%ls, Hs, #Hls⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hls
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave HI : (∃ (n : w64) (lcur : Loc),
      "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ lcur ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ ls.length⌝ ∗
      "%Hmiss" ∷ ⌜cond_mem (pc.take (sint.nat n)) ox = false⌝ : IProp GF) $$ [i c]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    cases ox <;> rfl
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hn.1, Hif⟩]
    list_elem ls (sint.nat n) as lcur'
    list_elem pc (sint.nat n) as tcur
    ihave #Hcur := BigSepL2.bigSepL2_lookup (Φ := fun _ l t => is_term (GF := GF) l t)
      Hlcur'_lookup Htcur_lookup $$ Hls
    wp_apply wp_load_slice_index s (sint.Z n) ls _ lcur' Hn.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Hlcur'_lookup
    wp_apply wp_termEq lcur' lx (some tcur) ox $$ []
    · rw [is_oterm_some]; iframe #
    wp_if_destruct
    · -- this fact is the one
      wp_for_post
      rw [cond_holds_hit pc (sint.nat n) tcur _ Htcur_lookup rfl]
      iapply HΦ
      iexists ls; iframe Hs Hls
    · -- keep scanning
      wp_for_post
      iframe
      iexists n + W64 1, lcur'
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
      exact cond_mem_step pc _ tcur ox Htcur_lookup Hmiss (fun h => Hif (by simp [h]))
  · -- the scan reached the end of the path condition
    have Htake : pc.take (sint.nat n) = pc := List.take_of_length_le (by word)
    rw [Htake] at Hmiss
    ihave %Hnull := is_oterm_null _ _ $$ Hox
    wp_if_destruct
    · -- `t` is nil
      obtain rfl : ox = none := Hnull.mp rfl
      rw [show (#false : val) = #(cond_holds pc none) from rfl]
      iapply HΦ
      iexists ls; iframe Hs Hls
    · cases ox with
      | none => exact absurd (Hnull.mpr rfl) Hif
      | some y =>
      rw [is_oterm_some]
      icases is_term_node _ _ $$ Hox with ⟨%la, %lb, %lc, %Hw, #Hn, #Ha, #Hb, #Hc⟩
      iStructNamed Hn
      have Hch : cond_holds pc (some y) = cond_refl y := by
        simp only [cond_mem] at Hmiss; simp [cond_holds, Hmiss]
      rw [Hch]
      wp_auto
      rw [is_teq_code]
      cases Hq : is_teq y
      · -- not a `TEq` node
        wp_auto
        rw [is_tbool_code]
        cases Hb' : is_tbool y
        · rw [cond_refl_other _ Hq Hb']
          wp_auto
          iapply HΦ
          iexists ls; iframe Hs Hls
        · -- `t.Kind == TBool`: is it the literal `true`?
          rw [cond_refl_tbool _ Hb']
          wp_auto
          wp_if_destruct
          · iapply HΦ
            iexists ls; iframe Hs Hls
          · iapply HΦ
            iexists ls; iframe Hs Hls
      · -- `t.Kind == TEq`: compare the two children
        rw [cond_refl_teq _ Hq]
        wp_auto
        wp_apply wp_termEq la lb (term_a y) (term_b y) $$ []
        · iframe #
        wp_if_destruct
        · iapply HΦ
          iexists ls; iframe Hs Hls
        · -- they differ, and a `TEq` node is not a `TBool` node
          rw [is_tbool_code, is_teq_tbool _ Hq]
          wp_auto
          iapply HΦ
          iexists ls; iframe Hs Hls

end proof

end Checker
end Perennial
