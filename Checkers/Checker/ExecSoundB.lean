/-
Port of `new/checker/exec_sound_b.v`.

Helpers for the per-case proofs of `exec` (fn/execLet.v, fn/execSeq.v,
fn/execLoad.v, fn/execUnOp.v, fn/execBinOp.v), and the semantic
composition lemmas for the operator cases, `exec_sound_at_unop` and
`exec_sound_at_binop`, in the style of exec_spec.v.

Lean notes:
* The compound proofs use `exec_bind` (ExecSpec.lean) in place of Rocq's
  inlined bind steps; `fill_two` unfolds a two-item context.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.Fn.heapLookup

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic

/-! ## Load: the value found is scoped by the state -/
theorem heap_lookup_below (k : Nat) (H : List scell) (x y : term) :
    heap_below k H → heap_lookup H x = some y → vars_below k y := by
  induction H with
  | nil => intro _ h; cases h
  | cons c H ih =>
    intro Hb
    simp only [heap_lookup]
    split
    · intro h; cases h; exact (Hb c (List.mem_cons_self ..)).2
    · exact ih (fun c' Hc' => Hb c' (List.mem_cons_of_mem _ Hc'))

/-! ## Operator results are scoped by their operands -/
theorem apply_unop_below (k : Nat) (op : cop) (cty : ctype) (u r : term) :
    apply_unop op cty u = some r → vars_below k u → vars_below k r := by
  intro Hr Hu
  cases op <;> simp only [apply_unop] at Hr <;> (repeat' split at Hr) <;>
    (try cases Hr) <;> exact Hu

theorem apply_binop_below (k : Nat) (op : cop) (cty : ctype) (u w r : term) :
    apply_binop op cty u w = some r → vars_below k u → vars_below k w → vars_below k r := by
  intro Hr Hu Hw
  cases op <;> simp only [apply_binop] at Hr <;> (repeat' split at Hr) <;>
    (try cases Hr) <;> first | exact ⟨Hu, Hw⟩ | exact ⟨Hw, Hu⟩

/-- Lean addition: list facts the range loops of the exec case proofs use. -/
theorem drop_cons_of_getElem? {α : Type} (l : List α) (n : Nat) (a : α) :
    l[n]? = some a → l.drop n = a :: l.drop (n + 1) := by
  intro h
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hl, he]

theorem take_snoc_of_getElem? {α : Type} (l : List α) (n : Nat) (a : α) :
    l[n]? = some a → l.take (n + 1) = l.take n ++ [a] := by
  intro h
  rw [List.take_add_one, h]; rfl

theorem forall2_snoc {α β : Type} (R : α → β → Prop) (l1 : List α) (l2 : List β) (a : α) (b : β) :
    List.Forall₂ R l1 l2 → R a b → List.Forall₂ R (l1 ++ [a]) (l2 ++ [b]) := by
  intro H Hab
  induction H with
  | nil => exact .cons Hab .nil
  | cons h _ ih => exact .cons h ih

section exec_sound_b
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem fill_two (K1 K2 : EctxItem) (e : Expr) :
    fill [K1, K2] e = fillItem K2 (fillItem K1 e) :=
  rfl

/-! ## `exec_post` -/

theorem exec_post_fail (ce : cexpr) ρ sst (s : GoSlice) (lf : Loc) :
    lf ≠ null → ⊢ exec_post (GF := GF) ce ρ sst s lf := by
  intro Hne
  unfold exec_post
  split
  · contradiction
  · exact true_intro

theorem exec_post_ok (ce : cexpr) ρ sst (s : GoSlice) :
    exec_post (GF := GF) ce ρ sst s null ⊣⊢
      iprop(∃ ps, is_paths s ps ∗ ⌜paths_wf (svars sst).length ps⌝ ∗ ⌜exec_sound ce ρ sst ps⌝) := by
  unfold exec_post
  split
  · exact .rfl
  · contradiction

/-! ## Unary operators

The checker has checked, at the operand's own state, that the operand has
the sort of the operator's type; that makes the GooseLang step
(`wp_unop`) go through, and the result term is what `apply_unop` built. -/
theorem exec_sound_at_unop (op : cop) (cty : ctype) (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound_at (GF := GF) ce ρ sst ps →
    (∀ p, p ∈ ps → ∃ r,
       sort_of_vars (svars (pst p)) (pret p) = some (ctype_sort cty) ∧
       apply_unop op cty (pret p) = some r ∧ mkPath r (pst p) ∈ out) →
    exec_sound_at (GF := GF) (CEUnOp op cty ce) ρ sst out := by
  intro He Hcont Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.AppRCtx _] ce ρ sst ps V _ He Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_singleton, fillItem]
  obtain ⟨r, Hsort, Hr, Hout⟩ := Hcont p Hin
  have Hs := sort_of_vars_sound V' _ _ _ Hsat'.1 Hsort
  iintro Hheap'
  iapply wp_unop op cty (pret p) r V' _ Hr Hs
  unfold paths_post
  iexists mkPath r (pst p), V'
  iframe Hheap'
  ipureintro
  exact ⟨Hout, Hag, rfl, Hsat'⟩

/-! ## Binary operators

GooseLang evaluates a `Pair` left to right, as the checker does: `ce1`
first, then `ce2` from each of its paths, then the operator. The left
operand's term is scoped by the state `ce1` ended in, so it keeps its
value under the valuation `ce2` ended with; the sort checks are made at
the final state, whose valuation is the one the operator step sees. -/
theorem exec_sound_at_binop (op : cop) (cty : ctype) (ce1 ce2 : cexpr) ρ sst
    (ps out : List spath) :
    exec_sound_at (GF := GF) ce1 ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → ∃ qs, exec_sound_at (GF := GF) ce2 ρ (pst p) qs ∧
       ∀ q, q ∈ qs → ∃ r,
         sort_of_vars (svars (pst q)) (pret p) = some (ctype_sort cty) ∧
         sort_of_vars (svars (pst q)) (pret q) = some (ctype_sort cty) ∧
         apply_binop op cty (pret p) (pret q) = some r ∧ mkPath r (pst q) ∈ out) →
    exec_sound_at (GF := GF) (CEBinOp op cty ce1 ce2) ρ sst out := by
  intro He1 Hwfps Hcont Hwf Hρ V Hsat
  simp only [csubst]
  refine exec_bind [EctxItem.PairLCtx _, EctxItem.AppRCtx _] ce1 ρ sst ps V _ He1 Hwf Hρ Hsat ?_
  intro p V' Hin Hag Hsat'
  simp only [fill_two, fillItem]
  obtain ⟨qs, Hqs, Hcont2⟩ := Hcont p Hin
  have Hwfp := Hwfps.paths_wf_state p Hin
  have Hgrow := Hwfps.paths_wf_grow p Hin
  have Hbret := Hwfps.paths_wf_ret p Hin
  have Hbp : env_below (svars (pst p)).length ρ := env_below_mono _ _ _ Hgrow Hρ
  rw [env_interp_agree _ V V' ρ Hag Hρ]
  refine exec_bind [EctxItem.PairRCtx (teval V' (pret p)), EctxItem.AppRCtx _] ce2 ρ (pst p) qs
    V' _ Hqs Hwfp Hbp Hsat' ?_
  intro q V'' Hin2 Hag2 Hsat''
  simp only [fill_two, fillItem]
  obtain ⟨r, Hs1, Hs2, Hr, Hout⟩ := Hcont2 q Hin2
  have Ha := sort_of_vars_sound V'' _ _ _ Hsat''.1 Hs1
  have Hb := sort_of_vars_sound V'' _ _ _ Hsat''.1 Hs2
  rw [teval_agree _ V' V'' (pret p) Hag2 Hbret]
  iintro Hheap''
  wp_pure
  iapply wp_binop op cty (pret p) (pret q) r V'' _ Hr Ha Hb
  unfold paths_post
  iexists mkPath r (pst q), V''
  iframe Hheap''
  ipureintro
  exact ⟨Hout, agree_below_trans _ _ _ _ Hag (agree_below_weaken _ _ _ _ Hgrow Hag2), rfl,
    Hsat''⟩

end exec_sound_b

/-! ## The ghost-state-independent layer (see exec_spec.v) -/
section exec_uniform_b

theorem exec_sound_unop (op : cop) (cty : ctype) (ce : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce ρ sst ps →
    (∀ p, p ∈ ps → ∃ r,
       sort_of_vars (svars (pst p)) (pret p) = some (ctype_sort cty) ∧
       apply_unop op cty (pret p) = some r ∧ mkPath r (pst p) ∈ out) →
    exec_sound (CEUnOp op cty ce) ρ sst out :=
  fun He Hc ext ffi fi fs gc hlc GF hG sem =>
    exec_sound_at_unop (GF := GF) _ _ _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hc

theorem exec_sound_binop (op : cop) (cty : ctype) (ce1 ce2 : cexpr) ρ sst (ps out : List spath) :
    exec_sound ce1 ρ sst ps →
    paths_wf (svars sst).length ps →
    (∀ p, p ∈ ps → ∃ qs, exec_sound ce2 ρ (pst p) qs ∧
       ∀ q, q ∈ qs → ∃ r,
         sort_of_vars (svars (pst q)) (pret p) = some (ctype_sort cty) ∧
         sort_of_vars (svars (pst q)) (pret q) = some (ctype_sort cty) ∧
         apply_binop op cty (pret p) (pret q) = some r ∧ mkPath r (pst q) ∈ out) →
    exec_sound (CEBinOp op cty ce1 ce2) ρ sst out :=
  fun He Hwf Hc ext ffi fi fs gc hlc GF hG sem =>
    exec_sound_at_binop (GF := GF) _ _ _ _ _ _ _ _ (He ext ffi fi fs gc hlc GF hG sem) Hwf
      (fun p Hp => let ⟨qs, Hq, H2⟩ := Hc p Hp; ⟨qs, Hq ext ffi fi fs gc hlc GF hG sem, H2⟩)

end exec_uniform_b

end Checker
end Perennial
