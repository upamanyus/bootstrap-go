/-
Port of `new/checker/term_lemmas.v`.

Semantics of the checker's symbolic terms.

Pure metatheory of `teval`, `has_sort` and the sort discipline
`sortOfEnv` of checker/sorts.go, plus the small term operations the
symbolic execution performs (`negate`). Nothing here mentions the Go
program; these are the specification functions the Go specs are stated
over.

Lean notes:
* The decidable-equality instances of the Rocq file are `deriving
  DecidableEq` clauses in Defs.lean.
* Everything here needs only `[FfiSyntax]` (for `val`); Lean only abstracts
  the section variables a declaration uses, so these lemmas do not pick up
  the ghost-state variables (Rocq's "`Default Proof Using "All"` poisons pure
  lemmas" problem does not arise).
* `pc1 ⊆ pc2` is `List.Subset`; `t ∈ pc` is `List.Mem`.
-/
import Checkers.Checker.Defs

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

section term_semantics
variable [ext : FfiSyntax]

/-! ## Injectivity of the value constructors -/

theorem ival_inj (w1 w2 : w64) : ival w1 = ival w2 → w1 = w2 := by
  simp [ival]
theorem bval_inj (b1 b2 : Bool) : bval b1 = bval b2 → b1 = b2 := by
  simp [bval]
theorem lval_inj (l1 l2 : Loc) : lval l1 = lval l2 → l1 = l2 := by
  simp [lval]

/-- The four value shapes are pairwise distinct, which is what makes
`has_sort` at one sort exclude the others. -/
theorem has_sort_unique (v : val) (s1 s2 : sort) :
    has_sort v s1 → has_sort v s2 → s1 = s2 := by
  intro H1 H2
  cases s1 <;> cases s2 <;> first | rfl | skip
  all_goals exfalso
  all_goals simp only [has_sort, ival, bval, lval, uval] at H1 H2
  all_goals first | (obtain ⟨_, rfl⟩ := H1; simp at H2) | (subst H1; simp at H2)

/-! ## The sort environment of checker/sorts.go -/

/-- Mirrors `sortEnv`: sorts for the logical variables, for the
postcondition's pattern variables (with `se_pat_ok` marking the ones a
binder actually declared), and for `ret`. -/
structure sort_env where
  mkSortEnv ::
  se_vars : List sort
  se_pats : List sort
  se_pat_ok : List Bool
  se_ret : sort
  se_ret_ok : Bool

export sort_env (mkSortEnv se_vars se_pats se_pat_ok se_ret se_ret_ok)

/-- `sortOfEnv` indexes `patOk` after bounds-checking against `pats`, so it is
only well defined when the two have the same length. Every `sortEnv` the
checker builds satisfies this. -/
def sort_env_wf (E : sort_env) : Prop :=
  (se_pats E).length = (se_pat_ok E).length

/-- Mirrors `sortOfEnv`. `TExec` and `TRet` have no sort. -/
def sort_of (E : sort_env) : term → Option sort
  | TVar n => (se_vars E)[n]?
  | TPat n =>
      match (se_pats E)[n]?, (se_pat_ok E)[n]? with
      | some s, some true => some s
      | _, _ => none
  | TResult => if se_ret_ok E then some (se_ret E) else none
  | TInt _ => some SInt
  | TBool _ => some SBool
  | TUnit => some SUnit
  | TNull => some SLoc
  | TPlus a b | TMinus a b | TMul a b =>
      match sort_of E a, sort_of E b with
      | some SInt, some SInt => some SInt
      | _, _ => none
  | TNeg a => match sort_of E a with | some SInt => some SInt | _ => none
  | TEq a b =>
      match sort_of E a, sort_of E b with
      | some sa, some sb => if sa = sb then some SBool else none
      | _, _ => none
  | TLt _ a b | TLe _ a b =>
      match sort_of E a, sort_of E b with
      | some SInt, some SInt => some SBool
      | _, _ => none
  | TNot a => match sort_of E a with | some SBool => some SBool | _ => none
  | TIte c a b =>
      match sort_of E c, sort_of E a, sort_of E b with
      | some SBool, some sa, some sb => if sa = sb then some sa else none
      | _, _, _ => none
  | TExec => none
  | TRet _ => none

/-- Mirrors `SortOf`: only the logical variables are in scope. -/
def vars_env (vars : List sort) : sort_env :=
  mkSortEnv vars [] [] SInt false
def sort_of_vars (vars : List sort) (t : term) : Option sort :=
  sort_of (vars_env vars) t

theorem vars_env_wf (vars : List sort) : sort_env_wf (vars_env vars) := rfl

/-- A valuation respects a sort environment. -/
structure env_sat (V : valuation) (E : sort_env) : Prop where
  mkEnvSat ::
  env_sat_vars : ∀ n s, (se_vars E)[n]? = some s → has_sort (vvar V n) s
  env_sat_pats : ∀ n s, (se_pats E)[n]? = some s → (se_pat_ok E)[n]? = some true →
                        has_sort (vpat V n) s
  env_sat_ret : se_ret_ok E = true → has_sort (vret V) (se_ret E)

/-- The key fact: a term the checker assigns a sort to evaluates to a value of
that sort, so the `if:` condition really is a boolean and the operands of
a `GoOp` really are machine integers. -/
theorem sort_of_sound (V : valuation) (E : sort_env) (t : term) (s : sort) :
    env_sat V E → sort_of E t = some s → has_sort (teval V t) s := by
  intro HE
  induction t generalizing s with
  | TVar n => intro Hs; exact HE.env_sat_vars n s Hs
  | TPat n =>
    intro Hs
    simp only [sort_of] at Hs
    split at Hs
    · rename_i sp Hp Hok; cases Hs; exact HE.env_sat_pats n _ Hp Hok
    · cases Hs
  | TResult =>
    intro Hs
    simp only [sort_of] at Hs
    split at Hs
    · rename_i Hr; cases Hs; exact HE.env_sat_ret Hr
    · cases Hs
  | TInt w => intro Hs; cases Hs; exact ⟨w, rfl⟩
  | TBool b => intro Hs; cases Hs; exact ⟨b, rfl⟩
  | TUnit => intro Hs; cases Hs; rfl
  | TNull => intro Hs; cases Hs; exact ⟨null, rfl⟩
  | TPlus a b iha ihb | TMinus a b iha ihb | TMul a b iha ihb =>
    intro Hs
    simp only [sort_of] at Hs
    split at Hs
    · rename_i H1 H2
      cases Hs
      obtain ⟨x, hx⟩ := iha SInt H1
      obtain ⟨y, hy⟩ := ihb SInt H2
      simp only [teval, hx, hy, ival]
      exact ⟨_, rfl⟩
    · cases Hs
  | TNeg a iha =>
    intro Hs
    simp only [sort_of] at Hs
    split at Hs
    · rename_i H1
      cases Hs
      obtain ⟨x, hx⟩ := iha SInt H1
      simp only [teval, hx, ival]
      exact ⟨_, rfl⟩
    · cases Hs
  | TEq a b iha ihb =>
    intro Hs
    simp only [sort_of] at Hs
    split at Hs
    · split at Hs
      · cases Hs; exact ⟨_, rfl⟩
      · cases Hs
    · cases Hs
  | TLt sg a b iha ihb | TLe sg a b iha ihb =>
    intro Hs
    simp only [sort_of] at Hs
    split at Hs
    · rename_i H1 H2
      cases Hs
      obtain ⟨x, hx⟩ := iha SInt H1
      obtain ⟨y, hy⟩ := ihb SInt H2
      simp only [teval, hx, hy, ival]
      exact ⟨_, rfl⟩
    · cases Hs
  | TNot a iha =>
    intro Hs
    simp only [sort_of] at Hs
    split at Hs
    · rename_i H1
      cases Hs
      obtain ⟨x, hx⟩ := iha SBool H1
      simp only [teval, hx, bval]
      exact ⟨_, rfl⟩
    · cases Hs
  | TIte c a b ihc iha ihb =>
    intro Hs
    simp only [sort_of] at Hs
    split at Hs
    · rename_i sa sb H1 H2 H3
      split at Hs
      · rename_i Heq
        cases Hs
        subst Heq
        obtain ⟨x, hx⟩ := ihc SBool H1
        simp only [teval, hx, bval]
        cases x
        · exact ihb _ H3
        · exact iha _ H2
      · cases Hs
    · cases Hs
  | TExec => intro Hs; cases Hs
  | TRet a _ => intro Hs; cases Hs

theorem sort_of_vars_sound (V : valuation) (vars : List sort) (t : term) (s : sort) :
    (∀ n s', vars[n]? = some s' → has_sort (vvar V n) s') →
    sort_of_vars vars t = some s →
    has_sort (teval V t) s := by
  intro Hv Hs
  refine sort_of_sound V _ t s ⟨Hv, ?_, ?_⟩ Hs
  · intro n s' H; simp [vars_env] at H
  · intro H; cases H

/-! ## Variable bounds and agreement

Symbolic execution only ever extends the valuation at indices at or above
the current number of logical variables, so terms built earlier keep their
meaning. -/

def vars_below (k : Nat) : term → Prop
  | TVar n => n < k
  -- Pattern variables and `ret` belong to postconditions; a term of the
  -- program's own execution never mentions them. The postcondition matcher
  -- relies on this: it re-interprets a path's return term under a valuation
  -- whose pattern variables and `ret` have been changed.
  | TPat _ | TResult => False
  | TInt _ | TBool _ | TUnit | TNull | TExec => True
  | TPlus a b | TMinus a b | TMul a b | TEq a b | TLt _ a b | TLe _ a b =>
      vars_below k a ∧ vars_below k b
  | TNeg a | TNot a | TRet a => vars_below k a
  | TIte c a b => vars_below k c ∧ vars_below k a ∧ vars_below k b

theorem vars_below_mono (k k' : Nat) (t : term) : k ≤ k' → vars_below k t → vars_below k' t := by
  intro Hle
  induction t with
  | TVar n => simp only [vars_below]; omega
  | TPlus a b iha ihb | TMinus a b iha ihb | TMul a b iha ihb | TEq a b iha ihb
  | TLt _ a b iha ihb | TLe _ a b iha ihb =>
    intro H; exact ⟨iha H.1, ihb H.2⟩
  | TNeg a iha | TNot a iha | TRet a iha => exact iha
  | TIte c a b ihc iha ihb => intro H; exact ⟨ihc H.1, iha H.2.1, ihb H.2.2⟩
  | _ => exact id

/-- Two valuations agreeing on the variables a term mentions give it the same
value. -/
def agree_below (k : Nat) (V V' : valuation) : Prop :=
  (∀ n, n < k → vvar V n = vvar V' n) ∧ vpat V = vpat V' ∧ vret V = vret V'

theorem agree_below_refl (k : Nat) (V : valuation) : agree_below k V V :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

theorem agree_below_trans (k : Nat) (V1 V2 V3 : valuation) :
    agree_below k V1 V2 → agree_below k V2 V3 → agree_below k V1 V3 := by
  intro ⟨H1, Hp1, Hr1⟩ ⟨H2, Hp2, Hr2⟩
  exact ⟨fun n Hn => (H1 n Hn).trans (H2 n Hn), Hp1.trans Hp2, Hr1.trans Hr2⟩

theorem agree_below_weaken (k k' : Nat) (V V' : valuation) :
    k' ≤ k → agree_below k V V' → agree_below k' V V' := by
  intro Hle ⟨H, Hp, Hr⟩
  exact ⟨fun n Hn => H n (by omega), Hp, Hr⟩

theorem teval_agree (k : Nat) (V V' : valuation) (t : term) :
    agree_below k V V' → vars_below k t → teval V t = teval V' t := by
  intro ⟨Hv, Hp, Hr⟩
  induction t with
  | TVar n => intro Hb; exact Hv n Hb
  | TPat n => intro Hb; exact Hb.elim
  | TResult => intro Hb; exact Hb.elim
  | TPlus a b iha ihb | TMinus a b iha ihb | TMul a b iha ihb | TEq a b iha ihb
  | TLt _ a b iha ihb | TLe _ a b iha ihb =>
    intro Hb; simp only [teval, iha Hb.1, ihb Hb.2]
  | TNeg a iha | TNot a iha | TRet a iha =>
    intro Hb; simp only [teval, iha Hb]
  | TIte c a b ihc iha ihb =>
    intro Hb; simp only [teval, ihc Hb.1, iha Hb.2.1, ihb Hb.2.2]
  | _ => intro _; rfl

/-- Sorting is insensitive to variables beyond the table, so extending the
table preserves the sort of an already well-scoped term. -/
theorem sort_of_vars_mono (vars vars' : List sort) (t : term) (s : sort) :
    (∀ (n : Nat) (s' : sort), vars[n]? = some s' → vars'[n]? = some s') →
    sort_of_vars vars t = some s → sort_of_vars vars' t = some s := by
  intro Hsub
  simp only [sort_of_vars]
  induction t generalizing s with
  | TVar n => exact Hsub n s
  | TPat n => intro H; simp [sort_of, vars_env] at H
  | TResult => intro H; simp [sort_of, vars_env] at H
  | TPlus a b iha ihb | TMinus a b iha ihb | TMul a b iha ihb
  | TLt _ a b iha ihb | TLe _ a b iha ihb =>
    intro H
    simp only [sort_of] at H ⊢
    split at H
    · rename_i H1 H2; rw [iha _ H1, ihb _ H2]; exact H
    · cases H
  | TNeg a iha =>
    intro H
    simp only [sort_of] at H ⊢
    split at H
    · rename_i H1; rw [iha _ H1]; exact H
    · cases H
  | TNot a iha =>
    intro H
    simp only [sort_of] at H ⊢
    split at H
    · rename_i H1; rw [iha _ H1]; exact H
    · cases H
  | TEq a b iha ihb =>
    intro H
    simp only [sort_of] at H ⊢
    split at H
    · rename_i H1 H2; rw [iha _ H1, ihb _ H2]; exact H
    · cases H
  | TIte c a b ihc iha ihb =>
    intro H
    simp only [sort_of] at H ⊢
    split at H
    · rename_i H1 H2 H3; rw [ihc _ H1, iha _ H2, ihb _ H3]; exact H
    · cases H
  | _ => exact id

theorem sort_of_vars_app (vars vars' : List sort) (t : term) (s : sort) :
    sort_of_vars vars t = some s → sort_of_vars (vars ++ vars') t = some s := by
  apply sort_of_vars_mono
  intro n s' Hn
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp Hn).1]
  exact Hn

/-! ## `negate` -/

/-- Mirrors `negate` in checker/exec.go: the double negation is cancelled so
that the `else` branch after `if !b` records just `b`. -/
def negate : term → term
  | TNot a => a
  | t => TNot t

theorem teval_negate (V : valuation) (t : term) (b : Bool) :
    teval V t = bval b → teval V (negate t) = bval (!b) := by
  intro Ht
  cases t with
  | TNot a =>
    -- `negate (TNot a) = a`: the checker cancels the double negation
    simp only [negate]
    simp only [teval] at Ht
    split at Ht
    · rename_i b' Ha
      simp only [bval, val.LitV.injEq, BaseLit.LitBool.injEq] at Ht
      subst Ht
      simp [Ha, bval]
    · simp [uval, bval] at Ht
  | _ =>
    simp only [negate, teval] at Ht ⊢
    rw [Ht]; rfl

theorem sort_of_negate (E : sort_env) (t : term) :
    sort_of E t = some SBool → sort_of E (negate t) = some SBool := by
  intro Ht
  cases t with
  | TNot a =>
    simp only [negate]
    simp only [sort_of] at Ht
    split at Ht
    · assumption
    · cases Ht
  | _ =>
    simp only [negate, sort_of] at Ht ⊢
    all_goals first | (rw [Ht]) | simp at Ht

theorem vars_below_negate (k : Nat) (t : term) : vars_below k t → vars_below k (negate t) := by
  cases t <;> simp [negate, vars_below]

/-! ## Path conditions -/

def pc_sat (V : valuation) (pc : List term) : Prop :=
  ∀ t, t ∈ pc → teval V t = bval true

theorem pc_sat_nil (V : valuation) : pc_sat V [] := by
  intro t H; cases H

theorem pc_sat_app (V : valuation) (pc1 pc2 : List term) :
    pc_sat V pc1 → pc_sat V pc2 → pc_sat V (pc1 ++ pc2) := by
  intro H1 H2 t Ht
  rcases List.mem_append.mp Ht with H | H
  · exact H1 t H
  · exact H2 t H

theorem pc_sat_snoc (V : valuation) (pc : List term) (t : term) :
    pc_sat V pc → teval V t = bval true → pc_sat V (pc ++ [t]) := by
  intro H Ht
  apply pc_sat_app V _ _ H
  intro t' Ht'
  rw [List.mem_singleton.mp Ht']
  exact Ht

theorem pc_sat_weaken (V : valuation) (pc1 pc2 : List term) :
    pc1 ⊆ pc2 → pc_sat V pc2 → pc_sat V pc1 := by
  intro Hsub H t Ht
  exact H t (Hsub Ht)

def pc_below (k : Nat) (pc : List term) : Prop :=
  ∀ t, t ∈ pc → vars_below k t

theorem pc_sat_agree (k : Nat) (V V' : valuation) (pc : List term) :
    agree_below k V V' → pc_below k pc → pc_sat V pc → pc_sat V' pc := by
  intro Hag Hb H t Ht
  rw [← teval_agree k V V' t Hag (Hb t Ht)]
  exact H t Ht

end term_semantics

end Checker
end Perennial
