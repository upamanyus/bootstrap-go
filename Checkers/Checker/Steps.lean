/-
Port of `new/checker/steps.v`.

Per-instruction WP lemmas at the types of the fragment.

The exec proof needs, for every supported `ctype`, the step the GooseLang
instruction takes, phrased in the untyped vocabulary the symbolic heap and
`teval` use (`ival`/`bval`/`lval`/`uval` and `heapPointsto`) rather than
in the `IntoValTyped` vocabulary of `Perennial/Golang/Theory`. That is what this
file provides.

Lean notes:
* Rocq's lemmas `Φ v -∗ WP e {{ Φ }}` are closed entailments
  `Φ v ⊢ WP e {{ Φ }}` here; use them with `iapply (wp_do v Φ)` (or
  `iapply wp_do`) exactly as in Rocq.
* The instructions are written out as the constructors `expr_of` produces:
  `App (Val (GoInstruction (GoLoad t))) (Val #l)` for Rocq `![t] #l`,
  `App (Val (GoInstruction (GoOp o t))) (Val (PairV a b))` for
  `GoOp o t (a, b)%V`, `App (Val doExecute) (Val v)` for `do: v`, and so on.
* `#x` is `intoVal x`, opaque as in Rocq; `go.intoVal_unfold` (from
  `go.Semantics`) gives `ival_eq` & co. The `op_operands`/`op_finish` Ltacs
  are inlined into the proofs of `wp_binop`/`wp_unop` (they are not used
  elsewhere).
* `Convert t t` is the identity on every value in the Lean semantics too, so
  `wp_convert` keeps Rocq's statement.
* Rocq's `wp_beta_func` is about `#(func.mk BAnon x B)`, the value Rocq's goose
  makes a `Rec` step to. In Lean `Rec f x e` steps to `RecV f x e` (no
  `func.mk`), so `wp_lams` uses `wp_beta_recv` only; `wp_beta_func` is kept for
  the downstream proofs (a closure stored with `wp_auto` is a `#(func.mk ..)`).
* Iris-lean has `wp_bind_inv`, but `wp_lams` keeps Rocq's statement (the rest
  of the application in the postcondition): `fill (app_ctx vs) h` is
  `apply_vals_e h vs` by definition (`apply_vals_e_fill` is `rfl`).
* The `wp_ctype_*` lemmas take the instruction's argument as written by
  `expr_of` after evaluation (`Val #l`, `Val (PairV #l w)`).
-/
import Checkers.Checker.Subst
import Checkers.Checker.TermLemmas

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic

/-! ## The sort of a supported type (pure)

Every `ctype` is supported, so unlike `TypeSort` in checker/sorts.go this
is total. -/
-- `ctype_sort`, `ctype_signed`, `ctype_zero`, `apply_binop`, `apply_unop`: in LCheck/Fns.lean.


/-! ## Operators (pure)

`apply_binop`/`apply_unop` mirror the term-building half of `applyBinOp`
and `applyUnOp` in checker/exec.go; the sort checks those functions also
perform become hypotheses of the WP lemmas below. -/


/-! ## `intoVal` at the four value shapes

Stated with only the instances `#` and `go.intoVal_unfold` need, so that
`rw [← ival_eq]` does not leave the ghost state to be inferred. -/
section into_val
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [lc : GoLocalContext]
variable [sem : go.Semantics]

theorem ival_eq (w : w64) : (#w : val) = ival w := by rw [go.intoVal_unfold w64]; rfl
theorem bval_eq (b : Bool) : (#b : val) = bval b := by rw [go.intoVal_unfold Bool]; rfl
theorem lval_eq (l : Loc) : (#l : val) = lval l := by rw [go.intoVal_unfold Loc]; rfl
theorem uval_eq : (#() : val) = uval := by rw [go.intoVal_unfold Unit]; rfl
theorem sval_eq (s : GoString) : (#s : val) = LitV (LitString s) := by
  rw [go.intoVal_unfold GoString]

/-- The operands of a `GoOp` are `#x` for a Lean `x`; these turn a
`has_sort` fact into that form. -/
theorem has_sort_int (v : val) : has_sort v SInt → ∃ w : w64, v = #w := by
  intro ⟨w, h⟩; exact ⟨w, by rw [h, ival_eq]⟩
theorem has_sort_bool (v : val) : has_sort v SBool → ∃ b : Bool, v = #b := by
  intro ⟨b, h⟩; exact ⟨b, by rw [h, bval_eq]⟩
theorem has_sort_loc (v : val) : has_sort v SLoc → ∃ l : Loc, v = #l := by
  intro ⟨l, h⟩; exact ⟨l, by rw [h, lval_eq]⟩

/-- `TEq` compares GooseLang values; `GoEquals` compares the Lean values
they come from. `intoVal` is injective at each of these types. -/
theorem decide_iv_w64 (x y : w64) : decide ((#x : val) = #y) = decide (x = y) := by
  rw [ival_eq, ival_eq]; simp [ival]
theorem decide_iv_bool (x y : Bool) : decide ((#x : val) = #y) = decide (x = y) := by
  rw [bval_eq, bval_eq]; simp [bval]
theorem decide_iv_loc (x y : Loc) : decide ((#x : val) = #y) = decide (x = y) := by
  rw [lval_eq, lval_eq]; simp [lval]

theorem exec_v_eq : exec_v = executeVal := by
  rw [executeVal_unseal, executeValDef, exec_v, sval_eq, uval_eq]

theorem ret_v_eq (v : val) : ret_v v = returnVal v := by
  rw [returnVal_unseal, returnValDef, ret_v, sval_eq]

end into_val

section steps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## Memory

Stated over the untyped `heapPointsto` so that the same lemma covers
every supported type; `assn_interp` in the statement of soundness uses
`heapPointsto` for the same reason. -/

/-- The typed points-to of each of the three value types the fragment uses is
the untyped one (the `TypedPointsto` instances of
Perennial/Golang/Theory/PostLifting.lean are all `heapPointsto l dq #v`); the
extra `l ≠ null` it carries is already implied by `heapPointsto`. -/
theorem pointsto_w64 (l : Loc) (dq : DFrac) (w : w64) :
    (l ↦{dq} w : IProp GF) ⊣⊢ heapPointsto l dq #w := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  rw [typedPointstoDef_heap]
  constructor
  · iintro ⟨H, _⟩; iexact H
  · iintro H
    ihave %Hn := heapPointsto_non_null _ _ _ $$ H
    iframe H; ipureintro; exact Hn

theorem pointsto_bool (l : Loc) (dq : DFrac) (b : Bool) :
    (l ↦{dq} b : IProp GF) ⊣⊢ heapPointsto l dq #b := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  rw [typedPointstoDef_heap]
  constructor
  · iintro ⟨H, _⟩; iexact H
  · iintro H
    ihave %Hn := heapPointsto_non_null _ _ _ $$ H
    iframe H; ipureintro; exact Hn

theorem pointsto_loc (l : Loc) (dq : DFrac) (lo : Loc) :
    (l ↦{dq} lo : IProp GF) ⊣⊢ heapPointsto l dq #lo := by
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  rw [typedPointstoDef_heap]
  constructor
  · iintro ⟨H, _⟩; iexact H
  · iintro H
    ihave %Hn := heapPointsto_non_null _ _ _ $$ H
    iframe H; ipureintro; exact Hn

theorem wp_ctype_load (t : ctype) (l : Loc) (dq : DFrac) (v : val) :
    has_sort v (ctype_sort t) →
    {{ heapPointsto (GF := GF) l dq v }}
      (App (Val (GoInstruction (GoLoad (type_of t)))) (Val #l))
    {{ RET v; heapPointsto l dq v }} := by
  intro Hs
  iintro %Φ Hl HΦ
  cases t <;> simp only [ctype_sort, has_sort] at Hs <;> obtain ⟨w, rfl⟩ := Hs <;>
    simp only [type_of]
  · rw [← ival_eq, ← (pointsto_w64 l dq w).to_eq]
    wp_apply IntoValTyped.wp_load (t := go.int) l dq w $$ Hl as Hl
    iapply HΦ; rw [(pointsto_w64 l dq w).to_eq]; iexact Hl
  · rw [← ival_eq, ← (pointsto_w64 l dq w).to_eq]
    wp_apply IntoValTyped.wp_load (t := go.int64) l dq w $$ Hl as Hl
    iapply HΦ; rw [(pointsto_w64 l dq w).to_eq]; iexact Hl
  · rw [← ival_eq, ← (pointsto_w64 l dq w).to_eq]
    wp_apply IntoValTyped.wp_load (t := go.uint64) l dq w $$ Hl as Hl
    iapply HΦ; rw [(pointsto_w64 l dq w).to_eq]; iexact Hl
  · rw [← bval_eq, ← (pointsto_bool l dq w).to_eq]
    wp_apply IntoValTyped.wp_load (t := go.bool) l dq w $$ Hl as Hl
    iapply HΦ; rw [(pointsto_bool l dq w).to_eq]; iexact Hl
  · rw [← lval_eq, ← (pointsto_loc l dq w).to_eq]
    wp_apply IntoValTyped.wp_load (t := go.GoType.PointerType (type_of _)) l dq w $$ Hl as Hl
    iapply HΦ; rw [(pointsto_loc l dq w).to_eq]; iexact Hl

theorem wp_ctype_store (t : ctype) (l : Loc) (v w : val) :
    has_sort v (ctype_sort t) → has_sort w (ctype_sort t) →
    {{ heapPointsto (GF := GF) l (DFrac.own 1) v }}
      (App (Val (GoInstruction (GoStore (type_of t)))) (Val (PairV #l w)))
    {{ RET #(); heapPointsto l (DFrac.own 1) w }} := by
  intro Hv Hw
  iintro %Φ Hl HΦ
  cases t <;> simp only [ctype_sort, has_sort] at Hv Hw <;>
    obtain ⟨x, rfl⟩ := Hv <;> obtain ⟨y, rfl⟩ := Hw <;> simp only [type_of]
  · rw [← ival_eq, ← ival_eq, ← (pointsto_w64 l _ x).to_eq]
    wp_apply IntoValTyped.wp_store (t := go.int) l x y $$ Hl as Hl
    iapply HΦ; rw [(pointsto_w64 l _ y).to_eq]; iexact Hl
  · rw [← ival_eq, ← ival_eq, ← (pointsto_w64 l _ x).to_eq]
    wp_apply IntoValTyped.wp_store (t := go.int64) l x y $$ Hl as Hl
    iapply HΦ; rw [(pointsto_w64 l _ y).to_eq]; iexact Hl
  · rw [← ival_eq, ← ival_eq, ← (pointsto_w64 l _ x).to_eq]
    wp_apply IntoValTyped.wp_store (t := go.uint64) l x y $$ Hl as Hl
    iapply HΦ; rw [(pointsto_w64 l _ y).to_eq]; iexact Hl
  · rw [← bval_eq, ← bval_eq, ← (pointsto_bool l _ x).to_eq]
    wp_apply IntoValTyped.wp_store (t := go.bool) l x y $$ Hl as Hl
    iapply HΦ; rw [(pointsto_bool l _ y).to_eq]; iexact Hl
  · rw [← lval_eq, ← lval_eq, ← (pointsto_loc l _ x).to_eq]
    wp_apply IntoValTyped.wp_store (t := go.GoType.PointerType (type_of _)) l x y $$ Hl as Hl
    iapply HΦ; rw [(pointsto_loc l _ y).to_eq]; iexact Hl

theorem wp_ctype_alloc (t : ctype) (v : val) :
    has_sort v (ctype_sort t) →
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (GoAlloc (type_of t)))) (Val v))
    {{ (l : Loc), RET #l; heapPointsto l (DFrac.own 1) v }} := by
  intro Hv
  iintro %Φ _ HΦ
  cases t <;> simp only [ctype_sort, has_sort] at Hv <;> obtain ⟨x, rfl⟩ := Hv <;>
    simp only [type_of]
  · rw [← ival_eq]
    wp_apply wp_alloc (t := go.int) x as %l Hl
    iapply HΦ; rw [← (pointsto_w64 l _ x).to_eq]; iexact Hl
  · rw [← ival_eq]
    wp_apply wp_alloc (t := go.int64) x as %l Hl
    iapply HΦ; rw [← (pointsto_w64 l _ x).to_eq]; iexact Hl
  · rw [← ival_eq]
    wp_apply wp_alloc (t := go.uint64) x as %l Hl
    iapply HΦ; rw [← (pointsto_w64 l _ x).to_eq]; iexact Hl
  · rw [← bval_eq]
    wp_apply wp_alloc (t := go.bool) x as %l Hl
    iapply HΦ; rw [← (pointsto_bool l _ x).to_eq]; iexact Hl
  · rw [← lval_eq]
    wp_apply wp_alloc (t := go.GoType.PointerType (type_of _)) x as %l Hl
    iapply HΦ; rw [← (pointsto_loc l _ x).to_eq]; iexact Hl

/-- `GoZeroVal` produces exactly the term `typeZero` builds. -/
theorem ctype_zero_sort (V : valuation) (t : ctype) :
    has_sort (teval V (ctype_zero t)) (ctype_sort t) := by
  cases t <;> simp only [ctype_zero, ctype_sort, teval, has_sort] <;> exact ⟨_, rfl⟩

theorem wp_ctype_zero (t : ctype) (V : valuation) (Φ : val → IProp GF) :
    Φ (teval V (ctype_zero t)) ⊢
      WP (App (Val (GoInstruction (GoZeroVal (type_of t)))) (Val #())) {{ Φ }} := by
  iintro HΦ
  cases t <;> simp only [ctype_zero, teval, type_of]
  · wp_pures; rw [ival_eq, show zero_val w64 = W64 0 from rfl]; iexact HΦ
  · wp_pures; rw [ival_eq, show zero_val w64 = W64 0 from rfl]; iexact HΦ
  · wp_pures; rw [ival_eq, show zero_val w64 = W64 0 from rfl]; iexact HΦ
  · wp_pures; rw [bval_eq, show zero_val Bool = false from rfl]; iexact HΦ
  · wp_pures; rw [lval_eq, show zero_val Loc = null from rfl]; iexact HΦ

/-! ## Operators -/

theorem wp_binop (op : cop) (t : ctype) (a b r : term) (V : valuation) (Φ : val → IProp GF) :
    apply_binop op t a b = some r →
    has_sort (teval V a) (ctype_sort t) →
    has_sort (teval V b) (ctype_sort t) →
    Φ (teval V r) ⊢
      WP (App (Val (GoInstruction (GoOp (binop_of op) (type_of t))))
            (Val (PairV (teval V a) (teval V b)))) {{ Φ }} := by
  intro Hr Ha Hb
  iintro HΦ
  cases op <;> cases t <;> simp [apply_binop, ctype_sort, ctype_signed] at Hr <;> subst Hr <;>
    simp only [ctype_sort, has_sort] at Ha Hb <;>
    obtain ⟨x, hx⟩ := Ha <;> obtain ⟨y, hy⟩ := Hb <;>
    simp only [teval, hx, hy, binop_of, type_of] <;>
    simp only [← ival_eq, ← bval_eq, ← lval_eq] <;>
    wp_pures <;>
    simp only [cmp_lt, cmp_le, ival_eq, bval_eq, lval_eq] <;>
    simp only [ival, bval, lval, val.LitV.injEq, BaseLit.LitInt.injEq, BaseLit.LitBool.injEq,
      BaseLit.LitLoc.injEq, Bool.false_eq_true, ↓reduceIte] <;>
    iexact HΦ

theorem wp_unop (op : cop) (t : ctype) (a r : term) (V : valuation) (Φ : val → IProp GF) :
    apply_unop op t a = some r →
    has_sort (teval V a) (ctype_sort t) →
    Φ (teval V r) ⊢
      WP (App (Val (GoInstruction (GoUnOp (unop_of op) (type_of t))))
            (Val (teval V a))) {{ Φ }} := by
  intro Hr Ha
  iintro HΦ
  cases op <;> cases t <;> simp [apply_unop, ctype_sort, ctype_signed] at Hr <;> subst Hr <;>
    simp only [ctype_sort, has_sort] at Ha <;>
    obtain ⟨x, hx⟩ := Ha <;>
    simp only [teval, hx, unop_of, type_of] <;>
    simp only [← ival_eq, ← bval_eq] <;>
    wp_pures <;>
    simp only [ival_eq, bval_eq] <;>
    simp only [ival, bval] <;>
    iexact HΦ

/-- An identity conversion is the identity. -/
theorem wp_convert (t : ctype) (v : val) (Φ : val → IProp GF) :
    Φ v ⊢ WP (App (Val (GoInstruction (Convert (type_of t) (type_of t)))) (Val v)) {{ Φ }} := by
  iintro HΦ
  wp_pures
  iexact HΦ

/-! ## The exception monad

`teval` of `TExec`/`TRet` is exactly `executeVal`/`returnVal`, so the
`PureWp` instances of Perennial/Golang/Theory/Exception.lean apply directly. -/

theorem wp_do (v : val) (Φ : val → IProp GF) :
    Φ exec_v ⊢ WP (App (Val doExecute) (Val v)) {{ Φ }} := by
  iintro HΦ; wp_pures; rw [exec_v_eq]; iexact HΦ

theorem wp_return (v : val) (Φ : val → IProp GF) :
    Φ (ret_v v) ⊢ WP (App (Val doReturn) (Val v)) {{ Φ }} := by
  iintro HΦ; wp_pures; rw [ret_v_eq]; iexact HΦ

/-- `;;;` runs its second argument only when the first executed normally. -/
theorem wp_exc_seq_exec (e2 : Expr) (Φ : val → IProp GF) :
    WP e2 {{ Φ }} ⊢ WP (App (App (Val exceptionSeq) (Rec BAnon BAnon e2)) (Val exec_v)) {{ Φ }} := by
  iintro H; rw [exec_v_eq]; wp_pures; iexact H

theorem wp_exc_seq_ret (v : val) (e2 : Expr) (Φ : val → IProp GF) :
    Φ (ret_v v) ⊢
      WP (App (App (Val exceptionSeq) (Rec BAnon BAnon e2)) (Val (ret_v v))) {{ Φ }} := by
  iintro H; rw [ret_v_eq]; wp_pures; iexact H

theorem wp_exc_do_exec (Φ : val → IProp GF) :
    Φ uval ⊢ WP (App (Val exceptionDo) (Val exec_v)) {{ Φ }} := by
  iintro H; rw [exec_v_eq]; wp_pures; rw [uval_eq]; iexact H

theorem wp_exc_do_ret (v : val) (Φ : val → IProp GF) :
    Φ v ⊢ WP (App (Val exceptionDo) (Val (ret_v v))) {{ Φ }} := by
  iintro H; rw [ret_v_eq]; wp_pures; iexact H

/-! ## Applying a curried function to its arguments

`apply_vals (func_val f) (arg_vals f θ)` beta-reduces to the body with the
parameters bound, which is exactly `csubst` under the environment
`binds`. Later parameters shadow earlier ones, matching `envBind` in
`Analyze`. -/

def apply_vals_e (h : Expr) (vs : List val) : Expr :=
  vs.foldl (fun e v => App e (Val v)) h

theorem apply_vals_e_cons (h : Expr) (v : val) (vs : List val) :
    apply_vals_e h (v :: vs) = apply_vals_e (App h (Val v)) vs := rfl

theorem apply_vals_unfold (f : val) (vs : List val) :
    apply_vals f vs = apply_vals_e (Val f) vs := rfl

/-- The argument list is an evaluation context. -/
def app_ctx (vs : List val) : List EctxItem := vs.map EctxItem.AppLCtx

theorem apply_vals_e_fill (h : Expr) (vs : List val) :
    apply_vals_e h vs = fill (app_ctx vs) h := by
  induction vs generalizing h with
  | nil => rfl
  | cons v vs ih => exact ih (App h (Val v))

/-- These three are proved once with `B` abstract, so that applying one takes
exactly the steps of a beta reduction and does not reduce the body. -/
theorem wp_beta_recv (x : String) (B : Expr) (v : val) (Ψ : val → IProp GF) :
    WP (subst x v B) {{ Ψ }} ⊢ WP (App (Val (RecV BAnon (BNamed x) B)) (Val v)) {{ Ψ }} := by
  iintro H; wp_pure; iexact H

theorem wp_beta_func (x : String) (B : Expr) (v : val) (Ψ : val → IProp GF) :
    WP (subst x v B) {{ Ψ }} ⊢
      WP (App (Val #(func.mk BAnon (BNamed x) B)) (Val v)) {{ Ψ }} := by
  rw [go.intoVal_unfold GoFunc]
  exact wp_beta_recv x B v Ψ

theorem wp_beta_anon (B : Expr) (v : val) (Ψ : val → IProp GF) :
    WP B {{ Ψ }} ⊢ WP (App (Val (RecV BAnon BAnon B)) (Val v)) {{ Ψ }} := by
  iintro H; wp_pure; iexact H

/-- Consuming the arguments one at a time. The postcondition is the "rest of
the application", which is what makes the induction go through without an
inverse bind rule (as in Rocq). -/
theorem wp_lams (xs : List GoString) (vs : List val) (m : GMap String val) (e : cexpr)
    (Φ : val → IProp GF) :
    xs.length = vs.length →
    WP (csubst (binds (pnames xs) vs m) e) {{ Φ }} ⊢
    WP (lams xs (csubst (delete_names (pnames xs) m) e))
       {{ w, WP (apply_vals_e (Val w) vs) {{ Φ }} }} := by
  induction xs generalizing vs m Φ with
  | nil =>
    intro Hlen
    cases vs with
    | cons _ _ => cases Hlen
    | nil =>
      iintro H
      simp only [pnames, List.map_nil, delete_names_nil, binds, lams]
      iapply wp_wand $$ H
      iintro %w Hw
      simp only [apply_vals_e, List.foldl_nil]
      wp_pures
      iexact Hw
  | cons x xs ih =>
    intro Hlen
    cases vs with
    | nil => cases Hlen
    | cons v vs =>
      rw [show binds (pnames (x :: xs)) (v :: vs) m = binds (pnames xs) vs (<[pname x := v]> m)
        from rfl]
      iintro H
      simp only [lams]
      wp_pures
      rw [apply_vals_e_cons, apply_vals_e_fill]
      iapply wp_bind (fill (app_ctx vs))
      iapply wp_beta_recv
      rw [lams_step]
      iapply wp_wand $$ [H]
      · iapply ih vs _ _ (by simpa using Hlen)
        iexact H
      · iintro %w Hw
        rw [← apply_vals_e_fill]
        iexact Hw

/-- The top-level application: `func_val f` applied to its arguments. -/
theorem wp_func_val (f : cfunc) (args : List val) (Φ : val → IProp GF) :
    args.length = f.fparams.length →
    f.fparams ≠ [] →
    WP (csubst (binds (pnames f.fparams) args ∅) f.fbody) {{ Φ }} ⊢
    WP (apply_vals (func_val f) args) {{ Φ }} := by
  intro Hlen Hne
  obtain ⟨ps, body⟩ := f
  simp only at Hlen Hne ⊢
  cases ps with
  | nil => exact absurd rfl Hne
  | cons x xs =>
    cases args with
    | nil => cases Hlen
    | cons v vs =>
      rw [pnames_cons, binds_cons]
      iintro H
      rw [apply_vals_unfold, apply_vals_e_cons, apply_vals_e_fill]
      simp only [func_val]
      iapply wp_bind (fill (app_ctx vs))
      iapply wp_beta_recv
      rw [lams_step_empty]
      iapply wp_wand $$ [H]
      · iapply wp_lams xs vs _ _ _ (by simpa using Hlen.symm)
        iexact H
      · iintro %w Hw
        rw [← apply_vals_e_fill]
        iexact Hw

theorem wp_func_val_nil (f : cfunc) (θ : Nat → val) (Φ : val → IProp GF) :
    f.fparams = [] →
    WP (expr_of f.fbody) {{ Φ }} ⊢
    WP (apply_vals (func_val f) (arg_vals f θ)) {{ Φ }} := by
  intro Hnil
  obtain ⟨ps, body⟩ := f
  simp only at Hnil
  subst Hnil
  simp only [apply_vals, arg_vals, func_val, List.foldl]
  exact wp_beta_anon _ _ _

end steps

end Checker
end Perennial
