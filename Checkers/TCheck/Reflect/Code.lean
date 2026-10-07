/-
Soundness of the Lean table checker, part 2: the code.

`csubst DA m e` is the GooseLang expression the code `e` stands for
(`cexpr_den DA e`, Denote.lean) once its free variables are replaced by the
values `m` gives them -- the shape of the body after the function has been
applied and its `let:`s have taken their beta steps. `env_den θ en` is the
substitution the checker's environment stands for. As
Checkers/Checker/Subst.lean does for checker/, a beta step is `csubst_insert`
and the application of the function to its arguments is `wp_func_val`.
-/
import Checkers.TCheck.Reflect.Terms
import Checkers.Checker.ExecSpec

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace TCheck
namespace LC

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open GMap (delete)

section subst
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
variable {syms : List symdecl} {preds : List preddecl} (DA : DenAt GF syms preds)

mutual
/-- `cexpr_den DA e` with the free variables in `m`'s domain replaced. -/
def csubst (m : GMap String val) : cexpr → Expr
  | CVal t => Val (val_den DA [] t)
  | CVar x => match m !! x with | some v => Val v | none => Var x
  | CApp a b => App (csubst m a) (csubst m b)
  | CPair a b => Pair (csubst m a) (csubst m b)
  | CLet x a b => App (Rec BAnon (BNamed x) (csubst (delete x m) b)) (csubst m a)
  | CSeq a b => App (Rec BAnon BAnon (csubst m b)) (csubst m a)
  | CLit ty es => LiteralValue (csubst_lit m (type_den DA ty) es)
  | CDo a => App (Val doExecute) (csubst m a)
  | CRet a => App (Val doReturn) (csubst m a)
  | CXSeq a b => App (App (Val exceptionSeq) (Rec BAnon BAnon (csubst m b))) (csubst m a)
  | CXDo a => App (Val exceptionDo) (csubst m a)
def csubst_lit (m : GMap String val) (t : go.GoType) : List cexpr → List keyed_element
  | [] => []
  | e :: es => KeyedElement none (ElementExpression t (csubst m e)) :: csubst_lit m t es
end

mutual
theorem csubst_empty : ∀ e : cexpr, csubst DA ∅ e = cexpr_den DA e
  | CVal _ => rfl
  | CVar x => by simp [csubst, cexpr_den, GMap.lookup_empty]
  | CApp a b => by simp only [csubst, cexpr_den, csubst_empty a, csubst_empty b]
  | CPair a b => by simp only [csubst, cexpr_den, csubst_empty a, csubst_empty b]
  | CLet x a b => by simp only [csubst, cexpr_den, GMap.delete_empty, csubst_empty a, csubst_empty b]
  | CSeq a b => by simp only [csubst, cexpr_den, csubst_empty a, csubst_empty b]
  | CLit ty es => by simp only [csubst, cexpr_den, csubst_lit_empty (type_den DA ty) es]
  | CDo a => by simp only [csubst, cexpr_den, csubst_empty a]
  | CRet a => by simp only [csubst, cexpr_den, csubst_empty a]
  | CXSeq a b => by simp only [csubst, cexpr_den, csubst_empty a, csubst_empty b]
  | CXDo a => by simp only [csubst, cexpr_den, csubst_empty a]
theorem csubst_lit_empty (t : go.GoType) : ∀ es : List cexpr, csubst_lit DA ∅ t es = lit_den DA t es
  | [] => rfl
  | e :: es => by simp only [csubst_lit, lit_den, csubst_empty e, csubst_lit_empty t es]
end

mutual
/-- The equation a beta step needs: substituting the argument into the body
extends the environment. -/
theorem csubst_insert (x : String) (v : val) :
    ∀ (m : GMap String val) (e : cexpr), subst x v (csubst DA (delete x m) e) = csubst DA (<[x := v]> m) e
  | m, CVal _ => rfl
  | m, CVar y => by
      simp only [csubst]
      by_cases hx : y = x
      · subst hx; simp [subst]
      · rw [GMap.lookup_delete_ne _ (Ne.symm hx), GMap.lookup_insert_ne _ _ (Ne.symm hx)]
        cases m !! y <;> simp [subst, Ne.symm hx]
  | m, CApp a b => by simp only [csubst, subst, csubst_insert x v m a, csubst_insert x v m b]
  | m, CPair a b => by simp only [csubst, subst, csubst_insert x v m a, csubst_insert x v m b]
  | m, CLet y a b => by
      simp only [csubst, subst, csubst_insert x v m a]
      by_cases hx : x = y
      · subst hx
        simp [GMap.delete_idemp, GMap.delete_insert_eq]
      · have hne : BNamed x ≠ BNamed y := by simpa using hx
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, hne, and_self, ↓reduceIte]
        rw [GMap.delete_commute, csubst_insert x v (delete y m) b, GMap.delete_insert_ne _ _ (Ne.symm hx)]
  | m, CSeq a b => by
      simp only [csubst, subst, csubst_insert x v m a, csubst_insert x v m b]
      simp
  | m, CLit ty es => by simp only [csubst, subst, csubst_lit_insert x v m (type_den DA ty) es]
  | m, CDo a => by simp only [csubst, subst, csubst_insert x v m a]
  | m, CRet a => by simp only [csubst, subst, csubst_insert x v m a]
  | m, CXSeq a b => by
      simp only [csubst, subst, csubst_insert x v m a, csubst_insert x v m b]
      simp
  | m, CXDo a => by simp only [csubst, subst, csubst_insert x v m a]
theorem csubst_lit_insert (x : String) (v : val) (m : GMap String val) (t : go.GoType) :
    ∀ es : List cexpr, substKeyedElements x v (csubst_lit DA (delete x m) t es) =
      csubst_lit DA (<[x := v]> m) t es
  | [] => rfl
  | e :: es => by
      simp only [csubst_lit, substKeyedElements, substKeyedElement, substOptKey, substElement,
        csubst_insert x v m e, csubst_lit_insert x v m t es]
end

/-! ## The environment -/

/-- The substitution the checker's environment stands for; the head of the
list wins, as in `lookup`. -/
def env_den (θ : List (dyn DA)) (en : env) : GMap String val :=
  en.foldr (fun xt m => <[xt.1 := val_den DA θ xt.2]> m) ∅

theorem env_den_cons (θ : List (dyn DA)) (x : String) (t : tterm) (en : env) :
    env_den DA θ ((x, t) :: en) = <[x := val_den DA θ t]> (env_den DA θ en) := rfl

theorem env_den_lookup (θ : List (dyn DA)) : ∀ (en : env) (x : String),
    env_den DA θ en !! x = (lookup en x).map (val_den DA θ)
  | [], _ => by simp [env_den, lookup, GMap.lookup_empty]
  | (y, t) :: en, x => by
      rw [env_den_cons]
      simp only [lookup, beq_iff_eq]
      by_cases h : y = x
      · subst h; simp [GMap.lookup_insert_eq]
      · rw [GMap.lookup_insert_ne _ _ h]; simp [h, env_den_lookup θ en x]

theorem env_den_bindParams (θ : List (dyn DA)) : ∀ (xs : List String) (ts : List tterm) (en : env),
    env_den DA θ (bindParams xs ts en) = Checker.binds xs (ts.map (val_den DA θ)) (env_den DA θ en)
  | x :: xs, t :: ts, en => by
      simp only [bindParams, List.map_cons, Checker.binds_cons]
      rw [env_den_bindParams θ xs ts, env_den_cons]
  | [], _, _ => by cases ‹List tterm› <;> rfl
  | _ :: _, [], _ => rfl

/-! ## Substitution under a chain of lambdas -/

theorem subst_lams (x : String) (v : val) : ∀ (xs : List String) (e : Expr),
    subst x v (lams xs e) = lams xs (if x ∈ xs then e else subst x v e)
  | [], e => by simp [lams]
  | y :: ys, e => by
      simp only [lams]
      rw [Checker.subst_lam_named]
      congr 1
      by_cases hxy : x = y
      · have : x ∈ y :: ys := by simp [hxy]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hxy), ite_eq_left_of_eq_true _ _ (eq_true this)]
      · simp only [hxy, ↓reduceIte]
        rw [subst_lams x v ys e]
        congr 1
        simp [hxy]

theorem lams_step (x : String) (xs : List String) (m : GMap String val) (v : val) (e : cexpr) :
    subst x v (lams xs (csubst DA (Checker.delete_names (x :: xs) m) e)) =
    lams xs (csubst DA (Checker.delete_names xs (<[x := v]> m)) e) := by
  rw [subst_lams]
  congr 1
  rw [Checker.delete_names_cons]
  by_cases Hin : x ∈ xs
  · simp only [Hin, ↓reduceIte]
    rw [Checker.delete_names_insert_elem _ _ _ _ Hin, Checker.delete_names_elem _ _ _ Hin]
  · simp only [Hin, ↓reduceIte]
    rw [Checker.delete_names_insert_not_elem _ _ _ _ Hin, ← csubst_insert]

theorem lams_step_empty (x : String) (xs : List String) (v : val) (e : cexpr) :
    subst x v (lams xs (cexpr_den DA e)) =
    lams xs (csubst DA (Checker.delete_names xs (<[x := v]> ∅)) e) := by
  rw [← lams_step DA x xs ∅ v e, Checker.delete_names_empty, csubst_empty]

end subst

section wp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {syms : List symdecl} {preds : List preddecl} (DA : DenAt GF syms preds)

/-! ## Steps in an evaluation context -/

/-- A value step in context `K`. -/
theorem wp_ctx_val (K : List EctxItem) (e : Expr) (v : val) (Ψ : val → IProp GF)
    (H : ∀ Φ : val → IProp GF, Φ v ⊢ WP e {{ Φ }}) :
    WP (fill K (Val v)) {{ Ψ }} ⊢ WP (fill K e) {{ Ψ }} := by
  iintro Hk
  iapply wp_bind (fill K)
  iapply H (fun w => iprop(WP (fill K (Val w)) {{ Ψ }}))
  iexact Hk

/-- An expression step in context `K`. -/
theorem wp_ctx_expr (K : List EctxItem) (e1 e2 : Expr) (Ψ : val → IProp GF)
    (H : ∀ Φ : val → IProp GF, WP e2 {{ Φ }} ⊢ WP e1 {{ Φ }}) :
    WP (fill K e2) {{ Ψ }} ⊢ WP (fill K e1) {{ Ψ }} := by
  iintro Hk
  iapply wp_bind (fill K)
  iapply H
  iapply wp_bind_inv (fill K)
  iexact Hk

/-! ## Applying the function to its arguments -/

theorem apply_vals_fill' (h : Expr) (vs : List val) :
    vs.foldl (fun e v => App e (Val v)) h = fill (vs.map EctxItem.AppLCtx) h :=
  apply_vals_fill vs h

theorem wp_lams (xs : List String) (vs : List val) (m : GMap String val) (e : cexpr)
    (Φ : val → IProp GF) :
    xs.length = vs.length →
    WP (csubst DA (Checker.binds xs vs m) e) {{ Φ }} ⊢
    WP (lams xs (csubst DA (Checker.delete_names xs m) e))
       {{ w, WP (vs.foldl (fun e v => App e (Val v)) (Val w)) {{ Φ }} }} := by
  induction xs generalizing vs m Φ with
  | nil =>
    intro Hlen
    cases vs with
    | cons _ _ => cases Hlen
    | nil =>
      iintro H
      simp only [Checker.delete_names_nil, Checker.binds, lams]
      iapply wp_wand $$ H
      iintro %w Hw
      simp only [List.foldl_nil]
      wp_pures
      iexact Hw
  | cons x xs ih =>
    intro Hlen
    cases vs with
    | nil => cases Hlen
    | cons v vs =>
      rw [show Checker.binds (x :: xs) (v :: vs) m = Checker.binds xs vs (<[x := v]> m) from rfl]
      iintro H
      simp only [lams]
      wp_pures
      rw [List.foldl_cons, apply_vals_fill']
      iapply wp_bind (fill (vs.map EctxItem.AppLCtx))
      iapply Checker.wp_beta_recv
      rw [lams_step]
      iapply wp_wand $$ [H]
      · iapply ih vs _ _ (by simpa using Hlen)
        iexact H
      · iintro %w Hw
        rw [← apply_vals_fill']
        iexact Hw

/-- The top-level application: `func_val f` applied to its arguments. -/
theorem wp_func_val (f : cfunc) (args : List val) (Φ : val → IProp GF) :
    args.length = f.fn_params.length → f.fn_params ≠ [] →
    WP (csubst DA (Checker.binds f.fn_params args ∅) f.fn_body) {{ Φ }} ⊢
    WP (apply_vals (func_val DA f) args) {{ Φ }} := by
  intro Hlen Hne
  obtain ⟨ps, body⟩ := f
  simp only at Hlen Hne ⊢
  cases ps with
  | nil => exact absurd rfl Hne
  | cons x xs =>
    cases args with
    | nil => cases Hlen
    | cons v vs =>
      rw [Checker.binds_cons]
      iintro H
      simp only [apply_vals, List.foldl_cons]
      rw [apply_vals_fill']
      simp only [func_val]
      iapply wp_bind (fill (vs.map EctxItem.AppLCtx))
      iapply Checker.wp_beta_recv
      rw [lams_step_empty]
      iapply wp_wand $$ [H]
      · iapply wp_lams DA xs vs _ _ _ (by simpa using Hlen.symm)
        iexact H
      · iintro %w Hw
        rw [← apply_vals_fill']
        iexact Hw

end wp

end LC
end TCheck
end Perennial
