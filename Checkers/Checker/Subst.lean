/-
Port of `new/checker/subst.v`.

Substitution for the checker's fragment.

The reference semantics of the analysed program substitutes values for
parameters and `let`-bound names; the checker instead carries an
environment. `csubst m e` is the GooseLang expression that the checker
input `e` denotes once its free variables have been replaced according to
`m` -- that is, `expr_of e` with the environment already applied.

Defining it by recursion on `cexpr` rather than as a `subst_map` over all
of GooseLang's `Expr` keeps every induction here an 18-case induction over
the fragment, instead of a mutual induction over `Expr`/`val`/keyed
elements/select clauses.

Lean notes:
* Rocq's `pname` notation is the definition `pname` of Defs.lean (Rocq
  `go.go_string_to_string`). Its injectivity (`pname_inj`) is proved directly
  (each byte is a valid character, `Char.ofNat` is injective below 256)
  instead of through a left inverse.
* Maps are `GMap String val`; `delete` is `GMap.delete`.
* Everything here needs only `[FfiSyntax] [GoGlobalContext]` (for `#`) and is
  stated outside any ghost-state section.
-/
import Checkers.Checker.Defs

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open GMap (delete)

section subst
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

theorem char_ofNat_toNat_lt (n : Nat) (h : n < 256) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := by unfold Nat.isValidChar; omega
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

/-- `pname` is injective, so distinct Go names stay distinct as GooseLang
binders. -/
theorem list_map_inj_of_inj {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ (x y : List α), x.map f = y.map f → x = y
  | [], [], _ => rfl
  | [], _ :: _, H => by simp at H
  | _ :: _, [], H => by simp at H
  | a :: x, b :: y, H => by
    simp only [List.map_cons, List.cons.injEq] at H
    rw [hf a b H.1, list_map_inj_of_inj f hf x y H.2]

theorem pname_inj {x y : GoString} : pname x = pname y → x = y := by
  intro H
  have H' := congrArg String.toList H
  simp only [pname, String.toList_ofList] at H'
  have Hc : ∀ b : w8, (Char.ofNat b.toNat).toNat = b.toNat :=
    fun b => char_ofNat_toNat_lt _ b.isLt
  refine list_map_inj_of_inj _ ?_ x y H'
  intro a b Hab
  apply BitVec.eq_of_toNat_eq
  rw [← Hc a, ← Hc b, Hab]

theorem pname_ne {x y : GoString} : x ≠ y → pname x ≠ pname y :=
  fun H H' => H (pname_inj H')

/-- `csubst m e` agrees with `expr_of e` except at the free variables in the
domain of `m`, which become the values `m` gives them. -/
def csubst (m : GMap String val) : cexpr → Expr
  | CEInt w => Val #w
  | CEBool b => Val #b
  | CEUnit => Val #()
  | CEVar x => match m !! pname x with | some v => Val v | none => Var (pname x)
  | CELet x e1 e2 =>
      App (Rec BAnon (BNamed (pname x)) (csubst (delete (pname x) m) e2)) (csubst m e1)
  | CESeq e1 e2 => App (Rec BAnon BAnon (csubst m e2)) (csubst m e1)
  | CEIf c e1 e2 => If (csubst m c) (csubst m e1) (csubst m e2)
  | CELoad t e => App (Val (GoInstruction (GoLoad (type_of t)))) (csubst m e)
  | CEStore t e1 e2 =>
      App (Val (GoInstruction (GoStore (type_of t)))) (Pair (csubst m e1) (csubst m e2))
  | CEAlloc t e => App (Val (GoInstruction (GoAlloc (type_of t)))) (csubst m e)
  | CEZero t => App (Val (GoInstruction (GoZeroVal (type_of t)))) (Val #())
  | CEBinOp op t e1 e2 =>
      App (Val (GoInstruction (GoOp (binop_of op) (type_of t)))) (Pair (csubst m e1) (csubst m e2))
  | CEUnOp op t e => App (Val (GoInstruction (GoUnOp (unop_of op) (type_of t)))) (csubst m e)
  | CEConvert t1 t2 e =>
      App (Val (GoInstruction (Convert (type_of t1) (type_of t2)))) (csubst m e)
  | CEDo e => App (Val doExecute) (csubst m e)
  | CEReturn e => App (Val doReturn) (csubst m e)
  | CEExcSeq e1 e2 => App (App (Val exceptionSeq) (Rec BAnon BAnon (csubst m e2))) (csubst m e1)
  | CEExcDo e => App (Val exceptionDo) (csubst m e)

theorem csubst_empty (e : cexpr) : csubst ∅ e = expr_of e := by
  induction e <;> simp_all [csubst, expr_of, GMap.delete_empty]

/-- The equation that a beta step needs: substituting the argument into the
body is the same as extending the environment. -/
theorem csubst_insert (m : GMap String val) (x : String) (v : val) (e : cexpr) :
    subst x v (csubst (delete x m) e) = csubst (<[x := v]> m) e := by
  induction e generalizing m with
  | CEVar y =>
    simp only [csubst]
    by_cases hx : pname y = x
    · subst hx
      simp [subst]
    · rw [GMap.lookup_delete_ne _ (Ne.symm hx), GMap.lookup_insert_ne _ _ (Ne.symm hx)]
      cases m !! pname y <;> simp [subst, Ne.symm hx]
  | CELet y e1 e2 ih1 ih2 =>
    simp only [csubst, subst, ih1]
    by_cases hx : x = pname y
    · subst hx
      simp [GMap.delete_idemp, GMap.delete_insert_eq]
    · have hne : BNamed x ≠ BNamed (pname y) := by simpa using hx
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, hne, and_self, ↓reduceIte]
      rw [GMap.delete_commute, ih2, GMap.delete_insert_ne _ _ (Ne.symm hx)]
  | _ => simp_all [csubst, subst]

/-! ## Deleting a list of names, and the environment a curried application
builds -/

def pnames (xs : List GoString) : List String := xs.map pname

theorem pnames_cons (x : GoString) (xs : List GoString) :
    pnames (x :: xs) = pname x :: pnames xs := rfl

def delete_names (xs : List String) (m : GMap String val) : GMap String val :=
  xs.foldr delete m

theorem delete_names_nil (m : GMap String val) : delete_names [] m = m := rfl
theorem delete_names_cons (x : String) (xs : List String) (m : GMap String val) :
    delete_names (x :: xs) m = delete x (delete_names xs m) := rfl

theorem delete_names_empty (xs : List String) : delete_names xs (∅ : GMap String val) = ∅ := by
  induction xs with
  | nil => rfl
  | cons y xs ih => rw [delete_names_cons, ih, GMap.delete_empty]

theorem delete_names_elem (x : String) (xs : List String) (m : GMap String val) :
    x ∈ xs → delete x (delete_names xs m) = delete_names xs m := by
  induction xs with
  | nil => intro H; cases H
  | cons y xs ih =>
    intro H
    rw [delete_names_cons]
    rcases List.mem_cons.mp H with rfl | Hin
    · exact GMap.delete_idemp _ _
    · rw [GMap.delete_commute, ih Hin]

theorem delete_names_insert_not_elem (x : String) (xs : List String) (v : val)
    (m : GMap String val) :
    x ∉ xs → delete_names xs (<[x := v]> m) = <[x := v]> (delete_names xs m) := by
  induction xs with
  | nil => intro _; rfl
  | cons y xs ih =>
    intro Hnin
    rw [delete_names_cons, delete_names_cons, ih (fun h => Hnin (List.mem_cons_of_mem _ h))]
    apply GMap.delete_insert_ne
    intro h; exact Hnin (h ▸ List.mem_cons_self)

theorem delete_names_insert_elem (x : String) (xs : List String) (v : val)
    (m : GMap String val) :
    x ∈ xs → delete_names xs (<[x := v]> m) = delete_names xs m := by
  induction xs with
  | nil => intro H; cases H
  | cons y xs ih =>
    intro Hin
    rw [delete_names_cons, delete_names_cons]
    by_cases Hin' : x ∈ xs
    · rw [ih Hin']
    · rcases List.mem_cons.mp Hin with rfl | H
      · rw [delete_names_insert_not_elem _ _ _ _ Hin', GMap.delete_insert_eq]
      · exact absurd H Hin'

/-- The environment built by applying `vs` to the parameters `xs`: later
parameters shadow earlier ones, exactly as `envBind` in checker/check.go
puts the last binding at the head of the list. -/
def binds : List String → List val → GMap String val → GMap String val
  | x :: xs', v :: vs', m => binds xs' vs' (<[x := v]> m)
  | _, _, m => m

theorem binds_cons (x : String) (xs : List String) (v : val) (vs : List val)
    (m : GMap String val) :
    binds (x :: xs) (v :: vs) m = binds xs vs (<[x := v]> m) := rfl

/-! ## Substitution under a chain of lambdas -/

/-- `subst` stops at a binder that shadows the substituted name. -/
theorem subst_lam_named (x : String) (v : val) (y : String) (e : Expr) :
    subst x v (Rec BAnon (BNamed y) e) =
    Rec BAnon (BNamed y) (if x = y then e else subst x v e) := by
  by_cases h : x = y
  · subst h; simp [subst]
  · simp [subst, h]

theorem subst_lams (x : String) (v : val) (xs : List GoString) (e : Expr) :
    subst x v (lams xs e) =
      lams xs (if x ∈ pnames xs then e else subst x v e) := by
  induction xs with
  | nil => simp [lams, pnames]
  | cons y ys ih =>
    simp only [lams]
    rw [subst_lam_named]
    congr 1
    by_cases hxy : x = pname y
    · -- the binder shadows `x`: substitution stops here
      have : x ∈ pnames (y :: ys) := by simp [pnames_cons, hxy]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hxy), ite_eq_left_of_eq_true _ _ (eq_true this)]
    · simp only [hxy, ↓reduceIte]
      rw [ih]
      congr 1
      simp [pnames_cons, hxy]

/-- The body of a curried function after one argument has been consumed. -/
theorem lams_step (x : GoString) (xs : List GoString) (m : GMap String val) (v : val)
    (e : cexpr) :
    subst (pname x) v (lams xs (csubst (delete_names (pnames (x :: xs)) m) e)) =
    lams xs (csubst (delete_names (pnames xs) (<[pname x := v]> m)) e) := by
  rw [subst_lams]
  congr 1
  rw [pnames_cons, delete_names_cons]
  by_cases Hin : pname x ∈ pnames xs
  · simp only [Hin, ↓reduceIte]
    rw [delete_names_insert_elem _ _ _ _ Hin, delete_names_elem _ _ _ Hin]
  · simp only [Hin, ↓reduceIte]
    rw [delete_names_insert_not_elem _ _ _ _ Hin, ← csubst_insert]

/-- The same, starting from the empty environment: this is the shape the
top-level application of `func_val` has. -/
theorem lams_step_empty (x : GoString) (xs : List GoString) (v : val) (e : cexpr) :
    subst (pname x) v (lams xs (expr_of e)) =
    lams xs (csubst (delete_names (pnames xs) (<[pname x := v]> ∅)) e) := by
  rw [← lams_step x xs ∅ v e, delete_names_empty, csubst_empty]

/-! ## The environment of the checker's linked-list `env` -/

/-- `env_interp V ρ` is the substitution the checker's environment stands for.
The head of the list wins, matching `envLookup`. -/
def env_interp (V : valuation) (ρ : List (GoString × term)) : GMap String val :=
  ρ.foldr (fun xt m => <[pname xt.1 := teval V xt.2]> m) ∅

theorem env_interp_nil (V : valuation) : env_interp V [] = ∅ := rfl

theorem env_interp_bind (V : valuation) (x : GoString) (t : term) (ρ : List (GoString × term)) :
    env_interp V ((x, t) :: ρ) = <[pname x := teval V t]> (env_interp V ρ) := rfl

/-- `envLookup` finds the first binding of `x`. -/
def env_lookup : List (GoString × term) → GoString → Option term
  | [], _ => none
  | (y, t) :: ρ', x => if y = x then some t else env_lookup ρ' x

theorem env_interp_lookup (V : valuation) (ρ : List (GoString × term)) (x : GoString) :
    env_interp V ρ !! pname x = (env_lookup ρ x).map (teval V) := by
  induction ρ with
  | nil => rfl
  | cons yt ρ ih =>
    obtain ⟨y, t⟩ := yt
    rw [env_interp_bind]
    simp only [env_lookup]
    by_cases h : y = x
    · subst h; simp only [GMap.lookup_insert_eq, ↓reduceIte]; rfl
    · rw [GMap.lookup_insert_ne _ _ (pname_ne h)]
      simp only [h, ↓reduceIte, ih]

end subst

end Checker
end Perennial
