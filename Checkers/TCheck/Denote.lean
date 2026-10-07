/-
Port of `new/tcheck/denote.v`.

# What an input of the table-driven checker means

A table names its sorts, symbols and predicates; a denotation `DA`
gives each of them a Lean meaning, typed by the table's declarations (so
that a well-sorted term always evaluates).  Everything is relative to an
ambient GooseLang setting -- an FFI, a ghost state `HeapGS hlc GF`, a Go
semantics -- exactly the section variables of a spec in the etcd proofs
(`raft.becomeFollower.spec` etc.); a denotation may need more (for raft,
the package assumptions `go_etcd_io.raft.v3.Assumptions`), which it takes
as arguments of its own.

- `rule_valid DA r` is the Hoare triple a rule stands for, in Perennial's
  texan-triple form, so that it computes to the statement of the lemma it
  is linked to.
- `table_valid DA rs fs`: every rule and fact of the input holds and every
  predicate declared persistent is.
- `input_holds i`: in every ambient setting and every denotation in which
  the table is valid, the function satisfies its specification.

Lean notes:
* **The ambient is quantified once, in `input_holds`, outside the
  denotation**, and a denotation (`DenAt`) is one ambient's. Rocq instead
  quantified it inside every validity statement (`every_ambient`) and made a
  denotation a family over ambients satisfying package assumptions `d_pkg`.
  The Lean form is forced by etcdGrove's spec/proof discipline: a proof's
  callee specs are hypotheses *at the proof's own ambient* (its section
  variables), so the validity of a rule linked to one holds at that ambient
  only, and Rocq's `table_valid` (at every ambient) could not be established
  from it. The two statements of `input_holds` are equivalent (instantiate
  Rocq's family at one ambient; conversely, take the family that is `DA` at
  `DA`'s ambient and empty elsewhere), so `check_adequate` claims no more.
  With the ambient fixed, `d_pkg` disappears: the package assumptions are
  arguments of the table's denotation (`raft_den`, `TableRaft.lean`).
* Functions over lists of terms (`teval`'s arguments, a literal's
  elements) are mutual with a list version (`tevals`, `cexprs_den`), so that
  the recursion is structural and computes in the kernel.
* `Forall` is a recursive conjunction (Rocq's inductive `Forall`), so that a
  concrete `table_valid` is proved by an anonymous constructor of the rules'
  lemmas without computing anything. `vapp` (Rocq `app`) and `nth_error` are
  defined here by structural recursion, and `nat_cast` takes its argument,
  so that `tc_simp` (`Link.lean`) computes them.
* `#()`, `#l` are Perennial's `intoVal` (`GoGlobalContext`), which is what
  the Goose output and the specs use; so `TUnit` denotes `#()`, not a
  literal `LitV LitUnit`.
-/
import Perennial.Golang.Theory
import Checkers.TCheck.Syntax

noncomputable section

namespace Perennial
namespace TCheck

open Iris Iris.BI

def lookup_sym : List symdecl → Nat → symdecl
  | [], _ => mkSym [] SVal
  | d :: _, 0 => d
  | _ :: l, n + 1 => lookup_sym l n

def lookup_pred : List preddecl → Nat → preddecl
  | [], _ => mkPred false []
  | d :: _, 0 => d
  | _ :: l, n + 1 => lookup_pred l n

/-- Rocq `List.nth_error`. -/
def nth_error {A : Type} : List A → Nat → Option A
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: l, n + 1 => nth_error l n

/-- Rocq `app` (`++`), by structural recursion of its own, so that `tc_simp`
(`Link.lean`) computes it with its equations. -/
def vapp {A : Type} : List A → List A → List A
  | [], l => l
  | x :: l, l' => x :: vapp l l'

/-- `P` of every element of a list (Rocq `Forall`). -/
def Forall {A : Type} (P : A → Prop) : List A → Prop
  | [] => True
  | x :: l => P x ∧ Forall P l

section sorts
variable [ext : FfiSyntax] (ds : Nat → Type)

def srt_den (s : srt) : Type :=
  match s with
  | SVal => val
  | SType => go.GoType
  | SU n => ds n

universe u in
def arrows (args : List srt) (R : Type u) : Type u :=
  match args with
  | [] => R
  | a :: l => srt_den ds a → arrows l R

def sym_ty (d : symdecl) : Type := arrows ds d.sd_args (srt_den ds d.sd_res)
def pred_ty (GF : BundledGFunctors) (d : preddecl) : Type := arrows ds d.pd_args (IProp GF)
end sorts

/-- The meaning of the table's sorts, symbols and predicates, in one ambient
setting. -/
structure DenAt [FfiSyntax] (GF : BundledGFunctors) (syms : List symdecl) (preds : List preddecl) where
  mkDenAt ::
  d_sort : Nat → Type
  d_sym : ∀ n, sym_ty d_sort (lookup_sym syms n)
  d_pred : ∀ n, pred_ty d_sort GF (lookup_pred preds n)
export DenAt (mkDenAt)

section eval
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {syms : List symdecl} {preds : List preddecl} (DA : DenAt GF syms preds)

/-- A value of some sort. -/
abbrev dyn : Type := (s : srt) × srt_den DA.d_sort s

def nat_cast (P : Nat → Type) : (i j : Nat) → P i → Option (P j)
  | 0, 0, x => some x
  | i + 1, j + 1, x => nat_cast (fun k => P (k + 1)) i j x
  | _, _, _ => none

/-- `d` at sort `s`, if it has that sort.  Defined by matching on the two
sort codes, so that it computes on closed codes without any proof of
equality. -/
def cast (s : srt) (d : dyn DA) : Option (srt_den DA.d_sort s) :=
  match d with
  | ⟨s', x⟩ =>
      (match (motive := ∀ s' s : srt, srt_den DA.d_sort s' → Option (srt_den DA.d_sort s)) s', s with
       | SVal, SVal => fun x => some x
       | SType, SType => fun x => some x
       | SU i, SU j => fun x => nat_cast DA.d_sort i j x
       | _, _ => fun _ => none) x

universe u in
def sym_apply : (args : List srt) → {R : Type u} → arrows DA.d_sort args R →
    List (Option (dyn DA)) → Option R
  | [], _, f, [] => some f
  | [], _, _, _ :: _ => none
  | _ :: _, _, _, [] => none
  | _ :: _, _, _, none :: _ => none
  | a :: args, _, f, some d :: vs =>
      match cast DA a d with
      | some x => sym_apply args (f x) vs
      | none => none

def as_val (d : Option (dyn DA)) : Option val :=
  match d with
  | some d => cast DA SVal d
  | none => none

def vals_of : List (Option (dyn DA)) → Option (List val)
  | [] => some []
  | d :: ds =>
      match as_val DA d, vals_of ds with
      | some v, some vs => some (v :: vs)
      | _, _ => none

mutual
def teval (θ : List (dyn DA)) : tterm → Option (dyn DA)
  | TVar n => nth_error θ n
  | TSym n args =>
      match sym_apply DA (lookup_sym syms n).sd_args (DA.d_sym n) (tevals θ args) with
      | some r => some ⟨(lookup_sym syms n).sd_res, r⟩
      | none => none
  | TPair a b =>
      match as_val DA (teval θ a), as_val DA (teval θ b) with
      | some va, some vb => some ⟨SVal, PairV va vb⟩
      | _, _ => none
  | TLit ty es =>
      match (match teval θ ty with
             | some d => cast DA SType d
             | none => none),
            vals_of DA (tevals θ es) with
      | some t, some vs =>
          some ⟨SVal, LiteralValueV (vs.map fun v => KeyedElement none (ElementExpression t (Val v)))⟩
      | _, _ => none
  | TUnit => some ⟨SVal, #()⟩
/-- `teval` of each term (Rocq `map (teval θ)`). -/
def tevals (θ : List (dyn DA)) : List tterm → List (Option (dyn DA))
  | [] => []
  | t :: ts => teval θ t :: tevals θ ts
end

/-- A term at sort `val`; `#()` if it is not one (which a well-formed input
never asks for). -/
def val_den (θ : List (dyn DA)) (t : tterm) : val :=
  match as_val DA (teval DA θ t) with
  | some v => v
  | none => #()

def type_den (t : tterm) : go.GoType :=
  match teval DA [] t with
  | some d =>
      match cast DA SType d with
      | some ty => ty
      | none => go.bool
  | none => go.bool

def atom_den (θ : List (dyn DA)) (a : tatom) : IProp GF :=
  match a with
  | APred n args =>
      match sym_apply DA (lookup_pred preds n).pd_args (DA.d_pred n) (tevals DA θ args) with
      | some P => P
      | none => iprop(False)
  | AEq a b => iprop(⌜∃ d, teval DA θ a = some d ∧ teval DA θ b = some d⌝)

/-- An assertion: `True` if empty, else its atoms joined by `∗` without a
trailing unit, the way a spec is written. -/
def assn_den (θ : List (dyn DA)) : List tatom → IProp GF
  | [] => iprop(True)
  | [a] => atom_den DA θ a
  | a :: l => iprop(atom_den DA θ a ∗ assn_den θ l)

def pat_den (θ : List (dyn DA)) : tpat → Expr
  | PVal t => Val (val_den DA θ t)
  | PApp a b => App (pat_den θ a) (pat_den θ b)

mutual
/-- The code, as GooseLang: each node is what Goose emits for it. -/
def cexpr_den : cexpr → Expr
  | CVal t => Val (val_den DA [] t)
  | CVar x => Var x
  | CApp a b => App (cexpr_den a) (cexpr_den b)
  | CPair a b => Pair (cexpr_den a) (cexpr_den b)
  | CLet x a b => App (Rec BAnon (BNamed x) (cexpr_den b)) (cexpr_den a)
  | CSeq a b => App (Rec BAnon BAnon (cexpr_den b)) (cexpr_den a)
  | CLit ty es => LiteralValue (lit_den (type_den DA ty) es)
  | CDo a => App (Val doExecute) (cexpr_den a)
  | CRet a => App (Val doReturn) (cexpr_den a)
  | CXSeq a b => App (App (Val exceptionSeq) (Rec BAnon BAnon (cexpr_den b))) (cexpr_den a)
  | CXDo a => App (Val exceptionDo) (cexpr_den a)
/-- The elements of a literal at type `t` (Rocq `List.map` of
`KeyedElement None (ElementExpression t _)`). -/
def lit_den (t : go.GoType) : List cexpr → List keyed_element
  | [] => []
  | e :: es => KeyedElement none (ElementExpression t (cexpr_den e)) :: lit_den t es
end

def lams : List String → Expr → Expr
  | [], e => e
  | x :: xs, e => Rec BAnon (BNamed x) (lams xs e)

/-- `λ: x1 .. xn, body`, or `λ: <>, body` without parameters. -/
def func_val (f : cfunc) : val :=
  match f.fn_params with
  | [] => RecV BAnon BAnon (cexpr_den DA f.fn_body)
  | x :: xs => RecV BAnon (BNamed x) (lams xs (cexpr_den DA f.fn_body))

def apply_vals (f : val) (args : List val) : Expr :=
  args.foldl (fun e v => App e (Val v)) (Val f)

/-- Universal quantification over variables of sorts `ss`, appended to a
valuation; it computes to curried binders. -/
def forall_sorts : (ss : List srt) → (List (dyn DA) → Prop) → Prop
  | [], k => k []
  | s :: ss, k => ∀ x : srt_den DA.d_sort s, forall_sorts ss (fun θ => k (⟨s, x⟩ :: θ))

def bi_forall_sorts : (ss : List srt) → (List (dyn DA) → IProp GF) → IProp GF
  | [], k => k []
  | s :: ss, k => iprop(∀ x : srt_den DA.d_sort s, bi_forall_sorts ss (fun θ => k (⟨s, x⟩ :: θ)))

/-- `{{ pre }} e {{ ∃ ex, RET ret; post }}` at valuation `θ`, as the texan
triple unfolds (iris-lean `Iris/BI/WeakestPre.lean`). -/
def triple_at (θ : List (dyn DA)) (pre : List tatom) (e : Expr) (ex : List srt) (ret : tterm)
    (post : List tatom) : Prop :=
  ⊢ iprop(∀ Φ : val → IProp GF,
    assn_den DA θ pre -∗
    ▷ bi_forall_sorts DA ex (fun θx => iprop(assn_den DA (vapp θ θx) post -∗ Φ (val_den DA (vapp θ θx) ret))) -∗
    WP e {{ Φ }})

def pers_ok : (args : List srt) → arrows DA.d_sort args (IProp GF) → Prop
  | [], P => @Persistent (IProp GF) _ P
  | _ :: args, P => ∀ x, pers_ok args (P x)

/-- The persistence obligations of the predicates `n0`, `n0 + 1`, ... in
`l`: one conjunct per persistent one. -/
def pers_obl : List preddecl → Nat → Prop
  | [], _ => True
  | d :: l, n0 =>
      (match d.pd_pers with
       | true => pers_ok DA (lookup_pred preds n0).pd_args (DA.d_pred n0)
       | false => True) ∧
      pers_obl l (n0 + 1)

def rule_valid (r : trule) : Prop :=
  forall_sorts DA r.r_vars (fun θ =>
    triple_at DA θ r.r_pre (pat_den DA θ r.r_lhs) r.r_ex r.r_ret r.r_post)

def fact_valid (f : tfact) : Prop :=
  forall_sorts DA f.f_vars (fun θ => teval DA θ f.f_lhs = teval DA θ f.f_rhs)

def preds_valid : Prop := pers_obl DA preds 0

def table_valid (rs : List trule) (fs : List tfact) : Prop :=
  Forall (rule_valid DA) rs ∧ Forall (fact_valid DA) fs ∧ preds_valid DA

/-- The function's specification, in denotation `DA`. -/
def spec_valid (f : cfunc) (sp : tspec) : Prop :=
  forall_sorts DA sp.sp_vars (fun θ =>
    triple_at DA θ sp.sp_pre (apply_vals (func_val DA f) (sp.sp_args.map (val_den DA θ)))
      sp.sp_ex sp.sp_ret sp.sp_post)
end eval

/-- What `tcheck.Check` answering `true` on `ser_input i` is claimed to
mean (`Observe.lean`): in every ambient setting, the specification holds in
every denotation of the table in which its rules, facts and persistence
claims hold. -/
def input_holds (i : tinput) : Prop :=
  ∀ [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors} [HeapGS hlc GF] [go.Semantics]
    (DA : DenAt GF i.in_syms i.in_preds),
    table_valid DA i.in_rules i.in_facts → spec_valid DA i.in_func i.in_spec

end TCheck
end Perennial
