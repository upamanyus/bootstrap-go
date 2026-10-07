/-
Port of `new/checker/defs.v`.

Definitions used to state (and prove) soundness of the Go
symbolic-execution checker in checker/.

The statement itself is in new/checker/soundness.v, which exports this
file; everything here is a definition needed to state it:

- the meaning of the checker's symbolic terms (`teval`) and sorts;
- the checker's input syntax mirrored as inductives (`ctype`,
  `cexpr`, `cfunc`, `cassn`) together with its denotation into real
  GooseLang (`type_of`, `expr_of`, `func_val`) and into Iris assertions
  (`assn_interp`);
- representation predicates (`is_type`, `is_expr`, ...) describing how an
  input tree is laid out in the Go heap, in terms of the Goosed struct types.

Kind codes used in the representation predicates must agree with the
constants in checker/ast.go, checker/term.go and checker/assn.go.

Lean notes:
* Names are Rocq's (`teval`, `is_term`, `triple_holds`), types included
  (`sort`, `term`, `cexpr`); constructors are exported into `Perennial.Checker`
  (`TVar`, `CEInt`, ...). The Go package's own constants (`checker.TVar`, a
  `val`) are only reachable qualified: we `open github_com.upamanyus.bootstrap_go`
  so that `checker.X` names the Goose output, and never open `checker` itself.
* Rocq's `go.go_string_to_string` (a byte-to-character map) is `pname` here:
  each byte becomes the character with that code (`Char.ofNat`). It is
  injective (`pname_inj`, Subst.lean), and on ASCII names it agrees with the
  identifiers the Lean goose backend writes (`pname go!"x" = "x"` by `rfl`).
  A non-ASCII Go identifier would make `func_val f = F.impl` fail to hold,
  which is safe (the trusted equation is checked, not assumed).
* `expr_of` is written with the raw constructors, as in Rocq. The Lean goose
  output uses the abbreviations `Let x e1 e2 = App (Rec BAnon x e2) e1` and
  `Lam BAnon e = Rec BAnon BAnon e`, which unfold to exactly these (the
  `example`s at the bottom of this file check `func_val` against
  `examples.Double.impl` and `examples.Median3.impl` by `rfl`).
* `#x` is `intoVal x`, a field of `GoGlobalContext` (a section variable here,
  while in Rocq it came with `heapGS`), so `triple_holds` also quantifies over
  `GoGlobalContext`, and over `HasLC` (Rocq has no such parameter).
* `heap_pointsto` is `heapPointsto`; the persistent node points-to `l ↦□ v`
  is the typed one (`typedPointsto l v DFrac.discard`) as in Rocq.
-/
import LCheck.Fns
import Generated.GeneratedProof.github_com.upamanyus.bootstrap_go.checker
import Generated.Code.github_com.upamanyus.bootstrap_go.checker.examples

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

namespace Checker

/-! ## Sorts and symbolic terms -/

-- `sort`, `term`, `ctype`, `cop`, `cexpr`, `cfunc`, `cassn`: in LCheck/Syntax.lean.

/-- Codes as in checker/term.go. -/
def sort_code : sort → w64
  | SInt => W64 0
  | SBool => W64 1
  | SLoc => W64 2
  | SUnit => W64 3


section semantics
variable [ext : FfiSyntax]

/-- Concrete GooseLang values. Under `go.Semantics` these are `#w`, `#b`, `#l`,
`#()` (see `go.intoVal_unfold`); the concrete constructors are used so that
`teval` can pattern match. -/
def ival (w : w64) : val := LitV (LitInt w)
def bval (b : Bool) : val := LitV (LitBool b)
def lval (l : Loc) : val := LitV (LitLoc l)
def uval : val := LitV LitUnit
/-- The exception-monad values of Perennial/Golang/Defn/Exception.lean. -/
def exec_v : val := PairV (LitV (LitString go!"execute")) uval
def ret_v (v : val) : val := PairV (LitV (LitString go!"return")) v

def cmp_lt (signed : Bool) (x y : w64) : Bool :=
  if signed then decide (sint.Z x < sint.Z y) else decide (uint.Z x < uint.Z y)
def cmp_le (signed : Bool) (x y : w64) : Bool :=
  if signed then decide (sint.Z x ≤ sint.Z y) else decide (uint.Z x ≤ uint.Z y)

/-- A valuation gives values to logical variables, pattern variables, and the
return value. -/
structure valuation where
  mkVal ::
  vvar : Nat → val
  vpat : Nat → val
  vret : val

export valuation (mkVal vvar vpat vret)

def upd_pat (V : valuation) (n : Nat) (v : val) : valuation :=
  mkVal (vvar V) (fun m => if m = n then v else vpat V m) (vret V)

/-- Total evaluation; ill-sorted terms evaluate to junk (`uval`). -/
def teval (V : valuation) : term → val
  | TVar n => vvar V n
  | TPat n => vpat V n
  | TResult => vret V
  | TInt w => ival w
  | TBool b => bval b
  | TUnit => uval
  | TNull => lval null
  | TPlus a b =>
      match teval V a, teval V b with
      | LitV (LitInt x), LitV (LitInt y) => ival (x + y)
      | _, _ => uval
  | TMinus a b =>
      match teval V a, teval V b with
      | LitV (LitInt x), LitV (LitInt y) => ival (x - y)
      | _, _ => uval
  | TMul a b =>
      match teval V a, teval V b with
      | LitV (LitInt x), LitV (LitInt y) => ival (x * y)
      | _, _ => uval
  | TNeg a =>
      match teval V a with
      | LitV (LitInt x) => ival (-x)
      | _ => uval
  | TEq a b => bval (decide (teval V a = teval V b))
  | TLt sg a b =>
      match teval V a, teval V b with
      | LitV (LitInt x), LitV (LitInt y) => bval (cmp_lt sg x y)
      | _, _ => uval
  | TLe sg a b =>
      match teval V a, teval V b with
      | LitV (LitInt x), LitV (LitInt y) => bval (cmp_le sg x y)
      | _, _ => uval
  | TNot a =>
      match teval V a with
      | LitV (LitBool b) => bval (!b)
      | _ => uval
  | TIte c a b =>
      match teval V c with
      | LitV (LitBool true) => teval V a
      | LitV (LitBool false) => teval V b
      | _ => uval
  | TExec => exec_v
  | TRet a => ret_v (teval V a)

def has_sort (v : val) : sort → Prop
  | SInt => ∃ w, v = ival w
  | SBool => ∃ b, v = bval b
  | SLoc => ∃ l, v = lval l
  | SUnit => v = uval

/-- `θ` respects the sort table `vars` (indexed by variable number). -/
def vars_sat (θ : Nat → val) (vars : List sort) : Prop :=
  ∀ n s, vars[n]? = some s → has_sort (θ n) s

end semantics

/-! ## The checker's input syntax, mirrored -/


/-! ## Denotation of the input syntax into GooseLang -/

section denote
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

def type_of : ctype → go.GoType
  | CTyInt => go.int
  | CTyInt64 => go.int64
  | CTyUint64 => go.uint64
  | CTyBool => go.bool
  | CTyPtr e => go.GoType.PointerType (type_of e)

def binop_of : cop → GoOperator
  | COAdd => GoPlus | COSub => GoSub | COMul => GoMul
  | COEq => GoEquals | COLt => GoLt | COLe => GoLe | COGt => GoGt | COGe => GoGe
  | CONeg | CONot => GoPlus -- unary operators; unused here

def unop_of : cop → GoUnaryOperator
  | CONeg => GoNeg
  | CONot => GoNot
  | _ => GoPos -- binary operators; unused here

/-- Rocq `go.go_string_to_string`: the GooseLang variable name of a Go name,
one character per byte. -/
def pname (x : GoString) : String := String.ofList (x.map fun b => Char.ofNat b.toNat)

/-- `expr_of e` is the GooseLang expression the checker input `e` stands for.
Each case is the shape Goose emits (compare
Generated/Code/github_com/upamanyus/bootstrap_go/checker/examples.lean). -/
def expr_of : cexpr → Expr
  | CEInt w => Val #w
  | CEBool b => Val #b
  | CEUnit => Val #()
  | CEVar x => Var (pname x)
  -- let: x := e1 in e2  (goose: `Let x e1 e2`)
  | CELet x e1 e2 => App (Rec BAnon (BNamed (pname x)) (expr_of e2)) (expr_of e1)
  -- e1 ;; e2
  | CESeq e1 e2 => App (Rec BAnon BAnon (expr_of e2)) (expr_of e1)
  | CEIf c e1 e2 => If (expr_of c) (expr_of e1) (expr_of e2)
  | CELoad t e => App (Val (GoInstruction (GoLoad (type_of t)))) (expr_of e)
  | CEStore t e1 e2 =>
      App (Val (GoInstruction (GoStore (type_of t)))) (Pair (expr_of e1) (expr_of e2))
  | CEAlloc t e => App (Val (GoInstruction (GoAlloc (type_of t)))) (expr_of e)
  | CEZero t => App (Val (GoInstruction (GoZeroVal (type_of t)))) (Val #())
  | CEBinOp op t e1 e2 =>
      App (Val (GoInstruction (GoOp (binop_of op) (type_of t)))) (Pair (expr_of e1) (expr_of e2))
  | CEUnOp op t e => App (Val (GoInstruction (GoUnOp (unop_of op) (type_of t)))) (expr_of e)
  | CEConvert t1 t2 e =>
      App (Val (GoInstruction (Convert (type_of t1) (type_of t2)))) (expr_of e)
  -- do: e
  | CEDo e => App (Val doExecute) (expr_of e)
  -- return: e
  | CEReturn e => App (Val doReturn) (expr_of e)
  -- e1 ;;; e2  (goose: `exceptionSeq (Lam BAnon e2) e1`)
  | CEExcSeq e1 e2 => App (App (Val exceptionSeq) (Rec BAnon BAnon (expr_of e2))) (expr_of e1)
  | CEExcDo e => App (Val exceptionDo) (expr_of e)

def lams : List GoString → Expr → Expr
  | [], e => e
  | x :: xs, e => Rec BAnon (BNamed (pname x)) (lams xs e)

/-- The function value Goose emits for a Go function: `λ: x1 .. xn, body`, or
`λ: <>, body` for a function without parameters. -/
def func_val (f : cfunc) : val :=
  match f.fparams with
  | [] => RecV BAnon BAnon (expr_of f.fbody)
  | x :: xs => RecV BAnon (BNamed (pname x)) (lams xs (expr_of f.fbody))

end denote

section apply
variable [ext : FfiSyntax]

def apply_vals (f : val) (args : List val) : Expr :=
  args.foldl (fun e v => App e (Val v)) (Val f)

/-- The arguments passed to `f`: the values of logical variables
`0 .. nparams-1`, or a single unit for a parameterless function. -/
def arg_vals (f : cfunc) (θ : Nat → val) : List val :=
  match f.fparams with
  | [] => [uval]
  | _ => (List.range f.fparams.length).map θ

end apply

/-! ## Denotation of assertions, and the representation of the inputs -/

section iprop
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance checker_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker :=
  define_is_pkg_init iprop(True)
instance checker_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.upamanyus.bootstrap_go.checker :=
  build_get_is_pkg_init_wf

def assn_interp (V : valuation) : cassn → IProp GF
  | CAEmp => iprop(True)
  | CASep p q => iprop(assn_interp V p ∗ assn_interp V q)
  | CAOr p q => iprop(assn_interp V p ∨ assn_interp V q)
  | CAExists n s p => iprop(∃ w : val, ⌜has_sort w s⌝ ∗ assn_interp (upd_pat V n w) p)
  | CAPure t => iprop(⌜teval V t = bval true⌝)
  | CAPointsTo l v =>
      iprop(∃ lo : Loc, ⌜teval V l = lval lo⌝ ∗ heapPointsto lo (DFrac.own 1) (teval V v))

/-- Preconditions mention only logical variables; postconditions may also
mention pattern variables (bound inside) and `ret`. -/
def pre_interp (θ : Nat → val) (a : cassn) : IProp GF :=
  assn_interp (mkVal θ (fun _ => uval) uval) a
def post_interp (θ : Nat → val) (v : val) (a : cassn) : IProp GF :=
  assn_interp (mkVal θ (fun _ => uval) v) a

/-! ### Representation of the checker's inputs in the Go heap

The checker's input is a tree of `checker.Type'`, `checker.Expr`,
`checker.Term`, `checker.Assn` and `checker.Func` structs. Nodes are never
mutated by the checker, so they are described with persistent (discarded
fraction) points-to facts. The numeric kind codes below are those of
checker/ast.go, checker/term.go and checker/assn.go. -/

def bool_code (b : Bool) : w64 := if b then W64 1 else W64 0

/-- checker.Op codes -/
def op_code : cop → w64
  | COAdd => W64 1 | COSub => W64 2 | COMul => W64 3 | COEq => W64 4
  | COLt => W64 5 | COLe => W64 6 | COGt => W64 7 | COGe => W64 8
  | CONeg => W64 9 | CONot => W64 10

def is_type (l : Loc) : ctype → IProp GF
  | CTyInt => iprop(l ↦□ checker.Type'.mk (W64 1) null)
  | CTyInt64 => iprop(l ↦□ checker.Type'.mk (W64 2) null)
  | CTyUint64 => iprop(l ↦□ checker.Type'.mk (W64 3) null)
  | CTyBool => iprop(l ↦□ checker.Type'.mk (W64 4) null)
  | CTyPtr e => iprop(∃ le, l ↦□ checker.Type'.mk (W64 5) le ∗ is_type le e)

/-- A term node with kind `k`, number `n` and children `a b c`. -/
def tnode (k n : w64) (a b c : Loc) : checker.Term := checker.Term.mk k n a b c

/-- Variable indices are `Nat` here but a `uint64` in the Go struct, so a
representation predicate only pins down the index modulo 2^64. The
in-range side condition below is what makes `is_term` (and `is_assn`)
injective, and it is trivially true of every tree the frontend builds. -/
def idx_wf (n : Nat) : Prop := uint.nat (W64 n) = n

def is_term (l : Loc) : term → IProp GF
  | TVar n => iprop(⌜idx_wf n⌝ ∗ l ↦□ tnode (W64 1) (W64 n) null null null)
  | TPat n => iprop(⌜idx_wf n⌝ ∗ l ↦□ tnode (W64 2) (W64 n) null null null)
  | TResult => iprop(l ↦□ tnode (W64 3) (W64 0) null null null)
  | TInt w => iprop(l ↦□ tnode (W64 4) w null null null)
  | TBool b => iprop(l ↦□ tnode (W64 5) (bool_code b) null null null)
  | TUnit => iprop(l ↦□ tnode (W64 6) (W64 0) null null null)
  | TNull => iprop(l ↦□ tnode (W64 7) (W64 0) null null null)
  | TPlus a b => iprop(∃ la lb, l ↦□ tnode (W64 8) (W64 0) la lb null ∗ is_term la a ∗ is_term lb b)
  | TMinus a b => iprop(∃ la lb, l ↦□ tnode (W64 9) (W64 0) la lb null ∗ is_term la a ∗ is_term lb b)
  | TMul a b => iprop(∃ la lb, l ↦□ tnode (W64 10) (W64 0) la lb null ∗ is_term la a ∗ is_term lb b)
  | TNeg a => iprop(∃ la, l ↦□ tnode (W64 11) (W64 0) la null null ∗ is_term la a)
  | TEq a b => iprop(∃ la lb, l ↦□ tnode (W64 12) (W64 0) la lb null ∗ is_term la a ∗ is_term lb b)
  | TLt sg a b =>
      iprop(∃ la lb, l ↦□ tnode (if sg then W64 13 else W64 14) (W64 0) la lb null ∗
        is_term la a ∗ is_term lb b)
  | TLe sg a b =>
      iprop(∃ la lb, l ↦□ tnode (if sg then W64 15 else W64 16) (W64 0) la lb null ∗
        is_term la a ∗ is_term lb b)
  | TNot a => iprop(∃ la, l ↦□ tnode (W64 17) (W64 0) la null null ∗ is_term la a)
  | TIte c a b =>
      iprop(∃ lc la lb, l ↦□ tnode (W64 18) (W64 0) lc la lb ∗
        is_term lc c ∗ is_term la a ∗ is_term lb b)
  | TExec => iprop(l ↦□ tnode (W64 19) (W64 0) null null null)
  | TRet a => iprop(∃ la, l ↦□ tnode (W64 20) (W64 0) la null null ∗ is_term la a)

/-- An expression node: kind, name, number, operator, two types, three children. -/
def enode (k : w64) (name : GoString) (n op : w64) (ty ty2 a b c : Loc) : checker.Expr :=
  checker.Expr.mk k name n op ty ty2 a b c
def enode0 (k : w64) (a b c : Loc) : checker.Expr :=
  enode k go!"" (W64 0) (W64 0) null null a b c

def is_expr (l : Loc) : cexpr → IProp GF
  | CEInt w => iprop(l ↦□ enode (W64 1) go!"" w (W64 0) null null null null null)
  | CEBool b => iprop(l ↦□ enode (W64 2) go!"" (bool_code b) (W64 0) null null null null null)
  | CEUnit => iprop(l ↦□ enode0 (W64 3) null null null)
  | CEVar x => iprop(l ↦□ enode (W64 4) x (W64 0) (W64 0) null null null null null)
  | CELet x e1 e2 =>
      iprop(∃ la lb, l ↦□ enode (W64 5) x (W64 0) (W64 0) null null la lb null ∗
        is_expr la e1 ∗ is_expr lb e2)
  | CESeq e1 e2 =>
      iprop(∃ la lb, l ↦□ enode0 (W64 6) la lb null ∗ is_expr la e1 ∗ is_expr lb e2)
  | CEIf c e1 e2 =>
      iprop(∃ lc la lb, l ↦□ enode0 (W64 7) lc la lb ∗
        is_expr lc c ∗ is_expr la e1 ∗ is_expr lb e2)
  | CELoad t e =>
      iprop(∃ lt la, l ↦□ enode (W64 8) go!"" (W64 0) (W64 0) lt null la null null ∗
        is_type lt t ∗ is_expr la e)
  | CEStore t e1 e2 =>
      iprop(∃ lt la lb, l ↦□ enode (W64 9) go!"" (W64 0) (W64 0) lt null la lb null ∗
        is_type lt t ∗ is_expr la e1 ∗ is_expr lb e2)
  | CEAlloc t e =>
      iprop(∃ lt la, l ↦□ enode (W64 10) go!"" (W64 0) (W64 0) lt null la null null ∗
        is_type lt t ∗ is_expr la e)
  | CEZero t =>
      iprop(∃ lt, l ↦□ enode (W64 11) go!"" (W64 0) (W64 0) lt null null null null ∗ is_type lt t)
  | CEBinOp op t e1 e2 =>
      iprop(∃ lt la lb, l ↦□ enode (W64 12) go!"" (W64 0) (op_code op) lt null la lb null ∗
        is_type lt t ∗ is_expr la e1 ∗ is_expr lb e2)
  | CEUnOp op t e =>
      iprop(∃ lt la, l ↦□ enode (W64 13) go!"" (W64 0) (op_code op) lt null la null null ∗
        is_type lt t ∗ is_expr la e)
  | CEConvert t1 t2 e =>
      iprop(∃ lt1 lt2 la, l ↦□ enode (W64 14) go!"" (W64 0) (W64 0) lt1 lt2 la null null ∗
        is_type lt1 t1 ∗ is_type lt2 t2 ∗ is_expr la e)
  | CEDo e => iprop(∃ la, l ↦□ enode0 (W64 15) la null null ∗ is_expr la e)
  | CEReturn e => iprop(∃ la, l ↦□ enode0 (W64 16) la null null ∗ is_expr la e)
  | CEExcSeq e1 e2 =>
      iprop(∃ la lb, l ↦□ enode0 (W64 17) la lb null ∗ is_expr la e1 ∗ is_expr lb e2)
  | CEExcDo e => iprop(∃ la, l ↦□ enode0 (W64 18) la null null ∗ is_expr la e)

/-- An assertion node: kind, L, R, X, Y, Var, Sort. -/
def anode (k : w64) (L R X Y : Loc) (var : w64) (s : w64) : checker.Assn :=
  checker.Assn.mk k L R X Y var s

def is_assn (l : Loc) : cassn → IProp GF
  | CAEmp => iprop(l ↦□ anode (W64 1) null null null null (W64 0) (W64 0))
  | CASep p q =>
      iprop(∃ lp lq, l ↦□ anode (W64 2) lp lq null null (W64 0) (W64 0) ∗
        is_assn lp p ∗ is_assn lq q)
  | CAOr p q =>
      iprop(∃ lp lq, l ↦□ anode (W64 3) lp lq null null (W64 0) (W64 0) ∗
        is_assn lp p ∗ is_assn lq q)
  | CAExists n s p =>
      iprop(∃ lp, ⌜idx_wf n⌝ ∗ l ↦□ anode (W64 4) lp null null null (W64 n) (sort_code s) ∗
        is_assn lp p)
  | CAPure t => iprop(∃ lx, l ↦□ anode (W64 5) null null lx null (W64 0) (W64 0) ∗ is_term lx t)
  | CAPointsTo x y =>
      iprop(∃ lx ly, l ↦□ anode (W64 6) null null lx ly (W64 0) (W64 0) ∗
        is_term lx x ∗ is_term ly y)

def is_func (l : Loc) (f : cfunc) : IProp GF :=
  iprop(∃ (s : GoSlice) (lb : Loc),
    l ↦□ checker.Func.mk s lb ∗ s ↦*□ f.fparams ∗ is_expr lb f.fbody)

def is_sorts (s : GoSlice) (vars : List sort) : IProp GF :=
  iprop(s ↦*□ (vars.map sort_code))

end iprop

/-! ## The meaning of a verified function, independent of the ghost state

`triple_holds f vars pre post` is the Hoare triple of `check_sound`
(soundness.v) for every valuation respecting `vars`, for every FFI, in
every ghost state `HeapGS hlc GF` and under every Go semantics satisfying
`go.Semantics`. Unlike the triple itself, which is a statement about one
particular language and `HeapGS hlc GF`, this is a plain proposition, and it
is what adequacy (new/checker/adequacy.v) delivers from a closed
execution of `checker.Check` that returns `true`: one run of the checker,
in whatever model, establishes the triple in every model. -/
def triple_holds (f : cfunc) (vars : List sort) (pre post : cassn) : Prop :=
  ∀ (ext : FfiSyntax) (ffi : FfiModel) (_ffi_interp : FfiInterp ffi)
    (_ffi_sem : FfiSemantics ext ffi) (_go_gctx : GoGlobalContext)
    (hlc : HasLC) (GF : BundledGFunctors) (_hG : HeapGS hlc GF) (_sem : go.Semantics),
    ∀ θ : Nat → val,
    vars_sat θ vars →
    {{ pre_interp (GF := GF) θ pre }}
      (apply_vals (func_val f) (arg_vals f θ))
    {{ (v : val), RET v; post_interp (GF := GF) θ v post }}

/-! ## Fidelity tests: `func_val` denotes what the Lean goose backend emits

The checker inputs of two of the examples, written by hand from the Goose
output (the same mechanical reading gocheck does), denote exactly
`examples.Double.impl` and `examples.Median3.impl`: `func_val` and `expr_of`
match the shapes of the Lean backend (`Let`, `Lam BAnon`, `exceptionSeq`,
`doExecute`, `doReturn`, `exceptionDo`, `Convert go.untypedBool go.bool`). -/
section fidelity
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

private def double_func : cfunc :=
  mkFunc [go!"x", go!"z"]
  (CEExcDo (CELet go!"z" (CEAlloc (CTyPtr CTyInt) (CEVar go!"z")) (CELet go!"x" (CEAlloc CTyInt (CEVar go!"x")) (CEExcSeq (CELet go!"y" (CEAlloc CTyInt (CEZero CTyInt)) (CELet go!"$r0" (CELoad CTyInt (CEVar go!"x")) (CEExcSeq (CEDo (CEStore CTyInt (CEVar go!"y") (CEVar go!"$r0"))) (CEExcSeq (CEIf (CEConvert CTyBool CTyBool (CEBinOp COEq CTyInt (CELoad CTyInt (CEVar go!"x")) (CEInt (W64 0)))) (CELet go!"$r0" (CEInt (W64 37)) (CEDo (CEStore CTyInt (CEVar go!"y") (CEVar go!"$r0")))) (CEDo CEUnit)) (CELet go!"$r0" (CEBinOp COAdd CTyInt (CELoad CTyInt (CEVar go!"y")) (CELoad CTyInt (CEVar go!"y"))) (CEDo (CEStore CTyInt (CELoad (CTyPtr CTyInt) (CEVar go!"z")) (CEVar go!"$r0")))))))) (CEReturn CEUnit)))))

private def median3_func : cfunc :=
  mkFunc [go!"a", go!"b", go!"c"]
  (CEExcDo (CELet go!"c" (CEAlloc CTyUint64 (CEVar go!"c")) (CELet go!"b" (CEAlloc CTyUint64 (CEVar go!"b")) (CELet go!"a" (CEAlloc CTyUint64 (CEVar go!"a")) (CELet go!"x" (CEAlloc CTyUint64 (CEZero CTyUint64)) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"a")) (CEExcSeq (CEDo (CEStore CTyUint64 (CEVar go!"x") (CEVar go!"$r0"))) (CELet go!"y" (CEAlloc CTyUint64 (CEZero CTyUint64)) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"b")) (CEExcSeq (CEDo (CEStore CTyUint64 (CEVar go!"y") (CEVar go!"$r0"))) (CELet go!"z" (CEAlloc CTyUint64 (CEZero CTyUint64)) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"c")) (CEExcSeq (CEDo (CEStore CTyUint64 (CEVar go!"z") (CEVar go!"$r0"))) (CEExcSeq (CEIf (CEConvert CTyBool CTyBool (CEBinOp COLt CTyUint64 (CELoad CTyUint64 (CEVar go!"y")) (CELoad CTyUint64 (CEVar go!"x")))) (CELet go!"t" (CEAlloc CTyUint64 (CEZero CTyUint64)) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"x")) (CEExcSeq (CEDo (CEStore CTyUint64 (CEVar go!"t") (CEVar go!"$r0"))) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"y")) (CEExcSeq (CEDo (CEStore CTyUint64 (CEVar go!"x") (CEVar go!"$r0"))) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"t")) (CEDo (CEStore CTyUint64 (CEVar go!"y") (CEVar go!"$r0"))))))))) (CEDo CEUnit)) (CEExcSeq (CEIf (CEConvert CTyBool CTyBool (CEBinOp COLt CTyUint64 (CELoad CTyUint64 (CEVar go!"z")) (CELoad CTyUint64 (CEVar go!"y")))) (CELet go!"t" (CEAlloc CTyUint64 (CEZero CTyUint64)) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"y")) (CEExcSeq (CEDo (CEStore CTyUint64 (CEVar go!"t") (CEVar go!"$r0"))) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"z")) (CEExcSeq (CEDo (CEStore CTyUint64 (CEVar go!"y") (CEVar go!"$r0"))) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"t")) (CEDo (CEStore CTyUint64 (CEVar go!"z") (CEVar go!"$r0"))))))))) (CEDo CEUnit)) (CEExcSeq (CEIf (CEConvert CTyBool CTyBool (CEBinOp COLt CTyUint64 (CELoad CTyUint64 (CEVar go!"y")) (CELoad CTyUint64 (CEVar go!"x")))) (CELet go!"t" (CEAlloc CTyUint64 (CEZero CTyUint64)) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"x")) (CEExcSeq (CEDo (CEStore CTyUint64 (CEVar go!"t") (CEVar go!"$r0"))) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"y")) (CEExcSeq (CEDo (CEStore CTyUint64 (CEVar go!"x") (CEVar go!"$r0"))) (CELet go!"$r0" (CELoad CTyUint64 (CEVar go!"t")) (CEDo (CEStore CTyUint64 (CEVar go!"y") (CEVar go!"$r0"))))))))) (CEDo CEUnit)) (CEReturn (CELoad CTyUint64 (CEVar go!"y")))))))))))))))))))

example : func_val double_func = checker.examples.Double.impl := rfl
example : func_val median3_func = checker.examples.Median3.impl := rfl

end fidelity

end Checker
end Perennial
