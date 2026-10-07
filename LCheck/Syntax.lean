/-
The checker's data, with no program logic: the mirrors of the Go checker's
input syntax (`term`, `cexpr`, `cassn`, ...) and of its internal state
(`sstate`, `spath`, `cdisjunct`, `sort_env`).

This library (`LCheck`, precompiled; see lakefile.toml) imports nothing
beyond Lean's core, so `lcheck` (LCheck/Check.lean) is compiled to native
code without compiling Iris or Perennial: Lake links precompiled code per
library, and importing even `Perennial.Std.Word` would link (and so compile)
all of the Perennial library and, through it, Iris. Perennial's `w64`,
`GoString` and `W64 0` are therefore written out as what they abbreviate,
`BitVec 64`, `List (BitVec 8)` and `BitVec.ofInt 64 0`; the terms are the
same up to reducible unfolding, so the proofs use them unchanged.
The definitions used to live in Checkers/Checker/{Defs,Interp,TermLemmas,
Disjunct}.lean, which now import this file; names and namespaces are
unchanged.
-/

namespace Perennial
namespace Checker

inductive sort where
  | SInt | SBool | SLoc | SUnit
deriving DecidableEq, Inhabited, Repr

export sort (SInt SBool SLoc SUnit)

/-- Mirrors checker.Term. `TVar` are logical variables (parameters, ghost
variables of the precondition, and variables allocated during execution),
`TPat` are pattern variables bound by `∃` in a postcondition, `TResult` is
the return value `ret`. Signedness of comparisons is a flag here and folded
into the kind on the Go side. -/
inductive term where
  | TVar (n : Nat)
  | TPat (n : Nat)
  | TResult
  | TInt (w : BitVec 64)
  | TBool (b : Bool)
  | TUnit
  | TNull
  | TPlus (a b : term)
  | TMinus (a b : term)
  | TMul (a b : term)
  | TNeg (a : term)
  | TEq (a b : term)
  | TLt (signed : Bool) (a b : term)
  | TLe (signed : Bool) (a b : term)
  | TNot (a : term)
  | TIte (c a b : term)
  | TExec
  | TRet (a : term)
deriving DecidableEq, Inhabited, Repr

export term (TVar TPat TResult TInt TBool TUnit TNull TPlus TMinus TMul TNeg TEq TLt TLe
  TNot TIte TExec TRet)

/-- Mirrors checker.Type. -/
inductive ctype where
  | CTyInt | CTyInt64 | CTyUint64 | CTyBool | CTyPtr (elem : ctype)
deriving DecidableEq, Inhabited, Repr

export ctype (CTyInt CTyInt64 CTyUint64 CTyBool CTyPtr)

/-- Mirrors checker.Op (codes as in checker/ast.go). -/
inductive cop where
  | COAdd | COSub | COMul | COEq | COLt | COLe | COGt | COGe | CONeg | CONot
deriving DecidableEq, Inhabited, Repr

export cop (COAdd COSub COMul COEq COLt COLe COGt COGe CONeg CONot)

/-- Mirrors checker.Expr. -/
inductive cexpr where
  | CEInt (w : BitVec 64)
  | CEBool (b : Bool)
  | CEUnit
  | CEVar (x : List (BitVec 8))
  | CELet (x : List (BitVec 8)) (e1 e2 : cexpr)
  | CESeq (e1 e2 : cexpr)
  | CEIf (c e1 e2 : cexpr)
  | CELoad (t : ctype) (e : cexpr)
  | CEStore (t : ctype) (e1 e2 : cexpr)
  | CEAlloc (t : ctype) (e : cexpr)
  | CEZero (t : ctype)
  | CEBinOp (op : cop) (t : ctype) (e1 e2 : cexpr)
  | CEUnOp (op : cop) (t : ctype) (e : cexpr)
  | CEConvert (from_ to : ctype) (e : cexpr)
  | CEDo (e : cexpr)
  | CEReturn (e : cexpr)
  | CEExcSeq (e1 e2 : cexpr)
  | CEExcDo (e : cexpr)
deriving DecidableEq, Inhabited, Repr

export cexpr (CEInt CEBool CEUnit CEVar CELet CESeq CEIf CELoad CEStore CEAlloc CEZero
  CEBinOp CEUnOp CEConvert CEDo CEReturn CEExcSeq CEExcDo)

/-- Mirrors checker.Func: a curried function value `λ: p0 .. pn, body`. -/
structure cfunc where
  mkFunc ::
  fparams : List (List (BitVec 8))
  fbody : cexpr
deriving DecidableEq, Inhabited, Repr

export cfunc (mkFunc fparams fbody)

/-- Mirrors checker.Assn. -/
inductive cassn where
  | CAEmp
  | CASep (p q : cassn)
  | CAOr (p q : cassn)
  | CAExists (n : Nat) (s : sort) (p : cassn)
  | CAPure (t : term)
  | CAPointsTo (l v : term)
deriving DecidableEq, Inhabited, Repr

export cassn (CAEmp CASep CAOr CAExists CAPure CAPointsTo)

/-- Mirrors `checker.Cell`: a location term and the value term stored there. -/
structure scell where
  mkCell ::
  cloc : term
  cval : term
deriving DecidableEq, Repr

export scell (mkCell cloc cval)

/-- Mirrors `checker.State`. -/
structure sstate where
  mkState ::
  sheap : List scell
  spc : List term
  svars : List sort
deriving DecidableEq, Repr

export sstate (mkState sheap spc svars)

/-- Mirrors `checker.Path`. -/
structure spath where
  mkPath ::
  pret : term
  pst : sstate
deriving DecidableEq, Repr

export spath (mkPath pret pst)

instance scell_inhabited : Inhabited scell := ⟨mkCell TUnit TUnit⟩

instance sstate_inhabited : Inhabited sstate := ⟨mkState [] [] []⟩

instance spath_inhabited : Inhabited spath := ⟨mkPath TUnit default⟩

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

/-- The postcondition matcher's parsed disjunct (checker/match.go). `d_fail`
records only *whether* the disjunct is malformed: the `*Failure` the Go code
stores there is a diagnostic that nothing reads back. -/
structure cdisjunct where
  mkDisjunct ::
  d_pats : List sort
  d_pat_ok : List Bool
  d_atoms : List cassn
  d_fail : Bool

export cdisjunct (mkDisjunct d_pats d_pat_ok d_atoms d_fail)

end Checker
end Perennial
