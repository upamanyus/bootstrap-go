/-
The input of the table-driven checker (tcheck/), as Lean data: the mirrors of
tcheck/syntax.go. Moved here from Checkers/TCheck/Syntax.lean (which keeps the
serialization `ser_input`) so that the Lean version of the checker,
`ltcheck` (LCheck/TCheck/Check.lean), is in the precompiled library `LCheck`,
which imports nothing beyond Lean's core (see LCheck/Syntax.lean).
-/

namespace Perennial
namespace TCheck

/-- Sorts: GooseLang values, Go types, and the table's own sorts, which its
denotation maps to Lean types. -/
inductive srt where
  | SVal
  | SType
  | SU (n : Nat)
deriving DecidableEq, Repr
export srt (SVal SType SU)

/-- Terms.  `TLit ty es` is the value `LiteralValueV` of the elements `es`
at type `ty`; `TUnit` is `#()`. -/
inductive tterm where
  | TVar (n : Nat)
  | TSym (n : Nat) (args : List tterm)
  | TPair (a b : tterm)
  | TLit (ty : tterm) (es : List tterm)
  | TUnit
deriving Repr
export tterm (TVar TSym TPair TLit TUnit)

structure symdecl where
  mkSym ::
  sd_args : List srt
  sd_res : srt
export symdecl (mkSym)

structure preddecl where
  mkPred ::
  pd_pers : Bool
  pd_args : List srt
export preddecl (mkPred)

inductive tatom where
  | APred (n : Nat) (args : List tterm)
  | AEq (a b : tterm)
deriving Repr
export tatom (APred AEq)

/-- Expressions whose leaves are values: the left-hand sides of rules. -/
inductive tpat where
  | PVal (t : tterm)
  | PApp (a b : tpat)
deriving Repr
export tpat (PVal PApp)

/-- `∀ vars, {{ pre }} lhs {{ ∃ ex, RET ret; post }}`; the variables of
`ret` and `post` are `vars ++ ex`. -/
structure trule where
  mkRule ::
  r_vars : List srt
  r_lhs : tpat
  r_pre : List tatom
  r_ex : List srt
  r_ret : tterm
  r_post : List tatom
export trule (mkRule)

/-- `∀ vars, lhs = rhs`, used left to right. -/
structure tfact where
  mkFact ::
  f_vars : List srt
  f_lhs : tterm
  f_rhs : tterm
export tfact (mkFact)

/-- The code of a function, as Goose emits it (see `cexpr_den` in
`Denote.lean` for what each node stands for). -/
inductive cexpr where
  | CVal (t : tterm)
  | CVar (x : String)
  | CApp (a b : cexpr)
  | CPair (a b : cexpr)
  | CLet (x : String) (a b : cexpr)
  | CSeq (a b : cexpr)
  | CLit (ty : tterm) (es : List cexpr)
  | CDo (a : cexpr)
  | CRet (a : cexpr)
  | CXSeq (a b : cexpr)
  | CXDo (a : cexpr)
export cexpr (CVal CVar CApp CPair CLet CSeq CLit CDo CRet CXSeq CXDo)

structure cfunc where
  mkFunc ::
  fn_params : List String
  fn_body : cexpr
export cfunc (mkFunc)

/-- `∀ vars, {{ pre }} f args {{ ∃ ex, RET ret; post }}`. -/
structure tspec where
  mkSpec ::
  sp_vars : List srt
  sp_args : List tterm
  sp_pre : List tatom
  sp_ex : List srt
  sp_ret : tterm
  sp_post : List tatom
export tspec (mkSpec)

structure tinput where
  mkInput ::
  in_syms : List symdecl
  in_preds : List preddecl
  in_rules : List trule
  in_facts : List tfact
  in_func : cfunc
  in_spec : tspec
export tinput (mkInput)

end TCheck
end Perennial
