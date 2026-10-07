/-
The table-driven checker (tcheck/) as Lean functions: `ltcheck`.

`ltcheck i = true` establishes `input_holds i` (Checkers/TCheck/Reflect/,
`ltcheck_sound`), the statement the Go checker's soundness axiom
`check_adequate` (Checkers/TCheck/Observe.lean) claims for a `true` answer
of `tcheck.Check` on `ser_input i`. So a proof can run this checker, by
`decide` or `native_decide`, instead of observing a run of the Go one.

It is tcheck/{exec,check,term}.go's algorithm -- interpret core GooseLang,
hand applications of values to the table's rules (first rule, first heap
match, outermost application on the function spine), normalize terms with
the facts, match the postcondition at the end -- with these differences:

* Failures are `none`; there are no diagnostics, and nothing records which
  rules were used.
* The input is not checked for well-formedness up front (`wfInput`).
  Instead each step checks what its soundness needs, where it needs it: a
  value of the code is a closed term of sort `val`; a rule's or fact's
  variables are all bound by matching (else it does not apply); every
  instantiated variable is in range; a rule's result has sort `val`; a
  literal's type is a closed term of sort `type`. On a well-formed input
  these hold whenever the Go checks pass.
* Loops have fuel: normalization by the facts (`norm`, a depth of rewriting)
  and re-reduction of an application's spine (`reduce`).
* `eval` has a flag for the Go `shallow` (evaluate an application's argument
  and function, but not the application itself), so that the recursion is
  structural; `eres` is its result, a value-or-monad result or a spine.
* Terms are compared with `teq`: `tterm` is nested, and Lean derives no
  `DecidableEq` for it.

Nothing here mentions GooseLang or the table's denotation: it imports only
LCheck/TCheck/Syntax.lean, so it is precompiled with the rest of `LCheck`.
-/
import LCheck.TCheck.Syntax

namespace Perennial
namespace TCheck

deriving instance DecidableEq for srt

namespace LC

/-! ## Terms -/

mutual
def teq : tterm → tterm → Bool
  | TVar n, TVar m => n == m
  | TSym n a, TSym m b => n == m && teqs a b
  | TPair a b, TPair c d => teq a c && teq b d
  | TLit t a, TLit u b => teq t u && teqs a b
  | TUnit, TUnit => true
  | _, _ => false
def teqs : List tterm → List tterm → Bool
  | [], [] => true
  | a :: as, b :: bs => teq a b && teqs as bs
  | _, _ => false
end

mutual
/-- The sort of a term whose variables have sorts `vars` (`sortOf`). -/
def sortOf (syms : List symdecl) (vars : List srt) : tterm → Option srt
  | TVar n => vars[n]?
  | TSym n args =>
      match syms[n]? with
      | some d => if sortsOf syms vars args d.sd_args then some d.sd_res else none
      | none => none
  | TPair a b =>
      match sortOf syms vars a, sortOf syms vars b with
      | some SVal, some SVal => some SVal
      | _, _ => none
  | TLit ty es =>
      match sortOf syms vars ty with
      | some SType => if valsOf syms vars es then some SVal else none
      | _ => none
  | TUnit => some SVal
/-- Each term has the corresponding sort. -/
def sortsOf (syms : List symdecl) (vars : List srt) : List tterm → List srt → Bool
  | [], [] => true
  | t :: ts, s :: ss => decide (sortOf syms vars t = some s) && sortsOf syms vars ts ss
  | _, _ => false
/-- Each term has sort `val`. -/
def valsOf (syms : List symdecl) (vars : List srt) : List tterm → Bool
  | [] => true
  | t :: ts => decide (sortOf syms vars t = some SVal) && valsOf syms vars ts
end

/-- A partial binding of a pattern's variables (`matcher.bind`). -/
abbrev Bind := List (Option tterm)

mutual
/-- Match pattern `p` against `t`, extending `b`; a variable binds only to a
term of its sort `psorts[n]`, over the state's variables `vars`. -/
def mterm (syms : List symdecl) (vars psorts : List srt) : tterm → tterm → Bind → Option Bind
  | TVar n, t, b =>
      match b[n]? with
      | some (some u) => if teq u t then some b else none
      | some none =>
          match psorts[n]? with
          | some s => if sortOf syms vars t = some s then some (b.set n (some t)) else none
          | none => none
      | none => none
  | TSym n ps, TSym m ts, b => if n == m then mterms syms vars psorts ps ts b else none
  | TPair p q, TPair t u, b =>
      match mterm syms vars psorts p t b with
      | some b1 => mterm syms vars psorts q u b1
      | none => none
  | TLit p ps, TLit t ts, b =>
      match mterm syms vars psorts p t b with
      | some b1 => mterms syms vars psorts ps ts b1
      | none => none
  | TUnit, TUnit, b => some b
  | _, _, _ => none
def mterms (syms : List symdecl) (vars psorts : List srt) :
    List tterm → List tterm → Bind → Option Bind
  | [], [], b => some b
  | p :: ps, t :: ts, b =>
      match mterm syms vars psorts p t b with
      | some b1 => mterms syms vars psorts ps ts b1
      | none => none
  | _, _, _ => none
end

def mpat (syms : List symdecl) (vars psorts : List srt) : tpat → tpat → Bind → Option Bind
  | PVal p, PVal t, b => mterm syms vars psorts p t b
  | PApp p q, PApp s u, b =>
      match mpat syms vars psorts p s b with
      | some b1 => mpat syms vars psorts q u b1
      | none => none
  | _, _, _ => none

/-- Every variable bound. -/
def allBound : Bind → Option (List tterm)
  | [] => some []
  | some t :: b =>
      match allBound b with
      | some ts => some (t :: ts)
      | none => none
  | none :: _ => none

mutual
/-- Replace variable `n` by `bs[n]`; `none` if some variable is out of range. -/
def inst (bs : List tterm) : tterm → Option tterm
  | TVar n => bs[n]?
  | TSym n args =>
      match insts bs args with
      | some args' => some (TSym n args')
      | none => none
  | TPair a b =>
      match inst bs a, inst bs b with
      | some a', some b' => some (TPair a' b')
      | _, _ => none
  | TLit ty es =>
      match inst bs ty, insts bs es with
      | some ty', some es' => some (TLit ty' es')
      | _, _ => none
  | TUnit => some TUnit
def insts (bs : List tterm) : List tterm → Option (List tterm)
  | [] => some []
  | t :: ts =>
      match inst bs t, insts bs ts with
      | some t', some ts' => some (t' :: ts')
      | _, _ => none
end

/-! ## Normalization by the facts -/

/-- `f` of each term of a list. -/
def mapOpt (f : tterm → Option tterm) : List tterm → Option (List tterm)
  | [] => some []
  | t :: ts =>
      match f t, mapOpt f ts with
      | some t', some ts' => some (t' :: ts')
      | _, _ => none

/-- `f` of each immediate subterm. -/
def mapArgs (f : tterm → Option tterm) : tterm → Option tterm
  | TSym n args =>
      match mapOpt f args with
      | some args' => some (TSym n args')
      | none => none
  | TPair a b =>
      match f a, f b with
      | some a', some b' => some (TPair a' b')
      | _, _ => none
  | TLit ty es =>
      match f ty, mapOpt f es with
      | some ty', some es' => some (TLit ty' es')
      | _, _ => none
  | t => some t

/-- The first fact whose left-hand side matches `t`, binding all its
variables, rewrites `t` to its right-hand side. -/
def tryFacts (syms : List symdecl) (vars : List srt) : List tfact → tterm → Option tterm
  | [], _ => none
  | f :: fs, t =>
      match mterm syms vars f.f_vars f.f_lhs t (List.replicate f.f_vars.length none) with
      | some b =>
          match allBound b with
          | some bs =>
              match inst bs f.f_rhs with
              | some u => some u
              | none => tryFacts syms vars fs t
          | none => tryFacts syms vars fs t
      | none => tryFacts syms vars fs t

/-- Rewrite with the facts, innermost first, to a normal form (`norm`). -/
def norm (syms : List symdecl) (facts : List tfact) (vars : List srt) : Nat → tterm → Option tterm
  | 0, _ => none
  | fuel + 1, t =>
      match mapArgs (norm syms facts vars fuel) t with
      | some t2 =>
          match tryFacts syms vars facts t2 with
          | some t3 => norm syms facts vars fuel t3
          | none => some t2
      | none => none

/-! ## The symbolic state -/

/-- Owned predicate atoms, known equations, and the sorts of the logical
variables. -/
structure lstate where
  mkLState ::
  heap : List tatom
  pure : List (tterm × tterm)
  vars : List srt
export lstate (mkLState)

/-- The read-only part of the input. -/
structure ctx where
  mkCtx ::
  syms : List symdecl
  preds : List preddecl
  rules : List trule
  facts : List tfact
export ctx (mkCtx)

def normFuel : Nat := 1000

def normT (c : ctx) (vars : List srt) (t : tterm) : Option tterm :=
  norm c.syms c.facts vars normFuel t

def pers (c : ctx) (n : Nat) : Bool :=
  match c.preds[n]? with
  | some d => d.pd_pers
  | none => false

/-- The first heap atom of predicate `n` whose arguments match `args`. -/
def findAtom (c : ctx) (vars psorts : List srt) (n : Nat) (args : List tterm) :
    List tatom → Nat → Bind → Option (Bind × Nat)
  | [], _, _ => none
  | APred m hargs :: h, j, b =>
      if n == m then
        match mterms c.syms vars psorts args hargs b with
        | some b1 => some (b1, j)
        | none => findAtom c vars psorts n args h (j + 1) b
      else findAtom c vars psorts n args h (j + 1) b
  | AEq _ _ :: h, j, b => findAtom c vars psorts n args h (j + 1) b

/-- Match the predicate atoms of an assertion against the heap, in order; a
non-persistent atom consumes the heap atom it matches (`matchAtoms`). -/
def matchPreds (c : ctx) (vars psorts : List srt) :
    List tatom → List tatom → Bind → Option (Bind × List tatom)
  | [], h, b => some (b, h)
  | APred n args :: as, h, b =>
      match findAtom c vars psorts n args h 0 b with
      | some (b1, j) => matchPreds c vars psorts as (if pers c n then h else h.eraseIdx j) b1
      | none => none
  | AEq _ _ :: as, h, b => matchPreds c vars psorts as h b

/-- A pure fact: syntactically, after normalization, or because it is known. -/
def holds (c : ctx) (st : lstate) (a b : tterm) : Bool :=
  match normT c st.vars a, normT c st.vars b with
  | some na, some nb =>
      (teq na nb && (sortOf c.syms st.vars na).isSome) ||
      st.pure.any (fun p => (teq p.1 na && teq p.2 nb) || (teq p.1 nb && teq p.2 na))
  | _, _ => false

/-- The equations of an assertion, instantiated by `bs`, hold. -/
def eqsHold (c : ctx) (st : lstate) (bs : List tterm) : List tatom → Bool
  | [] => true
  | APred _ _ :: as => eqsHold c st bs as
  | AEq a b :: as =>
      (match inst bs a, inst bs b with
       | some a', some b' => holds c st a' b'
       | _, _ => false) && eqsHold c st bs as

/-- Add the atoms of an assertion, instantiated by `bs` and normalized. -/
def addAtoms (c : ctx) (vars : List srt) (bs : List tterm) :
    List tatom → List tatom → List (tterm × tterm) → Option (List tatom × List (tterm × tterm))
  | [], h, p => some (h, p)
  | APred n args :: as, h, p =>
      match insts bs args with
      | some args' =>
          match mapOpt (normT c vars) args' with
          | some nargs => addAtoms c vars bs as (h ++ [APred n nargs]) p
          | none => none
      | none => none
  | AEq a b :: as, h, p =>
      match inst bs a, inst bs b with
      | some a', some b' =>
          match normT c vars a', normT c vars b' with
          | some na, some nb => addAtoms c vars bs as h (p ++ [(na, nb)])
          | _, _ => none
      | _, _ => none

/-! ## Rules -/

/-- Apply rule `r` to the application `p` (`applyRule`). -/
def applyRule (c : ctx) (st : lstate) (r : trule) (p : tpat) : Option (tterm × lstate) :=
  match mpat c.syms st.vars r.r_vars r.r_lhs p (List.replicate r.r_vars.length none) with
  | none => none
  | some b1 =>
    match matchPreds c st.vars r.r_vars r.r_pre st.heap b1 with
    | none => none
    | some (b2, h) =>
      match allBound b2 with
      | none => none
      | some bs =>
        if eqsHold c st bs r.r_pre then
          let vars' := st.vars ++ r.r_ex
          let bs' := bs ++ (List.range r.r_ex.length).map (fun i => TVar (st.vars.length + i))
          match addAtoms c vars' bs' r.r_post h st.pure with
          | none => none
          | some (h', p') =>
            match inst bs' r.r_ret with
            | none => none
            | some t0 =>
              match normT c vars' t0 with
              | none => none
              | some t =>
                if sortOf c.syms vars' t = some SVal then some (t, mkLState h' p' vars')
                else none
        else none

/-- The first rule that applies. -/
def tryRules (c : ctx) (st : lstate) (p : tpat) : List trule → Option (tterm × lstate)
  | [] => none
  | r :: rs =>
      match applyRule c st r p with
      | some res => some res
      | none => tryRules c st p rs

/-- The outermost application on the function spine of `s` that a rule
applies to: its depth, and the rule's result. -/
def spineTry (c : ctx) (st : lstate) : tpat → Option (Nat × tterm × lstate)
  | PApp a b =>
      match tryRules c st (PApp a b) c.rules with
      | some (t, st') => some (0, t, st')
      | none =>
          match spineTry c st a with
          | some (d, t, st') => some (d + 1, t, st')
          | none => none
  | PVal _ => none

/-- `s` with the node `d` steps down its function spine replaced by `t`. -/
def replaceSpine (t : tterm) : Nat → tpat → tpat
  | 0, _ => PVal t
  | d + 1, PApp a b => PApp (replaceSpine t d a) b
  | _ + 1, s => s

def reduceFuel : Nat := 1000

/-- Reduce an application of values until a rule applies to the whole of it
(`reduce`). -/
def reduce (c : ctx) : Nat → lstate → tpat → Option (tterm × lstate)
  | 0, _, _ => none
  | fuel + 1, st, s =>
      match spineTry c st s with
      | some (0, t, st') => some (t, st')
      | some (d + 1, t, st') => reduce c fuel st' (replaceSpine t (d + 1) s)
      | none => none

/-! ## Evaluation -/

/-- A value, or one of the two exception-monad values. -/
inductive lres where
  | rVal (t : tterm)
  | rExec
  | rRet (t : tterm)
export lres (rVal rExec rRet)

/-- What `eval` returns: a result, or (in shallow mode) a spine. -/
inductive eres where
  | eR (r : lres)
  | eS (p : tpat)
export eres (eR eS)

abbrev env := List (String × tterm)

def lookup : env → String → Option tterm
  | [], _ => none
  | (y, t) :: e, x => if y == x then some t else lookup e x

/-- Finish a case: the result, or in shallow mode the value as a spine. -/
def fin (sh : Bool) (r : lres) (st : lstate) : Option (eres × lstate) :=
  if sh then
    match r with
    | rVal t => some (eS (PVal t), st)
    | _ => none
  else some (eR r, st)

/-- The elements of a literal: closed values and variables. -/
def litElems (c : ctx) (en : env) : List cexpr → Option (List tterm)
  | [] => some []
  | CVal t :: es =>
      if sortOf c.syms [] t = some SVal then
        match litElems c en es with
        | some ts => some (t :: ts)
        | none => none
      else none
  | CVar x :: es =>
      match lookup en x, litElems c en es with
      | some t, some ts => some (t :: ts)
      | _, _ => none
  | _ :: _ => none

/-- Evaluate `e` (`eval`; with `sh`, `shallow`). -/
def eval (c : ctx) (sh : Bool) (en : env) : cexpr → lstate → Option (eres × lstate)
  | CVal t, st =>
      if sortOf c.syms [] t = some SVal then
        match normT c st.vars t with
        | some t' => fin sh (rVal t') st
        | none => none
      else none
  | CVar x, st =>
      match lookup en x with
      | some t => fin sh (rVal t) st
      | none => none
  | CApp a b, st =>
      match eval c false en b st with
      | some (eR (rVal arg), st1) =>
          match eval c true en a st1 with
          | some (eS sp, st2) =>
              if sh then some (eS (PApp sp (PVal arg)), st2)
              else
                match reduce c reduceFuel st2 (PApp sp (PVal arg)) with
                | some (t, st3) => some (eR (rVal t), st3)
                | none => none
          | _ => none
      | _ => none
  | CPair a b, st =>
      match eval c false en a st with
      | some (eR (rVal ta), st1) =>
          match eval c false en b st1 with
          | some (eR (rVal tb), st2) =>
              match normT c st2.vars (TPair ta tb) with
              | some t => fin sh (rVal t) st2
              | none => none
          | _ => none
      | _ => none
  | CLet x a b, st =>
      match eval c false en a st with
      | some (eR (rVal v), st1) =>
          match eval c false ((x, v) :: en) b st1 with
          | some (eR r, st2) => fin sh r st2
          | _ => none
      | _ => none
  | CSeq a b, st =>
      match eval c false en a st with
      | some (eR (rVal _), st1) =>
          match eval c false en b st1 with
          | some (eR r, st2) => fin sh r st2
          | _ => none
      | _ => none
  | CLit ty es, st =>
      if sortOf c.syms [] ty = some SType then
        match litElems c en es with
        | some ts =>
            match normT c st.vars (TLit ty ts) with
            | some t => fin sh (rVal t) st
            | none => none
        | none => none
      else none
  | CDo a, st =>
      match eval c false en a st with
      | some (eR (rVal _), st1) => fin sh rExec st1
      | _ => none
  | CRet a, st =>
      match eval c false en a st with
      | some (eR (rVal v), st1) => fin sh (rRet v) st1
      | _ => none
  | CXSeq a b, st =>
      match eval c false en a st with
      | some (eR (rRet t), st1) => fin sh (rRet t) st1
      | some (eR rExec, st1) =>
          match eval c false en b st1 with
          | some (eR r, st2) => fin sh r st2
          | _ => none
      | _ => none
  | CXDo a, st =>
      match eval c false en a st with
      | some (eR rExec, st1) => fin sh (rVal TUnit) st1
      | some (eR (rRet t), st1) => fin sh (rVal t) st1
      | _ => none

/-! ## The entry point -/

/-- The postcondition holds of the final state and returned value
(`checkPost`): the specification's own variables are bound to themselves,
its existentials by matching. -/
def checkPost (c : ctx) (sp : tspec) (st : lstate) (t : tterm) : Bool :=
  let nv := sp.sp_vars.length
  let psorts := sp.sp_vars ++ sp.sp_ex
  let b0 : Bind := (List.range nv).map (fun i => some (TVar i)) ++
    List.replicate sp.sp_ex.length none
  match mterm c.syms st.vars psorts sp.sp_ret t b0 with
  | none => false
  | some b1 =>
      match matchPreds c st.vars psorts sp.sp_post st.heap b1 with
      | none => false
      | some (b2, _) =>
          match allBound b2 with
          | some bs => eqsHold c st bs sp.sp_post
          | none => false

/-- The parameters, bound to the arguments, the last parameter first (a later
parameter shadows an earlier one, as in Go). -/
def bindParams : List String → List tterm → env → env
  | x :: xs, t :: ts, en => bindParams xs ts ((x, t) :: en)
  | _, _, en => en

/-- `Check`: `true` only if the specification is established. -/
def ltcheck (i : tinput) : Bool :=
  let c := mkCtx i.in_syms i.in_preds i.in_rules i.in_facts
  let sp := i.in_spec
  let f := i.in_func
  let vars := sp.sp_vars
  let ids := (List.range vars.length).map TVar
  if f.fn_params ≠ [] ∧ f.fn_params.length = sp.sp_args.length then
    match addAtoms c vars ids sp.sp_pre [] [] with
    | none => false
    | some (h, p) =>
      match mapOpt (normT c vars) sp.sp_args with
      | none => false
      | some args =>
        if valsOf c.syms vars args then
          match eval c false (bindParams f.fn_params args []) f.fn_body (mkLState h p vars) with
          | some (eR (rVal t), st) => checkPost c sp st t
          | _ => false
        else false
  else false

end LC

export LC (ltcheck)

end TCheck
end Perennial
