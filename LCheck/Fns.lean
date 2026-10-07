/-
The pure functions the checker's specifications are stated over, and that
`lcheck` (LCheck/Check.lean) computes with: sorting, the symbolic heap,
pattern instantiation, flattening and parsing of assertions, and the
initial state.

Each mirrors a Go function of checker/ and used to live next to that
function's proof (Checkers/Checker/{TermLemmas,Subst,Steps,ExecSpec,
ExecSoundC,ParseSound,PreSound,MatchSound}.lean and Checkers/Checker/Fn/);
those files now import this one, with names and namespaces unchanged.
-/
import LCheck.Syntax

namespace Perennial
namespace Checker

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

/-- Mirrors `negate` in checker/exec.go: the double negation is cancelled so
that the `else` branch after `if !b` records just `b`. -/
def negate : term → term
  | TNot a => a
  | t => TNot t

/-- The sort environment a disjunct induces on a path: the path's logical
variables, the disjunct's pattern variables, and the sort of the path's
return term. This is the `sortEnv` that `checkDisjunct` builds. -/
def disjunct_env (vars : List sort) (dj : cdisjunct) (rs : sort) (rok : Bool) : sort_env :=
  mkSortEnv vars (d_pats dj) (d_pat_ok dj) rs rok

/-- `envLookup` finds the first binding of `x`. -/
def env_lookup : List (List (BitVec 8) × term) → List (BitVec 8) → Option term
  | [], _ => none
  | (y, t) :: ρ', x => if y = x then some t else env_lookup ρ' x

def ctype_sort : ctype → sort
  | CTyInt | CTyInt64 | CTyUint64 => SInt
  | CTyBool => SBool
  | CTyPtr _ => SLoc

/-- Mirrors `typeSigned`. -/
def ctype_signed : ctype → Bool
  | CTyInt | CTyInt64 => true
  | _ => false

/-- The zero value, mirroring `typeZero`. -/
def ctype_zero : ctype → term
  | CTyInt | CTyInt64 | CTyUint64 => TInt (BitVec.ofInt 64 0)
  | CTyBool => TBool false
  | CTyPtr _ => TNull

def apply_binop (op : cop) (t : ctype) (a b : term) : Option term :=
  match op with
  | COEq => if ctype_sort t = SUnit then none else some (TEq a b)
  | COAdd => if ctype_sort t = SInt then some (TPlus a b) else none
  | COSub => if ctype_sort t = SInt then some (TMinus a b) else none
  | COMul => if ctype_sort t = SInt then some (TMul a b) else none
  | COLt => if ctype_sort t = SInt then some (TLt (ctype_signed t) a b) else none
  | COLe => if ctype_sort t = SInt then some (TLe (ctype_signed t) a b) else none
  | COGt => if ctype_sort t = SInt then some (TLt (ctype_signed t) b a) else none
  | COGe => if ctype_sort t = SInt then some (TLe (ctype_signed t) b a) else none
  | CONeg | CONot => none

/-- Unary minus exists only at the signed integer types: GooseLang has no
`GoUnOp GoNeg` at `go.uint64` (see Perennial/Golang/Defn/Predeclared.lean), which
is why `applyUnOp` asks for `typeSigned`. -/
def apply_unop (op : cop) (t : ctype) (a : term) : Option term :=
  match op with
  | CONeg => if ctype_sort t = SInt then
               (if ctype_signed t then some (TNeg a) else none) else none
  | CONot => if ctype_sort t = SBool then some (TNot a) else none
  | _ => none

/-- The two states `execIf` forks into. -/
def st_assume (sst : sstate) (x : term) : sstate :=
  mkState (sheap sst) (spc sst ++ [x]) (svars sst)

/-- The state `exec` forks to on an allocation. -/
def st_alloc (sst : sstate) (x : term) : sstate :=
  mkState (sheap sst ++ [mkCell (TVar (svars sst).length) x])
          (spc sst)
          (svars sst ++ [SLoc])

/-- The path `execAlloc` produces from a path of its operand. -/
def alloc_path (p : spath) : spath :=
  mkPath (TVar (svars (pst p)).length) (st_alloc (pst p) (pret p))

/-- The state `storeAll` produces: only the heap changes. -/
def st_heap (sst : sstate) (H : List scell) : sstate :=
  mkState H (spc sst) (svars sst)

/-- The Lean mirror: the first cell whose location term is syntactically
`x`. -/
def heap_lookup : List scell → term → Option term
  | [], _ => none
  | c :: H', x => if cloc c = x then some (cval c) else heap_lookup H' x

/-- The Lean mirror. -/
def heap_update : List scell → term → term → Option (List scell)
  | [], _, _ => none
  | c :: H', x, v =>
      if cloc c = x then some (mkCell (cloc c) v :: H')
      else (heap_update H' x v).map (fun r => c :: r)

/-- Mirrors `findCell`: the first index `i` at which the cell is unused and
its location term is `y`, counting from `i`. -/
def find_cell : List scell → List Bool → term → Nat → Option Nat
  | [], _, _, _ => none
  | c :: cs', u, y, i =>
      if (!(u.getD i false) && decide (cloc c = y)) then some i
      else find_cell cs' u y (i + 1)

def tbind1 (f : term → term) (oa : Option term) : Option term :=
  match oa with | some a => some (f a) | none => none

def tbind2 (f : term → term → term) (oa ob : Option term) : Option term :=
  match oa, ob with | some a, some b => some (f a b) | _, _ => none

def tbind3 (f : term → term → term → term) (oa ob oc : Option term) : Option term :=
  match oa, ob, oc with | some a, some b, some c => some (f a b c) | _, _, _ => none

/-- `none` is the nil pointer. A node is rebuilt from its instantiated
children, so it is `none` as soon as one of them is -- see `inst_wf` below
for the side condition that rules that out. -/
def instantiate_t (x : term) (σ : List (Option term)) (r : Option term) : Option term :=
  match x with
  | TPat n => some (match σ[n]? with | some (some y) => y | _ => TPat n)
  | TResult => r
  | TPlus p q => tbind2 TPlus (instantiate_t p σ r) (instantiate_t q σ r)
  | TMinus p q => tbind2 TMinus (instantiate_t p σ r) (instantiate_t q σ r)
  | TMul p q => tbind2 TMul (instantiate_t p σ r) (instantiate_t q σ r)
  | TNeg p => tbind1 TNeg (instantiate_t p σ r)
  | TEq p q => tbind2 TEq (instantiate_t p σ r) (instantiate_t q σ r)
  | TLt sg p q => tbind2 (TLt sg) (instantiate_t p σ r) (instantiate_t q σ r)
  | TLe sg p q => tbind2 (TLe sg) (instantiate_t p σ r) (instantiate_t q σ r)
  | TNot p => tbind1 TNot (instantiate_t p σ r)
  | TIte p q z => tbind3 TIte (instantiate_t p σ r) (instantiate_t q σ r) (instantiate_t z σ r)
  | TRet p => tbind1 TRet (instantiate_t p σ r)
  | _ => some x

/-- Mirrors `hasPat`: `TPat` anywhere below, reached through the `A`, `B` and
`C` fields, which is exactly `term_a`/`term_b`/`term_c`. -/
def has_pat : term → Bool
  | TPat _ => true
  | TPlus p q | TMinus p q | TMul p q | TEq p q | TLt _ p q | TLe _ p q =>
      has_pat p || has_pat q
  | TNeg p | TNot p | TRet p => has_pat p
  | TIte p q r => (has_pat p || has_pat q) || has_pat r
  | _ => false

/-- What the `range` loop decides: `t` is non-nil and is one of the recorded
facts. `termEq c t` is `decide (some c = ox)`, and every cell of `is_cond`
is a real term, so a nil `t` never matches. -/
def cond_mem (pc : List term) : Option term → Bool
  | none => false
  | some y => decide (y ∈ pc)

/-- ... and what it checks afterwards. -/
def cond_refl : term → Bool
  | TEq p q => decide (p = q)
  | TBool b => b
  | _ => false

def cond_holds (pc : List term) : Option term → Bool
  | none => false
  | some y => decide (y ∈ pc) || cond_refl y

/-- Appending to a disjunct's atom list. -/
def dj_atoms (dj : cdisjunct) (ats : List cassn) : cdisjunct :=
  mkDisjunct (d_pats dj) (d_pat_ok dj) (d_atoms dj ++ ats) (d_fail dj)

/-- The mirror: the atoms of a separating conjunction, left to right, or
`none` if the assertion is not a separating conjunction of atoms. -/
def assn_flatten : cassn → Option (List cassn)
  | CAEmp => some []
  | CASep p q =>
      match assn_flatten p with
      | some l1 => match assn_flatten q with
                   | some l2 => some (l1 ++ l2)
                   | none => none
      | none => none
  | CAPure t => some [CAPure t]
  | CAPointsTo l v => some [CAPointsTo l v]
  | CAOr _ _ => none
  | CAExists _ _ _ => none

/-- Pad a list with `x` until index `k` is in range. -/
def pad {A : Type} (xs : List A) (x : A) (k : Nat) : List A :=
  xs ++ List.replicate (k + 1 - xs.length) x

/-- The mirror: both fields are extended, so the length agreement
`sort_env_wf` needs is preserved. -/
def grow_pats (dj : cdisjunct) (k : Nat) : cdisjunct :=
  mkDisjunct (pad (d_pats dj) SInt k) (pad (d_pat_ok dj) false k) (d_atoms dj) (d_fail dj)

def dj_failed (dj : cdisjunct) : cdisjunct :=
  mkDisjunct (d_pats dj) (d_pat_ok dj) (d_atoms dj) true

/-- The binder a parse step records. -/
def bind_pat (dj : cdisjunct) (k : Nat) (s : sort) : cdisjunct :=
  mkDisjunct ((d_pats dj).set k s) ((d_pat_ok dj).set k true) (d_atoms dj) (d_fail dj)

def assn_disjuncts : cassn → List (Option cassn)
  | CAOr p q => assn_disjuncts p ++ assn_disjuncts q
  | x => [some x]

/-- The mirror. `none` is the nil `*Assn`, which is accepted (as `emp`). -/
def cassn_ws (E : sort_env) : cassn → Bool
  | CAEmp => true
  | CASep p q => cassn_ws E p && cassn_ws E q
  | CAPure t => match sort_of E t with | some SBool => true | _ => false
  | CAPointsTo x v =>
      match sort_of E x, sort_of E v with
      | some SLoc, some _ => true
      | _, _ => false
  | _ => false

/-- The mirror. `none` stands for the nil `*Assn`, which is rejected. -/
def atom_well_sorted (E : sort_env) : Option cassn → Bool
  | some (CAPure x) =>
      match sort_of E x with | some SBool => true | _ => false
  | some (CAPointsTo x v) =>
      match sort_of E x, sort_of E v with
      | some SLoc, some _ => true
      | _, _ => false
  | _ => false

def cassn_heap : cassn → List scell
  | CASep p q => cassn_heap p ++ cassn_heap q
  | CAPointsTo lx ly => [mkCell lx ly]
  | _ => []

def cassn_pure : cassn → List term
  | CASep p q => cassn_pure p ++ cassn_pure q
  | CAPure t => [t]
  | _ => []

def penv_from : Nat → List (List (BitVec 8)) → List (List (BitVec 8) × term) → List (List (BitVec 8) × term)
  | _, [], ρ => ρ
  | k, x :: xs', ρ => penv_from (k + 1) xs' ((x, TVar k) :: ρ)

def penv (xs : List (List (BitVec 8))) : List (List (BitVec 8) × term) := penv_from 0 xs []

/-- The initial symbolic state `Analyze` builds. -/
def pre_state (vars : List sort) (pre : cassn) : sstate :=
  mkState (cassn_heap pre) (cassn_pure pre) vars

def is_pts : cassn → Bool
  | CAPointsTo _ _ => true
  | _ => false

def is_pure : cassn → Bool
  | CAPure _ => true
  | _ => false

/-- The number of points-to atoms not resolved yet: `remaining` in
`matchHeap`. -/
def undone : List cassn → List Bool → Nat
  | a :: atoms', d :: done' => (if is_pts a && !d then 1 else 0) + undone atoms' done'
  | _, _ => 0

end Checker
end Perennial
