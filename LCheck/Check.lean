/-
A Lean-native checker.

`lcheck f vars pre post` is the algorithm of `checker.Check` (checker/*.go),
written as Lean functions over the mirrors of the checker's data
(Checkers/Checker/Defs.lean, Interp.lean, Disjunct.lean) instead of as Go.
It imports nothing beyond Lean's core (see LCheck/Syntax.lean), so the
`LCheck` library is precompiled to native code
(`precompileModules`, lakefile.toml). It is proved sound in
Checkers/Native/Sound.lean (`lcheck_sound`: a `true`
answer gives `triple_holds`), so a proof of a triple can run it by
`native_decide` (compiled code) or by `decide` (the kernel), with no Go run in
the trusted base.

It follows the Go code case for case, and reuses the pure mirror functions
the Go proof already states its specifications over (`heap_lookup`,
`heap_update`, `find_cell`, `instantiate_t`, `cond_holds`, `assn_flatten`,
`grow_pats`, `cassn_ws`, ...), so the soundness proof can reuse the semantic
lemmas (`exec_sound_*`, `match_path_sat`, `binders_interp_step`, ...).
Where it differs:

* Failures are `none` (or `false`); there is no `*Failure` diagnostic.
* `TypeSort` cannot fail on a `ctype`, so `exec` drops those checks.
* `matchTerm` is structural: the `TResult` case matches the path's return
  term with a copy of the matcher that rejects `TResult` (`mt_core`), which
  is what the Go recursion does, since a return term has no `TResult`. Leaf
  nodes must be equal as terms, and `TVar`/`TPat` indices below 2^64
  (`tidx_ok`), which is what the Go comparison of the `Num` field means.
* `matchHeap` repeats passes while one makes progress, at most once per
  atom, and then requires every points-to atom resolved; the Go loop counts
  down `remaining` instead.
-/
import LCheck.Fns

namespace Perennial
namespace Checker
namespace Native

/-! ## Symbolic execution (checker/exec.go) -/

/-- Run `k` on every path of `ps`, in order, and concatenate the results;
`none` as soon as one fails. The loops of `execLet`, `execSeq`, ... -/
def bindAll (ps : List spath) (k : spath → Option (List spath)) : Option (List spath) :=
  match ps with
  | [] => some []
  | p :: ps' =>
      match k p, bindAll ps' k with
      | some qs, some rs => some (qs ++ rs)
      | _, _ => none

/-- `exec`: one path per feasible execution of `ce`, in evaluation order. -/
def lexec : cexpr → List (List (BitVec 8) × term) → sstate → Option (List spath)
  | CEInt w, _, st => some [mkPath (TInt w) st]
  | CEBool b, _, st => some [mkPath (TBool b) st]
  | CEUnit, _, st => some [mkPath TUnit st]
  | CEVar x, ρ, st =>
      match env_lookup ρ x with
      | some t => some [mkPath t st]
      | none => none
  | CELet x e1 e2, ρ, st =>
      match lexec e1 ρ st with
      | some ps => bindAll ps (fun p => lexec e2 ((x, pret p) :: ρ) (pst p))
      | none => none
  | CESeq e1 e2, ρ, st =>
      match lexec e1 ρ st with
      | some ps => bindAll ps (fun p => lexec e2 ρ (pst p))
      | none => none
  | CEIf c e1 e2, ρ, st =>
      match lexec c ρ st with
      | some ps => bindAll ps (fun p =>
          if sort_of_vars (svars (pst p)) (pret p) = some SBool then
            match pret p with
            | TBool true => lexec e1 ρ (pst p)
            | TBool false => lexec e2 ρ (pst p)
            | _ =>
                match lexec e1 ρ (st_assume (pst p) (pret p)),
                      lexec e2 ρ (st_assume (pst p) (negate (pret p))) with
                | some qs1, some qs2 => some (qs1 ++ qs2)
                | _, _ => none
          else none)
      | none => none
  | CELoad _ e, ρ, st =>
      match lexec e ρ st with
      | some ps => bindAll ps (fun p =>
          match heap_lookup (sheap (pst p)) (pret p) with
          | some y => some [mkPath y (pst p)]
          | none => none)
      | none => none
  | CEStore _ e1 e2, ρ, st =>
      match lexec e1 ρ st with
      | some ps => bindAll ps (fun p =>
          match lexec e2 ρ (pst p) with
          | some qs => bindAll qs (fun q =>
              match heap_update (sheap (pst q)) (pret p) (pret q) with
              | some H' => some [mkPath TUnit (st_heap (pst q) H')]
              | none => none)
          | none => none)
      | none => none
  | CEAlloc _ e, ρ, st =>
      match lexec e ρ st with
      | some ps => some (ps.map alloc_path)
      | none => none
  | CEZero t, _, st => some [mkPath (ctype_zero t) st]
  | CEBinOp op t e1 e2, ρ, st =>
      match lexec e1 ρ st with
      | some ps => bindAll ps (fun p =>
          match lexec e2 ρ (pst p) with
          | some qs => bindAll qs (fun q =>
              if sort_of_vars (svars (pst q)) (pret p) = some (ctype_sort t) ∧
                 sort_of_vars (svars (pst q)) (pret q) = some (ctype_sort t) then
                match apply_binop op t (pret p) (pret q) with
                | some r => some [mkPath r (pst q)]
                | none => none
              else none)
          | none => none)
      | none => none
  | CEUnOp op t e, ρ, st =>
      match lexec e ρ st with
      | some ps => bindAll ps (fun p =>
          if sort_of_vars (svars (pst p)) (pret p) = some (ctype_sort t) then
            match apply_unop op t (pret p) with
            | some r => some [mkPath r (pst p)]
            | none => none
          else none)
      | none => none
  | CEConvert t1 t2 e, ρ, st => if t1 = t2 then lexec e ρ st else none
  | CEDo e, ρ, st =>
      match lexec e ρ st with
      | some ps => some (ps.map fun p => mkPath TExec (pst p))
      | none => none
  | CEReturn e, ρ, st =>
      match lexec e ρ st with
      | some ps => some (ps.map fun p => mkPath (TRet (pret p)) (pst p))
      | none => none
  | CEExcSeq e1 e2, ρ, st =>
      match lexec e1 ρ st with
      | some ps => bindAll ps (fun p =>
          match pret p with
          | TExec => lexec e2 ρ (pst p)
          | TRet _ => some [p]
          | _ => none)
      | none => none
  | CEExcDo e, ρ, st =>
      match lexec e ρ st with
      | some ps => bindAll ps (fun p =>
          match pret p with
          | TExec => some [mkPath TUnit (pst p)]
          | TRet x => some [mkPath x (pst p)]
          | _ => none)
      | none => none

/-! ## Parsing the postcondition (checker/match.go) -/

/-- `parseDisjunct`'s loop, from the disjunct built so far: peel the `∃`
binders, then flatten the separating conjunction underneath. -/
def parse_from (dj : cdisjunct) : cassn → cdisjunct
  | CAExists k s p =>
      if (d_pat_ok (grow_pats dj k))[k]? = some true then dj_failed (grow_pats dj k)
      else parse_from (bind_pat (grow_pats dj k) k s) p
  | b =>
      match assn_flatten b with
      | some ats => dj_atoms dj ats
      | none => dj_failed dj

def parse_disjunct (a : cassn) : cdisjunct :=
  parse_from (mkDisjunct [] [] [] false) a

/-- `parseDisjuncts`. -/
def parse_disjuncts (post : cassn) : List cdisjunct :=
  (assn_disjuncts post).map fun
    | some a => parse_disjunct a
    | none => mkDisjunct [] [] [] true

/-! ## Matching a path against a disjunct -/

/-- A `TVar`/`TPat` index the Go `Num` field holds exactly. -/
def tidx_ok : term → Bool
  | TVar n | TPat n => decide (n < 2 ^ 64)
  | _ => true

/-- `matchTerm`, with the `TResult` case delegated to `res`. -/
def mt_core (pats : List sort) (pok : List Bool) (PV : List sort)
    (res : term → List (Option term) → Option (List (Option term))) :
    term → term → List (Option term) → Option (List (Option term))
  | TPat n, y, σ =>
      match σ[n]?, pok[n]?, pats[n]? with
      | some none, some true, some s =>
          if sort_of_vars PV y = some s then some (σ.set n (some y)) else none
      | some (some z), some true, _ => if z = y then some σ else none
      | _, _, _ => none
  | TResult, y, σ => res y σ
  | TPlus a b, TPlus a' b', σ =>
      match mt_core pats pok PV res a a' σ with
      | some σ1 => mt_core pats pok PV res b b' σ1
      | none => none
  | TMinus a b, TMinus a' b', σ =>
      match mt_core pats pok PV res a a' σ with
      | some σ1 => mt_core pats pok PV res b b' σ1
      | none => none
  | TMul a b, TMul a' b', σ =>
      match mt_core pats pok PV res a a' σ with
      | some σ1 => mt_core pats pok PV res b b' σ1
      | none => none
  | TEq a b, TEq a' b', σ =>
      match mt_core pats pok PV res a a' σ with
      | some σ1 => mt_core pats pok PV res b b' σ1
      | none => none
  | TLt sg a b, TLt sg' a' b', σ =>
      if sg = sg' then
        match mt_core pats pok PV res a a' σ with
        | some σ1 => mt_core pats pok PV res b b' σ1
        | none => none
      else none
  | TLe sg a b, TLe sg' a' b', σ =>
      if sg = sg' then
        match mt_core pats pok PV res a a' σ with
        | some σ1 => mt_core pats pok PV res b b' σ1
        | none => none
      else none
  | TNeg a, TNeg a', σ => mt_core pats pok PV res a a' σ
  | TNot a, TNot a', σ => mt_core pats pok PV res a a' σ
  | TRet a, TRet a', σ => mt_core pats pok PV res a a' σ
  | TIte c a b, TIte c' a' b', σ =>
      match mt_core pats pok PV res c c' σ with
      | some σ1 =>
          match mt_core pats pok PV res a a' σ1 with
          | some σ2 => mt_core pats pok PV res b b' σ2
          | none => none
      | none => none
  | x, y, σ => if x = y ∧ tidx_ok x = true then some σ else none

/-- `matchTerm`: `ret` (`TResult`) stands for the path's return term `r`. -/
def mt (pats : List sort) (pok : List Bool) (PV : List sort) (r : term) :
    term → term → List (Option term) → Option (List (Option term)) :=
  mt_core pats pok PV (fun y σ => mt_core pats pok PV (fun _ _ => none) r y σ)

/-- Phase 1 state: the substitution, the used cells, the resolved atoms, and
whether the current pass resolved one. -/
structure p1state where
  mkP1 ::
  p1σ : List (Option term)
  p1used : List Bool
  p1done : List Bool
  p1prog : Bool

export p1state (mkP1)

/-- `matchAtom` on the points-to atom `x ↦ v`: `some (false, ..)` when the
location still mentions an unbound pattern variable, `none` on failure. -/
def match_atom (H : List scell) (pats : List sort) (pok : List Bool) (PV : List sort)
    (r : term) (x v : term) (σ : List (Option term)) (used : List Bool) :
    Option (Bool × List (Option term) × List Bool) :=
  match instantiate_t x σ (some r) with
  | none => none
  | some l =>
      if has_pat l then some (false, σ, used)
      else
        match find_cell H used l 0 with
        | none => none
        | some j =>
            match H[j]? with
            | none => none
            | some c =>
                match mt pats pok PV r v (cval c) σ with
                | some σ' => some (true, σ', used.set j true)
                | none => none

/-- `matchPass`, over the atom indices `is`. -/
def match_pass (H : List scell) (atoms : List cassn) (pats : List sort) (pok : List Bool)
    (PV : List sort) (r : term) : List Nat → p1state → Option p1state
  | [], s => some s
  | i :: is, s =>
      match atoms[i]?, s.p1done[i]? with
      | some (CAPointsTo x v), some false =>
          match match_atom H pats pok PV r x v s.p1σ s.p1used with
          | some (false, _, _) => match_pass H atoms pats pok PV r is s
          | some (true, σ', used') =>
              match_pass H atoms pats pok PV r is (mkP1 σ' used' (s.p1done.set i true) true)
          | none => none
      | _, _ => match_pass H atoms pats pok PV r is s

/-- `matchHeap`: passes until every points-to atom is resolved, failing on a
pass that resolves none. -/
def match_heap (H : List scell) (atoms : List cassn) (pats : List sort) (pok : List Bool)
    (PV : List sort) (r : term) : Nat → p1state → Option p1state
  | fuel, s =>
      if undone atoms s.p1done = 0 then some s
      else
        match fuel with
        | 0 => none
        | fuel + 1 =>
            match match_pass H atoms pats pok PV r (List.range atoms.length)
                    (mkP1 s.p1σ s.p1used s.p1done false) with
            | some s' => if s'.p1prog then match_heap H atoms pats pok PV r fuel s' else none
            | none => none

/-- `checkPure`: every pure atom, instantiated, is justified by the path
condition. -/
def pure_check (pc : List term) (atoms : List cassn) (σ : List (Option term)) (r : term) :
    Bool :=
  (List.range atoms.length).all fun i =>
    match atoms[i]? with
    | some (CAPure x) =>
        match instantiate_t x σ (some r) with
        | some y => !has_pat y && cond_holds pc (some y)
        | none => false
    | _ => true

/-- The sort `checkSorts` gives `ret`: that of the path's return term. -/
def ret_sort (p : spath) : sort × Bool :=
  match sort_of_vars (svars (pst p)) (pret p) with
  | some s => (s, true)
  | none => (SInt, false)

/-- `checkSorts`: every atom is well sorted under the declared variables. -/
def sorts_check (vars : List sort) (p : spath) (dj : cdisjunct) : Bool :=
  (d_atoms dj).all fun a =>
    atom_well_sorted (disjunct_env vars dj (ret_sort p).1 (ret_sort p).2) (some a)

/-- `checkDisjunct`. -/
def check_disjunct (vars : List sort) (p : spath) (dj : cdisjunct) : Bool :=
  !d_fail dj && decide ((d_pats dj).length = (d_pat_ok dj).length) &&
  sorts_check vars p dj &&
  match match_heap (sheap (pst p)) (d_atoms dj) (d_pats dj) (d_pat_ok dj) (svars (pst p))
          (pret p) ((d_atoms dj).length + 1)
          (mkP1 (List.replicate (d_pats dj).length none)
            (List.replicate (sheap (pst p)).length false)
            (List.replicate (d_atoms dj).length false) false) with
  | some s => pure_check (spc (pst p)) (d_atoms dj) s.p1σ (pret p)
  | none => false

/-- `Verify`: every path satisfies some disjunct. -/
def lverify (ps : List spath) (vars : List sort) (post : cassn) : Bool :=
  ps.all fun p => (parse_disjuncts post).any fun dj => check_disjunct vars p dj

/-! ## The entry point (checker/check.go) -/

/-- `Analyze`: the strongest postcondition, as a path list. -/
def lanalyze (f : cfunc) (vars : List sort) (pre : cassn) : Option (List spath) :=
  if (fparams f).length ≤ vars.length ∧ cassn_ws (vars_env vars) pre = true then
    lexec (fbody f) (penv (fparams f)) (pre_state vars pre)
  else none

/-- `Check`. -/
def lcheck (f : cfunc) (vars : List sort) (pre post : cassn) : Bool :=
  match lanalyze f vars pre with
  | some ps => lverify ps vars post
  | none => false

end Native
end Checker
end Perennial
