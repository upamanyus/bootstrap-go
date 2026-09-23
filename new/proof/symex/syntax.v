(** Proof by reflection for symbolic execution of loop-free Goose code: the
    syntax the executor works on, and the executor itself.

    Everything in this file is plain Gallina with no Iris or GooseLang in it,
    so that [vm_compute] can run [run] on a closed term. The meaning of this
    syntax is in [denote.v] and the correctness proof in [sound.v]; [tactic.v]
    puts the three together into [wp_symex].

    The design is the usual one for reflective tactics:

    - a small deep embedding [sexpr] of the fragment Goose emits for straight-line
      Go over [int]/[int64]/[uint64]/[bool]/pointers, together with symbolic
      values [sval] built from numbered *atoms*;
    - the Rocq-level values an expression mentions (Go parameters, literals) are
      collected into an environment by the reifier, and the syntax refers to
      them only by position, so the executor never has to look at a Rocq term;
    - the executor [exec] computes, for every path through the program, the
      symbolic return value, the path condition and the symbolic heap;
    - one soundness theorem, proved once, turns that list of paths into a
      proof of the weakest precondition, leaving one *residual goal* per path. *)
From stdpp Require Import base list strings.
From Stdlib Require Import String.

(** * Types

    The Go types the fragment supports. [go.untyped_bool] is [go.bool], so an
    untyped boolean (the result of a comparison) is a [TyBool]. *)
Inductive sty := TyInt | TyInt64 | TyUint64 | TyBool | TyPtr (t : sty).

Fixpoint sty_eqb (t1 t2 : sty) : bool :=
  match t1, t2 with
  | TyInt, TyInt | TyInt64, TyInt64 | TyUint64, TyUint64 | TyBool, TyBool => true
  | TyPtr a, TyPtr b => sty_eqb a b
  | _, _ => false
  end.

Lemma sty_eqb_eq t1 t2 : sty_eqb t1 t2 = true → t1 = t2.
Proof.
  revert t2. induction t1; destruct t2; simpl; try done.
  intros H. by rewrite (IHt1 _ H).
Qed.

(** What kind of Gallina value a Go value of the type is. *)
Inductive ssort := SortW | SortB | SortL.

Definition sty_sort (t : sty) : ssort :=
  match t with
  | TyInt | TyInt64 | TyUint64 => SortW
  | TyBool => SortB
  | TyPtr _ => SortL
  end.

Definition sty_signed (t : sty) : bool :=
  match t with TyInt | TyInt64 => true | _ => false end.

(** * Symbolic values

    Words and booleans are terms over atoms, which index the environment's
    list of words or booleans. Locations are atoms too; the location
    environment grows by one fresh atom per allocation. *)
Inductive wterm :=
| WAtom (n : nat)
| WZero
| WAdd (a b : wterm)
| WSub (a b : wterm)
| WMul (a b : wterm)
| WNeg (a : wterm).

Inductive lterm := LAtom (n : nat) | LNull.

Inductive bterm :=
| BAtom (n : nat)
| BLit (b : bool)
| BNot (a : bterm)
| BEqW (a b : wterm)
| BEqB (a b : bterm)
| BLt (signed : bool) (a b : wterm)
| BLe (signed : bool) (a b : wterm).

(** [VExec] and [VRet v] are the two values of Goose's exception monad,
    [execute_val] and [return_val v]. *)
Inductive sval :=
| VW (t : wterm)
| VB (t : bterm)
| VL (l : lterm)
| VUnit
| VExec
| VRet (v : sval).

Definition sval_sort (v : sval) : option ssort :=
  match v with
  | VW _ => Some SortW
  | VB _ => Some SortB
  | VL _ => Some SortL
  | _ => None
  end.

Definition ssort_eqb (s1 s2 : ssort) : bool :=
  match s1, s2 with
  | SortW, SortW | SortB, SortB | SortL, SortL => true
  | _, _ => false
  end.

(** A value of the right shape to be stored at a Go type. *)
Definition sort_ok (t : sty) (v : sval) : bool :=
  match sval_sort v with
  | Some s => ssort_eqb (sty_sort t) s
  | None => false
  end.

Definition sty_zero (t : sty) : sval :=
  match sty_sort t with
  | SortW => VW WZero
  | SortB => VB (BLit false)
  | SortL => VL LNull
  end.

(** * Expressions

    One constructor per shape Goose emits; the comment on each is the
    GooseLang it denotes (see [eden] in denote.v). *)
Inductive sbinop := OPlus | OSub | OMul | OEq | OLt | OLe | OGt | OGe.
Inductive sunop := ONeg | ONot.

Inductive sexpr :=
| EVal (v : sval)                          (* Val v *)
| EVar (x : string)                        (* Var x *)
| ELet (x : string) (e1 e2 : sexpr)        (* let: x := e1 in e2 *)
| EIf (c e1 e2 : sexpr)                    (* if: c then e1 else e2 *)
| EAlloc (t : sty) (e : sexpr)             (* GoAlloc t e *)
| EZero (t : sty)                          (* GoZeroVal t #() *)
| ELoad (t : sty) (e : sexpr)              (* ![t] e *)
| EStore (t : sty) (e1 e2 : sexpr)         (* e1 <-[t] e2 *)
| EBinOp (op : sbinop) (t : sty) (e1 e2 : sexpr)
| EUnOp (op : sunop) (t : sty) (e : sexpr)
| EConvert (t1 t2 : sty) (e : sexpr)       (* Convert t1 t2 e *)
| EDo (e : sexpr)                          (* do: e *)
| EReturn (e : sexpr)                      (* return: e *)
| EExcSeq (e1 e2 : sexpr)                  (* e1 ;;; e2 *)
| EExcDo (e : sexpr).                      (* exception_do e *)

(** Substitution of a value for a variable, following GooseLang's [subst]:
    a [let] binding the same name shadows it. *)
Fixpoint ssubst (x : string) (v : sval) (e : sexpr) : sexpr :=
  match e with
  | EVal _ | EZero _ => e
  | EVar y => if String.eqb x y then EVal v else e
  | ELet y e1 e2 =>
      ELet y (ssubst x v e1) (if String.eqb x y then e2 else ssubst x v e2)
  | EIf c e1 e2 => EIf (ssubst x v c) (ssubst x v e1) (ssubst x v e2)
  | EAlloc t e => EAlloc t (ssubst x v e)
  | ELoad t e => ELoad t (ssubst x v e)
  | EStore t e1 e2 => EStore t (ssubst x v e1) (ssubst x v e2)
  | EBinOp op t e1 e2 => EBinOp op t (ssubst x v e1) (ssubst x v e2)
  | EUnOp op t e => EUnOp op t (ssubst x v e)
  | EConvert t1 t2 e => EConvert t1 t2 (ssubst x v e)
  | EDo e => EDo (ssubst x v e)
  | EReturn e => EReturn (ssubst x v e)
  | EExcSeq e1 e2 => EExcSeq (ssubst x v e1) (ssubst x v e2)
  | EExcDo e => EExcDo (ssubst x v e)
  end.

Fixpoint ssize (e : sexpr) : nat :=
  match e with
  | EVal _ | EVar _ | EZero _ => 1
  | ELet _ e1 e2 | EStore _ e1 e2 | EBinOp _ _ e1 e2 | EExcSeq e1 e2 =>
      S (ssize e1 + ssize e2)
  | EIf c e1 e2 => S (ssize c + ssize e1 + ssize e2)
  | EAlloc _ e | ELoad _ e | EUnOp _ _ e | EConvert _ _ e | EDo e | EReturn e
  | EExcDo e => S (ssize e)
  end.

(** * Symbolic states and the executor *)

(** A heap cell: a location atom owned with the given contents. *)
Definition scell : Type := nat * sval.

Record sstate := mkState {
  s_heap : list scell;
  s_pc : list bterm;       (* each term is true on this path *)
  s_nlocs : nat;           (* number of location atoms in scope *)
}.

(** One result of the execution: the value and the final state. *)
Definition spath : Type := sval * sstate.

Fixpoint hlookup (n : nat) (h : list scell) : option sval :=
  match h with
  | [] => None
  | (m, v) :: h => if Nat.eqb n m then Some v else hlookup n h
  end.

(** A store replaces the first cell for the location; the old contents must
    have the type's shape too, since the typed store rule needs a points-to
    at that type. *)
Fixpoint hupdate (t : sty) (n : nat) (w : sval) (h : list scell) : option (list scell) :=
  match h with
  | [] => None
  | (m, v) :: h =>
      if Nat.eqb n m then (if sort_ok t v then Some ((m, w) :: h) else None)
      else (λ h', (m, v) :: h') <$> hupdate t n w h
  end.

Definition st_assume (s : sstate) (b : bterm) : sstate :=
  mkState (s_heap s) (b :: s_pc s) (s_nlocs s).

Definition st_alloc (s : sstate) (v : sval) : sstate :=
  mkState ((s_nlocs s, v) :: s_heap s) (s_pc s) (S (s_nlocs s)).

Definition st_heap (s : sstate) (h : list scell) : sstate :=
  mkState h (s_pc s) (s_nlocs s).

Definition sbinop_eval (op : sbinop) (t : sty) (v1 v2 : sval) : option sval :=
  match op, sty_sort t, v1, v2 with
  | OPlus, SortW, VW a, VW b => Some (VW (WAdd a b))
  | OSub, SortW, VW a, VW b => Some (VW (WSub a b))
  | OMul, SortW, VW a, VW b => Some (VW (WMul a b))
  | OEq, SortW, VW a, VW b => Some (VB (BEqW a b))
  | OEq, SortB, VB a, VB b => Some (VB (BEqB a b))
  | OLt, SortW, VW a, VW b => Some (VB (BLt (sty_signed t) a b))
  | OLe, SortW, VW a, VW b => Some (VB (BLe (sty_signed t) a b))
  | OGt, SortW, VW a, VW b => Some (VB (BLt (sty_signed t) b a))
  | OGe, SortW, VW a, VW b => Some (VB (BLe (sty_signed t) b a))
  | _, _, _, _ => None
  end.

(** Unary minus exists only at the signed types: GooseLang has no [GoNeg] at
    [uint64]. *)
Definition sunop_eval (op : sunop) (t : sty) (v : sval) : option sval :=
  match op, sty_sort t, v with
  | ONeg, SortW, VW a => if sty_signed t then Some (VW (WNeg a)) else None
  | ONot, SortB, VB a => Some (VB (BNot a))
  | _, _, _ => None
  end.

Definition cont : Type := sval → sstate → option (list spath).

(** The executor, in continuation-passing style: [exec n e s k] runs [e] from
    [s] and hands each resulting value and state to [k]; the paths of an [if]
    are concatenated. [None] means the executor could not show the program
    safe (a load from a location it does not own, an operator at the wrong
    sort, a free variable, ...). The fuel [n] bounds the nesting depth, which
    [ssubst] does not change; [run] passes the size of the program. *)
Fixpoint exec (n : nat) (e : sexpr) (s : sstate) (k : cont) : option (list spath) :=
  match n with
  | 0 => None
  | S n =>
  match e with
  | EVal v => k v s
  | EVar _ => None
  | ELet x e1 e2 => exec n e1 s (λ v s', exec n (ssubst x v e2) s' k)
  | EIf c e1 e2 =>
      exec n c s (λ v s',
        match v with
        | VB b =>
            r1 ← exec n e1 (st_assume s' b) k;
            r2 ← exec n e2 (st_assume s' (BNot b)) k;
            Some (r1 ++ r2)
        | _ => None
        end)
  | EAlloc t e =>
      exec n e s (λ v s',
        if sort_ok t v then k (VL (LAtom (s_nlocs s'))) (st_alloc s' v) else None)
  | EZero t => k (sty_zero t) s
  | ELoad t e =>
      exec n e s (λ v s',
        match v with
        | VL (LAtom m) =>
            match hlookup m (s_heap s') with
            | Some w => if sort_ok t w then k w s' else None
            | None => None
            end
        | _ => None
        end)
  | EStore t e1 e2 =>
      exec n e1 s (λ v1 s1,
        exec n e2 s1 (λ v2 s2,
          match v1 with
          | VL (LAtom m) =>
              if sort_ok t v2 then
                match hupdate t m v2 (s_heap s2) with
                | Some h => k VUnit (st_heap s2 h)
                | None => None
                end
              else None
          | _ => None
          end))
  | EBinOp op t e1 e2 =>
      exec n e1 s (λ v1 s1,
        exec n e2 s1 (λ v2 s2,
          match sbinop_eval op t v1 v2 with
          | Some v => k v s2
          | None => None
          end))
  | EUnOp op t e =>
      exec n e s (λ v s',
        match sunop_eval op t v with
        | Some w => k w s'
        | None => None
        end)
  | EConvert t1 t2 e =>
      if sty_eqb t1 t2 then exec n e s k else None
  | EDo e => exec n e s (λ _ s', k VExec s')
  | EReturn e => exec n e s (λ v s', k (VRet v) s')
  | EExcSeq e1 e2 =>
      exec n e1 s (λ v s',
        match v with
        | VExec => exec n e2 s' k
        | VRet _ => k v s'
        | _ => None
        end)
  | EExcDo e =>
      exec n e s (λ v s',
        match v with
        | VExec => k VUnit s'
        | VRet w => k w s'
        | _ => None
        end)
  end
  end.

Definition init_state (h : list scell) (nlocs : nat) : sstate := mkState h [] nlocs.

(** * The cells a path hands back

    A function allocates a cell for every parameter and local variable, and
    those cells are still in the final heap. Nothing the caller can name
    points to them, so the residual goal drops every cell that is not
    reachable from the caller's own locations (the atoms below [n0]) or from
    the returned value. Dropping resources is sound because the logic is
    affine; it only makes the residual goals smaller. *)
Fixpoint sval_locs (v : sval) : list nat :=
  match v with
  | VL (LAtom n) => [n]
  | VRet v => sval_locs v
  | _ => []
  end.

Definition mem_nat (n : nat) (l : list nat) : bool := existsb (Nat.eqb n) l.

Fixpoint reach (fuel : nat) (h : list scell) (acc : list nat) : list nat :=
  match fuel with
  | 0 => acc
  | S fuel =>
      reach fuel h (acc ++ List.concat (List.map (λ c, if mem_nat c.1 acc then sval_locs c.2 else []) h))
  end.

Definition kept_cells (n0 : nat) (v : sval) (h : list scell) : list scell :=
  let r := reach (List.length h) h (seq 0 n0 ++ sval_locs v) in
  List.filter (λ c, mem_nat c.1 r) h.

Definition run (e : sexpr) (h : list scell) (nlocs : nat) : option (list spath) :=
  exec (ssize e) e (init_state h nlocs)
    (λ v s, Some [(v, st_heap s (kept_cells nlocs v (s_heap s)))]).
