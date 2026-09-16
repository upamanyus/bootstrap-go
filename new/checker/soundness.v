(** Statement of soundness for the Go symbolic-execution checker in checker/.

    The checker (checker/*.go, translated by Goose into
    new/code/github_com/mit_pdos/perennial/checker.v) is NOT verified. This file
    only *states* what a [true] answer of [checker.Check] means, as [Axiom
    check_sound] at the end. Everything before the axiom is a definition needed
    to state it:

    - the meaning of the checker's symbolic terms ([teval]) and sorts;
    - the checker's input syntax mirrored as Gallina inductives ([ctype],
      [cexpr], [cfunc], [cassn]) together with its denotation into real
      GooseLang ([type_of], [expr_of], [func_val]) and into Iris assertions
      ([assn_interp]);
    - representation predicates ([is_type], [is_expr], ...) describing how an
      input tree is laid out in the Go heap, in terms of the Goosed struct types.

    Kind codes used in the representation predicates must agree with the
    constants in checker/ast.go, checker/term.go and checker/assn.go.

    Trust boundary of the whole pipeline: the GooseLang semantics, this axiom,
    and the unverified frontend (gocheck/) that produces the checker's input
    from Go source. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.generatedproof.github_com.mit_pdos.perennial Require Import checker.

Set Default Proof Using "Type".

(** * Sorts and symbolic terms *)

Inductive sort := SInt | SBool | SLoc | SUnit.

(* Codes as in checker/term.go. *)
Definition sort_code (s : sort) : w64 :=
  match s with SInt => W64 0 | SBool => W64 1 | SLoc => W64 2 | SUnit => W64 3 end.

(** Mirrors checker.Term. [TVar] are logical variables (parameters, ghost
    variables of the precondition, and variables allocated during execution),
    [TPat] are pattern variables bound by [∃] in a postcondition, [TResult] is
    the return value [ret]. Signedness of comparisons is a flag here and folded
    into the kind on the Go side. *)
Inductive term :=
| TVar (n : nat)
| TPat (n : nat)
| TResult
| TInt (w : w64)
| TBool (b : bool)
| TUnit
| TNull
| TPlus (a b : term)
| TMinus (a b : term)
| TMul (a b : term)
| TNeg (a : term)
| TEq (a b : term)
| TLt (signed : bool) (a b : term)
| TLe (signed : bool) (a b : term)
| TNot (a : term)
| TIte (c a b : term)
| TExec
| TRet (a : term).

Section semantics.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) checker := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) checker := build_get_is_pkg_init_wf.

(** Concrete GooseLang values. Under [go.Semantics] these are [#w], [#b], [#l],
    [#()] (see [into_val_unfold]); the concrete constructors are used so that
    [teval] can pattern match. *)
Definition ival (w : w64) : val := LitV (LitInt w).
Definition bval (b : bool) : val := LitV (LitBool b).
Definition lval (l : loc) : val := LitV (LitLoc l).
Definition uval : val := LitV LitUnit.
(* The exception-monad values of new/golang/defn/exception.v. *)
Definition exec_v : val := PairV (LitV (LitString "execute"%go)) uval.
Definition ret_v (v : val) : val := PairV (LitV (LitString "return"%go)) v.

Definition cmp_lt (signed : bool) (x y : w64) : bool :=
  if signed then bool_decide (sint.Z x < sint.Z y) else bool_decide (uint.Z x < uint.Z y).
Definition cmp_le (signed : bool) (x y : w64) : bool :=
  if signed then bool_decide (sint.Z x ≤ sint.Z y) else bool_decide (uint.Z x ≤ uint.Z y).

(** A valuation gives values to logical variables, pattern variables, and the
    return value. *)
Record valuation := mkVal {
  vvar : nat → val;
  vpat : nat → val;
  vret : val;
}.

Definition upd_pat (V : valuation) (n : nat) (v : val) : valuation :=
  mkVal (vvar V) (λ m, if decide (m = n) then v else vpat V m) (vret V).

(** Total evaluation; ill-sorted terms evaluate to junk ([uval]). *)
Fixpoint teval (V : valuation) (t : term) : val :=
  match t with
  | TVar n => vvar V n
  | TPat n => vpat V n
  | TResult => vret V
  | TInt w => ival w
  | TBool b => bval b
  | TUnit => uval
  | TNull => lval null
  | TPlus a b =>
      match teval V a, teval V b with
      | LitV (LitInt x), LitV (LitInt y) => ival (word.add x y)
      | _, _ => uval
      end
  | TMinus a b =>
      match teval V a, teval V b with
      | LitV (LitInt x), LitV (LitInt y) => ival (word.sub x y)
      | _, _ => uval
      end
  | TMul a b =>
      match teval V a, teval V b with
      | LitV (LitInt x), LitV (LitInt y) => ival (word.mul x y)
      | _, _ => uval
      end
  | TNeg a =>
      match teval V a with
      | LitV (LitInt x) => ival (word.opp x)
      | _ => uval
      end
  | TEq a b => bval (bool_decide (teval V a = teval V b))
  | TLt sg a b =>
      match teval V a, teval V b with
      | LitV (LitInt x), LitV (LitInt y) => bval (cmp_lt sg x y)
      | _, _ => uval
      end
  | TLe sg a b =>
      match teval V a, teval V b with
      | LitV (LitInt x), LitV (LitInt y) => bval (cmp_le sg x y)
      | _, _ => uval
      end
  | TNot a =>
      match teval V a with
      | LitV (LitBool b) => bval (negb b)
      | _ => uval
      end
  | TIte c a b =>
      match teval V c with
      | LitV (LitBool true) => teval V a
      | LitV (LitBool false) => teval V b
      | _ => uval
      end
  | TExec => exec_v
  | TRet a => ret_v (teval V a)
  end.

Definition has_sort (v : val) (s : sort) : Prop :=
  match s with
  | SInt => ∃ w, v = ival w
  | SBool => ∃ b, v = bval b
  | SLoc => ∃ l, v = lval l
  | SUnit => v = uval
  end.

(** [θ] respects the sort table [vars] (indexed by variable number). *)
Definition vars_sat (θ : nat → val) (vars : list sort) : Prop :=
  ∀ n s, vars !! n = Some s → has_sort (θ n) s.

(** * The checker's input syntax, mirrored *)

(** Mirrors checker.Type. *)
Inductive ctype := CTyInt | CTyInt64 | CTyUint64 | CTyBool | CTyPtr (elem : ctype).

(** Mirrors checker.Op (codes as in checker/ast.go). *)
Inductive cop := COAdd | COSub | COMul | COEq | COLt | COLe | COGt | COGe | CONeg | CONot.

(** Mirrors checker.Expr. *)
Inductive cexpr :=
| CEInt (w : w64)
| CEBool (b : bool)
| CEUnit
| CEVar (x : go_string)
| CELet (x : go_string) (e1 e2 : cexpr)
| CESeq (e1 e2 : cexpr)
| CEIf (c e1 e2 : cexpr)
| CELoad (t : ctype) (e : cexpr)
| CEStore (t : ctype) (e1 e2 : cexpr)
| CEAlloc (t : ctype) (e : cexpr)
| CEZero (t : ctype)
| CEBinOp (op : cop) (t : ctype) (e1 e2 : cexpr)
| CEUnOp (op : cop) (t : ctype) (e : cexpr)
| CEConvert (from to : ctype) (e : cexpr)
| CEDo (e : cexpr)
| CEReturn (e : cexpr)
| CEExcSeq (e1 e2 : cexpr)
| CEExcDo (e : cexpr).

(** Mirrors checker.Func: a curried function value [λ: p0 .. pn, body]. *)
Record cfunc := mkFunc { fparams : list go_string; fbody : cexpr }.

(** Mirrors checker.Assn. *)
Inductive cassn :=
| CAEmp
| CASep (p q : cassn)
| CAOr (p q : cassn)
| CAExists (n : nat) (s : sort) (p : cassn)
| CAPure (t : term)
| CAPointsTo (l v : term).

(** * Denotation of the input syntax into GooseLang *)

Fixpoint type_of (t : ctype) : go.type :=
  match t with
  | CTyInt => go.int
  | CTyInt64 => go.int64
  | CTyUint64 => go.uint64
  | CTyBool => go.bool
  | CTyPtr e => go.PointerType (type_of e)
  end.

Definition binop_of (op : cop) : go_operator :=
  match op with
  | COAdd => GoPlus | COSub => GoSub | COMul => GoMul
  | COEq => GoEquals | COLt => GoLt | COLe => GoLe | COGt => GoGt | COGe => GoGe
  | CONeg | CONot => GoPlus (* unary operators; unused here *)
  end.

Definition unop_of (op : cop) : go_unary_operator :=
  match op with
  | CONeg => GoNeg
  | CONot => GoNot
  | _ => GoPos (* binary operators; unused here *)
  end.

(** [expr_of e] is the GooseLang expression the checker input [e] stands for.
    Each case is the shape Goose emits (compare
    new/code/github_com/mit_pdos/perennial/checker/examples.v). *)
Fixpoint expr_of (e : cexpr) : expr :=
  match e with
  | CEInt w => Val #w
  | CEBool b => Val #b
  | CEUnit => Val #()
  | CEVar x => Var (go.go_string_to_string x)
  (* let: x := e1 in e2 *)
  | CELet x e1 e2 => App (Rec BAnon (BNamed (go.go_string_to_string x)) (expr_of e2)) (expr_of e1)
  (* e1 ;; e2 *)
  | CESeq e1 e2 => App (Rec BAnon BAnon (expr_of e2)) (expr_of e1)
  | CEIf c e1 e2 => If (expr_of c) (expr_of e1) (expr_of e2)
  | CELoad t e => App (Val (GoInstruction (GoLoad (type_of t)))) (expr_of e)
  | CEStore t e1 e2 => App (Val (GoInstruction (GoStore (type_of t)))) (Pair (expr_of e1) (expr_of e2))
  | CEAlloc t e => App (Val (GoInstruction (GoAlloc (type_of t)))) (expr_of e)
  | CEZero t => App (Val (GoInstruction (GoZeroVal (type_of t)))) (Val #())
  | CEBinOp op t e1 e2 =>
      App (Val (GoInstruction (GoOp (binop_of op) (type_of t)))) (Pair (expr_of e1) (expr_of e2))
  | CEUnOp op t e => App (Val (GoInstruction (GoUnOp (unop_of op) (type_of t)))) (expr_of e)
  | CEConvert t1 t2 e => App (Val (GoInstruction (Convert (type_of t1) (type_of t2)))) (expr_of e)
  | CEDo e => (do: expr_of e)%E
  | CEReturn e => (return: expr_of e)%E
  | CEExcSeq e1 e2 => (expr_of e1 ;;; expr_of e2)%E
  | CEExcDo e => App (Val exception_do) (expr_of e)
  end.

Fixpoint lams (xs : list go_string) (e : expr) : expr :=
  match xs with
  | [] => e
  | x :: xs => Lam (BNamed (go.go_string_to_string x)) (lams xs e)
  end.

(** The function value Goose emits for a Go function: [λ: x1 .. xn, body], or
    [λ: <>, body] for a function without parameters. *)
Definition func_val (f : cfunc) : val :=
  match f.(fparams) with
  | [] => LamV BAnon (expr_of f.(fbody))
  | x :: xs => LamV (BNamed (go.go_string_to_string x)) (lams xs (expr_of f.(fbody)))
  end.

Definition apply_vals (f : val) (args : list val) : expr :=
  foldl (λ e v, App e (Val v)) (Val f) args.

(** The arguments passed to [f]: the values of logical variables
    [0 .. nparams-1], or a single unit for a parameterless function. *)
Definition arg_vals (f : cfunc) (θ : nat → val) : list val :=
  match f.(fparams) with
  | [] => [uval]
  | _ => θ <$> seq 0 (length f.(fparams))
  end.

(** * Denotation of assertions *)

Fixpoint assn_interp (V : valuation) (a : cassn) : iProp Σ :=
  match a with
  | CAEmp => True
  | CASep p q => assn_interp V p ∗ assn_interp V q
  | CAOr p q => assn_interp V p ∨ assn_interp V q
  | CAExists n s p => ∃ w : val, ⌜has_sort w s⌝ ∗ assn_interp (upd_pat V n w) p
  | CAPure t => ⌜teval V t = bval true⌝
  | CAPointsTo l v => ∃ lo : loc, ⌜teval V l = lval lo⌝ ∗ heap_pointsto lo (DfracOwn 1) (teval V v)
  end%I.

(** Preconditions mention only logical variables; postconditions may also
    mention pattern variables (bound inside) and [ret]. *)
Definition pre_interp (θ : nat → val) (a : cassn) : iProp Σ :=
  assn_interp (mkVal θ (λ _, uval) uval) a.
Definition post_interp (θ : nat → val) (v : val) (a : cassn) : iProp Σ :=
  assn_interp (mkVal θ (λ _, uval) v) a.

(** * Representation of the checker's inputs in the Go heap

    The checker's input is a tree of [checker.Type], [checker.Expr],
    [checker.Term], [checker.Assn] and [checker.Func] structs. Nodes are never
    mutated by the checker, so they are described with persistent (discarded
    fraction) points-to facts. The numeric kind codes below are those of
    checker/ast.go, checker/term.go and checker/assn.go. *)

Definition bool_code (b : bool) : w64 := if b then W64 1 else W64 0.

(* checker.Op codes *)
Definition op_code (op : cop) : w64 :=
  match op with
  | COAdd => W64 1 | COSub => W64 2 | COMul => W64 3 | COEq => W64 4
  | COLt => W64 5 | COLe => W64 6 | COGt => W64 7 | COGe => W64 8
  | CONeg => W64 9 | CONot => W64 10
  end.

Fixpoint is_type (l : loc) (t : ctype) : iProp Σ :=
  match t with
  | CTyInt => l ↦□ checker.Type'.mk (W64 1) null
  | CTyInt64 => l ↦□ checker.Type'.mk (W64 2) null
  | CTyUint64 => l ↦□ checker.Type'.mk (W64 3) null
  | CTyBool => l ↦□ checker.Type'.mk (W64 4) null
  | CTyPtr e => ∃ le, l ↦□ checker.Type'.mk (W64 5) le ∗ is_type le e
  end%I.

(* A term node with kind [k], number [n] and children [a b c]. *)
Definition tnode (k n : w64) (a b c : loc) : checker.Term.t := checker.Term.mk k n a b c.

Fixpoint is_term (l : loc) (t : term) : iProp Σ :=
  match t with
  | TVar n => l ↦□ tnode (W64 1) (W64 n) null null null
  | TPat n => l ↦□ tnode (W64 2) (W64 n) null null null
  | TResult => l ↦□ tnode (W64 3) (W64 0) null null null
  | TInt w => l ↦□ tnode (W64 4) w null null null
  | TBool b => l ↦□ tnode (W64 5) (bool_code b) null null null
  | TUnit => l ↦□ tnode (W64 6) (W64 0) null null null
  | TNull => l ↦□ tnode (W64 7) (W64 0) null null null
  | TPlus a b => ∃ la lb, l ↦□ tnode (W64 8) (W64 0) la lb null ∗ is_term la a ∗ is_term lb b
  | TMinus a b => ∃ la lb, l ↦□ tnode (W64 9) (W64 0) la lb null ∗ is_term la a ∗ is_term lb b
  | TMul a b => ∃ la lb, l ↦□ tnode (W64 10) (W64 0) la lb null ∗ is_term la a ∗ is_term lb b
  | TNeg a => ∃ la, l ↦□ tnode (W64 11) (W64 0) la null null ∗ is_term la a
  | TEq a b => ∃ la lb, l ↦□ tnode (W64 12) (W64 0) la lb null ∗ is_term la a ∗ is_term lb b
  | TLt sg a b =>
      ∃ la lb, l ↦□ tnode (if sg then W64 13 else W64 14) (W64 0) la lb null ∗ is_term la a ∗ is_term lb b
  | TLe sg a b =>
      ∃ la lb, l ↦□ tnode (if sg then W64 15 else W64 16) (W64 0) la lb null ∗ is_term la a ∗ is_term lb b
  | TNot a => ∃ la, l ↦□ tnode (W64 17) (W64 0) la null null ∗ is_term la a
  | TIte c a b =>
      ∃ lc la lb, l ↦□ tnode (W64 18) (W64 0) lc la lb ∗ is_term lc c ∗ is_term la a ∗ is_term lb b
  | TExec => l ↦□ tnode (W64 19) (W64 0) null null null
  | TRet a => ∃ la, l ↦□ tnode (W64 20) (W64 0) la null null ∗ is_term la a
  end%I.

(* An expression node: kind, name, number, operator, two types, three children. *)
Definition enode (k : w64) (name : go_string) (n op : w64) (ty ty2 a b c : loc) : checker.Expr.t :=
  checker.Expr.mk k name n op ty ty2 a b c.
Definition enode0 (k : w64) (a b c : loc) : checker.Expr.t :=
  enode k ""%go (W64 0) (W64 0) null null a b c.

Fixpoint is_expr (l : loc) (e : cexpr) : iProp Σ :=
  match e with
  | CEInt w => l ↦□ enode (W64 1) ""%go w (W64 0) null null null null null
  | CEBool b => l ↦□ enode (W64 2) ""%go (bool_code b) (W64 0) null null null null null
  | CEUnit => l ↦□ enode0 (W64 3) null null null
  | CEVar x => l ↦□ enode (W64 4) x (W64 0) (W64 0) null null null null null
  | CELet x e1 e2 =>
      ∃ la lb, l ↦□ enode (W64 5) x (W64 0) (W64 0) null null la lb null ∗ is_expr la e1 ∗ is_expr lb e2
  | CESeq e1 e2 => ∃ la lb, l ↦□ enode0 (W64 6) la lb null ∗ is_expr la e1 ∗ is_expr lb e2
  | CEIf c e1 e2 =>
      ∃ lc la lb, l ↦□ enode0 (W64 7) lc la lb ∗ is_expr lc c ∗ is_expr la e1 ∗ is_expr lb e2
  | CELoad t e =>
      ∃ lt la, l ↦□ enode (W64 8) ""%go (W64 0) (W64 0) lt null la null null ∗ is_type lt t ∗ is_expr la e
  | CEStore t e1 e2 =>
      ∃ lt la lb, l ↦□ enode (W64 9) ""%go (W64 0) (W64 0) lt null la lb null ∗
                  is_type lt t ∗ is_expr la e1 ∗ is_expr lb e2
  | CEAlloc t e =>
      ∃ lt la, l ↦□ enode (W64 10) ""%go (W64 0) (W64 0) lt null la null null ∗ is_type lt t ∗ is_expr la e
  | CEZero t => ∃ lt, l ↦□ enode (W64 11) ""%go (W64 0) (W64 0) lt null null null null ∗ is_type lt t
  | CEBinOp op t e1 e2 =>
      ∃ lt la lb, l ↦□ enode (W64 12) ""%go (W64 0) (op_code op) lt null la lb null ∗
                  is_type lt t ∗ is_expr la e1 ∗ is_expr lb e2
  | CEUnOp op t e =>
      ∃ lt la, l ↦□ enode (W64 13) ""%go (W64 0) (op_code op) lt null la null null ∗
               is_type lt t ∗ is_expr la e
  | CEConvert t1 t2 e =>
      ∃ lt1 lt2 la, l ↦□ enode (W64 14) ""%go (W64 0) (W64 0) lt1 lt2 la null null ∗
                    is_type lt1 t1 ∗ is_type lt2 t2 ∗ is_expr la e
  | CEDo e => ∃ la, l ↦□ enode0 (W64 15) la null null ∗ is_expr la e
  | CEReturn e => ∃ la, l ↦□ enode0 (W64 16) la null null ∗ is_expr la e
  | CEExcSeq e1 e2 => ∃ la lb, l ↦□ enode0 (W64 17) la lb null ∗ is_expr la e1 ∗ is_expr lb e2
  | CEExcDo e => ∃ la, l ↦□ enode0 (W64 18) la null null ∗ is_expr la e
  end%I.

(* An assertion node: kind, L, R, X, Y, Var, Sort. *)
Definition anode (k : w64) (L R X Y : loc) (var : w64) (s : w64) : checker.Assn.t :=
  checker.Assn.mk k L R X Y var s.

Fixpoint is_assn (l : loc) (a : cassn) : iProp Σ :=
  match a with
  | CAEmp => l ↦□ anode (W64 1) null null null null (W64 0) (W64 0)
  | CASep p q => ∃ lp lq, l ↦□ anode (W64 2) lp lq null null (W64 0) (W64 0) ∗ is_assn lp p ∗ is_assn lq q
  | CAOr p q => ∃ lp lq, l ↦□ anode (W64 3) lp lq null null (W64 0) (W64 0) ∗ is_assn lp p ∗ is_assn lq q
  | CAExists n s p =>
      ∃ lp, l ↦□ anode (W64 4) lp null null null (W64 n) (sort_code s) ∗ is_assn lp p
  | CAPure t => ∃ lx, l ↦□ anode (W64 5) null null lx null (W64 0) (W64 0) ∗ is_term lx t
  | CAPointsTo x y =>
      ∃ lx ly, l ↦□ anode (W64 6) null null lx ly (W64 0) (W64 0) ∗ is_term lx x ∗ is_term ly y
  end%I.

Definition is_func (l : loc) (f : cfunc) : iProp Σ :=
  (∃ (s : slice.t) (lb : loc),
      l ↦□ checker.Func.mk s lb ∗ s ↦*□ f.(fparams) ∗ is_expr lb f.(fbody))%I.

Definition is_sorts (s : slice.t) (vars : list sort) : iProp Σ :=
  (s ↦*□ (sort_code <$> vars))%I.

(** * The soundness statement

    If [checker.Check] answers [true] on (the heap representation of) a
    function [f], sort table [vars], precondition [pre] and postcondition
    [post], then for every valuation of the logical variables respecting the
    sorts, [f] applied to the values of variables [0 .. nparams-1] satisfies the
    Hoare triple with precondition [pre] and postcondition [post] (in which
    [ret] denotes the return value). This is the only unproved assumption of
    the pipeline besides the GooseLang semantics itself; the checker is not
    verified. *)
Axiom check_sound :
  ∀ (f : cfunc) (vars : list sort) (pre post : cassn)
    (lf : loc) (svars : slice.t) (lpre lpost : loc),
  {{{ is_pkg_init checker ∗
      is_func lf f ∗ is_sorts svars vars ∗ is_assn lpre pre ∗ is_assn lpost post }}}
    @! checker.Check #lf #svars #lpre #lpost
  {{{ (b : bool), RET #b;
      ⌜ b = true →
        ∀ θ : nat → val,
          vars_sat θ vars →
          {{{ pre_interp θ pre }}}
            apply_vals (func_val f) (arg_vals f θ)
          {{{ (v : val), RET v; post_interp θ v post }}} ⌝ }}}.

End semantics.
