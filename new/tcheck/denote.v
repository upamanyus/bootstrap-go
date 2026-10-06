(** * What an input of the table-driven checker means

    A table names its sorts, symbols and predicates; a denotation [den]
    gives each of them a Gallina meaning, typed by the table's declarations
    (so that a well-sorted term always evaluates).  Everything is relative to
    an ambient GooseLang setting -- an FFI, a ghost state [heapGS Σ], a Go
    semantics -- and to the package assumptions [d_pkg] the denotation
    needs (for raft, [raft.Assumptions]): exactly the binders of a spec body
    in the etcd proofs ([wp_raft__becomeFollower_body] etc.).

    - [rule_valid D r] is the Hoare triple a rule stands for, in Perennial's
      Prop-level [{{{ }}}] form, so that it computes to the statement of the
      lemma it is linked to.
    - [table_valid D i]: every rule and fact of the input holds and every
      predicate declared persistent is.
    - [input_holds i]: in every denotation in which the table is valid, the
      function satisfies its specification. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.tcheck Require Export syntax.

Fixpoint lookup_sym (l : list symdecl) (n : nat) : symdecl :=
  match l with
  | [] => mkSym [] SVal
  | d :: l => match n with O => d | S n => lookup_sym l n end
  end.

Fixpoint lookup_pred (l : list preddecl) (n : nat) : preddecl :=
  match l with
  | [] => mkPred false []
  | d :: l => match n with O => d | S n => lookup_pred l n end
  end.

Section ambient.
Context {ext : ffi_syntax} {ffi : ffi_model} {ffi_interp0 : ffi_interp ffi}
  {Σ : gFunctors} {hG : heapGS Σ} {ffi_semantics0 : ffi_semantics ext ffi}
  {sem : go.Semantics}.

Section sorts.
Context (ds : nat → Type).

Definition srt_den (s : srt) : Type :=
  match s with SVal => val | SType => go.type | SU n => ds n end.

Fixpoint arrows (args : list srt) (R : Type) : Type :=
  match args with [] => R | a :: l => srt_den a → arrows l R end.

Definition sym_ty (d : symdecl) : Type := arrows d.(sd_args) (srt_den d.(sd_res)).
Definition pred_ty (d : preddecl) : Type := arrows d.(pd_args) (iProp Σ).
End sorts.

(** The meaning of the table's sorts, symbols and predicates. *)
Record den_at (syms : list symdecl) (preds : list preddecl) := mkDenAt {
  d_sort : nat → Type;
  d_sym : ∀ n, sym_ty d_sort (lookup_sym syms n);
  d_pred : ∀ n, pred_ty d_sort (lookup_pred preds n);
}.
Arguments d_sort {_ _}.
Arguments d_sym {_ _}.
Arguments d_pred {_ _}.

Section eval.
Context {syms : list symdecl} {preds : list preddecl} (DA : den_at syms preds).
Notation ds := DA.(d_sort).

(** A value of some sort. *)
Definition dyn : Type := { s : srt & srt_den ds s }.

Fixpoint nat_cast (P : nat → Type) (i j : nat) {struct i} : P i → option (P j) :=
  match i, j return P i → option (P j) with
  | O, O => λ x, Some x
  | S i, S j => nat_cast (λ k, P (S k)) i j
  | _, _ => λ _, None
  end.

(** [d] at sort [s], if it has that sort.  Defined by matching on the two
    sort codes, so that it computes on closed codes without any proof of
    equality. *)
Definition cast (s : srt) (d : dyn) : option (srt_den ds s) :=
  match d with
  | existT s' x =>
      (match s', s return srt_den ds s' → option (srt_den ds s) with
       | SVal, SVal => λ x, Some x
       | SType, SType => λ x, Some x
       | SU i, SU j => nat_cast ds i j
       | _, _ => λ _, None
       end) x
  end.

Fixpoint sym_apply (args : list srt) {R : Type} (f : arrows ds args R)
    (vs : list (option dyn)) : option R :=
  match args return arrows ds args R → option R with
  | [] => λ f, match vs with [] => Some f | _ => None end
  | a :: args => λ f,
      match vs with
      | Some d :: vs => match cast a d with Some x => sym_apply args (f x) vs | None => None end
      | _ => None
      end
  end f.

Definition as_val (d : option dyn) : option val :=
  match d with Some d => cast SVal d | None => None end.

Fixpoint vals_of (ds : list (option dyn)) : option (list val) :=
  match ds with
  | [] => Some []
  | d :: ds => match as_val d, vals_of ds with Some v, Some vs => Some (v :: vs) | _, _ => None end
  end.

Fixpoint teval (θ : list dyn) (t : tterm) : option dyn :=
  match t with
  | TVar n => List.nth_error θ n
  | TSym n args =>
      match sym_apply (lookup_sym syms n).(sd_args) (DA.(d_sym) n) (map (teval θ) args) with
      | Some r => Some (existT (lookup_sym syms n).(sd_res) r)
      | None => None
      end
  | TPair a b =>
      match as_val (teval θ a), as_val (teval θ b) with
      | Some va, Some vb => Some (existT SVal (PairV va vb))
      | _, _ => None
      end
  | TLit ty es =>
      match (match teval θ ty with Some d => cast SType d | None => None end),
            vals_of (List.map (teval θ) es) with
      | Some t, Some vs =>
          Some (existT SVal
                  (LiteralValueV (List.map (λ v, KeyedElement None (ElementExpression t (Val v))) vs)))
      | _, _ => None
      end
  | TUnit => Some (existT SVal #())
  end.

(** A term at sort [val]; [#()] if it is not one (which a well-formed input
    never asks for). *)
Definition val_den (θ : list dyn) (t : tterm) : val :=
  match as_val (teval θ t) with Some v => v | None => #() end.

Definition type_den (t : tterm) : go.type :=
  match teval [] t with
  | Some d => match cast SType d with Some ty => ty | None => go.bool end
  | None => go.bool
  end.

Definition atom_den (θ : list dyn) (a : tatom) : iProp Σ :=
  match a with
  | APred n args =>
      match sym_apply (lookup_pred preds n).(pd_args) (DA.(d_pred) n) (map (teval θ) args) with
      | Some P => P
      | None => False
      end
  | AEq a b => ⌜∃ d, teval θ a = Some d ∧ teval θ b = Some d⌝
  end%I.

(** An assertion: [True] if empty, else its atoms joined by [∗] without a
    trailing unit, the way a spec is written. *)
Fixpoint assn_den (θ : list dyn) (l : list tatom) : iProp Σ :=
  match l with
  | [] => True
  | [a] => atom_den θ a
  | a :: l => atom_den θ a ∗ assn_den θ l
  end%I.

Fixpoint pat_den (θ : list dyn) (p : tpat) : expr :=
  match p with
  | PVal t => Val (val_den θ t)
  | PApp a b => App (pat_den θ a) (pat_den θ b)
  end.

(** The code, as GooseLang: each node is what Goose emits for it. *)
Fixpoint cexpr_den (e : cexpr) : expr :=
  match e with
  | CVal t => Val (val_den [] t)
  | CVar x => Var (go.go_string_to_string x)
  | CApp a b => App (cexpr_den a) (cexpr_den b)
  | CPair a b => Pair (cexpr_den a) (cexpr_den b)
  | CLet x a b => App (Rec BAnon (BNamed (go.go_string_to_string x)) (cexpr_den b)) (cexpr_den a)
  | CSeq a b => App (Rec BAnon BAnon (cexpr_den b)) (cexpr_den a)
  | CLit ty es =>
      LiteralValue (List.map (λ e, KeyedElement None (ElementExpression (type_den ty) (cexpr_den e)))
                      es)
  | CDo a => (do: cexpr_den a)%E
  | CRet a => (return: cexpr_den a)%E
  | CXSeq a b => (cexpr_den a ;;; cexpr_den b)%E
  | CXDo a => App (Val exception_do) (cexpr_den a)
  end.

Fixpoint lams (xs : list go_string) (e : expr) : expr :=
  match xs with
  | [] => e
  | x :: xs => Lam (BNamed (go.go_string_to_string x)) (lams xs e)
  end.

(** [λ: x1 .. xn, body], or [λ: <>, body] without parameters. *)
Definition func_val (f : cfunc) : val :=
  match f.(fn_params) with
  | [] => LamV BAnon (cexpr_den f.(fn_body))
  | x :: xs => LamV (BNamed (go.go_string_to_string x)) (lams xs (cexpr_den f.(fn_body)))
  end.

Definition apply_vals (f : val) (args : list val) : expr :=
  foldl (λ e v, App e (Val v)) (Val f) args.

(** Universal quantification over variables of sorts [ss], appended to a
    valuation; it computes to curried binders. *)
Fixpoint forall_sorts (ss : list srt) (k : list dyn → Prop) : Prop :=
  match ss with
  | [] => k []
  | s :: ss => ∀ x : srt_den ds s, forall_sorts ss (λ θ, k (existT s x :: θ))
  end.

Fixpoint bi_forall_sorts (ss : list srt) (k : list dyn → iProp Σ) : iProp Σ :=
  match ss with
  | [] => k []
  | s :: ss => ∀ x : srt_den ds s, bi_forall_sorts ss (λ θ, k (existT s x :: θ))
  end%I.

(** [{{{ pre }}} e {{{ ∃ ex, RET ret; post }}}] at valuation [θ]. *)
Definition triple_at (θ : list dyn) (pre : list tatom) (e : expr) (ex : list srt) (ret : tterm)
    (post : list tatom) : Prop :=
  ∀ Φ : val → iProp Σ,
    assn_den θ pre -∗
    ▷ bi_forall_sorts ex (λ θx, assn_den (θ ++ θx) post -∗ Φ (val_den (θ ++ θx) ret)) -∗
    WP e {{ Φ }}.

Fixpoint pers_ok (args : list srt) (P : arrows ds args (iProp Σ)) : Prop :=
  match args return arrows ds args (iProp Σ) → Prop with
  | [] => λ P, Persistent P
  | a :: args => λ P, ∀ x, pers_ok args (P x)
  end P.

(** The persistence obligations of the predicates [n0], [n0 + 1], ... in
    [l]: one conjunct per persistent one. *)
Fixpoint pers_obl (l : list preddecl) (n0 : nat) : Prop :=
  match l with
  | [] => True
  | d :: l =>
      (if d.(pd_pers) then pers_ok (lookup_pred preds n0).(pd_args) (DA.(d_pred) n0) else True) ∧
      pers_obl l (S n0)
  end.
End eval.
End ambient.

(** A denotation: the package assumptions it needs, and the meaning of the
    table in every ambient setting satisfying them. *)
Record den (syms : list symdecl) (preds : list preddecl) := mkDen {
  d_pkg : ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics), Prop;
  d_at : ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics),
    d_pkg ext ffi ffi_interp0 Σ hG ffi_semantics0 sem → den_at (ext:=ext) (Σ:=Σ) syms preds;
}.
Arguments d_pkg {_ _}.
Arguments d_at {_ _}.

Section valid.
Context {syms : list symdecl} {preds : list preddecl} (D : den syms preds).

(** [∀ ambient (pkg : d_pkg), P (d_at pkg)], with the binders of a spec
    body. *)
Definition every_ambient (P : ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics), den_at (ext:=ext) (Σ:=Σ) syms preds → Prop) : Prop :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (pkg : D.(d_pkg) ext ffi ffi_interp0 Σ hG ffi_semantics0 sem),
    P ext ffi ffi_interp0 Σ hG ffi_semantics0 sem (D.(d_at) ext ffi ffi_interp0 Σ hG ffi_semantics0 sem pkg).

Definition rule_valid (r : trule) : Prop :=
  every_ambient (λ ext ffi ffi_interp0 Σ hG ffi_semantics0 sem DA,
    forall_sorts DA r.(r_vars) (λ θ,
      triple_at DA θ r.(r_pre) (pat_den DA θ r.(r_lhs)) r.(r_ex) r.(r_ret) r.(r_post))).

Definition fact_valid (f : tfact) : Prop :=
  every_ambient (λ ext ffi ffi_interp0 Σ hG ffi_semantics0 sem DA,
    forall_sorts DA f.(f_vars) (λ θ, teval DA θ f.(f_lhs) = teval DA θ f.(f_rhs))).

Definition preds_valid : Prop :=
  every_ambient (λ ext ffi ffi_interp0 Σ hG ffi_semantics0 sem DA, pers_obl DA preds 0).
End valid.

Definition table_valid {syms preds} (D : den syms preds) (rs : list trule) (fs : list tfact) : Prop :=
  Forall (rule_valid D) rs ∧ Forall (fact_valid D) fs ∧ preds_valid D.

(** The function's specification, in denotation [D]. *)
Definition spec_valid {syms preds} (D : den syms preds) (f : cfunc) (sp : tspec) : Prop :=
  every_ambient D (λ ext ffi ffi_interp0 Σ hG ffi_semantics0 sem DA,
    forall_sorts DA sp.(sp_vars) (λ θ,
      triple_at DA θ sp.(sp_pre) (apply_vals (func_val DA f) (List.map (val_den DA θ) sp.(sp_args)))
        sp.(sp_ex) sp.(sp_ret) sp.(sp_post))).

(** What [tcheck.Check] answering [true] on [ser_input i] is claimed to
    mean (observe.v). *)
Definition input_holds (i : tinput) : Prop :=
  ∀ D : den i.(in_syms) i.(in_preds),
    table_valid D i.(in_rules) i.(in_facts) → spec_valid D i.(in_func) i.(in_spec).
