(** * The input of the table-driven checker (tcheck/), and its serialization

    Every type here mirrors one in tcheck/syntax.go, and [ser_input] writes
    exactly the format tcheck/parse.go reads: the bytes that [tcheck.Check]
    is run on.  A generated observation file (see observe.v) states that a
    run of [Check] on some bytes returned [true], and proves that those bytes
    are [ser_input] of its input by computation; so nothing on the Go side
    of the serialization has to be trusted. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import defn.

(** Sorts: GooseLang values, Go types, and the table's own sorts, which its
    denotation maps to Gallina types. *)
Inductive srt := SVal | SType | SU (n : nat).

(** Terms.  [TLit ty es] is the value [LiteralValueV] of the elements [es]
    at type [ty]; [TUnit] is [#()]. *)
Inductive tterm :=
| TVar (n : nat)
| TSym (n : nat) (args : list tterm)
| TPair (a b : tterm)
| TLit (ty : tterm) (es : list tterm)
| TUnit.

Record symdecl := mkSym { sd_args : list srt; sd_res : srt }.
Record preddecl := mkPred { pd_pers : bool; pd_args : list srt }.

Inductive tatom :=
| APred (n : nat) (args : list tterm)
| AEq (a b : tterm).

(** Expressions whose leaves are values: the left-hand sides of rules. *)
Inductive tpat :=
| PVal (t : tterm)
| PApp (a b : tpat).

(** [∀ vars, {{{ pre }}} lhs {{{ ∃ ex, RET ret; post }}}]; the variables of
    [ret] and [post] are [vars ++ ex]. *)
Record trule := mkRule {
  r_vars : list srt; r_lhs : tpat; r_pre : list tatom;
  r_ex : list srt; r_ret : tterm; r_post : list tatom }.

(** [∀ vars, lhs = rhs], used left to right. *)
Record tfact := mkFact { f_vars : list srt; f_lhs : tterm; f_rhs : tterm }.

(** The code of a function, as Goose emits it (see [cexpr_den] in
    denote.v for what each node stands for). *)
Inductive cexpr :=
| CVal (t : tterm)
| CVar (x : go_string)
| CApp (a b : cexpr)
| CPair (a b : cexpr)
| CLet (x : go_string) (a b : cexpr)
| CSeq (a b : cexpr)
| CLit (ty : tterm) (es : list cexpr)
| CDo (a : cexpr)
| CRet (a : cexpr)
| CXSeq (a b : cexpr)
| CXDo (a : cexpr).

Record cfunc := mkFunc { fn_params : list go_string; fn_body : cexpr }.

(** [∀ vars, {{{ pre }}} f args {{{ ∃ ex, RET ret; post }}}]. *)
Record tspec := mkSpec {
  sp_vars : list srt; sp_args : list tterm; sp_pre : list tatom;
  sp_ex : list srt; sp_ret : tterm; sp_post : list tatom }.

Record tinput := mkInput {
  in_syms : list symdecl; in_preds : list preddecl;
  in_rules : list trule; in_facts : list tfact;
  in_func : cfunc; in_spec : tspec }.

(** * Serialization *)
Section ser.
Local Open Scope byte_string_scope.

Fixpoint ser_digits (fuel n : nat) (acc : go_string) : go_string :=
  match fuel with
  | O => acc
  | S fuel =>
      let d := W8 (Z.of_nat (48 + n mod 10)) in
      if decide (n < 10) then d :: acc else ser_digits fuel (n / 10) (d :: acc)
  end.
Definition ser_nat (n : nat) : go_string := ser_digits 20 n [].

Definition ser_list {A} (f : A → go_string) (l : list A) : go_string :=
  match l with
  | [] => "()"
  | x :: l => "(" ++ f x ++ foldr (λ y s, " " ++ f y ++ s) ")" l
  end.

(** " x1 .. xn" *)
Definition ser_tail {A} (f : A → go_string) (l : list A) : go_string :=
  foldr (λ y s, " " ++ f y ++ s) "" l.

Definition ser_srt (s : srt) : go_string :=
  match s with SVal => "v" | SType => "y" | SU n => "(u " ++ ser_nat n ++ ")" end.

Fixpoint ser_term (t : tterm) : go_string :=
  match t with
  | TVar n => "(var " ++ ser_nat n ++ ")"
  | TSym n args => "(sym " ++ ser_nat n ++ foldr (λ y s, " " ++ ser_term y ++ s) ")" args
  | TPair a b => "(pair " ++ ser_term a ++ " " ++ ser_term b ++ ")"
  | TLit ty es => "(lit " ++ ser_term ty ++ foldr (λ y s, " " ++ ser_term y ++ s) ")" es
  | TUnit => "unit"
  end.

Fixpoint ser_pat (p : tpat) : go_string :=
  match p with
  | PVal t => "(pval " ++ ser_term t ++ ")"
  | PApp a b => "(papp " ++ ser_pat a ++ " " ++ ser_pat b ++ ")"
  end.

Definition ser_atom (a : tatom) : go_string :=
  match a with
  | APred n args => "(pred " ++ ser_nat n ++ ser_tail ser_term args ++ ")"
  | AEq a b => "(eq " ++ ser_term a ++ " " ++ ser_term b ++ ")"
  end.

Definition ser_str (x : go_string) : go_string := """" ++ x ++ """".

Fixpoint ser_cexpr (e : cexpr) : go_string :=
  match e with
  | CVal t => "(val " ++ ser_term t ++ ")"
  | CVar x => "(cvar " ++ ser_str x ++ ")"
  | CApp a b => "(app " ++ ser_cexpr a ++ " " ++ ser_cexpr b ++ ")"
  | CPair a b => "(cpair " ++ ser_cexpr a ++ " " ++ ser_cexpr b ++ ")"
  | CLet x a b => "(let " ++ ser_str x ++ " " ++ ser_cexpr a ++ " " ++ ser_cexpr b ++ ")"
  | CSeq a b => "(seq " ++ ser_cexpr a ++ " " ++ ser_cexpr b ++ ")"
  | CLit ty es => "(clit " ++ ser_term ty ++ foldr (λ y s, " " ++ ser_cexpr y ++ s) ")" es
  | CDo a => "(do " ++ ser_cexpr a ++ ")"
  | CRet a => "(ret " ++ ser_cexpr a ++ ")"
  | CXSeq a b => "(xseq " ++ ser_cexpr a ++ " " ++ ser_cexpr b ++ ")"
  | CXDo a => "(xdo " ++ ser_cexpr a ++ ")"
  end.

Definition ser_sym (d : symdecl) : go_string :=
  "(sym " ++ ser_list ser_srt d.(sd_args) ++ " " ++ ser_srt d.(sd_res) ++ ")".
Definition ser_pred (d : preddecl) : go_string :=
  "(pred " ++ (if d.(pd_pers) then "1" else "0") ++ " " ++ ser_list ser_srt d.(pd_args) ++ ")".
Definition ser_rule (r : trule) : go_string :=
  "(rule " ++ ser_list ser_srt r.(r_vars) ++ " " ++ ser_pat r.(r_lhs) ++ " " ++
  ser_list ser_atom r.(r_pre) ++ " " ++ ser_list ser_srt r.(r_ex) ++ " " ++
  ser_term r.(r_ret) ++ " " ++ ser_list ser_atom r.(r_post) ++ ")".
Definition ser_fact (f : tfact) : go_string :=
  "(fact " ++ ser_list ser_srt f.(f_vars) ++ " " ++ ser_term f.(f_lhs) ++ " " ++
  ser_term f.(f_rhs) ++ ")".
Definition ser_func (f : cfunc) : go_string :=
  "(func " ++ ser_list ser_str f.(fn_params) ++ " " ++ ser_cexpr f.(fn_body) ++ ")".
Definition ser_spec (s : tspec) : go_string :=
  "(spec " ++ ser_list ser_srt s.(sp_vars) ++ " " ++ ser_list ser_term s.(sp_args) ++ " " ++
  ser_list ser_atom s.(sp_pre) ++ " " ++ ser_list ser_srt s.(sp_ex) ++ " " ++
  ser_term s.(sp_ret) ++ " " ++ ser_list ser_atom s.(sp_post) ++ ")".

Definition ser_input (i : tinput) : go_string :=
  "(input (syms" ++ ser_tail ser_sym i.(in_syms) ++ ") (preds" ++
  ser_tail ser_pred i.(in_preds) ++ ") (rules" ++ ser_tail ser_rule i.(in_rules) ++
  ") (facts" ++ ser_tail ser_fact i.(in_facts) ++ ") " ++ ser_func i.(in_func) ++ " " ++
  ser_spec i.(in_spec) ++ ")".
End ser.
