(** Substitution for the checker's fragment.

    The reference semantics of the analysed program substitutes values for
    parameters and [let]-bound names; the checker instead carries an
    environment. [csubst m e] is the GooseLang expression that the checker
    input [e] denotes once its free variables have been replaced according to
    [m] -- that is, [expr_of e] with the environment already applied.

    Defining it by recursion on [cexpr] rather than as a [subst_map] over all
    of GooseLang's [expr] keeps every induction here an 18-case induction over
    the fragment, instead of a mutual induction over [expr]/[val]/keyed
    elements/select clauses. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.checker Require Import defs.

Set Default Proof Using "Type".

Section subst.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.

Definition pname (x : go_string) : string := go.go_string_to_string x.

(** [go_string_to_string] is a bijection onto its image, so distinct Go names
    stay distinct as GooseLang binders. *)
Lemma string_to_go_string_to_string gs :
  go.string_to_go_string (go.go_string_to_string gs) = gs.
Proof.
  rewrite /go.string_to_go_string /go.go_string_to_string.
  rewrite String.list_byte_of_string_of_list_byte -list_fmap_compose.
  rewrite (list_fmap_ext _ id); last first.
  { intros i w _. simpl. byte_cases w; reflexivity. }
  by rewrite list_fmap_id.
Qed.

#[global] Instance pname_inj : Inj (=) (=) pname.
Proof.
  intros x y Heq. rewrite /pname in Heq.
  by rewrite -(string_to_go_string_to_string x) -(string_to_go_string_to_string y) Heq.
Qed.

(** [csubst m e] agrees with [expr_of e] except at the free variables in the
    domain of [m], which become the values [m] gives them. *)
Fixpoint csubst (m : gmap string val) (e : cexpr) : expr :=
  match e with
  | CEInt w => Val #w
  | CEBool b => Val #b
  | CEUnit => Val #()
  | CEVar x => match m !! pname x with Some v => Val v | None => Var (pname x) end
  | CELet x e1 e2 =>
      App (Rec BAnon (BNamed (pname x)) (csubst (delete (pname x) m) e2)) (csubst m e1)
  | CESeq e1 e2 => App (Rec BAnon BAnon (csubst m e2)) (csubst m e1)
  | CEIf c e1 e2 => If (csubst m c) (csubst m e1) (csubst m e2)
  | CELoad t e => App (Val (GoInstruction (GoLoad (type_of t)))) (csubst m e)
  | CEStore t e1 e2 =>
      App (Val (GoInstruction (GoStore (type_of t)))) (Pair (csubst m e1) (csubst m e2))
  | CEAlloc t e => App (Val (GoInstruction (GoAlloc (type_of t)))) (csubst m e)
  | CEZero t => App (Val (GoInstruction (GoZeroVal (type_of t)))) (Val #())
  | CEBinOp op t e1 e2 =>
      App (Val (GoInstruction (GoOp (binop_of op) (type_of t)))) (Pair (csubst m e1) (csubst m e2))
  | CEUnOp op t e => App (Val (GoInstruction (GoUnOp (unop_of op) (type_of t)))) (csubst m e)
  | CEConvert t1 t2 e =>
      App (Val (GoInstruction (Convert (type_of t1) (type_of t2)))) (csubst m e)
  | CEDo e => (do: csubst m e)%E
  | CEReturn e => (return: csubst m e)%E
  | CEExcSeq e1 e2 => (csubst m e1 ;;; csubst m e2)%E
  | CEExcDo e => App (Val exception_do) (csubst m e)
  end.

Lemma csubst_empty e : csubst ∅ e = expr_of e.
Proof.
  induction e; simpl; rewrite ?delete_empty; try congruence.
  by rewrite lookup_empty.
Qed.

(** The equation that a beta step needs: substituting the argument into the
    body is the same as extending the environment. *)
Lemma csubst_insert m x v e :
  subst x v (csubst (delete x m) e) = csubst (<[x := v]> m) e.
Proof.
  revert m. induction e; intros m; simpl; try (by rewrite ?IHe ?IHe1 ?IHe2 ?IHe3).
  - (* CEVar *)
    destruct (decide (pname x0 = x)) as [->|Hne].
    + rewrite lookup_delete_eq /= decide_True // lookup_insert_eq //.
    + rewrite lookup_delete_ne // lookup_insert_ne //.
      destruct (m !! pname x0); simpl; [done|by rewrite decide_False].
  - (* CELet *)
    rewrite IHe1. f_equal. f_equal.
    destruct (decide (BNamed x ≠ BAnon ∧ BNamed x ≠ BNamed (pname x0))) as [Hd|Hd];
      rewrite decide_bool_decide.
    + rewrite (bool_decide_true _ Hd).
      assert (x ≠ pname x0) as Hne by naive_solver.
      rewrite delete_commute IHe2 delete_insert_ne //.
    + rewrite (bool_decide_false _ Hd).
      assert (x = pname x0) as -> by naive_solver.
      by rewrite delete_idemp delete_insert_delete.
Qed.

(** * Deleting a list of names, and the environment a curried application
      builds *)

Definition pnames (xs : list go_string) : list string := pname <$> xs.

Definition delete_names (xs : list string) (m : gmap string val) : gmap string val :=
  foldr delete m xs.

Lemma delete_names_nil m : delete_names [] m = m.
Proof. done. Qed.
Lemma delete_names_cons x xs m : delete_names (x :: xs) m = delete x (delete_names xs m).
Proof. done. Qed.

Lemma delete_names_elem x xs m : x ∈ xs → delete x (delete_names xs m) = delete_names xs m.
Proof.
  induction xs as [|y xs IH]; first by inversion 1.
  rewrite delete_names_cons.
  intros [->|Hin]%elem_of_cons; first by rewrite delete_idemp.
  by rewrite delete_commute IH.
Qed.

Lemma delete_names_insert_not_elem x xs v m :
  x ∉ xs → delete_names xs (<[x := v]> m) = <[x := v]> (delete_names xs m).
Proof.
  induction xs as [|y xs IH]; first done.
  intros Hnin. rewrite !delete_names_cons IH; last set_solver.
  rewrite delete_insert_ne //. set_solver.
Qed.

Lemma delete_names_insert_elem x xs v m :
  x ∈ xs → delete_names xs (<[x := v]> m) = delete_names xs m.
Proof.
  induction xs as [|y xs IH]; first by inversion 1.
  intros Hin. rewrite !delete_names_cons.
  destruct (decide (x ∈ xs)) as [Hin'|Hnin']; first by rewrite IH.
  apply elem_of_cons in Hin as [->|?]; last done.
  by rewrite delete_names_insert_not_elem // delete_insert_delete.
Qed.

(** The environment built by applying [vs] to the parameters [xs]: later
    parameters shadow earlier ones, exactly as [envBind] in checker/check.go
    puts the last binding at the head of the list. *)
Fixpoint binds (xs : list string) (vs : list val) (m : gmap string val) : gmap string val :=
  match xs, vs with
  | x :: xs', v :: vs' => binds xs' vs' (<[x := v]> m)
  | _, _ => m
  end.

(** * Substitution under a chain of lambdas *)

Lemma subst_lams x v xs e :
  subst x v (lams xs e) =
    lams xs (if decide (x ∈ pnames xs) then e else subst x v e).
Proof.
  induction xs as [|y ys IH]; simpl.
  { by rewrite decide_False; last set_solver. }
  rewrite /Lam. f_equal. rewrite decide_bool_decide.
  destruct (decide (x = pname y)) as [->|Hne].
  - rewrite bool_decide_false; last naive_solver.
    rewrite decide_True //. rewrite /pnames fmap_cons. set_solver.
  - rewrite bool_decide_true; last naive_solver.
    rewrite IH. f_equal.
    rewrite /pnames fmap_cons.
    destruct (decide (x ∈ pname y :: (pname <$> ys))) as [Hin|Hnin];
      destruct (decide (x ∈ (pname <$> ys))) as [Hin'|Hnin']; try done.
    + set_solver.
    + set_solver.
Qed.

(** The body of a curried function after one argument has been consumed. *)
Lemma lams_step x xs m v e :
  subst (pname x) v (lams xs (csubst (delete_names (pnames (x :: xs)) m) e)) =
  lams xs (csubst (delete_names (pnames xs) (<[pname x := v]> m)) e).
Proof.
  rewrite subst_lams. f_equal.
  rewrite /pnames fmap_cons delete_names_cons.
  destruct (decide (pname x ∈ pnames xs)) as [Hin|Hnin].
  - rewrite delete_names_insert_elem //. f_equal. by apply delete_names_elem.
  - rewrite delete_names_insert_not_elem // -csubst_insert //.
Qed.

(** * The environment of the checker's linked-list [env] *)

(** [env_interp V ρ] is the substitution the checker's environment stands for.
    The head of the list wins, matching [envLookup]. *)
Definition env_interp (V : valuation) (ρ : list (go_string * term)) : gmap string val :=
  foldr (λ xt m, <[pname xt.1 := teval V xt.2]> m) ∅ ρ.

Lemma env_interp_nil V : env_interp V [] = ∅.
Proof. done. Qed.

Lemma env_interp_bind V x t ρ :
  env_interp V ((x, t) :: ρ) = <[pname x := teval V t]> (env_interp V ρ).
Proof. done. Qed.

(** [envLookup] finds the first binding of [x]. *)
Fixpoint env_lookup (ρ : list (go_string * term)) (x : go_string) : option term :=
  match ρ with
  | [] => None
  | (y, t) :: ρ' => if decide (y = x) then Some t else env_lookup ρ' x
  end.

Lemma env_interp_lookup V ρ x :
  env_interp V ρ !! pname x = teval V <$> env_lookup ρ x.
Proof.
  induction ρ as [|[y t] ρ IH]; simpl; first by rewrite lookup_empty.
  destruct (decide (y = x)) as [->|Hne]; first by rewrite lookup_insert_eq.
  rewrite lookup_insert_ne //. by intros ?%pname_inj.
Qed.

End subst.
