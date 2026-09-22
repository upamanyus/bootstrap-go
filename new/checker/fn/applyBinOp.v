(** [checker.applyBinOp] (checker/exec.go): the term for a binary Go operator
    at a type, after checking that both operands' sorts are the type's.

    Note on naming: no Rocq variable here may be called [op], [t], [vars],
    [a], [b], [tok], [ts], [oka], [sa], [okb], [sb] or [signed] -- those are
    the Go function's own locals and [wp_auto] derives Rocq identifiers from
    the Go names (see NOTES.md).  The operator is therefore [o], the type
    [cty], the slice of variable sorts [sv] and the operands [u] and [w]. *)
From New.checker Require Import prelude nodes.
From New.checker.fn Require Import TypeSort typeSigned.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.

(** * The specification of [SortOf]

    [new/checker/fn/SortOf.vo] had not been built when this file was written,
    so [wp_SortOf] is assumed here.  The statement, and the three definitions
    it is phrased over, are character-identical to the ones proved in
    [new/checker/fn/sortOfEnv.v] and [new/checker/fn/SortOf.v]: deleting this
    block and adding [SortOf] to the [Require Import] above is the only change
    needed once those files are compiled. *)

Definition osort_of (E : sort_env) (ot : option term) : option sort :=
  match ot with None => None | Some ty => sort_of E ty end.

Definition osort_code (os : option sort) : w64 :=
  match os with Some s => sort_code s | None => W64 0 end.
Definition osort_ok (os : option sort) : bool :=
  match os with Some _ => true | None => false end.

Context (wp_SortOf :
  forall (sv : slice.t) (lterm : loc) (vl : list sort) (oty : option term),
  {{{ is_pkg_init checker ∗ sv ↦*□ (sort_code <$> vl) ∗ is_oterm lterm oty }}}
    @! checker.SortOf #sv #lterm
  {{{ RET (#(osort_code (osort_of (vars_env vl) oty)),
           #(osort_ok (osort_of (vars_env vl) oty)));
      True }}}).

Set Default Proof Using "All".

(** The Go code compares sorts by their codes, the mirrors by [decide]; the
    two agree because the encoding is injective. *)
Lemma sort_code_inj' s1 s2 : sort_code s1 = sort_code s2 -> s1 = s2.
Proof. destruct s1, s2; try done; intros Hc; exfalso; revert Hc; by vm_compute. Qed.

(** Whether the Go function's second result is [true]. *)
Definition oterm_ok (ot : option term) : bool :=
  match ot with Some _ => true | None => false end.

(** The Gallina mirror of the whole function: the sort check of [applyBinOp],
    then the term-building half, which is [apply_binop] in steps.v. *)
Definition binop_result (o : cop) (cty : ctype) (vl : list sort)
    (ox oy : option term) : option term :=
  match ox, oy with
  | Some u, Some w =>
      if decide (sort_of_vars vl u = Some (ctype_sort cty) ∧
                 sort_of_vars vl w = Some (ctype_sort cty))
      then apply_binop o cty u w else None
  | _, _ => None
  end.

(** Either operand failing the sort check makes the whole thing fail.  This is
    phrased over [osort_of] because that is the form the two [SortOf] results
    appear in. *)
Lemma binop_result_none o cty vl ox oy :
  ¬ (osort_of (vars_env vl) ox = Some (ctype_sort cty) ∧
     osort_of (vars_env vl) oy = Some (ctype_sort cty)) →
  binop_result o cty vl ox oy = None.
Proof.
  intros Hne. destruct ox as [u|], oy as [w|]; try done.
  rewrite /binop_result. by rewrite decide_False.
Qed.

Lemma binop_result_good o cty vl u w :
  sort_of_vars vl u = Some (ctype_sort cty) →
  sort_of_vars vl w = Some (ctype_sort cty) →
  binop_result o cty vl (Some u) (Some w) = apply_binop o cty u w.
Proof. intros H1 H2. rewrite /binop_result /=. by rewrite decide_True. Qed.

(** [ctype_sort] is never [SUnit], so the [OpEq]-at-unit rejection in
    [apply_binop] (and in the Go code) is unreachable at a supported type. *)
Lemma ctype_sort_ne_unit cty : ctype_sort cty ≠ SUnit.
Proof. by destruct cty. Qed.

(** [apply_binop] with its [decide]s resolved, at an integer type ... *)
Lemma apply_binop_int o cty u w :
  ctype_sort cty = SInt →
  apply_binop o cty u w =
    match o with
    | COAdd => Some (TPlus u w)
    | COSub => Some (TMinus u w)
    | COMul => Some (TMul u w)
    | COEq => Some (TEq u w)
    | COLt => Some (TLt (ctype_signed cty) u w)
    | COLe => Some (TLe (ctype_signed cty) u w)
    | COGt => Some (TLt (ctype_signed cty) w u)
    | COGe => Some (TLe (ctype_signed cty) w u)
    | CONeg | CONot => None
    end.
Proof.
  intros Hs. destruct o; rewrite /apply_binop;
    rewrite ?(decide_True _ _ Hs) ?(decide_False _ _ (ctype_sort_ne_unit cty)) //.
Qed.

(** ... and at [bool] or a pointer, where only [OpEq] survives. *)
Lemma apply_binop_nonint o cty u w :
  ctype_sort cty ≠ SInt →
  apply_binop o cty u w = match o with COEq => Some (TEq u w) | _ => None end.
Proof.
  intros Hs. destruct o; rewrite /apply_binop;
    rewrite ?(decide_False _ _ Hs) ?(decide_False _ _ (ctype_sort_ne_unit cty)) //.
Qed.

Local Ltac reject := iApply ("HΦ" $! null false); by iFrame.

(** Every accepting branch ends with an anonymous [GoAlloc] of the new [Term]
    node, which [wp_auto] cannot do (see NOTES.md).  The node's name has to be
    an argument: an [ident] written inside an [Ltac] body is resolved when the
    body is parsed, and fails there. *)
Local Ltac alloc_term l :=
  iApply wp_fupd; wp_alloc l as "Hr"; try wp_auto; iPersist "Hr";
  iModIntro; iApply ("HΦ" $! l true); iSplit; first done;
  simpl; iFrame "Hr Hp Hq".

(** At an integer type the Go code reads [typeSigned] before dispatching. *)
Local Ltac go_signed lt cty0 :=
  try wp_auto; wp_apply (wp_typeSigned lt cty0 with "[$]");
  cbn [ctype_signed]; try wp_auto.

Lemma wp_applyBinOp (o : cop) (lty : loc) (cty : ctype)
      (sv : slice.t) (vl : list sort) (lp lq : loc) (ox oy : option term) :
  {{{ is_pkg_init checker ∗ is_type lty cty ∗
      sv ↦*□ (sort_code <$> vl) ∗ is_oterm lp ox ∗ is_oterm lq oy }}}
    @! checker.applyBinOp #(op_code o) #lty #sv #lp #lq
  {{{ (lr : loc) (ok : bool), RET (#lr, #ok);
      ⌜ok = oterm_ok (binop_result o cty vl ox oy)⌝ ∗
      is_oterm lr (binop_result o cty vl ox oy) }}}.
Proof.
  wp_start as "(#Hty & #Hsv & #Hp & #Hq)".
  wp_auto.
  wp_apply (wp_TypeSort lty (Some cty) with "[$]").
  try wp_auto.
  wp_apply (wp_SortOf sv lp vl ox with "[$]").
  try wp_auto.
  wp_apply (wp_SortOf sv lq vl oy with "[$]").
  try wp_auto.
  destruct (osort_of (vars_env vl) ox) as [s1|] eqn:E1; cbn [osort_code osort_ok];
    last first.
  { (* the first operand has no sort *)
    assert (binop_result o cty vl ox oy = None) as Hr
      by (apply binop_result_none; rewrite E1; by intros [[= ?] _]).
    rewrite Hr. try wp_auto. reject. }
  destruct (osort_of (vars_env vl) oy) as [s2|] eqn:E2; cbn [osort_code osort_ok];
    last first.
  { (* the second operand has no sort *)
    assert (binop_result o cty vl ox oy = None) as Hr
      by (apply binop_result_none; rewrite E2; by intros [_ [= ?]]).
    rewrite Hr. try wp_auto. reject. }
  destruct (decide (s1 = ctype_sort cty)) as [->|Hne1]; last first.
  { (* the first operand's sort is not the type's *)
    assert (binop_result o cty vl ox oy = None) as Hr
      by (apply binop_result_none; rewrite E1; by intros [[= ?] _]).
    rewrite Hr. try wp_auto.
    rewrite bool_decide_eq_false_2;
      last (intros Hc; apply sort_code_inj' in Hc; by apply Hne1).
    try wp_auto. reject. }
  destruct (decide (s2 = ctype_sort cty)) as [->|Hne2]; last first.
  { (* the second operand's sort is not the type's *)
    assert (binop_result o cty vl ox oy = None) as Hr
      by (apply binop_result_none; rewrite E2; by intros [_ [= ?]]).
    rewrite Hr. try wp_auto.
    rewrite bool_decide_eq_true_2 //. try wp_auto.
    rewrite bool_decide_eq_false_2;
      last (intros Hc; apply sort_code_inj' in Hc; by apply Hne2).
    try wp_auto. reject. }
  (* both operands have the type's sort *)
  destruct ox as [u|]; last by (cbn in E1).
  destruct oy as [w|]; last by (cbn in E2).
  cbn [osort_of] in E1, E2.
  rewrite (binop_result_good o cty vl u w E1 E2).
  try wp_auto.
  rewrite bool_decide_eq_true_2 //. try wp_auto.
  rewrite bool_decide_eq_true_2 //. try wp_auto.
  (* dispatch on the operator *)
  destruct cty as [ | | | | cel ].
  - (* CTyInt *)
    rewrite (apply_binop_int o CTyInt u w eq_refl).
    cbn [ctype_sort sort_code ctype_signed].
    destruct o; cbn [op_code].
    + (* COAdd *) go_signed lty CTyInt. alloc_term lr.
    + (* COSub *) go_signed lty CTyInt. alloc_term lr.
    + (* COMul *) go_signed lty CTyInt. alloc_term lr.
    + (* COEq: returns before [typeSigned] is reached *) try wp_auto. alloc_term lr.
    + (* COLt *) go_signed lty CTyInt. alloc_term lr.
    + (* COLe *) go_signed lty CTyInt. alloc_term lr.
    + (* COGt: the Go code swaps the operands *) go_signed lty CTyInt. alloc_term lr.
    + (* COGe: the Go code swaps the operands *) go_signed lty CTyInt. alloc_term lr.
    + (* CONeg: not a binary operator *) go_signed lty CTyInt. reject.
    + (* CONot: not a binary operator *) go_signed lty CTyInt. reject.
  - (* CTyInt64 *)
    rewrite (apply_binop_int o CTyInt64 u w eq_refl).
    cbn [ctype_sort sort_code ctype_signed].
    destruct o; cbn [op_code].
    + (* COAdd *) go_signed lty CTyInt64. alloc_term lr.
    + (* COSub *) go_signed lty CTyInt64. alloc_term lr.
    + (* COMul *) go_signed lty CTyInt64. alloc_term lr.
    + (* COEq: returns before [typeSigned] is reached *) try wp_auto. alloc_term lr.
    + (* COLt *) go_signed lty CTyInt64. alloc_term lr.
    + (* COLe *) go_signed lty CTyInt64. alloc_term lr.
    + (* COGt: the Go code swaps the operands *) go_signed lty CTyInt64. alloc_term lr.
    + (* COGe: the Go code swaps the operands *) go_signed lty CTyInt64. alloc_term lr.
    + (* CONeg: not a binary operator *) go_signed lty CTyInt64. reject.
    + (* CONot: not a binary operator *) go_signed lty CTyInt64. reject.
  - (* CTyUint64 *)
    rewrite (apply_binop_int o CTyUint64 u w eq_refl).
    cbn [ctype_sort sort_code ctype_signed].
    destruct o; cbn [op_code].
    + (* COAdd *) go_signed lty CTyUint64. alloc_term lr.
    + (* COSub *) go_signed lty CTyUint64. alloc_term lr.
    + (* COMul *) go_signed lty CTyUint64. alloc_term lr.
    + (* COEq: returns before [typeSigned] is reached *) try wp_auto. alloc_term lr.
    + (* COLt *) go_signed lty CTyUint64. alloc_term lr.
    + (* COLe *) go_signed lty CTyUint64. alloc_term lr.
    + (* COGt: the Go code swaps the operands *) go_signed lty CTyUint64. alloc_term lr.
    + (* COGe: the Go code swaps the operands *) go_signed lty CTyUint64. alloc_term lr.
    + (* CONeg: not a binary operator *) go_signed lty CTyUint64. reject.
    + (* CONot: not a binary operator *) go_signed lty CTyUint64. reject.
  - (* CTyBool: the sort is not SortInt, so only OpEq is accepted *)
    rewrite (apply_binop_nonint o CTyBool u w); last done.
    cbn [ctype_sort sort_code].
    destruct o; cbn [op_code].
    + (* COAdd *) try wp_auto. reject.
    + (* COSub *) try wp_auto. reject.
    + (* COMul *) try wp_auto. reject.
    + (* COEq *) try wp_auto. alloc_term lr.
    + (* COLt *) try wp_auto. reject.
    + (* COLe *) try wp_auto. reject.
    + (* COGt *) try wp_auto. reject.
    + (* COGe *) try wp_auto. reject.
    + (* CONeg *) try wp_auto. reject.
    + (* CONot *) try wp_auto. reject.
  - (* CTyPtr: the sort is not SortInt, so only OpEq is accepted *)
    rewrite (apply_binop_nonint o (CTyPtr cel) u w); last done.
    cbn [ctype_sort sort_code].
    destruct o; cbn [op_code].
    + (* COAdd *) try wp_auto. reject.
    + (* COSub *) try wp_auto. reject.
    + (* COMul *) try wp_auto. reject.
    + (* COEq *) try wp_auto. alloc_term lr.
    + (* COLt *) try wp_auto. reject.
    + (* COLe *) try wp_auto. reject.
    + (* COGt *) try wp_auto. reject.
    + (* COGe *) try wp_auto. reject.
    + (* CONeg *) try wp_auto. reject.
    + (* CONot *) try wp_auto. reject.
Qed.

End proof.
