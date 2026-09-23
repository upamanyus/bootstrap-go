(** [checker.applyUnOp] (checker/exec.go): the term for a unary Go operator at
    a type, after checking that the operand's sort is the type's.

    Note on naming: no Rocq variable here may be called [op], [t], [vars],
    [a], [tok], [ts], [sa] or [oka] -- those are the Go function's own locals
    and [wp_auto] derives Rocq identifiers from the Go names (see NOTES.md).
    The operator is therefore [o], the type [cty], the slice of variable sorts
    [sv] and the operand [u]. *)
From New.checker Require Import prelude nodes.
From New.checker.fn Require Import TypeSort typeSigned sortOfEnv SortOf.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.

Set Default Proof Using "All".

(** The Go code compares sorts by their codes, the mirrors by [decide]; the
    two agree because the encoding is injective. *)
Lemma sort_code_inj' s1 s2 : sort_code s1 = sort_code s2 -> s1 = s2.
Proof. destruct s1, s2; try done; intros Hc; exfalso; revert Hc; by vm_compute. Qed.

(** Whether the Go function's second result is [true]. *)
Definition oterm_ok (ot : option term) : bool :=
  match ot with Some _ => true | None => false end.

(** The Gallina mirror of the whole function: the sort check of [applyUnOp],
    then the term-building half, which is [apply_unop] in steps.v. *)
Definition unop_result (o : cop) (cty : ctype) (vl : list sort)
    (ox : option term) : option term :=
  match ox with
  | None => None
  | Some u => if decide (sort_of_vars vl u = Some (ctype_sort cty))
              then apply_unop o cty u else None
  end.

Lemma unop_result_bad o cty vl u :
  sort_of_vars vl u ≠ Some (ctype_sort cty) → unop_result o cty vl (Some u) = None.
Proof. intros Hne. rewrite /unop_result /=. by rewrite decide_False. Qed.

Lemma unop_result_good o cty vl u :
  sort_of_vars vl u = Some (ctype_sort cty) →
  unop_result o cty vl (Some u) = apply_unop o cty u.
Proof. intros Heq. rewrite /unop_result /=. by rewrite decide_True. Qed.

Local Ltac reject := iApply ("HΦ" $! null false); by iFrame.

Lemma wp_applyUnOp (o : cop) (lty : loc) (cty : ctype)
      (sv : slice.t) (vl : list sort) (lx : loc) (ox : option term) :
  {{{ is_pkg_init checker ∗ is_type lty cty ∗
      sv ↦*□ (sort_code <$> vl) ∗ is_oterm lx ox }}}
    @! checker.applyUnOp #(op_code o) #lty #sv #lx
  {{{ (lr : loc) (ok : bool), RET (#lr, #ok);
      ⌜ok = oterm_ok (unop_result o cty vl ox)⌝ ∗
      is_oterm lr (unop_result o cty vl ox) }}}.
Proof.
  wp_start as "(#Hty & #Hsv & #Hx)".
  wp_auto.
  wp_apply (wp_TypeSort lty (Some cty) with "[$]").
  try wp_auto.
  wp_apply (wp_SortOf sv lx vl ox with "[$]").
  try wp_auto.
  destruct ox as [u|]; cbn [osort_of osort_code osort_ok].
  2: { (* the operand is nil: [SortOf] rejects it *)
    try wp_auto. reject. }
  fold (sort_of_vars vl u).
  destruct (sort_of_vars vl u) as [s1|] eqn:Hs; cbn [osort_code osort_ok].
  2: { (* the operand is ill-sorted *)
    try wp_auto.
    rewrite (unop_result_bad o cty vl u); last by rewrite Hs.
    reject. }
  destruct (decide (s1 = ctype_sort cty)) as [->|Hne].
  2: { (* the operand's sort is not the type's *)
    try wp_auto.
    wp_if_destruct.
    { exfalso. by apply sort_code_inj' in e. }
    rewrite (unop_result_bad o cty vl u); last by rewrite Hs; intros [= ?].
    reject. }
  (* the sort check passed *)
  rewrite (unop_result_good o cty vl u) //.
  try wp_auto.
  rewrite bool_decide_eq_true_2 //.
  try wp_auto.
  destruct o; cbn [op_code apply_unop].
  1-8: (* a binary operator: neither [if] matches *)
    try wp_auto; reject.
  - (* CONeg: unary minus, only at the signed integer types *)
    destruct cty; cbn [ctype_sort sort_code ctype_signed].
    + (* int *)
      try wp_auto.
      wp_apply (wp_typeSigned lty CTyInt with "[$]").
      try wp_auto.
      iApply wp_fupd. wp_alloc lr as "Hr". try wp_auto. iPersist "Hr".
      iModIntro. iApply ("HΦ" $! lr true). iSplit; first done.
      simpl. iFrame "Hr Hx".
    + (* int64 *)
      try wp_auto.
      wp_apply (wp_typeSigned lty CTyInt64 with "[$]").
      try wp_auto.
      iApply wp_fupd. wp_alloc lr as "Hr". try wp_auto. iPersist "Hr".
      iModIntro. iApply ("HΦ" $! lr true). iSplit; first done.
      simpl. iFrame "Hr Hx".
    + (* uint64: unsigned, so GooseLang has no [GoNeg] here and the Go code
         rejects it (see NOTES.md) *)
      try wp_auto.
      wp_apply (wp_typeSigned lty CTyUint64 with "[$]").
      try wp_auto. reject.
    + (* bool: the sort is not SortInt *)
      try wp_auto. reject.
    + (* pointer: the sort is not SortInt *)
      try wp_auto. reject.
  - (* CONot: logical negation, only at bool *)
    destruct cty; cbn [ctype_sort sort_code ctype_signed];
      try (try wp_auto; reject).
    (* bool *)
    try wp_auto.
    iApply wp_fupd. wp_alloc lr as "Hr". try wp_auto. iPersist "Hr".
    iModIntro. iApply ("HΦ" $! lr true). iSplit; first done.
    simpl. iFrame "Hr Hx".
Qed.

End proof.
