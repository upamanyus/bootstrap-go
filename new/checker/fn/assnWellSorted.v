(** [checker.assnWellSorted] (checker/check.go): the sort check of a
    precondition. [emp] and [∗] are traversed, the two atoms go to
    [atomWellSorted], and every other form (and nothing else) is rejected.

    Naming: the Go locals are [se], [a] and [fl], so no Rocq variable here may
    be called any of those (see NOTES.md). *)
From New.checker Require Import prelude nodes.
From New.checker.fn Require Import atomWellSorted.

(** The mirror. [None] is the nil [*Assn], which is accepted (as [emp]). *)
Fixpoint cassn_ws (E : sort_env) (x : cassn) : bool :=
  match x with
  | CAEmp => true
  | CASep p q => cassn_ws E p && cassn_ws E q
  | CAPure t => match sort_of E t with Some SBool => true | _ => false end
  | CAPointsTo x v =>
      match sort_of E x, sort_of E v with
      | Some SLoc, Some _ => true
      | _, _ => false
      end
  | _ => false
  end.

Definition oassn_ws (E : sort_env) (x : option cassn) : bool :=
  match x with None => true | Some x' => cassn_ws E x' end.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All - package_sem".

Local Ltac reject :=
  try wp_auto;
  let lf := fresh "lf" in
  wp_alloc lf as "Hf"; try wp_auto;
  iDestruct (typed_pointsto_not_null with "Hf") as %Hnn;
  iApply "HΦ"; iFrame; iPureIntro; naive_solver.

Lemma wp_assnWellSorted (dq : dfrac) (lse la : loc) (E : sort_env) (oa : option cassn) :
  {{{ is_pkg_init checker ∗ is_sortenv dq lse E ∗ is_oassn la oa ∗ ⌜sort_env_wf E⌝ }}}
    @! checker.assnWellSorted #lse #la
  {{{ (lf : loc), RET #lf;
      is_sortenv dq lse E ∗ ⌜(lf = null) ↔ oassn_ws E oa = true⌝ }}}.
Proof using All.
  iLöb as "IH" forall (la oa).
  wp_start as "(Henv & #Hoa & %Hwf)".
  iDestruct (is_oassn_null with "Hoa") as %Hnull.
  wp_auto.
  wp_if_destruct.
  { (* nil *)
    assert (oa = None) as -> by naive_solver.
    iApply "HΦ". iFrame. iPureIntro. naive_solver. }
  destruct oa as [aa|]; last naive_solver.
  iDestruct (is_assn_node with "Hoa") as (lL lR lX lY)
    "(%Hidx & #Hnode & #HL & #HR & #HX & #HY)".
  destruct aa as [|x1 x2|x1 x2|nn srt x1|x1|x1 x2];
    cbn [assn_code assn_l assn_r assn_x assn_y assn_var assn_sort] in *.
  - (* CAEmp *)
    wp_auto. iApply "HΦ". iFrame. iPureIntro. naive_solver.
  - (* CASep *)
    wp_auto.
    wp_apply ("IH" $! lL (Some x1) with "[$Henv]") as (lf1) "[Henv %Hlf1]".
    { iFrame "#". done. }
    wp_if_destruct.
    + (* the left half passed *)
      wp_apply ("IH" $! lR (Some x2) with "[$Henv]") as (lf2) "[Henv %Hlf2]".
      { iFrame "#". done. }
      try wp_auto.
      iApply "HΦ". iFrame. iPureIntro. cbn [oassn_ws cassn_ws] in *.
      destruct (cassn_ws E x1); naive_solver.
    + (* the left half failed *)
      iApply "HΦ". iFrame. iPureIntro. cbn [oassn_ws cassn_ws] in *.
      destruct (cassn_ws E x1); naive_solver.
  - (* CAOr *) reject.
  - (* CAExists *) reject.
  - (* CAPure *)
    wp_auto.
    wp_apply (wp_atomWellSorted dq lse la E (Some (CAPure x1)) with "[$Henv]")
      as (lf1) "[Henv %Hlf1]".
    { iFrame "Hoa". iFrame "#". done. }
    try wp_auto.
    iApply "HΦ". iFrame. done.
  - (* CAPointsTo *)
    wp_auto.
    wp_apply (wp_atomWellSorted dq lse la E (Some (CAPointsTo x1 x2)) with "[$Henv]")
      as (lf1) "[Henv %Hlf1]".
    { iFrame "Hoa". iFrame "#". done. }
    try wp_auto.
    iApply "HΦ". iFrame. done.
Qed.

End proof.
