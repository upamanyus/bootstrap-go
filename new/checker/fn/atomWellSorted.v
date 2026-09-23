(** [checker.atomWellSorted] (checker/match.go): the sort check for a single
    atom of a postcondition's disjunct.

    An atom passes exactly when it is a pure assertion whose term has sort
    [SBool], or a points-to whose location term has sort [SLoc] and whose
    value term has a sort at all. Every other kind -- and the nil pointer --
    is rejected with a freshly allocated [Failure]; the specification says
    nothing about the failure's contents, only that the returned pointer is
    non-nil, which is what every caller tests.

    Naming: the Go locals are [se], [a], [s], [ok] and [ok2], so no Rocq
    variable here may be called any of those (see NOTES.md). *)
From New.checker Require Import prelude nodes.
From New.checker.fn Require Import sortOfEnv.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The mirror. [None] stands for the nil [*Assn], which is rejected. *)
Definition atom_well_sorted (E : sort_env) (oa : option cassn) : bool :=
  match oa with
  | Some (CAPure x) =>
      match sort_of E x with Some SBool => true | _ => false end
  | Some (CAPointsTo x v) =>
      match sort_of E x, sort_of E v with
      | Some SLoc, Some _ => true
      | _, _ => false
      end
  | _ => false
  end.

Local Ltac reject :=
  try wp_auto;
  let lf := fresh "lf" in
  wp_alloc lf as "Hf"; try wp_auto;
  iDestruct (typed_pointsto_not_null with "Hf") as %Hnn;
  iApply "HΦ"; iFrame; iPureIntro; naive_solver.

Lemma wp_atomWellSorted (dq : dfrac) (lse la : loc) (E : sort_env) (oa : option cassn) :
  {{{ is_pkg_init checker ∗ is_sortenv dq lse E ∗ is_oassn la oa ∗ ⌜sort_env_wf E⌝ }}}
    @! checker.atomWellSorted #lse #la
  {{{ (lf : loc), RET #lf;
      is_sortenv dq lse E ∗ ⌜(lf = null) ↔ atom_well_sorted E oa = true⌝ }}}.
Proof.
  wp_start as "(Henv & #Hoa & %Hwf)".
  iDestruct (is_oassn_null with "Hoa") as %Hnull.
  wp_auto.
  wp_if_destruct.
  { (* the atom pointer is nil *)
    assert (oa = None) as -> by naive_solver. reject. }
  destruct oa as [aa|]; last naive_solver.
  iDestruct (is_assn_node with "Hoa") as (lL lR lX lY)
    "(%Hidx & #Hnode & #HL & #HR & #HX & #HY)".
  destruct aa as [|x1 x2|x1 x2|nn srt x1|x1|x1 x2];
    cbn [assn_code assn_l assn_r assn_x assn_y assn_var assn_sort] in *.
  - (* CAEmp *) reject.
  - (* CASep *) reject.
  - (* CAOr *) reject.
  - (* CAExists *) reject.
  - (* CAPure *)
    wp_auto.
    wp_apply (wp_sortOfEnv dq lse lX E (Some x1) with "[$Henv $HX]") as "Henv".
    { done. }
    cbn [osort_of osort_code osort_ok atom_well_sorted].
    destruct (sort_of E x1) as [[| | |]|]; cbn [osort_code osort_ok sort_code].
    + (* SInt *) reject.
    + (* SBool: accepted *)
      wp_auto. iApply "HΦ". iFrame. iPureIntro. naive_solver.
    + (* SLoc *) reject.
    + (* SUnit *) reject.
    + (* no sort *) reject.
  - (* CAPointsTo *)
    wp_auto.
    wp_apply (wp_sortOfEnv dq lse lX E (Some x1) with "[$Henv $HX]") as "Henv".
    { done. }
    cbn [osort_of osort_code osort_ok atom_well_sorted].
    destruct (sort_of E x1) as [[| | |]|]; cbn [osort_code osort_ok sort_code].
    + (* SInt *) reject.
    + (* SBool *) reject.
    + (* SLoc: the location is fine; the value must have some sort *)
      wp_auto.
      wp_apply (wp_sortOfEnv dq lse lY E (Some x2) with "[$Henv $HY]") as "Henv".
      { done. }
      cbn [osort_of osort_code osort_ok].
      destruct (sort_of E x2) as [s2|]; cbn [osort_code osort_ok].
      * wp_auto. iApply "HΦ". iFrame. iPureIntro. naive_solver.
      * reject.
    + (* SUnit *) reject.
    + (* no sort *) reject.
Qed.

End proof.
