(** [checker.assnPure] (checker/check.go): the pure atoms of an assertion,
    left to right.

    Note on naming: no Rocq variable here may be called [a] or [out], the
    names of the Go function's own locals, because [wp_auto] derives Rocq
    identifiers from the Go names. *)
From New.checker Require Import prelude nodes.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Fixpoint cassn_pure (x : cassn) : list term :=
  match x with
  | CASep p q => cassn_pure p ++ cassn_pure q
  | CAPure t => [t]
  | _ => []
  end.

Definition oassn_pure (x : option cassn) : list term :=
  match x with None => [] | Some x' => cassn_pure x' end.

Lemma is_cond_nil : ⊢ is_cond slice.nil [].
Proof. iExists []. iSplit; [iApply own_slice_nil | done]. Qed.

(** Appending onto the nil slice: the Go code starts [out] at nil and appends
    to it, and [wp_slice_append]'s two [own_slice]s are ambiguous enough that
    [iFrame] picks the wrong one unless both slices are named variables. *)
Lemma wp_append_nil (s2 : slice.t) (ls : list loc) Φ :
  s2 ↦* ls -∗
  (∀ s' : slice.t,
     s' ↦* ls ∗ own_slice_cap loc s' (DfracOwn 1) -∗ Φ #s') -∗
  WP #(functions go.append [go.SliceType (go.PointerType checker.Term)])
       #slice.nil #s2 {{ Φ }}.
Proof.
  iIntros "Hs2 HΦ".
  iDestruct (own_slice_nil (V:=loc) (DfracOwn 1)) as "Hnil".
  iDestruct (own_slice_cap_nil (V:=loc)) as "Hnilc".
  wp_apply (wp_slice_append slice.nil [] s2 ls (DfracOwn 1)
             with "[$Hnil $Hnilc $Hs2]") as (s') "(Hs' & Hs'c & _)".
  iApply "HΦ". iFrame.
Qed.

Lemma wp_assnPure (l : loc) (x : option cassn) :
  {{{ is_pkg_init checker ∗ is_oassn l x }}}
    @! checker.assnPure #l
  {{{ (s : slice.t), RET #s;
      is_cond s (oassn_pure x) ∗ own_slice_cap loc s (DfracOwn 1) }}}.
Proof.
  iLöb as "IH" forall (l x).
  wp_start as "#Hx".
  iDestruct (is_oassn_null with "Hx") as %Hn.
  wp_auto.
  wp_if_destruct.
  - (* the argument is nil: no pure atoms *)
    assert (x = None) as -> by naive_solver.
    iApply "HΦ". iSplitR; [iApply is_cond_nil | iApply own_slice_cap_nil].
  - destruct x as [x'|]; last naive_solver.
    iDestruct (is_assn_node with "Hx")
      as (lL lR lX lY) "(%Hwf & #Hnode & #HL & #HR & #HX & #HY)".
    destruct x'; simpl.
    + (* CAEmp *)
      try wp_auto.
      iApply "HΦ". iSplitR; [iApply is_cond_nil | iApply own_slice_cap_nil].
    + (* CASep: the left atoms, then the right ones *)
      try wp_auto.
      wp_apply ("IH" $! lL (Some x'1) with "[$]") as (s1) "[Hp1 _]".
      iDestruct "Hp1" as (ls1) "[Hs1 #Hc1]".
      wp_apply (wp_append_nil with "Hs1").
      iIntros (s2) "[Hs2 Hs2c]".
      try wp_auto.
      wp_apply ("IH" $! lR (Some x'2) with "[$]") as (s3) "[Hp3 _]".
      iDestruct "Hp3" as (ls3) "[Hs3 #Hc3]".
      wp_apply (wp_slice_append s2 ls1 s3 ls3 (DfracOwn 1)
                 with "[$Hs2 $Hs2c $Hs3]") as (s4) "(Hs4 & Hs4c & _)".
      try wp_auto.
      iApply "HΦ". iFrame "Hs4c". iExists _. iFrame "Hs4".
      iApply (big_sepL2_app with "Hc1 Hc3").
    + (* CAOr *)
      try wp_auto.
      iApply "HΦ". iSplitR; [iApply is_cond_nil | iApply own_slice_cap_nil].
    + (* CAExists *)
      try wp_auto.
      iApply "HΦ". iSplitR; [iApply is_cond_nil | iApply own_slice_cap_nil].
    + (* CAPure: the one atom *)
      try wp_auto.
      wp_apply wp_slice_literal.
      iSplitR; first done.
      iIntros "% [Hsl Hslc]".
      wp_auto.
      wp_apply (wp_append_nil with "Hsl").
      iIntros (s2) "[Hs2 Hs2c]".
      try wp_auto.
      iApply "HΦ". iFrame "Hs2c". iExists _. iFrame "Hs2".
      simpl. iFrame "HX". done.
    + (* CAPointsTo *)
      try wp_auto.
      iApply "HΦ". iSplitR; [iApply is_cond_nil | iApply own_slice_cap_nil].
  (* [wp_slice_literal] leaves the element type of the literal as a shelved
     evar; it is the pointer-to-[Term] type. *)
  Unshelve.
  all: first [ exact (go.PointerType checker.Term) | apply _ ].
Qed.

End proof.
