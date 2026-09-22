(** [checker.assnHeap] (checker/check.go): the points-to atoms of an
    assertion, left to right.

    Note on naming: no Rocq variable here may be called [a] or [out], the
    names of the Go function's own locals, because [wp_auto] derives Rocq
    identifiers from the Go names. *)
From New.checker Require Import prelude nodes.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Fixpoint cassn_heap (x : cassn) : list scell :=
  match x with
  | CASep p q => cassn_heap p ++ cassn_heap q
  | CAPointsTo lx ly => [mkCell lx ly]
  | _ => []
  end.

Definition oassn_heap (x : option cassn) : list scell :=
  match x with None => [] | Some x' => cassn_heap x' end.

Lemma is_heap_nil : ⊢ is_heap slice.nil [].
Proof. iExists []. iSplit; [iApply own_slice_nil | done]. Qed.

(** Appending onto the nil slice: the Go code starts [out] at nil and appends
    to it, and [wp_slice_append]'s two [own_slice]s are ambiguous enough that
    [iFrame] picks the wrong one unless both slices are named variables. *)
Lemma wp_append_nil (s2 : slice.t) (vs : list checker.Cell.t) Φ :
  s2 ↦* vs -∗
  (∀ s' : slice.t,
     s' ↦* vs ∗ own_slice_cap checker.Cell.t s' (DfracOwn 1) -∗ Φ #s') -∗
  WP #(functions go.append [go.SliceType checker.Cell]) #slice.nil #s2 {{ Φ }}.
Proof.
  iIntros "Hs2 HΦ".
  iDestruct (own_slice_nil (V:=checker.Cell.t) (DfracOwn 1)) as "Hnil".
  iDestruct (own_slice_cap_nil (V:=checker.Cell.t)) as "Hnilc".
  wp_apply (wp_slice_append slice.nil [] s2 vs (DfracOwn 1)
             with "[$Hnil $Hnilc $Hs2]") as (s') "(Hs' & Hs'c & _)".
  iApply "HΦ". iFrame.
Qed.

Lemma wp_assnHeap (l : loc) (x : option cassn) :
  {{{ is_pkg_init checker ∗ is_oassn l x }}}
    @! checker.assnHeap #l
  {{{ (s : slice.t), RET #s;
      is_heap s (oassn_heap x) ∗ own_slice_cap checker.Cell.t s (DfracOwn 1) }}}.
Proof.
  iLöb as "IH" forall (l x).
  wp_start as "#Hx".
  iDestruct (is_oassn_null with "Hx") as %Hn.
  wp_auto.
  wp_if_destruct.
  - (* the argument is nil: the empty heap *)
    assert (x = None) as -> by naive_solver.
    iApply "HΦ". iSplitR; [iApply is_heap_nil | iApply own_slice_cap_nil].
  - destruct x as [x'|]; last naive_solver.
    iDestruct (is_assn_node with "Hx")
      as (lL lR lX lY) "(%Hwf & #Hnode & #HL & #HR & #HX & #HY)".
    destruct x'; simpl.
    + (* CAEmp *)
      try wp_auto.
      iApply "HΦ". iSplitR; [iApply is_heap_nil | iApply own_slice_cap_nil].
    + (* CASep: the left heap, then the right one *)
      try wp_auto.
      wp_apply ("IH" $! lL (Some x'1) with "[$]") as (s1) "[Hh1 _]".
      iDestruct "Hh1" as (cs1) "[Hs1 #Hc1]".
      wp_apply (wp_append_nil with "Hs1").
      iIntros (s2) "[Hs2 Hs2c]".
      try wp_auto.
      wp_apply ("IH" $! lR (Some x'2) with "[$]") as (s3) "[Hh3 _]".
      iDestruct "Hh3" as (cs3) "[Hs3 #Hc3]".
      wp_apply (wp_slice_append s2 cs1 s3 cs3 (DfracOwn 1)
                 with "[$Hs2 $Hs2c $Hs3]") as (s4) "(Hs4 & Hs4c & _)".
      try wp_auto.
      iApply "HΦ". iFrame "Hs4c". iExists _. iFrame "Hs4".
      iApply (big_sepL2_app with "Hc1 Hc3").
    + (* CAOr *)
      try wp_auto.
      iApply "HΦ". iSplitR; [iApply is_heap_nil | iApply own_slice_cap_nil].
    + (* CAExists *)
      try wp_auto.
      iApply "HΦ". iSplitR; [iApply is_heap_nil | iApply own_slice_cap_nil].
    + (* CAPure *)
      try wp_auto.
      iApply "HΦ". iSplitR; [iApply is_heap_nil | iApply own_slice_cap_nil].
    + (* CAPointsTo: the one cell *)
      try wp_auto.
      wp_apply wp_slice_literal.
      iSplitR; first done.
      iIntros "% [Hsl Hslc]".
      wp_auto.
      wp_apply (wp_append_nil with "Hsl").
      iIntros (s2) "[Hs2 Hs2c]".
      try wp_auto.
      iApply "HΦ". iFrame "Hs2c". iExists _. iFrame "Hs2".
      simpl. iFrame "HX HY". done.
  (* [wp_slice_literal] leaves the element type of the literal as a shelved
     evar; it is the [Cell] struct. *)
  Unshelve.
  all: first [ exact checker.Cell | apply _ ].
Qed.

End proof.
