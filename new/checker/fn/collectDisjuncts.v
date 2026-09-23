(** [checker.collectDisjuncts] (checker/match.go): the top-level disjunction
    of a postcondition, flattened left to right.

    An assertion that is not an [AOr] is a single disjunct -- and so is nil,
    which the Go code appends unchanged, so the mirror is over
    [option cassn] and returns a list of [option cassn].

    Naming: the Go locals are [a] and [out], so no Rocq variable here is
    called either (see NOTES.md). *)
From New.checker Require Import prelude nodes.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All - package_sem".

Fixpoint assn_disjuncts (x : cassn) : list (option cassn) :=
  match x with
  | CAOr p q => assn_disjuncts p ++ assn_disjuncts q
  | _ => [Some x]
  end.

Definition oassn_disjuncts (x : option cassn) : list (option cassn) :=
  match x with None => [None] | Some x' => assn_disjuncts x' end.

(** The slice of [*Assn] the function returns. *)
Definition is_assns (s : slice.t) (xs : list (option cassn)) : iProp Σ :=
  (∃ ls : list loc, s ↦* ls ∗ own_slice_cap loc s (DfracOwn 1) ∗
                    [∗ list] l;y ∈ ls; xs, is_oassn l y)%I.

(** Appending onto the nil slice: [out] starts at nil, and
    [wp_slice_append]'s two [own_slice]s are ambiguous enough that [iFrame]
    picks the wrong one unless both slices are named variables (as in
    assnHeap.v). *)
Lemma wp_append_nil (s2 : slice.t) (vs : list loc) Φ :
  s2 ↦* vs -∗
  (∀ s' : slice.t,
     s' ↦* vs ∗ own_slice_cap loc s' (DfracOwn 1) -∗ Φ #s') -∗
  WP #(functions go.append [go.SliceType (go.PointerType checker.Assn)]) #slice.nil #s2 {{ Φ }}.
Proof using All.
  iIntros "Hs2 HΦ".
  iDestruct (own_slice_nil (V:=loc) (DfracOwn 1)) as "Hnil".
  iDestruct (own_slice_cap_nil (V:=loc)) as "Hnilc".
  wp_apply (wp_slice_append slice.nil [] s2 vs (DfracOwn 1)
             with "[$Hnil $Hnilc $Hs2]") as (s') "(Hs' & Hs'c & _)".
  iApply "HΦ". iFrame.
Qed.

Lemma wp_collectDisjuncts (la : loc) (x : option cassn) :
  {{{ is_pkg_init checker ∗ is_oassn la x }}}
    @! checker.collectDisjuncts #la
  {{{ (s : slice.t), RET #s; is_assns s (oassn_disjuncts x) }}}.
Proof using All.
  iLöb as "IH" forall (la x).
  wp_start as "#Hx".
  iDestruct (is_oassn_null with "Hx") as %Hnull.
  wp_auto.
  destruct x as [x'|]; last first.
  { (* nil: the singleton [nil] *)
    assert (la = null) as Hla by (apply Hnull; reflexivity). subst la.
    try wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "% [Hsl Hslc]".
    try wp_auto.
    wp_apply (wp_append_nil with "Hsl").
    iIntros (s') "[Hs' Hs'c]".
    try wp_auto.
    iApply "HΦ". iExists [null]. iFrame "Hs' Hs'c". simpl. by iFrame "Hx". }
  iDestruct (is_assn_node with "Hx")
    as (lL lR lX lY) "(%Hwf & #Hnode & #HL & #HR & #HX & #HY)".
  iDestruct (is_assn_not_null with "Hx") as %?.
  destruct x'; simpl.
  - (* CAEmp *)
    wp_if_destruct; first congruence.
    try wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "% [Hsl Hslc]".
    try wp_auto.
    wp_apply (wp_append_nil with "Hsl").
    iIntros (s') "[Hs' Hs'c]".
    try wp_auto.
    iApply "HΦ". iExists [la]. iFrame "Hs' Hs'c". simpl. by iFrame "Hx".
  - (* CASep *)
    wp_if_destruct; first congruence.
    try wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "% [Hsl Hslc]".
    try wp_auto.
    wp_apply (wp_append_nil with "Hsl").
    iIntros (s') "[Hs' Hs'c]".
    try wp_auto.
    iApply "HΦ". iExists [la]. iFrame "Hs' Hs'c". simpl. by iFrame "Hx".
  - (* CAOr: the left chain, then the right one *)
    wp_if_destruct; first congruence.
    try wp_auto.
    wp_apply ("IH" $! lL (Some x'1) with "[$]") as (s1) "Hs1".
    iDestruct "Hs1" as (ls1) "(Hs1 & _ & #Hd1)".
    wp_apply (wp_append_nil with "Hs1").
    iIntros (s2) "[Hs2 Hs2c]".
    try wp_auto.
    wp_apply ("IH" $! lR (Some x'2) with "[$]") as (s3) "Hs3".
    iDestruct "Hs3" as (ls3) "(Hs3 & _ & #Hd3)".
    wp_apply (wp_slice_append s2 ls1 s3 ls3 (DfracOwn 1)
               with "[$Hs2 $Hs2c $Hs3]") as (s4) "(Hs4 & Hs4c & _)".
    try wp_auto.
    iApply "HΦ". iExists (ls1 ++ ls3). iFrame "Hs4 Hs4c".
    iApply (big_sepL2_app with "Hd1 Hd3").
  - (* CAExists *)
    wp_if_destruct; first congruence.
    try wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "% [Hsl Hslc]".
    try wp_auto.
    wp_apply (wp_append_nil with "Hsl").
    iIntros (s') "[Hs' Hs'c]".
    try wp_auto.
    iApply "HΦ". iExists [la]. iFrame "Hs' Hs'c". simpl. by iFrame "Hx".
  - (* CAPure *)
    wp_if_destruct; first congruence.
    try wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "% [Hsl Hslc]".
    try wp_auto.
    wp_apply (wp_append_nil with "Hsl").
    iIntros (s') "[Hs' Hs'c]".
    try wp_auto.
    iApply "HΦ". iExists [la]. iFrame "Hs' Hs'c". simpl. by iFrame "Hx".
  - (* CAPointsTo *)
    wp_if_destruct; first congruence.
    try wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "% [Hsl Hslc]".
    try wp_auto.
    wp_apply (wp_append_nil with "Hsl").
    iIntros (s') "[Hs' Hs'c]".
    try wp_auto.
    iApply "HΦ". iExists [la]. iFrame "Hs' Hs'c". simpl. by iFrame "Hx".
  Unshelve.
  all: first [ exact (go.PointerType checker.Assn) | apply _ ].
Qed.

End proof.
