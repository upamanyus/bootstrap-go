(** [checker.binOpAll] (checker/exec.go): apply the operator of an [EBinOp]
    node, with left operand [a], to each of the paths the right operand
    reached. Each result path keeps the state of its input path and returns
    the term [applyBinOp] built (which checks both operands' sorts against
    that state's sort table); an ill-sorted operand makes the whole call
    fail.

    Note on naming: no Rocq variable here may be called [e], [a], [ps],
    [out], [q], [ok], [v] or [i], because those are the names of the Go
    function's own locals and [wp_auto] derives Rocq identifiers from them. *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_b.
From New.checker.fn Require Import applyBinOp.

(** How an input path and its output path are related. *)
Definition binop_path (o : cop) (cty : ctype) (ta : term) (sq sp : spath) : Prop :=
  ∃ r, sort_of_vars (svars (pst sq)) ta = Some (ctype_sort cty) ∧
       sort_of_vars (svars (pst sq)) (pret sq) = Some (ctype_sort cty) ∧
       apply_binop o cty ta (pret sq) = Some r ∧ sp = mkPath r (pst sq).

Lemma binop_result_some o cty vl u w r :
  binop_result o cty vl (Some u) (Some w) = Some r →
  sort_of_vars vl u = Some (ctype_sort cty) ∧ sort_of_vars vl w = Some (ctype_sort cty) ∧
  apply_binop o cty u w = Some r.
Proof.
  rewrite /binop_result. destruct (decide _) as [[H1 H2]|]; last done. by intros.
Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** Every input path has its result among the outputs. *)
Lemma binop_paths_in o cty ta qs outs big :
  Forall2 (binop_path o cty ta) qs outs → outs ⊆ big →
  ∀ sq, sq ∈ qs → ∃ r,
    sort_of_vars (svars (pst sq)) ta = Some (ctype_sort cty) ∧
    sort_of_vars (svars (pst sq)) (pret sq) = Some (ctype_sort cty) ∧
    apply_binop o cty ta (pret sq) = Some r ∧ mkPath r (pst sq) ∈ big.
Proof.
  intros HF Hsub sq Hin.
  apply list_elem_of_lookup in Hin as [j Hj].
  destruct (Forall2_lookup_l _ _ _ _ _ HF Hj) as (sp & Hsp & r & H1 & H2 & H3 & ->).
  exists r. split_and!; try done.
  apply Hsub. by eapply list_elem_of_lookup_2.
Qed.

(** The outputs are well formed, given that the inputs are and the left
    operand is scoped by the state it was computed in. *)
Lemma binop_paths_wf o cty ta qs outs k k' :
  (k ≤ k')%nat → vars_below k' ta → paths_wf k' qs →
  Forall2 (binop_path o cty ta) qs outs → paths_wf k outs.
Proof.
  intros Hle Hta Hwf HF.
  assert (∀ sp, sp ∈ outs → ∃ sq, sq ∈ qs ∧ binop_path o cty ta sq sp) as Hback.
  { intros sp Hin. apply list_elem_of_lookup in Hin as [j Hj].
    destruct (Forall2_lookup_r _ _ _ _ _ HF Hj) as (sq & Hsq & HR).
    exists sq. split; last done. by eapply list_elem_of_lookup_2. }
  split.
  - intros sp (sq & Hin & r & _ & _ & _ & ->)%Hback. simpl. by apply (paths_wf_state _ _ Hwf).
  - intros sp (sq & Hin & r & _ & _ & _ & ->)%Hback. simpl.
    pose proof (paths_wf_grow _ _ Hwf sq Hin). lia.
  - intros sp (sq & Hin & r & _ & _ & Hr & ->)%Hback. simpl.
    eapply apply_binop_below; first done.
    + eapply vars_below_mono; last done. by apply (paths_wf_grow _ _ Hwf).
    + by apply (paths_wf_ret _ _ Hwf).
Qed.

Lemma wp_binOpAll (le lta : loc) (o : cop) (cty : ctype) (ce1 ce2 : cexpr)
      (ta : term) (s : slice.t) (qs0 : list spath) :
  {{{ is_pkg_init checker ∗ is_expr le (CEBinOp o cty ce1 ce2) ∗ is_term lta ta ∗
      is_paths s qs0 }}}
    @! checker.binOpAll #le #lta #s
  {{{ (s' : slice.t) (lf : loc), RET (#s', #lf);
      if decide (lf = null) then
        ∃ outs, is_paths s' outs ∗ ⌜Forall2 (binop_path o cty ta) qs0 outs⌝
      else True }}}.
Proof.
  wp_start as "(#He & #Hta & Hps)".
  iDestruct "He" as (lty la lb) "(#Hnode & #Hty & _ & _)".
  iDestruct "Hps" as (xs) "[Hs Hxs]".
  iDestruct (big_sepL2_length with "Hxs") as %Hlen2.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  wp_auto.
  iAssert (∃ (n : w64) (cur : checker.Path.t) (so : slice.t)
             (ys : list checker.Path.t) (outs : list spath),
      "i" ∷ i_ptr ↦ n ∗
      "q" ∷ q_ptr ↦ cur ∗
      "out" ∷ out_ptr ↦ so ∗
      "Hys" ∷ so ↦* ys ∗
      "Hcap" ∷ own_slice_cap checker.Path.t so (DfracOwn 1) ∗
      "Hysp" ∷ ([∗ list] y;sp ∈ ys;outs, is_path y sp) ∗
      "Hrest" ∷ ([∗ list] x;sq ∈ drop (sint.nat n) xs; drop (sint.nat n) qs0, is_path x sq) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ≤ length xs⌝ ∗
      "%HF" ∷ ⌜Forall2 (binop_path o cty ta) (take (sint.nat n) qs0) outs⌝)%I
    with "[i q out Hxs]" as "HI".
  { iExists (W64 0), _, slice.nil, [], []. iFrame "i q out".
    iDestruct (own_slice_nil (V:=checker.Path.t) (DfracOwn 1)) as "$".
    iDestruct (own_slice_cap_nil (V:=checker.Path.t)) as "$".
    iSplit; first by iApply big_sepL2_nil.
    replace (sint.nat (W64 0)) with 0%nat by word.
    rewrite !drop_0 take_0. iFrame "Hxs". iPureIntro.
    split; [word|constructor]. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem xs (sint.nat n) as xp.
    list_elem qs0 (sint.nat n) as sq.
    wp_apply (wp_load_slice_index with "[$Hs]").
    { word. }
    { done. }
    iIntros "Hs".
    rewrite (drop_S xs xp (sint.nat n)) // (drop_S qs0 sq (sint.nat n)) //.
    iDestruct "Hrest" as "[[#Hret Hst'] Hrest]".
    iDestruct "Hst'" as (hs cs vs) "(Hstl & Hheap & Hcond & #Hvars)".
    wp_auto.
    wp_apply (wp_applyBinOp o lty cty vs (svars (pst sq)) _ _ (Some ta) (Some (pret sq))
               with "[$Hty $Hvars $Hta $Hret]").
    iIntros (lv okb) "(%Hok & #Hlv)".
    destruct (binop_result o cty (svars (pst sq)) (Some ta) (Some (pret sq)))
      as [y|] eqn:Hbr.
    2:{ (* ill-sorted *)
      simpl in Hok. subst okb.
      wp_auto.
      wp_alloc lfail as "Hlf".
      iDestruct (typed_pointsto_not_null with "Hlf") as %Hnn.
      wp_auto.
      wp_for_post.
      iApply "HΦ". by rewrite decide_False. }
    simpl in Hok. subst okb.
    destruct (binop_result_some _ _ _ _ _ _ Hbr) as (Hs1 & Hs2 & Hr).
    wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sl [Hsl _]".
    replace (Z.to_nat (sint.Z (W64 0))) with 0%nat by word.
    iSimpl in "Hsl".
    wp_auto.
    wp_apply (wp_slice_append with "[$Hys $Hcap $Hsl]").
    iIntros (so') "(Hys & Hcap & _)".
    wp_auto.
    wp_for_post.
    iFrame "Hs HΦ a e".
    iExists (word.add n (W64 1)), xp, so',
      (ys ++ [checker.Path.mk lv xp.(checker.Path.St')]), (outs ++ [mkPath y (pst sq)]).
    iFrame "i q out Hys Hcap".
    replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
    iFrame "Hrest".
    iSplitL "Hysp Hstl Hheap Hcond".
    { iApply (big_sepL2_app with "Hysp"). simpl. iSplitL; last done.
      iFrame "Hlv". iExists hs, cs, vs. iFrame "∗#". }
    iPureIntro. split; first word.
    rewrite (take_S_r _ _ sq) //.
    apply Forall2_app; first done.
    constructor; last constructor.
    exists y. done.
  - (* the loop is over *)
    assert (take (sint.nat n) qs0 = qs0) as Htake by (apply take_ge; word).
    rewrite Htake in HF.
    try wp_auto.
    iApply "HΦ". destruct (decide (null = null)) as [_|Hc]; last done.
    iExists outs. iFrame "Hys Hysp". done.
Qed.

End proof.
