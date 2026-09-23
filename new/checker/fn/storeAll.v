(** [checker.storeAll] (checker/exec.go): the store of an [EStore] at
    location term [l], performed on each path the stored value reached.

    For each path [q], the state is cloned, [heapUpdate] replaces the cell at
    [l] with [q.Ret] (failing if there is none), and the new path returns
    [TUnit] in the updated state.

    Naming: the Go locals are [e], [l], [ps], [out], [q], [st2], [ok], [h],
    and the range loop's [i], so no Rocq variable here is called any of those
    (see NOTES.md). *)
From New.checker Require Import prelude nodes exec_spec exec_sound_c.
From New.checker.fn Require Import State__clone heapUpdate.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The path [storeAll] produces from a path [qv] of the stored value. *)
Definition store_path (x : term) (qv : spath) : option spath :=
  (λ H', mkPath TUnit (st_heap (pst qv) H')) <$> heap_update (sheap (pst qv)) x (pret qv).

Definition store_rel (x : term) (qvs outs : list spath) : Prop :=
  Forall2 (λ qv o, store_path x qv = Some o) qvs outs.

Lemma store_rel_ok x qvs outs : store_rel x qvs outs → store_ok x qvs outs.
Proof.
  intros Hrel qv Hin. apply list_elem_of_lookup in Hin as [j Hj].
  destruct (Forall2_lookup_l _ _ _ _ _ Hrel Hj) as (o & Ho & Hso).
  rewrite /store_path in Hso.
  destruct (heap_update (sheap (pst qv)) x (pret qv)) as [H'|] eqn:Hup; last done.
  exists H'. split; first done. simpl in Hso. injection Hso as <-.
  by eapply list_elem_of_lookup_2.
Qed.

Lemma store_rel_wf k x qvs outs : paths_wf k qvs → store_rel x qvs outs → paths_wf k outs.
Proof.
  intros Hwf Hrel.
  assert (∀ o, o ∈ outs → ∃ qv H', qv ∈ qvs ∧
            heap_update (sheap (pst qv)) x (pret qv) = Some H' ∧
            o = mkPath TUnit (st_heap (pst qv) H')) as Hsrc.
  { intros o Hin. apply list_elem_of_lookup in Hin as [j Hj].
    destruct (Forall2_lookup_r _ _ _ _ _ Hrel Hj) as (qv & Hq & Hso).
    rewrite /store_path in Hso.
    destruct (heap_update (sheap (pst qv)) x (pret qv)) as [H'|] eqn:Hup; last done.
    simpl in Hso. injection Hso as <-. exists qv, H'.
    split; last done. by eapply list_elem_of_lookup_2. }
  split.
  - intros o Hin. destruct (Hsrc o Hin) as (qv & H' & Hq & Hup & ->). simpl.
    eapply wf_state_heap; [by apply (paths_wf_state _ _ Hwf)|by apply (paths_wf_ret _ _ Hwf)|done].
  - intros o Hin. destruct (Hsrc o Hin) as (qv & H' & Hq & Hup & ->). simpl.
    by apply (paths_wf_grow _ _ Hwf).
  - intros o Hin. destruct (Hsrc o Hin) as (qv & H' & Hq & Hup & ->). done.
Qed.

Lemma wp_storeAll (le lx : loc) (sq : slice.t) (x : term) (qvs : list spath) :
  {{{ is_pkg_init checker ∗ is_term lx x ∗ is_paths sq qvs }}}
    @! checker.storeAll #le #lx #sq
  {{{ (s : slice.t) (lf : loc), RET (#s, #lf);
      if decide (lf = null) then
        ∃ outs, is_paths s outs ∗ ⌜store_rel x qvs outs⌝
      else True }}}.
Proof.
  wp_start as "(#Hx & Hqs)".
  iDestruct "Hqs" as (xs) "[Hxs Hxp]".
  iDestruct (big_sepL2_length with "Hxp") as %Hlen2.
  iDestruct (own_slice_len with "Hxs") as %Hlen.
  wp_auto.
  iAssert (∃ (k : w64) (pcur : checker.Path.t) (so : slice.t) (os : list checker.Path.t)
             (outs : list spath),
      "i" ∷ i_ptr ↦ k ∗
      "q" ∷ q_ptr ↦ pcur ∗
      "out" ∷ out_ptr ↦ so ∗
      "Hos" ∷ so ↦* os ∗
      "Hcap" ∷ own_slice_cap checker.Path.t so (DfracOwn 1) ∗
      "Hosp" ∷ ([∗ list] y;o ∈ os; outs, is_path y o) ∗
      "Hrest" ∷ ([∗ list] y;o ∈ drop (sint.nat k) xs; drop (sint.nat k) qvs, is_path y o) ∗
      "%Hrel" ∷ ⌜store_rel x (take (sint.nat k) qvs) outs⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ≤ length xs⌝)%I
    with "[i q out Hxp]" as "HI".
  { iExists (W64 0), _, slice.nil, [], [].
    iFrame "i q out". iDestruct own_slice_nil as "$". iDestruct own_slice_cap_nil as "$".
    replace (sint.nat (W64 0)) with 0%nat by word.
    rewrite take_0 !drop_0 /=. iFrame "Hxp".
    iPureIntro. split; [apply Forall2_nil|word]. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem xs (sint.nat k) as x0.
    list_elem qvs (sint.nat k) as q0.
    rewrite (drop_S xs x0 (sint.nat k)) // (drop_S qvs q0 (sint.nat k)) //.
    iDestruct "Hrest" as "[[#Hret Hst0] Hrest]".
    wp_apply (wp_load_slice_index with "[$Hxs]").
    { word. }
    { done. }
    iIntros "Hxs".
    wp_auto.
    wp_apply (wp_State__clone with "[$Hst0]") as (lst2) "[_ Hfr]".
    iDestruct "Hfr" as (hs cs vs) "(Hl & Hh & Hhcap & Hc & Hccap & Hv & Hvcap)".
    wp_auto.
    wp_apply (wp_heapUpdate_aux with "[$Hh]") as (hs' okb) "(_ & %Hok & Hnew)".
    { iFrame "#". }
    destruct okb; last first.
    { (* no cell at [l] *)
      wp_auto. wp_alloc lfail as "Hf". wp_auto. wp_for_post.
      iDestruct (typed_pointsto_not_null with "Hf") as %Hnn.
      iApply "HΦ". by rewrite decide_False. }
    iDestruct "Hnew" as (H') "[%Hup Hh']".
    wp_auto.
    wp_alloc lunit as "Hu".
    iPersist "Hu".
    iPersist "Hv".
    iAssert (is_state lst2 (st_heap (pst q0) H')) with "[Hl Hh' Hc]" as "Hst2".
    { iExists hs', cs, vs. iFrame "Hl Hh' Hc". rewrite /is_vars. iFrame "#". }
    wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "%sl3 [Hsl3 _]".
    rewrite insert0_singleton. wp_auto.
    wp_apply (wp_slice_append so os _ _ (DfracOwn 1)
               with "[$Hos $Hcap $Hsl3]") as (so') "(Hos & Hcap & _)".
    wp_for_post.
    iFrame "HΦ Hxs l e".
    iExists (word.add k (W64 1)), x0, so',
      (os ++ [checker.Path.mk lunit lst2]), (outs ++ [mkPath TUnit (st_heap (pst q0) H')]).
    replace (sint.nat (word.add k (W64 1))) with (S (sint.nat k)) by word.
    iFrame "i q out Hos Hcap Hrest".
    iSplitL "Hosp Hst2".
    { iApply (big_sepL2_app with "Hosp"). cbn. iSplit; last done.
      rewrite /is_path /=. iFrame "Hst2". iExact "Hu". }
    iPureIntro. split; last word.
    rewrite (take_S_r qvs (sint.nat k) q0) //.
    apply Forall2_app; first done. apply Forall2_cons; last apply Forall2_nil.
    rewrite /store_path Hup //.
  - (* the loop is over *)
    try wp_auto.
    rewrite take_ge in Hrel; last lia.
    iApply "HΦ".
    destruct (decide (null = null)) as [_|]; last congruence.
    iExists outs. iSplitL; last done.
    iExists os. iFrame.
  Unshelve. all: try apply _.
Qed.

End proof.
