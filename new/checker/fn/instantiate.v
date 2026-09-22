(** [checker.instantiate] (checker/match.go): substitute the bound pattern
    variables and [ret] into a term, rebuilding the spine above them.

    Note on naming: the Go function's locals are [t], [subst] and [ret], so no
    Rocq variable in [wp_instantiate] may be called any of those (see
    NOTES.md). *)
From New.checker Require Import prelude nodes.

(** * The Gallina mirror (no Iris here, so these stay outside the
    section: [Set Default Proof Using "All"] would otherwise make every
    pure lemma depend on [Σ], which then cannot be inferred when the
    lemma is applied to plain Gallina arguments). *)

Definition tbind1 (f : term → term) (oa : option term) : option term :=
  match oa with Some a => Some (f a) | None => None end.
Definition tbind2 (f : term → term → term) (oa ob : option term) : option term :=
  match oa, ob with Some a, Some b => Some (f a b) | _, _ => None end.
Definition tbind3 (f : term → term → term → term) (oa ob oc : option term) : option term :=
  match oa, ob, oc with Some a, Some b, Some c => Some (f a b c) | _, _, _ => None end.

(** [None] is the nil pointer.  A node is rebuilt from its instantiated
    children, so it is [None] as soon as one of them is -- see
    [inst_wf] below for the side condition that rules that out. *)
Fixpoint instantiate_t (x : term) (σ : list (option term)) (r : option term) : option term :=
  match x with
  | TPat n => Some (match σ !! n with Some (Some y) => y | _ => TPat n end)
  | TResult => r
  | TPlus p q => tbind2 TPlus (instantiate_t p σ r) (instantiate_t q σ r)
  | TMinus p q => tbind2 TMinus (instantiate_t p σ r) (instantiate_t q σ r)
  | TMul p q => tbind2 TMul (instantiate_t p σ r) (instantiate_t q σ r)
  | TNeg p => tbind1 TNeg (instantiate_t p σ r)
  | TEq p q => tbind2 TEq (instantiate_t p σ r) (instantiate_t q σ r)
  | TLt sg p q => tbind2 (TLt sg) (instantiate_t p σ r) (instantiate_t q σ r)
  | TLe sg p q => tbind2 (TLe sg) (instantiate_t p σ r) (instantiate_t q σ r)
  | TNot p => tbind1 TNot (instantiate_t p σ r)
  | TIte p q z => tbind3 TIte (instantiate_t p σ r) (instantiate_t q σ r) (instantiate_t z σ r)
  | TRet p => tbind1 TRet (instantiate_t p σ r)
  | _ => Some x
  end.

Definition oinstantiate_t (ox : option term) (σ : list (option term)) (r : option term)
  : option term :=
  match ox with None => None | Some x => instantiate_t x σ r end.

(** * When the result of a child is a real term

    [instantiate(t, subst, nil)] with a [TResult] strictly below the root
    builds a node with a nil child, which no [term] describes (see the report
    in NOTES.md).  [inst_wf] excludes exactly that; it is vacuous whenever
    [ret] is a real term, which is the case at every call site. *)

Fixpoint has_result (x : term) : bool :=
  match x with
  | TResult => true
  | TPlus p q | TMinus p q | TMul p q | TEq p q | TLt _ p q | TLe _ p q =>
      has_result p || has_result q
  | TNeg p | TNot p | TRet p => has_result p
  | TIte p q z => has_result p || has_result q || has_result z
  | _ => false
  end.

Definition ohas_result (ox : option term) : bool :=
  match ox with None => false | Some x => has_result x end.

Definition is_tpat (x : term) : bool := match x with TPat _ => true | _ => false end.
Definition is_tresult (x : term) : bool := match x with TResult => true | _ => false end.

Lemma is_tpat_code x : bool_decide (term_code x = W64 2) = is_tpat x.
Proof. destruct x; simpl; repeat case_match; by vm_compute. Qed.

Lemma is_tresult_code x : bool_decide (term_code x = W64 3) = is_tresult x.
Proof. destruct x; simpl; repeat case_match; by vm_compute. Qed.

Lemma has_result_node x :
  has_result x = (is_tresult x || ohas_result (term_a x) || ohas_result (term_b x)
                  || ohas_result (term_c x))%bool.
Proof. destruct x; simpl; by rewrite ?orb_false_r. Qed.

Lemma has_result_children x :
  has_result x = false →
  ohas_result (term_a x) = false ∧ ohas_result (term_b x) = false ∧
  ohas_result (term_c x) = false.
Proof. rewrite has_result_node !orb_false_iff. tauto. Qed.

Lemma inst_Some_r x σ r : is_Some r → ∃ y, instantiate_t x σ r = Some y.
Proof.
  intros Hr. induction x; simpl;
    repeat match goal with H : ∃ y, _ = Some y |- _ => destruct H as [? ->] end;
    try (by eexists).
  destruct Hr as [y ->]. by eexists.
Qed.

Lemma inst_Some_n x σ r : has_result x = false → ∃ y, instantiate_t x σ r = Some y.
Proof.
  induction x; simpl; intros Hn; try discriminate; try (by eexists);
    rewrite ?orb_false_iff in Hn; destruct_and?;
    repeat match goal with
    | IH : ?P → ∃ y, instantiate_t _ _ _ = Some y, H : ?P |- _ =>
        destruct (IH H) as [? ->]; clear IH
    end; by eexists.
Qed.

Lemma inst_Some x σ r :
  (is_Some r ∨ has_result x = false) → ∃ y, instantiate_t x σ r = Some y.
Proof. intros [?|?]; [by apply inst_Some_r | by apply inst_Some_n]. Qed.

Definition inst_wf (r : option term) (x : term) : Prop :=
  is_Some r ∨ (ohas_result (term_a x) = false ∧ ohas_result (term_b x) = false ∧
               ohas_result (term_c x) = false).

Definition inst_wf_o (r : option term) (ox : option term) : Prop :=
  match ox with None => True | Some x => inst_wf r x end.

Lemma inst_wf_child r x p :
  inst_wf r x → (term_a x = Some p ∨ term_b x = Some p ∨ term_c x = Some p) →
  inst_wf r p.
Proof.
  intros [Hr|(Ha & Hb & Hc)] Hin; first by left.
  right. apply has_result_children.
  destruct Hin as [H|[H|H]]; [rewrite H in Ha|rewrite H in Hb|rewrite H in Hc]; done.
Qed.

Lemma inst_wf_o_a r x : inst_wf r x → inst_wf_o r (term_a x).
Proof. intros H. destruct (term_a x) eqn:E; simpl; last done. by eapply inst_wf_child; eauto. Qed.
Lemma inst_wf_o_b r x : inst_wf r x → inst_wf_o r (term_b x).
Proof. intros H. destruct (term_b x) eqn:E; simpl; last done. by eapply inst_wf_child; eauto. Qed.
Lemma inst_wf_o_c r x : inst_wf r x → inst_wf_o r (term_c x).
Proof. intros H. destruct (term_c x) eqn:E; simpl; last done. by eapply inst_wf_child; eauto. Qed.

(** A node with no children is returned unchanged. *)
Lemma instantiate_leaf x σ r :
  is_tpat x = false → is_tresult x = false →
  term_a x = None → term_b x = None → term_c x = None →
  instantiate_t x σ r = Some x.
Proof. destruct x; simpl; congruence. Qed.
(** What each child needs for the rebuilt node to have no nil child. *)
Definition inst_ok (r : option term) (ox : option term) : Prop :=
  match ox with None => True | Some p => is_Some r ∨ has_result p = false end.

Lemma inst_wf_ok_a r x : inst_wf r x → inst_ok r (term_a x).
Proof. intros [?|(?&?&?)]; destruct (term_a x); simpl in *; auto. Qed.
Lemma inst_wf_ok_b r x : inst_wf r x → inst_ok r (term_b x).
Proof. intros [?|(?&?&?)]; destruct (term_b x); simpl in *; auto. Qed.
Lemma inst_wf_ok_c r x : inst_wf r x → inst_ok r (term_c x).
Proof. intros [?|(?&?&?)]; destruct (term_c x); simpl in *; auto. Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** * The specification *)

Definition is_subst (s : slice.t) (σ : list (option term)) : iProp Σ :=
  (∃ ls : list loc, s ↦* ls ∗ [∗ list] li;oi ∈ ls;σ, is_oterm li oi)%I.

(** The rebuilt node.  Every constructor with a child is covered here, so
    that the [wp] proof below can stay generic in the node's kind. *)
Lemma is_oterm_rebuild (lz : loc) (x : term) (l2 l3 l4 : loc)
      (sg : list (option term)) (r : option term) :
  inst_wf r x →
  (term_a x ≠ None ∨ term_b x ≠ None ∨ term_c x ≠ None) →
  lz ↦□ tnode (term_code x) (term_num x) l2 l3 l4 -∗
  is_oterm l2 (oinstantiate_t (term_a x) sg r) -∗
  is_oterm l3 (oinstantiate_t (term_b x) sg r) -∗
  is_oterm l4 (oinstantiate_t (term_c x) sg r) -∗
  is_oterm lz (instantiate_t x sg r).
Proof.
  intros Hwf Hch.
  pose proof (inst_wf_ok_a _ _ Hwf) as Hoa.
  pose proof (inst_wf_ok_b _ _ Hwf) as Hob.
  pose proof (inst_wf_ok_c _ _ Hwf) as Hoc.
  clear Hwf.
  iIntros "#Hl #H2 #H3 #H4".
  destruct x as [m|m| |w|bb| | |p q|p q|p q|p|p q|sgn p q|sgn p q|p|p q z| |p];
    simpl in Hch, Hoa, Hob, Hoc;
    try (exfalso; destruct Hch as [Hne|[Hne|Hne]]; by apply Hne).
  all: simpl.
  all: destruct (inst_Some _ sg r Hoa) as [ya Hya]; rewrite Hya.
  all: try (destruct (inst_Some _ sg r Hob) as [yb Hyb]; rewrite Hyb).
  all: try (destruct (inst_Some _ sg r Hoc) as [yc Hyc]; rewrite Hyc).
  all: simpl.
  all: try (iDestruct "H2" as %->).
  all: try (iDestruct "H3" as %->).
  all: try (iDestruct "H4" as %->).
  all: iFrame "∗ #".
Qed.

Lemma wp_instantiate (lx : loc) (s : slice.t) (lr : loc)
      (ox : option term) (σ : list (option term)) (oret : option term) :
  {{{ is_pkg_init checker ∗ ⌜inst_wf_o oret ox⌝ ∗
      is_oterm lx ox ∗ is_subst s σ ∗ is_oterm lr oret }}}
    @! checker.instantiate #lx #s #lr
  {{{ (l : loc), RET #l; is_subst s σ ∗ is_oterm l (oinstantiate_t ox σ oret) }}}.
Proof.
  iLöb as "IH" forall (lx ox).
  wp_start as "(%Hwf & #Hox & Hsub & #Hor)".
  iDestruct (is_oterm_null with "Hox") as %Hnull.
  wp_auto.
  wp_if_destruct.
  { (* [t] is nil *)
    assert (ox = None) as -> by naive_solver.
    try wp_auto. iApply ("HΦ" $! null). iFrame "Hsub". done. }
  destruct ox as [x|]; last naive_solver.
  iDestruct (is_term_node with "Hox") as (la lb lc) "(%Hw & #Hn & #Ha & #Hb & #Hc)".
  try wp_auto.
  rewrite is_tpat_code.
  destruct (is_tpat x) eqn:Hp.
  { (* [t.Kind == TPat]: look the index up in [subst] *)
    destruct x as [m|m| |w|bb| | |p q|p q|p q|p|p q|sg p q|sg p q|p|p q z| |p];
      try discriminate Hp.
    simpl in Hw.
    iDestruct "Hsub" as (ls) "[Hs #Hls]".
    iDestruct (big_sepL2_length with "Hls") as %Hlen2.
    iDestruct (own_slice_len with "Hs") as %Hlen.
    try wp_auto.
    wp_if_destruct.
    - (* the index is in range *)
      destruct Hlen as [Hlen Hlen0].
      rewrite /idx_wf in Hw.
      assert (sint.nat (W64 m) = m) as Hsn by word.
      assert (m < length ls)%nat as Hmlt by word.
      list_elem ls m as li.
      list_elem σ m as oi.
      iDestruct (big_sepL2_lookup with "Hls") as "#Hli"; [done|done|].
      iDestruct (is_oterm_null with "Hli") as %Hlin.
      rewrite -> decide_True; last word.
      wp_apply (wp_load_slice_index with "[$Hs]").
      { word. }
      { rewrite Hsn. done. }
      iIntros "Hs".
      wp_auto.
      wp_if_destruct.
      + (* [subst[n]] is nil: the pattern variable is unbound *)
        assert (oi = None) as Hoi by naive_solver.
        try wp_auto.
        iApply ("HΦ" $! lx).
        iSplitL "Hs"; first by iFrame "Hs Hls".
        simpl. rewrite Hoi_lookup Hoi. by iFrame "Hox".
      + destruct oi as [y|]; last naive_solver.
        try wp_auto.
        rewrite -> decide_True; last word.
        wp_apply (wp_load_slice_index with "[$Hs]").
        { word. }
        { rewrite Hsn. done. }
        iIntros "Hs".
        try wp_auto.
        iSpecialize ("HΦ" $! li with "[Hs]").
        { iSplitL "Hs"; first by iFrame "Hs Hls".
          simpl. rewrite Hoi_lookup. by iFrame "Hli". }
        iExact "HΦ".
    - (* the index is out of range *)
      destruct Hlen as [Hlen Hlen0].
      rewrite /idx_wf in Hw.
      assert (σ !! m = None) as Hoob.
      { apply lookup_ge_None_2. word. }
      try wp_auto.
      iApply ("HΦ" $! lx).
      iSplitL "Hs"; first by iFrame "Hs Hls".
      simpl. rewrite Hoob. by iFrame "Hox". }
  try wp_auto.
  rewrite is_tresult_code.
  destruct (is_tresult x) eqn:Hr.
  { (* [t.Kind == TResult]: return [ret] *)
    destruct x as [m|m| |w|bb| | |p q|p q|p q|p|p q|sg p q|sg p q|p|p q z| |p];
      try discriminate Hr.
    try wp_auto.
    iSpecialize ("HΦ" $! lr with "[Hsub]"); first by iFrame "Hsub Hor".
    iExact "HΦ". }
  try wp_auto.
  iDestruct (is_oterm_null with "Ha") as %Hna.
  iDestruct (is_oterm_null with "Hb") as %Hnb.
  iDestruct (is_oterm_null with "Hc") as %Hnc.
  wp_if_destruct; [wp_if_destruct; [wp_if_destruct|]|].
  { (* no children: the node is returned unchanged *)
    try wp_auto.
    iSpecialize ("HΦ" $! lx with "[Hsub]").
    { iFrame "Hsub". simpl.
      rewrite (instantiate_leaf x σ oret) //; naive_solver. }
    iExact "HΦ". }
  (* the node has at least one child: rebuild it *)
  all: assert (term_a x ≠ None ∨ term_b x ≠ None ∨ term_c x ≠ None) as Hch
         by naive_solver.
  all: iApply wp_fupd.
  all: wp_apply ("IH" $! _ (term_a x) with "[Hsub]");
         [ iFrame "∗ #"; iPureIntro; by apply inst_wf_o_a |].
  all: iIntros (l2) "[Hsub #Hia]".
  all: try wp_auto.
  all: wp_apply ("IH" $! _ (term_b x) with "[Hsub]");
         [ iFrame "∗ #"; iPureIntro; by apply inst_wf_o_b |].
  all: iIntros (l3) "[Hsub #Hib]".
  all: try wp_auto.
  all: wp_apply ("IH" $! _ (term_c x) with "[Hsub]");
         [ iFrame "∗ #"; iPureIntro; by apply inst_wf_o_c |].
  all: iIntros (l4) "[Hsub #Hic]".
  all: try wp_auto.
  all: wp_alloc lz as "Hl".
  all: try wp_auto.
  all: iPersist "Hl".
  all: iModIntro.
  all: iSpecialize ("HΦ" $! lz with "[$Hsub]");
    [ iApply (is_oterm_rebuild with "Hl Hia Hib Hic"); try done | iExact "HΦ" ].
Qed.

(** The side condition is vacuous whenever [ret] is a real term, which is the
    case at every call site ([is_path] describes [p.Ret] with [is_term]). *)
Lemma wp_instantiate_ret (lx : loc) (s : slice.t) (lr : loc)
      (ox : option term) (σ : list (option term)) (rt : term) :
  {{{ is_pkg_init checker ∗ is_oterm lx ox ∗ is_subst s σ ∗ is_term lr rt }}}
    @! checker.instantiate #lx #s #lr
  {{{ (l : loc), RET #l;
      is_subst s σ ∗ is_oterm l (oinstantiate_t ox σ (Some rt)) }}}.
Proof.
  iIntros (Φ) "(#Hpkg & #Hox & Hsub & #Hor) HΦ".
  iApply (wp_instantiate lx s lr ox σ (Some rt) with "[Hsub]").
  { iFrame "∗ #". iPureIntro. destruct ox as [xx|]; simpl; last done.
    left. by eexists. }
  iNext. iIntros (l) "[Hsub #Hres]".
  iApply "HΦ". by iFrame "Hsub Hres".
Qed.

End proof.
