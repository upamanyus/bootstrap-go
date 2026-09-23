(** Soundness of the reflective symbolic executor.

    [symex_sound] is the one theorem the tactic applies: if [run] succeeds on
    the reflected program, then the program's weakest precondition follows
    from the initial heap and the residual goal [paths_goal] (one conjunct per
    path). It is proved once, here, by induction on the executor's fuel;
    applying it costs a [vm_compute] of [run] and nothing proportional to the
    length of the program. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.proof.symex Require Export denote.

Set Default Proof Using "All".

Lemma nth_error_snoc {A} (l : list A) x n : length l = n → nth_error (l ++ [x]) n = Some x.
Proof.
  revert n. induction l as [|y l IH]; intros [|n]; simpl; try done; intros [=]; auto.
Qed.

Section sound.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

Lemma wp_wand' e (Φ Ψ : val → iProp Σ) :
  WP e {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Ψ }}.
Proof. iIntros "H HΦ". iApply (wp_wand_r _ _ _ Φ). iFrame. Qed.

(** * One step of each instruction

    Each lemma is stated with the continuation abstract, so that proving it
    takes exactly the steps of that instruction. *)

Lemma wp_let_bind (x : string) (d1 d2 : expr) (Φ : val → iProp Σ) :
  WP d1 {{ w, WP subst x w d2 {{ Φ }} }} -∗ WP App (Rec BAnon (BNamed x) d2) d1 {{ Φ }}.
Proof.
  iIntros "H".
  iApply (wp_bind (fill [AppRCtx (Rec BAnon (BNamed x) d2)])).
  iApply (wp_wand' with "H"). iIntros (w) "H". simpl. by wp_pures.
Qed.

(** A pair is evaluated left to right, and then the instruction applied. *)
Lemma wp_app_pair (f : val) (d1 d2 : expr) (Φ : val → iProp Σ) :
  WP d1 {{ w1, WP d2 {{ w2, WP App (Val f) (Val (PairV w1 w2)) {{ Φ }} }} }} -∗
  WP App (Val f) (Pair d1 d2) {{ Φ }}.
Proof.
  iIntros "H".
  iApply (wp_bind (fill [PairLCtx d2; AppRCtx (Val f)])).
  iApply (wp_wand' with "H"). iIntros (w1) "H". simpl.
  iApply (wp_bind (fill [PairRCtx w1; AppRCtx (Val f)])).
  iApply (wp_wand' with "H"). iIntros (w2) "H". simpl.
  by wp_pures.
Qed.

Lemma wp_if_bool (b : bool) (d1 d2 : expr) (Φ : val → iProp Σ) :
  WP (if b then d1 else d2) {{ Φ }} -∗ WP If (Val #b) d1 d2 {{ Φ }}.
Proof. iIntros "H". destruct b; by wp_pures. Qed.

Lemma wp_convert_id (t : go.type) (w : val) (Φ : val → iProp Σ) :
  Φ w -∗ WP App (Val (GoInstruction (Convert t t))) (Val w) {{ Φ }}.
Proof. iIntros "H". by wp_pures. Qed.

Lemma wp_do_exec (w : val) (Φ : val → iProp Σ) :
  Φ execute_val -∗ WP App (Val do_execute) (Val w) {{ Φ }}.
Proof. iIntros "H". wp_pures. by rewrite execute_val_unseal. Qed.

Lemma wp_do_return (w : val) (Φ : val → iProp Σ) :
  Φ (return_val w) -∗ WP App (Val do_return) (Val w) {{ Φ }}.
Proof. iIntros "H". wp_pures. by rewrite return_val_unseal. Qed.

Lemma wp_exc_seq_exec (d2 : expr) (Φ : val → iProp Σ) :
  WP d2 {{ Φ }} -∗ WP App (App (Val exception_seq) (Rec BAnon BAnon d2)) (Val execute_val) {{ Φ }}.
Proof. iIntros "H". by wp_pures. Qed.

Lemma wp_exc_seq_ret (d2 : expr) (w : val) (Φ : val → iProp Σ) :
  Φ (return_val w) -∗
  WP App (App (Val exception_seq) (Rec BAnon BAnon d2)) (Val (return_val w)) {{ Φ }}.
Proof. iIntros "H". by wp_pures. Qed.

Lemma wp_exc_do_exec (Φ : val → iProp Σ) :
  Φ #() -∗ WP App (Val exception_do) (Val execute_val) {{ Φ }}.
Proof. iIntros "H". by wp_pures. Qed.

Lemma wp_exc_do_ret (w : val) (Φ : val → iProp Σ) :
  Φ w -∗ WP App (Val exception_do) (Val (return_val w)) {{ Φ }}.
Proof. iIntros "H". by wp_pures. Qed.

(** ** Memory *)

Lemma wp_alloc_sval (t : sty) ρ v w (Φ : val → iProp Σ) :
  sort_ok t v = true → vden ρ v = Some w →
  (∀ l : loc, pts l ρ v -∗ Φ #l) -∗
  WP App (Val (GoInstruction (GoAlloc (ty_den t)))) (Val w) {{ Φ }}.
Proof.
  intros Hs Hv. iIntros "HΦ".
  destruct v as [a|a|a| | |]; rewrite /sort_ok /= in Hs; try discriminate; cbn [vden] in Hv.
  - simplify_eq. destruct t; try discriminate;
      wp_apply wp_alloc; iIntros (l) "Hl"; by iApply "HΦ".
  - destruct (beval ρ a) as [b|] eqn:Hb; simplify_eq.
    destruct t; try discriminate.
    rewrite /pts Hb. wp_apply wp_alloc; iIntros (l) "Hl". by iApply "HΦ".
  - destruct (leval ρ a) as [lo|] eqn:Hl; simplify_eq.
    destruct t; try discriminate.
    rewrite /pts Hl. wp_apply wp_alloc; iIntros (l) "Hl". by iApply "HΦ".
Qed.

Lemma wp_load_sval (t : sty) ρ (l : loc) v (Φ : val → iProp Σ) :
  sort_ok t v = true →
  pts l ρ v -∗ (∀ w, ⌜vden ρ v = Some w⌝ -∗ pts l ρ v -∗ Φ w) -∗
  WP App (Val (GoInstruction (GoLoad (ty_den t)))) (Val #l) {{ Φ }}.
Proof.
  intros Hs. iIntros "Hl HΦ".
  destruct v as [a|a|a| | |]; rewrite /sort_ok /= in Hs; try discriminate; rewrite /pts.
  - destruct t; try discriminate;
      wp_apply (wp_load with "Hl"); iIntros "Hl"; by iApply ("HΦ" with "[//] Hl").
  - destruct (beval ρ a) as [b|] eqn:Hb; last by iDestruct "Hl" as "[]".
    destruct t; try discriminate.
    wp_apply (wp_load with "Hl"). iIntros "Hl". iApply ("HΦ" with "[] Hl").
    iPureIntro. by rewrite /= Hb.
  - destruct (leval ρ a) as [lo|] eqn:Hl; last by iDestruct "Hl" as "[]".
    destruct t; try discriminate.
    wp_apply (wp_load with "Hl"). iIntros "Hl". iApply ("HΦ" with "[] Hl").
    iPureIntro. by rewrite /= Hl.
Qed.

Lemma wp_store_sval (t : sty) ρ (l : loc) v v' w' (Φ : val → iProp Σ) :
  sort_ok t v = true → sort_ok t v' = true → vden ρ v' = Some w' →
  pts l ρ v -∗ (pts l ρ v' -∗ Φ #()) -∗
  WP App (Val (GoInstruction (GoStore (ty_den t)))) (Val (PairV #l w')) {{ Φ }}.
Proof.
  intros Hs Hs' Hv'. iIntros "Hl HΦ".
  destruct v as [a|a|a| | |], v' as [b|b|b| | |], t;
    simpl in Hs, Hs'; try discriminate; cbn [vden] in Hv'; rewrite /pts.
  1-3: simplify_eq; wp_apply (wp_store with "Hl"); iIntros "Hl"; by iApply "HΦ".
  - destruct (beval ρ a); last by iDestruct "Hl" as "[]".
    destruct (beval ρ b); simplify_eq.
    wp_apply (wp_store with "Hl"); iIntros "Hl"; by iApply "HΦ".
  - destruct (leval ρ a); last by iDestruct "Hl" as "[]".
    destruct (leval ρ b); simplify_eq.
    wp_apply (wp_store with "Hl"); iIntros "Hl"; by iApply "HΦ".
Qed.

Lemma wp_zero_sval (t : sty) ρ :
  ∃ w, vden ρ (sty_zero t) = Some w ∧
       ∀ Φ : val → iProp Σ, Φ w -∗
         WP App (Val (GoInstruction (GoZeroVal (ty_den t)))) (Val #()) {{ Φ }}.
Proof.
  destruct t; eexists; (split; [reflexivity|]); iIntros (Φ) "H"; by wp_pures.
Qed.

(** ** Operators *)

Lemma wp_binop_sval op (t : sty) ρ v1 v2 v w1 w2 :
  sbinop_eval op t v1 v2 = Some v → vden ρ v1 = Some w1 → vden ρ v2 = Some w2 →
  ∃ w, vden ρ v = Some w ∧
       ∀ Φ : val → iProp Σ, Φ w -∗
         WP App (Val (GoInstruction (GoOp (binop_den op) (ty_den t)))) (Val (PairV w1 w2)) {{ Φ }}.
Proof.
  rewrite /sbinop_eval. intros Hop Hv1 Hv2.
  destruct v1 as [a|a|a| | |]; try (destruct op, (sty_sort t); discriminate);
  destruct v2 as [b|b|b| | |]; try (destruct op, (sty_sort t); discriminate);
    cbn [vden] in Hv1, Hv2.
  - simplify_eq. destruct op, t; simpl in Hop; simplify_eq;
      (eexists; split; [reflexivity|]); iIntros (Φ) "H"; cbn [binop_den ty_den]; by wp_pures.
  - destruct (beval ρ a) as [x|] eqn:Ha; last done.
    destruct (beval ρ b) as [y|] eqn:Hb; last done.
    simplify_eq. destruct op, t; simpl in Hop; simplify_eq.
    eexists; split; first by rewrite /= Ha Hb.
    iIntros (Φ) "H". by wp_pures.
Qed.

Lemma wp_unop_sval op (t : sty) ρ v1 v w1 :
  sunop_eval op t v1 = Some v → vden ρ v1 = Some w1 →
  ∃ w, vden ρ v = Some w ∧
       ∀ Φ : val → iProp Σ, Φ w -∗
         WP App (Val (GoInstruction (GoUnOp (unop_den op) (ty_den t)))) (Val w1) {{ Φ }}.
Proof.
  rewrite /sunop_eval. intros Hop Hv1.
  destruct v1 as [a|a|a| | |]; try (destruct op, (sty_sort t); discriminate); cbn [vden] in Hv1.
  - simplify_eq. destruct op, t; simpl in Hop; simplify_eq;
      (eexists; split; [reflexivity|]); iIntros (Φ) "H"; by wp_pures.
  - destruct (beval ρ a) as [x|] eqn:Ha; last done.
    simplify_eq. destruct op, t; simpl in Hop; simplify_eq.
    eexists; split; first by rewrite /= Ha.
    iIntros (Φ) "H". by wp_pures.
Qed.

(** * The heap *)

Lemma heap_den_lookup ρ h m v lo :
  hlookup m h = Some v → nth_error (e_ls ρ) m = Some lo →
  heap_den ρ h ⊢ pts lo ρ v ∗ (pts lo ρ v -∗ heap_den ρ h).
Proof.
  intros Hlk Hlo. induction h as [|[n v'] h IH]; first done.
  cbn [hlookup] in Hlk. cbn [heap_den].
  destruct (Nat.eqb_spec m n) as [<-|Hne].
  - simplify_eq. rewrite /cell_den Hlo. iIntros "[$ $]". auto.
  - iIntros "[Hc Hh]". iDestruct (IH Hlk with "Hh") as "[$ Hback]".
    iIntros "Hp". iFrame "Hc". by iApply "Hback".
Qed.

Lemma heap_den_update ρ t h m v h' lo :
  hupdate t m v h = Some h' → nth_error (e_ls ρ) m = Some lo →
  heap_den ρ h ⊢ ∃ vold, ⌜sort_ok t vold = true⌝ ∗ pts lo ρ vold ∗
                         (pts lo ρ v -∗ heap_den ρ h').
Proof.
  intros Hup Hlo. revert h' Hup. induction h as [|[n v'] h IH]; intros h' Hup; first done.
  cbn [hupdate] in Hup. cbn [heap_den].
  destruct (Nat.eqb_spec m n) as [<-|Hne].
  - destruct (sort_ok t v') eqn:Hs; last done. simplify_eq. cbn [heap_den].
    rewrite /cell_den Hlo. iIntros "[Hc Hh]". iExists v'. iFrame. auto.
  - destruct (hupdate t m v h) as [h''|] eqn:Hup'; last done. simpl in Hup. simplify_eq. cbn [heap_den].
    iIntros "[Hc Hh]". iDestruct (IH h'' eq_refl with "Hh") as (vold) "(% & Hp & Hback)".
    iExists vold. iFrame "Hp". iSplit; first done.
    iIntros "Hp". iFrame "Hc". by iApply "Hback".
Qed.

(** * The executor *)

(** What running a subexpression with continuation [k] promises: it ends in
    some value and state that [k] accepts, with a result contained in the
    whole run's result [r], in an environment that extends [ρ] by the
    locations allocated on the way. *)
Definition kpost (ρ : senv) (k : cont) (r : list spath) : val → iProp Σ :=
  λ w, (∃ v s r' fr,
      ⌜k v s = Some r'⌝ ∗ ⌜∀ p, p ∈ r' → p ∈ r⌝ ∗
      ⌜vden (env_ext ρ fr) v = Some w⌝ ∗ ⌜length (e_ls ρ ++ fr) = s_nlocs s⌝ ∗
      ⌜pc_holds (env_ext ρ fr) (s_pc s)⌝ ∗ heap_den (env_ext ρ fr) (s_heap s))%I.

Lemma kpost_ext ρ fr k r r' w :
  (∀ p, p ∈ r' → p ∈ r) → kpost (env_ext ρ fr) k r' w ⊢ kpost ρ k r w.
Proof.
  iIntros (Hsub) "(%v & %s & %r'' & %fr2 & %Hk & %Hsub' & %Hv & %Hlen & %Hpc & Hh)".
  iExists v, s, r'', (fr ++ fr2). rewrite -!env_ext_app. iFrame. iPureIntro.
  split_and!; auto. by rewrite app_assoc.
Qed.

Lemma kpost_intro ρ k r v s w r' :
  k v s = Some r' → (∀ p, p ∈ r' → p ∈ r) → vden ρ v = Some w →
  length (e_ls ρ) = s_nlocs s → pc_holds ρ (s_pc s) →
  heap_den ρ (s_heap s) ⊢ kpost ρ k r w.
Proof.
  iIntros (Hk Hsub Hv Hlen Hpc) "Hh". iExists v, s, r', [].
  rewrite env_ext_nil app_nil_r. by iFrame.
Qed.

Lemma exec_sound n : ∀ e s k r ρ d,
  exec n e s k = Some r → eden ρ e = Some d →
  length (e_ls ρ) = s_nlocs s → pc_holds ρ (s_pc s) →
  heap_den ρ (s_heap s) ⊢ WP d {{ kpost ρ k r }}.
Proof.
  induction n as [|n IH]; intros e s k r ρ d Hex Hd Hlen Hpc; first done.
  destruct e as [v|x|x e1 e2|c e1 e2|t e|t|t e|t e1 e2|op t e1 e2|op t e|t1 t2 e|e|e|e1 e2|e];
    cbn [exec] in Hex; cbn [eden] in Hd.
  - (* EVal *)
    destruct (vden ρ v) as [w|] eqn:Hv; simplify_eq. iIntros "Hh". iApply wp_value.
    by iApply (kpost_intro with "Hh").
  - (* EVar *) done.
  - (* ELet *)
    destruct (eden ρ e1) as [d1|] eqn:Hd1, (eden ρ e2) as [d2|] eqn:Hd2; simplify_eq.
    iIntros "Hh". iApply wp_let_bind.
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (wv) "(%v & %s1 & %r1 & %fr & %Hk & %Hsub & %Hv & %Hlen1 & %Hpc1 & Hh)".
    iApply (wp_wand' with "[Hh]").
    { iApply (IH _ _ _ _ (env_ext ρ fr) _ Hk with "Hh"); [|exact Hlen1|exact Hpc1].
      apply eden_ssubst; [exact Hv|by apply eden_ext]. }
    iIntros (u) "Hu". by iApply (kpost_ext with "Hu").
  - (* EIf *)
    destruct (eden ρ c) as [dc|] eqn:Hdc, (eden ρ e1) as [d1|] eqn:Hd1,
      (eden ρ e2) as [d2|] eqn:Hd2; simplify_eq.
    iIntros "Hh". iApply (wp_bind (fill [IfCtx d1 d2])).
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hdc Hlen Hpc with "Hh").
    iIntros (wv) "(%v & %s1 & %r1 & %fr & %Hk & %Hsub & %Hv & %Hlen1 & %Hpc1 & Hh)".
    destruct v as [|b| | | |]; try done.
    destruct (exec n e1 (st_assume s1 b) k) as [ra|] eqn:Ha; last done.
    destruct (exec n e2 (st_assume s1 (BNot b)) k) as [rb|] eqn:Hb; last done.
    simplify_eq. cbn [vden] in Hv.
    destruct (beval (env_ext ρ fr) b) as [bb|] eqn:Hbb; simplify_eq.
    simpl. iApply wp_if_bool. destruct bb.
    + iApply (wp_wand' with "[Hh]").
      { iApply (IH _ _ _ _ (env_ext ρ fr) _ Ha with "Hh"); [by apply eden_ext|exact Hlen1|].
        constructor; [by apply bprop_beval|done]. }
      iIntros (u) "Hu". iApply (kpost_ext with "Hu"). intros p Hp. apply Hsub. set_solver.
    + iApply (wp_wand' with "[Hh]").
      { iApply (IH _ _ _ _ (env_ext ρ fr) _ Hb with "Hh"); [by apply eden_ext|exact Hlen1|].
        constructor; [by apply bprop_beval; rewrite /= Hbb|done]. }
      iIntros (u) "Hu". iApply (kpost_ext with "Hu"). intros p Hp. apply Hsub. set_solver.
  - (* EAlloc *)
    destruct (eden ρ e) as [d1|] eqn:Hd1; simplify_eq.
    iIntros "Hh". iApply (wp_bind (fill [AppRCtx (Val (GoInstruction (GoAlloc (ty_den t))))])).
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (wv) "(%v & %s1 & %r1 & %fr & %Hk & %Hsub & %Hv & %Hlen1 & %Hpc1 & Hh)".
    destruct (sort_ok t v) eqn:Hs; last done.
    simpl. iApply (wp_alloc_sval t (env_ext ρ fr) v with "[Hh]"); [done|done|].
    iIntros (l) "Hl".
    iApply (kpost_ext ρ fr k r r1 with "[-]"); first done.
    iExists _, _, r1, [l]. iSplit; first (iPureIntro; exact Hk).
    iSplit; first done.
    iSplit. { iPureIntro. by rewrite /= nth_error_snoc. }
    iSplit. { iPureIntro. rewrite /= !length_app /=. rewrite length_app in Hlen1. lia. }
    iSplit; first (iPureIntro; by apply pc_holds_ext).
    cbn [st_alloc s_heap heap_den]. iSplitL "Hl".
    + rewrite /cell_den /= nth_error_snoc //. by iApply pts_ext.
    + by iApply heap_den_ext.
  - (* EZero *)
    simplify_eq. destruct (wp_zero_sval t ρ) as (w & Hw & Hwp).
    iIntros "Hh". iApply Hwp. by iApply (kpost_intro with "Hh").
  - (* ELoad *)
    destruct (eden ρ e) as [d1|] eqn:Hd1; simplify_eq.
    iIntros "Hh". iApply (wp_bind (fill [AppRCtx (Val (GoInstruction (GoLoad (ty_den t))))])).
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (wv) "(%v & %s1 & %r1 & %fr & %Hk & %Hsub & %Hv & %Hlen1 & %Hpc1 & Hh)".
    destruct v as [| |[m|]| | |]; try done.
    destruct (hlookup m (s_heap s1)) as [v'|] eqn:Hlk; last done.
    destruct (sort_ok t v') eqn:Hs; last done.
    cbn [vden leval] in Hv.
    destruct (nth_error (e_ls (env_ext ρ fr)) m) as [lo|] eqn:Hlo; simplify_eq.
    iDestruct (heap_den_lookup with "Hh") as "[Hp Hback]"; [done|done|].
    simpl. iApply (wp_load_sval with "Hp"); first done.
    iIntros (w') "%Hw' Hp".
    iApply (kpost_ext ρ fr k r r1 with "[-]"); first done.
    iApply (kpost_intro with "[Hp Hback]"); [exact Hk|done|exact Hw'|exact Hlen1|exact Hpc1|].
    by iApply "Hback".
  - (* EStore *)
    destruct (eden ρ e1) as [d1|] eqn:Hd1, (eden ρ e2) as [d2|] eqn:Hd2; simplify_eq.
    iIntros "Hh". iApply wp_app_pair.
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (wv) "(%v1 & %s1 & %r1 & %fr1 & %Hk1 & %Hsub1 & %Hv1 & %Hlen1 & %Hpc1 & Hh)".
    iApply (wp_wand' with "[Hh]").
    { iApply (IH _ _ _ _ (env_ext ρ fr1) _ Hk1 with "Hh"); [by apply eden_ext|exact Hlen1|exact Hpc1]. }
    iIntros (wv2) "(%v2 & %s2 & %r2 & %fr2 & %Hk2 & %Hsub2 & %Hv2 & %Hlen2 & %Hpc2 & Hh)".
    destruct v1 as [| |[m|]| | |]; try done.
    destruct (sort_ok t v2) eqn:Hs2; last done.
    destruct (hupdate t m v2 (s_heap s2)) as [h'|] eqn:Hup; last done.
    cbn [vden leval] in Hv1.
    destruct (nth_error (e_ls (env_ext ρ fr1)) m) as [lo|] eqn:Hlo; simplify_eq.
    iDestruct (heap_den_update with "Hh") as (vold) "(%Hs & Hp & Hback)";
      [done|by apply nth_error_ext|].
    iApply (wp_store_sval t (env_ext (env_ext ρ fr1) fr2) lo vold v2 wv2 _ Hs Hs2 Hv2 with "Hp").
    iIntros "Hp".
    iApply (kpost_ext ρ fr1 k r r1 with "[-]"); first done.
    iApply (kpost_ext (env_ext ρ fr1) fr2 k r1 r2 with "[-]"); first done.
    iApply (kpost_intro with "[Hp Hback]"); [exact Hk2|done|done|exact Hlen2|exact Hpc2|].
    by iApply "Hback".
  - (* EBinOp *)
    destruct (eden ρ e1) as [d1|] eqn:Hd1, (eden ρ e2) as [d2|] eqn:Hd2; simplify_eq.
    iIntros "Hh". iApply wp_app_pair.
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (wv) "(%v1 & %s1 & %r1 & %fr1 & %Hk1 & %Hsub1 & %Hv1 & %Hlen1 & %Hpc1 & Hh)".
    iApply (wp_wand' with "[Hh]").
    { iApply (IH _ _ _ _ (env_ext ρ fr1) _ Hk1 with "Hh"); [by apply eden_ext|exact Hlen1|exact Hpc1]. }
    iIntros (wv2) "(%v2 & %s2 & %r2 & %fr2 & %Hk2 & %Hsub2 & %Hv2 & %Hlen2 & %Hpc2 & Hh)".
    destruct (sbinop_eval op t v1 v2) as [v|] eqn:Hop; last done.
    destruct (wp_binop_sval op t _ v1 v2 v _ _ Hop (vden_ext _ fr2 _ _ Hv1) Hv2) as (w & Hw & Hwp).
    iApply Hwp.
    iApply (kpost_ext ρ fr1 k r r1 with "[-]"); first done.
    iApply (kpost_ext (env_ext ρ fr1) fr2 k r1 r2 with "[-]"); first done.
    by iApply (kpost_intro with "Hh").
  - (* EUnOp *)
    destruct (eden ρ e) as [d1|] eqn:Hd1; simplify_eq.
    iIntros "Hh".
    iApply (wp_bind (fill [AppRCtx (Val (GoInstruction (GoUnOp (unop_den op) (ty_den t))))])).
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (wv) "(%v1 & %s1 & %r1 & %fr & %Hk & %Hsub & %Hv1 & %Hlen1 & %Hpc1 & Hh)".
    destruct (sunop_eval op t v1) as [v|] eqn:Hop; last done.
    destruct (wp_unop_sval op t _ v1 v _ Hop Hv1) as (w & Hw & Hwp).
    simpl. iApply Hwp.
    iApply (kpost_ext ρ fr k r r1 with "[-]"); first done.
    by iApply (kpost_intro with "Hh").
  - (* EConvert *)
    destruct (sty_eqb t1 t2) eqn:Heq; last done. apply sty_eqb_eq in Heq as <-.
    destruct (eden ρ e) as [d1|] eqn:Hd1; simplify_eq.
    iIntros "Hh".
    iApply (wp_bind (fill [AppRCtx (Val (GoInstruction (Convert (ty_den t1) (ty_den t1))))])).
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (w) "Hw". simpl. by iApply wp_convert_id.
  - (* EDo *)
    destruct (eden ρ e) as [d1|] eqn:Hd1; simplify_eq.
    iIntros "Hh". iApply (wp_bind (fill [AppRCtx (Val do_execute)])).
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (wv) "(%v & %s1 & %r1 & %fr & %Hk & %Hsub & %Hv & %Hlen1 & %Hpc1 & Hh)".
    simpl. iApply wp_do_exec.
    iApply (kpost_ext ρ fr k r r1 with "[-]"); first done.
    by iApply (kpost_intro with "Hh").
  - (* EReturn *)
    destruct (eden ρ e) as [d1|] eqn:Hd1; simplify_eq.
    iIntros "Hh". iApply (wp_bind (fill [AppRCtx (Val do_return)])).
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (wv) "(%v & %s1 & %r1 & %fr & %Hk & %Hsub & %Hv & %Hlen1 & %Hpc1 & Hh)".
    simpl. iApply wp_do_return.
    iApply (kpost_ext ρ fr k r r1 with "[-]"); first done.
    iApply (kpost_intro with "Hh"); [exact Hk|done| |exact Hlen1|exact Hpc1].
    by rewrite /= Hv.
  - (* EExcSeq *)
    destruct (eden ρ e1) as [d1|] eqn:Hd1, (eden ρ e2) as [d2|] eqn:Hd2; simplify_eq.
    iIntros "Hh".
    iApply (wp_bind (fill [AppRCtx (App (Val exception_seq) (Rec BAnon BAnon d2))])).
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (wv) "(%v & %s1 & %r1 & %fr & %Hk & %Hsub & %Hv & %Hlen1 & %Hpc1 & Hh)".
    destruct v as [| | | | |v0]; try done; cbn [vden] in Hv.
    + simplify_eq. simpl. iApply wp_exc_seq_exec.
      iApply (wp_wand' with "[Hh]").
      { iApply (IH _ _ _ _ (env_ext ρ fr) _ Hk with "Hh"); [by apply eden_ext|exact Hlen1|exact Hpc1]. }
      iIntros (u) "Hu". by iApply (kpost_ext with "Hu").
    + destruct (vden (env_ext ρ fr) v0) as [w0|] eqn:Hv0; simplify_eq.
      simpl. iApply wp_exc_seq_ret.
      iApply (kpost_ext ρ fr k r r1 with "[-]"); first done.
      iApply (kpost_intro with "Hh"); [exact Hk|done| |exact Hlen1|exact Hpc1].
      by rewrite /= Hv0.
  - (* EExcDo *)
    destruct (eden ρ e) as [d1|] eqn:Hd1; simplify_eq.
    iIntros "Hh". iApply (wp_bind (fill [AppRCtx (Val exception_do)])).
    iApply (wp_wand' with "[Hh]"); first by iApply (IH _ _ _ _ _ _ Hex Hd1 Hlen Hpc with "Hh").
    iIntros (wv) "(%v & %s1 & %r1 & %fr & %Hk & %Hsub & %Hv & %Hlen1 & %Hpc1 & Hh)".
    destruct v as [| | | | |v0]; try done; cbn [vden] in Hv.
    + simplify_eq. simpl. iApply wp_exc_do_exec.
      iApply (kpost_ext ρ fr k r r1 with "[-]"); first done.
      by iApply (kpost_intro with "Hh").
    + destruct (vden (env_ext ρ fr) v0) as [w0|] eqn:Hv0; simplify_eq.
      simpl. iApply wp_exc_do_ret.
      iApply (kpost_ext ρ fr k r r1 with "[-]"); first done.
      by iApply (kpost_intro with "Hh").
Qed.

(** * The theorem the tactic applies *)
Theorem symex_sound (ρ : senv) (se : sexpr) (d : expr) (h : list scell) (r : list spath)
    (Φ : val → iProp Σ) :
  eden ρ se = Some d →
  run se h (length (e_ls ρ)) = Some r →
  heap_den ρ h ∗ paths_goal ρ Φ r ⊢ WP d {{ Φ }}.
Proof.
  intros Hd Hrun. iIntros "[Hh Hgoal]".
  iApply (wp_wand' with "[Hh]").
  { iApply (exec_sound _ _ _ _ _ ρ d Hrun Hd with "Hh"); first done. constructor. }
  iIntros (w) "(%v & %s & %r' & %fr & %Hk & %Hsub & %Hv & %Hlen & %Hpc & Hh)".
  simplify_eq.
  iDestruct (paths_goal_elem _ _ _ (v, st_heap s (kept_cells (length (e_ls ρ)) v (s_heap s)))
              with "Hgoal") as "Hp"; first (apply Hsub; set_solver).
  iDestruct (heap_den_filter with "Hh") as "Hh".
  rewrite /path_goal /=.
  iDestruct (forall_locs_elim _ _ fr with "Hp") as "Hp".
  { rewrite length_app in Hlen. lia. }
  iDestruct (pc_wand_elim with "Hp") as "Hp"; first done.
  iDestruct (heap_wand_elim with "[$Hh $Hp]") as "Hp".
  by rewrite /vpost Hv.
Qed.

End sound.
