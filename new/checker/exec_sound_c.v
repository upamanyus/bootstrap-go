(** Semantic lemmas for the [if], allocation and store cases of [exec]
    (checker/exec.go): the shapes [execIfs], [execAlloc] and [execStore]
    actually produce.

    - [exec_sound_if_gen] generalizes [exec_sound_if] (exec_spec.v) to what
      [execIf] does per path: a *literal* condition takes one branch with the
      state unchanged, anything else forks with the condition (resp. its
      negation) assumed.
    - [exec_sound_store] is the store case, which exec_spec.v does not have.
    - [paths_wf_alloc] / [paths_wf_store] are the well-formedness of the
      result lists [execAlloc] and [storeAll] build. *)
From New.checker Require Import prelude nodes exec_spec.
From New.checker.fn Require Import heapUpdate.

Section exec_sound_c.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** * Well-formedness of the result lists *)

(** The path [execAlloc] produces from a path of its operand. *)
Definition alloc_path (p : spath) : spath :=
  mkPath (TVar (length (svars (pst p)))) (st_alloc (pst p) (pret p)).

Lemma paths_wf_alloc k ps : paths_wf k ps → paths_wf k (alloc_path <$> ps).
Proof.
  intros Hwf. split.
  - intros p' (p & -> & Hp)%list_elem_of_fmap. simpl.
    apply wf_state_alloc; [by apply (paths_wf_state _ _ Hwf)|by apply (paths_wf_ret _ _ Hwf)].
  - intros p' (p & -> & Hp)%list_elem_of_fmap. cbn [alloc_path pst st_alloc svars].
    rewrite length_app /=. pose proof (paths_wf_grow _ _ Hwf p Hp). lia.
  - intros p' (p & -> & Hp)%list_elem_of_fmap. cbn [alloc_path pst pret st_alloc svars].
    rewrite length_app /=. cbn [vars_below]. lia.
Qed.

(** The state [storeAll] produces: only the heap changes. *)
Definition st_heap (sst : sstate) (H : list scell) : sstate :=
  mkState H (spc sst) (svars sst).

Lemma heap_update_below k H x y H' :
  heap_below k H → vars_below k y → heap_update H x y = Some H' → heap_below k H'.
Proof.
  revert H'. induction H as [|c H IH]; first done.
  intros H' Hb Hy. simpl. destruct (decide (cloc c = x)).
  - intros [= <-]. intros c' [->|Hc']%elem_of_cons.
    + split; [apply (Hb c); set_solver|done].
    + apply Hb. set_solver.
  - destruct (heap_update H x y) as [H''|] eqn:Hup; last done.
    intros [= <-]. intros c' [->|Hc']%elem_of_cons.
    + apply Hb. set_solver.
    + eapply IH; [|done|done|done]. intros c'' Hc''. apply Hb. set_solver.
Qed.

Lemma wf_state_heap sst x y H' :
  wf_state sst → vars_below (length (svars sst)) y →
  heap_update (sheap sst) x y = Some H' → wf_state (st_heap sst H').
Proof.
  intros [Hh Hpc] Hy Hup. split; cbn [st_heap sheap spc svars]; last done.
  by eapply heap_update_below.
Qed.


(** * [if]

    What [execIf] establishes for one path [p] of the condition, with result
    list [qs]. *)
Definition if_ok (ct cf : cexpr) ρ (p : spath) (qs : list spath) : Prop :=
  (∃ b, pret p = TBool b ∧ exec_sound (if b then ct else cf) ρ (pst p) qs) ∨
  (exec_sound ct ρ (st_assume (pst p) (pret p)) qs ∧
   exec_sound cf ρ (st_assume (pst p) (negate (pret p))) qs).

Lemma if_ok_mono ct cf ρ p qs qs' :
  qs ⊆ qs' → if_ok ct cf ρ p qs → if_ok ct cf ρ p qs'.
Proof.
  intros Hsub [(b & Hb & Hs)|[H1 H2]].
  - left. exists b. split; first done. by eapply exec_sound_mono.
  - right. split; by eapply exec_sound_mono.
Qed.

Lemma exec_sound_if_gen (cc ct cf : cexpr) ρ sst ps out :
  exec_sound cc ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → sort_of_vars (svars (pst p)) (pret p) = Some SBool) →
  (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧ if_ok ct cf ρ p qs) →
  exec_sound (CEIf cc ct cf) ρ sst out.
Proof.
  intros Hc Hwfps Hsort Hbr Hwf Hρ V Hsat.
  iIntros "Hheap". simpl.
  iApply (wp_bind (fill [IfCtx (csubst (env_interp V ρ) ct)
                               (csubst (env_interp V ρ) cf)])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (Hc Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  assert (wf_state (pst p)) as Hwfp by (by apply (paths_wf_state _ _ Hwfps)).
  assert ((length (svars sst) ≤ length (svars (pst p)))%nat) as Hgrow
    by (by apply (paths_wf_grow _ _ Hwfps)).
  assert (vars_below (length (svars (pst p))) (pret p)) as Hbret
    by (by apply (paths_wf_ret _ _ Hwfps)).
  assert (env_below (length (svars (pst p))) ρ) as Hbp
    by (by eapply env_below_mono).
  assert (has_sort (teval V' (pret p)) SBool) as [b Hb].
  { eapply sort_of_vars_sound; last by apply Hsort.
    by destruct Hsat'. }
  destruct (Hbr p Hin) as (qs & Hsub & Hok).
  rewrite Hret Hb (env_interp_agree (length (svars sst)) V V') //.
  iApply wp_if_bval.
  (* after the branch, the result is a path of [qs] over a valuation that
     agrees with [V'] far enough *)
  iAssert (∀ k u, ⌜(length (svars (pst p)) ≤ k)%nat⌝ -∗
             paths_post k V' qs u -∗ paths_post (length (svars sst)) V out u)%I
    as "Hfin".
  { iIntros (k u Hk) "Hu".
    iApply (paths_post_mono _ _ qs out _ Hsub).
    iApply (paths_post_compose _ (length (svars (pst p))) V V' qs u Hgrow Hag).
    iApply (paths_post_compose _ k V' V' qs u Hk (agree_below_refl _ _)).
    iExact "Hu". }
  destruct Hok as [(b' & Hlit & Hqs)|[Hqt Hqf]].
  - (* a literal condition: one branch, state unchanged *)
    assert (b' = b) as ->.
    { rewrite Hlit /= in Hb. destruct b, b'; try done; exfalso;
        apply (f_equal (λ v, bool_decide (v = bval true))) in Hb;
        rewrite /bval in Hb; vm_compute in Hb; congruence. }
    iApply (wp_wand_r _ _ _ (paths_post (length (svars (pst p))) V' qs)).
    iSplitL "Hheap'".
    { destruct b; iApply (Hqs Hwfp Hbp V' Hsat' with "Hheap'"). }
    iIntros (u) "Hu". iApply ("Hfin" with "[] Hu"). done.
  - destruct b.
    + iApply (wp_wand_r _ _ _
                (paths_post (length (svars (st_assume (pst p) (pret p)))) V' qs)).
      iSplitL "Hheap'".
      { iApply (Hqt _ _ V' _ with "Hheap'").
        Unshelve.
        - by apply wf_state_assume.
        - exact Hbp.
        - by apply st_sat_assume. }
      iIntros (u) "Hu". iApply ("Hfin" with "[] Hu"). done.
    + iApply (wp_wand_r _ _ _
                (paths_post (length (svars (st_assume (pst p) (negate (pret p))))) V' qs)).
      iSplitL "Hheap'".
      { iApply (Hqf _ _ V' _ with "Hheap'").
        Unshelve.
        - apply wf_state_assume; [done|by apply vars_below_negate].
        - exact Hbp.
        - apply st_sat_assume; first done.
          rewrite (teval_negate V' (pret p) false) //. }
      iIntros (u) "Hu". iApply ("Hfin" with "[] Hu"). done.
Qed.

(** * Store *)

(** Like [heap_interp_update], but the location comes out of the matching
    cell rather than being supplied: the operand of a store is only known to
    be a location because a cell of the heap is at it. *)
Lemma heap_interp_update_ex V H H' (x y : term) :
  heap_update H x y = Some H' →
  heap_interp V H -∗
  ∃ (lo : loc) (z : term), ⌜teval V x = lval lo⌝ ∗
     heap_pointsto lo (DfracOwn 1) (teval V z) ∗
     (heap_pointsto lo (DfracOwn 1) (teval V y) -∗ heap_interp V H').
Proof.
  revert H'. induction H as [|c H IH]; first done.
  intros H'. simpl. destruct (decide (cloc c = x)) as [Heq|Hne].
  - intros Hh. assert (H' = mkCell (cloc c) y :: H) as -> by congruence.
    iIntros "[Hc HH]". iDestruct "Hc" as (lo) "[%Hl Hp]".
    iExists lo, (cval c). rewrite Heq in Hl. iFrame "Hp". iSplit; first done.
    iIntros "Hp". iFrame "HH". iExists lo. rewrite /= Heq. by iFrame "Hp".
  - destruct (heap_update H x y) as [H''|] eqn:Hup; last done.
    intros Hh. assert (H' = c :: H'') as -> by (simpl in Hh; congruence).
    iIntros "[Hc HH]".
    iDestruct (IH H'' eq_refl with "HH") as (lo z) "(%Hl & Hp & Hback)".
    iExists lo, z. iFrame "Hp". iSplit; first done.
    iIntros "Hp". iFrame "Hc". by iApply "Hback".
Qed.

(** What [storeAll] establishes for the paths [qs] of the stored value, at
    location term [x], with result list [out]. *)
Definition store_ok (x : term) (qs out : list spath) : Prop :=
  ∀ q, q ∈ qs → ∃ H', heap_update (sheap (pst q)) x (pret q) = Some H' ∧
                     mkPath TUnit (st_heap (pst q) H') ∈ out.

Lemma exec_sound_store (cty : ctype) (ce1 ce2 : cexpr) ρ sst ps out :
  exec_sound ce1 ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ qs, exec_sound ce2 ρ (pst p) qs ∧
                       paths_wf (length (svars (pst p))) qs ∧
                       store_ok (pret p) qs out) →
  exec_sound (CEStore cty ce1 ce2) ρ sst out.
Proof.
  intros He1 Hwfps Hcont Hwf Hρ V Hsat. iIntros "Hheap". simpl.
  iApply (wp_bind (fill [PairLCtx (csubst (env_interp V ρ) ce2);
                         AppRCtx (Val (GoInstruction (GoStore (type_of cty))))])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He1 Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  destruct (Hcont p Hin) as (qs & Hqs & Hwfqs & Hst).
  assert (wf_state (pst p)) as Hwfp by (by apply (paths_wf_state _ _ Hwfps)).
  assert ((length (svars sst) ≤ length (svars (pst p)))%nat) as Hgrow
    by (by apply (paths_wf_grow _ _ Hwfps)).
  assert (vars_below (length (svars (pst p))) (pret p)) as Hbret
    by (by apply (paths_wf_ret _ _ Hwfps)).
  assert (env_below (length (svars (pst p))) ρ) as Hbp
    by (by eapply env_below_mono).
  simpl.
  iApply (wp_bind (fill [PairRCtx w;
                         AppRCtx (Val (GoInstruction (GoStore (type_of cty))))])).
  rewrite (env_interp_agree (length (svars sst)) V V') //.
  iApply (wp_wand_r _ _ _ (paths_post (length (svars (pst p))) V' qs)).
  iSplitL "Hheap'".
  { by iApply (Hqs Hwfp Hbp V' Hsat' with "Hheap'"). }
  iIntros (w2) "Hw2".
  iDestruct "Hw2" as (q V'') "(%Hinq & %Hag2 & %Hret2 & %Hsat'' & Hheap'')".
  destruct (Hst q Hinq) as (H' & Hup & Hout).
  iDestruct (heap_interp_update_ex V'' _ _ _ _ Hup with "Hheap''")
    as (lo z) "(%Hl & Hp & Hback)".
  assert (w = lval lo) as Hw.
  { rewrite Hret -Hl. by apply (teval_agree (length (svars (pst p)))). }
  simpl. rewrite Hw Hret2 -lval_eq.
  wp_pures.
  iApply (wp_ctype_store_any cty lo (teval V'' z) (teval V'' (pret q)) with "Hp").
  iIntros "!> Hp".
  iExists (mkPath TUnit (st_heap (pst q) H')), V''.
  iSplit; first (iPureIntro; exact Hout).
  iSplit.
  { iPureIntro. eapply agree_below_trans; first exact Hag.
    eapply agree_below_weaken; [exact Hgrow|exact Hag2]. }
  iSplit; first (iPureIntro; by rewrite uval_eq).
  iSplit.
  { iPureIntro. destruct Hsat'' as [Hv Hpc]. split; done. }
  by iApply "Hback".
Qed.

End exec_sound_c.
