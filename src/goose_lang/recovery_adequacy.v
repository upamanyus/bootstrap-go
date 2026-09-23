From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap_view.
From Perennial.goose_lang Require Import lang.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.goose_lang Require Export lifting recovery_lifting.
From Perennial.goose_lang Require Import adequacy lang crash_borrow.
Set Default Proof Using "Type".

(** [na_heap_name_init], but also handing out every cell of the initial heap,
    in the lock state it starts in. *)
Lemma na_heap_name_init_pointsto `{Countable L} `{!BlockAddr L} {V} `{!na_heapGpreS L V Σ}
    {LK} (tls : LK → lock_state) (σ : gmap L (LK * V)) :
  ⊢ |==> ∃ names : na_heap_names,
    na_heap_ctx (hG := na_heapGS_update_pre _ names) tls σ ∗
    [∗ map] l ↦ lkv ∈ σ,
      na_heap_pointsto_st (hG := na_heapGS_update_pre _ names) (tls lkv.1) l (DfracOwn 1) lkv.2.
Proof.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) (∅ : gmap L (na_heap_cmra V)))) as (γh) "Hh".
  { apply gmap_view_auth_valid. }
  iMod (own_update with "Hh") as "[Hh Hfrag]".
  { apply (gmap_view_alloc_big _ (to_na_heap tls σ) (DfracOwn 1));
      [apply map_disjoint_empty_r|done|].
    intros l x Hx. rewrite /to_na_heap in Hx.
    apply lookup_fmap_Some in Hx as (lkv & <- & _).
    split; simpl; last done. by destruct (tls lkv.1). }
  rewrite right_id_L.
  iMod (own_alloc (● to_na_size ∅)) as (γs) "Hs".
  { rewrite auth_auth_valid. exact: to_na_size_valid. }
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) (∅ : gmap L (agreeR gnameO)))) as (γm) "Hm".
  { apply gmap_view_auth_valid. }
  iModIntro. iExists {| na_heap_heap_name := γh; na_heap_size_name := γs; na_heap_meta_name := γm |}.
  iSplitR "Hfrag".
  - iExists ∅, ∅; simpl. iFrame "Hh Hm". rewrite dom_empty_L. iFrame.
    iPureIntro; split.
    + set_solver.
    + rewrite /block_sizes_wf. set_solver.
  - rewrite big_opM_own_1 /to_na_heap big_sepM_fmap. done.
Qed.

(** The general form: besides the FFI's and the package state's initial
    resources, the program gets every cell of the initial heap (in the lock
    state it starts in), and it may assume that the Go local context of its
    ghost state is that of the initial state. *)
Theorem goose_recv_adequacy_heap `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
  {go_gctx : GoGlobalContext}
  {Hffi_adequacy:ffi_interp_adequacy} Σ `{!all.allG Σ} `{hPre: !gooseGpreS Σ} s e r σ g φ φr φinv n :
  ffi_initgP g.(global_world) → ffi_initP σ.(world) g.(global_world) →
  (∀ (Hl : gooseLocalGS Σ) (Hg : gooseGlobalGS Σ),
     goose_go_local_context = σ.(go_state).(go_lctx) → ∃ Φinv,
     ⊢ ffi_global_start goose_ffiGlobalGS g.(global_world) -∗
       ffi_local_start goose_ffiLocalGS σ.(world) -∗
       own_go_state σ.(go_state).(package_state) -∗
       ([∗ map] l ↦ lkv ∈ σ.(heap),
          na_heap_pointsto_st (tls lkv.1) l (DfracOwn 1) lkv.2) -∗
       pre_borrowN n ={⊤}=∗
       □ (∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       □ (∀ hL : gooseLocalGS Σ,
           let hG := HeapGS _ _ _ hL _ in
           Φinv hG -∗ □ ∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       wpr s ⊤ e r (λ v, ⌜φ v⌝) (Φinv) (λ _ v, ⌜φr v⌝)) →
  recv_adequate (CS := goose_crash_lang) s e r σ g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
Proof.
  intros Hinit Hinitg Hwp.
  eapply (wp_recv_adequacy_inv Σ _ _ (n * 4 + crash_borrow_ginv_number)).
  iIntros (???).
  iMod (na_heap_name_init_pointsto tls σ.(heap)) as (name_na_heap) "[Hh Hcells]".
  iMod (ffi_global_init _ _ g.(global_world)) as (ffi_namesg) "(Hgw&Hgstart)"; first by eauto.
  iMod (ffi_local_init _ _ σ.(world)) as (ffi_names) "(Hw&Hstart)"; first by eauto.
  iMod (go_state_init _ σ.(go_state).(package_state)) as (globals_name) "(Hg & Hgfrag)".
  iMod (credit_name_init (n*4 + crash_borrow_ginv_number)) as (name_credit) "(Hcred_auth&Hcred&Htok)".
  iDestruct (cred_frag_split with "Hcred") as "(Hpre&Hcred)".
  iMod (proph_map_init κs g.(used_proph_id)) as (proph_names) "Hproph".

  set (creditH:=creditGS_update_pre Σ (@goose_preG_credit ext ffi ffi_sem ffi_interp0 Hffi_adequacy Σ hPre)
          name_credit).
  iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">#Hinv".
  { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }
  (* TODO(RJ): reformulate init lemmas to better match what we need here. *)
  set (hG := GooseGlobalGS _ _ proph_names (creditGS_update_pre _ _ name_credit) ffi_namesg).
  set (hL := GooseLocalGS Σ Hc ffi_names
                          (σ.(go_state).(go_lctx))
                          (na_heapGS_update_pre _ name_na_heap)
                          (go_stateGS_update_pre Σ _ globals_name)).
  destruct (Hwp hL hG eq_refl) as [Φinv Hwp']. clear Hwp.
  iExists state_interp, global_state_interp, fork_post.
  iExists _, _.
  iExists ((λ Hinv hGen, ∃ hL:gooseLocalGS Σ, ⌜hGen = goose_generationGS (L:=hL)⌝ ∗ Φinv (HeapGS _ _ _ hL _)))%I.
  iDestruct (@cred_frag_to_pre_borrowN _ _ _ _ _ hG _ n with "Hpre") as "Hpre".
  iMod (Hwp' with "[$] [$] [$] Hcells [$]") as "(#H1&#H2&Hwp)".
  iModIntro.
  iSplitR.
  { iModIntro. iIntros (??) "Hσ".
    iApply ("H1" with "Hσ").
  }
  iSplitR.
  {
    iModIntro. iIntros (HG') "(%hL' & -> & H)".
    iApply "H2". done.
  }
  iFrame. iFrame "Hinv". iSplitR; first done. iSplitR; first done.
  rewrite /wpr.
  iApply (recovery_weakestpre.wpr_strong_mono with "Hwp").
  iSplit; first by eauto.
  iSplit; first by eauto.
  iIntros (? v) "(% & % & $)". done.
Qed.

Theorem goose_recv_adequacy `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}
  {go_gctx : GoGlobalContext}
  {Hffi_adequacy:ffi_interp_adequacy} Σ `{!all.allG Σ} `{hPre: !gooseGpreS Σ} s e r σ g φ φr φinv n :
  ffi_initgP g.(global_world) → ffi_initP σ.(world) g.(global_world) →
  (∀ (Hl : gooseLocalGS Σ) (Hg : gooseGlobalGS Σ), ∃ Φinv,
     ⊢ ffi_global_start goose_ffiGlobalGS g.(global_world) -∗
       ffi_local_start goose_ffiLocalGS σ.(world) -∗
       own_go_state σ.(go_state).(package_state) -∗
       pre_borrowN n ={⊤}=∗
       □ (∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       □ (∀ hL : gooseLocalGS Σ,
           let hG := HeapGS _ _ _ hL _ in
           Φinv hG -∗ □ ∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       wpr s ⊤ e r (λ v, ⌜φ v⌝) (Φinv) (λ _ v, ⌜φr v⌝)) →
  recv_adequate (CS := goose_crash_lang) s e r σ g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
Proof.
  intros Hinit Hinitg Hwp. apply (goose_recv_adequacy_heap Σ s e r σ g φ φr φinv n); [done|done|].
  intros Hl Hg _. destruct (Hwp Hl Hg) as [Φinv Hwp']. exists Φinv.
  iIntros "Hgs Hls Hgo _ Hpre". iApply (Hwp' with "Hgs Hls Hgo Hpre").
Qed.

Section failstop.

Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy}.
Context {go_gctx : GoGlobalContext}.

(* We can model failstop execution by just having the restart thread be a trivial program that just halts.
   Thus, the machine "restarts" after a crash but it does not do anything. *)
Definition adequate_failstop (e: expr) (σ: state) (g: global_state)
    (φpost : val → state → global_state → Prop) :=
  recv_adequate (CS := goose_crash_lang) NotStuck e (of_val #()) σ g φpost (λ _ _ _, True) (λ _ _, True).

(* Like above, but, for failstop execution one only needs to prove a wp, not a
wpr. Due to that, no φinv is supported (since after the crash σ changed so
[φinv σ] no longer has any reason to hold). *)
Theorem goose_recv_adequacy_failstop
        Σ `{!all.allG Σ} `{hPre: !gooseGpreS Σ} (e: expr) (σ: state) (g: global_state) φpost :
  ffi_initgP g.(global_world) → ffi_initP σ.(world) g.(global_world) →
  (∀ (Hl : gooseLocalGS Σ) (Hg : gooseGlobalGS Σ),
    ⊢ ffi_global_start goose_ffiGlobalGS g.(global_world) -∗
      ffi_local_start goose_ffiLocalGS σ.(world) ={⊤}=∗
      WP e @ ⊤ {{ v, ⌜φpost v⌝ }}) →
  adequate_failstop e σ g (λ v _ _, φpost v).
Proof.
  intros Hinitg Hinit Hwp. eapply goose_recv_adequacy with (n:=0%nat); [done..|].
  exists (λ _, True)%I.
  iIntros "Hstartg Hstart _ _".
  iMod (Hwp with "Hstartg Hstart") as "Hwp". iModIntro.
  iSplitR.
  { iIntros "!> * _". iApply ncfupd_mask_intro; auto. }
  iSplitR.
  { do 2 iIntros "!> * _". iApply ncfupd_mask_intro; auto. }
  iApply (idempotence_wpr (hG:=HeapGS _ _ _ _ _) _ _ _ _ _ _ _ (λ _, True%I) with "[Hwp] []").
  { iApply wp_wpc. eauto. }
  { iModIntro. iIntros (????) "_".
    iModIntro.
    rewrite /crash_modality.post_crash.
    iIntros (???) "H". iModIntro; iFrame. iIntros "H". iSplit; first auto.
    iApply wpc_value; eauto.
  }
Qed.

End failstop.
