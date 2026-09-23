(** Adequacy of GooseLang for runs that do not crash, with the initial heap.

    [goose_adequacy_heap] turns a WP for [e] into facts about the executions
    of [e] from [σ] ([goose_adequate]): every value the main thread reduces
    to satisfies the postcondition, and no thread gets stuck. The WP may use
    every cell of the initial heap (in the lock state it starts in), and may
    assume that the Go local context of its ghost state is [σ]'s.

    The executions are those of [erased_step], which has no crash steps.
    (The proof goes through [goose_recv_adequacy_heap] with a restart program
    that is never run.) *)
From iris.proofmode Require Import proofmode.
From Perennial.goose_lang Require Import lang.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.goose_lang Require Export lifting recovery_lifting.
From Perennial.goose_lang Require Import adequacy recovery_adequacy crash_borrow.
Set Default Proof Using "Type".

Section heap_adequacy.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} {Hffi_adequacy:ffi_interp_adequacy}.
Context {go_gctx : GoGlobalContext}.

(** What the executions of [e] from [σ] and [g] satisfy. *)
Record goose_adequate (e : expr) (σ : state) (g : global_state) (φ : val → Prop) : Prop := {
  goose_adequate_result tp σ' g' v :
    rtc erased_step ([e], (σ, g)) (of_val v :: tp, (σ', g')) → φ v;
  goose_adequate_not_stuck tp σ' g' e' :
    rtc erased_step ([e], (σ, g)) (tp, (σ', g')) →
    e' ∈ tp → is_Some (to_val e') ∨ reducible e' σ' g';
}.

Theorem goose_adequacy_heap
        Σ `{!all.allG Σ} `{hPre: !gooseGpreS Σ} (e: expr) (σ: state) (g: global_state)
        (φ : val → Prop) :
  ffi_initgP g.(global_world) → ffi_initP σ.(world) g.(global_world) →
  (∀ (Hl : gooseLocalGS Σ) (Hg : gooseGlobalGS Σ),
    goose_go_local_context = σ.(go_state).(go_lctx) →
    ⊢ ffi_global_start goose_ffiGlobalGS g.(global_world) -∗
      ffi_local_start goose_ffiLocalGS σ.(world) -∗
      own_go_state σ.(go_state).(package_state) -∗
      ([∗ map] l ↦ lkv ∈ σ.(heap),
         na_heap_pointsto_st (tls lkv.1) l (DfracOwn 1) lkv.2) ={⊤}=∗
      WP e @ ⊤ {{ v, ⌜φ v⌝ }}) →
  goose_adequate e σ g φ.
Proof.
  intros Hinitg Hinit Hwp.
  assert (recv_adequate (CS := goose_crash_lang) NotStuck e (of_val #()) σ g
            (λ v _ _, φ v) (λ _ _ _, True) (λ _ _, True)) as Had.
  { eapply goose_recv_adequacy_heap with (n:=0%nat); [done..|].
    intros Hl Hg Hlctx. exists (λ _, True)%I.
    iIntros "Hstartg Hstart Hgo Hcells _".
    iMod (Hwp Hl Hg Hlctx with "Hstartg Hstart Hgo Hcells") as "Hwp". iModIntro.
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
      iApply wpc_value; eauto. } }
  destruct Had as [Hnormal _ Hnotstuck _]. split.
  - intros tp σ' g' v Hsteps. apply (Hnormal tp σ' g' v). by constructor.
  - intros tp σ' g' e' Hsteps Hin. apply (Hnotstuck tp σ' g' e' Normal); [done| |done].
    by constructor.
Qed.

End heap_adequacy.
