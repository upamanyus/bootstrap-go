(** Adequacy of the checker: a closed execution of [checker.Check] that
    returns [true] establishes the Hoare triple.

    [check_sound] (soundness.v) is a separation-logic statement: its promise
    lives inside the program logic, relative to one choice of ghost state. This
    file discharges the program logic for a concrete run. Suppose [Check] is
    started in a state [σ] whose heap holds the input trees ([inputs_in],
    layout.v, a plain proposition about [σ.(heap)]), and the run reduces, with
    no crash, to [#true] (with any other threads in any state). Then
    [triple_holds] (defs.v): the triple of [check_sound] holds for [f], in
    every ghost state and under every Go semantics satisfying the
    assumptions.

    The proof is the fail-stop adequacy theorem of GooseLang, in the form
    [goose_recv_adequacy_failstop_heap] (src/goose_lang/recovery_adequacy.v),
    which also hands the program the cells of the initial heap. Inside it,
    [wp_Check_closed] reads the input trees out of those cells and runs
    [wp_Check]. The postcondition that adequacy extracts has to be a fact
    that does not mention the ghost state adequacy allocates, and
    [triple_holds] is that fact: the checker's specifications promise their
    results in every ghost state (see exec_spec.v). *)
From New.checker Require Import prelude layout.
From New.checker.fn Require Import Check.
From Perennial.goose_lang Require Import adequacy recovery_adequacy.

Section closed.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The checker package has no dependencies and a trivial initialisation
    predicate (defs.v). *)
Lemma is_pkg_init_checker : ⊢@{iProp Σ} is_pkg_init checker.
Proof. rewrite is_pkg_init_unfold /named /=. iSplit; iModIntro; done. Qed.

(** [checker.Check], from the raw cells of a heap holding its input. *)
Lemma wp_Check_closed (h : heap_t) (cf : cfunc) (vs : list sort) (P Q : cassn)
    (lf : loc) (sv : slice.t) (lpre lpost : loc) :
  inputs_in h lf cf sv vs lpre P lpost Q →
  ([∗ map] l ↦ lkv ∈ h, na_heap_pointsto_st (tls lkv.1) l (DfracOwn 1) lkv.2) ={⊤}=∗
  WP @! checker.Check #lf #sv #lpre #lpost {{ v, ⌜v = #true → triple_holds cf vs P Q⌝ }}.
Proof.
  iIntros (Hin) "Hcells".
  iMod (heap_ro_init with "Hcells") as "#Hro".
  iDestruct (inputs_in_sound with "Hro") as "(Hf & Hs & Hpre & Hpost)"; first done.
  iModIntro.
  iApply (wp_Check cf vs P Q lf sv lpre lpost with "[$Hf $Hs $Hpre $Hpost]").
  { iApply is_pkg_init_checker. }
  iIntros "!>" (b) "%Hb". iPureIntro. intros Heq.
  apply Hb. by apply (inj into_val) in Heq.
Qed.

End closed.

Section adequacy.
Context {ext : ffi_syntax} {ffi : ffi_model} {ffi_sem : ffi_semantics ext ffi}
        {ffi_interp0 : ffi_interp ffi} {Hffi_adequacy : ffi_interp_adequacy}.
(** The Go semantics the run is in. *)
Context {go_gctx : GoGlobalContext} {lctx : GoLocalContext}
        {sem : go.Semantics} {package_sem : checker.Assumptions}.

(** The ghost state the run is carried out in. *)
Definition checkΣ : gFunctors := #[heapΣ; all.allΣ].

(** The adequacy statement. [erased_step] ignores crashes: this is a run of
    the machine that did not crash. *)
Theorem check_adequate (f : cfunc) (vars : list sort) (pre post : cassn)
    (lf : loc) (svars : slice.t) (lpre lpost : loc)
    (σ σ' : state) (g g' : global_state) (tp : list expr) :
  ffi_initgP g.(global_world) → ffi_initP σ.(world) g.(global_world) →
  σ.(go_state).(go_lctx) = lctx →
  inputs_in σ.(heap) lf f svars vars lpre pre lpost post →
  rtc erased_step ([(@! checker.Check #lf #svars #lpre #lpost)%E], (σ, g))
                  (of_val #true :: tp, (σ', g')) →
  triple_holds f vars pre post.
Proof.
  intros Hinitg Hinit Hlctx Hin Hsteps.
  assert (adequate_failstop (@! checker.Check #lf #svars #lpre #lpost)%E σ g
            (λ v _ _, v = #true → triple_holds f vars pre post)) as Had.
  { apply (goose_recv_adequacy_failstop_heap checkΣ); [done|done|].
    intros Hl Hg Hctx.
    (* The run's Go local context is [lctx], so [sem] and [package_sem]
       describe the semantics of the ghost state adequacy provides. *)
    destruct Hl as [crashG ffiL lctx' naG goG]. simpl in Hctx.
    rewrite Hlctx in Hctx. subst lctx'.
    iIntros "_ _ _ Hcells".
    iApply (wp_Check_closed (hG := HeapGS checkΣ _ Hg (GooseLocalGS _ crashG ffiL lctx naG goG) _)
              with "Hcells").
    done. }
  destruct Had as [Hnormal _ _ _].
  pose proof (Hnormal tp σ' g' #true) as Hres. simpl in Hres.
  apply Hres; last done.
  by constructor.
Qed.

End adequacy.
