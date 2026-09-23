(** Semantic lemmas for the value, conversion and exception-monad cases of
    [exec] (fn/execInt.v, ..., fn/execExcSeq.v), in the style of
    exec_spec.v: [exec_sound_convert], [exec_sound_exc_seq], and the
    well-formedness of the singleton path list [onePath] returns. *)
From New.checker Require Import prelude nodes exec_spec.

(** The kind codes [W64 19] and [W64 20] belong to [TExec] and [TRet]
    alone; the monad cases dispatch on them without destructing the term. *)
Lemma term_code_TExec (u : term) : term_code u = W64 19 → u = TExec.
Proof.
  destruct u; simpl; try done;
    try destruct signed; intros Hc; exfalso; revert Hc; by vm_compute.
Qed.

Lemma term_code_TRet (u : term) : term_code u = W64 20 → ∃ x, u = TRet x.
Proof.
  destruct u; simpl; try (intros ?; by eauto);
    try destruct signed; intros Hc; exfalso; revert Hc; by vm_compute.
Qed.

Section exec_sound_a.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** * The singleton path list *)
Lemma paths_wf_single k (x : term) sst :
  wf_state sst → (k ≤ length (svars sst))%nat → vars_below (length (svars sst)) x →
  paths_wf k [mkPath x sst].
Proof.
  intros Hwf Hk Hx. split; intros q ->%list_elem_of_singleton; done.
Qed.

Lemma vars_below_ctype_zero k cty : vars_below k (ctype_zero cty).
Proof. by destruct cty. Qed.

(** * Conversion

    The checker only accepts a conversion between equal types, which is the
    identity. *)
Lemma exec_sound_convert (cty : ctype) (ce : cexpr) ρ sst ps :
  exec_sound ce ρ sst ps → exec_sound (CEConvert cty cty ce) ρ sst ps.
Proof.
  intros He Hwf Hρ V Hsat. iIntros "Hheap". simpl.
  iApply (wp_bind (fill [AppRCtx (Val (GoInstruction (Convert (type_of cty) (type_of cty))))])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw". simpl. by iApply (wp_convert cty w).
Qed.

(** * Exception sequencing

    On a path that ended in [execute], the second statement runs from that
    path's state; on a path that ended in a [return], the second statement is
    skipped and the path itself is a result. *)
Lemma exec_sound_exc_seq (ce1 ce2 : cexpr) ρ sst ps out :
  exec_sound ce1 ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps →
     (pret p = TExec ∧ ∃ qs, qs ⊆ out ∧ exec_sound ce2 ρ (pst p) qs) ∨
     ((∃ x, pret p = TRet x) ∧ p ∈ out)) →
  exec_sound (CEExcSeq ce1 ce2) ρ sst out.
Proof.
  intros He1 Hwfps Hcont Hwf Hρ V Hsat.
  iIntros "Hheap". simpl.
  iApply (wp_bind (fill [AppRCtx (App (Val exception_seq)
                                      (Lam BAnon (csubst (env_interp V ρ) ce2)))])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He1 Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  simpl.
  destruct (Hcont p Hin) as [[Hex (qs & Hsub & Hqs)]|[[x Hrx] Hout]].
  - assert (wf_state (pst p)) as Hwfp by (by apply (paths_wf_state _ _ Hwfps)).
    assert ((length (svars sst) ≤ length (svars (pst p)))%nat) as Hgrow
      by (by apply (paths_wf_grow _ _ Hwfps)).
    assert (env_below (length (svars (pst p))) ρ) as Hbp
      by (by eapply env_below_mono).
    rewrite Hret Hex /=.
    iApply wp_exc_seq_exec.
    rewrite (env_interp_agree (length (svars sst)) V V') //.
    iApply (wp_wand_r _ _ _ (paths_post (length (svars (pst p))) V' qs)).
    iSplitL "Hheap'".
    { by iApply (Hqs Hwfp Hbp V' Hsat' with "Hheap'"). }
    iIntros (u) "Hu".
    iApply (paths_post_mono _ _ qs out _ Hsub).
    iApply (paths_post_compose _ (length (svars (pst p))) V V' qs u Hgrow Hag).
    iExact "Hu".
  - rewrite Hret Hrx /=.
    iApply (wp_exc_seq_ret (teval V' x)).
    iExists p, V'. iFrame "Hheap'". iPureIntro.
    split_and!; [done|done| |done].
    by rewrite Hrx.
Qed.

End exec_sound_a.
