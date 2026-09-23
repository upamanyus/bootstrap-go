(** [checker.sortOfEnv] (checker/sorts.go): the sort of a term in a sort
    environment.

    Note on naming: no Rocq variable here may be called [e], [t], [sa], [sb],
    [sc], [oka], [okb] or [okc] -- those are the Go function's own locals and
    [wp_auto] derives Rocq identifiers from them.

    Note on shape: the specification is stated once as an [iProp]
    ([sortOfEnv_spec]) and proved by one lemma per shape of term, each taking
    the Löb induction hypothesis as an argument.  Proving all eighteen cases
    inside a single [Lemma] works but builds a proof term of several
    gigabytes, which does not fit in a shared session. *)
From New.checker Require Import prelude nodes.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The Go function is nil-safe, so its specification is over an [option term];
    the nil pointer has no sort. *)
Definition osort_of (E : sort_env) (ot : option term) : option sort :=
  match ot with None => None | Some ty => sort_of E ty end.

(** The two components the Go function returns. On failure it answers
    [(SortInt, false)], and [SortInt]'s code is [W64 0]. *)
Definition osort_code (os : option sort) : w64 :=
  match os with Some s => sort_code s | None => W64 0 end.
Definition osort_ok (os : option sort) : bool :=
  match os with Some _ => true | None => false end.

(** The Go code compares sorts by their codes, [sort_of] by [decide]; the two
    agree because the encoding is injective. *)
Lemma sort_code_inj s1 s2 : sort_code s1 = sort_code s2 → s1 = s2.
Proof. destruct s1, s2; try done; intros Hc; exfalso; revert Hc; by vm_compute. Qed.

(** The four points-to that [sortOfEnv] reads.  They are kept apart from
    [is_sortenv] so that [wp_auto] can see them and so that every recursive
    call is about the same three slices. *)
Definition env_pts (dq : dfrac) (lenv : loc) (Env : sort_env)
    (svs sps sks : slice.t) : iProp Σ :=
  (lenv ↦{dq} checker.sortEnv.mk svs sps sks (sort_code (se_ret Env)) (se_ret_ok Env) ∗
   svs ↦*{dq} (sort_code <$> se_vars Env) ∗
   sps ↦*{dq} (sort_code <$> se_pats Env) ∗
   sks ↦*{dq} se_pat_ok Env)%I.

Definition sortOfEnv_spec (dq : dfrac) (lenv : loc) (Env : sort_env)
    (svs sps sks : slice.t) (lterm : loc) (oty : option term) : iProp Σ :=
  ({{{ is_pkg_init checker ∗ env_pts dq lenv Env svs sps sks ∗ is_oterm lterm oty }}}
     @! checker.sortOfEnv #lenv #lterm
   {{{ RET (#(osort_code (osort_of Env oty)), #(osort_ok (osort_of Env oty)));
       env_pts dq lenv Env svs sps sks }}})%I.

Local Ltac red_sort :=
  cbn [osort_of osort_code osort_ok sort_of sort_code term_a term_b term_c].
Local Ltac finish := iApply "HΦ"; iFrame.
Local Ltac neq_sort :=
  exfalso;
  match goal with H : sort_code _ = sort_code _ |- _ => apply sort_code_inj in H end;
  done.

(** Everything up to the dispatch on the node's kind. *)
(** A name introduced inside an [Ltac] body is not visible to the caller, so
    everything the case scripts refer to by name -- the children [la]/[lb]/[lc],
    [Hidx], the slice lengths -- is introduced at the call site instead. *)
Local Ltac open_node :=
  rewrite /sortOfEnv_spec /env_pts;
  wp_start as "((Hstruct & Hvars & Hpats & Hpok) & #Hot)";
  iDestruct (is_oterm_null with "Hot") as %Hnull;
  wp_auto;
  wp_if_destruct; first (exfalso; naive_solver).

(** The case analyses that follow the recursive calls.  They are kept as
    narrow as the Go code allows -- [&&] short-circuits, so a [false] [ok]
    flag makes the operand sorts irrelevant -- because every extra branch is
    another [wp_auto] over the (large) rest of the function body. *)

(** [x] and [y] must both have sort [SInt]. *)
Local Ltac bin_int E x y :=
  destruct (sort_of E x) as [[]|], (sort_of E y) as [sy|]; red_sort;
  [ destruct sy; red_sort | idtac .. ]; try wp_auto; finish.

(** [x] must have a particular sort. *)
Local Ltac un_sort E x :=
  destruct (sort_of E x) as [[]|]; red_sort; try wp_auto; finish.

(** The condition of an [ite] is ill-sorted: the branches are irrelevant, but
    their [ok] flags are still read. *)
Local Ltac ite_other E x y :=
  destruct (sort_of E x) as [sx|]; red_sort;
  [ destruct (sort_of E y) as [sy|]; red_sort | idtac ]; try wp_auto; finish.

(** [x] and [y] must have the same sort, whichever it is. *)
Local Ltac eq_sorts E x y :=
  destruct (sort_of E x) as [sx|], (sort_of E y) as [sy|]; red_sort;
  [ destruct (decide (sx = sy)) as [->|Hne]; red_sort;
    [ try wp_auto; try (wp_if_destruct; last done)
    | try wp_auto; try (wp_if_destruct; first neq_sort) ]
  | idtac .. ]; try wp_auto; finish.

(** * The recursive cases, one lemma each *)

Section cases.
Context (dq : dfrac) (lenv : loc) (Env : sort_env) (svs sps sks : slice.t).
Context (Hwf : sort_env_wf Env).
Context (lterm : loc).

Local Notation IH :=
  (▷ (∀ l o, sortOfEnv_spec dq lenv Env svs sps sks l o))%I.
Local Notation SPEC oty :=
  (sortOfEnv_spec dq lenv Env svs sps sks lterm oty).

Lemma step_TPlus (x1 x2 : term) : IH -∗ SPEC (Some (TPlus x1 x2)).
Proof.
  iIntros "#IH". open_node.
  iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
  cbn [term_code term_num term_idx_wf] in Hidx |- *. wp_auto.
  wp_apply ("IH" $! la (term_a (TPlus x1 x2)) with "[$Hstruct $Hvars $Hpats $Hpok $Hta]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  try wp_auto.
  wp_apply ("IH" $! lb (term_b (TPlus x1 x2)) with "[$Hstruct $Hvars $Hpats $Hpok $Htb]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  red_sort. bin_int Env x1 x2.
Qed.

Lemma step_TMinus (x1 x2 : term) : IH -∗ SPEC (Some (TMinus x1 x2)).
Proof.
  iIntros "#IH". open_node.
  iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
  cbn [term_code term_num term_idx_wf] in Hidx |- *. wp_auto.
  wp_apply ("IH" $! la (term_a (TMinus x1 x2)) with "[$Hstruct $Hvars $Hpats $Hpok $Hta]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  try wp_auto.
  wp_apply ("IH" $! lb (term_b (TMinus x1 x2)) with "[$Hstruct $Hvars $Hpats $Hpok $Htb]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  red_sort. bin_int Env x1 x2.
Qed.

Lemma step_TMul (x1 x2 : term) : IH -∗ SPEC (Some (TMul x1 x2)).
Proof.
  iIntros "#IH". open_node.
  iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
  cbn [term_code term_num term_idx_wf] in Hidx |- *. wp_auto.
  wp_apply ("IH" $! la (term_a (TMul x1 x2)) with "[$Hstruct $Hvars $Hpats $Hpok $Hta]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  try wp_auto.
  wp_apply ("IH" $! lb (term_b (TMul x1 x2)) with "[$Hstruct $Hvars $Hpats $Hpok $Htb]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  red_sort. bin_int Env x1 x2.
Qed.

Lemma step_TLt (sg : bool) (x1 x2 : term) : IH -∗ SPEC (Some (TLt sg x1 x2)).
Proof.
  (* [sg] only changes the kind code, so [open_node] -- whose trailing
     [wp_auto] walks the whole function body -- is done once, before the
     split, rather than once per sign. [term_a]/[term_b] do not mention
     [sg] at all, so the two recursive calls are shared too. *)
  iIntros "#IH". open_node.
  iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
  cbn [term_code term_num term_idx_wf term_a term_b term_c] in Hidx |- *.
  destruct sg; wp_auto;
    wp_apply ("IH" $! la (Some x1) with "[$Hstruct $Hvars $Hpats $Hpok $Hta]")
      as "(Hstruct & Hvars & Hpats & Hpok)";
    try wp_auto;
    wp_apply ("IH" $! lb (Some x2) with "[$Hstruct $Hvars $Hpats $Hpok $Htb]")
      as "(Hstruct & Hvars & Hpats & Hpok)";
    red_sort; bin_int Env x1 x2.
Qed.

Lemma step_TLe (sg : bool) (x1 x2 : term) : IH -∗ SPEC (Some (TLe sg x1 x2)).
Proof.
  (* [sg] only changes the kind code, so [open_node] -- whose trailing
     [wp_auto] walks the whole function body -- is done once, before the
     split, rather than once per sign. [term_a]/[term_b] do not mention
     [sg] at all, so the two recursive calls are shared too. *)
  iIntros "#IH". open_node.
  iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
  cbn [term_code term_num term_idx_wf term_a term_b term_c] in Hidx |- *.
  destruct sg; wp_auto;
    wp_apply ("IH" $! la (Some x1) with "[$Hstruct $Hvars $Hpats $Hpok $Hta]")
      as "(Hstruct & Hvars & Hpats & Hpok)";
    try wp_auto;
    wp_apply ("IH" $! lb (Some x2) with "[$Hstruct $Hvars $Hpats $Hpok $Htb]")
      as "(Hstruct & Hvars & Hpats & Hpok)";
    red_sort; bin_int Env x1 x2.
Qed.

Lemma step_TEq (x1 x2 : term) : IH -∗ SPEC (Some (TEq x1 x2)).
Proof.
  iIntros "#IH". open_node.
  iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
  cbn [term_code term_num term_idx_wf] in Hidx |- *. wp_auto.
  wp_apply ("IH" $! la (term_a (TEq x1 x2)) with "[$Hstruct $Hvars $Hpats $Hpok $Hta]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  try wp_auto.
  wp_apply ("IH" $! lb (term_b (TEq x1 x2)) with "[$Hstruct $Hvars $Hpats $Hpok $Htb]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  red_sort. eq_sorts Env x1 x2.
Qed.

Lemma step_TNeg (x1 : term) : IH -∗ SPEC (Some (TNeg x1)).
Proof.
  iIntros "#IH". open_node.
  iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
  cbn [term_code term_num term_idx_wf] in Hidx |- *. wp_auto.
  wp_apply ("IH" $! la (term_a (TNeg x1)) with "[$Hstruct $Hvars $Hpats $Hpok $Hta]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  red_sort. un_sort Env x1.
Qed.

Lemma step_TNot (x1 : term) : IH -∗ SPEC (Some (TNot x1)).
Proof.
  iIntros "#IH". open_node.
  iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
  cbn [term_code term_num term_idx_wf] in Hidx |- *. wp_auto.
  wp_apply ("IH" $! la (term_a (TNot x1)) with "[$Hstruct $Hvars $Hpats $Hpok $Hta]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  red_sort. un_sort Env x1.
Qed.

Lemma step_TIte (x1 x2 x3 : term) : IH -∗ SPEC (Some (TIte x1 x2 x3)).
Proof.
  iIntros "#IH". open_node.
  iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
  cbn [term_code term_num term_idx_wf] in Hidx |- *. wp_auto.
  wp_apply ("IH" $! la (term_a (TIte x1 x2 x3)) with "[$Hstruct $Hvars $Hpats $Hpok $Hta]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  try wp_auto.
  wp_apply ("IH" $! lb (term_b (TIte x1 x2 x3)) with "[$Hstruct $Hvars $Hpats $Hpok $Htb]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  try wp_auto.
  wp_apply ("IH" $! lc (term_c (TIte x1 x2 x3)) with "[$Hstruct $Hvars $Hpats $Hpok $Htc]")
    as "(Hstruct & Hvars & Hpats & Hpok)".
  red_sort.
  destruct (sort_of Env x1) as [[]|]; red_sort;
    [ ite_other Env x2 x3
    | eq_sorts Env x2 x3
    | ite_other Env x2 x3
    | ite_other Env x2 x3
    | try wp_auto; finish ].
Qed.

End cases.

(** * The dispatch *)

Lemma sortOfEnv_spec_holds (dq : dfrac) (lenv : loc) (Env : sort_env)
    (svs sps sks : slice.t) :
  sort_env_wf Env →
  ⊢ ∀ (lterm : loc) (oty : option term), sortOfEnv_spec dq lenv Env svs sps sks lterm oty.
Proof.
  intros Hwf.
  iLöb as "IH". iIntros (lterm oty).
  destruct oty as [ty|]; last first.
  { (* the term is nil *)
    rewrite /sortOfEnv_spec /env_pts.
    wp_start as "((Hstruct & Hvars & Hpats & Hpok) & #Hot)".
    iDestruct "Hot" as %->.
    wp_auto. try (wp_if_destruct; last done). try wp_auto.
    red_sort. finish. }
  destruct ty as [k|k| |w|bb| | |x1 x2|x1 x2|x1 x2|x1|x1 x2|sg x1 x2|sg x1 x2|x1|x1 x2 x3| |x1].
  - (* TVar *)
    open_node.
    iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
    cbn [term_code term_num term_idx_wf] in Hidx |- *.
    iDestruct (own_slice_len with "Hvars") as %[Hlv Hlv2].
    rewrite length_fmap in Hlv. rewrite /idx_wf in Hidx.
    try wp_auto.
    wp_if_destruct.
    + (* the index is out of range *)
      assert (se_vars Env !! k = None) as Hlook by (apply lookup_ge_None_2; word).
      red_sort. rewrite Hlook. red_sort. finish.
    + (* the index is in range *)
      assert (is_Some (se_vars Env !! k)) as [srt Hlook]
        by (apply lookup_lt_is_Some_2; word).
      red_sort. rewrite Hlook. red_sort.
      rewrite decide_True; last word.
      wp_apply (wp_load_slice_index with "[$Hvars]") as "Hvars".
      { word. }
      { iPureIntro. rewrite list_lookup_fmap.
        replace (Z.to_nat (sint.Z (W64 k))) with k by word. by rewrite Hlook. }
      try wp_auto. finish.
  - (* TPat *)
    open_node.
    iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
    cbn [term_code term_num term_idx_wf] in Hidx |- *.
    iDestruct (own_slice_len with "Hpats") as %[Hlp Hlp2].
    iDestruct (own_slice_len with "Hpok") as %[Hlk Hlk2].
    rewrite length_fmap in Hlp.
    rewrite /idx_wf in Hidx. rewrite /sort_env_wf in Hwf.
    try wp_auto.
    wp_if_destruct.
    + (* the index is out of range *)
      assert (se_pats Env !! k = None) as Hlook by (apply lookup_ge_None_2; word).
      red_sort. rewrite Hlook. red_sort. finish.
    + (* the index is in range; [sort_env_wf] makes [patOk] in range too *)
      assert (is_Some (se_pats Env !! k)) as [srt Hlook]
        by (apply lookup_lt_is_Some_2; word).
      assert (is_Some (se_pat_ok Env !! k)) as [bk Hok]
        by (apply lookup_lt_is_Some_2; word).
      red_sort. rewrite Hlook Hok.
      rewrite decide_True; last word.
      wp_apply (wp_load_slice_index with "[$Hpok]") as "Hpok".
      { word. }
      { iPureIntro. replace (Z.to_nat (sint.Z (W64 k))) with k by word. done. }
      destruct bk; red_sort.
      * (* the pattern variable is declared *)
        try wp_auto.
        rewrite decide_True; last word.
        wp_apply (wp_load_slice_index with "[$Hpats]") as "Hpats".
        { word. }
        { iPureIntro. rewrite list_lookup_fmap.
          replace (Z.to_nat (sint.Z (W64 k))) with k by word. by rewrite Hlook. }
        try wp_auto. finish.
      * (* no binder declared it *)
        try wp_auto. finish.
  - (* TResult *)
    open_node.
    iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
    cbn [term_code term_num term_idx_wf] in Hidx |- *.
    red_sort. destruct (se_ret_ok Env); red_sort; try wp_auto; finish.
  - (* TInt *)
    open_node.
    iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
    cbn [term_code term_num term_idx_wf] in Hidx |- *.
    try wp_auto. red_sort. finish.
  - (* TBool *)
    open_node.
    iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
    cbn [term_code term_num term_idx_wf] in Hidx |- *.
    try wp_auto. red_sort. finish.
  - (* TUnit *)
    open_node.
    iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
    cbn [term_code term_num term_idx_wf] in Hidx |- *.
    try wp_auto. red_sort. finish.
  - (* TNull *)
    open_node.
    iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
    cbn [term_code term_num term_idx_wf] in Hidx |- *.
    try wp_auto. red_sort. rewrite /checker.SortLoc. finish.
  - by iApply (step_TPlus with "IH").
  - by iApply (step_TMinus with "IH").
  - by iApply (step_TMul with "IH").
  - by iApply (step_TNeg with "IH").
  - by iApply (step_TEq with "IH").
  - by iApply (step_TLt with "IH").
  - by iApply (step_TLe with "IH").
  - by iApply (step_TNot with "IH").
  - by iApply (step_TIte with "IH").
  - (* TExec *)
    open_node.
    iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
    cbn [term_code term_num term_idx_wf] in Hidx |- *.
    try wp_auto. red_sort. finish.
  - (* TRet *)
    open_node.
    iDestruct (is_term_node with "Hot") as (la lb lc) "(%Hidx & #Hnode & #Hta & #Htb & #Htc)".
    cbn [term_code term_num term_idx_wf] in Hidx |- *.
    try wp_auto. red_sort. finish.
Qed.

(** * The public specifications *)

(** The unpacked form, with the [sortEnv] struct and its three slices written
    out: what [SortOf] needs, since it builds the struct itself. *)
Lemma wp_sortOfEnv_pts (dq : dfrac) (lenv : loc) (Env : sort_env)
    (svs sps sks : slice.t) (lterm : loc) (oty : option term) :
  sort_env_wf Env →
  {{{ is_pkg_init checker ∗
      lenv ↦{dq} checker.sortEnv.mk svs sps sks
                   (sort_code (se_ret Env)) (se_ret_ok Env) ∗
      svs ↦*{dq} (sort_code <$> se_vars Env) ∗
      sps ↦*{dq} (sort_code <$> se_pats Env) ∗
      sks ↦*{dq} se_pat_ok Env ∗
      is_oterm lterm oty }}}
    @! checker.sortOfEnv #lenv #lterm
  {{{ RET (#(osort_code (osort_of Env oty)), #(osort_ok (osort_of Env oty)));
      lenv ↦{dq} checker.sortEnv.mk svs sps sks
                   (sort_code (se_ret Env)) (se_ret_ok Env) ∗
      svs ↦*{dq} (sort_code <$> se_vars Env) ∗
      sps ↦*{dq} (sort_code <$> se_pats Env) ∗
      sks ↦*{dq} se_pat_ok Env }}}.
Proof.
  intros Hwf. iIntros (Φ) "(#Hinit & Hstruct & Hvars & Hpats & Hpok & #Hot) HΦ".
  iPoseProof (sortOfEnv_spec_holds dq lenv Env svs sps sks Hwf) as "#Hspec".
  rewrite /sortOfEnv_spec /env_pts.
  wp_apply ("Hspec" $! lterm oty with "[$Hstruct $Hvars $Hpats $Hpok $Hot]").
  iIntros "(Hstruct & Hvars & Hpats & Hpok)". iApply "HΦ". iFrame.
Qed.

(** The packaged form: [is_sortenv] hides the three slices. *)
Lemma wp_sortOfEnv (dq : dfrac) (lenv lterm : loc) (Env : sort_env) (oty : option term) :
  sort_env_wf Env →
  {{{ is_pkg_init checker ∗ is_sortenv dq lenv Env ∗ is_oterm lterm oty }}}
    @! checker.sortOfEnv #lenv #lterm
  {{{ RET (#(osort_code (osort_of Env oty)), #(osort_ok (osort_of Env oty)));
      is_sortenv dq lenv Env }}}.
Proof.
  intros Hwf. iIntros (Φ) "(#Hinit & Henv & #Hot) HΦ".
  iDestruct "Henv" as (svs sps sks) "(Hstruct & Hvars & Hpats & Hpok)".
  wp_apply (wp_sortOfEnv_pts dq lenv Env svs sps sks lterm oty Hwf
              with "[$Hstruct $Hvars $Hpats $Hpok $Hot]").
  iIntros "(Hstruct & Hvars & Hpats & Hpok)". iApply "HΦ".
  rewrite /is_sortenv. iFrame.
Qed.

(** The form a caller usually wants: the boolean decides whether the term has
    a sort at all, and the code is then that sort's. *)
Corollary wp_sortOfEnv' (dq : dfrac) (lenv lterm : loc) (Env : sort_env)
    (oty : option term) :
  {{{ is_pkg_init checker ∗ is_sortenv dq lenv Env ∗ is_oterm lterm oty ∗
      ⌜sort_env_wf Env⌝ }}}
    @! checker.sortOfEnv #lenv #lterm
  {{{ (scode : w64) (ok : bool), RET (#scode, #ok);
      is_sortenv dq lenv Env ∗
      ⌜ok = true ↔ ∃ ty s, oty = Some ty ∧ sort_of Env ty = Some s⌝ ∗
      ⌜∀ ty s, oty = Some ty → sort_of Env ty = Some s → scode = sort_code s⌝ }}}.
Proof.
  iIntros (Φ) "(#Hinit & Henv & #Hot & %Hwf) HΦ".
  wp_apply (wp_sortOfEnv dq lenv lterm Env oty Hwf with "[$Henv $Hot]").
  iIntros "Henv". iApply ("HΦ" $! _ _). iFrame "Henv". iPureIntro.
  destruct oty as [ty|]; simpl.
  - destruct (sort_of Env ty) as [s|] eqn:Hs; simpl; split.
    + split; [naive_solver|done].
    + intros ty' s' [= ->] Hs'. rewrite Hs' in Hs. by simplify_eq.
    + naive_solver.
    + intros ty' s' [= ->] Hs'. by rewrite Hs' in Hs.
  - split; [naive_solver|]. by intros ty' s' ?.
Qed.

End proof.
