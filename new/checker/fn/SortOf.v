(** [checker.SortOf] (checker/sorts.go): the sort of a term over a list of
    logical-variable sorts.

    Note on naming: no Rocq variable here may be called [vars], [t] or [e] --
    those are the Go function's own locals and [wp_auto] derives Rocq
    identifiers from them. *)
From New.checker Require Import prelude nodes.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The result of [sortOfEnv]/[SortOf] as an [option sort]: [None] is the
    Go pair [(SortInt, false)], and [SortInt]'s code is [W64 0]. Copies of
    the definitions in new/checker/fn/sortOfEnv__nobuild.v, for as long as
    that file is parked. *)
Definition osort_of (E : sort_env) (ot : option term) : option sort :=
  match ot with None => None | Some ty => sort_of E ty end.
Definition osort_code (os : option sort) : w64 :=
  match os with Some s => sort_code s | None => W64 0 end.
Definition osort_ok (os : option sort) : bool :=
  match os with Some _ => true | None => false end.

(** The specification of [checker.sortOfEnv], assumed.

    [new/checker/fn/sortOfEnv__nobuild.v] proves it (as [sortOfEnv_spec_holds],
    over the [env_pts] bundle) but is parked: see that file's header. This is
    the same statement with [env_pts] written out, which is the form the
    proof below uses. Discharging it is a `Require` and one `iApply` once
    that file compiles.

    The same hypothesis, in the [is_sortenv] packaging, appears in
    fn/atomWellSorted.v, and fn/applyBinOp.v and fn/applyUnOp.v assume
    [wp_SortOf] below for the same reason; all four go away together. *)
Context (wp_sortOfEnv_pts :
  ∀ (dq : dfrac) (lenv : loc) (Env : sort_env)
    (svs sps sks : slice.t) (lterm : loc) (oty : option term),
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
      sks ↦*{dq} se_pat_ok Env }}}).

(** [SortOf] builds a [sortEnv] with only [vars] populated, which is exactly
    [vars_env]: no pattern variables, and no [ret]. *)
Lemma wp_SortOf (sv : slice.t) (lterm : loc) (vl : list sort) (oty : option term) :
  {{{ is_pkg_init checker ∗ sv ↦*□ (sort_code <$> vl) ∗ is_oterm lterm oty }}}
    @! checker.SortOf #sv #lterm
  {{{ RET (#(osort_code (osort_of (vars_env vl) oty)),
           #(osort_ok (osort_of (vars_env vl) oty)));
      True }}}.
Proof.
  wp_start as "[#Hsl #Hot]".
  wp_auto.
  wp_alloc lenv as "Hlenv".
  wp_auto.
  iPersist "Hlenv".
  wp_apply (wp_sortOfEnv_pts DfracDiscarded lenv (vars_env vl)
              sv slice.nil slice.nil lterm oty (vars_env_wf vl)
              with "[$Hlenv $Hsl $Hot]").
  { iSplitL; iApply own_slice_nil. }
  iIntros "_". try wp_auto. by iApply "HΦ".
Qed.

End proof.
