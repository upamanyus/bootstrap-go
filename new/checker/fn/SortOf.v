(** [checker.SortOf] (checker/sorts.go): the sort of a term over a list of
    logical-variable sorts.

    Note on naming: no Rocq variable here may be called [vars], [t] or [e] --
    those are the Go function's own locals and [wp_auto] derives Rocq
    identifiers from them. *)
From New.checker Require Import prelude nodes.
From New.checker.fn Require Import sortOfEnv.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

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
