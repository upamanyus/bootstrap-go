(** [checker.onePath] (checker/exec.go): the singleton path list.

    Note on naming: no Rocq variable here may be called [v], [st] or [out],
    because those are the names of the Go function's own locals and [wp_auto]
    derives Rocq identifiers from them. *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The Go code appends a one-element slice literal to a nil slice, so the
    proof supplies the nil slice's (empty) contents and capacity itself; the
    caller gets back only [is_paths], the capacity of the result being of no
    use to the callers of [onePath]. *)
Lemma wp_onePath (lv lst : loc) (tv : term) (sst : sstate) :
  {{{ is_pkg_init checker ∗ is_term lv tv ∗ is_state lst sst }}}
    @! checker.onePath #lv #lst
  {{{ (s : slice.t), RET #s; is_paths s [mkPath tv sst] }}}.
Proof.
  wp_start as "(#Hv & Hst)".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sl [Hsl Hcap]".
  wp_auto.
  (* the literal's single element is written at index 0 *)
  replace (Z.to_nat (w64_word_instance.(word.signed) (W64 0))) with 0%nat by word.
  iSimpl in "Hsl".
  iDestruct (own_slice_nil (V:=checker.Path.t) (DfracOwn 1)) as "Hnil".
  iDestruct (own_slice_cap_nil (V:=checker.Path.t)) as "Hnilcap".
  (* the destination slice has to be pinned down explicitly: left to
     unification, [iFrame] uses the nil points-to for the source as well. *)
  wp_apply (wp_slice_append (t:=checker.Path) _ [] _ [checker.Path.mk lv lst] (DfracOwn 1)
             with "[$Hnil $Hnilcap $Hsl]").
  iIntros (s') "(Hs' & _ & _)".
  wp_auto.
  iApply "HΦ". iExists [checker.Path.mk lv lst].
  rewrite app_nil_l. iFrame "Hs'". simpl. by iFrame "Hv Hst".
  Unshelve. all: apply _.
Qed.

End proof.
