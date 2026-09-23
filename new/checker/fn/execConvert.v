(** [checker.execConvert] (checker/exec.go): a conversion is accepted only
    between a supported type ([TypeSort]) and itself ([TypeEq]), where it is
    the identity; the result is then that of the operand, by a tail call to
    [exec].

    Note on naming: no Rocq variable here may be called [e], [en], [st] or
    [tok], because those are the names of the Go function's own locals and
    [wp_auto] derives Rocq identifiers from them; the specification is
    therefore proved over [ce] and restated at the end. *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_b exec_sound_a.
From New.checker.fn Require Import TypeSort TypeEq.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_execConvert_aux (ty1 ty2 : ctype) (ce : cexpr) :
  (⊢ exec_like checker.exec ce) → ⊢ exec_like checker.execConvert (CEConvert ty1 ty2 ce).
Proof.
  intros Hex1.
  iPoseProof Hex1 as "#Hex1".
  iIntros (le lρ lst ρ sst).
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)".
  iDestruct "He" as (lt1 lt2 la) "(#Hnode & #Ht1 & #Ht2 & #Ha)".
  fold is_expr.
  wp_auto.
  wp_apply (wp_TypeSort lt1 (Some ty1) with "[$Ht1]").
  try wp_auto.
  wp_apply (wp_TypeEq (Some ty1) lt1 lt2 (Some ty2) with "[$Ht1 $Ht2]").
  destruct (decide (ty1 = ty2)) as [<-|Hne].
  2:{ rewrite bool_decide_eq_false_2; last congruence.
      wp_auto.
      wp_alloc lfail as "Hlf".
      iDestruct (typed_pointsto_not_null with "Hlf") as %Hnn.
      wp_auto.
      iApply "HΦ". by iApply exec_post_fail. }
  rewrite bool_decide_eq_true_2; last done.
  wp_auto.
  wp_apply ("Hex1" $! la lρ lst ρ sst with "[Hst]").
  { iFrame "∗#". iPureIntro. done. }
  iIntros (s lf) "Hpost".
  wp_auto.
  iApply "HΦ". rewrite /exec_post.
  destruct (decide (lf = null)); last done.
  iDestruct "Hpost" as (ps0) "(Hps & %Hwf0 & %Hsnd0)".
  iExists ps0. iFrame "Hps". iPureIntro. split; first done.
  by apply exec_sound_convert.
Qed.

Lemma wp_execConvert t1 t2 e : (⊢ exec_like checker.exec e) → ⊢ exec_like checker.execConvert (CEConvert t1 t2 e).
Proof. apply wp_execConvert_aux. Qed.

End proof.
