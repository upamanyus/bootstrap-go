(** [checker.typeSigned] (checker/sorts.go): is this integer type signed?

    Note on naming: no Rocq variable here may be called [t], the name of the
    Go function's own local, because [wp_auto] derives Rocq identifiers from
    the Go names. *)
From New.checker Require Import prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The Go function dereferences [t.Kind] with no nil check; that is safe
    exactly because [is_type] owns a real node ([is_type_not_null]). *)
Lemma wp_typeSigned (lt : loc) (t : ctype) :
  {{{ is_pkg_init checker ∗ is_type lt t }}}
    @! checker.typeSigned #lt
  {{{ RET #(ctype_signed t); True }}}.
Proof.
  wp_start as "#Ht".
  iDestruct (is_type_node with "Ht") as (le) "[#Hnode _]".
  destruct t; simpl; wp_auto; by iApply "HΦ".
Qed.

End proof.
