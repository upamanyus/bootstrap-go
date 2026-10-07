/-
Port of `new/checker/fn/storeAll.v`.

`checker.storeAll` (checker/exec.go): the store of an `EStore` at location
term `l`, performed on each path the stored value reached.

For each path `q`, the state is cloned, `heapUpdate` replaces the cell at
`l` with `q.Ret` (failing if there is none), and the new path returns
`TUnit` in the updated state.

Lean notes:
* Rocq's `Forall2` is Batteries' `List.Forall₂`; `forall2_snoc` is a helper in
  `ExecSoundB.lean`.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecSoundC
import Checkers.Checker.Fn.State__clone
import Checkers.Checker.Fn.heapUpdate

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

section pure
variable [ext : FfiSyntax]

/-- The path `storeAll` produces from a path `qv` of the stored value. -/
def store_path (x : term) (qv : spath) : Option spath :=
  (heap_update (sheap (pst qv)) x (pret qv)).map (fun H' => mkPath TUnit (st_heap (pst qv) H'))

def store_rel (x : term) (qvs outs : List spath) : Prop :=
  List.Forall₂ (fun qv o => store_path x qv = some o) qvs outs

theorem store_path_some (x : term) (qv o : spath) :
    store_path x qv = some o →
    ∃ H', heap_update (sheap (pst qv)) x (pret qv) = some H' ∧ o = mkPath TUnit (st_heap (pst qv) H') := by
  unfold store_path
  cases heap_update (sheap (pst qv)) x (pret qv) with
  | none => intro h; cases h
  | some H' => intro h; cases h; exact ⟨H', rfl, rfl⟩

theorem store_rel_ok (x : term) (qvs outs : List spath) :
    store_rel x qvs outs → store_ok x qvs outs := by
  intro Hrel
  induction Hrel with
  | nil => intro q Hq; cases Hq
  | cons Hso _ ih =>
    intro q Hq
    rcases List.mem_cons.mp Hq with rfl | Hq
    · obtain ⟨H', Hup, rfl⟩ := store_path_some _ _ _ Hso
      exact ⟨H', Hup, List.mem_cons_self ..⟩
    · obtain ⟨H', Hup, Hin⟩ := ih q Hq
      exact ⟨H', Hup, List.mem_cons_of_mem _ Hin⟩

theorem store_rel_wf (k : Nat) (x : term) (qvs outs : List spath) :
    paths_wf k qvs → store_rel x qvs outs → paths_wf k outs := by
  intro Hwf Hrel
  have Hsrc : ∀ o, o ∈ outs → ∃ qv H', qv ∈ qvs ∧
      heap_update (sheap (pst qv)) x (pret qv) = some H' ∧
      o = mkPath TUnit (st_heap (pst qv) H') := by
    clear Hwf
    induction Hrel with
    | nil => intro o Ho; cases Ho
    | cons Hso _ ih =>
      intro o Ho
      rcases List.mem_cons.mp Ho with rfl | Ho
      · obtain ⟨H', Hup, rfl⟩ := store_path_some _ _ _ Hso
        exact ⟨_, H', List.mem_cons_self .., Hup, rfl⟩
      · obtain ⟨qv, H', Hq, Hup, rfl⟩ := ih o Ho
        exact ⟨qv, H', List.mem_cons_of_mem _ Hq, Hup, rfl⟩
  refine ⟨?_, ?_, ?_⟩ <;> intro o Hin <;> obtain ⟨qv, H', Hq, Hup, rfl⟩ := Hsrc o Hin
  · exact wf_state_heap _ _ _ _ (Hwf.paths_wf_state qv Hq) (Hwf.paths_wf_ret qv Hq) Hup
  · exact Hwf.paths_wf_grow qv Hq
  · trivial

end pure

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

theorem wp_storeAll (le lx : Loc) (sq : GoSlice) (x : term) (qvs : List spath) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_term lx x ∗ is_paths sq qvs }}
      (App (App (App (Val (@! checker.storeAll)) (Val #le)) (Val #lx)) (Val #sq))
    {{ (s : GoSlice) (lf : Loc), RET (PairV #s #lf);
        if lf = null then
          iprop(∃ outs, is_paths s outs ∗ ⌜store_rel x qvs outs⌝)
        else iprop(True) }} := by
  wp_start as ⟨#Hx, Hqs⟩
  unfold is_paths
  icases Hqs with ⟨%xs, Hxs, Hxp⟩
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hxp
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  wp_auto
  ihave Hnil := ownSlice_nil (GF := GF) (V := checker.Path) (DFrac.own 1)
  ihave Hnilcap := ownSliceCap_nil (GF := GF) (V := checker.Path)
  rw [show (zero_val GoSlice) = slice.nil from rfl]
  ihave HI : (∃ (k : w64) (pcur : checker.Path) (so : GoSlice) (os : List checker.Path)
      (outs : List spath),
      "i" ∷ i_ptr ↦ k ∗ "q" ∷ q_ptr ↦ pcur ∗ "out" ∷ out_ptr ↦ so ∗
      "Hos" ∷ so ↦* os ∗ "Hcap" ∷ ownSliceCap checker.Path so (DFrac.own 1) ∗
      "Hosp" ∷ ([∗list] y;o ∈ os;outs, is_path y o) ∗
      "Hrest" ∷ ([∗list] y;o ∈ xs.drop (sint.nat k);qvs.drop (sint.nat k), is_path y o) ∗
      "%Hrel" ∷ ⌜store_rel x (qvs.take (sint.nat k)) outs⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ xs.length⌝ : IProp GF) $$ [i q out Hxp Hnil Hnilcap]
  · iexists W64 0, _, slice.nil, [], []
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero, List.drop_zero]
    iframe i q out Hxp Hnil Hnilcap
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro
    exact ⟨.nil, by word⟩
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left ⟨Hk.1, Hif⟩]
    list_elem xs (sint.nat k) as x0
    list_elem qvs (sint.nat k) as q0
    rw [drop_cons_of_getElem? _ _ _ Hx0_lookup, drop_cons_of_getElem? _ _ _ Hq0_lookup]
    icases (BigSepL2.bigSepL2_cons (Φ := fun _ y o => is_path (GF := GF) y o)).1 $$ Hrest
      with ⟨Hp0, Hrest⟩
    rw [show is_path x0 q0 = iprop(is_term (GF := GF) x0.Ret' (pret q0) ∗ is_state x0.St' (pst q0))
      from rfl]
    icases Hp0 with ⟨#Hret, Hst0⟩
    wp_apply wp_load_slice_index sq (sint.Z k) xs _ x0 Hk.1 $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hx0_lookup
    wp_apply wp_State__clone $$ [Hst0] as %lst2 ⟨-, Hfr⟩
    · iframe Hst0
    unfold is_state_fresh
    icases Hfr with ⟨%hs, %cs, %vs, Hl, Hh, Hhcap, Hc, Hccap, Hv, Hvcap⟩
    wp_auto
    wp_apply wp_heapUpdate hs (sheap (pst q0)) lx x0.Ret' x (pret q0) $$ [Hh]
      as %hs' %okb ⟨-, %Hok, Hnew⟩
    · iframe Hh #
    cases okb with
    | false =>
      -- no cell at `l`
      wp_auto
      wp_alloc lfail as Hf
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hf
      wp_auto
      wp_for_post
      iapply HΦ
      rw [ite_eq_right Hnn]
      itrivial
    | true =>
      simp only [ite_true]
      icases Hnew with ⟨%H', %Hup, Hh'⟩
      wp_auto
      ipersist «$v0»
      imod ownSlice_persist _ _ _ $$ Hv with #Hv
      ihave Hst2 : is_state (GF := GF) lst2 (st_heap (pst q0) H') $$ [Hl Hh' Hc]
      · unfold is_state is_vars
        simp only [st_heap]
        iexists hs', cs, vs
        iframe Hh' Hc Hv
        iexact Hl
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl3 ⟨Hsl3, _⟩
      wp_auto
      wp_apply wp_slice_append (t := checker.Path.ty) so os _ [checker.Path.mk «$v0_ptr» lst2]
        (DFrac.own 1) $$ [Hos Hcap Hsl3] as %so' ⟨Hos, Hcap, -⟩
      · iframe Hos Hcap Hsl3
      wp_for_post
      iframe HΦ Hxs l e
      iexists k + W64 1, x0, so', os ++ [checker.Path.mk «$v0_ptr» lst2],
        outs ++ [mkPath TUnit (st_heap (pst q0) H')]
      have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      rw [Hk1]
      iframe i q out Hos Hcap Hrest
      isplitl [Hosp Hst2]
      · iapply BigSepL2.bigSepL2_snoc.2
        iframe Hosp
        rw [show is_path (checker.Path.mk «$v0_ptr» lst2) (mkPath TUnit (st_heap (pst q0) H')) =
          iprop(is_term (GF := GF) «$v0_ptr» TUnit ∗ is_state lst2 (st_heap (pst q0) H')) from rfl]
        iframe Hst2
        simp only [is_term, tnode]
        iExactEq «$v0»; rfl
      ipureintro
      refine ⟨?_, by word⟩
      rw [List.take_add_one, Hq0_lookup]
      simp only [Option.toList]
      exact forall2_snoc _ _ _ _ _ Hrel (by simp [store_path, Hup])
  · -- the loop is over
    have Htake : qvs.take (sint.nat k) = qvs := List.take_of_length_le (by word)
    rw [Htake] at Hrel
    iapply HΦ
    rw [ite_eq_left rfl]
    iexists outs
    isplitl
    · iexists os; iframe Hos Hosp
    · ipureintro; exact Hrel

end proof

end Checker
end Perennial
