/-
Port of `new/checker/interp.v`.

Interpretation of the checker's *internal* data.

`State` and `Path` (checker/state.go) never appear in the soundness
statement, but every exec-level specification has to say what a symbolic
state means, so they get mirrors here together with their interpretation as
an Iris assertion.

Lean notes:
* The mirrors and their pure predicates need only `[FfiSyntax]`; only
  `heap_interp`/`paths_post` live in the ghost-state section.
* Rocq's wands `P -∗ Q` between closed assertions are entailments `P ⊢ Q`.
* `[∗ list]` over the empty list is `emp`, which is `True` in the affine
  `IProp GF` (`heap_interp_nil` states it with `True`, as in Rocq).
-/
import Checkers.Checker.TermLemmas

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode

/-- Mirrors `checker.Cell`: a location term and the value term stored there. -/
structure scell where
  mkCell ::
  cloc : term
  cval : term
deriving DecidableEq, Repr

export scell (mkCell cloc cval)

/-- Mirrors `checker.State`. -/
structure sstate where
  mkState ::
  sheap : List scell
  spc : List term
  svars : List sort
deriving DecidableEq, Repr

export sstate (mkState sheap spc svars)

/-- Mirrors `checker.Path`. -/
structure spath where
  mkPath ::
  pret : term
  pst : sstate
deriving DecidableEq, Repr

export spath (mkPath pret pst)

instance scell_inhabited : Inhabited scell := ⟨mkCell TUnit TUnit⟩
instance sstate_inhabited : Inhabited sstate := ⟨mkState [] [] []⟩
instance spath_inhabited : Inhabited spath := ⟨mkPath TUnit default⟩

section pure
variable [ext : FfiSyntax]

/-- The pure side: the valuation respects the state's sort table and makes
every recorded path condition true. -/
def st_sat (V : valuation) (st : sstate) : Prop :=
  (∀ n s, (svars st)[n]? = some s → has_sort (vvar V n) s) ∧ pc_sat V (spc st)

/-- Every term in a state mentions only the logical variables the state
declares, so extending the valuation beyond `length (svars st)` is
harmless. -/
def heap_below (k : Nat) (H : List scell) : Prop :=
  ∀ c, c ∈ H → vars_below k (cloc c) ∧ vars_below k (cval c)

structure wf_state (st : sstate) : Prop where
  mkWfState ::
  wf_heap : heap_below (svars st).length (sheap st)
  wf_pc : pc_below (svars st).length (spc st)

theorem heap_below_mono (k k' : Nat) (H : List scell) :
    k ≤ k' → heap_below k H → heap_below k' H := by
  intro Hle Hb c Hc
  obtain ⟨h1, h2⟩ := Hb c Hc
  exact ⟨vars_below_mono _ _ _ Hle h1, vars_below_mono _ _ _ Hle h2⟩

theorem pc_below_mono (k k' : Nat) (pc : List term) :
    k ≤ k' → pc_below k pc → pc_below k' pc := by
  intro Hle Hb t Ht
  exact vars_below_mono _ _ _ Hle (Hb t Ht)

theorem st_sat_agree (k : Nat) (V V' : valuation) (st : sstate) :
    agree_below k V V' → (svars st).length ≤ k → wf_state st →
    st_sat V st → st_sat V' st := by
  intro Hag Hlen Hwf ⟨Hv, Hpc⟩
  refine ⟨?_, ?_⟩
  · intro n s Hn
    have : n < k := by
      have := (List.getElem?_eq_some_iff.mp Hn).1
      omega
    rw [← Hag.1 n this]
    exact Hv n s Hn
  · exact pc_sat_agree k V V' _ Hag (pc_below_mono _ _ _ Hlen Hwf.wf_pc) Hpc

/-- Well-formedness of a result list: each path's state is well-formed and has
at least the caller's logical variables, and its return term is scoped by
that state. -/
structure paths_wf (k : Nat) (ps : List spath) : Prop where
  mkPathsWf ::
  paths_wf_state : ∀ p, p ∈ ps → wf_state (pst p)
  paths_wf_grow : ∀ p, p ∈ ps → k ≤ (svars (pst p)).length
  paths_wf_ret : ∀ p, p ∈ ps → vars_below (svars (pst p)).length (pret p)

theorem paths_wf_nil (k : Nat) : paths_wf k [] where
  paths_wf_state _ H := nomatch H
  paths_wf_grow _ H := nomatch H
  paths_wf_ret _ H := nomatch H

theorem paths_wf_app (k : Nat) (ps ps' : List spath) :
    paths_wf k ps → paths_wf k ps' → paths_wf k (ps ++ ps') := by
  intro ⟨A1, B1, C1⟩ ⟨A2, B2, C2⟩
  refine ⟨?_, ?_, ?_⟩ <;> intro p Hp <;> rcases List.mem_append.mp Hp with H | H
  · exact A1 p H
  · exact A2 p H
  · exact B1 p H
  · exact B2 p H
  · exact C1 p H
  · exact C2 p H

theorem paths_wf_mono (k k' : Nat) (ps : List spath) :
    k' ≤ k → paths_wf k ps → paths_wf k' ps := by
  intro Hle ⟨H1, H2, H3⟩
  exact ⟨H1, fun p Hp => Nat.le_trans Hle (H2 p Hp), H3⟩

/-! ## Environments -/

/-- Every term an environment binds is scoped by the current variables. -/
def env_below (k : Nat) (ρ : List (GoString × term)) : Prop :=
  ∀ xt, xt ∈ ρ → vars_below k xt.2

theorem env_below_mono (k k' : Nat) (ρ : List (GoString × term)) :
    k ≤ k' → env_below k ρ → env_below k' ρ := by
  intro Hle Hb xt Hxt
  exact vars_below_mono _ _ _ Hle (Hb xt Hxt)

theorem env_below_cons (k : Nat) (x : GoString) (t : term) (ρ : List (GoString × term)) :
    vars_below k t → env_below k ρ → env_below k ((x, t) :: ρ) := by
  intro Ht Hb xt Hxt
  rcases List.mem_cons.mp Hxt with rfl | H
  · exact Ht
  · exact Hb xt H

end pure

section interp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The meaning of a symbolic state -/

/-- The separating conjunction of the cells the state owns. -/
def heap_interp (V : valuation) (H : List scell) : IProp GF :=
  iprop([∗list] c ∈ H, ∃ lo : Loc,
      ⌜teval V (cloc c) = lval lo⌝ ∗ heapPointsto lo (DFrac.own 1) (teval V (cval c)))

theorem heap_interp_nil (V : valuation) : heap_interp (GF := GF) V [] ⊣⊢ iprop(True) := by
  unfold heap_interp
  exact ⟨true_intro, BigSepL.bigSepL_nil_intro⟩

theorem heap_interp_cons (V : valuation) (c : scell) (H : List scell) :
    heap_interp (GF := GF) V (c :: H) ⊣⊢
    iprop((∃ lo : Loc, ⌜teval V (cloc c) = lval lo⌝ ∗
        heapPointsto lo (DFrac.own 1) (teval V (cval c)))
      ∗ heap_interp V H) := by
  unfold heap_interp
  exact BigSepL.bigSepL_cons

theorem heap_interp_app (V : valuation) (H1 H2 : List scell) :
    heap_interp (GF := GF) V (H1 ++ H2) ⊣⊢ iprop(heap_interp V H1 ∗ heap_interp V H2) := by
  unfold heap_interp
  exact BigSepL.bigSepL_append

/-- Agreeing valuations give the same interpretation of a well-scoped heap. -/
theorem heap_interp_agree (k : Nat) (V V' : valuation) (H : List scell) :
    agree_below k V V' → heap_below k H →
    heap_interp (GF := GF) V H ⊣⊢ heap_interp V' H := by
  intro Hag Hb
  apply BiEntails.of_eq
  unfold heap_interp
  apply BigSepL.bigSepL_eq
  intro i c Hc
  have Hin : c ∈ H := List.mem_of_getElem? Hc
  obtain ⟨Hl, Hv⟩ := Hb c Hin
  rw [teval_agree k V V' (cloc c) Hag Hl, teval_agree k V V' (cval c) Hag Hv]

/-! ## Path lists

A path list is a *disjunction*: the program ends in some one of them. This
is the postcondition every exec-level specification produces. `k` is the
number of logical variables the caller had, which the callee may only
extend. -/
def paths_post (k : Nat) (V : valuation) (ps : List spath) : val → IProp GF :=
  fun v => iprop(∃ (p : spath) (V' : valuation),
      ⌜p ∈ ps⌝ ∗ ⌜agree_below k V V'⌝ ∗
      ⌜v = teval V' (pret p)⌝ ∗ ⌜st_sat V' (pst p)⌝ ∗
      heap_interp V' (sheap (pst p)))

theorem paths_post_mono (k : Nat) (V : valuation) (ps ps' : List spath) (v : val) :
    ps ⊆ ps' → paths_post (GF := GF) k V ps v ⊢ paths_post k V ps' v := by
  intro Hsub
  unfold paths_post
  iintro ⟨%p, %V', %Hin, %Hag, %Hv, %Hst, H⟩
  iexists p, V'
  iframe H
  ipureintro
  exact ⟨Hsub Hin, Hag, Hv, Hst⟩

theorem paths_post_app_l (k : Nat) (V : valuation) (ps ps' : List spath) (v : val) :
    paths_post (GF := GF) k V ps v ⊢ paths_post k V (ps ++ ps') v :=
  paths_post_mono k V _ _ v (fun _ h => List.mem_append_left _ h)

theorem paths_post_app_r (k : Nat) (V : valuation) (ps ps' : List spath) (v : val) :
    paths_post (GF := GF) k V ps' v ⊢ paths_post k V (ps ++ ps') v :=
  paths_post_mono k V _ _ v (fun _ h => List.mem_append_right _ h)

end interp

end Checker
end Perennial
