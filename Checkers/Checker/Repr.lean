/-
Port of `new/checker/repr.v`.

Representation predicates.

`is_type`, `is_term`, `is_expr`, `is_assn`, `is_func` and `is_sorts`
(Defs.lean) describe the checker's *input* in the Go heap; this file gives
their persistence instances and the corresponding predicates for the
checker's *internal* data (environments, cells, states, paths), which do
not appear in the soundness statement.

Lean notes:
* Rocq's `checker.Cell.t`, `checker.State.t`, ... are the Goose structs
  `checker.Cell`, `checker.State`, ...; `slice.t` is `GoSlice`;
  `own_slice_cap` is `ownSliceCap`.
* The node-decoding lemmas (`is_type_node`, `is_term_node`) are entailments
  `⊢` (Rocq: wands `-∗` between closed assertions); use them with
  `icases is_term_node _ _ $$ H with ⟨%la, %lb, %lc, %Hwf, #Hn, #Ha, #Hb, #Hc⟩`
  (or `ihave` to keep `H`).
* `is_otype_some`/`is_oterm_some` (`rfl`) turn `is_otype l (some t)` into
  `is_type l t` without unfolding the `is_otype` of a Löb hypothesis, which
  a `simp only [is_otype]` would also do.
* The pure mirror functions (`type_code`, `term_code`, `ctype_elem`, ...)
  need no section variables; they are stated before the ghost-state section.
-/
import Checkers.Checker.Interp

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode
open github_com.upamanyus.bootstrap_go

/-! ## Node codes (pure) -/

def type_code : ctype → w64
  | CTyInt => W64 1 | CTyInt64 => W64 2 | CTyUint64 => W64 3
  | CTyBool => W64 4 | CTyPtr _ => W64 5

def ctype_elem : ctype → Option ctype
  | CTyPtr e => some e
  | _ => none

/-- A type is determined by its kind code and its element type -- which is
what makes `TypeEq`'s two comparisons complete. -/
theorem ctype_eq_iff (ta tb : ctype) :
    ta = tb ↔ type_code ta = type_code tb ∧ ctype_elem ta = ctype_elem tb := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨Hc, He⟩
    cases ta <;> cases tb <;> simp_all [type_code, ctype_elem] <;> revert Hc <;> decide

def term_code : term → w64
  | TVar _ => W64 1 | TPat _ => W64 2 | TResult => W64 3 | TInt _ => W64 4
  | TBool _ => W64 5 | TUnit => W64 6 | TNull => W64 7
  | TPlus _ _ => W64 8 | TMinus _ _ => W64 9 | TMul _ _ => W64 10
  | TNeg _ => W64 11 | TEq _ _ => W64 12
  | TLt sg _ _ => if sg then W64 13 else W64 14
  | TLe sg _ _ => if sg then W64 15 else W64 16
  | TNot _ => W64 17 | TIte _ _ _ => W64 18 | TExec => W64 19 | TRet _ => W64 20

def term_num : term → w64
  | TVar n | TPat n => W64 n
  | TInt w => w
  | TBool b => bool_code b
  | _ => W64 0

def term_a : term → Option term
  | TPlus x _ | TMinus x _ | TMul x _ | TEq x _ | TLt _ x _ | TLe _ x _
  | TNeg x | TNot x | TRet x | TIte x _ _ => some x
  | _ => none

def term_b : term → Option term
  | TPlus _ y | TMinus _ y | TMul _ y | TEq _ y | TLt _ _ y | TLe _ _ y
  | TIte _ y _ => some y
  | _ => none

def term_c : term → Option term
  | TIte _ _ z => some z
  | _ => none

/-- The side condition that makes the `Num` field pin down the index. -/
def term_idx_wf : term → Prop
  | TVar n | TPat n => idx_wf n
  | _ => True

/-- Index equality at the `Num` field. -/
theorem W64_nat_inj (n m : Nat) : idx_wf n → idx_wf m → W64 n = W64 m → n = m := by
  unfold idx_wf
  intro Hn Hm Heq
  rw [← Hn, ← Hm, Heq]

section repr
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## Persistence

The checker never mutates a `Type`, `Term`, `Expr` or `Assn` node after
construction (see the immutability invariant in checker/doc.go), which is
what lets these be described with discarded fractions. -/

instance is_type_persistent (l : Loc) (t : ctype) : Persistent (is_type (GF := GF) l t) := by
  induction t generalizing l with
  | CTyPtr e ih => unfold is_type; infer_instance
  | _ => unfold is_type; infer_instance

instance is_term_persistent (l : Loc) (t : term) : Persistent (is_term (GF := GF) l t) := by
  induction t generalizing l <;> unfold is_term <;> infer_instance

instance is_expr_persistent (l : Loc) (e : cexpr) : Persistent (is_expr (GF := GF) l e) := by
  induction e generalizing l <;> unfold is_expr <;> infer_instance

instance is_assn_persistent (l : Loc) (a : cassn) : Persistent (is_assn (GF := GF) l a) := by
  induction a generalizing l <;> unfold is_assn <;> infer_instance

instance is_func_persistent (l : Loc) (f : cfunc) : Persistent (is_func (GF := GF) l f) := by
  unfold is_func; infer_instance

instance is_sorts_persistent (s : GoSlice) (vars : List sort) :
    Persistent (is_sorts (GF := GF) s vars) := by
  unfold is_sorts; infer_instance

/-! ## Non-nullness

A represented node is a real allocation, so the nil checks the Go code
performs first always take the non-nil branch. -/

theorem is_type_not_null (l : Loc) (t : ctype) : is_type (GF := GF) l t ⊢ ⌜l ≠ null⌝ := by
  cases t <;> simp only [is_type]
  all_goals first
    | (iintro ⟨%_, H, _⟩; iapply typedPointsto_not_null $$ H)
    | (iintro H; iapply typedPointsto_not_null $$ H)

theorem is_term_not_null (l : Loc) (t : term) : is_term (GF := GF) l t ⊢ ⌜l ≠ null⌝ := by
  cases t <;> simp only [is_term]
  all_goals first
    | (iintro ⟨%_, %_, %_, H, _⟩; iapply typedPointsto_not_null $$ H)
    | (iintro ⟨%_, %_, H, _⟩; iapply typedPointsto_not_null $$ H)
    | (iintro ⟨%_, H, _⟩; iapply typedPointsto_not_null $$ H)
    | (iintro ⟨%_, H⟩; iapply typedPointsto_not_null $$ H)
    | (iintro H; iapply typedPointsto_not_null $$ H)

theorem is_expr_not_null (l : Loc) (e : cexpr) : is_expr (GF := GF) l e ⊢ ⌜l ≠ null⌝ := by
  cases e <;> simp only [is_expr]
  all_goals first
    | (iintro ⟨%_, %_, %_, H, _⟩; iapply typedPointsto_not_null $$ H)
    | (iintro ⟨%_, %_, H, _⟩; iapply typedPointsto_not_null $$ H)
    | (iintro ⟨%_, H, _⟩; iapply typedPointsto_not_null $$ H)
    | (iintro H; iapply typedPointsto_not_null $$ H)

theorem is_assn_not_null (l : Loc) (a : cassn) : is_assn (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  cases a <;> simp only [is_assn]
  all_goals first
    | (iintro ⟨%_, %_, H, _⟩; iapply typedPointsto_not_null $$ H)
    | (iintro ⟨%_, %_, H, _⟩; iapply typedPointsto_not_null $$ H)
    | (iintro ⟨%_, H, _⟩; iapply typedPointsto_not_null $$ H)
    | (iintro H; iapply typedPointsto_not_null $$ H)

/-! ## Decoding a node

The Go code switches on a node's kind field, so each proof needs the node
in a uniform shape: the kind code, and the children. -/

/-- A `Type` node's `Elem` field is `null` at every type but a pointer. -/
def is_otype (l : Loc) : Option ctype → IProp GF
  | none => iprop(⌜l = null⌝)
  | some t' => is_type l t'

theorem is_otype_some (l : Loc) (t : ctype) : is_otype (GF := GF) l (some t) = is_type l t := rfl
theorem is_otype_none (l : Loc) : is_otype (GF := GF) l none = iprop(⌜l = null⌝) := rfl

instance is_otype_persistent (l : Loc) (t : Option ctype) :
    Persistent (is_otype (GF := GF) l t) := by
  cases t <;> unfold is_otype <;> infer_instance

theorem is_otype_null (l : Loc) (t : Option ctype) :
    is_otype (GF := GF) l t ⊢ ⌜l = null ↔ t = none⌝ := by
  cases t with
  | none => simp only [is_otype]; iintro %H; ipureintro; simp [H]
  | some t' =>
    simp only [is_otype]
    iintro H
    ihave %Hn := is_type_not_null _ _ $$ H
    ipureintro; simp [Hn]

theorem is_type_node (l : Loc) (t : ctype) :
    is_type (GF := GF) l t ⊢ ∃ le : Loc,
      l ↦□ checker.Type'.mk (type_code t) le ∗ is_otype le (ctype_elem t) := by
  cases t <;> simp only [is_type, type_code, ctype_elem, is_otype]
  all_goals first
    | (iintro ⟨%le, #H, #He⟩; iexists le; iframe H He)
    | (iintro #H; iexists null; iframe H; ipureintro; rfl)

/-- A `Term` node's `A`/`B`/`C` fields are `null` where the constructor has
no child there. -/
def is_oterm (l : Loc) : Option term → IProp GF
  | none => iprop(⌜l = null⌝)
  | some t' => is_term l t'

theorem is_oterm_some (l : Loc) (t : term) : is_oterm (GF := GF) l (some t) = is_term l t := rfl
theorem is_oterm_none (l : Loc) : is_oterm (GF := GF) l none = iprop(⌜l = null⌝) := rfl

instance is_oterm_persistent (l : Loc) (t : Option term) :
    Persistent (is_oterm (GF := GF) l t) := by
  cases t <;> unfold is_oterm <;> infer_instance

theorem is_oterm_null (l : Loc) (t : Option term) :
    is_oterm (GF := GF) l t ⊢ ⌜l = null ↔ t = none⌝ := by
  cases t with
  | none => simp only [is_oterm]; iintro %H; ipureintro; simp [H]
  | some t' =>
    simp only [is_oterm]
    iintro H
    ihave %Hn := is_term_not_null _ _ $$ H
    ipureintro; simp [Hn]

theorem is_term_node (l : Loc) (t : term) :
    is_term (GF := GF) l t ⊢ ∃ la lb lc : Loc,
      ⌜term_idx_wf t⌝ ∗
      l ↦□ tnode (term_code t) (term_num t) la lb lc ∗
      is_oterm la (term_a t) ∗ is_oterm lb (term_b t) ∗ is_oterm lc (term_c t) := by
  cases t <;> simp only [is_term, term_idx_wf, term_code, term_num, term_a, term_b, term_c,
    is_oterm]
  all_goals first
    | (iintro ⟨%x, %y, %z, #H, #H1, #H2, #H3⟩; iexists x, y, z; iframe H H1 H2 H3)
    | (iintro ⟨%x, %y, #H, #H1, #H2⟩; iexists x, y, null; iframe H H1 H2; ipureintro; trivial)
    | (iintro ⟨%x, #H, #H1⟩; iexists x, null, null; iframe H H1; ipureintro; trivial)
    | (iintro ⟨%Hw, #H⟩; iexists null, null, null; iframe H; ipureintro; trivial)
    | (iintro #H; iexists null, null, null; iframe H; ipureintro; trivial)

/-! ## The checker's internal data -/

def is_cell (c : checker.Cell) (sc : scell) : IProp GF :=
  iprop(is_term c.Loc' (cloc sc) ∗ is_term c.Val' (cval sc))

instance is_cell_persistent (c : checker.Cell) (sc : scell) :
    Persistent (is_cell (GF := GF) c sc) := by
  unfold is_cell; infer_instance

/-- A symbolic heap: a slice of `Cell` structs, one per owned cell. The slice
is mutable (a state is cloned before it is changed), the terms in it are
not. -/
def is_heap (s : GoSlice) (H : List scell) : IProp GF :=
  iprop(∃ cs : List checker.Cell, s ↦* cs ∗ [∗list] c;sc ∈ cs;H, is_cell c sc)

def is_cond (s : GoSlice) (pc : List term) : IProp GF :=
  iprop(∃ ls : List Loc, s ↦* ls ∗ [∗list] l;t ∈ ls;pc, is_term l t)

/-- A state's sort table is written only while the state is fresh (the one
`append` in `EAlloc`, on a clone), so it is read-only as part of a state:
`SortOf`, `applyBinOp` and `applyUnOp` all need it persistent. -/
def is_vars (s : GoSlice) (vars : List sort) : IProp GF :=
  iprop(s ↦*□ (vars.map sort_code))

instance is_vars_persistent (s : GoSlice) (vars : List sort) :
    Persistent (is_vars (GF := GF) s vars) := by
  unfold is_vars; infer_instance

def is_state (l : Loc) (st : sstate) : IProp GF :=
  iprop(∃ hs cs vs : GoSlice,
      l ↦ checker.State.mk hs cs vs ∗
      is_heap hs (sheap st) ∗ is_cond cs (spc st) ∗ is_vars vs (svars st))

/-- A state straight out of `clone`, before it is changed and published: all
three slices owned together with their capacities, which is what the
`append`s of `EIf` and `EAlloc` consume. -/
def is_state_fresh (l : Loc) (st : sstate) : IProp GF :=
  iprop(∃ hs cs vs : GoSlice,
      l ↦ checker.State.mk hs cs vs ∗
      is_heap hs (sheap st) ∗ ownSliceCap checker.Cell hs (DFrac.own 1) ∗
      is_cond cs (spc st) ∗ ownSliceCap Loc cs (DFrac.own 1) ∗
      vs ↦* ((svars st).map sort_code) ∗ ownSliceCap w64 vs (DFrac.own 1))

theorem is_state_fresh_publish (l : Loc) (st : sstate) :
    is_state_fresh (GF := GF) l st ⊢ |==> is_state l st := by
  unfold is_state_fresh is_state is_vars
  iintro ⟨%hs, %cs, %vs, Hl, Hh, -, Hc, -, Hv, -⟩
  imod ownSlice_persist _ _ _ $$ Hv with #Hv
  imodintro
  iexists hs, cs, vs
  iframe Hl Hh Hc Hv

def is_path (p : checker.Path) (sp : spath) : IProp GF :=
  iprop(is_term p.Ret' (pret sp) ∗ is_state p.St' (pst sp))

def is_paths (s : GoSlice) (ps : List spath) : IProp GF :=
  iprop(∃ xs : List checker.Path, s ↦* xs ∗ [∗list] x;p ∈ xs;ps, is_path x p)

/-- The variable environment of checker/exec.go: a linked list, most recent
binding first, never mutated. -/
def is_env (l : Loc) : List (GoString × term) → IProp GF
  | [] => iprop(⌜l = null⌝)
  | xt :: ρ' =>
      iprop(∃ lt ln, l ↦□ checker.env.mk xt.1 lt ln ∗ is_term lt xt.2 ∗ is_env ln ρ')

instance is_env_persistent (l : Loc) (ρ : List (GoString × term)) :
    Persistent (is_env (GF := GF) l ρ) := by
  induction ρ generalizing l <;> unfold is_env <;> infer_instance

end repr

end Checker
end Perennial
