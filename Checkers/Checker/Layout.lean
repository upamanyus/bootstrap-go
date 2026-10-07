/-
Port of `new/checker/layout.v`.

The checker's input laid out in a concrete heap.

`check_adequate` (adequacy.v) starts `checker.Check` in a state whose heap
contains the input trees. Its precondition is a plain proposition about
that heap, `inputs_in`: for every struct node that the input's
representation predicate (`is_func`, `is_sorts`, `is_assn`, ..., Defs.lean)
asserts, each field's cell (`structFieldRef`) holds the field's value,
and for every slice, each element's cell (`arrayIndexRef`) holds the
element. The predicates here mirror those of Defs.lean one for one, with
`l ↦□ v` replaced by `node_in h l v`, `∗` by `∧` and `⌜P⌝` by `P`.

The cells must be non-null and unlocked (`Free`): a cell that starts out
locked is not a points-to fact a program can begin with.

`inputs_in_sound` turns the proposition back into the representation
predicates, from `heap_ro`, a persistent read-only view of the initial
heap that `heap_ro_init` builds from the cells adequacy hands out.

Lean notes:
* `heap_t` is `GMap Loc (NonAtomic val)`, the type of `state.heap`.
* `heap_ro_init` is stated, as in Rocq, on the big separating conjunction
  of `naHeapPointstoSt (tls lkv.1) l (.own 1) lkv.2` in an arbitrary
  `HeapGS hlc GF`; `heap_ro_init_cells` is the same fact for
  `heapCells h` (`Checkers/GooseLang/HeapAdequacy.lean`), which is what
  `goose_adequacy_heap` hands the program (it fixes `hlc = .hasLC`).
* The proof of `heap_ro_init` is an induction over the map (`GMap.map_ind`)
  instead of `big_sepM_bupd` + `big_sepM_impl` (Lean's Iris has no
  `bigSepM_bupd`).
* `Forall P l` is `∀ c ∈ l, P c`.
-/
import Checkers.Checker.Prelude
import Checkers.GooseLang.HeapAdequacy

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode
open github_com.upamanyus.bootstrap_go

/-- The heap of a GooseLang state. -/
abbrev heap_t [FfiSyntax] := GMap Loc (NonAtomic val)

section layout
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [sem_fn : GoSemanticsFunctions]

/-- Cell `l` of `h` holds `v`, unlocked. -/
def heap_cell (h : heap_t) (l : Loc) (v : val) : Prop :=
  l ≠ null ∧ h !! l = some (Free v)

/-- The cells a struct node occupies: one per field, holding the field. -/
class NodeCells (V : Type) where
  node_cells : Loc → V → List (Loc × val)

export NodeCells (node_cells)

instance Type'_cells : NodeCells checker.Type' where
  node_cells l v :=
    [(l.[checker.Type', go!"Kind"], #v.Kind'), (l.[checker.Type', go!"Elem"], #v.Elem')]

instance Term_cells : NodeCells checker.Term where
  node_cells l v :=
    [(l.[checker.Term, go!"Kind"], #v.Kind'),
     (l.[checker.Term, go!"Num"], #v.Num'),
     (l.[checker.Term, go!"A"], #v.A'),
     (l.[checker.Term, go!"B"], #v.B'),
     (l.[checker.Term, go!"C"], #v.C')]

instance Expr_cells : NodeCells checker.Expr where
  node_cells l v :=
    [(l.[checker.Expr, go!"Kind"], #v.Kind'),
     (l.[checker.Expr, go!"Name"], #v.Name'),
     (l.[checker.Expr, go!"Num"], #v.Num'),
     (l.[checker.Expr, go!"Op"], #v.Op'),
     (l.[checker.Expr, go!"Ty"], #v.Ty'),
     (l.[checker.Expr, go!"Ty2"], #v.Ty2'),
     (l.[checker.Expr, go!"A"], #v.A'),
     (l.[checker.Expr, go!"B"], #v.B'),
     (l.[checker.Expr, go!"C"], #v.C')]

instance Assn_cells : NodeCells checker.Assn where
  node_cells l v :=
    [(l.[checker.Assn, go!"Kind"], #v.Kind'),
     (l.[checker.Assn, go!"L"], #v.L'),
     (l.[checker.Assn, go!"R"], #v.R'),
     (l.[checker.Assn, go!"X"], #v.X'),
     (l.[checker.Assn, go!"Y"], #v.Y'),
     (l.[checker.Assn, go!"Var"], #v.Var'),
     (l.[checker.Assn, go!"Sort"], #v.Sort')]

instance Func_cells : NodeCells checker.Func where
  node_cells l v :=
    [(l.[checker.Func, go!"Params"], #v.Params'), (l.[checker.Func, go!"Body"], #v.Body')]

/-- A struct node `v` at `l`. -/
def node_in {V : Type} [NodeCells V] (h : heap_t) (l : Loc) (v : V) : Prop :=
  l ≠ null ∧ ∀ c ∈ node_cells l v, heap_cell h c.1 c.2

/-- A slice `s` with elements `xs`: nil, or a backing array whose element
cells hold `xs`. -/
def slice_in {V : Type} (h : heap_t) (s : GoSlice) (xs : List V) : Prop :=
  (s = slice.nil ∧ xs = []) ∨
  ((xs.length : Int) = sint.Z s.len ∧
   sint.Z s.len ≤ sint.Z s.cap ∧
   s.ptr ≠ null ∧
   ∀ (i : Nat) x, xs[i]? = some x →
     heap_cell h (arrayIndexRef V (i : Int) s.ptr) #x)

def type_in (h : heap_t) (l : Loc) : ctype → Prop
  | CTyInt => node_in h l (checker.Type'.mk (W64 1) null)
  | CTyInt64 => node_in h l (checker.Type'.mk (W64 2) null)
  | CTyUint64 => node_in h l (checker.Type'.mk (W64 3) null)
  | CTyBool => node_in h l (checker.Type'.mk (W64 4) null)
  | CTyPtr e => ∃ le, node_in h l (checker.Type'.mk (W64 5) le) ∧ type_in h le e

def term_in (h : heap_t) (l : Loc) : term → Prop
  | TVar n => idx_wf n ∧ node_in h l (tnode (W64 1) (W64 n) null null null)
  | TPat n => idx_wf n ∧ node_in h l (tnode (W64 2) (W64 n) null null null)
  | TResult => node_in h l (tnode (W64 3) (W64 0) null null null)
  | TInt w => node_in h l (tnode (W64 4) w null null null)
  | TBool b => node_in h l (tnode (W64 5) (bool_code b) null null null)
  | TUnit => node_in h l (tnode (W64 6) (W64 0) null null null)
  | TNull => node_in h l (tnode (W64 7) (W64 0) null null null)
  | TPlus a b =>
      ∃ la lb, node_in h l (tnode (W64 8) (W64 0) la lb null) ∧ term_in h la a ∧ term_in h lb b
  | TMinus a b =>
      ∃ la lb, node_in h l (tnode (W64 9) (W64 0) la lb null) ∧ term_in h la a ∧ term_in h lb b
  | TMul a b =>
      ∃ la lb, node_in h l (tnode (W64 10) (W64 0) la lb null) ∧ term_in h la a ∧ term_in h lb b
  | TNeg a => ∃ la, node_in h l (tnode (W64 11) (W64 0) la null null) ∧ term_in h la a
  | TEq a b =>
      ∃ la lb, node_in h l (tnode (W64 12) (W64 0) la lb null) ∧ term_in h la a ∧ term_in h lb b
  | TLt sg a b =>
      ∃ la lb, node_in h l (tnode (if sg then W64 13 else W64 14) (W64 0) la lb null) ∧
               term_in h la a ∧ term_in h lb b
  | TLe sg a b =>
      ∃ la lb, node_in h l (tnode (if sg then W64 15 else W64 16) (W64 0) la lb null) ∧
               term_in h la a ∧ term_in h lb b
  | TNot a => ∃ la, node_in h l (tnode (W64 17) (W64 0) la null null) ∧ term_in h la a
  | TIte c a b =>
      ∃ lc la lb, node_in h l (tnode (W64 18) (W64 0) lc la lb) ∧
                  term_in h lc c ∧ term_in h la a ∧ term_in h lb b
  | TExec => node_in h l (tnode (W64 19) (W64 0) null null null)
  | TRet a => ∃ la, node_in h l (tnode (W64 20) (W64 0) la null null) ∧ term_in h la a

def expr_in (h : heap_t) (l : Loc) : cexpr → Prop
  | CEInt w => node_in h l (enode (W64 1) go!"" w (W64 0) null null null null null)
  | CEBool b => node_in h l (enode (W64 2) go!"" (bool_code b) (W64 0) null null null null null)
  | CEUnit => node_in h l (enode0 (W64 3) null null null)
  | CEVar x => node_in h l (enode (W64 4) x (W64 0) (W64 0) null null null null null)
  | CELet x e1 e2 =>
      ∃ la lb, node_in h l (enode (W64 5) x (W64 0) (W64 0) null null la lb null) ∧
               expr_in h la e1 ∧ expr_in h lb e2
  | CESeq e1 e2 =>
      ∃ la lb, node_in h l (enode0 (W64 6) la lb null) ∧ expr_in h la e1 ∧ expr_in h lb e2
  | CEIf c e1 e2 =>
      ∃ lc la lb, node_in h l (enode0 (W64 7) lc la lb) ∧
                  expr_in h lc c ∧ expr_in h la e1 ∧ expr_in h lb e2
  | CELoad t e =>
      ∃ lt la, node_in h l (enode (W64 8) go!"" (W64 0) (W64 0) lt null la null null) ∧
               type_in h lt t ∧ expr_in h la e
  | CEStore t e1 e2 =>
      ∃ lt la lb, node_in h l (enode (W64 9) go!"" (W64 0) (W64 0) lt null la lb null) ∧
                  type_in h lt t ∧ expr_in h la e1 ∧ expr_in h lb e2
  | CEAlloc t e =>
      ∃ lt la, node_in h l (enode (W64 10) go!"" (W64 0) (W64 0) lt null la null null) ∧
               type_in h lt t ∧ expr_in h la e
  | CEZero t =>
      ∃ lt, node_in h l (enode (W64 11) go!"" (W64 0) (W64 0) lt null null null null) ∧
            type_in h lt t
  | CEBinOp op t e1 e2 =>
      ∃ lt la lb, node_in h l (enode (W64 12) go!"" (W64 0) (op_code op) lt null la lb null) ∧
                  type_in h lt t ∧ expr_in h la e1 ∧ expr_in h lb e2
  | CEUnOp op t e =>
      ∃ lt la, node_in h l (enode (W64 13) go!"" (W64 0) (op_code op) lt null la null null) ∧
               type_in h lt t ∧ expr_in h la e
  | CEConvert t1 t2 e =>
      ∃ lt1 lt2 la, node_in h l (enode (W64 14) go!"" (W64 0) (W64 0) lt1 lt2 la null null) ∧
                    type_in h lt1 t1 ∧ type_in h lt2 t2 ∧ expr_in h la e
  | CEDo e => ∃ la, node_in h l (enode0 (W64 15) la null null) ∧ expr_in h la e
  | CEReturn e => ∃ la, node_in h l (enode0 (W64 16) la null null) ∧ expr_in h la e
  | CEExcSeq e1 e2 =>
      ∃ la lb, node_in h l (enode0 (W64 17) la lb null) ∧ expr_in h la e1 ∧ expr_in h lb e2
  | CEExcDo e => ∃ la, node_in h l (enode0 (W64 18) la null null) ∧ expr_in h la e

def assn_in (h : heap_t) (l : Loc) : cassn → Prop
  | CAEmp => node_in h l (anode (W64 1) null null null null (W64 0) (W64 0))
  | CASep p q =>
      ∃ lp lq, node_in h l (anode (W64 2) lp lq null null (W64 0) (W64 0)) ∧
               assn_in h lp p ∧ assn_in h lq q
  | CAOr p q =>
      ∃ lp lq, node_in h l (anode (W64 3) lp lq null null (W64 0) (W64 0)) ∧
               assn_in h lp p ∧ assn_in h lq q
  | CAExists n s p =>
      ∃ lp, idx_wf n ∧ node_in h l (anode (W64 4) lp null null null (W64 n) (sort_code s)) ∧
            assn_in h lp p
  | CAPure t =>
      ∃ lx, node_in h l (anode (W64 5) null null lx null (W64 0) (W64 0)) ∧ term_in h lx t
  | CAPointsTo x y =>
      ∃ lx ly, node_in h l (anode (W64 6) null null lx ly (W64 0) (W64 0)) ∧
               term_in h lx x ∧ term_in h ly y

def func_in (h : heap_t) (l : Loc) (f : cfunc) : Prop :=
  ∃ (s : GoSlice) (lb : Loc),
    node_in h l (checker.Func.mk s lb) ∧ slice_in h s f.fparams ∧ expr_in h lb f.fbody

def sorts_in (h : heap_t) (s : GoSlice) (vars : List sort) : Prop :=
  slice_in h s (vars.map sort_code)

/-- The whole input of `checker.Check #lf #svars #lpre #lpost`. -/
def inputs_in (h : heap_t) (lf : Loc) (f : cfunc) (svars : GoSlice) (vars : List sort)
    (lpre : Loc) (pre : cassn) (lpost : Loc) (post : cassn) : Prop :=
  func_in h lf f ∧ sorts_in h svars vars ∧ assn_in h lpre pre ∧ assn_in h lpost post

end layout

section layout_sound
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Every unlocked, non-null cell of `h`, read-only. -/
def heap_ro (h : heap_t) : IProp GF :=
  iprop(□ ∀ l v, ⌜heap_cell h l v⌝ → heapPointsto l DFrac.discard v)

instance heap_ro_persistent (h : heap_t) : Persistent (heap_ro (GF := GF) h) := by
  unfold heap_ro; infer_instance

instance heap_ro_intuitionistic (h : heap_t) : Intuitionistic (heap_ro (GF := GF) h) := by
  unfold heap_ro; infer_instance

/-- From the cells of the initial heap, as adequacy hands them out
(`goose_adequacy_heap`). -/
theorem heap_ro_init (h : heap_t) :
    ([∗map] l ↦ lkv ∈ h, naHeapPointstoSt (tls lkv.1) l (.own 1) lkv.2) ⊢@{IProp GF}
      |==> heap_ro h := by
  induction h using GMap.map_ind with
  | h0 =>
    iintro _
    imodintro
    unfold heap_ro
    iintro !> %l %v %Hc
    exact absurd Hc.2 (by simp)
  | hins l lkv σ Hl IH =>
    iintro Hh
    icases (BigSepM.bigSepM_insert Hl).1 $$ Hh with ⟨Hc, Hh⟩
    imod IH $$ Hh with #Hro
    -- the new cell, read-only if it is an unlocked non-null cell
    ihave Hnew : iprop(|==> □ (⌜lkv.1 = Reading 0⌝ → ⌜l ≠ null⌝ →
        heapPointsto l DFrac.discard lkv.2)) $$ [Hc]
    · by_cases Hok : lkv.1 = Reading 0 ∧ l ≠ null
      · obtain ⟨Hm, Hnn⟩ := Hok
        rw [Hm, tls_Reading]
        imod heapPointsto_persist l (.own 1) lkv.2 $$ [Hc] with #Hp
        · unfold heapPointsto naHeapPointsto
          iframe Hc
          ipureintro; exact Hnn
        imodintro
        iintro !> _ _
        iexact Hp
      · imodintro
        iintro !> %Hm %Hnn
        exact absurd ⟨Hm, Hnn⟩ Hok
    imod Hnew with #Hnew
    imodintro
    unfold heap_ro
    iintro !> %l' %v' %Hc'
    obtain ⟨Hnn', Hl'⟩ := Hc'
    by_cases Heq : l = l'
    · subst Heq
      rw [GMap.lookup_insert] at Hl'
      cases Hl'
      simp only [Free]
      iapply Hnew
      · ipureintro; trivial
      · ipureintro; exact Hnn'
    · rw [GMap.lookup_insert_ne _ _ Heq] at Hl'
      iapply Hro $$ %l' %v'
      ipureintro; exact ⟨Hnn', Hl'⟩

theorem cell_sound (h : heap_t) (c : Loc) (w : val) :
    heap_cell h c w → heap_ro (GF := GF) h ⊢ heapPointsto c DFrac.discard w ∗ ⌜c ≠ null⌝ := by
  intro ⟨Hnn, Hc⟩
  unfold heap_ro
  iintro #H
  isplitl
  · iapply H $$ %c %w; ipureintro; exact ⟨Hnn, Hc⟩
  · ipureintro; exact Hnn

/-- A cell holding a value of a type whose typed points-to is the heap
points-to (`w64`, `Loc`, `GoSlice`, `GoString`, ...). -/
theorem cell_sound_typed {V : Type} (hinj : Function.Injective (intoVal (V := V)))
    (h : heap_t) (c : Loc) (x : V) :
    heap_cell h c #x →
    heap_ro (GF := GF) h ⊢ @typedPointsto GF V (heapTypedPointsto V hinj) c x DFrac.discard := by
  intro Hc
  letI : TypedPointsto (GF := GF) V := heapTypedPointsto V hinj
  rw [typedPointsto_unseal_eq]
  exact cell_sound h c #x Hc

/-- A struct node, read from its cells. -/
class NodeSound (V : Type) [NodeCells V] [TypedPointsto (GF := GF) V] : Prop where
  node_sound : ∀ (h : heap_t) (l : Loc) (v : V), node_in h l v → heap_ro (GF := GF) h ⊢ l ↦□ v

/-- Each field's cell gives the field's points-to; the struct's typed
points-to is their conjunction. -/
local macro "node_tac" : tactic => `(tactic| (
  intro h l v ⟨Hnn, Hc⟩
  simp only [node_cells, List.forall_mem_cons] at Hc
  iintro #H
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef, named]
  repeat (
    obtain ⟨Hc1, Hc⟩ := Hc
    isplitr
    · iapply cell_sound_typed _ h _ _ Hc1 $$ H)
  itrivial))

instance Type'_sound : NodeSound (GF := GF) checker.Type' where
  node_sound := by node_tac
instance Term_sound : NodeSound (GF := GF) checker.Term where
  node_sound := by node_tac
instance Expr_sound : NodeSound (GF := GF) checker.Expr where
  node_sound := by node_tac
instance Assn_sound : NodeSound (GF := GF) checker.Assn where
  node_sound := by node_tac
instance Func_sound : NodeSound (GF := GF) checker.Func where
  node_sound := by node_tac

theorem slice_in_sound_w64 (h : heap_t) (s : GoSlice) (xs : List w64) :
    slice_in h s xs → heap_ro (GF := GF) h ⊢ s ↦*□ xs := by
  intro Hs
  rcases Hs with ⟨Hs, Hxs⟩ | ⟨Hlen, Hcap, Hnn, Hc⟩
  · subst Hs; subst Hxs
    iintro _; iapply ownSlice_nil
  · iintro #H
    rw [ownSlice_unseal]; unfold ownSliceDef
    iright
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      isplitr
      · ipureintro; exact Hlen
      · unfold arrayElems
        iapply (BigSepL.bigSepL_intro (P := heap_ro (GF := GF) h)
          fun k x Hk => cell_sound_typed _ h _ x (Hc k x Hk))
        iexact H
    · ipureintro; exact Hcap

theorem slice_in_sound_string (h : heap_t) (s : GoSlice) (xs : List GoString) :
    slice_in h s xs → heap_ro (GF := GF) h ⊢ s ↦*□ xs := by
  intro Hs
  rcases Hs with ⟨Hs, Hxs⟩ | ⟨Hlen, Hcap, Hnn, Hc⟩
  · subst Hs; subst Hxs
    iintro _; iapply ownSlice_nil
  · iintro #H
    rw [ownSlice_unseal]; unfold ownSliceDef
    iright
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      isplitr
      · ipureintro; exact Hlen
      · unfold arrayElems
        iapply (BigSepL.bigSepL_intro (P := heap_ro (GF := GF) h)
          fun k x Hk => cell_sound_typed _ h _ x (Hc k x Hk))
        iexact H
    · ipureintro; exact Hcap

set_option hygiene false in
/-- One leaf of a tree: a pure side condition, a node, or a subtree (by
`type_in_sound`, `term_in_sound` or an induction hypothesis `ih1`/`ih2`/`ih3`). -/
local macro "tree_leaf " Hx:ident : tactic => `(tactic| first
  | (ipureintro; exact $Hx)
  | (iapply NodeSound.node_sound _ _ _ $Hx $$ H)
  | (iapply ih1 _ $Hx $$ H)
  | (iapply ih2 _ $Hx $$ H)
  | (iapply ih3 _ $Hx $$ H)
  | (iapply type_in_sound _ _ _ $Hx $$ H)
  | (iapply term_in_sound _ _ _ $Hx $$ H))

set_option hygiene false in
/-- The trees: take the conjuncts of `Hin` apart in the order of the goal,
reading every node and subtree. -/
local macro "tree_tac" : tactic => `(tactic| (
  iintro #H
  repeat (first
    | (obtain ⟨xx, Hin⟩ := Hin; iexists xx)
    | (obtain ⟨Hx, Hin⟩ := Hin; isplit; · tree_leaf Hx))
  tree_leaf Hin))

theorem type_in_sound (h : heap_t) (l : Loc) (t : ctype) :
    type_in h l t → heap_ro (GF := GF) h ⊢ is_type l t := by
  induction t generalizing l with
  | CTyPtr e ih1 => intro Hin; simp only [type_in] at Hin; simp only [is_type]; tree_tac
  | _ => intro Hin; simp only [type_in] at Hin; simp only [is_type]; tree_tac

theorem term_in_sound (h : heap_t) (l : Loc) (t : term) :
    term_in h l t → heap_ro (GF := GF) h ⊢ is_term l t := by
  induction t generalizing l with
  | TPlus _ _ ih1 ih2 | TMinus _ _ ih1 ih2 | TMul _ _ ih1 ih2 | TEq _ _ ih1 ih2
  | TLt _ _ _ ih1 ih2 | TLe _ _ _ ih1 ih2 =>
    intro Hin; simp only [term_in] at Hin; simp only [is_term]; tree_tac
  | TNeg _ ih1 | TNot _ ih1 | TRet _ ih1 =>
    intro Hin; simp only [term_in] at Hin; simp only [is_term]; tree_tac
  | TIte _ _ _ ih1 ih2 ih3 =>
    intro Hin; simp only [term_in] at Hin; simp only [is_term]; tree_tac
  | _ => intro Hin; simp only [term_in] at Hin; simp only [is_term]; tree_tac

theorem expr_in_sound (h : heap_t) (l : Loc) (e : cexpr) :
    expr_in h l e → heap_ro (GF := GF) h ⊢ is_expr l e := by
  induction e generalizing l with
  | CELet _ _ _ ih1 ih2 | CESeq _ _ ih1 ih2 | CEStore _ _ _ ih1 ih2
  | CEBinOp _ _ _ _ ih1 ih2 | CEExcSeq _ _ ih1 ih2 =>
    intro Hin; simp only [expr_in] at Hin; simp only [is_expr]; tree_tac
  | CEIf _ _ _ ih1 ih2 ih3 =>
    intro Hin; simp only [expr_in] at Hin; simp only [is_expr]; tree_tac
  | CELoad _ _ ih1 | CEAlloc _ _ ih1 | CEUnOp _ _ _ ih1 | CEConvert _ _ _ ih1
  | CEDo _ ih1 | CEReturn _ ih1 | CEExcDo _ ih1 =>
    intro Hin; simp only [expr_in] at Hin; simp only [is_expr]; tree_tac
  | _ => intro Hin; simp only [expr_in] at Hin; simp only [is_expr]; tree_tac

theorem assn_in_sound (h : heap_t) (l : Loc) (a : cassn) :
    assn_in h l a → heap_ro (GF := GF) h ⊢ is_assn l a := by
  induction a generalizing l with
  | CASep _ _ ih1 ih2 | CAOr _ _ ih1 ih2 =>
    intro Hin; simp only [assn_in] at Hin; simp only [is_assn]; tree_tac
  | CAExists _ _ _ ih1 =>
    intro Hin; simp only [assn_in] at Hin; simp only [is_assn]; tree_tac
  | _ => intro Hin; simp only [assn_in] at Hin; simp only [is_assn]; tree_tac

theorem func_in_sound (h : heap_t) (l : Loc) (f : cfunc) :
    func_in h l f → heap_ro (GF := GF) h ⊢ is_func l f := by
  intro ⟨s, lb, Hn, Hs, He⟩
  unfold is_func
  iintro #H
  iexists s, lb
  isplit
  · iapply NodeSound.node_sound _ _ _ Hn $$ H
  isplit
  · iapply slice_in_sound_string _ _ _ Hs $$ H
  · iapply expr_in_sound _ _ _ He $$ H

theorem sorts_in_sound (h : heap_t) (s : GoSlice) (vars : List sort) :
    sorts_in h s vars → heap_ro (GF := GF) h ⊢ is_sorts s vars := by
  intro Hs
  unfold is_sorts
  exact slice_in_sound_w64 h s _ Hs

theorem inputs_in_sound (h : heap_t) (lf : Loc) (f : cfunc) (sv : GoSlice) (vars : List sort)
    (lpre : Loc) (pre : cassn) (lpost : Loc) (post : cassn) :
    inputs_in h lf f sv vars lpre pre lpost post →
    heap_ro (GF := GF) h ⊢
      is_func lf f ∗ is_sorts sv vars ∗ is_assn lpre pre ∗ is_assn lpost post := by
  intro ⟨Hf, Hs, Hpre, Hpost⟩
  iintro #H
  isplit
  · iapply func_in_sound _ _ _ Hf $$ H
  isplit
  · iapply sorts_in_sound _ _ _ Hs $$ H
  isplit
  · iapply assn_in_sound _ _ _ Hpre $$ H
  · iapply assn_in_sound _ _ _ Hpost $$ H

end layout_sound

section cells
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics]

/-- `heap_ro_init` for the cells `goose_adequacy_heap` hands the program. -/
theorem heap_ro_init_cells (h : heap_t) :
    heapCells h ⊢@{IProp GF} |==> heap_ro h :=
  heap_ro_init h

end cells

end Checker
end Perennial
