/- Port of `src/goose_lang/heap_adequacy.v`.

Adequacy of GooseLang for runs that do not crash, with the initial heap.

    [goose_adequacy_heap] turns a WP for [e] into facts about the executions
    of [e] from [σ] ([goose_adequate]): every value the main thread reduces
    to satisfies the postcondition, and no thread gets stuck. The WP may use
    every cell of the initial heap (in the lock state it starts in), and may
    assume that the Go local context of its ghost state is [σ]'s.

    The executions are those of [erased_step], which has no crash steps.
    (The proof goes through [goose_recv_adequacy_heap] with a restart program
    that is never run.)

Lean notes:
* Perennial's Lean port has no crash logic, so there is no restart program:
  the proof copies the (crash-free) `goose_init` / `goose_adequacy_blang` /
  `goose_adequacy` of `Perennial/GooseLang/Adequacy.lean`, allocating the heap
  with `na_heap_init_pointsto` (proved here: Perennial Lean's `na_heap_init`
  hands out only the authoritative heap) instead of `na_heap_init`, and handing
  the cells (`heapCells σ.heap`) to the WP as a fourth premise.
* There is no separate `global_state` argument in the run: a configuration
  state is `CfgState = state × GlobalState`, and `σ`, `g` are its two halves.
* Time receipts. Perennial Lean's program logic is built for a step-bounded
  semantics, and its adequacy takes a receipt bound `N` (the WP may assume
  `receiptBound GF = N`) and concludes for real executions of fewer than `N`
  steps. That form is `goose_adequacy_heap_N`. The Rocq-shaped theorem
  `goose_adequacy_heap` hides `N`: its WP premise is required under every
  instantiation of the ghost state (whatever `receiptBound GF` is), and so it
  can pick `N = n + 1` for a run of `n` steps; its conclusion `GooseAdequate`
  is about every finite execution `RealNsteps n` of the trusted (real)
  semantics, for any `n` (Rocq `rtc erased_step`). A client such as
  `check_adequate` takes the run as `RealNsteps n ([e], (σ, g)) κs
  (Val v :: tp, σ')` and applies `goose_adequate_result`. A WP proof that
  needs a bound on `N` (e.g. `N ≤ 2^48`) uses `goose_adequacy_heap_N`.
* Not-stuck is `RealNotStuck` (a value, or a real primitive step), Rocq's
  `is_Some (to_val e') ∨ reducible e' σ' g'`.
* Rocq's `all.allG Σ` is not a hypothesis: Lean's `HeapGS` does not include
  it, and a client needing more ghost state puts it in its `GF`.
-/
import Perennial.GooseLang.Adequacy

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.Algebra Iris.ProgramLogic Iris.Std ProofMode Language.Notation

section na_heap
open CMRA HeapView

variable {L V : Type} [DecidableEq L] {GF : BundledGFunctors} {LK : Type} (tls : LK → LockState)

theorem na_heap_alloc_st [hG : NaHeapGS L V GF] (σ : GMap L (LK × V)) (l : L) (v : V) (lk : LK)
    (Hσl : σ !! l = none) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls σ ==∗
      naHeapCtx tls (<[l := (lk, v)]> σ) ∗ naHeapPointstoSt (tls lk) l (.own 1) v := by
  unfold naHeapCtx naHeapPointstoSt
  have hupd : Auth (H := GMap L) (.own 1) (toNaHeap tls σ) ~~>
      Auth (H := GMap L) (.own 1) (toNaHeap tls (<[l := (lk, v)]> σ)) •
        Frag (H := GMap L) l (.own 1)
          ((toLockStateR (tls lk), toAgree (DiscreteO.mk v)) : NaHeapCmra V) := by
    rw [toNaHeap_insert]
    exact update_one_alloc (by simp [Hσl]) DFrac.valid_own_one (naHeapCmra_valid _ _)
  iintro H
  iapply (BIUpdate.mono iOwn_op.1)
  iapply (iOwn_update hupd) $$ H

theorem na_heap_alloc_big [hG : NaHeapGS L V GF] (σ : GMap L (LK × V)) :
    ⊢@{IProp GF} naHeapCtx (hG := hG) tls ∅ ==∗
      naHeapCtx tls σ ∗ [∗map] l ↦ lkv ∈ σ, naHeapPointstoSt (tls lkv.1) l (.own 1) lkv.2 := by
  induction σ using GMap.map_ind with
  | h0 =>
    iintro H
    imodintro
    iframe H
    iapply BigSepM.bigSepM_empty.2
    iempintro
  | hins l lkv σ Hl IH =>
    iintro H
    imod IH $$ H with ⟨H, Hs⟩
    imod na_heap_alloc_st tls σ l lkv.2 lkv.1 Hl $$ H with ⟨H, Hp⟩
    imodintro
    iframe H
    iapply (BigSepM.bigSepM_insert Hl).2
    iframe Hp Hs

theorem na_heap_init_pointsto [hpre : NaHeapGpreS L V GF] (σ : GMap L (LK × V)) :
    ⊢@{IProp GF} |==> ∃ hG : NaHeapGS L V GF, naHeapCtx (hG := hG) tls σ ∗
      [∗map] l ↦ lkv ∈ σ, naHeapPointstoSt (hG := hG) (tls lkv.1) l (.own 1) lkv.2 := by
  imod na_heap_init (L := L) (V := V) (hG := ⟨hpre.na_heap_preG_inG, default⟩) tls (∅ : GMap L (LK × V)) with ⟨%hG, H⟩
  imod na_heap_alloc_big (hG := hG) tls σ $$ H with ⟨H, Hs⟩
  imodintro
  iexists hG
  iframe H Hs

end na_heap

attribute [local instance] GSet.lawfulSet

section adequacy
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiInterpAdequacy ffi]
variable [FfiSemantics ext ffi] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- The cells of a heap `h`, each in the lock state it is in (Rocq
`[∗ map] l ↦ lkv ∈ h, na_heap_pointsto_st (tls lkv.1) l (DfracOwn 1) lkv.2`). -/
abbrev heapCells [hG : HeapGS .hasLC GF] (h : GMap Loc (NonAtomic val)) : IProp GF :=
  iprop([∗map] l ↦ lkv ∈ h, naHeapPointstoSt (tls lkv.1) l (.own 1) lkv.2)

/-- `goose_init` (Perennial `GooseLang/Adequacy.lean`), with the heap allocated
by `na_heap_init_pointsto`, so that `Hwp` also receives the cells of `σ.heap`. -/
theorem goose_init_heap [hPre : GooseGpreS ffi GF] [Hinv : InvGS_gen .hasLC GF]
    (N : Nat) (hN : 0 < N) (σ : state) (g : GlobalState) (κs : List Observation)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (P : HeapGS .hasLC GF → IProp GF)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      hG.goose_globalGS.gooseInvGS = Hinv →
      receiptBound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗
        heapCells σ.heap ={⊤}=∗ P hG) :
    ⊢@{IProp GF} |={⊤}=> ∃ hG : HeapGS .hasLC GF,
      ⌜hG.goose_globalGS.gooseInvGS = Hinv⌝ ∗
      gooseBstateInterp (((σ, g), N - 1) : BcfgState) κs ∗ P hG := by
  imod na_heap_init_pointsto (L := Loc) (V := val) tls σ.heap with ⟨%hHeap, Hh, Hcells⟩
  imod ProphMap.init (H := GMap proph_id) (V := val) κs g.usedProphId with ⟨%hProph, Hp⟩
  imod goState_init hPre.goose_preG_go_state σ.goState.packageState with ⟨%γ, Hgs, Hgs'⟩
  imod ffi_global_init GF hPre.goosePreGFfi g.globalWorld Hinitg with ⟨%hFG, Hgctx, Hgstart⟩
  imod ffi_local_init GF hPre.goosePreGFfi σ.world g.globalWorld Hinit
    with ⟨%hFL, Hlctx, Hlstart⟩
  imod receipt_init (hPre := hPre.goose_preG_receipt) N hN with ⟨%γR, %γL, HR⟩
  let G : GooseGlobalGS .hasLC GF :=
    ⟨Hinv, hProph, hFG, ⟨hPre.goose_preG_receipt.receiptPreGAllG, γR, γL, N, hN⟩⟩
  let L : GooseLocalGS GF :=
    ⟨hFL, σ.goState.goLctx, hHeap, goStateGSUpdatePre GF hPre.goose_preG_go_state γ⟩
  let hG : HeapGS .hasLC GF := ⟨G, L⟩
  imod (@Hwp hG rfl rfl rfl) $$ Hgstart Hlstart Hgs' Hcells with HP
  imodintro
  iexists hG
  isplitr
  · ipureintro; rfl
  iframe HP
  unfold gooseBstateInterp gooseStateInterp
  iframe
  ipureintro; rfl

/-- `goose_adequacy_blang` with the cells of the initial heap. -/
theorem goose_adequacy_heap_blang [hPre : GooseGpreS ffi GF] (N : Nat) (hN : 0 < N)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗
        heapCells σ.heap ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}) :
    adequate Stuckness.NotStuck e (((σ, g), N - 1) : BcfgState) (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) Stuckness.NotStuck e (((σ, g), N - 1) : BcfgState) φ ?_
  intro Hinv κs
  imod goose_init_heap (Hinv := Hinv) N hN σ g κs Hinitg Hinit
    (fun (_ : HeapGS .hasLC GF) => iprop(WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}))
    (@fun hG HinvEq HN Hlctx => by subst HinvEq; exact Hwp (hG := hG) HN Hlctx)
    with ⟨%hG, %HinvEq, Hσ, Hwp⟩
  imodintro
  iexists (fun σ κs => gooseBstateInterp (G := hG.goose_globalGS) (L := hG.goose_localGS) σ κs)
  iexists (fun _ => iprop(True))
  iframe Hσ
  obtain ⟨⟨Ginv, Gproph, Gffi, Grcpt⟩, L⟩ := hG
  cases HinvEq
  iexact Hwp

/-- Adequacy with the initial heap, for the real semantics and the time-receipt
bound `N`: in every real execution of `e` of fewer than `N` steps, the main
thread's result (if any) satisfies `φ`, and no thread is stuck. -/
theorem goose_adequacy_heap_N [hPre : GooseGpreS ffi GF] (N : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗
        heapCells σ.heap ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) := by
  have Hadeq := goose_adequacy_heap_blang N (by omega) e σ g φ Hinitg Hinit Hwp
  obtain ⟨c, Hb⟩ := bounded_nsteps_of_real Hsteps (N - 1) (by omega)
  have Hreach : ([e], (((σ, g), N - 1) : BcfgState)) -·->ₜₚ* (t2, (σ2, c)) :=
    (Language.erasedStep_nSteps _ _).mpr ⟨n, κs, Hb⟩
  refine ⟨?_, ?_⟩
  · rintro v t2' rfl
    exact Hadeq.adequate_result t2' (σ2, c) v Hreach
  · intro e2 he2
    exact realNotStuck_of_bounded (Hadeq.adequate_not_stuck t2 (σ2, c) e2 rfl Hreach he2)

/-- What the (real, crash-free) executions of `e` from `σ`, `g` satisfy (Rocq
`goose_adequate`): every value the main thread reduces to satisfies `φ`, and no
thread gets stuck. An execution is `RealNsteps n` for some `n` (Rocq
`rtc erased_step`). -/
structure GooseAdequate (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) : Prop where
  goose_adequate_result : ∀ n κs tp σ' v,
    RealNsteps n ([e], ((σ, g) : CfgState)) κs (Val v :: tp, σ') → φ v
  goose_adequate_not_stuck : ∀ n κs tp σ' e',
    RealNsteps n ([e], ((σ, g) : CfgState)) κs (tp, σ') → e' ∈ tp → RealNotStuck e' σ'

/-- Adequacy of GooseLang for runs that do not crash, with the initial heap
(Rocq `goose_adequacy_heap`). The WP is proved under every instantiation of
the ghost state whose Go local context is `σ`'s, and so for every time-receipt
bound: a proof that needs a bound on `N` uses `goose_adequacy_heap_N`. -/
theorem goose_adequacy_heap [hPre : GooseGpreS ffi GF]
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗
        heapCells σ.heap ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}) :
    GooseAdequate e σ g φ := by
  have H := fun n κs t2 σ2 Hs =>
    goose_adequacy_heap_N (GF := GF) (n + 1) e σ g φ Hinitg Hinit
      (@fun hG _ Hl => Hwp (hG := hG) Hl) n κs t2 σ2 Hs (by omega)
  exact ⟨fun n κs tp σ' v Hs => (H n κs _ σ' Hs).1 v tp rfl,
    fun n κs tp σ' e' Hs Hin => (H n κs tp σ' Hs).2 e' Hin⟩

end adequacy

end Perennial
