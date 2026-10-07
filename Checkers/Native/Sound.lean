/-
Soundness of the Lean-native checker (Checkers/Native/Check.lean).

`lcheck_sound`: if `lcheck f vars pre post = true` then
`triple_holds f vars pre post`, the statement `check_sound` and
`check_adequate` give for a `true` answer of the Go checker.

The proof is the Go proof's semantic layer, reused unchanged: each case of
`lexec` is the corresponding `exec_sound_*` lemma (ExecSpec.lean,
ExecSoundA/B/C.lean), the matcher ends in `match_path_sat` (MatchSound.lean),
the parser in `binders_interp_step` and `dj_interp_flatten` (ParseSound.lean),
and the composition is `triple_holds_intro` (Fn/Check.lean). What is new is
only the part the Go proof does with WP rules on Go loops: that the Lean
functions establish those lemmas' premises.
-/
import Checkers.Native.Check

set_option linter.unusedSectionVars false

namespace Perennial
namespace Checker
namespace Native

open Iris Iris.BI Iris.ProofMode

/-! ## Symbolic execution -/

section exec
variable [ext : FfiSyntax]

theorem paths_wf_tail (k : Nat) (p : spath) (ps : List spath) :
    paths_wf k (p :: ps) → paths_wf k ps := fun ⟨A, B, C⟩ =>
  ⟨fun q hq => A q (List.mem_cons_of_mem _ hq), fun q hq => B q (List.mem_cons_of_mem _ hq),
    fun q hq => C q (List.mem_cons_of_mem _ hq)⟩

theorem paths_wf_one (k : Nat) (p : spath) :
    wf_state (pst p) → k ≤ (svars (pst p)).length → vars_below (svars (pst p)).length (pret p) →
    paths_wf k [p] := by
  intro A B C
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq <;> rw [List.mem_singleton.mp hq] <;> assumption

/-- The paths of `ps` with a new return term and the same state. -/
theorem paths_wf_map_ret (k : Nat) (ps : List spath) (f : spath → term) :
    paths_wf k ps →
    (∀ p, p ∈ ps → vars_below (svars (pst p)).length (pret p) →
      vars_below (svars (pst p)).length (f p)) →
    paths_wf k (ps.map fun p => mkPath (f p) (pst p)) := by
  intro Hwf Hf
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq <;> obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  · exact Hwf.paths_wf_state p hp
  · exact Hwf.paths_wf_grow p hp
  · exact Hf p hp (Hwf.paths_wf_ret p hp)

/-- What `bindAll` gives: each path's continuation succeeded with a sublist
of the result, and the result is well formed if every continuation's is. -/
theorem bindAll_gen (k : Nat) (ps : List spath) (kf : spath → Option (List spath))
    (P : spath → List spath → Prop) (out : List spath) :
    bindAll ps kf = some out → paths_wf k ps →
    (∀ p, p ∈ ps → ∀ qs, kf p = some qs → P p qs ∧ paths_wf (svars (pst p)).length qs) →
    (∀ p, p ∈ ps → ∃ qs, qs ⊆ out ∧ P p qs) ∧ paths_wf k out := by
  induction ps generalizing out with
  | nil =>
    intro H _ _
    simp only [bindAll, Option.some.injEq] at H
    subst H
    exact ⟨fun _ hp => (nomatch hp), paths_wf_nil k⟩
  | cons p ps ih =>
    intro H Hwf Hk
    simp only [bindAll] at H
    split at H
    · rename_i qs rs Hq Hr
      cases H
      obtain ⟨A, B⟩ := ih rs Hr (paths_wf_tail _ _ _ Hwf)
        (fun p' hp' => Hk p' (List.mem_cons_of_mem _ hp'))
      obtain ⟨P1, W1⟩ := Hk p (List.mem_cons_self ..) qs Hq
      refine ⟨?_, paths_wf_app _ _ _
        (paths_wf_mono _ _ _ (Hwf.paths_wf_grow p (List.mem_cons_self ..)) W1) B⟩
      intro p' hp'
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact ⟨qs, List.subset_append_left _ _, P1⟩
      · obtain ⟨qs', Hs, HP⟩ := A p' hp'
        exact ⟨qs', fun x hx => List.mem_append_right _ (Hs hx), HP⟩
    · cases H

/-- The facts a continuation runs under, for a path of a well-formed list. -/
theorem path_ctx (k : Nat) (ps : List spath) (ρ : List (GoString × term)) (p : spath) :
    paths_wf k ps → env_below k ρ → p ∈ ps →
    wf_state (pst p) ∧ env_below (svars (pst p)).length ρ ∧
    vars_below (svars (pst p)).length (pret p) ∧ k ≤ (svars (pst p)).length := by
  intro Hwf Hρ hp
  have Hg := Hwf.paths_wf_grow p hp
  exact ⟨Hwf.paths_wf_state p hp, env_below_mono _ _ _ Hg Hρ, Hwf.paths_wf_ret p hp, Hg⟩

theorem lexec_sound (ce : cexpr) :
    ∀ (ρ : List (GoString × term)) (sst : sstate) (out : List spath),
      wf_state sst → env_below (svars sst).length ρ → lexec ce ρ sst = some out →
      exec_sound ce ρ sst out ∧ paths_wf (svars sst).length out := by
  induction ce with
  | CEInt w =>
    intro ρ sst out Hwf _ H
    simp only [lexec, Option.some.injEq] at H; subst H
    exact ⟨exec_sound_int _ _ _, paths_wf_single _ _ _ Hwf (Nat.le_refl _) trivial⟩
  | CEBool b =>
    intro ρ sst out Hwf _ H
    simp only [lexec, Option.some.injEq] at H; subst H
    exact ⟨exec_sound_bool _ _ _, paths_wf_single _ _ _ Hwf (Nat.le_refl _) trivial⟩
  | CEUnit =>
    intro ρ sst out Hwf _ H
    simp only [lexec, Option.some.injEq] at H; subst H
    exact ⟨exec_sound_unit _ _, paths_wf_single _ _ _ Hwf (Nat.le_refl _) trivial⟩
  | CEVar x =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i t Hlk
      cases H
      have Hb := env_below_lookup _ _ _ _ Hρ Hlk
      exact ⟨exec_sound_var _ _ _ _ Hlk Hb, paths_wf_single _ _ _ Hwf (Nat.le_refl _) Hb⟩
    · cases H
  | CEZero t =>
    intro ρ sst out Hwf _ H
    simp only [lexec, Option.some.injEq] at H; subst H
    exact ⟨exec_sound_zero _ _ _,
      paths_wf_single _ _ _ Hwf (Nat.le_refl _) (vars_below_ctype_zero _ _)⟩
  | CELet x e1 e2 ih1 ih2 =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      obtain ⟨S1, W1⟩ := ih1 ρ sst ps Hwf Hρ Hps
      obtain ⟨A, B⟩ := bindAll_gen _ ps _
        (fun p qs => exec_sound e2 ((x, pret p) :: ρ) (pst p) qs) out H W1 (by
          intro p hp qs Hk
          obtain ⟨Hw, Hρ', Hr, _⟩ := path_ctx _ _ ρ p W1 Hρ hp
          exact ih2 _ _ qs Hw (env_below_cons _ _ _ _ Hr Hρ') Hk)
      exact ⟨exec_sound_let _ _ _ _ _ _ _ S1 W1 A, B⟩
    · cases H
  | CESeq e1 e2 ih1 ih2 =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      obtain ⟨S1, W1⟩ := ih1 ρ sst ps Hwf Hρ Hps
      obtain ⟨A, B⟩ := bindAll_gen _ ps _
        (fun p qs => exec_sound e2 ρ (pst p) qs) out H W1 (by
          intro p hp qs Hk
          obtain ⟨Hw, Hρ', _, _⟩ := path_ctx _ _ ρ p W1 Hρ hp
          exact ih2 _ _ qs Hw Hρ' Hk)
      exact ⟨exec_sound_seq _ _ _ _ _ _ S1 W1 A, B⟩
    · cases H
  | CEIf c e1 e2 ihc ih1 ih2 =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      obtain ⟨S1, W1⟩ := ihc ρ sst ps Hwf Hρ Hps
      obtain ⟨A, B⟩ := bindAll_gen _ ps _
        (fun p qs => sort_of_vars (svars (pst p)) (pret p) = some SBool ∧ if_ok e1 e2 ρ p qs)
        out H W1 (by
          intro p hp qs Hk
          obtain ⟨Hw, Hρ', Hr, _⟩ := path_ctx _ _ ρ p W1 Hρ hp
          split at Hk
          · rename_i Hsort
            split at Hk
            · rename_i Hb
              obtain ⟨S, W⟩ := ih1 _ _ qs Hw Hρ' Hk
              exact ⟨⟨Hsort, .inl ⟨true, Hb, S⟩⟩, W⟩
            · rename_i Hb
              obtain ⟨S, W⟩ := ih2 _ _ qs Hw Hρ' Hk
              exact ⟨⟨Hsort, .inl ⟨false, Hb, S⟩⟩, W⟩
            · split at Hk
              · rename_i qs1 qs2 Hq1 Hq2
                cases Hk
                obtain ⟨S1, W1⟩ := ih1 _ _ qs1 (wf_state_assume _ _ Hw Hr) Hρ' Hq1
                obtain ⟨S2, W2⟩ := ih2 _ _ qs2
                  (wf_state_assume _ _ Hw (vars_below_negate _ _ Hr)) Hρ' Hq2
                exact ⟨⟨Hsort, .inr ⟨exec_sound_app_l _ _ _ _ _ S1,
                  exec_sound_app_r _ _ _ _ _ S2⟩⟩, paths_wf_app _ _ _ W1 W2⟩
              · cases Hk
          · cases Hk)
      exact ⟨exec_sound_if_gen _ _ _ _ _ _ _ S1 W1 (fun p hp => let ⟨_, _, Hs, _⟩ := A p hp; Hs)
        (fun p hp => let ⟨qs, Hs, _, Hok⟩ := A p hp; ⟨qs, Hs, Hok⟩), B⟩
    · cases H
  | CELoad t e ih =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      obtain ⟨S1, W1⟩ := ih ρ sst ps Hwf Hρ Hps
      obtain ⟨A, B⟩ := bindAll_gen _ ps _
        (fun p qs => ∃ y, heap_lookup (sheap (pst p)) (pret p) = some y ∧
          qs = [mkPath y (pst p)]) out H W1 (by
          intro p hp qs Hk
          obtain ⟨Hw, _, _, _⟩ := path_ctx _ _ ρ p W1 Hρ hp
          split at Hk
          · rename_i y Hy
            cases Hk
            exact ⟨⟨y, Hy, rfl⟩, paths_wf_single _ _ _ Hw (Nat.le_refl _)
              (heap_lookup_below _ _ _ _ Hw.wf_heap Hy)⟩
          · cases Hk)
      refine ⟨exec_sound_load _ _ _ _ _ _ S1 W1 (fun p hp => ?_), B⟩
      obtain ⟨qs, Hs, y, Hy, rfl⟩ := A p hp
      exact ⟨y, Hy, Hs (List.mem_singleton_self _)⟩
    · cases H
  | CEStore t e1 e2 ih1 ih2 =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      obtain ⟨S1, W1⟩ := ih1 ρ sst ps Hwf Hρ Hps
      obtain ⟨A, B⟩ := bindAll_gen _ ps _
        (fun p outp => ∃ qs, exec_sound e2 ρ (pst p) qs ∧
          paths_wf (svars (pst p)).length qs ∧ store_ok (pret p) qs outp) out H W1 (by
          intro p hp outp Hk
          obtain ⟨Hw, Hρ', _, _⟩ := path_ctx _ _ ρ p W1 Hρ hp
          split at Hk
          · rename_i qs Hq
            obtain ⟨S, W⟩ := ih2 _ _ qs Hw Hρ' Hq
            obtain ⟨A2, B2⟩ := bindAll_gen _ qs _
              (fun q rs => ∃ H', heap_update (sheap (pst q)) (pret p) (pret q) = some H' ∧
                rs = [mkPath TUnit (st_heap (pst q) H')]) outp Hk W (by
                intro q hq rs Hk2
                split at Hk2
                · rename_i H' Hu
                  cases Hk2
                  exact ⟨⟨H', Hu, rfl⟩, paths_wf_single _ _ _
                    (wf_state_heap _ _ _ _ (W.paths_wf_state q hq) (W.paths_wf_ret q hq) Hu)
                    (Nat.le_refl _) trivial⟩
                · cases Hk2)
            refine ⟨⟨qs, S, W, fun q hq => ?_⟩, B2⟩
            obtain ⟨rs, Hs, H', Hu, rfl⟩ := A2 q hq
            exact ⟨H', Hu, Hs (List.mem_singleton_self _)⟩
          · cases Hk)
      refine ⟨exec_sound_store _ _ _ _ _ _ _ S1 W1 (fun p hp => ?_), B⟩
      obtain ⟨outp, Hs, qs, S, W, Hok⟩ := A p hp
      refine ⟨qs, S, W, fun q hq => ?_⟩
      obtain ⟨H', Hu, Hin⟩ := Hok q hq
      exact ⟨H', Hu, Hs Hin⟩
    · cases H
  | CEAlloc t e ih =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      cases H
      obtain ⟨S1, W1⟩ := ih ρ sst ps Hwf Hρ Hps
      exact ⟨exec_sound_alloc _ _ _ _ _ _ S1 W1
        (fun p hp => List.mem_map.mpr ⟨p, hp, rfl⟩), paths_wf_alloc _ _ W1⟩
    · cases H
  | CEBinOp op t e1 e2 ih1 ih2 =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      obtain ⟨S1, W1⟩ := ih1 ρ sst ps Hwf Hρ Hps
      obtain ⟨A, B⟩ := bindAll_gen _ ps _
        (fun p outp => ∃ qs, exec_sound e2 ρ (pst p) qs ∧ ∀ q, q ∈ qs → ∃ r,
          sort_of_vars (svars (pst q)) (pret p) = some (ctype_sort t) ∧
          sort_of_vars (svars (pst q)) (pret q) = some (ctype_sort t) ∧
          apply_binop op t (pret p) (pret q) = some r ∧ mkPath r (pst q) ∈ outp)
        out H W1 (by
          intro p hp outp Hk
          obtain ⟨Hw, Hρ', Hr, _⟩ := path_ctx _ _ ρ p W1 Hρ hp
          split at Hk
          · rename_i qs Hq
            obtain ⟨S, W⟩ := ih2 _ _ qs Hw Hρ' Hq
            obtain ⟨A2, B2⟩ := bindAll_gen _ qs _
              (fun q rs => ∃ r,
                sort_of_vars (svars (pst q)) (pret p) = some (ctype_sort t) ∧
                sort_of_vars (svars (pst q)) (pret q) = some (ctype_sort t) ∧
                apply_binop op t (pret p) (pret q) = some r ∧ rs = [mkPath r (pst q)])
              outp Hk W (by
                intro q hq rs Hk2
                split at Hk2
                · rename_i Hs
                  split at Hk2
                  · rename_i r Hap
                    cases Hk2
                    refine ⟨⟨r, Hs.1, Hs.2, Hap, rfl⟩, paths_wf_single _ _ _
                      (W.paths_wf_state q hq) (Nat.le_refl _) ?_⟩
                    exact apply_binop_below _ _ _ _ _ _ Hap
                      (vars_below_mono _ _ _ (W.paths_wf_grow q hq) Hr) (W.paths_wf_ret q hq)
                  · cases Hk2
                · cases Hk2)
            refine ⟨⟨qs, S, fun q hq => ?_⟩, B2⟩
            obtain ⟨rs, Hs, r, H1, H2, H3, rfl⟩ := A2 q hq
            exact ⟨r, H1, H2, H3, Hs (List.mem_singleton_self _)⟩
          · cases Hk)
      refine ⟨exec_sound_binop _ _ _ _ _ _ _ _ S1 W1 (fun p hp => ?_), B⟩
      obtain ⟨outp, Hs, qs, S, Hq⟩ := A p hp
      refine ⟨qs, S, fun q hq => ?_⟩
      obtain ⟨r, H1, H2, H3, Hin⟩ := Hq q hq
      exact ⟨r, H1, H2, H3, Hs Hin⟩
    · cases H
  | CEUnOp op t e ih =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      obtain ⟨S1, W1⟩ := ih ρ sst ps Hwf Hρ Hps
      obtain ⟨A, B⟩ := bindAll_gen _ ps _
        (fun p qs => ∃ r, sort_of_vars (svars (pst p)) (pret p) = some (ctype_sort t) ∧
          apply_unop op t (pret p) = some r ∧ qs = [mkPath r (pst p)]) out H W1 (by
          intro p hp qs Hk
          obtain ⟨Hw, _, Hr, _⟩ := path_ctx _ _ ρ p W1 Hρ hp
          split at Hk
          · rename_i Hs
            split at Hk
            · rename_i r Hap
              cases Hk
              exact ⟨⟨r, Hs, Hap, rfl⟩, paths_wf_single _ _ _ Hw (Nat.le_refl _)
                (apply_unop_below _ _ _ _ _ Hap Hr)⟩
            · cases Hk
          · cases Hk)
      refine ⟨exec_sound_unop _ _ _ _ _ _ _ S1 (fun p hp => ?_), B⟩
      obtain ⟨qs, Hs, r, H1, H2, rfl⟩ := A p hp
      exact ⟨r, H1, H2, Hs (List.mem_singleton_self _)⟩
    · cases H
  | CEConvert t1 t2 e ih =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i Heq
      subst Heq
      obtain ⟨S, W⟩ := ih ρ sst out Hwf Hρ H
      exact ⟨exec_sound_convert _ _ _ _ _ S, W⟩
    · cases H
  | CEDo e ih =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      cases H
      obtain ⟨S1, W1⟩ := ih ρ sst ps Hwf Hρ Hps
      exact ⟨exec_sound_do _ _ _ _ _ S1 (fun p hp => List.mem_map.mpr ⟨p, hp, rfl⟩),
        paths_wf_map_ret _ _ _ W1 (fun _ _ _ => trivial)⟩
    · cases H
  | CEReturn e ih =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      cases H
      obtain ⟨S1, W1⟩ := ih ρ sst ps Hwf Hρ Hps
      exact ⟨exec_sound_return _ _ _ _ _ S1 (fun p hp => List.mem_map.mpr ⟨p, hp, rfl⟩),
        paths_wf_map_ret _ _ _ W1 (fun _ _ h => h)⟩
    · cases H
  | CEExcSeq e1 e2 ih1 ih2 =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      obtain ⟨S1, W1⟩ := ih1 ρ sst ps Hwf Hρ Hps
      obtain ⟨A, B⟩ := bindAll_gen _ ps _
        (fun p qs => (pret p = TExec ∧ exec_sound e2 ρ (pst p) qs) ∨
          ((∃ x, pret p = TRet x) ∧ qs = [p])) out H W1 (by
          intro p hp qs Hk
          obtain ⟨Hw, Hρ', Hr, _⟩ := path_ctx _ _ ρ p W1 Hρ hp
          split at Hk
          · rename_i Hb
            obtain ⟨S, W⟩ := ih2 _ _ qs Hw Hρ' Hk
            exact ⟨.inl ⟨Hb, S⟩, W⟩
          · rename_i x Hb
            cases Hk
            exact ⟨.inr ⟨⟨x, Hb⟩, rfl⟩, paths_wf_one _ _ Hw (Nat.le_refl _) Hr⟩
          · cases Hk)
      refine ⟨exec_sound_exc_seq _ _ _ _ _ _ S1 W1 (fun p hp => ?_), B⟩
      obtain ⟨qs, Hs, Hp⟩ := A p hp
      rcases Hp with ⟨Hb, S⟩ | ⟨Hx, rfl⟩
      · exact .inl ⟨Hb, qs, Hs, S⟩
      · exact .inr ⟨Hx, Hs (List.mem_singleton_self _)⟩
    · cases H
  | CEExcDo e ih =>
    intro ρ sst out Hwf Hρ H
    simp only [lexec] at H
    split at H
    · rename_i ps Hps
      obtain ⟨S1, W1⟩ := ih ρ sst ps Hwf Hρ Hps
      obtain ⟨A, B⟩ := bindAll_gen _ ps _
        (fun p qs => (pret p = TExec ∧ qs = [mkPath TUnit (pst p)]) ∨
          (∃ x, pret p = TRet x ∧ qs = [mkPath x (pst p)])) out H W1 (by
          intro p hp qs Hk
          obtain ⟨Hw, _, Hr, _⟩ := path_ctx _ _ ρ p W1 Hρ hp
          split at Hk
          · rename_i Hb
            cases Hk
            exact ⟨.inl ⟨Hb, rfl⟩, paths_wf_single _ _ _ Hw (Nat.le_refl _) trivial⟩
          · rename_i x Hb
            cases Hk
            rw [Hb] at Hr
            exact ⟨.inr ⟨x, Hb, rfl⟩, paths_wf_single _ _ _ Hw (Nat.le_refl _) Hr⟩
          · cases Hk)
      refine ⟨exec_sound_exc_do _ _ _ _ _ S1 (fun p hp => ?_), B⟩
      obtain ⟨qs, Hs, Hp⟩ := A p hp
      rcases Hp with ⟨Hb, rfl⟩ | ⟨x, Hb, rfl⟩
      · exact .inl ⟨Hb, Hs (List.mem_singleton_self _)⟩
      · exact .inr ⟨x, Hb, Hs (List.mem_singleton_self _)⟩
    · cases H

end exec

/-! ## Matching a path against a disjunct

None of this needs an FFI: the semantic facts are `MatchSound.lean`'s
relations (`match_rel`, `atom_step`, `phase1_inv`, `pure_ok`). -/

theorem tidx_ok_wf (x : term) : tidx_ok x = true → term_idx_wf x := by
  cases x <;> simp only [tidx_ok, term_idx_wf, decide_eq_true_eq] <;>
    first | (intro; trivial) | (intro h; unfold idx_wf; word)

/-- A leaf of the pattern matches only itself. -/
theorem match_rel_leaf (pats pok PV r) (x : term) (σ : List (Option term)) :
    is_tpat x = false → is_tresult x = false → tidx_ok x = true →
    term_a x = none → term_b x = none → term_c x = none →
    match_rel pats pok PV r (some x) (some x) σ σ := by
  intro Hp Hr Hok Ha Hb Hc
  refine MR_node x x σ σ σ σ Hp Hr rfl rfl (tidx_ok_wf x Hok) (tidx_ok_wf x Hok) ?_ ?_ ?_ <;>
    simp only [Ha, Hb, Hc] <;> exact MR_nil σ

theorem mt_core_sound (pats : List sort) (pok : List Bool) (PV : List sort) (r : term)
    (res : term → List (Option term) → Option (List (Option term)))
    (Hres : ∀ y σ σ', res y σ = some σ' → match_rel pats pok PV r (some TResult) (some y) σ σ') :
    ∀ x y σ σ', mt_core pats pok PV res x y σ = some σ' →
      match_rel pats pok PV r (some x) (some y) σ σ' := by
  intro x
  induction x with
  | TPat n =>
    intro y σ σ' H
    simp only [mt_core] at H
    split at H
    · rename_i s h1 h2 h3
      split at H
      · rename_i hs; cases H; exact MR_pat_new n y s σ h1 h2 h3 hs
      · cases H
    · rename_i z h1 h2
      split at H
      · rename_i hz; subst hz; cases H; exact MR_pat_old n z σ h1 h2
      · cases H
    · cases H
  | TResult => intro y σ σ' H; exact Hres y σ σ' H
  | TPlus a b iha ihb | TMinus a b iha ihb | TMul a b iha ihb | TEq a b iha ihb =>
    intro y σ σ' H
    cases y <;> simp only [mt_core] at H <;> try (simp at H; done)
    all_goals
      split at H
      · rename_i σ1 H1
        exact MR_node _ _ σ σ1 σ' σ' rfl rfl rfl rfl trivial trivial (iha _ _ _ H1) (ihb _ _ _ H)
          (MR_nil σ')
      · cases H
  | TLt sg a b iha ihb | TLe sg a b iha ihb =>
    intro y σ σ' H
    cases y <;> simp only [mt_core] at H <;> try (simp at H; done)
    all_goals
      split at H
      · rename_i hsg
        subst hsg
        split at H
        · rename_i σ1 H1
          exact MR_node _ _ σ σ1 σ' σ' rfl rfl rfl rfl trivial trivial (iha _ _ _ H1)
            (ihb _ _ _ H) (MR_nil σ')
        · cases H
      · cases H
  | TNeg a iha | TNot a iha | TRet a iha =>
    intro y σ σ' H
    cases y <;> simp only [mt_core] at H <;> try (simp at H; done)
    all_goals
      exact MR_node _ _ σ σ' σ' σ' rfl rfl rfl rfl trivial trivial (iha _ _ _ H) (MR_nil σ')
        (MR_nil σ')
  | TIte c a b ihc iha ihb =>
    intro y σ σ' H
    cases y <;> simp only [mt_core] at H <;> try (simp at H; done)
    split at H
    · rename_i σ1 H1
      split at H
      · rename_i σ2 H2
        exact MR_node _ _ σ σ1 σ2 σ' rfl rfl rfl rfl trivial trivial (ihc _ _ _ H1) (iha _ _ _ H2)
          (ihb _ _ _ H)
      · cases H
    · cases H
  | _ =>
    intro y σ σ' H
    simp only [mt_core] at H
    split at H
    · rename_i h
      obtain ⟨rfl, hok⟩ := h
      cases H
      exact match_rel_leaf _ _ _ _ _ σ rfl rfl hok rfl rfl rfl
    · cases H

theorem mt_sound (pats : List sort) (pok : List Bool) (PV : List sort) (r : term) :
    ∀ x y σ σ', mt pats pok PV r x y σ = some σ' →
      match_rel pats pok PV r (some x) (some y) σ σ' :=
  mt_core_sound pats pok PV r _ (fun y σ σ' H =>
    MR_result _ _ _ (mt_core_sound pats pok PV r (fun _ _ => none) (fun _ _ _ h => by cases h)
      r y σ σ' H))

theorem match_atom_sound (H : List scell) (pats : List sort) (pok : List Bool) (PV : List sort)
    (r x v : term) (σ : List (Option term)) (used : List Bool) (ok : Bool)
    (σ' : List (Option term)) (used' : List Bool) :
    used.length = H.length →
    match_atom H pats pok PV r x v σ used = some (ok, σ', used') →
    atom_step H pats pok PV r x v σ used ok σ' used' := by
  intro Hlen Hm
  simp only [match_atom] at Hm
  split at Hm
  · cases Hm
  · rename_i l Hl
    split at Hm
    · cases Hm; exact .inl ⟨rfl, rfl, rfl⟩
    · rename_i Hp
      split at Hm
      · cases Hm
      · rename_i j Hf
        split at Hm
        · cases Hm
        · rename_i c Hc
          split at Hm
          · rename_i σ'' Hmt
            cases Hm
            obtain ⟨sc, Hsc, Hu, Hloc⟩ := find_cell_Some H used l 0 j Hf
            simp only [Nat.sub_zero, Hc, Option.some.injEq] at Hsc
            subst Hsc
            have Hj : j < used.length := by rw [Hlen]; exact (List.getElem?_eq_some_iff.mp Hc).1
            refine .inr ⟨rfl, j, c, by rw [Hl, Hloc], by rw [Hloc]; simpa using Hp, Hc, ?_, rfl,
              mt_sound _ _ _ _ _ _ _ _ Hmt⟩
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem Hj,
              Option.getD_some] at Hu
            rw [List.getElem?_eq_getElem Hj, Hu]
          · cases Hm

theorem match_pass_sound (H : List scell) (atoms : List cassn) (pats : List sort)
    (pok : List Bool) (PV : List sort) (r : term) :
    ∀ (is : List Nat) (s s' : p1state),
      phase1_inv H atoms pats pok PV r s.p1σ s.p1used s.p1done →
      match_pass H atoms pats pok PV r is s = some s' →
      phase1_inv H atoms pats pok PV r s'.p1σ s'.p1used s'.p1done := by
  intro is
  induction is with
  | nil =>
    intro s s' Hi Hm
    simp only [match_pass, Option.some.injEq] at Hm
    subst Hm; exact Hi
  | cons i is ih =>
    intro s s' Hi Hm
    simp only [match_pass] at Hm
    split at Hm
    · rename_i x v Ha Hd
      split at Hm
      · exact ih s s' Hi Hm
      · rename_i σ'' used'' Hma
        exact ih _ s' (phase1_inv_step i Hi Ha Hd
          (match_atom_sound _ _ _ _ _ _ _ _ _ _ _ _ Hi.p1_len_used Hma)) Hm
      · cases Hm
    · exact ih s s' Hi Hm

theorem match_heap_sound (H : List scell) (atoms : List cassn) (pats : List sort)
    (pok : List Bool) (PV : List sort) (r : term) :
    ∀ (fuel : Nat) (s s' : p1state),
      phase1_inv H atoms pats pok PV r s.p1σ s.p1used s.p1done →
      match_heap H atoms pats pok PV r fuel s = some s' →
      phase1_inv H atoms pats pok PV r s'.p1σ s'.p1used s'.p1done ∧
        undone atoms s'.p1done = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro s s' Hi Hm
    rw [match_heap] at Hm
    split at Hm
    · rename_i Hu; cases Hm; exact ⟨Hi, Hu⟩
    · simp at Hm
  | succ fuel ih =>
    intro s s' Hi Hm
    rw [match_heap] at Hm
    split at Hm
    · rename_i Hu; cases Hm; exact ⟨Hi, Hu⟩
    · split at Hm
      · rename_i s'' Hp
        split at Hm
        · exact ih s'' s' (match_pass_sound _ _ _ _ _ _ _ (mkP1 s.p1σ s.p1used s.p1done false) s'' Hi Hp) Hm
        · cases Hm
      · cases Hm

theorem pure_check_sound (pc : List term) (atoms : List cassn) (σ : List (Option term))
    (r : term) : pure_check pc atoms σ r = true → pure_ok pc atoms σ r := by
  intro Hc i x Ha
  simp only [pure_check, List.all_eq_true, List.mem_range] at Hc
  have Hi := Hc i (List.getElem?_eq_some_iff.mp Ha).1
  rw [Ha] at Hi
  simp only at Hi
  split at Hi
  · rename_i y Hy
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at Hi
    exact ⟨y, Hy, Hi.1, Hi.2⟩
  · cases Hi

theorem sorts_check_sound (vars : List sort) (p : spath) (dj : cdisjunct) :
    sorts_check vars p dj = true → ∀ a, a ∈ d_atoms dj → atom_scoped vars.length a := by
  intro Hc a Ha
  simp only [sorts_check, List.all_eq_true] at Hc
  exact atom_well_sorted_scoped _ a (Hc a Ha)

theorem check_disjunct_sound (vars : List sort) (p : spath) (dj : cdisjunct) :
    check_disjunct vars p dj = true → d_fail dj = false ∧ path_sat_dj vars p dj := by
  intro Hc
  simp only [check_disjunct, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq] at Hc
  obtain ⟨⟨⟨Hf, Hlen⟩, Hs⟩, Hm⟩ := Hc
  split at Hm
  · rename_i s Hh
    obtain ⟨Hinv, Hund⟩ := match_heap_sound _ _ _ _ _ _ _ _ s (phase1_inv_init _ _ _ _ _ _) Hh
    refine ⟨Hf, ?_⟩
    intro ext ffi fi fs gc hlc GF hG sem
    exact @match_path_sat ext ffi fi fs gc hlc GF hG sem vars p dj s.p1σ s.p1used s.p1done Hlen
      (sorts_check_sound _ _ _ Hs) Hinv Hund (pure_check_sound _ _ _ _ Hm)
  · cases Hm

/-! ## Parsing the postcondition -/

section parse
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `parse_from`'s result entails the binders declared so far over what is
left of the assertion: `parseDisjunct`'s loop invariant (ParseSound.lean). -/
theorem parse_from_sound (b : cassn) : ∀ (dj : cdisjunct), d_atoms dj = [] →
    (d_pats dj).length = (d_pat_ok dj).length → d_fail (parse_from dj b) = false →
    ∀ V, dj_interp (GF := GF) V (parse_from dj b) ⊢ binders_interp V dj b := by
  induction b with
  | CAExists k s p ih =>
    intro dj Hat Hlen Hf V
    simp only [parse_from] at Hf ⊢
    split
    · rename_i h; simp only [h, ↓reduceIte, dj_failed] at Hf; cases Hf
    · rename_i h
      simp only [h, ↓reduceIte] at Hf
      refine (ih _ (by simp [bind_pat, grow_pats, Hat])
        (by simp [bind_pat, grow_pats, pad_length, Hlen]) Hf V).trans
        (binders_interp_step V dj k s p Hlen h)
  | _ =>
    intro dj Hat _ Hf V
    simp only [parse_from] at Hf ⊢
    split
    · rename_i ats Hfl
      exact dj_interp_flatten V dj _ ats Hat Hfl
    · rename_i Hfl
      rw [Hfl] at Hf
      simp [dj_failed] at Hf

theorem parse_disjunct_sound (a : cassn) : d_fail (parse_disjunct a) = false →
    ∀ V, dj_interp (GF := GF) V (parse_disjunct a) ⊢ assn_interp V a :=
  fun Hf V => (parse_from_sound a _ rfl rfl Hf V).trans (binders_interp_init V _ a rfl)

end parse

theorem parse_disjuncts_sound (post : cassn) (dj : cdisjunct) :
    dj ∈ parse_disjuncts post → d_fail dj = false → dj_entails dj post := by
  intro Hin Hf ext ffi fi fs gc hlc GF hG sem V
  simp only [parse_disjuncts, List.mem_map] at Hin
  obtain ⟨oa, Hoa, rfl⟩ := Hin
  cases oa with
  | none => simp at Hf
  | some a =>
    exact (parse_disjunct_sound (GF := GF) a Hf V).trans (assn_disjuncts_sound V post a Hoa)

/-! ## The checker -/

theorem lverify_sound (ps : List spath) (vars : List sort) (post : cassn) :
    lverify ps vars post = true → ∀ sp, sp ∈ ps → path_ok vars post sp := by
  intro Hv sp Hsp
  simp only [lverify, List.all_eq_true, List.any_eq_true] at Hv
  obtain ⟨dj, Hdj, Hc⟩ := Hv sp Hsp
  obtain ⟨Hf, Hsat⟩ := check_disjunct_sound _ _ _ Hc
  exact ⟨dj, Hf, Hsat, parse_disjuncts_sound _ _ Hdj Hf⟩

/-- Soundness of the Lean-native checker: a `true` answer establishes the
same triple, in every FFI, ghost state and Go semantics, as a `true` answer
of `checker.Check` (`check_sound`, `check_adequate`). -/
theorem lcheck_sound (f : cfunc) (vars : List sort) (pre post : cassn) :
    lcheck f vars pre post = true → triple_holds f vars pre post := by
  intro Hc
  simp only [lcheck] at Hc
  split at Hc
  · rename_i ps Ha
    simp only [lanalyze] at Ha
    split at Ha
    · rename_i Hok
      obtain ⟨Hlen, Hws⟩ := Hok
      intro ext ffi fi fs gc hlc GF hG sem
      obtain ⟨Hsnd, Hwf⟩ := lexec_sound _ _ _ ps (pre_state_wf vars pre Hws)
        (penv_below _ _ Hlen) Ha
      exact triple_holds_intro f vars pre post ps Hwf ⟨Hlen, Hws, Hsnd⟩
        (lverify_sound _ _ _ Hc) ext ffi fi fs gc hlc GF hG sem
    · cases Ha
  · cases Hc

end Native
end Checker
end Perennial
