/-
Soundness of the Lean table checker (LCheck/TCheck/Check.lean), part 1: terms.

What the term operations of `ltcheck` mean under a denotation `DA`, at a
valuation `θ` of the logical variables (`teval DA θ`, Denote.lean):

* `teq` is equality; a term of sort `s` (`sortOf`) evaluates to a value of
  sort `s` (`sortOf_sound`), at a valuation with the right sorts (`sorted`);
* an evaluation that succeeds is unchanged by new variables (`teval_ext`);
* instantiation is substitution (`inst_teval`), matching produces an
  instance (`mterm_inst`), and normalization by valid facts preserves
  evaluation (`norm_teval`).

Nothing here mentions the program logic.
-/
import Checkers.TCheck.Link
import LCheck.TCheck.Check

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace TCheck
namespace LC

open Iris Iris.BI

/-! ## `teq` -/

mutual
theorem teq_sound : ∀ a b : tterm, teq a b = true → a = b
  | TVar n, TVar m, h => by simp only [teq, beq_iff_eq] at h; rw [h]
  | TSym n xs, TSym m bs, h => by
      simp only [teq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, teqs_sound xs bs h.2]
  | TPair a b, TPair c d, h => by
      simp only [teq, Bool.and_eq_true] at h
      rw [teq_sound a c h.1, teq_sound b d h.2]
  | TLit t xs, TLit u bs, h => by
      simp only [teq, Bool.and_eq_true] at h
      rw [teq_sound t u h.1, teqs_sound xs bs h.2]
  | TUnit, TUnit, _ => rfl
  | TVar _, TSym _ _, h | TVar _, TPair _ _, h | TVar _, TLit _ _, h | TVar _, TUnit, h
  | TSym _ _, TVar _, h | TSym _ _, TPair _ _, h | TSym _ _, TLit _ _, h | TSym _ _, TUnit, h
  | TPair _ _, TVar _, h | TPair _ _, TSym _ _, h | TPair _ _, TLit _ _, h | TPair _ _, TUnit, h
  | TLit _ _, TVar _, h | TLit _ _, TSym _ _, h | TLit _ _, TPair _ _, h | TLit _ _, TUnit, h
  | TUnit, TVar _, h | TUnit, TSym _ _, h | TUnit, TPair _ _, h | TUnit, TLit _ _, h => by
      simp [teq] at h
theorem teqs_sound : ∀ xs bs : List tterm, teqs xs bs = true → xs = bs
  | [], [], _ => rfl
  | a :: xs, b :: bs, h => by
      simp only [teqs, Bool.and_eq_true] at h
      rw [teq_sound a b h.1, teqs_sound xs bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [teqs] at h
end

/-! ## Lookups -/

theorem nth_error_eq {A : Type} : ∀ (l : List A) (n : Nat), nth_error l n = l[n]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => by simp [nth_error, nth_error_eq l n]

theorem lookup_sym_eq : ∀ (l : List symdecl) (n : Nat) (d : symdecl), l[n]? = some d →
    lookup_sym l n = d
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => by simpa [lookup_sym] using h
  | _ :: l, n + 1, d, h => by simpa [lookup_sym] using lookup_sym_eq l n d (by simpa using h)

theorem lookup_pred_eq : ∀ (l : List preddecl) (n : Nat) (d : preddecl), l[n]? = some d →
    lookup_pred l n = d
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => by simpa [lookup_pred] using h
  | _ :: l, n + 1, d, h => by simpa [lookup_pred] using lookup_pred_eq l n d (by simpa using h)

section den
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
variable {syms : List symdecl} {preds : List preddecl} (DA : DenAt GF syms preds)

/-! ## Casts -/

theorem nat_cast_self : ∀ (P : Nat → Type) (i : Nat) (x : P i), nat_cast P i i x = some x
  | _, 0, _ => rfl
  | P, i + 1, x => nat_cast_self (fun k => P (k + 1)) i x

theorem cast_self (s : srt) (x : srt_den DA.d_sort s) : cast DA s ⟨s, x⟩ = some x := by
  cases s with
  | SVal => rfl
  | SType => rfl
  | SU n => exact nat_cast_self DA.d_sort n x

/-- A valuation whose values have the sorts `vars`. -/
def sorted (θ : List (dyn DA)) (vars : List srt) : Prop := θ.map Sigma.fst = vars

theorem sorted_lookup (θ : List (dyn DA)) (vars : List srt) (n : Nat) (s : srt) :
    sorted DA θ vars → vars[n]? = some s → ∃ x, θ[n]? = some ⟨s, x⟩ := by
  intro Hs Hn
  subst Hs
  rw [List.getElem?_map] at Hn
  cases h : θ[n]? with
  | none => rw [h] at Hn; cases Hn
  | some d =>
    rw [h] at Hn
    obtain ⟨s', x⟩ := d
    simp only [Option.map_some, Option.some.injEq] at Hn
    subst Hn
    exact ⟨x, rfl⟩

theorem sorted_app (θ θx : List (dyn DA)) (vs ws : List srt) :
    sorted DA θ vs → sorted DA θx ws → sorted DA (θ ++ θx) (vs ++ ws) := by
  intro h1 h2; simp only [sorted, List.map_append] at *; rw [h1, h2]

/-- `sym_apply` of arguments of the declared sorts succeeds. -/
theorem sym_apply_sorted : ∀ (ss : List srt) {R : Type} (f : arrows DA.d_sort ss R)
    (vs : List (Option (dyn DA))),
    List.Forall₂ (fun v s => ∃ x, v = some ⟨s, x⟩) vs ss → ∃ r, sym_apply DA ss f vs = some r
  | [], _, f, [], _ => ⟨f, rfl⟩
  | s :: ss, _, f, v :: vs, h => by
      cases h with
      | cons h1 h2 =>
        obtain ⟨x, rfl⟩ := h1
        simp only [sym_apply, cast_self]
        exact sym_apply_sorted ss (f x) vs h2
  | [], _, _, _ :: _, h | _ :: _, _, _, [], h => by cases h

/-- `sym_apply` that succeeds had no failed argument. -/
theorem sym_apply_some : ∀ (ss : List srt) {R : Type} (f : arrows DA.d_sort ss R)
    (vs : List (Option (dyn DA))) (r : R),
    sym_apply DA ss f vs = some r → ∀ v, v ∈ vs → v.isSome
  | [], _, _, [], _, _, v, hv => by cases hv
  | [], _, _, _ :: _, _, h, _, _ => by simp [sym_apply] at h
  | _ :: _, _, _, [], _, h, _, _ => by simp [sym_apply] at h
  | _ :: _, _, _, none :: _, _, h, _, _ => by simp [sym_apply] at h
  | a :: ss, _, f, some d :: vs, r, h, v, hv => by
      simp only [sym_apply] at h
      split at h
      · rename_i x _
        rcases List.mem_cons.mp hv with rfl | hv
        · rfl
        · exact sym_apply_some ss (f x) vs r h v hv
      · cases h

theorem vals_of_some : ∀ (ds : List (Option (dyn DA))) (vs : List val),
    vals_of DA ds = some vs → ∀ d, d ∈ ds → d.isSome
  | [], _, _, _, h => by cases h
  | d :: ds, vs, h, e, he => by
      simp only [vals_of] at h
      split at h
      · rename_i v vs' hv hvs
        rcases List.mem_cons.mp he with rfl | he
        · cases e with
          | none => simp [as_val] at hv
          | some _ => rfl
        · exact vals_of_some ds vs' hvs e he
      · cases h

/-! ## Sorts -/

/-- A value of sort `s` evaluates to a value of sort `s`. -/
def has_srt (d : Option (dyn DA)) (s : srt) : Prop := ∃ x, d = some ⟨s, x⟩

mutual
theorem sortOf_sound (θ : List (dyn DA)) (vars : List srt) (Hθ : sorted DA θ vars) :
    ∀ (t : tterm) (s : srt), sortOf syms vars t = some s → has_srt DA (teval DA θ t) s
  | TVar n, s, h => by
      simp only [sortOf] at h
      obtain ⟨x, hx⟩ := sorted_lookup DA θ vars n s Hθ h
      exact ⟨x, by simp [teval, nth_error_eq, hx]⟩
  | TSym n args, s, h => by
      simp only [sortOf] at h
      split at h
      · rename_i d hd
        split at h
        · rename_i hargs
          cases h
          have hl := lookup_sym_eq syms n d hd
          rw [← hl] at hargs ⊢
          obtain ⟨r, hr⟩ := sym_apply_sorted DA _ (DA.d_sym n) (tevals DA θ args)
            (sortsOf_sound θ vars Hθ args _ hargs)
          exact ⟨r, by simp only [teval, hr]⟩
        · cases h
      · cases h
  | TPair a b, s, h => by
      simp only [sortOf] at h
      split at h
      · rename_i ha hb
        cases h
        obtain ⟨x, hx⟩ := sortOf_sound θ vars Hθ a SVal ha
        obtain ⟨y, hy⟩ := sortOf_sound θ vars Hθ b SVal hb
        exact ⟨PairV x y, by simp only [teval, hx, hy, as_val, cast_self]⟩
      · cases h
  | TLit ty es, s, h => by
      simp only [sortOf] at h
      split at h
      · rename_i hty
        split at h
        · rename_i hes
          cases h
          obtain ⟨T, hT⟩ := sortOf_sound θ vars Hθ ty SType hty
          obtain ⟨vs, hvs⟩ := valsOf_sound θ vars Hθ es hes
          refine ⟨(LiteralValueV (vs.map fun v => KeyedElement none (ElementExpression T (Val v))) :
            val), ?_⟩
          simp only [teval, hT, cast_self, hvs]
        · cases h
      · cases h
  | TUnit, s, h => by
      simp only [sortOf, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl⟩
theorem sortsOf_sound (θ : List (dyn DA)) (vars : List srt) (Hθ : sorted DA θ vars) :
    ∀ (ts : List tterm) (ss : List srt), sortsOf syms vars ts ss = true →
      List.Forall₂ (fun v s => ∃ x, v = some ⟨s, x⟩) (tevals DA θ ts) ss
  | [], [], _ => .nil
  | t :: ts, s :: ss, h => by
      simp only [sortsOf, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .cons (sortOf_sound θ vars Hθ t s h.1) (sortsOf_sound θ vars Hθ ts ss h.2)
  | [], _ :: _, h | _ :: _, [], h => by simp [sortsOf] at h
theorem valsOf_sound (θ : List (dyn DA)) (vars : List srt) (Hθ : sorted DA θ vars) :
    ∀ (ts : List tterm), valsOf syms vars ts = true → ∃ vs, vals_of DA (tevals DA θ ts) = some vs
  | [], _ => ⟨[], rfl⟩
  | t :: ts, h => by
      simp only [valsOf, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨x, hx⟩ := sortOf_sound θ vars Hθ t SVal h.1
      obtain ⟨vs, hvs⟩ := valsOf_sound θ vars Hθ ts h.2
      exact ⟨x :: vs, by simp only [tevals, vals_of, hx, as_val, cast_self, hvs]⟩
end

/-! ## Extending the valuation -/

mutual
theorem teval_ext (θ θx : List (dyn DA)) :
    ∀ (t : tterm) (d : dyn DA), teval DA θ t = some d → teval DA (θ ++ θx) t = some d
  | TVar n, d, h => by
      simp only [teval, nth_error_eq] at h ⊢
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1, h]
  | TSym n args, d, h => by
      simp only [teval] at h ⊢
      split at h
      · rename_i r hr
        rw [tevals_ext θ θx args (sym_apply_some DA _ _ _ r hr), hr]
        exact h
      · cases h
  | TPair a b, d, h => by
      simp only [teval] at h ⊢
      split at h
      · rename_i va vb ha hb
        cases ea : teval DA θ a with
        | none => rw [ea] at ha; simp [as_val] at ha
        | some da =>
          cases eb : teval DA θ b with
          | none => rw [eb] at hb; simp [as_val] at hb
          | some db =>
            rw [teval_ext θ θx a da ea, teval_ext θ θx b db eb, ← ea, ← eb, ha, hb]
            exact h
      · cases h
  | TLit ty es, d, h => by
      simp only [teval] at h ⊢
      split at h
      · rename_i T vs hT hvs
        cases et : teval DA θ ty with
        | none => rw [et] at hT; cases hT
        | some dt =>
          rw [teval_ext θ θx ty dt et, tevals_ext θ θx es (vals_of_some DA _ vs hvs), ← et]
          simp only [hT, hvs]
          exact h
      · cases h
  | TUnit, d, h => h
theorem tevals_ext (θ θx : List (dyn DA)) :
    ∀ (ts : List tterm), (∀ v, v ∈ tevals DA θ ts → v.isSome) →
      tevals DA (θ ++ θx) ts = tevals DA θ ts
  | [], _ => rfl
  | t :: ts, h => by
      simp only [tevals] at h ⊢
      cases et : teval DA θ t with
      | none => have := h _ (List.mem_cons_self ..); rw [et] at this; cases this
      | some d =>
        rw [teval_ext θ θx t d et,
          tevals_ext θ θx ts (fun v hv => h v (List.mem_cons_of_mem _ hv))]
end

end den

/-! ## Bindings and matching (no denotation) -/

/-- `b'` keeps every binding of `b`. -/
def bext (b b' : Bind) : Prop := ∀ (i : Nat) (u : tterm), b[i]? = some (some u) → b'[i]? = some (some u)

/-- The full binding `bs` agrees with the partial binding `b`. -/
def agrees (b : Bind) (bs : List tterm) : Prop := ∀ (i : Nat) (u : tterm), b[i]? = some (some u) → bs[i]? = some u

/-- Every bound term has its variable's sort, over the state's variables. -/
def bwf (syms : List symdecl) (vars psorts : List srt) (b : Bind) : Prop :=
  ∀ (i : Nat) (u : tterm), b[i]? = some (some u) → ∃ s, psorts[i]? = some s ∧
    sortOf syms vars u = some s

theorem bext_refl (b : Bind) : bext b b := fun _ _ h => h
theorem bext_trans {b1 b2 b3 : Bind} : bext b1 b2 → bext b2 b3 → bext b1 b3 :=
  fun h1 h2 i u h => h2 i u (h1 i u h)
theorem agrees_of_bext {b b' : Bind} {bs : List tterm} : bext b b' → agrees b' bs → agrees b bs :=
  fun h1 h2 i u h => h2 i u (h1 i u h)

theorem bwf_replicate (syms : List symdecl) (vars psorts : List srt) (n : Nat) :
    bwf syms vars psorts (List.replicate n none) := by
  intro i u h; simp [List.getElem?_replicate] at h

/-- Binding variable `n`, unbound so far, to `t` of its sort. -/
theorem bind_set (syms : List symdecl) (vars psorts : List srt) (b : Bind) (n : Nat) (t : tterm)
    (s : srt) : b[n]? = some none → psorts[n]? = some s → sortOf syms vars t = some s →
    bext b (b.set n (some t)) ∧ (bwf syms vars psorts b → bwf syms vars psorts (b.set n (some t))) ∧
    (b.set n (some t))[n]? = some (some t) := by
  intro hn hs ht
  have hlt : n < b.length := (List.getElem?_eq_some_iff.mp hn).1
  refine ⟨?_, ?_, by simp [List.getElem?_set_self hlt]⟩
  · intro i u hi
    by_cases hin : i = n
    · subst hin; rw [hn] at hi; cases hi
    · rw [List.getElem?_set_ne (Ne.symm hin)]; exact hi
  · intro hb i u hi
    by_cases hin : i = n
    · subst hin
      rw [List.getElem?_set_self hlt] at hi
      cases hi
      exact ⟨s, hs, ht⟩
    · rw [List.getElem?_set_ne (Ne.symm hin)] at hi; exact hb i u hi

mutual
/-- Matching binds every variable of the pattern, consistently with the
matched term, keeping the earlier bindings and their sorts. -/
theorem mterm_sound (syms : List symdecl) (vars psorts : List srt) :
    ∀ (p t : tterm) (b b' : Bind), mterm syms vars psorts p t b = some b' →
      bext b b' ∧ (bwf syms vars psorts b → bwf syms vars psorts b') ∧
      ∀ bs, agrees b' bs → inst bs p = some t
  | TVar n, t, b, b', h => by
      simp only [mterm] at h
      split at h
      · rename_i u hu
        split at h
        · rename_i heq
          cases h
          have := teq_sound u t heq
          subst this
          exact ⟨bext_refl b, id, fun bs hag => by simp only [inst]; exact hag n u hu⟩
        · cases h
      · rename_i hu
        split at h
        · rename_i s hs
          split at h
          · rename_i ht
            cases h
            obtain ⟨H1, H2, H3⟩ := bind_set syms vars psorts b n t s hu hs ht
            exact ⟨H1, H2, fun bs hag => by simp only [inst]; exact hag n t H3⟩
          · cases h
        · cases h
      · cases h
  | TSym n ps, TSym m ts, b, b', h => by
      simp only [mterm] at h
      split at h
      · rename_i hnm
        obtain ⟨H1, H2, H3⟩ := mterms_sound syms vars psorts ps ts b b' h
        refine ⟨H1, H2, fun bs hag => ?_⟩
        simp only [beq_iff_eq] at hnm
        subst hnm
        simp only [inst, H3 bs hag]
      · cases h
  | TPair p q, TPair t u, b, b', h => by
      simp only [mterm] at h
      split at h
      · rename_i b1 h1
        obtain ⟨A1, B1, C1⟩ := mterm_sound syms vars psorts p t b b1 h1
        obtain ⟨A2, B2, C2⟩ := mterm_sound syms vars psorts q u b1 b' h
        refine ⟨bext_trans A1 A2, fun hb => B2 (B1 hb), fun bs hag => ?_⟩
        simp only [inst, C1 bs (agrees_of_bext A2 hag), C2 bs hag]
      · cases h
  | TLit p ps, TLit t ts, b, b', h => by
      simp only [mterm] at h
      split at h
      · rename_i b1 h1
        obtain ⟨A1, B1, C1⟩ := mterm_sound syms vars psorts p t b b1 h1
        obtain ⟨A2, B2, C2⟩ := mterms_sound syms vars psorts ps ts b1 b' h
        refine ⟨bext_trans A1 A2, fun hb => B2 (B1 hb), fun bs hag => ?_⟩
        simp only [inst, C1 bs (agrees_of_bext A2 hag), C2 bs hag]
      · cases h
  | TUnit, TUnit, b, b', h => by
      simp only [mterm, Option.some.injEq] at h
      subst h
      exact ⟨bext_refl b, id, fun _ _ => rfl⟩
  | TSym _ _, TVar _, _, _, h | TSym _ _, TPair _ _, _, _, h | TSym _ _, TLit _ _, _, _, h
  | TSym _ _, TUnit, _, _, h
  | TPair _ _, TVar _, _, _, h | TPair _ _, TSym _ _, _, _, h | TPair _ _, TLit _ _, _, _, h
  | TPair _ _, TUnit, _, _, h
  | TLit _ _, TVar _, _, _, h | TLit _ _, TSym _ _, _, _, h | TLit _ _, TPair _ _, _, _, h
  | TLit _ _, TUnit, _, _, h
  | TUnit, TVar _, _, _, h | TUnit, TSym _ _, _, _, h | TUnit, TPair _ _, _, _, h
  | TUnit, TLit _ _, _, _, h => by simp [mterm] at h
theorem mterms_sound (syms : List symdecl) (vars psorts : List srt) :
    ∀ (ps ts : List tterm) (b b' : Bind), mterms syms vars psorts ps ts b = some b' →
      bext b b' ∧ (bwf syms vars psorts b → bwf syms vars psorts b') ∧
      ∀ bs, agrees b' bs → insts bs ps = some ts
  | [], [], b, b', h => by
      simp only [mterms, Option.some.injEq] at h
      subst h
      exact ⟨bext_refl b, id, fun _ _ => rfl⟩
  | p :: ps, t :: ts, b, b', h => by
      simp only [mterms] at h
      split at h
      · rename_i b1 h1
        obtain ⟨A1, B1, C1⟩ := mterm_sound syms vars psorts p t b b1 h1
        obtain ⟨A2, B2, C2⟩ := mterms_sound syms vars psorts ps ts b1 b' h
        refine ⟨bext_trans A1 A2, fun hb => B2 (B1 hb), fun bs hag => ?_⟩
        simp only [insts, C1 bs (agrees_of_bext A2 hag), C2 bs hag]
      · cases h
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [mterms] at h
end


mutual
theorem mterm_length (syms : List symdecl) (vars psorts : List srt) :
    ∀ (p t : tterm) (b b' : Bind), mterm syms vars psorts p t b = some b' → b'.length = b.length
  | TVar n, t, b, b', h => by
      simp only [mterm] at h
      split at h
      · split at h
        · cases h; rfl
        · cases h
      · split at h
        · split at h
          · cases h; simp
          · cases h
        · cases h
      · cases h
  | TSym n ps, TSym m ts, b, b', h => by
      simp only [mterm] at h
      split at h
      · exact mterms_length syms vars psorts ps ts b b' h
      · cases h
  | TPair p q, TPair t u, b, b', h => by
      simp only [mterm] at h
      split at h
      · rename_i b1 h1
        rw [mterm_length syms vars psorts q u b1 b' h, mterm_length syms vars psorts p t b b1 h1]
      · cases h
  | TLit p ps, TLit t ts, b, b', h => by
      simp only [mterm] at h
      split at h
      · rename_i b1 h1
        rw [mterms_length syms vars psorts ps ts b1 b' h, mterm_length syms vars psorts p t b b1 h1]
      · cases h
  | TUnit, TUnit, b, b', h => by simp only [mterm, Option.some.injEq] at h; subst h; rfl
  | TSym _ _, TVar _, _, _, h | TSym _ _, TPair _ _, _, _, h | TSym _ _, TLit _ _, _, _, h
  | TSym _ _, TUnit, _, _, h
  | TPair _ _, TVar _, _, _, h | TPair _ _, TSym _ _, _, _, h | TPair _ _, TLit _ _, _, _, h
  | TPair _ _, TUnit, _, _, h
  | TLit _ _, TVar _, _, _, h | TLit _ _, TSym _ _, _, _, h | TLit _ _, TPair _ _, _, _, h
  | TLit _ _, TUnit, _, _, h
  | TUnit, TVar _, _, _, h | TUnit, TSym _ _, _, _, h | TUnit, TPair _ _, _, _, h
  | TUnit, TLit _ _, _, _, h => by simp [mterm] at h
theorem mterms_length (syms : List symdecl) (vars psorts : List srt) :
    ∀ (ps ts : List tterm) (b b' : Bind), mterms syms vars psorts ps ts b = some b' →
      b'.length = b.length
  | [], [], b, b', h => by simp only [mterms, Option.some.injEq] at h; subst h; rfl
  | p :: ps, t :: ts, b, b', h => by
      simp only [mterms] at h
      split at h
      · rename_i b1 h1
        rw [mterms_length syms vars psorts ps ts b1 b' h, mterm_length syms vars psorts p t b b1 h1]
      · cases h
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [mterms] at h
end

theorem mpat_length (syms : List symdecl) (vars psorts : List srt) :
    ∀ (p s : tpat) (b b' : Bind), mpat syms vars psorts p s b = some b' → b'.length = b.length
  | PVal p, PVal t, b, b', h => mterm_length syms vars psorts p t b b' h
  | PApp p q, PApp s u, b, b', h => by
      simp only [mpat] at h
      split at h
      · rename_i b1 h1
        rw [mpat_length syms vars psorts q u b1 b' h, mpat_length syms vars psorts p s b b1 h1]
      · cases h
  | PVal _, PApp _ _, _, _, h | PApp _ _, PVal _, _, _, h => by simp [mpat] at h

/-- A pattern's instance, as an expression pattern. -/
def pinst (bs : List tterm) : tpat → Option tpat
  | PVal t =>
      match inst bs t with
      | some u => some (PVal u)
      | none => none
  | PApp a b =>
      match pinst bs a, pinst bs b with
      | some a', some b' => some (PApp a' b')
      | _, _ => none

theorem mpat_sound (syms : List symdecl) (vars psorts : List srt) :
    ∀ (p s : tpat) (b b' : Bind), mpat syms vars psorts p s b = some b' →
      bext b b' ∧ (bwf syms vars psorts b → bwf syms vars psorts b') ∧
      ∀ bs, agrees b' bs → pinst bs p = some s
  | PVal p, PVal t, b, b', h => by
      simp only [mpat] at h
      obtain ⟨A, B, C⟩ := mterm_sound syms vars psorts p t b b' h
      exact ⟨A, B, fun bs hag => by simp only [pinst, C bs hag]⟩
  | PApp p q, PApp s u, b, b', h => by
      simp only [mpat] at h
      split at h
      · rename_i b1 h1
        obtain ⟨A1, B1, C1⟩ := mpat_sound syms vars psorts p s b b1 h1
        obtain ⟨A2, B2, C2⟩ := mpat_sound syms vars psorts q u b1 b' h
        refine ⟨bext_trans A1 A2, fun hb => B2 (B1 hb), fun bs hag => ?_⟩
        simp only [pinst, C1 bs (agrees_of_bext A2 hag), C2 bs hag]
      · cases h
  | PVal _, PApp _ _, _, _, h | PApp _ _, PVal _, _, _, h => by simp [mpat] at h

theorem allBound_sound : ∀ (b : Bind) (bs : List tterm), allBound b = some bs →
    agrees b bs ∧ bs.length = b.length ∧ ∀ (i : Nat) (u : tterm), bs[i]? = some u → b[i]? = some (some u)
  | [], bs, h => by
      simp only [allBound, Option.some.injEq] at h; subst h
      exact ⟨fun _ _ h => by simp at h, rfl, fun _ _ h => by simp at h⟩
  | some t :: b, bs, h => by
      simp only [allBound] at h
      split at h
      · rename_i ts hts
        cases h
        obtain ⟨A, B, C⟩ := allBound_sound b ts hts
        refine ⟨?_, by simp [B], ?_⟩
        · intro i u hi
          cases i with
          | zero => simpa using hi
          | succ i => simpa using A i u (by simpa using hi)
        · intro i u hi
          cases i with
          | zero => simpa using hi
          | succ i => simpa using C i u (by simpa using hi)
      · cases h
  | none :: _, _, h => by simp [allBound] at h

theorem mapOpt_length (f : tterm → Option tterm) : ∀ (ts us : List tterm),
    mapOpt f ts = some us → us.length = ts.length
  | [], us, h => by simp only [mapOpt, Option.some.injEq] at h; subst h; rfl
  | t :: ts, us, h => by
      simp only [mapOpt] at h
      split at h
      · rename_i t' ts' _ h2; cases h; simp [mapOpt_length f ts ts' h2]
      · cases h

section den2
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
variable {syms : List symdecl} {preds : List preddecl} (DA : DenAt GF syms preds)

/-! ## Instantiation is substitution -/

/-- `bs` evaluates at `θ` to `θb`. -/
def evs (θ : List (dyn DA)) (bs : List tterm) (θb : List (dyn DA)) : Prop :=
  List.Forall₂ (fun t d => teval DA θ t = some d) bs θb

theorem forall2_lookup {A B : Type} {R : A → B → Prop} : ∀ {l1 : List A} {l2 : List B} (n : Nat) (a : A),
    List.Forall₂ R l1 l2 → l1[n]? = some a → ∃ b, l2[n]? = some b ∧ R a b
  | [], _, _, _, _, h => by simp at h
  | _ :: _, _ :: _, 0, _, .cons h1 _, h => by simp at h; subst h; exact ⟨_, rfl, h1⟩
  | _ :: _, _ :: _, n + 1, a, .cons _ h2, h => forall2_lookup n a h2 (by simpa using h)

mutual
theorem inst_teval (θ θb : List (dyn DA)) (bs : List tterm) (H : evs DA θ bs θb) :
    ∀ (t u : tterm), inst bs t = some u → teval DA θ u = teval DA θb t
  | TVar n, u, h => by
      simp only [inst] at h
      obtain ⟨d, hd, hu⟩ := forall2_lookup n u H h
      simp only [teval, nth_error_eq, hd, hu]
  | TSym n args, u, h => by
      simp only [inst] at h
      split at h
      · rename_i args' hargs
        cases h
        simp only [teval, insts_tevals θ θb bs H args args' hargs]
      · cases h
  | TPair a b, u, h => by
      simp only [inst] at h
      split at h
      · rename_i a' b' ha hb
        cases h
        simp only [teval, inst_teval θ θb bs H a a' ha, inst_teval θ θb bs H b b' hb]
      · cases h
  | TLit ty es, u, h => by
      simp only [inst] at h
      split at h
      · rename_i ty' es' hty hes
        cases h
        simp only [teval, inst_teval θ θb bs H ty ty' hty, insts_tevals θ θb bs H es es' hes]
      · cases h
  | TUnit, u, h => by simp only [inst, Option.some.injEq] at h; subst h; rfl
theorem insts_tevals (θ θb : List (dyn DA)) (bs : List tterm) (H : evs DA θ bs θb) :
    ∀ (ts us : List tterm), insts bs ts = some us → tevals DA θ us = tevals DA θb ts
  | [], us, h => by simp only [insts, Option.some.injEq] at h; subst h; rfl
  | t :: ts, us, h => by
      simp only [insts] at h
      split at h
      · rename_i t' ts' ht hts
        cases h
        simp only [tevals, inst_teval θ θb bs H t t' ht, insts_tevals θ θb bs H ts ts' hts]
      · cases h
end

theorem pinst_den (θ θb : List (dyn DA)) (bs : List tterm) (H : evs DA θ bs θb) :
    ∀ (p s : tpat), pinst bs p = some s → pat_den DA θ s = pat_den DA θb p
  | PVal t, s, h => by
      simp only [pinst] at h
      split at h
      · rename_i u hu
        cases h
        simp only [pat_den, val_den, inst_teval DA θ θb bs H t u hu]
      · cases h
  | PApp a b, s, h => by
      simp only [pinst] at h
      split at h
      · rename_i a' b' ha hb
        cases h
        simp only [pat_den, pinst_den θ θb bs H a a' ha, pinst_den θ θb bs H b b' hb]
      · cases h

/-- The values of a binding with the right sorts form a sorted valuation. -/
theorem evs_of_sorted (θ : List (dyn DA)) (vars : List srt) (Hθ : sorted DA θ vars) :
    ∀ (bs : List tterm) (psorts : List srt), bs.length = psorts.length →
      (∀ (i : Nat) (u : tterm), bs[i]? = some u → ∃ s, psorts[i]? = some s ∧ sortOf syms vars u = some s) →
      ∃ θb, evs DA θ bs θb ∧ sorted DA θb psorts
  | [], [], _, _ => ⟨[], .nil, rfl⟩
  | u :: bs, s :: ps, hl, h => by
      obtain ⟨s', hs', hu⟩ := h 0 u rfl
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs'
      subst hs'
      obtain ⟨x, hx⟩ := sortOf_sound DA θ vars Hθ u s hu
      obtain ⟨θb, H1, H2⟩ := evs_of_sorted θ vars Hθ bs ps (by simpa using hl)
        (fun i u hi => by simpa using h (i + 1) u (by simpa using hi))
      exact ⟨⟨s, x⟩ :: θb, .cons hx H1, by simp only [sorted, List.map_cons] at *; rw [H2]⟩
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- A full binding read off a well-sorted partial one evaluates to a sorted
valuation. -/
theorem evs_of_bound (θ : List (dyn DA)) (vars psorts : List srt) (Hθ : sorted DA θ vars)
    (b : Bind) (bs : List tterm) :
    b.length = psorts.length → bwf syms vars psorts b → allBound b = some bs →
    ∃ θb, evs DA θ bs θb ∧ sorted DA θb psorts := by
  intro hl hb ha
  obtain ⟨_, hl', hbs⟩ := allBound_sound b bs ha
  exact evs_of_sorted DA θ vars Hθ bs psorts (by rw [hl', hl])
    (fun i u hi => hb i u (hbs i u hi))

theorem forall_sorts_at : ∀ (ss : List srt) (P : List (dyn DA) → Prop) (θb : List (dyn DA)),
    forall_sorts DA ss P → sorted DA θb ss → P θb
  | [], P, θb, h, hs => by
      simp only [sorted, List.map_eq_nil_iff] at hs; subst hs; exact h
  | s :: ss, P, d :: θb, h, hs => by
      obtain ⟨s', x⟩ := d
      simp only [sorted, List.map_cons, List.cons.injEq] at hs
      obtain ⟨rfl, hs⟩ := hs
      exact forall_sorts_at ss (fun θ => P (⟨s', x⟩ :: θ)) θb (h x) hs
  | _ :: _, _, [], _, hs => by simp [sorted] at hs

theorem forall_mem {A : Type} {P : A → Prop} : ∀ {l : List A} {x : A}, Forall P l → x ∈ l → P x
  | [], _, _, hx => by cases hx
  | _ :: _, _, ⟨h1, h2⟩, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h1
      · exact forall_mem h2 hx

/-! ## Normalization -/

theorem mapOpt_tevals (θ : List (dyn DA)) (f : tterm → Option tterm)
    (Hf : ∀ a a', f a = some a' → teval DA θ a' = teval DA θ a) :
    ∀ (ts us : List tterm), mapOpt f ts = some us → tevals DA θ us = tevals DA θ ts
  | [], us, h => by simp only [mapOpt, Option.some.injEq] at h; subst h; rfl
  | t :: ts, us, h => by
      simp only [mapOpt] at h
      split at h
      · rename_i t' ts' h1 h2
        cases h
        simp only [tevals, Hf t t' h1, mapOpt_tevals θ f Hf ts ts' h2]
      · cases h

theorem mapArgs_teval (θ : List (dyn DA)) (f : tterm → Option tterm)
    (Hf : ∀ a a', f a = some a' → teval DA θ a' = teval DA θ a) :
    ∀ (t u : tterm), mapArgs f t = some u → teval DA θ u = teval DA θ t
  | TSym n args, u, h => by
      simp only [mapArgs] at h
      split at h
      · rename_i args' hargs
        cases h; simp only [teval, mapOpt_tevals DA θ f Hf args args' hargs]
      · cases h
  | TPair a b, u, h => by
      simp only [mapArgs] at h
      split at h
      · rename_i a' b' ha hb
        cases h; simp only [teval, Hf a a' ha, Hf b b' hb]
      · cases h
  | TLit ty es, u, h => by
      simp only [mapArgs] at h
      split at h
      · rename_i ty' es' hty hes
        cases h; simp only [teval, Hf ty ty' hty, mapOpt_tevals DA θ f Hf es es' hes]
      · cases h
  | TVar _, u, h | TUnit, u, h => by simp only [mapArgs, Option.some.injEq] at h; subst h; rfl

theorem tryFacts_teval (θ : List (dyn DA)) (vars : List srt) (Hθ : sorted DA θ vars) :
    ∀ (fs : List tfact), Forall (fact_valid DA) fs →
      ∀ t u, tryFacts syms vars fs t = some u → teval DA θ u = teval DA θ t
  | [], _, t, u, h => by simp [tryFacts] at h
  | f :: fs, ⟨Hf, Hfs⟩, t, u, h => by
      simp only [tryFacts] at h
      split at h
      · rename_i b hb
        split at h
        · rename_i bs hbs
          split at h
          · rename_i u' hu
            cases h
            obtain ⟨A, _, C⟩ := mterm_sound syms vars f.f_vars f.f_lhs t _ b hb
            obtain ⟨Hag, _, _⟩ := allBound_sound b bs hbs
            have hl : b.length = f.f_vars.length := by
              rw [mterm_length syms vars f.f_vars f.f_lhs t _ b hb, List.length_replicate]
            obtain ⟨θb, Hev, Hs⟩ := evs_of_bound DA θ vars f.f_vars Hθ b bs hl
              ((mterm_sound syms vars f.f_vars f.f_lhs t _ b hb).2.1
                (bwf_replicate syms vars f.f_vars _)) hbs
            rw [inst_teval DA θ θb bs Hev f.f_rhs u hu, inst_teval DA θ θb bs Hev f.f_lhs t (C bs Hag)]
            exact (forall_sorts_at DA f.f_vars _ θb Hf Hs).symm
          · exact tryFacts_teval θ vars Hθ fs Hfs t u h
        · exact tryFacts_teval θ vars Hθ fs Hfs t u h
      · exact tryFacts_teval θ vars Hθ fs Hfs t u h

theorem norm_teval (θ : List (dyn DA)) (vars : List srt) (Hθ : sorted DA θ vars)
    (facts : List tfact) (Hf : Forall (fact_valid DA) facts) :
    ∀ (fuel : Nat) (t u : tterm), norm syms facts vars fuel t = some u → teval DA θ u = teval DA θ t
  | 0, _, _, h => by simp [norm] at h
  | fuel + 1, t, u, h => by
      simp only [norm] at h
      split at h
      · rename_i t2 h2
        have E2 := mapArgs_teval DA θ _ (norm_teval θ vars Hθ facts Hf fuel) t t2 h2
        split at h
        · rename_i t3 h3
          rw [norm_teval θ vars Hθ facts Hf fuel t3 u h, tryFacts_teval DA θ vars Hθ facts Hf t2 t3 h3, E2]
        · cases h; exact E2
      · cases h

end den2

end LC
end TCheck
end Perennial
