(** [wp_symex]: symbolic execution of a loop-free Goose function body by
    reflection.

    On a goal [envs_entails Δ (WP e {{ Φ }})] it

    1. reifies [e] into an [sexpr], and the typed points-to facts of the
       spatial context into an initial symbolic heap, collecting every Rocq
       word, boolean and location they mention into an environment [ρ];
    2. runs the executor [run] with [vm_compute];
    3. applies [symex_sound], checking [eden ρ se = Some e] by conversion and
       the executor's answer by a [vm_cast];
    4. frames the initial heap, and leaves one goal per path of the program:

         ∀ (fresh locations) (_ : path condition) .., cells -∗ .. -∗ Φ ret

       where the cells are those reachable from the caller's locations or
       the result (the cells Goose allocates for locals are dropped).

    The proof term is the soundness theorem applied to data; its size does
    not grow with the number of steps the program takes, unlike the proof
    [wp_auto] builds one step at a time. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.proof.symex Require Export sound.
From iris.proofmode Require Import environments coq_tactics.

(** The proof-mode form of [symex_sound]. *)
Lemma tac_symex `{hG: heapGS Σ, !ffi_semantics _ _} {sem : go.Semantics}
    (ρ : senv) (se : sexpr) (h : list scell) (r : list spath)
    Δ (e : expr) (Φ : val → iProp Σ) :
  eden ρ se = Some e →
  run se h (length (e_ls ρ)) = Some r →
  envs_entails Δ (heap_den ρ h ∗ paths_goal ρ Φ r) →
  envs_entails Δ (WP e {{ Φ }}).
Proof.
  rewrite envs_entails_unseal. intros Hd Hr HΔ. rewrite HΔ.
  exact (symex_sound ρ se e h r Φ Hd Hr).
Qed.

(** Framing the initial heap must not look inside the residual goal: the
    [Frame] instances would unfold it, and with it every path. *)
#[global] Typeclasses Opaque paths_goal.

(** * Reification

    Reifying functions return a pair of the reified term and the new
    environment. An environment is a triple [(ws, bs, ls)] of Gallina lists;
    an atom is the position of a term in its list, found up to syntactic
    equality. *)

Ltac symex_index_or_add x l :=
  lazymatch l with
  | [] => constr:((O, [x]))
  | ?y :: ?l' =>
      lazymatch constr:((x, y)) with
      | (?a, ?a) => constr:((O, l))
      | _ =>
          let r := symex_index_or_add x l' in
          lazymatch r with (?n, ?l'') => constr:((S n, y :: l'')) end
      end
  end.

(** A Gallina value of a supported type, as a symbolic value. *)
Ltac symex_reify_gval x env :=
  lazymatch env with
  | (?ws, ?bs, ?ls) =>
      let T := type of x in
      lazymatch T with
      | w64 =>
          let r := symex_index_or_add x ws in
          lazymatch r with (?n, ?ws') => constr:((VW (WAtom n), (ws', bs, ls))) end
      | bool =>
          let r := symex_index_or_add x bs in
          lazymatch r with (?n, ?bs') => constr:((VB (BAtom n), (ws, bs', ls))) end
      | loc =>
          let r := symex_index_or_add x ls in
          lazymatch r with (?n, ?ls') => constr:((VL (LAtom n), (ws, bs, ls'))) end
      | unit => constr:((VUnit, env))
      | _ => fail "wp_symex: unsupported value type" T
      end
  end.

Ltac symex_reify_loc l env :=
  lazymatch env with
  | (?ws, ?bs, ?ls) =>
      let r := symex_index_or_add l ls in
      lazymatch r with (?n, ?ls') => constr:((n, (ws, bs, ls'))) end
  end.

Ltac symex_reify_ty t :=
  lazymatch t with
  | go.int => constr:(TyInt)
  | go.int64 => constr:(TyInt64)
  | go.uint64 => constr:(TyUint64)
  | go.bool => constr:(TyBool)
  | go.untyped_bool => constr:(TyBool)
  | go.PointerType ?t' => let r := symex_reify_ty t' in constr:(TyPtr r)
  | _ => fail "wp_symex: unsupported type" t
  end.

Ltac symex_reify_binop op :=
  lazymatch op with
  | GoPlus => constr:(OPlus) | GoSub => constr:(OSub) | GoMul => constr:(OMul)
  | GoEquals => constr:(OEq) | GoLt => constr:(OLt) | GoLe => constr:(OLe)
  | GoGt => constr:(OGt) | GoGe => constr:(OGe)
  | _ => fail "wp_symex: unsupported operator" op
  end.

Ltac symex_reify_unop op :=
  lazymatch op with
  | GoNeg => constr:(ONeg) | GoNot => constr:(ONot)
  | _ => fail "wp_symex: unsupported operator" op
  end.

Ltac symex_reify_expr e env :=
  let two e1 e2 k :=
    let r1 := symex_reify_expr e1 env in
    lazymatch r1 with
    | (?s1, ?env1) =>
        let r2 := symex_reify_expr e2 env1 in
        lazymatch r2 with (?s2, ?env2) => k s1 s2 env2 end
    end in
  lazymatch e with
  | Val (into_val ?x) =>
      let r := symex_reify_gval x env in
      lazymatch r with (?v, ?env') => constr:((EVal v, env')) end
  | Var ?x => constr:((EVar x, env))
  | App (Rec BAnon (BNamed ?x) ?e2) ?e1 =>
      two e1 e2 ltac:(fun s1 s2 env' => constr:((ELet x s1 s2, env')))
  | If ?c ?e1 ?e2 =>
      let rc := symex_reify_expr c env in
      lazymatch rc with
      | (?sc, ?envc) =>
          let r1 := symex_reify_expr e1 envc in
          lazymatch r1 with
          | (?s1, ?env1) =>
              let r2 := symex_reify_expr e2 env1 in
              lazymatch r2 with (?s2, ?env2) => constr:((EIf sc s1 s2, env2)) end
          end
      end
  | App (Val (GoInstruction (GoZeroVal ?t))) (Val (into_val tt)) =>
      let st := symex_reify_ty t in constr:((EZero st, env))
  | App (Val (GoInstruction (GoAlloc ?t))) ?e1 =>
      let st := symex_reify_ty t in
      let r := symex_reify_expr e1 env in
      lazymatch r with (?s1, ?env') => constr:((EAlloc st s1, env')) end
  | App (Val (GoInstruction (GoLoad ?t))) ?e1 =>
      let st := symex_reify_ty t in
      let r := symex_reify_expr e1 env in
      lazymatch r with (?s1, ?env') => constr:((ELoad st s1, env')) end
  | App (Val (GoInstruction (GoStore ?t))) (Pair ?e1 ?e2) =>
      let st := symex_reify_ty t in
      two e1 e2 ltac:(fun s1 s2 env' => constr:((EStore st s1 s2, env')))
  | App (Val (GoInstruction (GoOp ?op ?t))) (Pair ?e1 ?e2) =>
      let sop := symex_reify_binop op in
      let st := symex_reify_ty t in
      two e1 e2 ltac:(fun s1 s2 env' => constr:((EBinOp sop st s1 s2, env')))
  | App (Val (GoInstruction (GoUnOp ?op ?t))) ?e1 =>
      let sop := symex_reify_unop op in
      let st := symex_reify_ty t in
      let r := symex_reify_expr e1 env in
      lazymatch r with (?s1, ?env') => constr:((EUnOp sop st s1, env')) end
  | App (Val (GoInstruction (Convert ?t1 ?t2))) ?e1 =>
      let st1 := symex_reify_ty t1 in
      let st2 := symex_reify_ty t2 in
      let r := symex_reify_expr e1 env in
      lazymatch r with (?s1, ?env') => constr:((EConvert st1 st2 s1, env')) end
  | App (Val do_execute) ?e1 =>
      let r := symex_reify_expr e1 env in
      lazymatch r with (?s1, ?env') => constr:((EDo s1, env')) end
  | App (Val do_return) ?e1 =>
      let r := symex_reify_expr e1 env in
      lazymatch r with (?s1, ?env') => constr:((EReturn s1, env')) end
  | App (App (Val exception_seq) (Rec BAnon BAnon ?e2)) ?e1 =>
      two e1 e2 ltac:(fun s1 s2 env' => constr:((EExcSeq s1 s2, env')))
  | App (Val exception_do) ?e1 =>
      let r := symex_reify_expr e1 env in
      lazymatch r with (?s1, ?env') => constr:((EExcDo s1, env')) end
  | _ => fail "wp_symex: unsupported expression" e
  end.

(** The initial heap: every full-ownership typed points-to in the spatial
    context (other hypotheses are skipped). *)
Ltac symex_reify_heap Γ env :=
  lazymatch Γ with
  | Enil => constr:((@nil scell, env))
  | Esnoc ?Γ' _ ?P =>
      let r := symex_reify_heap Γ' env in
      lazymatch r with
      | (?cells, ?env1) =>
          lazymatch P with
          | typed_pointsto ?l ?x (DfracOwn 1) =>
              let rl := symex_reify_loc l env1 in
              lazymatch rl with
              | (?n, ?env2) =>
                  let rv := symex_reify_gval x env2 in
                  lazymatch rv with (?v, ?env3) => constr:(((n, v) :: cells, env3)) end
              end
          | _ => r
          end
      end
  end.

(** Everything the residual goals are stated with; [cbn] with exactly this
    list turns them into ordinary Iris goals over the original Rocq terms. *)
Ltac symex_simpl_heap :=
  cbn [heap_den cell_den pts weval beval leval env_ext e_ws e_bs e_ls nth nth_error].

Ltac symex_simpl :=
  cbn [paths_goal path_goal forall_locs pc_wand heap_wand vpost heap_den cell_den pts
       vden weval beval leval bprop cmp_lt cmp_le
       env_ext e_ws e_bs e_ls s_heap s_pc s_nlocs
       nth nth_error app length Nat.sub].

(** With an empty initial heap the framed goal is [emp ∗ G]. *)
Ltac symex_drop_emp :=
  lazymatch goal with
  | |- envs_entails _ (bi_sep emp _) => iSplitR; [iEmpIntro|]
  | |- _ => idtac
  end.

(** One goal per path; the conjunction is nested to the right. *)
Ltac symex_split_paths n :=
  lazymatch n with
  | O => idtac
  | S ?m => iSplit; [|symex_split_paths m]
  end.

Ltac wp_symex :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails (Envs _ ?Γs _) (wp _ _ ?e ?Φ) =>
      let env0 := constr:((@nil w64, @nil bool, @nil loc)) in
      let rh := symex_reify_heap Γs env0 in
      lazymatch rh with
      | (?cells, ?env1) =>
          let re := symex_reify_expr e env1 in
          lazymatch re with
          | (?se, (?ws, ?bs, ?ls)) =>
              let n := eval vm_compute in (length ls) in
              let res := eval vm_compute in (run se cells n) in
              lazymatch res with
              | Some ?ps =>
                  eapply (tac_symex (mkEnv ws bs ls) se cells ps _ e Φ);
                  [ reflexivity
                  | vm_cast_no_check (@eq_refl _ (Some ps))
                  | (* frame the heap while the residual is still folded: framing
                       searches the whole goal *)
                    symex_simpl_heap; iFrame; symex_drop_emp; symex_simpl;
                    let k := eval vm_compute in (length ps - 1) in
                    symex_split_paths k ]
              | None => fail "wp_symex: the symbolic executor could not show the program safe"
              end
          end
      end
  | |- _ => fail "wp_symex: the goal is not a WP"
  end.

(** Introduce one residual goal's fresh locations and path condition (into
    the Rocq context) and its cells. *)
Ltac symex_intros := iIntros "**".
