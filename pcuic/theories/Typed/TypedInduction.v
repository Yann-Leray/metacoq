(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect Program Lia BinPos Arith.Compare_dec Bool.
From MetaCoq.Utils Require Import utils LibHypsNaming.
From MetaCoq.PCUIC Require Import TypedAst TypedAstUtils.
From Coq Require Import List.
From Equations Require Import Equations.
From Equations.Prop Require Import Subterm.

Set Asymmetric Patterns.
Import PCUICEnvTyping.

(** Derive the well-founded subterm relation for terms. Not so useful
  yet as it doesn't go throught lists.
  *)
(* Derive Subterm for term. *)

(** * Deriving a compact induction principle for terms

  Allows to get the right induction principle on lists of terms appearing
  in the term syntax (in evar, applications, branches of cases and (co-)fixpoints. *)

(** Custom induction principle on syntax, dealing with the various lists appearing in terms. *)

Local Notation "[( H : T )] -> U" :=
  (forall H : T, U)
  (at level 0, T at next level, U at level 200, H ident, only parsing) : type_scope.
Local Notation "[( H x1 .. xn  : T )] -> U" :=
  (forall H : (forall x1, .. (forall xn, T) .. ), U)
  (at level 0, T at next level, U at level 200, H ident, x1 closed binder, xn closed binder, only parsing) : type_scope.

Lemma term_forall_list_ind P :
  [(XRel n ty s : P ty -> P (tRel n ty s))] ->
  [(XVar i ty s : P ty -> P (tVar i ty s))] ->
  [(XEvar n inst ty s : All P inst -> P ty -> P (tEvar n inst ty s))] ->
  [(XSort s : P (tSort s))] ->
  [(XProd na A s B s' : P A -> P B -> P (tProd na A s B s'))] ->
  [(XLambda na A s t B s' : P A -> P t -> P B -> P (tLambda na A s t B s'))] ->
  [(XLetIn na b B s t ty s' : P b -> P B -> P t -> P ty -> P (tLetIn na b B s t ty s'))] ->
  [(XApp na A s B s' t u : P A -> P B -> P t -> P u -> P (tApp na A s B s' t u))] ->
  [(XRef ref ui args : All P args -> P (tRef ref ui args))] ->
  [(XCase ind p c brs : tCasePredProp P P p -> P c -> tCaseBrsProp P brs -> P (tCase ind p c brs))] ->
  [(XProj pr c : P c -> P (tProj pr c))] ->
  [(XFix mfix idx : tFixProp P P mfix -> P (tFix mfix idx))] ->
  [(XCoFix mfix idx : tFixProp P P mfix -> P (tCoFix mfix idx))] ->
  [(XPrim prim : tPrimProp P prim -> P (tPrim prim))] ->
  [(XCast c ty s : P c -> P ty -> P (tCast c ty s))] ->
  forall t : term, P t.
Proof.
  intros. revert t.
  fix rec 1. move rec at top.
  destruct t; match goal with
                 H : _ |- _ => apply H
              end; auto.
  all: try now apply All_refl.
  - repeat split; auto.
    + now apply All_refl.
    + now apply All_refl.
  - destruct prim, p; cbn; intuition auto.
    now apply All_refl.
Defined.

(* Definition on_local_decl (P : context -> term -> Type) := lift_wf_term1 P.

Definition CasePredProp (P : context -> term -> Type) Γ (p : predicate term) :=
  All (P Γ) p.(pparams) × P (Γ ,,, inst_case_context p.(pparams) p.(puinst) p.(pcontext)) p.(preturn).

Definition CaseBrsProp p P Γ (brs : list (branch term)) :=
  All (fun x : branch term => onctx_rel P Γ (bcontext x) * P (Γ ,,, inst_case_context p.(pparams) p.(puinst)
    x.(bcontext)) (bbody x)) brs.

Lemma term_forall_ctx_list_ind :
  forall (P : context -> term -> Type),
    (forall Γ (n : nat), P Γ (tRel n)) ->
    (forall Γ (i : ident), P Γ (tVar i)) ->
    (forall Γ (n : nat) (l : list term), All (P Γ) l -> P Γ (tEvar n l)) ->
    (forall Γ s, P Γ (tSort s)) ->
    (forall Γ (n : aname) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tProd n t t0)) ->
    (forall Γ (n : aname) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tLambda n t t0)) ->
    (forall Γ (n : aname) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall t1 : term, P (vdef n t t0 :: Γ) t1 -> P Γ (tLetIn n t t0 t1)) ->
    (forall Γ (t u : term), P Γ t -> P Γ u -> P Γ (tApp t u)) ->
    (forall Γ s (u : list Level.t), P Γ (tConst s u)) ->
    (forall Γ (i : inductive) (u : list Level.t), P Γ (tInd i u)) ->
    (forall Γ (i : inductive) (n : nat) (u : list Level.t), P Γ (tConstruct i n u)) ->
    (forall Γ (ci : case_info) (p : predicate term) (t : term) (brs : list (branch term)),
        CasePredProp P Γ p ->
        P Γ t ->
        CaseBrsProp p P Γ brs ->
        P Γ (tCase ci p t brs)) ->
    (forall Γ (s : projection) (t : term), P Γ t -> P Γ (tProj s t)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tFix m n)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tCoFix m n)) ->
    (forall Γ p, tPrimProp (P Γ) p -> P Γ (tPrim p)) ->
    (forall Γ c ty, P Γ c -> P Γ ty -> P Γ (tCast c ty)) ->
    forall Γ (t : term), P Γ t.
Proof.
  intros ?????????????????? Γ t.
  revert Γ t. set(foo:=CoreTactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (MR lt size); unfold MR in *; simpl. clear H1.
  assert (auxl : forall Γ {A} (l : list A) (f : A -> term),
    list_size (fun x => size (f x)) l < size pr0 ->
    All (fun x => P Γ (f x)) l).
  { induction l; try solve [constructor].
    move=> f /= Hsize.
    constructor.
    * eapply aux => //. red. lia.
    * apply IHl => //. lia. }
  assert (forall mfix, context_size size (fix_context mfix) <= mfixpoint_size size mfix).
  { induction mfix. simpl. auto. simpl. unfold fix_context.
    unfold context_size.
    rewrite list_size_rev /=. cbn.
    rewrite size_lift. unfold context_size in IHmfix.
    epose (list_size_mapi_rec_le (def_size size) (decl_size size) mfix
                                 (fun (i : nat) (d : def term) => vass (dname d) ((lift0 i) (dtype d))) 1).
    forward l. intros. destruct x; cbn; rewrite size_lift. lia.
    unfold def_size, mfixpoint_size. lia. }
  assert (auxΓ : forall Γ Δ,
             context_size size Δ < size pr0 ->
             onctx_rel P Γ Δ).
  { move=> Γ Δ.
    induction Δ; cbn.
    - constructor.
    - case: a => [na [b|] ty] /=;
      rewrite {1}/decl_size /context_size /= => Hlt; constructor; auto.
      + eapply IHΔ => //. unfold context_size. lia.
      + split.
        * apply aux => //. red. lia.
        * apply aux => //. cbn. lia.
      + apply IHΔ => //; unfold context_size; lia.
      + split => //. apply aux => //. cbn. lia. }
  assert (forall m, list_size (fun x : def term => size (dtype x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }
  assert (forall m, list_size (fun x : def term => size (dbody x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }

  move aux at top. move auxl at top. move auxΓ at top.

  destruct pr0; eauto;
    (move: pr2=> /= /and3P [pr20 pr21 pr22] || move: pr2 => /= /andP [pr20 pr21] || idtac);
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); auto; red; simpl; try lia]
        end.

  - eapply X10; eauto.
    * red. split.
      + eapply auxl; auto. simpl. unfold predicate_size, branch_size.
        now change (fun x => size x) with size; lia.
      + split.
        ++ apply auxΓ. simpl. unfold predicate_size. lia.
        ++ eapply aux; auto. simpl. unfold predicate_size. lia.
    * eapply aux => //. simpl; lia.
    * red. simpl in aux.
      have auxbr := fun Γ t (H : size t <= list_size (branch_size size) brs) =>
        aux Γ t ltac:(lia).
      move: auxbr.
      clear -auxΓ.
      induction brs. simpl. constructor.
      constructor. simpl in auxbr.
      + split. eapply auxΓ. simpl. unfold branch_size. lia.
        eapply auxbr. unfold branch_size. lia.
      + eapply IHbrs. intros. apply auxΓ. simpl in *. lia.
        intros. apply auxbr. simpl. lia.
  - eapply X12; try (apply aux; red; simpl; lia).
    apply auxΓ => //. simpl. specialize (H mfix). lia.
    red. apply All_pair. split; apply auxl; simpl; auto.

  - eapply X13; try (apply aux; red; simpl; lia).
    apply auxΓ => //. simpl. specialize (H mfix). lia.
    red. apply All_pair. split; apply auxl; simpl; auto.

  - eapply X14.
    destruct prim. destruct p; cbn; intuition auto; destruct a; cbn in *.
    * eapply aux. cbn. lia.
    * eapply aux. cbn. lia.
    * eapply (auxl _ _ array_value id). unfold id.
      change (fun x => size x) with size. lia.
Defined. *)
