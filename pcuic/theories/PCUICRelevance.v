(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICLiftSubst PCUICGlobalEnv.

Require Import ssreflect.

Definition wfTermRel_ctx_weak isTermRel (Σ : global_env) (Γ : mark_context) :=
  PCUICEnvTyping.All_local_env (PCUICEnvTyping.lift_term_rel_type (fun Σ Δ t _ => ∑ rel, isTermRel Σ (Γ,,,Δ) t rel) (fun Σ Δ t => isTermRel Σ (Γ,,,Δ) t Relevant) Σ).

Definition wfTermRel_mfix isTermRel (Σ: global_env) (Γ mfixcontext : mark_context) (mfix : mfixpoint term) :=
  All (fun def => isTermRel Σ (Γ ,,, mfixcontext) def.(dbody) def.(dname).(binder_relevance) × isTermRel Σ Γ def.(dtype) Relevant) mfix.

Definition wfTermRel_pred isTermRel (Σ : global_env) (Γ : mark_context) (p : predicate term) :=
  All (fun p => ∑ r, isTermRel Σ Γ p r) p.(pparams) ×
  wfTermRel_ctx_weak isTermRel Σ (List.repeat Relevant #|p.(pparams)|) p.(pcontext) ×
  isTermRel Σ (Γ ,,, marks_of_context (inst_case_predicate_context p)) p.(preturn) Relevant.

Definition wfTermRel_branch isTermRel (Σ : global_env) (Γ : mark_context) (p: predicate term) (br : branch term) :=
  wfTermRel_ctx_weak isTermRel Σ (List.repeat Relevant #|p.(pparams)|) br.(bcontext) ×
  ∑ r, isTermRel Σ (Γ ,,, marks_of_context (inst_case_branch_context p br)) br.(bbody) r.

Inductive isTermRel (Σ : global_env) (Γ : mark_context) : term -> relevance -> Type :=
  | rel_Rel n rel :
      nth_error Γ n = Some rel -> isTermRel Σ Γ (tRel n) rel

  | rel_Lambda na A t rel :
      isTermRel Σ (Γ ,, na.(binder_relevance)) t rel ->
      isTermRel Σ Γ A Relevant ->
      isTermRel Σ Γ (tLambda na A t) rel
  
  | rel_LetIn na b B t rel :
      isTermRel Σ (Γ ,, na.(binder_relevance)) t rel ->
      isTermRel Σ Γ B Relevant ->
      isTermRel Σ Γ b na.(binder_relevance) ->
      isTermRel Σ Γ (tLetIn na b B t) rel
  
  | rel_App t u rel rel' :
      isTermRel Σ Γ t rel ->
      isTermRel Σ Γ u rel' ->
      isTermRel Σ Γ (tApp t u) rel
  
  | rel_Const kn u decl :
      declared_constant Σ kn decl -> isTermRel Σ Γ (tConst kn u) decl.(cst_relevance)
  
  | rel_Construct ind i u mdecl idecl cdecl :
      declared_constructor Σ (ind, i) mdecl idecl cdecl -> isTermRel Σ Γ (tConstruct ind i u) idecl.(ind_relevance)
  
  | rel_Case ci p c r brs :
      wfTermRel_pred isTermRel Σ Γ p ->
      All (wfTermRel_branch isTermRel Σ Γ p) brs ->
      isTermRel Σ Γ c r ->
      isTermRel Σ Γ (tCase ci p c brs) ci.(ci_relevance)
  
  | rel_Proj p u rel' mdecl idecl cdecl pdecl :
      declared_projection Σ p mdecl idecl cdecl pdecl ->
      isTermRel Σ Γ u rel' ->
      isTermRel Σ Γ (tProj p u) pdecl.(proj_relevance)
  
  | rel_Fix mfix n def :
      nth_error mfix n = Some def ->
      wfTermRel_mfix isTermRel Σ Γ (marks_of_context (fix_context mfix)) mfix ->
      isTermRel Σ Γ (tFix mfix n) def.(dname).(binder_relevance)
  
  | rel_CoFix mfix n def :
      nth_error mfix n = Some def ->
      wfTermRel_mfix isTermRel Σ Γ (marks_of_context (fix_context mfix)) mfix ->
      isTermRel Σ Γ (tCoFix mfix n) def.(dname).(binder_relevance)
  
  | rel_Sort s :
      isTermRel Σ Γ (tSort s) Relevant
  
  | rel_Prod na A B :
      isTermRel Σ Γ A Relevant ->
      isTermRel Σ (Γ ,, na.(binder_relevance)) B Relevant ->
      isTermRel Σ Γ (tProd na A B) Relevant
  
  | rel_Ind ind u :
      (* declared_inductive Σ ind mdecl idecl -> *)
      isTermRel Σ Γ (tInd ind u) Relevant.

Derive Signature for isTermRel.

#[global] Hint Constructors isTermRel : pcuic.

Notation isTermRelevant := (fun Σ Γ t => isTermRel Σ Γ t Relevant).
Notation isTermIrrel := (fun Σ Γ t => isTermRel Σ Γ t Irrelevant).
Notation wfTermRel := (fun Σ Γ t => ∑ rel, isTermRel Σ Γ t rel).
Definition isTermRelOpt Σ Γ t relopt := option_default (isTermRel Σ Γ t) relopt unit.

Definition wfTermRel_ctx (Σ : global_env) :=
  PCUICEnvTyping.All_local_env (PCUICEnvTyping.lift_term_rel_type isTermRelOpt isTermRelevant Σ).

Definition wfTermRel_ctx_rel (Σ : global_env) :=
  PCUICEnvTyping.All_local_rel (PCUICEnvTyping.lift_term_rel_type isTermRelOpt isTermRelevant Σ).

Definition wfTermRel_ctx_rel' (Σ : global_env) (Γ : mark_context) :=
  PCUICEnvTyping.All_local_env (PCUICEnvTyping.lift_term_rel_type (fun Σ Δ => isTermRelOpt Σ (Γ,,,Δ)) (fun Σ Δ t => isTermRel Σ (Γ,,,Δ) t Relevant) Σ).

Lemma isTermRel_mkApps Σ Γ rel t args : isTermRel Σ Γ t rel -> All (wfTermRel Σ Γ) args -> isTermRel Σ Γ (mkApps t args) rel.
Proof.
  induction args in t |- *; cbn; auto.
  intros H Hargs.
  inv Hargs. destruct X.
  eauto with pcuic.
Qed.

#[global] Hint Resolve isTermRel_mkApps : pcuic.

Lemma isTermRel_mkApps_inv Σ Γ rel t args : isTermRel Σ Γ (mkApps t args) rel -> isTermRel Σ Γ t rel × All (wfTermRel Σ Γ) args.
Proof.
  induction args in t |- *; cbn; auto.
  intro H.
  apply IHargs in H as (H1 & H2).
  inv H1.
  split; auto.
  constructor; eauto.
Qed.

Lemma ctx_ind P : P [] -> (forall na A Γ, P Γ -> P (Γ ,, vass na A)) -> (forall na b B Γ, P Γ -> P (Γ ,, vdef na b B)) -> forall Γ, P Γ.
Proof.
  intros X Xa Xd Γ.
  induction Γ as [| [na [b|] ty] Γ ] => //; eauto.
Qed.

Lemma marks_of_context_app Γ Δ :
  marks_of_context (Γ ,,, Δ) = marks_of_context Γ ,,, marks_of_context Δ.
Proof.
  rewrite /marks_of_context !map_app //.
Qed.

Lemma mark_fold_context_k f Γ : marks_of_context (fold_context_k f Γ) = marks_of_context Γ.
Proof.
  rewrite /marks_of_context /fold_context_k map_rev map_mapi /= mapi_cst_map map_rev rev_involutive //.
Qed.

Lemma marks_of_context_univ_subst Γ u : marks_of_context Γ@[u] = marks_of_context Γ.
Proof.
  rewrite /subst_instance /subst_instance_context /map_context /marks_of_context map_map /map_decl //.
Qed.

Lemma mark_inst_case_context params puinst (pctx : context) :
  marks_of_context (inst_case_context params puinst pctx) = marks_of_context pctx.
Proof.
  unfold inst_case_context, subst_context.
  rewrite mark_fold_context_k marks_of_context_univ_subst //.
Qed.

Lemma mark_inst_case_predicate_context p :
  marks_of_context (inst_case_predicate_context p) = marks_of_context p.(pcontext).
Proof. apply mark_inst_case_context. Qed.

Lemma mark_inst_case_branch_context p br :
  marks_of_context (inst_case_branch_context p br) = marks_of_context br.(bcontext).
Proof. apply mark_inst_case_context. Qed.

Lemma mark_fix_context f g mfix :
  marks_of_context (fix_context (map (map_def f g) mfix)) = marks_of_context (fix_context mfix).
Proof.
  rewrite /fix_context /marks_of_context !mapi_map !map_rev !map_mapi //.
Qed.

Lemma isTermRel_inj Σ Γ t r r' : isTermRel Σ Γ t r -> isTermRel Σ Γ t r' -> r = r'.
Proof.
  induction 1 in r' |- *; intro H; inv H.
  all: try congruence.
  all: eauto.
  - eapply declared_constructor_inj in d as (_ & -> & _); eauto.
  - eapply declared_projection_inj in d as (_ & _ & _ & <-); eauto.
Qed.

Lemma wfTermRel_ctx_rel'_rel Σ Γ Δ : wfTermRel_ctx_rel' Σ (marks_of_context Γ) Δ -> wfTermRel_ctx_rel Σ Γ Δ.
Proof.
  induction 1 as [ |????? H|?????? H]; constructor; auto.
  - destruct H; split; rewrite marks_of_context_app //.
  - destruct H; split; rewrite marks_of_context_app //.
Qed.
