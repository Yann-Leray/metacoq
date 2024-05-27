(* Distributed under the terms of the MIT license. *)
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config BasicAst Universes Environment Primitive.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICLiftSubst PCUICGlobalEnv PCUICEquality PCUICTyping.
Import PCUICEnvTyping.
Require Import ssreflect.

Definition lift_rel isTermRel (t : term) relopt := ∑ rel : relevance, isTermRel t rel × option_default (fun r => r = rel) relopt True.

Definition lift_term_rel_type isTermRel (j : judgment) := option_default (fun t => lift_rel isTermRel t (j_rel j)) (j_term j) (unit : Type) × (isTermRel (j_typ j) Relevant).

Inductive ctx_inst_rel isTermRel | : list term -> context -> Type :=
| ctx_inst_rel_nil : ctx_inst_rel [] []
| ctx_inst_rel_ass t na T inst Γ :
    isTermRel t na.(binder_relevance) ->
    ctx_inst_rel inst (subst_telescope [t] 0 Γ) ->
    ctx_inst_rel (t :: inst) (Γ ,, vass na T)
| ctx_inst_rel_def na b T inst Γ :
    ctx_inst_rel inst (subst_telescope [b] 0 Γ) ->
    ctx_inst_rel inst (Γ ,, vdef na b T).

Definition wfTermRel_ctx isTermRel (Γ : mark_context) :=
  All_local_env (fun Δ j => lift_term_rel_type (isTermRel (Γ,,, marks_of_context Δ)) j).

Definition wfTermRel_mfix isTermRel (Σ: global_env) (Γ mfixcontext : mark_context) (mfix : mfixpoint term) :=
  All (fun def => isTermRel Σ (Γ ,,, mfixcontext) def.(dbody) def.(dname).(binder_relevance) × isTermRel Σ Γ def.(dtype) rel_of_Type) mfix.

Definition wfTermRel_pred isTermRel (ind : inductive) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (Γ : mark_context) (p : predicate term) :=
  ctx_inst_rel (isTermRel Γ) p.(pparams) (List.rev mdecl.(ind_params)@[p.(puinst)]) ×
  eq_context_upto_names p.(pcontext) (ind_predicate_context ind mdecl idecl) ×
  isTermRel (Γ ,,, marks_of_context (case_predicate_context ind mdecl idecl p)) p.(preturn) rel_of_Type.
Locate inductive.
Definition wfTermRel_branch isTermRel (ind : inductive) (mdecl : mutual_inductive_body) (cdecl : constructor_body) (Γ : mark_context) (p: predicate term) (br : branch term) (r : relevance) :=
  eq_context_upto_names br.(bcontext) (cstr_branch_context ind mdecl cdecl) ×
  isTermRel (Γ ,,, marks_of_context (case_branch_context ind mdecl p (forget_types br.(bcontext)) cdecl)) br.(bbody) r.


Lemma eq_context_upto_names_inst_case_context_predicate_eq_annot ind mdecl idecl pctx :
  eq_context_upto_names pctx (ind_predicate_context ind mdecl idecl) ->
  eq_annots (forget_types pctx) (idecl_binder idecl :: idecl.(ind_indices)).
Proof.
  intro Hc.
  apply PCUICEquality.eq_context_upto_names_binder_annot in Hc.
  unfold ind_predicate_context in Hc.
  apply Forall2_map in Hc. cbn in Hc. change (map decl_name) with (forget_types (term := term)) in Hc.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context in Hc.
  rewrite !forget_types_fold_context_k in Hc.
  apply Forall2_map_inv, Hc.
Qed.

Lemma eq_context_upto_names_inst_case_branch_predicate_eq_annot ind mdecl cdecl bctx :
  eq_context_upto_names bctx (cstr_branch_context ind mdecl cdecl) ->
  eq_annots (forget_types bctx) cdecl.(cstr_args).
Proof.
  intro Hc.
  apply PCUICEquality.eq_context_upto_names_binder_annot in Hc.
  unfold ind_predicate_context in Hc.
  apply Forall2_map in Hc. cbn in Hc. change (map decl_name) with (forget_types (term := term)) in Hc.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context in Hc.
  rewrite !forget_types_fold_context_k in Hc.
  apply Forall2_map_inv, Hc.
Qed.


Lemma wfTermRel_pred_wf_predicate {cf : checker_flags} Σ (wfΣ : wf Σ) isTermRel ind mdecl idecl Γ p :
  declared_minductive Σ ind.(inductive_mind) mdecl ->
  wfTermRel_pred isTermRel ind mdecl idecl Γ p ->
  wf_predicate mdecl idecl p.
Proof.
  intros isdecl (Hp & Hc & Hr).
  split.
  - match type of Hp with context[?Δ] =>
    replace (ind_npars _) with (context_assumptions Δ) end.
    2: {
      rewrite (declared_minductive_ind_npars isdecl) context_assumptions_rev context_assumptions_map //.
    }
    induction Hp; cbn; eauto.
    all: rewrite /subst_telescope context_assumptions_mapi in IHHp; congruence.
  - now eapply eq_context_upto_names_inst_case_context_predicate_eq_annot.
Qed.

Lemma wfTermRel_pred_wf_branch isTermRel ind mdecl cdecl Γ p br ps :
  wfTermRel_branch isTermRel ind mdecl cdecl Γ p br ps ->
  wf_branch cdecl br.
Proof.
  intros (Hc & Hr).
  now eapply eq_context_upto_names_inst_case_branch_predicate_eq_annot.
Qed.

Variant primitive_relevance (P : term -> relevance -> Type) : prim_val -> relevance -> Type :=
| prim_int_rel i : primitive_relevance P (primInt; primIntModel i) rel_of_Type
| prim_float_hyps f : primitive_relevance P (primFloat; primFloatModel f) rel_of_Type
| prim_array_hyps a r
  (hty : P a.(array_type) rel_of_Type)
  (hdef : P a.(array_default) r)
  (hvalue : All (fun x => P x r) a.(array_value)) :
  primitive_relevance P (primArray; primArrayModel a) r.
Derive Signature for primitive_relevance.

Inductive isTermRel (Σ : global_env) (Γ : mark_context) : term -> relevance -> Type :=
  | rel_Rel n rel :
      nth_error Γ n = Some rel -> isTermRel Σ Γ (tRel n) rel

  | rel_Lambda na A t rel :
      isTermRel Σ Γ A rel_of_Type ->
      isTermRel Σ (Γ ,, na.(binder_relevance)) t rel ->
      isTermRel Σ Γ (tLambda na A t) rel

  | rel_LetIn na b B t rel :
      isTermRel Σ Γ b na.(binder_relevance) ->
      isTermRel Σ Γ B rel_of_Type ->
      isTermRel Σ (Γ ,, na.(binder_relevance)) t rel ->
      isTermRel Σ Γ (tLetIn na b B t) rel

  | rel_App t u rel rel' :
      isTermRel Σ Γ t rel ->
      isTermRel Σ Γ u rel' ->
      isTermRel Σ Γ (tApp t u) rel

  | rel_Const kn u decl :
      declared_constant Σ kn decl -> isTermRel Σ Γ (tConst kn u) decl.(cst_relevance)

  | rel_Construct ind i u mdecl idecl cdecl :
      declared_constructor Σ (ind, i) mdecl idecl cdecl -> isTermRel Σ Γ (tConstruct ind i u) idecl.(ind_relevance)

  | rel_Case mdecl idecl ci p c brs :
      declared_inductive Σ ci.(ci_ind) mdecl idecl ->
      wfTermRel_pred (isTermRel Σ) ci mdecl idecl Γ p ->
      All2 (fun cdecl br => wfTermRel_branch (isTermRel Σ) ci mdecl cdecl Γ p br ci.(ci_relevance)) idecl.(ind_ctors) brs ->
      isTermRel Σ Γ c idecl.(ind_relevance) ->
      isTermRel Σ Γ (tCase ci p c brs) ci.(ci_relevance)

  | rel_Proj p u mdecl idecl cdecl pdecl :
      declared_projection Σ p mdecl idecl cdecl pdecl ->
      isTermRel Σ Γ u idecl.(ind_relevance) ->
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
      isTermRel Σ Γ (tSort s) rel_of_Type

  | rel_Prod na A B :
      isTermRel Σ Γ A rel_of_Type ->
      isTermRel Σ (Γ ,, na.(binder_relevance)) B rel_of_Type ->
      isTermRel Σ Γ (tProd na A B) rel_of_Type

  | rel_Ind ind u :
      (* declared_inductive Σ ind mdecl idecl -> *)
      isTermRel Σ Γ (tInd ind u) rel_of_Type

  | rel_Prim p r :
      primitive_relevance (isTermRel Σ Γ) p r ->
      isTermRel Σ Γ (tPrim p) r.

Derive Signature for isTermRel.

#[global] Hint Constructors isTermRel : pcuic.

Notation isTermRelevant := (fun Σ Γ t => isTermRel Σ Γ t Relevant).
Notation isTermIrrel := (fun Σ Γ t => isTermRel Σ Γ t Irrelevant).
Notation wfTermRel := (fun Σ Γ t => ∑ rel, isTermRel Σ Γ t rel).
Definition isTermRelOpt Σ Γ t relopt := option_default (isTermRel Σ Γ t) relopt unit.

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

Lemma marks_of_context_length Γ :
  #|marks_of_context Γ| = #|Γ|.
Proof.
  rewrite /marks_of_context map_length //.
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

Lemma mark_set_binder_name nas Γ :
  #|nas| = #|Γ| ->
  marks_of_context (map2 set_binder_name nas Γ) = map binder_relevance nas.
Proof. intro H. rewrite /marks_of_context map_map2 /= -map_map2 map2_snd firstn_ge //. lia. Qed.

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

Lemma mark_case_predicate_context ind mdecl idecl p :
  #|pcontext p| = S #|ind_indices idecl| ->
  marks_of_context (case_predicate_context ind mdecl idecl p) = marks_of_context p.(pcontext).
Proof. intro H. rewrite mark_set_binder_name ?map_map //. rewrite map_length inst_case_context_length ind_predicate_context_length //. Qed.

Lemma mark_case_branch_context ind mdecl cdecl p bctx :
  #|bctx| = #|cstr_args cdecl| ->
  marks_of_context (case_branch_context ind mdecl p (forget_types bctx) cdecl) = marks_of_context bctx.
Proof. intro H. rewrite mark_set_binder_name ?map_map //. rewrite map_length inst_case_context_length cstr_branch_context_length //. Qed.

Lemma mark_fix_context f g mfix :
  marks_of_context (fix_context (map (map_def f g) mfix)) = marks_of_context (fix_context mfix).
Proof.
  rewrite /fix_context /marks_of_context !mapi_map !map_rev !map_mapi //.
Qed.

Lemma isTermRel_inj {cf : checker_flags} Σ {wfΣ : wf Σ} Γ t r r' : isTermRel Σ Γ t r -> isTermRel Σ Γ t r' -> r = r'.
Proof.
  revert Γ t r r'.
  fix f 2.
  intros Γ t r r' H H'; destruct t; inv H; inv H'.
  all: try congruence.
  all: eauto.
  - unshelve epose proof (X1 := declared_constant_to_gen H); eauto.
    unshelve epose proof (X2 := declared_constant_to_gen H0); eauto.
    eapply declared_constant_inj in X1 as <-; eauto.
  - unshelve epose proof (X1 := declared_constructor_to_gen H); eauto.
    unshelve epose proof (X2 := declared_constructor_to_gen H0); eauto.
    eapply declared_constructor_inj in X1 as (_ & -> & _); eauto.
  - unshelve epose proof (X1 := declared_projection_to_gen H); eauto.
    unshelve epose proof (X2 := declared_projection_to_gen H0); eauto.
    eapply declared_projection_inj in X1 as (_ & _ & _ & <-); eauto.
  - destruct prim as (? & []); inv X; inv X0; eauto.
Qed.
