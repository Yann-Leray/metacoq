(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst
  PCUICRelevance PCUICTyping PCUICReduction PCUICCumulativity
  PCUICEquality PCUICGlobalEnv PCUICClosed PCUICClosedConv PCUICClosedTyp PCUICEquality PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
  PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv PCUICWeakeningConv PCUICWeakeningTyp PCUICInstDef PCUICInstConv
  PCUICGuardCondition PCUICUnivSubstitutionConv PCUICOnFreeVars PCUICOnFreeVarsConv PCUICClosedTyp PCUICClosedTyp.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.
Set Keyed Unification.
Set Default Goal Selector "!".
Implicit Types cf : checker_flags.

(** * Type preservation for σ-calculus instantiation *)

Open Scope sigma_scope.

Definition well_subst_usubst {cf} (Σ:global_env_ext) (wfΣ : wf Σ) Γ σ Δ :
  is_closed_context Δ ->
  Σ ;;; Δ ⊢ σ : Γ ->
  usubst Γ σ Δ.
Proof.
  intuition eauto with *.
Defined.

Definition well_subst_closed_subst {cf} (Σ:global_env_ext) (wfΣ : wf Σ) Γ σ Δ :
  is_closed_context Δ ->
  Σ ;;; Δ ⊢ σ : Γ ->
  closed_subst Γ σ Δ.
Proof.
  intros hΔ (typed_σ & wfσ & hσ). repeat split; tea.
  intros x decl hnth. specialize (typed_σ x decl hnth) as htype.
  pose proof (typing_wf_local htype). pose (wf_local_closed_context X).
  apply closedn_on_free_vars. eapply subject_closed; eauto.
Defined.

Lemma inst_cumulSpec {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {pb Γ Δ σ A B} :
  closed_subst Γ σ Δ ->
  is_closed_context Γ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  Σ ;;; Γ ⊢ A ≤s[pb] B ->
  Σ ;;; Δ ⊢ A.[σ] ≤s[pb] B.[σ].
Proof.
  intros hσ HΓ HA HB e.
  revert pb Γ A B e Δ σ hσ HΓ HA HB e.
  induction 1; intros.
  all: inv_on_free_vars.
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  all: repeat match goal with
         | [ H : All2_dep _ _ |- _ ] => apply All2_undep in H
         end.
  - rewrite subst10_inst. sigma. solve [econstructor].
  - rewrite subst10_inst. sigma. solve [econstructor].
  - destruct (nth_error Γ i) eqn:hnth; noconf pf.
    destruct hσ as [_ [_ hσ]]. specialize (hσ _ _ hnth) as IH.
    specialize IH with (1:=H) as [(x' & decl' & hi & hnth' & eqbod) | eqr].
    * rewrite /= hi. sigma.
      destruct (decl_body decl') eqn:hdecl => //. noconf eqbod.
      let H1 := match goal with H : rename _ _ = _ |- _ => H end in
      rewrite -H1. sigma.
      relativize (t.[_]); [eapply cumul_rel|].
      { now rewrite hnth' /= hdecl. }
      rewrite lift0_inst. now sigma.
    * rewrite /= eqr. sigma. reflexivity.
  - cbn. rewrite inst_mkApps. simpl.
    rewrite inst_iota_red //.
    * rewrite skipn_length; lia.
    * eapply nth_error_forallb in Hbrs; tea. simpl in Hbrs.
      move/andP: Hbrs => [] clbctx clbod.
      rewrite closedn_ctx_on_free_vars.
      now rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
    * eapply cumul_iota.
      + rewrite nth_error_map Hbrs /= //.
      + simpl. now len.
  - rewrite 2!inst_mkApps. simpl.
    eapply cumul_fix.
    + eapply inst_unfold_fix. eassumption.
    + eapply is_constructor_inst. assumption.
  - simpl. rewrite !inst_mkApps. simpl.
    eapply cumul_cofix_case.
    eapply inst_unfold_cofix. eassumption.
  - simpl. rewrite 2!inst_mkApps. simpl.
    eapply cumul_cofix_proj.
    eapply inst_unfold_cofix. eassumption.
  - simpl.
    rewrite inst_closed0.
    * rewrite closedn_subst_instance.
      eapply declared_constant_closed_body. all: eauto.
    * eapply cumul_delta; eauto.
  - simpl. rewrite inst_mkApps. simpl.
    eapply cumul_proj; rewrite nth_error_map. rewrite Hargs. reflexivity.
  - rewrite closedP_on_free_vars in clu.
    eapply cumul_Trans; try apply IHe1; try apply IHe2; eauto.
    + rewrite closedn_ctx_on_free_vars //. apply hσ.
    + rewrite closedP_on_free_vars. eapply inst_is_open_term; eauto.
  - eapply cumul_Sym; eauto.
  - eapply cumul_Refl; eauto.
  - cbn. eapply cumul_Evar.
    solve_all.
  - eapply cumul_App; try apply IHe1; try apply IHe2; eauto.
  - cbn; eapply cumul_Lambda; try apply IHe1; try apply IHe2; eauto.
    * apply closed_subst_up_vass; eauto. eapply inst_is_open_term; eauto.
    * now apply on_free_vars_ctx_snoc_ass.
    * rewrite shiftnP_S //.
    * rewrite shiftnP_S //.
  - cbn; eapply cumul_Prod; try apply IHe1; try apply IHe2; eauto.
    * apply closed_subst_up_vass; eauto. eapply inst_is_open_term; eauto.
    * now apply on_free_vars_ctx_snoc_ass.
    * rewrite shiftnP_S //.
    * rewrite shiftnP_S //.
  - cbn; eapply cumul_LetIn; try apply IHe1; try apply IHe2; eauto; try apply IHe3; eauto.
    * apply closed_subst_up_vdef; eauto. all: eapply inst_is_open_term; eauto.
    * now apply on_free_vars_ctx_snoc_def.
    * rewrite shiftnP_S //.
    * rewrite shiftnP_S //.
  - destruct Hp as (Hp & Hu & Hc & Hr).
    destruct X as (Xp & Xu & Xc & Xr).
    rewrite -!(All2_length Xp) -?(All2_length Xc) in p1, p2, p4.
    cbn. eapply cumul_Case.
    * unfold cumul_predicate in *.
      repeat split; eauto.
      + eapply All2_map. solve_all.
      + cbn.
        rewrite -(All2_length Hc) inst_case_predicate_context_inst //.
        { rewrite closedn_ctx_on_free_vars //. }
        eapply Xr; tea.
        all: len; rewrite -?shiftnP_add //.
        -- erewrite <-inst_case_context_length.
          apply closed_subst_app_up; tas.
          rewrite -inst_case_predicate_context_inst; eauto.
          { rewrite closedn_ctx_on_free_vars //. }
          eapply PCUICOnFreeVars.on_free_vars_ctx_inst_case_context; trea.
          { solve_all. eapply inst_is_open_term; eauto. }
          len.
        -- apply on_free_vars_ctx_inst_case_context; eauto.
    * eauto.
    * unfold cumul_branches, cumul_branch in *.
      clear Hp Xp.
      solve_all; inv_on_free_vars.
      rewrite -(All2_length a1) inst_case_branch_context_inst // in H2 |- *.
      { rewrite closedn_ctx_on_free_vars //. }
      eapply b1; tea.
      all: len; rewrite -?shiftnP_add //.
      + erewrite <-inst_case_context_length.
        apply closed_subst_app_up; tas.
        rewrite -inst_case_branch_context_inst; eauto.
        { rewrite closedn_ctx_on_free_vars //. }
        eapply PCUICOnFreeVars.on_free_vars_ctx_inst_case_context; trea.
        { solve_all. eapply inst_is_open_term; eauto. }
        len.
      + apply on_free_vars_ctx_inst_case_context; eauto.
        now eapply All_forallb.
  - eapply cumul_Proj; eauto.
  - cbn. rewrite -(All2_length X).
    eapply cumul_Fix.
    unfold cumul_mfixpoint in *.
    have clmfix : is_closed_context (Γ ,,, fix_context mfix).
    { rewrite on_free_vars_ctx_app HΓ /=. now apply on_free_vars_fix_context. }
    have clmfix' : on_free_vars_ctx (shiftnP #|Δ| xpred0) (inst_context σ (fix_context mfix)).
    { rewrite -inst_fix_context. apply on_free_vars_fix_context.
      unfold test_def in *; solve_all.
      - eapply inst_is_open_term; now eauto.
      - rewrite -fix_context_length -up_Upn. eapply usubst_on_free_vars_shift; eauto. rewrite fix_context_length //. }
    rewrite -(All2_length H) inst_fix_context_up -fix_context_length in HA, HB |- *.
    set Ξ := fix_context _ in H, X, HA, HB, clmfix, clmfix' |- *. clearbody Ξ.
    solve_all.
    all: unfold test_def in *; rtoProp.
    1: now eapply a.
    eapply b2; len; rewrite -?shiftnP_add; eauto.
    now apply closed_subst_app_up.
  - cbn. rewrite -(All2_length X).
    eapply cumul_CoFix.
    unfold cumul_mfixpoint in *.
    have clmfix : is_closed_context (Γ ,,, fix_context mfix).
    { rewrite on_free_vars_ctx_app HΓ /=. now apply on_free_vars_fix_context. }
    have clmfix' : on_free_vars_ctx (shiftnP #|Δ| xpred0) (inst_context σ (fix_context mfix)).
    { rewrite -inst_fix_context. apply on_free_vars_fix_context.
      unfold test_def in *; solve_all.
      - eapply inst_is_open_term; now eauto.
      - rewrite -fix_context_length -up_Upn. eapply usubst_on_free_vars_shift; eauto. rewrite fix_context_length //. }
    rewrite -(All2_length H) inst_fix_context_up -fix_context_length in HA, HB |- *.
    set Ξ := fix_context _ in H, X, HA, HB, clmfix, clmfix' |- *. clearbody Ξ.
    solve_all.
    all: unfold test_def in *; rtoProp.
    1: now eapply a.
    eapply b2; len; rewrite -?shiftnP_add; eauto.
    now apply closed_subst_app_up.
  - cbn. eapply cumul_Prim. depelim X; cbn in HA, HB; rtoProp; constructor; cbn; eauto. solve_all.
  - cbn. repeat rewrite inst_mkApps. eapply cumul_Ind.
     * repeat rewrite map_length; eauto.
     * repeat toAll.
       eapply All2_impl. 1: tea. cbn; intros.
       destruct_head'_prod.
       eauto.
  - cbn. repeat rewrite inst_mkApps. eapply cumul_Construct.
     * repeat rewrite map_length; eauto.
     * repeat toAll.
       eapply All2_impl. 1: tea. cbn; intros.
       destruct_head'_prod.
       eauto.
  - eapply cumul_Sort; eauto.
  - eapply cumul_Const; eauto.
Defined.

Lemma inst_convSpec {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ σ A B} :
  closed_subst Γ σ Δ ->
  is_closed_context Γ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  Σ ;;; Γ |- A =s B ->
  Σ ;;; Δ |- A.[σ] =s B.[σ].
Proof.
  apply inst_cumulSpec.
Qed.

Lemma inst_prim_type σ p pty : (prim_type p pty).[σ] = prim_type (map_prim (inst σ) p) pty.
Proof.
  destruct p as [? []] => //.
Qed.

Lemma inst_isTermRel {cf} {Σ} {wfΣ : wf Σ} Γ Δ t rel σ :
  valid_subst Σ Γ σ Δ ->
  isTermRel Σ Γ t rel ->
  isTermRel Σ Δ t.[σ] rel.
Proof.
  intros hσ h.
  induction t using term_forall_list_ind in rel, σ, Γ, Δ, hσ, h |- *; cbn; depelim h.
  all: try solve [ try rewrite H; econstructor => //; eauto ].
  - now apply hσ in e.
  - constructor; [eapply IHt1|eapply IHt2]; eauto.
    now apply valid_subst_up.
  - constructor; [eapply IHt1|eapply IHt2]; eauto.
    now apply valid_subst_up.
  - constructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
    now apply valid_subst_up.

  - eapply wfTermRel_pred_wf_predicate in w as wfp; tea. 2: apply d.
    destruct X as (Xp & Xc & Xr). destruct w as (wp & wc & wr).
    econstructor; tea. 3: now eauto.
    1: repeat split.
    + rewrite /= /id.
      rewrite -[subst_instance _ _](inst_closedn_ctx σ 0).
      { pose proof (declared_minductive_closed (proj1 d)) as []%andb_and.
        now rewrite closedn_subst_instance_context. }
      rewrite inst_context_telescope.
      rewrite inst_telescope_upn0.
      clear -wp Xp hσ.
      induction wp in Xp |- *.
      1: constructor.
      all: rewrite inst_telescope_cons /=.
      * depelim Xp; constructor; eauto.
        rewrite -(inst_subst_telescope _ [t]). now apply IHwp.
      * constructor.
        rewrite -(inst_subst_telescope _ [b]). now apply IHwp.
    + now cbn.
    + eapply Xr; tea.
      apply wf_predicate_length_pcontext in wfp.
      rewrite /= !mark_case_predicate_context //=.
      rewrite -marks_of_context_length.
      now apply valid_subst_app_up.
    + solve_all.
      apply wfTermRel_pred_wf_branch in a as wfb.
      apply wf_branch_length in wfb.
      destruct a as (onbctx & onb).
      split; auto.
      eapply b0; tea.
      rewrite /= !mark_case_branch_context //=.
      rewrite -marks_of_context_length.
      now apply valid_subst_app_up.

  - erewrite map_dname. econstructor.
    1: now rewrite nth_error_map e.
    rewrite mark_fix_context.
    unfold wfTermRel_mfix in *.
    solve_all.
    eapply b0; tea.
    rewrite -fix_context_length -marks_of_context_length.
    now apply valid_subst_app_up.

  - erewrite map_dname. econstructor.
    1: now rewrite nth_error_map e.
    rewrite mark_fix_context.
    unfold wfTermRel_mfix in *.
    solve_all.
    eapply b0; tea.
    rewrite -fix_context_length -marks_of_context_length.
    now apply valid_subst_app_up.

  - econstructor. depelim p1; try now constructor.
    destruct X as (Xty & Xdef & Xval).
    constructor; cbn; eauto.
    solve_all.
Qed.

Lemma type_inst {cf : checker_flags} : env_prop
  (fun Σ Γ t A =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    Σ ;;; Δ |- t.[σ] : A.[σ])
  (fun Σ Γ j =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    lift_typing0 (fun t T => Σ ;;; Δ |- t.[σ] : T.[σ]) j)
  (fun Σ Γ =>
    All_local_env (fun Γ j =>
    forall Δ σ,
    wf_local Σ Δ ->
    Σ ;;; Δ ⊢ σ : Γ ->
    (lift_typing0 (fun (t T : term) => Σ ;;; Δ |- t.[σ] : T.[σ])) j) Γ).
Proof.
  apply typing_ind_env.

  - intros Σ wfΣ Γ j H Δ σ wfΔ Hσ.
    apply lift_typing_impl with (1 := H) => t T [_ IH].
    now apply IH.

  - intros Σ wfΣ Γ wfΓ _ X. assumption.
  - intros Σ wfΣ Γ wfΓ n decl e X Δ σ hΔ hσ. simpl.
    eapply hσ. assumption.
  - intros Σ wfΣ Γ wfΓ l X H0 Δ σ hΔ hσ. simpl.
    econstructor. all: assumption.
  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    assert (ihA' : lift_typing0 (typing Σ Δ) (j_vass_s na A.[σ] s1)) by now eapply ihA.
    econstructor; tas.
    apply lift_sorting_forget_univ in ihA'.
    eassert (wf_local Σ (Δ ,, _)) by (constructor; eassumption).
    eapply ihB; tea.
    eapply well_subst_Up ; assumption.
  - intros Σ wfΣ Γ wfΓ na A t bty X hA ihA ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    assert (ihA' : lift_typing0 (typing Σ Δ) (j_vass na A.[σ])) by now eapply ihA.
    econstructor; tas.
    eassert (wf_local Σ (Δ ,, _)) by (constructor; eassumption).
    eapply iht; tea.
    eapply well_subst_Up ; assumption.
  - intros Σ wfΣ Γ wfΓ na b B t A X hbB ihbB ht iht Δ σ hΔ hσ.
    autorewrite with sigma.
    assert (ihbB' : lift_typing0 (typing Σ Δ) (j_vdef na b.[σ] B.[σ])) by now eapply ihbB.
    econstructor; tas.
    eassert (wf_local Σ (Δ ,, _)) by (constructor; eassumption).
    eapply iht; tea.
    eapply well_subst_Up'; try assumption.
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu Δ σ hΔ hσ.
    autorewrite with sigma.
    econstructor.
    * specialize (ihty _ _ hΔ hσ).
      simpl in ihty. eapply meta_conv_term; [eapply ihty|].
      now rewrite up_Up.
    * specialize (iht _ _ hΔ hσ).
      simpl in iht. eapply meta_conv; [eapply iht|].
      now rewrite up_Up.
    * eapply ihu; auto.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst Δ σ hΔ hσ.
    autorewrite with sigma. simpl.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_constant_closed_type in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_inductive_closed_type in isdecl; eauto.
    rewrite inst_closed0; auto.
    now rewrite closedn_subst_instance.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst Δ σ hΔ hσ.
    eapply meta_conv; [econstructor; eauto|].
    eapply declared_constructor_closed_type in isdecl; eauto.
    rewrite inst_closed0; eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros IHΔ ci_npar eqpctx predctx wfp cup Hpctx Hpret
      IHpret IHpredctx isallowed Her.
    intros IHctxi Hc IHc iscof ptm wfbrs Hbrs Δ f HΔ Hf.
    autorewrite with sigma.
    rewrite map_app /=.
    rewrite /ptm inst_it_mkLambda_or_LetIn.
    assert (#|predctx| = #|pcontext p|) as predctx_len by now rewrite case_predicate_context_length //.
    rewrite predctx_len inst_predicate_preturn.
    rewrite inst_context_case_predicate_context //.
    eapply type_Case; eauto; simpl; rewrite - ?inst_context_case_predicate_context //.
    3,4: constructor; eauto; rewrite - ?inst_context_case_predicate_context //.
    + apply All_local_env_app_inv in Hpctx as [].
      apply All_local_env_app_inv in IHpredctx as [].
      eapply IHpret.
      * eapply wf_local_app_inst; eauto.
      * rewrite -predctx_len.
        eapply well_subst_app_up; tas.
        eapply wf_local_app_inst; eauto.
    + simpl. unfold id.
      specialize (IHc _ _ HΔ Hf).
      now rewrite inst_mkApps map_app in IHc.
    + now eapply inst_wf_predicate.
    + simpl. eauto.
      apply All_local_env_app_inv in IHpredctx as [].
      eapply wf_local_app_inst; eauto.
    + revert IHctxi.
      rewrite /= /id -map_app.
      rewrite -{2}[subst_instance _ _](inst_closedn_ctx f 0).
      { pose proof (declared_inductive_closed_pars_indices isdecl).
        now rewrite closedn_subst_instance_context. }
      rewrite inst_context_telescope.
      rewrite inst_telescope_upn0.
      clear -Δ HΔ f Hf.
      induction 1.
      { constructor; auto. }
      { destruct t0; simpl. rewrite inst_telescope_cons.
        constructor; cbn; eauto.
        now rewrite inst_subst_telescope /= in IHIHctxi. }
      { simpl. rewrite inst_telescope_cons.
        constructor; cbn; eauto.
        now rewrite inst_subst_telescope /= in IHIHctxi. }
    + now eapply inst_wf_branches.
    + eapply Forall2_All2 in wfbrs.
      eapply All2i_All2_mix_left in Hbrs; eauto.
      eapply All2i_nth_hyp in Hbrs.
      eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
      intros (Hnth & wfbr & eqbctx & IHbctx & (Hbod & IHbod) & Hbty & IHbty).
      split => //.
      rewrite -(inst_closed_constructor_body mdecl cdecl f).
      { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
        split; eauto. }
      rewrite inst_context_case_predicate_context //.
      rewrite inst_case_branch_type //.
      rewrite -/brctxty. intros brctx'.
      assert (wf_local Σ (Δ,,, brctx'.1)).
      { rewrite /brctx'. cbn.
        apply All_local_env_app_inv in IHbctx as [].
        eapply wf_local_app_inst; tea. }
      split => //. split.
      * eapply IHbod => //.
        rewrite /brctx' /brctxty; cbn.
        relativize #|bcontext br|.
        { eapply well_subst_app_up => //. }
        rewrite /case_branch_type /=.
        rewrite case_branch_context_length //.
      * eapply IHbty=> //.
        rewrite /brctx'; cbn.
        relativize #|bcontext br|.
        { eapply well_subst_app_up => //. }
        rewrite /brctxty /= case_branch_context_length //.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc e
           Δ σ hΔ hσ.
    simpl.
    eapply meta_conv; [econstructor|].
    * eauto.
    * specialize (ihc _ _ hΔ hσ).
      rewrite inst_mkApps in ihc. eapply ihc.
    * now rewrite map_length.
    * autorewrite with sigma.
      eapply declared_projection_closed in isdecl; auto.
      move: isdecl.
      rewrite -(closedn_subst_instance _ _ u).
      eapply inst_ext_closed.
      intros x Hx.
      rewrite subst_consn_lt /=; len; try lia.
      rewrite Upn_comp; cbn; try now repeat len.
      rewrite subst_consn_lt /=; cbn; len; try lia.
      now rewrite map_rev.
  - intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth htypes hmfixt ihmfixt hmfixb ihmfixb wffix Δ σ hΔ hσ.
    simpl. eapply meta_conv; [econstructor;eauto|].
    * now eapply fix_guard_inst.
    * now rewrite nth_error_map hnth.
    * apply All_map, (All_impl ihmfixt).
      intros x t. eapply t; eauto.
    * pose proof (inst_fix_context mfix σ).
      setoid_rewrite <-up_Upn at 1 in H. rewrite H.
      apply All_map, (All_impl ihmfixb).
      unfold on_def_body.
      intros x t. relativize (lift0 _ _).
      1: eenough (wf_local Σ (Δ ,,, _)).
      1: eapply t; eauto.
      + rewrite -(fix_context_length mfix).
        eapply well_subst_app_up => //.
      + eapply wf_local_app_inst; eauto.
        now eapply All_local_env_app_inv in htypes as [].
      + rewrite lift0_inst /types inst_context_length fix_context_length.
        now sigma.
    * now apply inst_wf_fixpoint.
    * reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types hguard hnth htypes hmfixt ihmfixt hmfixb ihmfixb wffix Δ σ hΔ hσ.
    simpl. eapply meta_conv; [econstructor;eauto|].
    * now eapply cofix_guard_inst.
    * now rewrite nth_error_map hnth.
    * apply All_map, (All_impl ihmfixt).
      intros x t. eapply t; eauto.
    * pose proof (inst_fix_context mfix σ).
      setoid_rewrite <-up_Upn at 1 in H. rewrite H.
      apply All_map, (All_impl ihmfixb).
      unfold on_def_body.
      intros x t. relativize (lift0 _ _).
      1: eenough (wf_local Σ (Δ ,,, _)).
      1: eapply t; eauto.
      + rewrite -(fix_context_length mfix).
        eapply well_subst_app_up => //.
      + eapply wf_local_app_inst; eauto.
        now eapply All_local_env_app_inv in htypes as [].
      + rewrite lift0_inst /types inst_context_length fix_context_length.
        now sigma.
    * now apply inst_wf_cofixpoint.
    * reflexivity.

  - intros Σ wfΣ Γ wfΓ p pty cdecl _ hp hdecl pinv hty hind Δ σ hΔ hσ.
    cbn. rewrite inst_prim_type. econstructor; tea.
    1-2:now rewrite prim_val_tag_map.
    depelim hind; constructor; cbn; eauto. solve_all.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht hB ihB hcum Δ σ hΔ hσ.
    eapply type_Cumul.
    + eapply iht. all: auto.
    + eapply ihB. all: auto.
    + eapply inst_cumulSpec; tea.
      all: fvs.
      eapply well_subst_closed_subst; tea.
      eapply wf_local_closed_context; tea.
Qed.

Lemma typing_inst {cf : checker_flags} Σ Γ t A Δ σ {wfΣ : wf Σ.1} :
  wf_local Σ Δ ->
  Σ ;;; Δ ⊢ σ : Γ ->
  Σ ;;; Γ |- t : A ->
  Σ ;;; Δ |- t.[σ] : A.[σ].
Proof.
  intros a b c; revert a b. eapply type_inst; eauto.
Qed.
