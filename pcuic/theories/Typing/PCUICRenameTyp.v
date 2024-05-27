(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICCumulativity PCUICRelevance
  PCUICTyping PCUICReduction PCUICGlobalEnv PCUICClosed PCUICEquality PCUICRenameDef
  PCUICSigmaCalculus PCUICClosed PCUICOnFreeVars PCUICOnFreeVarsConv PCUICGuardCondition PCUICTyping
  PCUICWeakeningEnvConv PCUICWeakeningEnvTyp PCUICClosedConv PCUICClosedTyp PCUICRenameConv.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.

(** * Type preservation for σ-calculus operations *)

Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".
Set Default Proof Using "Type*".

Section Renaming.

Context `{cf : checker_flags}.

Lemma renaming_vass_xpredT Σ Γ Δ na A f :
    wf_local Σ (Δ ,, vass na (rename f A)) ->
    renaming xpredT Σ Γ Δ f ->
    renaming xpredT Σ (Γ ,, vass na A) (Δ ,, vass na (rename f A)) (shiftn 1 f).
Proof.
  intros hΓ [? h].
  split. 1: auto.
  eapply urenaming_vass_xpredT; assumption.
Qed.

Lemma renaming_vdef_xpredT Σ Γ Δ na b B f :
    wf_local Σ (Δ ,, vdef na (rename f b) (rename f B)) ->
    renaming xpredT Σ Γ Δ f ->
    renaming xpredT Σ (Γ ,, vdef na b B) (Δ ,, vdef na (rename f b) (rename f B)) (shiftn 1 f).
Proof.
  intros hΓ [? h].
  split. 1: auto.
  eapply urenaming_vdef_xpredT; assumption.
Qed.

Lemma rename_ind_predicate_context {Σ : global_env} {wfΣ : wf Σ} {f ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl ->
  rename_context (shiftn (context_assumptions (ind_params mdecl)) f) (ind_predicate_context ind mdecl idecl) =
  ind_predicate_context ind mdecl idecl.
Proof.
  intros isdecl.
  generalize (declared_inductive_closed_pars_indices isdecl).
  rewrite closedn_ctx_app => /andP [] clpars /= clinds.
  rewrite /ind_predicate_context.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  rewrite !rename_context_snoc /= /map_decl /= /snoc. f_equal.
  - f_equal. len.
    rewrite rename_mkApps /=. f_equal.
    rewrite shiftn_add.
    relativize (#|_| + _).
    1:now erewrite -> rename_to_extended_list.
    now len.
  - rewrite rename_context_subst.
    rewrite rename_closed_extended_subst //. f_equal.
    rewrite shiftn_add Nat.add_comm. len.
    rewrite rename_context_lift. f_equal.
    rewrite rename_closedn_ctx //.
Qed.

Lemma rename_case_predicate_context {Σ : global_env} {wfΣ : wf Σ} {ind mdecl idecl f p} :
  declared_inductive Σ ind mdecl idecl ->
  wf_predicate mdecl idecl p ->
  rename_context f (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind mdecl idecl (rename_predicate f p).
Proof.
  intros decli wfp.
  unfold case_predicate_context. simpl.
  unfold id. unfold case_predicate_context_gen.
  rewrite rename_context_set_binder_name.
  - len.
    now rewrite -(wf_predicate_length_pcontext wfp).
  - f_equal. rewrite /pre_case_predicate_context_gen.
    rewrite rename_inst_case_context.
    rewrite (wf_predicate_length_pars wfp) (declared_minductive_ind_npars decli).
    now rewrite (rename_ind_predicate_context decli).
Qed.

Lemma rename_case_branch_context {Σ : global_env} {wfΣ : wf Σ} {ind mdecl idecl f p br cdecl} :
  declared_inductive Σ ind mdecl idecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  rename_context f (case_branch_context ind mdecl p (forget_types (bcontext br)) cdecl) =
  case_branch_context ind mdecl (rename_predicate f p) (forget_types (bcontext br)) (rename_constructor_body mdecl f cdecl).
Proof.
  unfold rename_constructor_body, map_constructor_body.
  intros isdecl wfp wfb.
  apply rename_case_branch_context_gen.
  - eapply declared_inductive_closed_params, isdecl.
  - rewrite map_length. now apply wf_branch_length.
  - rewrite (wf_predicate_length_pars wfp) (declared_minductive_ind_npars isdecl) //.
Qed.

Lemma rename_case_branch_type {Σ : global_env_ext} {wfΣ : wf Σ} f (ci : case_info) mdecl idecl p br i cdecl :
  declared_inductive Σ ci mdecl idecl ->
  wf_predicate mdecl idecl p ->
  wf_branch cdecl br ->
  let ptm := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) in
  let p' := rename_predicate f p in
  let ptm' := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p') (preturn p') in
  case_branch_type ci mdecl idecl
     (rename_predicate f p)
     (map_branch_shift rename shiftn f br)
     ptm' i (rename_constructor_body mdecl f cdecl) =
  map_pair (rename_context f) (rename (shiftn #|bcontext br| f))
  (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros decli wfp wfb ptm p' ptm'.
  rewrite /case_branch_type /case_branch_type_gen /map_pair /=.
  erewrite rename_case_branch_context; tea.
  f_equal.
  rewrite rename_mkApps map_app map_map_compose.
  rewrite (wf_branch_length wfb).
  f_equal.
  * rewrite /ptm' /ptm !lift_it_mkLambda_or_LetIn !rename_it_mkLambda_or_LetIn.
    rewrite !lift_rename. f_equal.
    ++ rewrite /p'. len.
      epose proof (rename_context_lift f #|cstr_args cdecl| 0).
        rewrite Nat.add_0_r in H.
        rewrite H. len.
        rewrite shiftn0 //. f_equal.
        rewrite rename_case_predicate_context //.
    ++ rewrite /p'. rewrite Nat.add_0_r. simpl. len.
      rewrite map2_length //. 1:{ len. now rewrite (wf_predicate_length_pcontext wfp). }
      rewrite - !lift_rename; len. rewrite case_predicate_context_length // shiftn_add.
      now rewrite -rename_shiftnk Nat.add_comm.
  * rewrite /= rename_mkApps /=. f_equal.
    ++ rewrite !map_map_compose /id. apply map_ext => t.
      rewrite /expand_lets /expand_lets_k.
      rewrite -rename_subst_instance. len.
      rewrite -shiftn_add -shiftn_add.
      rewrite rename_subst map_rev. f_equal.
      rewrite List.rev_length rename_subst.
      rewrite (wf_predicate_length_pars wfp).
      rewrite (declared_minductive_ind_npars decli).
      rewrite -{2}(context_assumptions_subst_instance (puinst p) (ind_params mdecl)).
      rewrite rename_closed_extended_subst.
      { rewrite closedn_subst_instance_context.
        apply (declared_inductive_closed_params decli). }
      f_equal. len. rewrite !shiftn_add.
      rewrite (Nat.add_comm _ (context_assumptions _)) rename_shiftnk.
      f_equal. rewrite Nat.add_comm rename_subst.
      rewrite rename_inds. f_equal.
      rewrite shiftn_add. now len.
    ++ unfold id. f_equal. f_equal.
       rewrite map_app map_map_compose.
       rewrite map_map_compose.
       setoid_rewrite rename_shiftn. len. f_equal.
       rewrite rename_to_extended_list.
       now rewrite /to_extended_list /to_extended_list_k reln_fold.
Qed.

Lemma cumulSpec_renameP pb P Σ Γ Δ f A B : let sP := shiftnP #|Γ| P in
  wf Σ.1 ->
  urenaming sP Γ Δ f ->
  is_closed_context Γ ->
  is_open_term Γ A ->
  is_open_term Γ B ->
  is_closed_context Δ ->
  Σ ;;; Γ ⊢ A ≤s[pb] B ->
  Σ ;;; Δ ⊢ rename f A ≤s[pb] rename f B.
Proof.
  intros sP wfΣ Hren HΓ HA HB HΔ e.
  revert pb Γ A B e sP Δ f wfΣ Hren HA HB HΓ HΔ e.
  induction 1; intros; cbn.
  all: lazymatch goal with
       | [ H : cumul_predicate_dep _ _ _ |- _ ] => apply cumul_predicate_undep in H
       | _ => idtac
       end.
  all: repeat match goal with
         | [ H : All2_dep _ _ |- _ ] => apply All2_undep in H
         end.
  all: inv_on_free_vars.
  - rewrite rename_subst10. solve [econstructor].
  - rewrite rename_subst10. solve [econstructor].
  - destruct (nth_error Γ i) eqn:hnth; noconf pf.
    assert (hav : sP i).
    { unfold sP, shiftnP in *. cbn in *. intuition auto with *. }
    specialize (Hren _ _ hav hnth) as (decl' & e' & eqann & hr & hbo).
    rewrite H /= in hbo.
    rewrite lift0_rename.
    destruct (decl_body decl') eqn:hdecl => //. noconf hbo.
    let H0 := match goal with H : rename _ _ = rename _ _ |- _ => H end in
    sigma in H0; sigma; rewrite H0.
    relativize (t.[_]).
    2:{ setoid_rewrite rshiftk_S. rewrite -rename_inst.
        now rewrite -(lift0_rename (S (f i)) _). }
     eapply cumul_rel. now rewrite e' /= hdecl.
  - rewrite rename_mkApps. simpl.
    rewrite rename_iota_red //.
    * rewrite skipn_length; lia.
    * eapply nth_error_forallb in Hbrs; tea. simpl in Hbrs.
      move/andP: Hbrs => [] clbctx clbod.
      rewrite closedn_ctx_on_free_vars.
      now rewrite test_context_k_closed_on_free_vars_ctx in clbctx.
   * eapply cumul_iota.
     + rewrite nth_error_map Hbrs /= //.
     + simpl. now len.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumul_fix.
     + eapply rename_unfold_fix. eassumption.
     + rewrite -is_constructor_rename. assumption.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumul_cofix_case.
     eapply rename_unfold_cofix. eassumption.
   - rewrite 2!rename_mkApps. simpl.
     eapply cumul_cofix_proj.
     eapply rename_unfold_cofix. eassumption.
   - rewrite rename_subst_instance.
     eapply cumul_delta.
     + eassumption.
     + rewrite rename_closed. 2: assumption.
       eapply declared_constant_closed_body. all: eauto.
  - rewrite rename_mkApps. simpl.
    eapply cumul_proj. rewrite nth_error_map. rewrite Hargs. reflexivity.
  - rewrite closedP_on_free_vars in clu.
    eapply cumul_Trans; try apply IHe1; try apply IHe2; eauto.
    + rewrite closedn_ctx_on_free_vars //.
    + rewrite closedP_on_free_vars. eapply urename_is_open_term; eauto.
  - eapply cumul_Sym; intuition; eauto.
  - eapply cumul_Refl; intuition; eauto.
  - eapply cumul_Evar.
    repeat toAll. eapply All2_impl. 1:tea. cbn; intros.
    eapply X0.1.2; intuition.
  - eapply cumul_App; eauto.
  - eapply cumul_Lambda; eauto.
    eapply IHe2; tea.
    * now apply urenaming_vass'.
    * rewrite shiftnP_S //.
    * rewrite shiftnP_S //.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
      cbn. eapply urename_is_open_term; eauto.
  - eapply cumul_Prod; eauto.
    eapply IHe2; tea.
    * now apply urenaming_vass'.
    * rewrite shiftnP_S //.
    * rewrite shiftnP_S //.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
    * rewrite on_free_vars_ctx_snoc. apply andb_and; split; eauto.
      cbn. eapply urename_is_open_term; eauto.
  - eapply cumul_LetIn; eauto.
    eapply IHe3; tea.
    * now apply urenaming_vdef'.
    * rewrite shiftnP_S //.
    * rewrite shiftnP_S //.
    * rewrite on_free_vars_ctx_snoc_def; eauto.
    * rewrite on_free_vars_ctx_snoc_def; eauto.
      all: eapply urename_is_open_term; eauto.
  - destruct Hp as (Hp & Hu & Hc & Hr).
    destruct X as (Xp & Xu & Xc & Xr).
    rewrite -!(All2_length Xp) -?(All2_length Xc) in p1, p2, p4.
    eapply cumul_Case.
    * unfold cumul_predicate in *.
      repeat split; eauto.
      + eapply All2_map. solve_all.
      + cbn.
        rewrite -(All2_length Hc) inst_case_predicate_context_rename //.
        eapply Xr; tea.
        all: len; rewrite -?shiftnP_add //.
        -- erewrite <-inst_case_context_length.
          apply urenaming_context'; tas.
        -- apply on_free_vars_ctx_inst_case_context; eauto.
        --
          rewrite -inst_case_predicate_context_rename; eauto.
          apply on_free_vars_ctx_inst_case_context; eauto.
          { solve_all. eapply urename_is_open_term; eauto. }
          len.
    * eauto.
    * unfold cumul_branches, cumul_branch in *.
      clear Hp Xp.
      solve_all; inv_on_free_vars.
      rewrite -(All2_length a1) inst_case_branch_context_rename // in H2 |- *.
      eapply b1; tea.
      all: len; rewrite -?shiftnP_add //.
      + erewrite <-inst_case_context_length.
        apply urenaming_context'; tas.
      + apply on_free_vars_ctx_inst_case_context; eauto.
        now eapply All_forallb.
      + rewrite -inst_case_branch_context_rename; eauto.
        apply on_free_vars_ctx_inst_case_context; eauto.
        { solve_all. eapply urename_is_open_term; eauto. }
        len.
  - eapply cumul_Proj; eauto.
  - rewrite -(All2_length X).
    eapply cumul_Fix.
    unfold cumul_mfixpoint in *.
    have clmfix : is_closed_context (Γ ,,, fix_context mfix).
    { rewrite on_free_vars_ctx_app HΓ /=. now apply on_free_vars_fix_context. }
    have clmfix' : is_closed_context (Δ ,,, rename_context f (fix_context mfix)).
    { rewrite on_free_vars_ctx_app HΔ /=. rewrite -rename_fix_context. apply on_free_vars_fix_context.
      unfold test_def in *; solve_all.
      - eapply urename_is_open_term; now eauto.
      - rewrite -fix_context_length. eapply urename_on_free_vars_shift; eauto. rewrite fix_context_length //. }
    rewrite -(All2_length H) rename_fix_context -fix_context_length in HA, HB |- *.
    set Ξ := fix_context _ in H, X, HA, HB, clmfix, clmfix' |- *. clearbody Ξ.
    solve_all.
    all: unfold test_def in *; rtoProp.
    1: now eapply a.
    eapply b2; len; rewrite -?shiftnP_add; eauto.
    now apply urenaming_context'.
  - rewrite -(All2_length X).
    eapply cumul_CoFix.
    unfold cumul_mfixpoint in *.
    have clmfix : is_closed_context (Γ ,,, fix_context mfix).
    { rewrite on_free_vars_ctx_app HΓ /=. now apply on_free_vars_fix_context. }
    have clmfix' : is_closed_context (Δ ,,, rename_context f (fix_context mfix)).
    { rewrite on_free_vars_ctx_app HΔ /=. rewrite -rename_fix_context. apply on_free_vars_fix_context.
      unfold test_def in *; solve_all.
      - eapply urename_is_open_term; now eauto.
      - rewrite -fix_context_length. eapply urename_on_free_vars_shift; eauto. rewrite fix_context_length //. }
    rewrite -(All2_length H) rename_fix_context -fix_context_length in HA, HB |- *.
    set Ξ := fix_context _ in H, X, HA, HB, clmfix, clmfix' |- *. clearbody Ξ.
    solve_all.
    all: unfold test_def in *; rtoProp.
    1: now eapply a.
    eapply b2; len; rewrite -?shiftnP_add; eauto.
    now apply urenaming_context'.
  - eapply cumul_Prim. depelim X; constructor; cbn in *; rtoProp; eauto. solve_all.
  - repeat rewrite rename_mkApps. eapply cumul_Ind.
    * repeat rewrite map_length; eauto.
    * repeat toAll. eapply All2_impl. 1: tea. cbn; intros.
      destruct_head'_prod.
      eauto.
  - repeat rewrite rename_mkApps. eapply cumul_Construct.
    * repeat rewrite map_length; eauto.
    * repeat toAll.
      eapply All2_impl. 1: tea. cbn; intros.
      destruct_head'_prod; eauto.
  - eapply cumul_Sort; eauto.
  - eapply cumul_Const; eauto.
Defined.

Lemma convSpec_renameP P Σ Γ Δ f A B : let sP := shiftnP #|Γ| P in
    wf Σ.1 ->
    urenaming sP Γ Δ f ->
    is_closed_context Γ ->
    is_open_term Γ A ->
    is_open_term Γ B ->
    is_closed_context Δ ->
    Σ ;;; Γ |- A =s B ->
    Σ ;;; Δ |- rename f A =s rename f B.
Proof.
  apply cumulSpec_renameP.
Qed.

(* Lemma cumul_decls_renameP {P Σ Γ Γ' Δ Δ' f} d d' :
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    urenaming P Δ' Γ' f ->
    on_free_vars_decl P d ->
    on_free_vars_decl P d' ->
    on_ctx_free_vars P Γ ->
    cumul_decls Σ Γ Γ' d d' ->
    cumul_decls Σ Δ Δ' (rename_decl f d) (rename_decl f d').
Proof.
  intros wf uren uren' ond ond' onΓ Hd; depelim Hd; constructor; tas;
    (eapply convSpec_renameP || eapply cumulSpec_renameP); tea.
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
Qed.

Lemma conv_decls_renameP {P Σ Γ Γ' Δ Δ' f} d d' :
    wf Σ.1 ->
    urenaming P Δ Γ f ->
    urenaming P Δ' Γ' f ->
    on_free_vars_decl P d ->
    on_free_vars_decl P d' ->
    on_ctx_free_vars P Γ ->
    conv_decls Σ Γ Γ' d d' ->
    conv_decls Σ Δ Δ' (rename_decl f d) (rename_decl f d').
Proof.
  intros wf uren uren' ond ond' onΓ Hd; depelim Hd; constructor; tas;
    (eapply convSpec_renameP || eapply cumulSpec_renameP); tea.
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
  * now move/andP: ond => [].
  * now move/andP: ond' => [].
Qed. *)

Lemma on_free_vars_ctx_onctx_k P ctx :
  reflectT (onctx_k (fun k => on_free_vars (shiftnP k P)) 0 ctx)
    (on_free_vars_ctx P ctx).
Proof.
  rewrite -test_context_k_on_free_vars_ctx.
  apply (onctx_k_P reflectT_pred2).
Qed.

Lemma Alli_helper Q Γ :
  Alli (fun (i : nat) (d : context_decl) => ondecl (Q (#|Γ| - i + 0)) d) 1 Γ ->
  onctx_k Q 0 Γ.
Proof.
  move/(Alli_shiftn_inv 0 _ 1) => H.
  eapply Alli_impl; tea => n x /=.
  now replace (#|Γ| - S n + 0) with (Nat.pred #|Γ| - n + 0) by lia.
Qed.

Lemma ondecl_on_free_vars_decl P d :
  ondecl (on_free_vars P) d ->
  on_free_vars_decl P d.
Proof.
  rewrite /on_free_vars_decl.
  now case: (ondeclP reflectT_pred).
Qed.

(* Lemma conv_ctx_renameP {Σ : global_env_ext} {P} {Γ Δ} {L R} f :
  wf Σ.1 ->
  urenaming P Δ Γ f ->
  on_free_vars_ctx P L ->
  on_free_vars_ctx P R ->
  on_ctx_free_vars P Γ ->
  conv_context Σ (Γ ,,, L) (Γ ,,, R) ->
  conv_context Σ (Δ ,,, rename_context f L) (Δ ,,, rename_context f R).
Proof.
  intros wf uren onL onL' onΓ H.
  rewrite /rename_context - !mapi_context_fold.
  pose proof (All2_fold_length H) as hlen.
  len in hlen. assert (#|L| = #|R|) by lia.
  eapply All2_fold_app_inv in H as [_ H] => //.
  eapply All2_fold_app; len => //; pcuic.
  { eapply conv_ctx_refl'. }
  move/on_free_vars_ctx_onctx_k: onL => onL.
  move/on_free_vars_ctx_onctx_k: onL' => onR.

  eapply All2_fold_mapi.
  eapply All2_fold_impl_ind_onctx_k; tea =>
    /= L' R' d d' IH onL' IH' ond ond'.
  simpl.
  rewrite !mapi_context_fold -/(rename_context f L') -/(rename_context f R').
  eapply conv_decls_renameP; eauto.
  + now eapply urenaming_context.
  + rewrite (All2_fold_length IH).
    now eapply urenaming_context.
  + now eapply ondecl_on_free_vars_decl.
  + rewrite (All2_fold_length IH').
    now eapply ondecl_on_free_vars_decl.
  + rewrite on_ctx_free_vars_extend // onΓ.
    now move/on_free_vars_ctx_onctx_k: onL'.
Qed. *)


(* Lemma cumul_ctx_renameP {Σ : global_env_ext} {P} {Γ Δ} {L R} f :
  wf Σ.1 ->
  urenaming P Δ Γ f ->
  on_free_vars_ctx P L ->
  on_free_vars_ctx P R ->
  on_ctx_free_vars P Γ ->
  cumul_context Σ (Γ ,,, L) (Γ ,,, R) ->
  cumul_context Σ (Δ ,,, rename_context f L) (Δ ,,, rename_context f R).
Proof.
  intros wf uren onL onL' onΓ H.
  rewrite /rename_context - !mapi_context_fold.
  pose proof (All2_fold_length H) as hlen.
  len in hlen. assert (#|L| = #|R|) by lia.
  eapply All2_fold_app_inv in H as [_ H] => //.
  eapply All2_fold_app; len => //; pcuic.
  { eapply cumul_ctx_refl'. }
  move/on_free_vars_ctx_onctx_k: onL => onL.
  move/on_free_vars_ctx_onctx_k: onL' => onR.

  eapply All2_fold_mapi.
  eapply All2_fold_impl_ind_onctx_k; tea =>
    /= L' R' d d' IH onL' IH' ond ond'.
  simpl.
  rewrite !mapi_context_fold -/(rename_context f L') -/(rename_context f R').
  eapply cumul_decls_renameP; eauto.
  + now eapply urenaming_context.
  + rewrite (All2_fold_length IH).
    now eapply urenaming_context.
  + now eapply ondecl_on_free_vars_decl.
  + rewrite (All2_fold_length IH').
    now eapply ondecl_on_free_vars_decl.
  + rewrite on_ctx_free_vars_extend // onΓ.
    now move/on_free_vars_ctx_onctx_k: onL'.
Qed. *)

Lemma subst1_inst :
  forall t n u,
    t{ n := u } = t.[⇑^n (u ⋅ ids)].
Proof.
  intros t n u.
  unfold subst1. rewrite subst_inst.
  eapply inst_ext. intro i.
  unfold Upn, subst_compose, subst_consn.
  destruct (Nat.ltb_spec0 i n).
  - rewrite -> nth_error_idsn_Some by assumption. reflexivity.
  - rewrite -> nth_error_idsn_None by lia.
    rewrite idsn_length.
    destruct (Nat.eqb_spec (i - n) 0).
    + rewrite e. simpl. reflexivity.
    + replace (i - n) with (S (i - n - 1)) by lia. simpl.
      destruct (i - n - 1) eqn: e.
      * simpl. reflexivity.
      * simpl. reflexivity.
Qed.
(* Hint Rewrite @subst1_inst : sigma. *)

Lemma rename_predicate_preturn f p :
  rename (shiftn #|p.(pcontext)| f) (preturn p) =
  preturn (rename_predicate f p).
Proof. reflexivity. Qed.

Lemma wf_local_app_renaming Σ Γ Δ :
  All_local_rel (fun (Γ : context) j =>
    forall Δ (f : nat -> nat),
    renaming xpredT Σ Γ Δ f ->
    lift_typing0 (fun t T => Σ ;;; Δ |- rename f t : rename f T) j)
    Γ Δ ->
  forall Δ' f,
  renaming xpredT Σ Γ Δ' f ->
  wf_local Σ (Δ' ,,, rename_context f Δ).
Proof.
  intros. destruct X0.
  induction X using All_local_rel_ind1.
  1: now apply a.
  rewrite rename_context_snoc /=. apply All_local_env_snoc; auto.
  eapply lift_typing_map with (j := j_decl _) => //.
  eapply X.
  split; auto.
  now eapply urenaming_context_xpredT.
Qed.

Lemma rename_decompose_prod_assum f Γ t :
    decompose_prod_assum (rename_context f Γ) (rename (shiftn #|Γ| f) t)
    = let '(Γ, t) := decompose_prod_assum Γ t in (rename_context f Γ, rename (shiftn #|Γ| f) t).
Proof.
  induction t in Γ |- *. all: try reflexivity.
  - specialize (IHt2 (Γ ,, vass na t1)).
    rewrite rename_context_snoc /= in IHt2.
    simpl. now rewrite shiftn_add IHt2.
  - specialize (IHt3 (Γ ,, vdef na t1 t2)).
    rewrite rename_context_snoc /= in IHt3.
    simpl. now rewrite shiftn_add IHt3.
Qed.

Lemma rename_app_context f Γ Δ :
  rename_context f (Γ ,,, Δ) =
  rename_context f Γ ,,, rename_context (shiftn #|Γ| f) Δ.
Proof.
  rewrite /rename_context fold_context_k_app /app_context. f_equal.
  apply fold_context_k_ext. intros i x. now rewrite shiftn_add.
Qed.

Lemma rename_smash_context f Γ Δ :
  rename_context f (smash_context Γ Δ) =
  smash_context (rename_context (shiftn #|Δ| f) Γ) (rename_context f Δ).
Proof.
  induction Δ as [|[na [b|] ty] Δ] in Γ |- *; simpl; auto;
    rewrite ?shiftn0 // ?rename_context_snoc IHΔ /=; len.
  - f_equal. now rewrite rename_context_subst /= shiftn_add.
  - f_equal. rewrite rename_app_context /map_decl /= /app_context.
    f_equal.
    * now rewrite shiftn_add.
    * rewrite /rename_context fold_context_k_tip /map_decl /=. do 2 f_equal.
      now rewrite shiftn0.
Qed.

Lemma nth_error_rename_context f Γ n :
  nth_error (rename_context f Γ) n =
  option_map (map_decl (rename (shiftn (#|Γ| - S n) f))) (nth_error Γ n).
Proof.
  induction Γ in n |- *; intros.
  - simpl. unfold rename_context, fold_context_k; simpl; rewrite nth_error_nil. easy.
  - simpl. destruct n; rewrite rename_context_snoc.
    + simpl. lia_f_equal.
    + simpl. rewrite IHΓ; simpl in *.
      assert (e : #|Γ| - S n = S #|Γ| - S (S n)). { lia. }
      rewrite e. reflexivity.
Qed.

Lemma rename_check_one_fix f (mfix : mfixpoint term) d x :
  check_one_fix d = Some x ->
  check_one_fix (map_def (rename f) (rename (shiftn #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (rename_decompose_prod_assum f [] dtype).
  rewrite shiftn0. intros ->.
  destruct decompose_prod_assum.
  rewrite -(rename_smash_context f []).
  destruct nth_error eqn:hnth => //.
  pose proof (nth_error_Some_length hnth). len in H.
  simpl in H.
  destruct (nth_error (List.rev (rename_context _ _)) _) eqn:hnth'.
  2:{ eapply nth_error_None in hnth'. len in hnth'. }
  rewrite nth_error_rev_inv in hnth; len; auto.
  len in hnth. simpl in hnth.
  rewrite nth_error_rev_inv in hnth'; len; auto.
  len in hnth'. simpl in hnth'.
  rewrite nth_error_rename_context /= hnth /= in hnth'. noconf hnth'.
  simpl.
  destruct decompose_app eqn:da. len.
  destruct t0 => /= //.
  eapply decompose_app_inv in da. rewrite da.
  rewrite rename_mkApps. simpl. rewrite decompose_app_mkApps //.
Qed.

Lemma rename_check_one_cofix f (mfix : mfixpoint term) d x :
  check_one_cofix d = Some x ->
  check_one_cofix (map_def (rename f) (rename (shiftn #|mfix| f)) d) = Some x.
Proof.
  destruct d; simpl.
  move: (rename_decompose_prod_assum f [] dtype).
  rewrite shiftn0. intros ->.
  destruct decompose_prod_assum.
  destruct decompose_app eqn:da.
  destruct t0 => /= //.
  eapply decompose_app_inv in da. rewrite da /=.
  rewrite rename_mkApps. simpl. rewrite decompose_app_mkApps //.
Qed.

Lemma rename_wf_fixpoint Σ f mfix :
  wf_fixpoint Σ mfix ->
  wf_fixpoint Σ (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  unfold wf_fixpoint, wf_fixpoint_gen.
  rewrite forallb_map.
  move/andP => [] hmfix ho.
  apply/andP; split.
  { eapply forallb_impl; tea. intros. cbn in H0.
    now eapply isLambda_rename. }
  move: ho.
  rewrite map_map_compose.
  destruct (map_option_out (map check_one_fix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (rename_check_one_fix f mfix). }
  now rewrite hmap.
Qed.

Lemma rename_wf_cofixpoint Σ f mfix :
  wf_cofixpoint Σ mfix ->
  wf_cofixpoint Σ (map (map_def (rename f) (rename (shiftn #|mfix| f))) mfix).
Proof.
  unfold wf_cofixpoint, wf_cofixpoint_gen.
  rewrite map_map_compose.
  destruct (map_option_out (map check_one_cofix mfix)) as [[]|] eqn:hmap => //.
  eapply map_option_out_impl in hmap.
  2:{ intros x y. apply (rename_check_one_cofix f mfix). }
  now rewrite hmap.
Qed.

Lemma rename_subst_telescope f s Γ :
  rename_telescope f (subst_telescope s 0 Γ) =
  subst_telescope (map (rename f) s) 0
    (rename_telescope (shiftn #|s| f) Γ).
Proof.
  rewrite /rename_telescope /subst_telescope.
  rewrite !mapi_compose. apply mapi_ext => k' d.
  rewrite !compose_map_decl; apply map_decl_ext => t'.
  now rewrite Nat.add_0_r rename_subst.
Qed.

Instance rename_telescope_ext : Proper (`=1` ==> `=1`) rename_telescope.
Proof.
  intros f g Hfg Γ.
  rewrite /rename_telescope. apply mapi_ext => n x.
  now rewrite Hfg.
Qed.

Lemma rename_telescope_shiftn0 f Γ : rename_telescope (shiftn 0 f) Γ = rename_telescope f Γ.
Proof. now sigma. Qed.

Lemma rename_telescope_cons f d Γ :
  rename_telescope f (d :: Γ) = rename_decl f d :: rename_telescope (shiftn 1 f) Γ.
Proof.
  rewrite /rename_telescope mapi_cons /rename_decl.
  f_equal; sigma => //.
  apply mapi_ext => i x. now rewrite shiftn_add Nat.add_1_r.
Qed.

Hint Rewrite <- Upn_ren : sigma.

Lemma rename_prim_type f p pty : rename f (prim_type p pty) = prim_type (map_prim (rename f) p) pty.
Proof.
  destruct p as [? []]; cbn; simp prim_type => //.
Qed.

Lemma rename_isTermRel P f Σ Δ Γ t rel :
  wf Σ ->
  let sP := shiftnP #|Γ| P in
  mrenaming sP Γ Δ f ->
  isTermRel Σ Γ t rel ->
  isTermRel Σ Δ (rename f t) rel.
Proof.
  intros wfΣ sP Hur H.
  induction t using term_forall_list_ind in f, Γ, Δ, sP, Hur, H, rel |- *; cbn; depelim H.
  all: try solve [ try rewrite H; econstructor => //; eauto ].
  - constructor.
    eapply Hur; tas.
    apply nth_error_Some_length in e.
    unfold sP, shiftnP. toProp. left. now apply Nat.ltb_lt.
  - constructor; [eapply IHt1|eapply IHt2]; tea.
    now apply mrenaming_snoc'.
  - constructor; [eapply IHt1|eapply IHt2]; tea.
    now apply mrenaming_snoc'.
  - constructor; [eapply IHt1|eapply IHt2|eapply IHt3]; tea.
    now apply mrenaming_snoc'.
  - eapply wfTermRel_pred_wf_predicate in w as wfp; tea. 2: apply d.
    destruct X as (Xp & Xc & Xr). destruct w as (wp & wc & wr).
    econstructor; tea. 3: now eauto.
    1: repeat split.
    + rewrite /= /id.
      rewrite -[subst_instance _ _](rename_closedn_ctx f 0).
      { pose proof (declared_minductive_closed (proj1 d)) as []%andb_and.
        now rewrite closedn_subst_instance_context. }
      rewrite rename_context_telescope.
      rewrite rename_telescope_shiftn0.
      clear -wp Xp Hur.
      induction wp in Xp |- *.
      1: constructor.
      all: rewrite rename_telescope_cons /=.
      * depelim Xp; constructor; eauto.
        rewrite -(rename_subst_telescope _ [t]). now apply IHwp.
      * constructor.
        rewrite -(rename_subst_telescope _ [b]). now apply IHwp.
    + now cbn.
    + eapply Xr; tea.
      apply wf_predicate_length_pcontext in wfp.
      rewrite app_length /= !mark_case_predicate_context //=.
      rewrite -marks_of_context_length.
      now apply mrenaming_app'.
    + solve_all.
      apply wfTermRel_pred_wf_branch in a as wfb.
      apply wf_branch_length in wfb.
      destruct a as (onbctx & onb).
      split; auto.
      eapply b0; tea.
      rewrite app_length /= !mark_case_branch_context //=.
      rewrite -marks_of_context_length.
      now apply mrenaming_app'.

  - erewrite map_dname. econstructor.
    1: now rewrite nth_error_map e.
    rewrite mark_fix_context.
    unfold wfTermRel_mfix in *.
    solve_all.
    eapply b0; tea.
    rewrite app_length -fix_context_length -marks_of_context_length.
    now apply mrenaming_app'.

  - erewrite map_dname. econstructor.
    1: now rewrite nth_error_map e.
    rewrite mark_fix_context.
    unfold wfTermRel_mfix in *.
    solve_all.
    eapply b0; tea.
    rewrite app_length -fix_context_length -marks_of_context_length.
    now apply mrenaming_app'.

  - econstructor. depelim p1; try now constructor.
    destruct X as (Xty & Xdef & Xval).
    constructor; cbn; eauto.
    solve_all.
Qed.


(** For an unconditional renaming defined on all variables in the source context *)
Lemma typing_rename_prop :
  let Pj := (fun Σ Γ j =>
    forall Δ f,
    renaming xpredT Σ Γ Δ f ->
    lift_typing (fun Σ Γ t T => Σ ;;; Δ |- rename f t : rename f T) Σ Γ j)
  in
  env_prop
  (fun Σ Γ t A =>
    forall Δ f,
    renaming xpredT Σ Γ Δ f ->
    Σ ;;; Δ |- rename f t : rename f A)
  Pj
  (fun Σ Γ => All_local_env (Pj Σ) Γ).
Proof.
  apply typing_ind_env.

  - intros Σ wfΣ Γ j H Δ f Hr.
    apply lift_typing_impl with (1 := H) => t T [_ IH].
    now eapply IH.

  - intros Σ wfΣ Γ _ _ HΓ. assumption.

  - intros Σ wfΣ Γ wfΓ n decl isdecl ihΓ Δ f hf.
    simpl in *.
    eapply hf in isdecl as h => //.
    destruct h as (decl' & isdecl' & ? & h1 & h2).
    rewrite lift0_rename rename_compose h1 -lift0_rename.
    econstructor. all: auto. apply hf.

  - intros Σ wfΣ Γ wfΓ l X H0 Δ f [hΔ hf].
    simpl. constructor. all: auto.

  - intros Σ wfΣ Γ wfΓ na A B s1 s2 X hA ihA hB ihB Δ f hf.
    assert (lift_typing0 (typing Σ Δ) (j_vass_s na (rename f A) s1)).
    + eapply ihA; eauto.
    + rewrite /=. econstructor; tas.
      eapply ihB; eauto.
      simpl.
      eapply renaming_vass_xpredT. 2: eauto.
      constructor.
      * destruct hf as [hΔ hf]. assumption.
      * eapply lift_sorting_forget_univ, X0.
  - intros Σ wfΣ Γ wfΓ na A t B X hA ihA ht iht Δ f hf.
    assert (lift_typing0 (typing Σ Δ) (j_vass na (rename f A))).
    + eapply ihA; eauto.
    + simpl. econstructor; tas.
      eapply iht; eauto; simpl.
      eapply renaming_vass_xpredT. 2: eauto.
      constructor; tas.
      destruct hf as [hΔ hf]. assumption.
  - intros Σ wfΣ Γ wfΓ na b B t A X hbB ihbB ht iht Δ f hf.
    assert (lift_typing0 (typing Σ Δ) (j_vdef na (rename f b) (rename f B))).
    + eapply ihbB; tea.
    + simpl. econstructor; tas.
      eapply iht; tea.
      eapply renaming_vdef_xpredT. 2: eauto.
      constructor; tas.
      destruct hf as [hΔ hf]. assumption.
  - intros Σ wfΣ Γ wfΓ t na A B s u X hty ihty ht iht hu ihu Δ f hf.
    simpl. eapply meta_conv.
    + eapply type_App.
      * simpl in ihty. eapply ihty; tea.
      * simpl in iht. eapply iht. eassumption.
      * eapply ihu. eassumption.
    + autorewrite with sigma. rewrite !subst1_inst. sigma.
      eapply inst_ext => i.
      unfold subst_cons, ren, shiftn, subst_compose. simpl.
      destruct i.
      * simpl. reflexivity.
      * simpl. replace (i - 0) with i by lia.
        reflexivity.
  - intros Σ wfΣ Γ wfΓ cst u decl X X0 isdecl hconst Δ f hf.
    simpl. eapply meta_conv.
    + constructor. all: eauto. apply hf.
    + rewrite rename_subst_instance. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_constant_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl X X0 hconst Δ σ hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf.
    + rewrite rename_subst_instance. f_equal.
      rewrite rename_closed. 2: auto.
      eapply declared_inductive_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl X X0 hconst Δ f hf.
    simpl. eapply meta_conv.
    + econstructor. all: eauto. apply hf.
    + rewrite rename_closed. 2: reflexivity.
      eapply declared_constructor_closed_type. all: eauto.
  - intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl HΣ.
    intros IHΔ ci_npar eqpctx predctx wfp cup wfpctx Hpret IHpret IHpredctx isallowed Her.
    intros IHctxi Hc IHc iscof ptm wfbrs Hbrs Δ f Hf.
    simpl.
    rewrite rename_mkApps.
    rewrite map_app. simpl.
    rewrite /ptm. rewrite rename_it_mkLambda_or_LetIn.
    assert (#|predctx| = #|pcontext p|) as predctx_len by now rewrite case_predicate_context_length //.
    rewrite predctx_len rename_predicate_preturn.
    rewrite rename_case_predicate_context //.
    eapply type_Case; eauto; simpl; rewrite - ?rename_case_predicate_context //.
    3,4: constructor; eauto; rewrite - ?rename_case_predicate_context //.
    + eapply IHpret.
      split.
      * apply All_local_env_app_inv in IHpredctx as [].
        eapply wf_local_app_renaming; eauto.
      * rewrite -predctx_len.
        eapply urenaming_context_xpredT.
        apply Hf.
    + unfold id.
      specialize (IHc _ _ Hf).
      now rewrite rename_mkApps map_app in IHc.
    + now eapply rename_wf_predicate.
    + simpl. eauto.
      apply All_local_env_app_inv in IHpredctx as [].
      eapply wf_local_app_renaming; eauto.
    + revert IHctxi.
      rewrite /= /id -map_app.
      rewrite -{2}[subst_instance _ _](rename_closedn_ctx f 0).
      { pose proof (declared_inductive_closed_pars_indices isdecl).
        now rewrite closedn_subst_instance_context. }
      rewrite rename_context_telescope.
      rewrite rename_telescope_shiftn0.
      clear -Δ f Hf.
      induction 1.
      { constructor; auto. }
      { destruct t0; simpl. rewrite rename_telescope_cons.
        constructor; cbn; eauto.
        now rewrite rename_subst_telescope /= in IHIHctxi. }
      { simpl. rewrite rename_telescope_cons.
        constructor; cbn; eauto.
        now rewrite rename_subst_telescope /= in IHIHctxi. }
    + now eapply rename_wf_branches.
    + eapply Forall2_All2 in wfbrs.
      eapply All2i_All2_mix_left in Hbrs; eauto.
      eapply All2i_nth_hyp in Hbrs.
      eapply All2i_map_right, (All2i_impl Hbrs) => i cdecl br.
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
      intros (Hnth & wfbr & eqbctx & IHbctx & (Hbod & IHbod) & Hbty & IHbty).
      rewrite -(rename_closed_constructor_body mdecl cdecl f).
      { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
        split; eauto. }
      split; auto.
      { simpl. rewrite -rename_cstr_branch_context //.
        1:eapply (declared_inductive_closed_params isdecl).
        rewrite rename_closedn_ctx //.
        eapply closed_cstr_branch_context. split; tea. }
      cbn -[case_branch_type].
      rewrite case_branch_type_fst.
      rewrite -rename_case_branch_context_gen //.
      2-3:len.
      1:exact (declared_inductive_closed_params isdecl).
      1:rewrite (wf_branch_length wfbr) //.
      1:rewrite (wf_predicate_length_pars wfp).
      1:now rewrite (declared_minductive_ind_npars isdecl).
      set (brctx' := rename_context f _).
      assert (wf_local Σ (Δ ,,, brctx')).
      { apply All_local_env_app_inv in IHbctx as [].
        eapply wf_local_app_renaming; tea. }
      split => //.
      rewrite rename_case_predicate_context // rename_case_branch_type //.
      split.
      * eapply IHbod => //.
        split => //.
        relativize #|bcontext br|; [eapply urenaming_context_xpredT|].
        1:apply Hf. rewrite case_branch_context_length //.
      * eapply IHbty. split=> //.
        rewrite /brctx' case_branch_type_fst.
        relativize #|bcontext br|; [eapply urenaming_context_xpredT, Hf|len].
        now rewrite case_branch_context_length.
  - intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc e
           Δ f hf.
    simpl. eapply meta_conv.
    + econstructor.
      * eassumption.
      * eapply meta_conv.
        -- eapply ihc; tea.
        -- rewrite rename_mkApps. simpl. reflexivity.
      * rewrite map_length. assumption.
    + rewrite rename_subst0. simpl. rewrite map_rev. f_equal.
      rewrite rename_subst_instance. f_equal.
      rewrite rename_closedn. 2: reflexivity.
      eapply declared_projection_closed_type in isdecl.
      rewrite List.rev_length. rewrite e. assumption.

  - intros Σ wfΣ Γ wfΓ mfix n decl types H1 hdecl X hmfixt ihmfixt hmfixb ihmfixb wffix Δ f hf.
    apply All_local_env_app_inv in X as [_ X].
    eapply wf_local_app_renaming in X; tea.
    simpl. eapply meta_conv.
    + eapply type_Fix.
      * apply hf.
      * destruct hf; eapply fix_guard_rename; eauto.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * apply All_map, (All_impl ihmfixt).
        intros x t. eapply t. eauto.
      * apply All_map, (All_impl ihmfixb).
        unfold on_def_body. rewrite fix_context_length map_length {2}/map_def /=.
        intros x t.
        relativize (lift0 _ _).
        1: eapply t; eauto.
        2: len; now sigma.
        rewrite rename_fix_context.
        split; auto.
        subst types. rewrite -(fix_context_length mfix).
        apply urenaming_context_xpredT; auto. apply hf.
      * now eapply rename_wf_fixpoint.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ mfix n decl types guard hdecl X hmfixt ihmfixt hmfixb ihmfixb wfcofix Δ f hf.
    apply All_local_env_app_inv in X as [_ X].
    eapply wf_local_app_renaming in X; eauto.
    simpl. eapply meta_conv.
    + eapply type_CoFix; auto.
      * apply hf.
      * destruct hf; eapply cofix_guard_rename; eauto.
      * rewrite nth_error_map. rewrite hdecl. simpl. reflexivity.
      * apply All_map, (All_impl ihmfixt).
        intros x t. eapply t. eauto.
      * apply All_map, (All_impl ihmfixb).
        unfold on_def_body. rewrite fix_context_length map_length {2}/map_def /=.
        intros x t.
        relativize (lift0 _ _).
        1: eapply t; eauto.
        2: len; now sigma.
        rewrite rename_fix_context.
        split; auto.
        subst types. rewrite -(fix_context_length mfix).
        apply urenaming_context_xpredT; auto. apply hf.
      * now eapply rename_wf_cofixpoint.
    + reflexivity.

  - intros Σ wfΣ Γ wfΓ p pty cdecl _ hp hdecl pinv ptyp IH Δ f hf.
    cbn. rewrite rename_prim_type /=. econstructor; tea.
    * apply hf.
    * rewrite prim_val_tag_map //.
    * rewrite prim_val_tag_map //.
    * depelim IH; eauto; cbn; constructor; cbn; eauto. solve_all.

  - intros Σ wfΣ Γ wfΓ t A B X hwf ht iht htB ihB cum Δ f hf.
    eapply type_Cumul.
    + eapply iht; tea.
    + eapply ihB; tea.
    + eapply cumulSpec_renameP with (P := xpredT).
      all: try eassumption.
      all: fvs.
      * eapply urenaming_ext; revgoals. 1: apply hf.
        1: reflexivity.
        rewrite shiftnP_xpredT //.
      * destruct hf as [HΔ _]. apply wf_local_closed_context; eauto.
Qed.

Lemma typing_rename_P {Σ Γ Δ f t A} {wfΣ : wf Σ.1} :
  renaming xpredT Σ Γ Δ f ->
  Σ ;;; Γ |- t : A ->
  Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros hf h.
  revert Σ wfΣ Γ t A h Δ f hf.
  apply typing_rename_prop.
Qed.

Lemma typing_rename {Σ Γ Δ f t A} :
  wf Σ.1 -> wf_local Σ Δ ->
  renaming_closed Γ Δ f ->
  Σ ;;; Γ |- t : A ->
  Σ ;;; Δ |- rename f t : rename f A.
Proof.
  intros ? ? hf h.
  eapply typing_rename_P; eauto; split; eauto.
Qed.

End Renaming.
