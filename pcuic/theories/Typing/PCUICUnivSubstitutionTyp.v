(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect CRelationClasses.
From MetaCoq.Template Require Import utils config Universes uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICOnFreeVars
     PCUICLiftSubst PCUICEquality PCUICUnivSubst
     PCUICCases PCUICContextRelation PCUICCumulativity PCUICTyping PCUICReduction PCUICWeakeningEnvConv PCUICWeakeningEnvTyp
     PCUICClosed PCUICPosition PCUICGuardCondition PCUICUnivSubstitutionConv.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

(** * Universe Substitution lemmas for typing derivations. *)

Local Set Keyed Unification.

Set Default Goal Selector "!".

Local Ltac aa := rdest; eauto with univ_subst.

Section SubstIdentity.
  Context `{cf:checker_flags}.

Lemma convSpec_subst_instance (Σ : global_env_ext) Γ u A B univs :
valid_constraints (global_ext_constraints (Σ.1, univs))
                  (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ |- A =s B ->
  (Σ.1,univs) ;;; subst_instance u Γ |- subst_instance u A =s subst_instance u B.
Proof.
  intros e H. pose proof (He := eq_universe_subst_instance _ _ _ e).
  revert Γ A B H e. 
  eapply (convSpec0_ind_all Σ (eq_universe (global_ext_constraints Σ)) 
            (fun Γ A B => valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
            (Σ.1 , univs) ;;; Γ@[u] |- A@[u] =s B@[u])); intros; cbn ;
            try solve [econstructor; intuition; eauto].
  - rewrite subst_instance_subst. solve [econstructor].
  - rewrite subst_instance_subst. solve [econstructor].
  - rewrite subst_instance_lift. eapply cumul_rel.
    unfold subst_instance.
    unfold option_map in *. destruct (nth_error Γ) eqn:E; inversion H.
    unfold map_context. rewrite nth_error_map E. cbn.
    rewrite map_decl_body. destruct c. cbn in H2. subst.
    reflexivity.
  - rewrite subst_instance_mkApps. cbn.
    rewrite iota_red_subst_instance.
    change (bcontext br) with (bcotext (map_branch (subst_instance u) br)). 
    eapply cumul_iota; eauto with pcuic.
    * rewrite nth_error_map H //.
    * simpl. now len.
  - rewrite !subst_instance_mkApps. cbn.
    eapply cumul_fix.
    + unfold unfold_fix in *. destruct (nth_error mfix idx) eqn:E.
      * inversion H.
        rewrite nth_error_map E. cbn.
        destruct d. cbn in *. cbn in *; try congruence.
        f_equal. f_equal. 
        now rewrite subst_instance_subst fix_subst_instance_subst.
      * inversion H.
    + unfold is_constructor in *.
      destruct (nth_error args narg) eqn:E; inversion H0; clear H0.
      rewrite nth_error_map E. cbn.
     eapply isConstruct_app_subst_instance.
  - rewrite !subst_instance_mkApps.
    unfold unfold_cofix in *. destruct (nth_error mfix idx) eqn:E.
    + inversion H.
    eapply cumul_cofix_case.  fold subst_instance_constr.
    unfold unfold_cofix.
    rewrite nth_error_map E. cbn.
    rewrite subst_instance_subst.
    now rewrite cofix_subst_instance_subst.
    + cbn.
    inversion H.
  - unfold unfold_cofix in *.
    destruct nth_error eqn:E; inversion H.
    rewrite !subst_instance_mkApps.
    eapply cumul_cofix_proj. fold subst_instance.
    unfold unfold_cofix.
    rewrite nth_error_map. destruct nth_error; cbn.
     1: rewrite subst_instance_subst cofix_subst_instance_subst.
    all: now inversion E.
  - rewrite subst_instance_two. solve [econstructor; eauto].
  - rewrite !subst_instance_mkApps.
    eapply cumul_proj. now rewrite nth_error_map H.
  - eapply cumul_Trans; intuition.
    * rewrite on_free_vars_ctx_subst_instance; eauto.
    * rewrite on_free_vars_subst_instance. unfold is_open_term. 
      replace #|Γ@[u]| with #|Γ|; eauto. rewrite map_length; eauto.
  - eapply cumul_Evar. eapply All2_map. 
    eapply All2_impl. 1: tea. cbn; intros. eapply X0.2; eauto.
  - eapply cumul_Case; try solve [intuition; eauto]. 
    * destruct X as [X [Xuni [Xcont [_ Xret]]]]. repeat split; eauto; cbn. 
      + apply All2_map. eapply All2_impl. 1: tea. cbn; intros. eapply X3.2; eauto.
      + apply precompose_subst_instance. eapply R_universe_instance_impl; eauto.   
      + rewrite subst_instance_app inst_case_predicate_context_subst_instance in Xret.
        eapply Xret. eauto.          
    * eapply All2_map. eapply All2_impl. 1: tea. cbn; intros.
      repeat split; eauto; intuition.
      rewrite subst_instance_app inst_case_branch_context_subst_instance in X1; eauto. 
  - eapply cumul_Fix. apply All2_map. eapply All2_impl. 1: tea. 
    cbn; intros; intuition. 
    rewrite subst_instance_app fix_context_subst_instance in X0; eauto. 
  - eapply cumul_CoFix. apply All2_map. eapply All2_impl. 1: tea. 
    cbn; intros; intuition. 
    rewrite subst_instance_app fix_context_subst_instance in X0; eauto. 
  - repeat rewrite subst_instance_mkApps. eapply cumul_Ind.
    * apply precompose_subst_instance_global. cbn. 
      rewrite map_length. eapply R_global_instance_impl_same_napp; eauto.
      all: eapply eq_universe_subst_instance; eauto.
    * eapply All2_map. eapply All2_impl. 1: tea. cbn; intros.
      eapply X0.2; eauto.
      - repeat rewrite subst_instance_mkApps. eapply cumul_Construct.
      * apply precompose_subst_instance_global. cbn. 
        rewrite map_length. eapply R_global_instance_impl_same_napp; eauto.
        all: eapply eq_universe_subst_instance; eauto.
      * eapply All2_map. eapply All2_impl. 1: tea. cbn; intros.
        eapply X0.2; eauto.
    - eapply cumul_Const. apply precompose_subst_instance.
      eapply R_universe_instance_impl; eauto. 
Defined. 

Lemma cumulSpec_subst_instance (Σ : global_env_ext) Γ u A B univs :
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ |- A <=s B ->
  (Σ.1,univs) ;;; subst_instance u Γ
                   |- subst_instance u A <=s subst_instance u B.
Proof.
  intros e H. unfold cumulSpec.  
  set (Rle' := leq_universe (global_ext_constraints (Σ.1,univs))). 
  set (Re := eq_universe (global_ext_constraints Σ)).
  pose proof (Hle := leq_universe_subst_instance _ _ _ e).
  pose proof (Hee := eq_universe_subst_instance _ _ _ e).
  assert (He : subrelation Re
          (fun x y : Universe.t => Rle' x@[u] y@[u])).
  { etransitivity; try apply leq_universe_subst_instance; eauto.
    apply eq_universe_leq_universe.  }
  pose proof (He_ := He). pose proof (Hle_ := Hle).  
  revert Hle_ He_. fold Rle'. generalize Rle'. unfold Rle' in *; clear Rle'; intros Rle' Hle_ He_.
  revert Γ A B H Rle' Hle_ He_ e. 
  eapply (cumulSpec0_ind_all Σ (eq_universe (global_ext_constraints Σ)) 
            (fun Rle Γ A B => forall (Rle' : _ -> _ -> Prop), subrelation Rle
            (fun x y : Universe.t_ => Rle' x@[u] y@[u]) ->
            subrelation (eq_universe Σ)
                        (fun x y : Universe.t_ => Rle' x@[u] y@[u]) ->
            valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
               cumulSpec0 Σ (eq_universe (global_ext_constraints (Σ.1,univs))) Rle' Γ@[u] A@[u] B@[u]))
             with (Rle := leq_universe (global_ext_constraints Σ))  ; intros; cbn ;
            try solve [econstructor; intuition; eauto].
  - rewrite subst_instance_subst. solve [econstructor].
  - rewrite subst_instance_subst. solve [econstructor].
  - rewrite subst_instance_lift. eapply cumul_rel.
    unfold subst_instance.
    unfold option_map in *. destruct (nth_error Γ) eqn:E; inversion H.
    unfold map_context. rewrite nth_error_map E. cbn.
    rewrite map_decl_body. destruct c. cbn in H2. subst.
    reflexivity.
  - rewrite subst_instance_mkApps. cbn.
    rewrite iota_red_subst_instance.
    change (bcontext br) with (bcotext (map_branch (subst_instance u) br)). 
    eapply cumul_iota; eauto with pcuic.
    * rewrite nth_error_map H //.
    * simpl. now len.
  - rewrite !subst_instance_mkApps. cbn.
    eapply cumul_fix.
    + unfold unfold_fix in *. destruct (nth_error mfix idx) eqn:E.
      * inversion H.
        rewrite nth_error_map E. cbn.
        destruct d. cbn in *. cbn in *; try congruence.
        f_equal. f_equal. 
        now rewrite subst_instance_subst fix_subst_instance_subst.
      * inversion H.
    + unfold is_constructor in *.
      destruct (nth_error args narg) eqn:E; inversion H0; clear H0.
      rewrite nth_error_map E. cbn.
     eapply isConstruct_app_subst_instance.
  - rewrite !subst_instance_mkApps.
    unfold unfold_cofix in *. destruct (nth_error mfix idx) eqn:E.
    + inversion H.
    eapply cumul_cofix_case.  fold subst_instance_constr.
    unfold unfold_cofix.
    rewrite nth_error_map E. cbn.
    rewrite subst_instance_subst.
    now rewrite cofix_subst_instance_subst.
    + cbn.
    inversion H.
  - unfold unfold_cofix in *.
    destruct nth_error eqn:E; inversion H.
    rewrite !subst_instance_mkApps.
    eapply cumul_cofix_proj. fold subst_instance.
    unfold unfold_cofix.
    rewrite nth_error_map. destruct nth_error; cbn.
     1: rewrite subst_instance_subst cofix_subst_instance_subst.
    all: now inversion E.
  - rewrite subst_instance_two. solve [econstructor; eauto].
  - rewrite !subst_instance_mkApps.
    eapply cumul_proj. now rewrite nth_error_map H.
  - eapply cumul_Trans; intuition.
    * rewrite on_free_vars_ctx_subst_instance; eauto.
    * rewrite on_free_vars_subst_instance. unfold is_open_term. 
      replace #|Γ@[u]| with #|Γ|; eauto. rewrite map_length; eauto.
  - eapply cumul_Evar. eapply All2_map. 
    eapply All2_impl. 1: tea. cbn; intros. eapply X2.2; eauto.
  - eapply cumul_Case; try solve [intuition; eauto]. 
    * destruct X as [X [Xuni [Xcont [_ Xret]]]]. repeat split; eauto; cbn. 
      + apply All2_map. eapply All2_impl. 1: tea. cbn; intros. eapply X5.2; eauto.
      + apply precompose_subst_instance. eapply R_universe_instance_impl; eauto.   
      + rewrite subst_instance_app inst_case_predicate_context_subst_instance in Xret.
        eapply Xret; eauto.           
    * eapply All2_map. eapply All2_impl. 1: tea. cbn; intros.
      repeat split; eauto; intuition.
      rewrite subst_instance_app inst_case_branch_context_subst_instance in b; eauto. 
  - eapply cumul_Fix. apply All2_map. eapply All2_impl. 1: tea. 
    cbn; intros; intuition. 
    rewrite subst_instance_app fix_context_subst_instance in a0; eauto. 
  - eapply cumul_CoFix. apply All2_map. eapply All2_impl. 1: tea. 
    cbn; intros; intuition. 
    rewrite subst_instance_app fix_context_subst_instance in a0; eauto. 
 - repeat rewrite subst_instance_mkApps. eapply cumul_Ind.
    * apply precompose_subst_instance_global.  
      rewrite map_length. eapply R_global_instance_impl_same_napp; try eapply H; eauto.
    * eapply All2_map. eapply All2_impl. 1: tea. cbn; intros.
      eapply X2.2; eauto.
 - repeat rewrite subst_instance_mkApps. eapply cumul_Construct.
    * apply precompose_subst_instance_global. cbn. 
      rewrite map_length. eapply R_global_instance_impl_same_napp; try eapply H; eauto.
    * eapply All2_map. eapply All2_impl. 1: tea. cbn; intros.
      eapply X2.2; eauto.
  - eapply cumul_Const. apply precompose_subst_instance.
    eapply R_universe_instance_impl; eauto. 
Defined. 

Lemma conv_decls_subst_instance (Σ : global_env_ext) {Γ Γ'} u univs d d' :
  valid_constraints (global_ext_constraints (Σ.1, univs))
    (subst_instance_cstrs u Σ) ->
  conv_decls Σ Γ Γ' d d' ->
  conv_decls (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ')
    (subst_instance u d) (subst_instance u d').
Proof.
  intros valid Hd; depelim Hd; constructor; tas;
    eapply convSpec_subst_instance; tea.
Qed.

Lemma cumul_decls_subst_instance (Σ : global_env_ext) {Γ Γ'} u univs d d' :
  valid_constraints (global_ext_constraints (Σ.1, univs))
    (subst_instance_cstrs u Σ) ->
  cumul_decls Σ Γ Γ' d d' ->
  cumul_decls (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ')
    (subst_instance u d) (subst_instance u d').
Proof.
  intros valid Hd; depelim Hd; constructor; tas;
    (eapply convSpec_subst_instance || eapply cumulSpec_subst_instance); tea.
Qed.

Lemma conv_ctx_subst_instance (Σ : global_env_ext) {Γ Γ'} u univs :
  valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
  conv_context Σ Γ Γ' ->
  conv_context (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ').
Proof.
  intros valid.
  intros; eapply All2_fold_map, All2_fold_impl; tea => ? ? d d'.
  now eapply conv_decls_subst_instance.
Qed.

Lemma subst_instance_context_equality_rel (Σ : global_env_ext) {Γ Γ'} u univs :
  valid_constraints (global_ext_constraints (Σ.1, univs)) (subst_instance_cstrs u Σ) ->
  cumul_context Σ Γ Γ' ->
  cumul_context (Σ.1, univs) (subst_instance u Γ) (subst_instance u Γ').
Proof.
  intros valid.
  intros; eapply All2_fold_map, All2_fold_impl; tea => ? ? d d'.
  now eapply cumul_decls_subst_instance.
Qed.

Hint Resolve subst_instance_cstrs_two
     satisfies_equal_sets satisfies_subsets : univ_subst.
Hint Resolve monomorphic_global_constraint monomorphic_global_constraint_ext : univ_subst. 
Hint Unfold CS.For_all : univ_subst.
Hint Resolve consistent_ext_trans : univ_subst.
Hint Resolve consistent_instance_valid_constraints : univ_subst.
Hint Rewrite subst_instance_extended_subst : substu.
Hint Rewrite expand_lets_subst_instance : substu.
Hint Rewrite subst_instance_subst_context subst_instance_lift_context
  subst_instance_lift subst_instance_mkApps
  subst_instance_subst
  subst_instance_it_mkProd_or_LetIn
  subst_instance_it_mkLambda_or_LetIn
  subst_instance_inds
  : substu.
Ltac substu := autorewrite with substu.
Hint Rewrite subst_instance_expand_lets_ctx : substu.
Hint Resolve subst_instance_wf_predicate
  subst_instance_wf_branch subst_instance_wf_branches : pcuic.
Hint Resolve All_local_env_over_subst_instance : univ_subst.
Hint Resolve declared_inductive_wf_ext_wk declared_inductive_wf_global_ext : pcuic.


Lemma typing_subst_instance :
  env_prop (fun Σ Γ t T => forall u univs,
                wf_ext_wk Σ ->
                sub_context_set (monomorphic_udecl Σ.2)
                                (global_ext_context_set (Σ.1, univs)) ->
                consistent_instance_ext (Σ.1, univs) Σ.2 u ->
                (Σ.1,univs) ;;; subst_instance u Γ
                |- subst_instance u t : subst_instance u T)
          (fun Σ Γ => forall u univs,
          wf_ext_wk Σ ->
          sub_context_set (monomorphic_udecl Σ.2)
                          (global_ext_context_set (Σ.1, univs)) ->
          consistent_instance_ext (Σ.1, univs) Σ.2 u ->
          wf_local(Σ.1,univs) (subst_instance u Γ)).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; cbn  -[Universe.make] in *.
  - rewrite /subst_instance /=.
    induction 1.
    + constructor.
    + simpl. constructor; auto.
      exists (subst_instance_univ u tu.π1). eapply p; auto.
    + simpl. constructor; auto.
      ++ exists (subst_instance_univ u tu.π1). eapply p0; auto.
      ++ apply p; auto.

  - intros n decl eq X u univs wfΣ' H Hsub. rewrite subst_instance_lift.
    rewrite map_decl_type. econstructor; aa.
    unfold subst_instance, map_context.
    now rewrite nth_error_map eq.
  - intros l X Hl u univs wfΣ' HSub H.
    rewrite subst_instance_univ_super.
    + econstructor.
      * aa.
      * now apply wf_universe_subst_instance.
  - intros n t0 b s1 s2 X X0 X1 X2 X3 u univs wfΣ' HSub H.
    rewrite product_subst_instance; aa. econstructor.
    + eapply X1; eauto.
    + eapply X3; eauto.
  - intros n t0 b s1 bty X X0 X1 X2 X3 u univs wfΣ' HSub H.
    econstructor.
    + eapply X1; aa.
    + eapply X3; aa.
  - intros n b b_ty b' s1 b'_ty X X0 X1 X2 X3 X4 X5 u univs wfΣ' HSub H.
    econstructor; eauto. eapply X5; aa.
  - intros t0 na A B s u X X0 X1 X2 X3 X4 X5 u0 univs wfΣ' HSub H.
    rewrite subst_instance_subst. cbn. econstructor.
    + eapply X1; eauto.
    + eapply X3; eauto.
    + eapply X5; eauto.
  - intros. rewrite subst_instance_two. econstructor; [aa|aa|].
    clear X X0; cbn in *.
    eapply consistent_ext_trans; eauto.
  - intros. rewrite subst_instance_two. econstructor; [aa|aa|].
    clear X X0; cbn in *.
    eapply consistent_ext_trans; eauto.
  - intros. eapply meta_conv. 1: econstructor; aa.
    clear.
    unfold type_of_constructor; cbn.
    rewrite subst_instance_subst. f_equal.
    + unfold inds. induction #|ind_bodies mdecl|. 1: reflexivity.
      cbn. now rewrite IHn.
    + symmetry; apply subst_instance_two.

  - intros ci p c brs args u mdecl idecl isdecl hΣ hΓ indnp eqpctx wfp cup
      wfpctx pty Hpty Hcpc kelim
      Hctxi IHctxi Hc IHc notCoFinite wfbrs hbrs i univs wfext Hsub cu.
    rewrite subst_instance_mkApps subst_instance_it_mkLambda_or_LetIn map_app.
    cbn.
    change (subst_instance i (preturn p)) with (preturn (subst_instance i p)).
    change (subst_instance i (pcontext p)) with (pcontext (subst_instance i p)).
    change (map_predicate _ _ _ _ _) with (subst_instance i p).
    rewrite subst_instance_case_predicate_context.
    eapply type_Case with (p0:=subst_instance i p)
                          (ps:=subst_instance_univ i u); eauto with pcuic.
    3,4: constructor; eauto with pcuic.                                              
    + rewrite -subst_instance_case_predicate_context - !subst_instance_app_ctx.
      eapply Hpty; eauto. 
    + eapply IHc in cu => //.
      now rewrite subst_instance_mkApps map_app in cu.
    + simpl. eapply consistent_ext_trans; tea.
    + now rewrite -subst_instance_case_predicate_context -subst_instance_app_ctx.
    + destruct Hsub.
      cbn in *.
      eapply is_allowed_elimination_subst_instance; aa.
    + move: IHctxi. simpl.
      rewrite -subst_instance_app.
      rewrite -subst_instance_two_context.
      rewrite -[List.rev (subst_instance i _)]map_rev.
      clear -wfext Hsub cu. induction 1; cbn; constructor; simpl; eauto.
      all:now rewrite -(subst_instance_subst_telescope i [_]).
    + rewrite -{1}(map_id (ind_ctors idecl)).
      eapply All2i_map. eapply All2i_impl; eauto. 
      cbn -[case_branch_type case_branch_context subst_instance].
      intros k cdecl br [hctx [hbod [hcbctx [ihbod [hbty ihbty]]]]].
      rewrite case_branch_type_fst.
      rewrite - !subst_instance_case_branch_context - !subst_instance_app_ctx.
      rewrite -subst_instance_case_predicate_context subst_instance_case_branch_type.
      repeat split; auto.
      * specialize (ihbod i univs wfext Hsub cu).
        cbn. eapply ihbod.
      * specialize (ihbty i univs wfext Hsub cu).
        cbn. eapply ihbty.
  - intros p c u mdecl idecl cdecl pdecl isdecl args X X0 X1 X2 H u0 univs wfΣ' HSub H0.
    rewrite subst_instance_subst. cbn.
    rewrite !subst_instance_two.
    rewrite {4}/subst_instance /subst_instance_list /=.
    rewrite map_rev.
    econstructor; eauto. 2:now rewrite map_length.
    eapply X2 in H0; tas. rewrite subst_instance_mkApps in H0.
    eassumption.

  - intros mfix n decl H H0 H1 X X0 wffix u univs wfΣ' HSub.
    rewrite (map_dtype _ (subst_instance u)). econstructor.
    + specialize (H1 u univs wfΣ' HSub H2).
      rewrite subst_instance_app in H1.
      now eapply wf_local_app_inv in H1 as [].
    + now eapply fix_guard_subst_instance.
    + rewrite nth_error_map H0. reflexivity.
    + apply All_map, (All_impl X); simpl; intuition auto.
      destruct X1 as [s Hs]. exists (subst_instance_univ u s).
      now apply Hs.
    + eapply All_map, All_impl; tea.
      intros x [X1 X3]. 
      specialize (X3 u univs wfΣ' HSub H2). 
      rewrite (map_dbody (subst_instance u)) in X3.
      rewrite subst_instance_lift in X3.
      rewrite fix_context_length ?map_length in X0, X1, X3.
      rewrite (map_dtype _ (subst_instance u) x) in X3.
      rewrite subst_instance_app in X3.
      rewrite <- (fix_context_subst_instance u mfix). len.
      eapply X3.
    + red; rewrite <- wffix.
      unfold wf_fixpoint.
      rewrite map_map_compose.
      now rewrite subst_instance_check_one_fix.

      - intros mfix n decl H H0 H1 X X0 wffix u univs wfΣ' HSub.
      rewrite (map_dtype _ (subst_instance u)). econstructor.
      + specialize (H1 u univs wfΣ' HSub H2).
        rewrite subst_instance_app in H1.
        now eapply wf_local_app_inv in H1 as [].
      + now eapply cofix_guard_subst_instance.
      + rewrite nth_error_map H0. reflexivity.
      + apply All_map, (All_impl X); simpl; intuition auto.
        destruct X1 as [s Hs]. exists (subst_instance_univ u s).
        now apply Hs.
      + eapply All_map, All_impl; tea.
        intros x [X1 X3]. 
        specialize (X3 u univs wfΣ' HSub H2). 
        rewrite (map_dbody (subst_instance u)) in X3.
        rewrite subst_instance_lift in X3.
        rewrite fix_context_length ?map_length in X0, X1, X3.
        rewrite (map_dtype _ (subst_instance u) x) in X3.
        rewrite subst_instance_app in X3.
        rewrite <- (fix_context_subst_instance u mfix). len.
        eapply X3.
      + red; rewrite <- wffix.
        unfold wf_cofixpoint.
        rewrite map_map_compose.
        now rewrite subst_instance_check_one_cofix.
      
  - intros t0 A B X X0 X1 X2 X3 X4 cum u univs wfΣ' HSub H.
    econstructor.
    + eapply X2; aa.
    + eapply X4; aa.
    + destruct HSub. eapply cumulSpec_subst_instance; aa.
Qed.

Lemma typing_subst_instance' Σ φ Γ t T u univs :
  wf_ext_wk (Σ, univs) ->
  (Σ, univs) ;;; Γ |- t : T ->
  sub_context_set (monomorphic_udecl univs) (global_ext_context_set (Σ, φ)) ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, φ) ;;; subst_instance u Γ
            |- subst_instance u t : subst_instance u T.
Proof.
  intros X X0 X1.
  eapply (typing_subst_instance (Σ, univs)); tas. apply X.
Qed.

Lemma typing_subst_instance_wf_local Σ φ Γ u univs :
  wf_ext_wk (Σ, univs) ->
  wf_local (Σ, univs) Γ ->
  sub_context_set (monomorphic_udecl univs) (global_ext_context_set (Σ, φ)) ->
  consistent_instance_ext (Σ, φ) univs u ->
  wf_local (Σ, φ) (subst_instance u Γ).
Proof.
  intros X X0 X1.
  eapply (env_prop_wf_local typing_subst_instance (Σ, univs)); tas. 1: apply X.
Qed.

Lemma typing_subst_instance'' Σ φ Γ t T u univs :
  wf_ext_wk (Σ, univs) ->
  (Σ, univs) ;;; Γ |- t : T ->
  sub_context_set (monomorphic_udecl univs) (global_context_set Σ) ->
  consistent_instance_ext (Σ, φ) univs u ->
  (Σ, φ) ;;; subst_instance u Γ
            |- subst_instance u t : subst_instance u T.
Proof.
  intros X X0 X1.
  eapply (typing_subst_instance (Σ, univs)); tas. 1: apply X.
  etransitivity; tea. apply global_context_set_sub_ext.
Qed.

Lemma typing_subst_instance_ctx (Σ : global_env_ext) Γ t T ctx u :
  wf Σ.1 ->
  on_udecl_prop Σ (Polymorphic_ctx ctx) ->
  (Σ.1, Polymorphic_ctx ctx) ;;; Γ |- t : T ->
  consistent_instance_ext Σ (Polymorphic_ctx ctx) u ->
  Σ ;;; subst_instance u Γ
            |- subst_instance u t : subst_instance u T.
Proof.
  destruct Σ as [Σ φ]. intros X X0 X1.
  eapply typing_subst_instance''; tea.
  - split; tas.
  - simpl. unfold sub_context_set. split; simpl.
    * intros x hx. now eapply LS.empty_spec in hx.
    * intros x hx. now eapply CS.empty_spec in hx. 
Qed.

Lemma typing_subst_instance_decl Σ Γ t T c decl u :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  (Σ.1, universes_decl_of_decl decl) ;;; Γ |- t : T ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  Σ ;;; subst_instance u Γ
            |- subst_instance u t : subst_instance u T.
Proof.
  destruct Σ as [Σ φ]. intros X X0 X1 X2.
  eapply typing_subst_instance''; tea.
  - split; tas.
    eapply weaken_lookup_on_global_env'; tea.
  - eapply weaken_lookup_on_global_env''; tea.
Qed.




Lemma wf_local_instantiate_poly {Σ ctx Γ u} : 
  wf_ext (Σ.1, Polymorphic_ctx ctx) ->
  consistent_instance_ext Σ (Polymorphic_ctx ctx) u ->
  wf_local (Σ.1, Polymorphic_ctx ctx) Γ -> 
  wf_local Σ (subst_instance u Γ).
Proof.
  intros wfΣ Huniv wf.
  epose proof (type_Sort _ _ Universes.Universe.lProp wf) as ty. forward ty.
  - now simpl.
  - eapply typing_subst_instance_ctx in ty;   
    eauto using typing_wf_local. 
    * apply wfΣ.
    * destruct wfΣ. now eapply on_udecl_on_udecl_prop.
Qed.

Lemma wf_local_instantiate {Σ} {decl : global_decl} {Γ u c} : 
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_local (Σ.1, universes_decl_of_decl decl) Γ -> 
  wf_local Σ (subst_instance u Γ).
Proof.
  intros wfΣ Hdecl Huniv wf.
  epose proof (type_Sort _ _ Universes.Universe.lProp wf) as ty. forward ty.
  - now simpl.
  - eapply typing_subst_instance_decl in ty;   
    eauto using typing_wf_local.
Qed.

Lemma isType_subst_instance_decl Σ Γ T c decl u :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  isType (Σ.1, universes_decl_of_decl decl) Γ T ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  isType Σ (subst_instance u Γ) (subst_instance u T).
Proof.
  intros wfΣ look [s Hs] cu.
  exists (subst_instance u s). 
  now eapply (typing_subst_instance_decl _ _ _ (tSort _)).
Qed.

Lemma isArity_subst_instance u T :
  isArity T ->
  isArity (subst_instance u T).
Proof.
  induction T; cbn; intros; tauto.
Qed.

Lemma wf_local_subst_instance Σ Γ ext u :
  wf_global_ext Σ.1 ext ->
  consistent_instance_ext Σ ext u ->
  wf_local (Σ.1, ext) Γ ->
  wf_local Σ (subst_instance u Γ).
Proof.
  destruct Σ as [Σ φ]. intros X X0 X1. simpl in *.
  induction X1; cbn; constructor; auto.
  - destruct t0 as [s Hs]. hnf.
    eapply typing_subst_instance'' in Hs; eauto; apply X.
  - destruct t0 as [s Hs]. hnf.
    eapply typing_subst_instance'' in Hs; eauto; apply X.
  - hnf in t1 |- *.
    eapply typing_subst_instance'' in t1; eauto; apply X.
Qed.

Lemma wf_local_subst_instance_decl Σ Γ c decl u :
  wf Σ.1 ->
  lookup_env Σ.1 c = Some decl ->
  wf_local (Σ.1, universes_decl_of_decl decl) Γ ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  wf_local Σ (subst_instance u Γ).
Proof.
  destruct Σ as [Σ φ]. intros X X0 X1 X2.
  induction X1; cbn; constructor; auto.
  - destruct t0 as [s Hs]. hnf.
    eapply typing_subst_instance_decl in Hs; eauto.
  - destruct t0 as [s Hs]. hnf.
    eapply typing_subst_instance_decl in Hs; eauto.
  - hnf in t1 |- *.
    eapply typing_subst_instance_decl in t1; eauto.
Qed.

  Lemma subst_instance_ind_sort_id Σ mdecl ind idecl :
    wf Σ ->
    declared_inductive Σ ind mdecl idecl ->
    let u := abstract_instance (ind_universes mdecl) in
    subst_instance_univ u (ind_sort idecl) = ind_sort idecl.
  Proof.
    intros wfΣ decli u.
    pose proof (on_declared_inductive decli) as [onmind oib].
    pose proof (onArity oib) as ona.
    rewrite (oib.(ind_arity_eq)) in ona.
    red in ona. destruct ona.
    eapply typed_subst_abstract_instance in t.
    2:split; simpl; auto.
    - rewrite !subst_instance_it_mkProd_or_LetIn in t.
      eapply (f_equal (destArity [])) in t.
      rewrite !destArity_it_mkProd_or_LetIn in t. simpl in t. noconf t.
      simpl in H; noconf H. apply H0.
    - destruct decli as [declm _].
      eapply declared_inductive_wf_global_ext in declm; auto.
      destruct declm. apply w.
  Qed.

  Lemma subst_instance_ind_type_id Σ mdecl ind idecl :
    wf Σ ->
    declared_inductive Σ ind mdecl idecl ->
    let u := abstract_instance (ind_universes mdecl) in
    subst_instance u (ind_type idecl) = ind_type idecl.
  Proof.
    intros wfΣ decli u.
    pose proof (on_declared_inductive decli) as [_ oib].
    pose proof (onArity oib) as ona.
    rewrite (oib.(ind_arity_eq)) in ona |- *.
    red in ona. destruct ona.
    eapply typed_subst_abstract_instance in t; eauto.
    destruct decli as [declm _].
    eapply declared_inductive_wf_global_ext in declm; auto.
    destruct declm. apply w.
  Qed.

  Lemma isType_subst_instance_id Σ Γ T :
    wf_ext_wk Σ ->
    let u := abstract_instance Σ.2 in
    isType Σ Γ T -> subst_instance u T = T.
  Proof.
    intros wf_ext u isT.
    destruct isT. eapply typed_subst_abstract_instance in t; auto.
  Qed.

End SubstIdentity.