From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICRelevance
  PCUICClosedTyp PCUICGlobalEnv
  PCUICTyping PCUICInversion PCUICConversion PCUICCumulProp PCUICWeakeningTyp PCUICWellScopedCumulativity
  PCUICInductives PCUICInductiveInversion.

Require Import ssreflect.
From Equations Require Import Equations.

Definition relevance_from_term_from_type {cf : checker_flags} (Σ : global_env_ext) Γ t T :=
  forall rel, isTermRel Σ (marks_of_context Γ) t rel <~> isTypeRel Σ Γ T rel.

Lemma cumul_sort_relevance {cf : checker_flags} (Σ : global_env_ext) Γ T s1 s2 :
  wf Σ ->
  Σ ;;; Γ |- T : tSort s1 -> Σ ;;; Γ |- T : tSort s2 -> relevance_of_sort s1 = relevance_of_sort s2.
Proof.
  intros wfΣ Hs1 Hs2.
  enough (eq_univ_prop s1 s2). 1: by now destruct s1, s2.
  unshelve eapply cumul_prop_sort; tea.
  eapply typing_leq_term_prop with (pb := Conv) (n := 0).
  all: tea.
  reflexivity.
Qed.

Lemma isTypeRel2_relevance {cf : checker_flags} Σ Γ T rel1 rel2 :
  wf Σ.1 ->
  isTypeRel Σ Γ T rel1 -> isTypeRel Σ Γ T rel2 -> rel1 = rel2.
Proof.
  intros wfΣ (_ & s1 & Hty1 & _ & <-) (_ & s2 & Hty2 & _ & <-).
  now eapply cumul_sort_relevance.
Qed.

Definition lift_term_rel_type {cf : checker_flags} (Σ : global_env) Γ (j : judgment) :=
  option_default (fun t => lift_rel (isTermRel Σ (marks_of_context Γ)) t (j_rel j)) (j_term j) (unit : Type) ×
  isTermRel Σ (marks_of_context Γ) (j_typ j) rel_of_Type.

Lemma All_local_env_lift_term_rel_type_subst_context {cf : checker_flags} (Σ : global_env) (wfΣ : wf Σ) Γ Γ' s Δ :
  PCUICSubstitution.marks_subslet Σ (marks_of_context Γ) s (marks_of_context Γ') ->
  All_local_env (lift_term_rel_type Σ) (Γ ,,, Γ' ,,, Δ) ->
  All_local_env (lift_term_rel_type Σ) (Γ ,,, subst_context s 0 Δ).
Proof.
  intros Hs X.
  apply All_local_env_app_inv in X as (X1 & X2).
  apply All_local_env_app_inv in X1 as (X0 & X1).
  apply All_local_env_app; tas.
  induction X2 using All_local_env_ind1.
  1: constructor.
  rewrite subst_context_snoc.
  apply All_local_env_snoc; eauto.
  destruct decl as [na bo ty], X as (onb & onty); split; cbn in *.
  - destruct bo as [b|] => //=.
    destruct onb as (_ & onb & <-).
    eexists; split; cbnr.
    rewrite !marks_of_context_app mark_fold_context_k Nat.add_0_r -{2}(app_context_nil_l (marks_of_context Γ)) -marks_of_context_length in onb |- *.
    eapply PCUICSubstitution.subst_isTermRel; tea.
    all: rewrite app_context_nil_l //; tea.
  - rewrite !marks_of_context_app mark_fold_context_k Nat.add_0_r -{2}(app_context_nil_l (marks_of_context Γ)) -marks_of_context_length in onty |- *.
    eapply PCUICSubstitution.subst_isTermRel; tea.
    all: rewrite app_context_nil_l //; tea.
Qed.

Lemma ctx_inst_to_rel {cf : checker_flags} {Σ : global_env_ext} {Γ} {Δ : context} {args} :
  wf Σ ->
  wf_local Σ (Γ ,,, List.rev Δ) ->
  PCUICEnvTyping.ctx_inst (fun (Γ : context) (t T : term) => Σ;;; Γ |- t : T ×
    (forall rel, isTypeRel Σ Γ T rel -> isTermRel Σ (marks_of_context Γ) t rel)) Γ args Δ ->
  ctx_inst_rel (isTermRel Σ (marks_of_context Γ)) args Δ.
Proof.
  intros wfΣ wfΓ.
  induction Δ using PCUICInduction.ctx_length_ind in args, wfΓ |- *; cbn.
  1: intro X; depelim X; constructor.
  rewrite /= in wfΓ.
  pose proof wfΓ as wfΓΔ. rewrite app_context_assoc in wfΓΔ.
  apply All_local_env_app_inv in wfΓ as (wfΓ & wfΓ').
  apply All_local_rel_app_inv in wfΓ' as (wfd & wfΔ).
  intro X0; depelim X0.
  - depelim wfd.
    eapply p in l as Hrel.
    constructor; eauto.
    eapply X; eauto.
    + now len.
    + rewrite -PCUICSpine.subst_context_rev_subst_telescope.
      eapply @PCUICSubstitution.substitution_wf_local; eauto.
      repeat constructor.
      rewrite PCUICLiftSubst.subst_empty. apply p.
  - depelim wfd.
    constructor; eauto.
    eapply X; eauto.
    + now len.
    + rewrite -PCUICSpine.subst_context_rev_subst_telescope.
      eapply @PCUICSubstitution.substitution_wf_local; eauto.
      rewrite -{1}(PCUICLiftSubst.subst_empty 0 b).
      repeat constructor.
      rewrite !PCUICLiftSubst.subst_empty. eapply unlift_TermTyp, l.
Qed.

Lemma relevance_type_to_term_mfix {cf : checker_flags} Σ Γ types mfix :
  All (on_def_type (lift_term_rel_type Σ) Γ) mfix ->
  All (on_def_body (lift_term_rel_type Σ) types Γ) mfix ->
  wfTermRel_mfix isTermRel Σ (marks_of_context Γ) (marks_of_context types) mfix.
Proof using Type.
  intros.
  unfold wfTermRel_mfix, on_def_body, on_def_type, lift_term_rel_type in *.
  solve_all.
  destruct a as (_ & a & <-).
  rewrite -marks_of_context_app //.
Qed.

Lemma global_isTypeRel_inj {cf : checker_flags} Σ (wfΣ : wf Σ.1) cst decl Γ u ty rel rel' :
  wf_local Σ Γ ->
  lookup_env Σ.1 cst = Some decl ->
  consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
  isTypeRel (Σ.1, universes_decl_of_decl decl) [] ty rel ->
  isTypeRel Σ Γ ty@[u] rel' ->
  rel = rel'.
Proof.
  intros wfΓ isdecl h_cuu X X'.
  eapply isTypeRel2_relevance; tea.
  eapply isTypeRel_weaken; tas.
  eapply PCUICUnivSubstitutionTyp.isTypeRel_subst_instance_decl with (Γ := []); tea.
Qed.

Lemma constant_isTypeRel_inj {cf : checker_flags} Σ (wfΣ : wf Σ.1) Γ cst u decl rel :
  wf_local Σ Γ ->
  declared_constant Σ.1 cst decl ->
  consistent_instance_ext Σ (cst_universes decl) u ->
  isTypeRel Σ Γ (cst_type decl)@[u] rel ->
  cst_relevance decl = rel.
Proof.
  intros wfΓ isdecl h_cuu X.
  eapply global_isTypeRel_inj with (decl := ConstantDecl decl); tea.
  1: unshelve eapply declared_constant_to_gen in isdecl as isdecl'; eauto.
  apply PCUICWeakeningEnvTyp.on_declared_constant in isdecl; tea.
  now apply lift_sorting_forget_body in isdecl.
Qed.

Lemma ind_isTypeRel_inj {cf : checker_flags} Σ (wfΣ : wf Σ.1) Γ ind u mdecl idecl rel :
  wf_local Σ Γ ->
  declared_inductive Σ.1 ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isTypeRel Σ Γ (ind_type idecl)@[u] rel ->
  rel_of_Type = rel.
Proof.
  intros wfΓ isdecl h_cuu X.
  eapply global_isTypeRel_inj with (decl := InductiveDecl mdecl); tea.
  1: unshelve eapply declared_inductive_to_gen in isdecl as isdecl'; eauto.
  apply PCUICWeakeningEnvTyp.on_declared_inductive in isdecl as (_ & []); tea.
Qed.


Lemma relevance_type_to_term {cf : checker_flags} :
  env_prop (fun Σ Γ t T => forall rel, isTypeRel Σ Γ T rel -> isTermRel Σ (marks_of_context Γ) t rel)
    lift_term_rel_type
    (fun Σ Γ => All_local_env (lift_term_rel_type Σ) Γ).
Proof using Type.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps; auto.
  - destruct X as (Htm & s & (Hty & IHty) & e & Hr).
    split.
    + destruct j_term => //=; cbn in *.
      exists (relevance_of_sort s).
      split. 2: destruct j_rel => //=; apply Hr.
      apply Htm.
      repeat eexists; tea.
    + apply IHty.
      repeat eexists.
      1: now eapply PCUICWfUniverses.sort_type_super.
      apply relevance_super.

  - constructor. rewrite nth_error_map heq_nth_error /option_map.
    f_equal. eapply isTypeRel2_relevance; eauto.
    eapply All_local_env_nth_error in wfΓ as Hty; tea. cbn in Hty.
    apply lift_sorting_forget_body in Hty.
    apply isTypeRel_lift in Hty => //.
    pose proof (nth_error_Some_length heq_nth_error); lia.

  - destruct X0 as (_ & s & Hty & _ & <-) => //. cbn in Hty.
    apply inversion_Sort in Hty as (_ & _ & le) => //.
    eapply ws_cumul_pb_Sort_inv, leq_relevance in le => //.
    rewrite le relevance_super. constructor.

  - destruct X4 as (_ & s & Hty & _ & <-) => //. cbn in Hty.
    destruct X1 as (_ & X1). cbn in X1.
    apply inversion_Sort in Hty as (_ & _ & le) => //.
    eapply ws_cumul_pb_Sort_inv, leq_relevance in le => //.
    rewrite le relevance_super. constructor.
    1: assumption.
    apply forall_rel.
    repeat eexists.
    1: now eapply PCUICWfUniverses.sort_type_super.
    apply relevance_super.

  - destruct X4 as (_ & s & Hty & _ & <-) => //. cbn in Hty.
    destruct X1 as (_ & X1). cbn in X1.
    constructor; tas.
    apply forall_rel.
    apply inversion_Prod in Hty as (s1 & s2 & e1 & Hty & le) => //.
    repeat (eexists; tea).
    eapply ws_cumul_pb_Sort_inv, leq_relevance in le as -> => //.
    apply relevance_product.

  - destruct X4 as (_ & s & Hty & _ & <-) => //. cbn in Hty.
    apply PCUICWfUniverses.typing_wf_sort in Hty as wfs; tas.
    destruct X1 as ((r & X1a & <-) & X1). cbn in X1a, X1.
    constructor; tas.
    apply forall_rel.
    apply inversion_LetIn in Hty as (s' & _ & Hty & le) => //.
    eapply ws_cumul_pb_Sort_r_inv in le as (ss & red & le) => //.
    repeat (eexists; tea). cbn.
    econstructor; eauto with pcuic. 1: constructor; eauto with pcuic.
    eapply cumul_Trans. 4: apply cumul_Sort, le. 1,2: rewrite ?PCUICOnFreeVars.closedn_ctx_on_free_vars; now fvs.
    apply cumulAlgo_cumulSpec.
    apply invert_red_letin in red as [(? & ? & ? & []) | ?]; try discriminate.
    unshelve epose proof (PCUICSpine.all_rels_subst_lift (Γ := Γ) (Δ := [vdef na b b_ty]) (t := s') (Δ' := []) _ _ _) => //=.
    all: change (Γ ,,, [_]) with (Γ ,, vdef na b b_ty). pcuic. fvs. fvs.
    rewrite /= PCUICLiftSubst.lift0_id PCUICLiftSubst.subst_empty in X2.
    change (subst0 _ _) with ((lift 1 1 s') {0 := lift0 1 b}) in X2.
    rewrite -PCUICLiftSubst.distr_lift_subst10 in X2.
    apply PCUICContextConversion.ws_cumul_pb_eq_le in X2.
    etransitivity. 1: apply X2.
    change (tSort ss) with (lift0 1 (tSort ss)).
    eapply red_conv in c.
    eapply (weakening_ws_cumul_pb (Γ' := []) (Γ'' := [vdef _ _ _]) c). fvs.

  - destruct X6 as (_ & s' & Hty & _ & <-) => //. cbn in Hty.
    apply PCUICWfUniverses.typing_wf_sort in Hty as wfs; tas.
    apply PCUICValidity.validity in typeu as IHA.
    pose proof (lift_sorting_extract_rel IHA).
    econstructor; tas. 2: now apply forall_rel1.
    apply forall_rel0.
    repeat (eexists; tea). cbn.
    apply inversion_Prod in IHB as (s1 & s2 & _ & HT & le) => //.
    eapply (PCUICSubstitution.substitution0 HT) in typeu; tea. cbn in typeu.
    transitivity (relevance_of_sort s2).
    2: eapply cumul_sort_relevance; tea.
    apply ws_cumul_pb_Sort_inv in le. rewrite -(leq_relevance_eq le) relevance_product //.

  - enough (cst_relevance decl = rel) by (subst rel; constructor => //).
    eapply constant_isTypeRel_inj; eassumption.

  - enough (rel_of_Type = rel) by (subst rel; constructor => //).
    eapply ind_isTypeRel_inj; eassumption.

  - enough (idecl.(ind_relevance) = rel) by (subst rel; econstructor; apply isdecl).
    destruct Σ as (Σ & φ).
    assert (isTypeRel (Σ, φ) _ (type_of_constructor mdecl cdecl (ind, i) u) (idecl.(ind_relevance))) by (apply isType_of_constructor; tea).
    eapply isTypeRel2_relevance; tea.

  - assert (rel = ci.(ci_relevance)) as ->. {
    eapply isTypeRel2_relevance; tea.
    repeat (eexists; tea). 2: instantiate (1 := ps); eassumption.
    apply PCUICInductiveInversion.apply_predctx => //. eapply ctx_inst_impl with (1 := X5) => ??[] //. }

    econstructor; tea.
    + split; [|split]; tas.
      2: {
        rewrite -marks_of_context_app; apply forall_rel.
        repeat (eexists; tea).
        1: now eapply PCUICWfUniverses.sort_type_super.
        apply relevance_super.
      }
      rewrite PCUICUnivSubstitutionConv.subst_instance_app_ctx List.rev_app_distr in X5.
      apply PCUICSpine.ctx_inst_app_inv_1 in X5.
      replace (context_assumptions (List.rev (ind_params mdecl)@[puinst p])) with (#|pparams p|) in X5.
      2: {
        rewrite context_assumptions_rev context_assumptions_subst_instance.
        destruct H0 as (-> & _).
        now unshelve eapply PCUICWeakeningEnvTyp.on_declared_inductive in isdecl as ([] & _).
      }
      rewrite -(Nat.add_0_r #|pparams p|) firstn_app_2 firstn_0 // app_nil_r in X5.
      apply ctx_inst_to_rel; eauto.
      all: rewrite List.rev_involutive.
      * apply weaken_wf_local; eauto.
        eapply PCUICArities.on_minductive_wf_params; tea.
        apply isdecl.
    + eapply All2i_All2 with (1 := X8).
      intros i ctor br (eqctx & IHctx & (Hbod & IHbod) & (Hty & IHty)).
      repeat split; tas.
      rewrite -marks_of_context_app.
      apply IHbod.
      repeat eexists; tea.
    + apply forall_rel0.
      eapply isTypeRel_mkApps_Ind; tea.
      unshelve eapply PCUICSpine.ctx_inst_spine_subst.
      { now eapply ctx_inst_impl with (1 := X5) => ??[]//. }
      eapply weaken_wf_local; tea.
      now eapply (on_minductive_wf_params_indices_inst isdecl).
  - assert (isTypeRel Σ Γ (subst0 (c :: List.rev args) (proj_type pdecl)@[u]) (pdecl.(proj_relevance)))
      by (eapply PCUICInductiveInversion.isTypeRel_projection; tea).
    assert (isTypeRel Σ Γ (mkApps (tInd (proj_ind p) u) args) idecl.(ind_relevance)). {
      apply PCUICValidity.validity in typec.
      epose proof (isType_mkApps_Ind_inv_spine wf isdecl wfΓ typec) as [subst [? ? ? cu]].
      eapply isTypeRel_mkApps_Ind; tea.
      now apply isdecl.
    }
    enough (pdecl.(proj_relevance) = rel).
    1: { subst rel. econstructor; tea. eauto. }
    eapply isTypeRel2_relevance; tea.
  - assert (rel = decl.(dname).(binder_relevance)) as ->.
    { eapply isTypeRel2_relevance; tea. now eapply All_nth_error in X0. }
    constructor; tea.
    now apply relevance_type_to_term_mfix.
  - assert (rel = decl.(dname).(binder_relevance)) as ->.
    { eapply isTypeRel2_relevance; tea. now eapply All_nth_error in X0. }
    constructor; tea.
    now apply relevance_type_to_term_mfix.
  - move: H1 X2.
    destruct p as [[] pv]; depelim pv; cbn in X0 |- *; simp prim_type => //=.
    3: depelim X0; depelim X1.
    all: intros [hty_cst _ hrel hu] hty'; eenough (rel = _) as H; [rewrite H; do 2 econstructor|].
    + eapply isTypeRel2_relevance; tea.
      eapply has_sort_isTypeRel with (s := Sort.type0) => //.
      change (tSort Sort.type0) with (tSort Sort.type0)@[[]].
      rewrite -hty_cst.
      eapply type_Const; tea. unfold consistent_instance_ext, consistent_instance. rewrite hu //.
    + eapply isTypeRel2_relevance; tea.
      eapply has_sort_isTypeRel with (s := Sort.type0) => //.
      change (tSort Sort.type0) with (tSort Sort.type0)@[[]].
      rewrite -hty_cst.
      eapply type_Const; tea. unfold consistent_instance_ext, consistent_instance. rewrite hu //.
    + apply hty0.
      apply PCUICValidity.validity_sort in hty; apply hty.
    + apply hdef0.
      eapply has_sort_isTypeRel. 2: apply hty.
      reflexivity.
    + solve_all.
      apply b. eapply has_sort_isTypeRel. 2: apply hty.
      reflexivity.
    + eapply isTypeRel2_relevance; tea.
      eapply has_sort_isTypeRel => //.
      change (tSort ?s) with (subst10 (array_type a) (tSort s)).
      eapply type_App; eauto.
      2: replace (tProd _ _ _) with ((tImpl (tSort (sType (Universe.make' (Level.lvar 0)))) (tSort (sType (Universe.make' (Level.lvar 0)))))@[[array_level a]]) by reflexivity.
      { repeat econstructor; cbnr; eauto. }
      rewrite -hty_cst.
      eapply (type_Const _ _ _ [array_level a]); tea.
      red. rewrite hu. simpl. rtoProp; intuition eauto. eapply LevelSet.mem_spec. eapply (wfl (array_level a, 0)). cbn. lsets.
      cbn. red. destruct check_univs => //. red. red. intros v H c. csets.

  - apply forall_rel.
    pose proof typet.
    apply PCUICValidity.validity in X0 as (_ & s' & Hty & _).
    destruct X5 as (_ & s0 & Hty0 & _ & <-).
    eapply has_sort_isTypeRel; tea.
    enough (cumul_prop Σ Γ (tSort s0) (tSort s')).
    { apply PCUICCumulProp.cumul_prop_sort in X0. now destruct s0, s'. }
    pose proof (cumulSpec_typed_cumulAlgo typet typeB cumulA).
    apply ws_cumul_pb_forget, PCUICCumulativity.cumul_alt in X0 as (A' & B' & red1 & red2 & leq).
    eapply PCUICSR.subject_reduction in red1, red2; tea.
    eapply typing_leq_term_prop; tea.
Qed.



Lemma relevance_term_to_type {cf : checker_flags} :
  env_prop (fun Σ Γ t T => forall rel, isTermRel Σ (marks_of_context Γ) t rel -> isTypeRel Σ Γ T rel)
    (fun Σ Γ j => True)
    (fun Σ Γ => True).
Proof using Type.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps; auto.

  - depelim X. rewrite nth_error_map heq_nth_error in e. inv e.
    eapply All_local_env_nth_error in wfΓ as X; tea.
    eapply @lift_typing_weakening with (Γ' := firstn (S n) Γ) in X; tea.
    2: rewrite /app_context firstn_skipn //.
    rewrite /app_context firstn_skipn in X.
    replace #|firstn (S n) Γ| with (S n) in *.
    2: { apply nth_error_Some_length in heq_nth_error. rewrite firstn_length. lia. }
    eapply lift_sorting_forget_body.
    apply X.

  - inv X.
    eapply has_sort_isTypeRel. 1: apply relevance_super.
    constructor; tea. eauto with pcuic.

  - inv X2.
    apply unlift_TypUniv in X. cbn in X.
    eapply has_sort_isTypeRel. 1: apply relevance_super.
    constructor; tea. eauto with pcuic.

  - inv X2.
    eapply forall_rel in X1 as (_ & s & Hs & _ & e). cbn in e.
    pose proof (lift_sorting_extract X).
    eapply has_sort_isTypeRel with (s := Sort.sort_of_product _ _). 1: rewrite relevance_product; eassumption.
    constructor; eassumption.

  - inv X2.
    eapply forall_rel in X3 as (_ & s & Hs & _ & e). cbn in e.
    eapply has_sort_isTypeRel; tea.
    econstructor.
    + eapply type_LetIn; eauto.
    + constructor; eauto with pcuic.
    + do 2 constructor. apply cumul_zeta.

  - inv X5.
    eapply forall_rel0 in X as (_ & s' & Hs & _ & e). cbn in e.
    assert (wf_sort Σ s') by auto with pcuic.
    apply inversion_Prod in Hs as (? & ss & ? & ? & le); tea.
    apply has_sort_isTypeRel with (s := s'); tas.
    econstructor; tea. instantiate (1 := tSort ss). 2: constructor; eauto with pcuic.
    2: { apply cumul_Sort. apply ws_cumul_pb_Sort_inv in le. etransitivity. 1: apply leq_sort_product. eassumption. }
    change (tSort ss) with ((tSort ss) { 0 := u }).
    eapply PCUICSubstitution.substitution0; tea.

  - apply PCUICWeakeningEnvTyp.on_declared_constant in H0 as H'; tea. unfold on_constant_decl in H'.
    inv X0.
    assert (decl = decl0) as <-. { eapply declared_constant_inj; unshelve eapply declared_constant_to_gen; tea. }
    unshelve eapply declared_constant_to_gen in H0; eauto.
    apply isTypeRel_weaken; tea.
    eapply PCUICUnivSubstitutionTyp.isTypeRel_subst_instance_decl with (Γ:=[]); eauto.
    unshelve epose proof (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ (ConstantDecl decl) wf _); eauto.
    now eapply lift_sorting_forget_body.

  - apply PCUICWeakeningEnvTyp.on_declared_inductive in isdecl as H'; tea.
    unshelve eapply declared_inductive_to_gen in isdecl; eauto.
    inv X0.
    eapply isTypeRel_weaken; tea.
    eapply PCUICUnivSubstitutionTyp.isTypeRel_subst_instance_decl with (Γ:=[]); eauto.
    now destruct H' as (H' & []).

  - apply PCUICWeakeningEnvTyp.on_declared_constructor in isdecl as H'; tea.
    inv X0.
    assert (idecl = idecl0) as <-. { unshelve eapply declared_constructor_to_gen in isdecl, H0; eauto. now eapply declared_constructor_inj. }
    now apply isType_of_constructor; eauto.

  - inv X7.
    assert (mdecl = mdecl0 /\ idecl = idecl0) as (<- & <-). { unshelve eapply declared_inductive_to_gen in isdecl, H0; eauto. now eapply declared_inductive_inj. }
    eapply has_sort_isTypeRel; tea.
    apply apply_predctx; eauto.
    eapply ctx_inst_impl with (1 := X3) => ??[] //.

  - inv X2.
    assert (mdecl = mdecl0 /\ idecl = idecl0 /\ cdecl = cdecl0 /\ pdecl = pdecl0) as (<- & <- & <- & <-).
      { unshelve eapply declared_projection_to_gen in isdecl, H0; eauto. now eapply declared_projection_inj. }
    now eapply isTypeRel_projection; tea.

  - inv X3.
    rewrite heq_nth_error in H0; injection H0 as [= <-].
    eapply All_nth_error in X; tea.

  - inv X3.
    rewrite heq_nth_error in H0; injection H0 as [= <-].
    eapply All_nth_error in X; tea.

  - inv X1.
    destruct p as [[] pv]; depelim pv; cbn in X0 |- *; simp prim_type => //=.
    all: depelim H2; depelim X; depelim X2.
    + eapply has_sort_isTypeRel with (s := Sort.type0) => //.
      change (tSort Sort.type0) with (tSort Sort.type0)@[[]].
      rewrite -H0.
      eapply type_Const; tea. unfold consistent_instance_ext, consistent_instance. rewrite H4 //.
    + eapply has_sort_isTypeRel with (s := Sort.type0) => //.
      change (tSort Sort.type0) with (tSort Sort.type0)@[[]].
      rewrite -H0.
      eapply type_Const; tea. unfold consistent_instance_ext, consistent_instance. rewrite H4 //.
    + depelim X0.
      specialize (hdef0 _ hdef1).
      eapply isTypeRel2_relevance in hdef0 as <-; cycle -1. 1: eapply has_sort_isTypeRel, hty.
      all: eauto.
      eapply has_sort_isTypeRel; eauto.
      change (tSort ?s) with (subst10 (array_type a) (tSort s)).
      eapply type_App; eauto.
      2: replace (tProd _ _ _) with ((tImpl (tSort (sType (Universe.make' (Level.lvar 0)))) (tSort (sType (Universe.make' (Level.lvar 0)))))@[[array_level a]]) by reflexivity.
      { repeat econstructor; cbnr; eauto. }
      rewrite -H0.
      eapply (type_Const _ _ _ [array_level a]); tea.
      red. rewrite H4. simpl. rtoProp; intuition eauto. eapply LevelSet.mem_spec. eapply (wfl (array_level a, 0)). cbn. lsets.
      cbn. red. destruct check_univs => //. red. red. intros v H' c. csets.

  - enough (isSortRel s rel) by now eapply has_sort_isTypeRel.
    specialize (forall_rel _ X4) as X.
    destruct X as (_ & s0 & Hty0 & _ & <-).
    enough (cumul_prop Σ Γ (tSort s) (tSort s0)).
    { apply PCUICCumulProp.cumul_prop_sort in X. now destruct s0, s. }
    pose proof (cumulSpec_typed_cumulAlgo typet typeB cumulA).
    apply ws_cumul_pb_forget, PCUICCumulativity.cumul_alt in X as (A' & B' & red1 & red2 & leq).
    eapply PCUICSR.subject_reduction in red1, red2; tea.
    eapply typing_leq_term_prop; tea.
Qed.


Theorem relevance_from_type {cf : checker_flags} (Σ : global_env_ext) Γ t T rel :
  wf Σ -> Σ ;;; Γ |- t : T ->
  isTermRel Σ (marks_of_context Γ) t rel <~> isTypeRel Σ Γ T rel.
Proof.
  intros wfΣ Hty.
  pose proof relevance_term_to_type.
  pose proof relevance_type_to_term.
  eapply env_prop_typing in X, X0; tea.
  now split.
Qed.
