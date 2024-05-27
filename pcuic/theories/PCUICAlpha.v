(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool CRelationClasses CMorphisms.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics
     PCUICLiftSubst PCUICTyping PCUICWeakeningConv PCUICWeakeningTyp
     PCUICCumulativity PCUICEquality PCUICEqualityLemmas PCUICAlphaDef PCUICClosedTyp
     PCUICConversion PCUICContextConversion PCUICContextConversionTyp
     PCUICValidity PCUICArities PCUICSpine
     PCUICInductives PCUICInductiveInversion PCUICOnFreeVars
     PCUICWellScopedCumulativity PCUICGuardCondition.

From Equations Require Import Equations.

(* Alpha convertible terms and contexts have the same typings *)

Implicit Types cf : checker_flags.

#[global]
Instance upto_names_terms_refl : CRelationClasses.Reflexive (All2 `≡α`).
Proof. intro; apply All2_refl; reflexivity. Qed.

Lemma eq_context_upto_empty_impl {cf} {Σ : global_env_ext} ctx ctx' :
  ctx ≡Γ ctx' ->
  eq_context Σ Σ ctx ctx'.
Proof.
  apply alpha_eq_context_impl_compare_context.
Qed.

Section Alpha.
  Context {cf:checker_flags}.

  (* TODO MOVE *)
  Lemma fix_context_nth_error :
    forall m i d,
      nth_error m i = Some d ->
      nth_error (fix_context m) (#|m| - S i) =
      Some (vass (dname d) (lift0 i (dtype d))).
  Proof using Type.
    intros m i d e.
    rewrite <- fix_context_length.
    unfold fix_context. rewrite List.rev_length.
    rewrite <- nth_error_rev.
    - rewrite nth_error_mapi. rewrite e. simpl. reflexivity.
    - rewrite mapi_length.
      eauto using nth_error_Some_length.
  Qed.

  Lemma decompose_prod_assum_upto_names' ctx ctx' x y :
    ctx ≡Γ ctx' -> x ≡α y ->
    let (ctx0, x0) := decompose_prod_assum ctx x in
    let (ctx1, x1) := decompose_prod_assum ctx' y in
    ctx0 ≡Γ ctx1 × x0 ≡α x1.
  Proof using Type.
    induction x in ctx, ctx', y |- *; intros eqctx eqt; inv eqt; simpl;
      try split; auto; try constructor; auto.
    - specialize (IHx2 (ctx,, vass na x1) (ctx',,vass na' a') b').
      apply IHx2; auto. constructor; auto; repeat split; auto. constructor; auto.
    - apply IHx3; auto. constructor; auto; repeat split; auto. constructor; auto.
  Qed.

  Lemma destInd_spec t :
    match destInd t with
    | Some (ind, u) => t = tInd ind u
    | None => forall ind u, t <> tInd ind u
    end.
  Proof using Type.
    destruct t; congruence.
  Qed.

  Lemma upto_names_destInd t u :
    t ≡α u ->
    rel_option (fun '(ind, u) '(ind', u') => (ind = ind') × u = u')%type (destInd t) (destInd u).
  Proof using Type.
    induction 1; simpl; constructor; try congruence.
    split; auto.
  Qed.

  Lemma alpha_eq_term_mkApps_l_inv u args v :
    mkApps u args ≡α v ->
    ∑ u' args',
      v = mkApps u' args' ×
      u ≡α u' ×
      All2 `≡α` args args'.
  Proof.
  intros h. induction args in u, v, h |- *.
  - cbn in h. exists v, []. split ; auto.
  - cbn in h. apply IHargs in h as [u' [args' (-> & h1 & h2)]].
    depelim h1.
    eexists _, (_ :: args'); repeat split.
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
  Qed.

  Lemma decompose_app_upto_names u v hd args :
    u ≡α v ->
    decompose_app u = (hd, args) ->
    ∑ hd' args', v = mkApps hd' args' ×
    hd ≡α hd' ×
    negb (isApp hd') ×
    All2 `≡α` args args'.
  Proof using Type.
    intros eq dapp.
    pose proof (decompose_app_notApp _ _ _ dapp).
    apply decompose_app_inv in dapp as ->.
    eapply alpha_eq_term_mkApps_l_inv in eq as [u' [l' (-> & eqh & eqtl)]].
    eexists _, _; intuition eauto.
    revert H.
    inv eqh; simpl in *; try discriminate; auto.
  Qed.

  Lemma upto_names_check_fix mfix mfix' :
     All2
      (fun x y : def term =>
        (`≡α` (dtype x) (dtype y) × `≡α` (dbody x) (dbody y))
        × rarg x = rarg y) mfix mfix' ->
      map check_one_fix mfix = map check_one_fix mfix'.
  Proof using Type.
    induction 1; simpl; auto.
    rewrite IHX. f_equal.
    unfold check_one_fix.
    destruct x as [name ty body rarg].
    destruct y as [name' ty' body' rarg'].
    simpl in r. destruct r as [[eqty eqb] eqrarg].
    pose proof (decompose_prod_assum_upto_names' [] [] ty ty' ltac:(constructor) eqty).
    do 2 destruct decompose_prod_assum.
    destruct X0 as [eqctx eqt].
    apply (alpha_eq_context_smash_context _ _ [] []) in eqctx; try constructor.
    apply All2_rev in eqctx.
    rewrite -eqrarg.
    destruct nth_error eqn:hnth.
    2: { now eapply All2_nth_error_None in hnth as -> => //. }
    eapply All2_nth_error_Some in hnth as (t' & -> & h) => //=; tea.
    destruct h as (eqna & eqbo & eqtyp).
    destruct (decompose_app) eqn:eqdec.
    edestruct decompose_app_upto_names as (hd' & tl' & eq & eqhd & napp & eqtl); revgoals; tea.
    rewrite eq. rewrite decompose_app_mkApps; auto.
    apply upto_names_destInd in eqhd.
    inv eqhd; auto.
    destruct a as [ind u], b as [ind' u']; simpl in *; auto.
    destruct X0 as [-> _]; auto.
  Qed.

  Lemma upto_names_check_cofix mfix mfix' :
    All2 (fun x y : def term =>
     (dtype x ≡α dtype y × dbody x ≡α dbody y)
     × rarg x = rarg y) mfix mfix' ->
   map check_one_cofix mfix = map check_one_cofix mfix'.
  Proof using Type.
    induction 1; simpl; auto.
    rewrite IHX. f_equal.
    unfold check_one_cofix. clear X IHX.
    destruct x as [name ty body rarg].
    destruct y as [name' ty' body' rarg'].
    simpl in r. destruct r as [[eqty eqb] <-].
    pose proof (decompose_prod_assum_upto_names' [] [] ty ty' ltac:(constructor) eqty).
    do 2 destruct decompose_prod_assum.
    destruct X as [_ eqt].
    destruct (decompose_app) eqn:eqdec.
    edestruct decompose_app_upto_names as (hd' & tl' & eq & eqhd & napp & eqtl); revgoals; tea.
    rewrite eq. rewrite decompose_app_mkApps; auto.
    apply upto_names_destInd in eqhd.
    inv eqhd; auto.
    destruct a as [ind u], b as [ind' u']; simpl in *; auto.
    destruct X as [-> _]; auto.
  Qed.

  Import PCUICClosed PCUICOnFreeVars PCUICParallelReduction PCUICConfluence.

  Lemma is_closed_context_app_left Γ Δ :
    is_closed_context (Γ ,,, Δ) ->
    is_closed_context Γ.
  Proof using Type.
    rewrite on_free_vars_ctx_app => /andP[] //.
  Qed.
  Hint Resolve is_closed_context_app_left : fvs.

  Lemma is_closed_context_app_right Γ Δ :
    is_closed_context (Γ ,,, Δ) ->
    on_free_vars_ctx (shiftnP #|Γ| xpred0) Δ.
  Proof using Type.
    rewrite on_free_vars_ctx_app => /andP[] //.
  Qed.
  Hint Resolve is_closed_context_app_right : fvs.
  Hint Constructors All_fold : core.

  Lemma on_free_vars_ctx_All_fold_over P Γ Δ :
    on_free_vars_ctx (shiftnP #|Γ| P) Δ <~>
    All_fold (fun Δ => on_free_vars_decl (shiftnP #|Γ ,,, Δ| P)) Δ.
  Proof using Type.
    split.
    - move/alli_Alli/Alli_rev_All_fold.
      intros a; eapply All_fold_impl; tea. cbn.
      intros Γ' x; now rewrite shiftnP_add app_length.
    - intros a'.
      apply alli_Alli.
      eapply (All_fold_impl (fun Δ d => on_free_vars_decl (shiftnP #|Δ| (shiftnP #|Γ| P)) d)) in a'.
      now apply (All_fold_Alli_rev (fun k => on_free_vars_decl (shiftnP k (shiftnP #|Γ| P))) 0) in a'.
      intros.
      now rewrite shiftnP_add -app_length.
  Qed.

  Lemma All2_fold_All_fold_mix_right A P Q Γ Γ' :
    All_fold P Γ' ->
    @All2_fold A Q Γ Γ' ->
    All2_fold (fun Γ Γ' d d' => P Γ' d' × Q Γ Γ' d d') Γ Γ'.
  Proof using Type.
    induction 1 in Γ |- *; intros H; depelim H; constructor; auto.
  Qed.

  Lemma All2_fold_All_right A P Γ Γ' :
    All2_fold (fun _ Γ _ d => P Γ d) Γ Γ' ->
    @All_fold A P Γ'.
  Proof using Type.
    induction 1; constructor; auto.
  Qed.

  Lemma All_decls_alpha_pb_ws_decl {le P} {Γ : context} {d d'} :
    (forall le t t', is_open_term Γ t -> is_open_term Γ t' -> `≡α` t t' -> P le t t') ->
    alpha_eq_decl d d' ->
    ws_decl Γ d ->
    ws_decl Γ d' ->
    All_decls_alpha_pb le P d d'.
  Proof using Type.
    intros HP (eqna & eqb & eqty); cbn.
    destruct d as [na [b|] ty], d' as [na' [b'|] ty']; depelim eqb;
      try now (constructor; eauto).
    move/andP=> [] /= clb clT /andP[] => clb' clT'.
    constructor; auto.
  Qed.

  Lemma eq_context_upto_conv_context_rel {Σ : global_env_ext} {wfΣ : wf Σ} {le} (Γ Δ Δ' : context) :
    is_closed_context (Γ ,,, Δ) ->
    is_closed_context (Γ ,,, Δ') ->
    Δ ≡Γ Δ' ->
    ws_cumul_ctx_pb_rel le Σ Γ Δ Δ'.
  Proof using Type.
    intros cl cl' eq.
    split; eauto with fvs.
    eapply on_free_vars_ctx_All_fold in cl.
    eapply on_free_vars_ctx_All_fold in cl'.
    apply All2_fold_All2 in eq.
    eapply All_fold_app_inv in cl as [onΓ onΔ].
    eapply All_fold_app_inv in cl' as [_ onΔ'].
    eapply All2_fold_All_fold_mix_left in eq; tea.
    eapply All2_fold_All_fold_mix_right in eq; tea.
    cbn in eq.
    eapply All2_fold_impl_ind. tea. cbn.
    intros ???? IH IH' [? [? e]].
    apply All2_fold_prod_inv in IH as [a a'].
    apply All2_fold_prod_inv in a' as [a' a''].
    eapply All2_fold_All_left in a'.
    eapply All2_fold_All_right in a.
    eapply on_free_vars_ctx_All_fold_over in a.
    eapply on_free_vars_ctx_All_fold_over in a'.
    eapply on_free_vars_ctx_All_fold in onΓ.
    move: (on_free_vars_ctx_app xpred0 Γ Γ0).
    rewrite onΓ a' /= => iscl.
    move: (on_free_vars_ctx_app xpred0 Γ Δ0).
    rewrite onΓ a /= => iscl'.
    eapply All_decls_alpha_pb_ws_decl; tea.
    intros. apply ws_cumul_pb_compare => //.
    now apply alpha_eq_term_impl_compare_term.
    rewrite app_length (All2_fold_length IH') -app_length //.
  Qed.


  Lemma eq_context_upto_names_set_binder_name (Γ Δ : context) :
    eq_annots (forget_types Δ) Γ ->
    eq_context_upto_names (map2 set_binder_name (forget_types Δ) Γ) Γ.
  Proof.
    induction 1 => //=.
    constructor; tas.
    destruct y as [?[]?]; constructor; tas.
  Qed.

  Lemma eq_context_upto_names_map2_set_binder_name_alpha pctx pctx' Γ Δ :
    pctx ≡Γ pctx' ->
    Γ ≡Γ Δ ->
    map2 set_binder_name (forget_types pctx) Γ ≡Γ
      map2 set_binder_name (forget_types pctx') Δ.
  Proof using Type.
    intros eqp.
    induction 1 in pctx, pctx', eqp |- *.
    - destruct eqp; cbn; constructor.
    - destruct eqp; simpl; constructor; auto.
      destruct r as (eqna & ? & ?), a as (? & ? & ?).
      repeat split; tas.
  Qed.

  Lemma eq_context_upto_names_map2_set_binder_name Σ cmp_univ' cmp_sort' pb' Ξ pctx pctx' Γ Δ :
    eq_annots (forget_types pctx) Γ ->
    eq_context_upto_names pctx pctx' ->
    eq_context_upto_rel Σ cmp_univ' cmp_sort' pb' Ξ Γ Δ ->
    eq_context_upto_rel Σ cmp_univ' cmp_sort' pb' Ξ
      (map2 set_binder_name (forget_types pctx) Γ)
      (map2 set_binder_name (forget_types pctx') Δ).
  Proof using Type.
    intros eqctx eqp.
    induction 1 in pctx, pctx', eqp, eqctx |- *.
    - destruct eqp; cbn; constructor.
    - destruct eqp; simpl.
      1: constructor.
      have [e0 eqctx'] : (eq_binder_annot (decl_name x) (decl_name d) /\ eq_annots (forget_types l) Γ)
        by depelim eqctx.
      constructor.
      1: now apply IHX.
      apply eq_context_upto_names_set_binder_name in eqctx'. symmetry in eqctx'.
      assert (eq_binder_annot (decl_name x) (decl_name y)) by now destruct e.
      destruct p; constructor; auto; cbn.
      all: eapply eq_term_upto_univ_eq_ctx_upto_names; tea.
      all: apply All2_app; trea.
  Qed.

  Lemma case_predicate_context_equiv {ind mdecl idecl p p'} :
    alpha_eq_predicate `≡α` p p' ->
    case_predicate_context ind mdecl idecl p ≡Γ case_predicate_context ind mdecl idecl p'.
  Proof using Type.
    intros [eqpars [eqinst [eqctx eqret]]].
    rewrite /case_predicate_context /case_predicate_context_gen.
    eapply eq_context_upto_names_map2_set_binder_name_alpha => //.
    1: now apply eq_context_upto_names_alpha_eq_context.
    rewrite /pre_case_predicate_context_gen.
    rewrite -eqinst.
    apply alpha_eq_context_subst.
    1: reflexivity.
    now apply All2_rev.
  Qed.

  Lemma case_branch_context_equiv {ind mdecl p p' bctx bctx' cdecl} :
    alpha_eq_predicate `≡α` p p' ->
    bctx ≡Γ bctx' ->
    (case_branch_context ind mdecl p (forget_types bctx) cdecl) ≡Γ
    (case_branch_context ind mdecl p' (forget_types bctx') cdecl).
  Proof using Type.
    intros [eqpars [eqinst [eqctx eqret]]] eqctx'.
    rewrite /case_branch_context /case_branch_context_gen -eqinst.
    eapply eq_context_upto_names_map2_set_binder_name_alpha; tea.
    rewrite /pre_case_branch_context_gen.
    apply alpha_eq_context_subst; tea; tc.
    1: reflexivity.
    now apply All2_rev.
  Qed.

  Lemma case_branch_type_equiv (Σ : global_env_ext) {ind mdecl idecl p p' br br' ctx ctx' c cdecl} :
    alpha_eq_predicate `≡α` p p' ->
    bcontext br ≡Γ bcontext br' ->
    ctx ≡Γ ctx' ->
    let ptm := it_mkLambda_or_LetIn ctx (preturn p) in
    let ptm' := it_mkLambda_or_LetIn ctx' (preturn p') in
    (case_branch_type ind mdecl idecl p br ptm c cdecl).2 ≡α
      (case_branch_type ind mdecl idecl p' br' ptm' c cdecl).2.
  Proof using Type.
    intros [eqpars [eqinst [eqctx eqret]]] eqbctx eqctx'.
    intros ptm ptm'.
    rewrite /case_branch_type /case_branch_type_gen -eqinst. cbn.
    eapply alpha_eq_term_mkApps. 2: eapply All2_app.
    - eapply alpha_eq_term_lift.
      rewrite /ptm /ptm'.
      now apply alpha_eq_term_it_mkLambda_or_LetIn.
    - eapply All2_map, All2_refl.
      intros.
      apply alpha_eq_term_subst; trea.
      now apply All2_rev.
    - repeat constructor.
      eapply alpha_eq_term_mkApps; trea.
      eapply All2_app; trea.
      solve_all.
      now eapply alpha_eq_term_lift.
  Qed.

  Import PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp.
  Lemma inst_case_predicate_context_eq {Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl p} :
    wf_predicate mdecl idecl p ->
    eq_context_upto_names (ind_predicate_context ind mdecl idecl) (pcontext p) ->
    eq_context_upto_names (case_predicate_context ind mdecl idecl p) (inst_case_predicate_context p).
  Proof using Type.
    intros wfp eq.
    rewrite /case_predicate_context /case_predicate_context_gen.
    epose proof (wf_pre_case_predicate_context_gen wfp).
    etransitivity.
    now apply eq_binder_annots_eq_ctx.
    rewrite /pre_case_predicate_context_gen /inst_case_predicate_context.
    rewrite /inst_case_context.
    eapply eq_context_upto_names_subst_context.
    now eapply eq_context_upto_names_univ_subst_preserved.
  Qed.

  Import PCUICSubstitution.
  Lemma ctx_inst_eq {Σ} {wfΣ : wf Σ.1} {Γ Δ : context} {args args'} :
    wf_local Σ (Γ ,,, List.rev Δ) ->
    PCUICTyping.ctx_inst
          (fun (Γ : context) (u A : term) =>
          forall v : term, `≡α` u v -> Σ;;; Γ |- v : A) Γ args Δ ->
    ctx_inst Σ Γ args Δ ->
    All2 `≡α` args args' ->
    ctx_inst Σ Γ args' Δ.
  Proof using Type.
    intros wf ctxi ctxi' a.
    eapply All2_ctx_inst; tea.
    2:exact ctxi. 2:auto.
    cbn; clear -wfΣ; intros.
    eapply substitution_ws_cumul_ctx_pb.
    now eapply subslet_untyped_subslet.
    now eapply subslet_untyped_subslet.
    eapply All2_rev.
    move/All_local_env_app_inv: X => [] /All_local_env_app_inv[] /wf_local_closed_context clΓ0 _ _.
    eapply subslet_open_terms, All_rev_inv in X0.
    eapply subslet_open_terms, All_rev_inv in X1.
    solve_all. eapply into_ws_cumul_pb; tea.
    constructor. now apply alpha_eq_term_impl_eq_term.
    all:eauto with fvs.
  Qed.

  Lemma ctx_inst_eq_context {P Q Γ Γ' s Δ}:
    (forall Γ Γ' u U, (Γ ≡Γ Γ') -> P Γ u U -> Q Γ' u U) ->
    Γ ≡Γ Γ' ->
    PCUICTyping.ctx_inst P Γ s Δ -> PCUICTyping.ctx_inst Q Γ' s Δ.
  Proof using Type.
    intros HP e.
    induction 1; constructor; eauto.
  Qed.

  Lemma wf_local_eq_context_upto_names {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ Δ'} :
    wf_local Σ (Γ,,, Δ) ->
    eq_context_upto_names Δ' Δ ->
    wf_local Σ (Γ ,,, Δ').
  Proof using Type.
    intros a eq.
    induction eq; depelim a; cbn; try solve [constructor; auto];
    depelim r; subst; constructor; auto.
    all: rewrite e.
    all: apply lift_typing_impl with (1 := l) => ?? Hs.
    all: eapply (closed_context_cumulativity _ (pb:=Conv)); tea; [apply IHeq; pcuic|].
    all: eapply ws_cumul_ctx_pb_rel_app.
    all: eapply eq_context_upto_conv_context_rel; fvs.
    all: now eapply eq_context_upto_names_alpha_eq_context.
  Qed.

  Lemma case_branch_type_eq_context_gen_1 {ind mdecl idecl cdecl p n br} {ctx ctx' ret} :
    (case_branch_type ind mdecl idecl p br
      (it_mkLambda_or_LetIn ctx ret) n cdecl).1 ≡Γ
    (case_branch_type ind mdecl idecl p br
      (it_mkLambda_or_LetIn ctx' ret) n cdecl).1.
  Proof using Type. reflexivity. Qed.

  Lemma case_branch_type_eq_context_gen_2 {ind mdecl idecl cdecl p n br} {ctx ctx' ret} :
    ctx ≡Γ ctx' ->
    (case_branch_type ind mdecl idecl p br
      (it_mkLambda_or_LetIn ctx ret) n cdecl).2 ≡α
    (case_branch_type ind mdecl idecl p br
      (it_mkLambda_or_LetIn ctx' ret) n cdecl).2.
  Proof using Type.
    intros eq.
    rewrite /case_branch_type /=.
    rewrite /case_branch_context_gen /=. cbn.
    eapply alpha_eq_term_mkApps.
    2: reflexivity.
    len. eapply alpha_eq_term_lift.
    apply alpha_eq_term_it_mkLambda_or_LetIn; trea.
  Qed.

  Lemma eq_context_conversion {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ} {t T} :
    Σ ;;; Γ |- t : T ->
    Γ ≡Γ Δ ->
    wf_local Σ Δ ->
    Σ ;;; Δ |- t : T.
  Proof using Type.
    intros.
    eapply closed_context_conversion; tea.
    eapply typing_wf_local in X.
    eapply (eq_context_upto_conv_context_rel []) in X0.
    eapply ws_cumul_ctx_pb_rel_app in X0; tea.
    rewrite !app_context_nil_l in X0. exact X0.
    all:rewrite !app_context_nil_l; fvs.
  Qed.

  Lemma upto_names_conv_context (Σ : global_env_ext) Γ Δ :
    Γ ≡Γ Δ -> conv_context cumulAlgo_gen Σ Γ Δ.
  Proof using Type.
    intro H.
    apply compare_context_cumul_pb_context.
    now eapply eq_context_upto_empty_impl.
  Qed.

  Lemma isType_eq_context_conversion {Σ : global_env_ext} {wfΣ : wf Σ} {Γ Δ} {T} :
    isType Σ Γ T ->
    Γ ≡Γ Δ ->
    wf_local Σ Δ ->
    isType Σ Δ T.
  Proof using Type.
    intros Hty eq wfΔ; apply lift_typing_impl with (1 := Hty); intros ?? Hs.
    now eapply eq_context_conversion.
  Qed.

  Lemma lift_judgment_alpha {Σ : global_env_ext} {Γ tm tm' t t' u r} :
    lift_typing0 (fun t T : term =>
      forall u : term, `≡α` t u -> Σ;;; Γ |- u : T)
      (Judge tm t u r) ->
      match tm', tm with None, _ => unit | Some tm', Some tm => tm ≡α tm' | _, _ => False end ->
    `≡α` t t' ->
    lift_typing typing Σ Γ (Judge tm' t' u r).
  Proof.
    intros tu Htm Hty.
    apply lift_sorting_it_impl_gen with tu => //.
    2: intro HT; now apply HT.
    destruct tm' as [tm'|], tm as [tm|] => // HT.
    specialize (HT _ Htm).
    eapply type_Cumul'; tea.
    { eapply lift_sorting_forget_rel, lift_sorting_forget_univ, lift_sorting_it_impl_gen with tu => // Ht. now apply Ht. }
    now eapply eq_term_upto_univ_cumulSpec, alpha_eq_term_impl_compare_term.
  Qed.

  Lemma typing_alpha_prop :
    env_prop (fun Σ Γ u A =>
      forall Δ v,
        u ≡α v ->
        Γ ≡Γ Δ ->
        Σ ;;; Δ |- v : A)
    (fun Σ Γ j =>
      forall Δ,
      Γ ≡Γ Δ ->
      lift_typing0 (fun t T =>
        forall u, t ≡α u ->
        Σ ;;; Δ |- u : T) j)
    (fun Σ Γ => forall Δ, Γ ≡Γ Δ -> wf_local Σ Δ).
  Proof using Type*.
    eapply typing_ind_env.
    1:{
      intros Σ wfΣ Γ j Hj Δ HΔ.
      apply lift_typing_impl with (1 := Hj); intros ?? [_ IH].
      intros; now apply IH.
    }
    all: intros Σ wfΣ Γ wfΓ.
    - intros _; clear wfΓ. induction 1 using All_local_env_ind1.
      * intros Δ eq; destruct Δ; depelim eq; constructor.
      * intros Δ eq; depelim eq. destruct a as (eqna&?&?).
        apply All_local_env_snoc; eauto.
        rewrite -eqna.
        eapply lift_judgment_alpha with (1 := X _ eq) => //.
        destruct r => //.

    - intros n decl hnth ih Δ v e eqctx; invs e.
      assert (isType Σ Γ (lift0 (S n) (decl_type decl))).
      { eapply validity. econstructor; eauto. }
      specialize (ih _ eqctx).
      eapply All2_nth_error_Some in eqctx as eqd; tea.
      destruct eqd as (decl' & hnth' & eqna & eqbod & eqty).
      eapply type_Cumul.
      eapply type_Rel ; tea.
      eapply eq_context_conversion; tea. eapply X.2.π2.1.
      eapply eq_term_upto_univ_cumulSpec, alpha_eq_term_impl_compare_term.
      apply alpha_eq_term_lift. now symmetry.
    - intros l ih hl Δ v e eqctx; invs e.
      specialize (ih _ eqctx).
      eapply eq_context_conversion; tea.
      eapply type_Sort; assumption.
    - intros na A B s1 s2 ih hA ihA hB ihB Δ v e eqctx; invs e.
      assert (lift_typing typing Σ Δ (j_vass_s na' a' s1)).
      + rewrite -H3.
        eapply lift_judgment_alpha with (1 := ihA _ eqctx) => //.
      + econstructor; tas.
        eapply context_conversion.
        * eapply ihB. assumption. reflexivity.
        * constructor; eauto.
          now eapply lift_sorting_forget_univ.
        * constructor.
          -- now eapply upto_names_conv_context.
          -- constructor. assumption. constructor.
             eapply alpha_eq_term_impl_eq_term. assumption.
    - intros na A t B ih hA ihA hB ihB Δ v e eqctx; invs e.
      eapply type_Cumul'.
      + assert (lift_typing typing Σ Δ (j_vass na' ty')).
        * rewrite -H3.
          eapply lift_judgment_alpha with (1 := ihA _ eqctx) => //.
        * econstructor; eauto.
          eapply eq_context_conversion.
          -- eapply ihB. assumption. reflexivity.
          -- constructor. 2: assumption.
             repeat split; tas.
             constructor; assumption.
          -- constructor; eauto.
      + eapply validity in hB;tea.
        eapply isType_tProd; eauto. split; eauto with pcuic.
        eapply lift_judgment_alpha with (1 := ihA _ eqctx) => //.
        1: reflexivity.
        eapply validity. eapply ihB; eauto.
        constructor; auto. repeat split; trea. constructor ; auto.
      + apply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
        symmetry. constructor; auto.
        all: try (eapply alpha_eq_term_impl_eq_term ; assumption).
        all: reflexivity.
    - intros na b B t A ih hbB ihbB hA ihA Δ v e eqctx; invs e.
      assert (isType Σ Γ (tLetIn na b B A)).
      { eapply validity. econstructor; eauto. }
      eapply type_Cumul'.
      + assert (lift_typing typing Σ Δ (j_vdef na' t' ty')).
        * rewrite -H4.
          eapply lift_judgment_alpha with (1 := ihbB _ eqctx) => //.
        * econstructor; auto.
          eapply eq_context_conversion.
          -- eapply ihA; trea.
          -- constructor; tas. repeat split; tas. constructor; tas.
          -- constructor; auto.
      + apply lift_typing_impl with (1 := X2) => ?? Hs.
        eapply eq_context_conversion; tea. eauto.
      + eapply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
        symmetry; constructor. assumption.
        all: try (eapply alpha_eq_term_impl_eq_term ; assumption).
        all: reflexivity.
    - intros t na A B s u ih hty ihty ht iht hu ihu Δ v e e'; invs e.
      assert (isType Σ Γ (B {0 := s})).
      { eapply validity; econstructor; eauto. }
      eapply type_Cumul'.
      + econstructor; cycle 1.
        * eapply iht; trea.
        * eapply ihu; trea.
        * eapply ihty. reflexivity. auto.
      + apply lift_typing_impl with (1 := X1) => ?? Hs. eapply eq_context_conversion; tea. eauto.
      + eapply eq_term_upto_univ_cumulSpec, eq_term_leq_term.
        symmetry.
        eapply alpha_eq_term_impl_eq_term.
        eapply alpha_eq_term_subst ; now auto.
    - intros cst u decl ? ? hdecl hcons Δ v e e'; invs e.
      constructor; eauto.
    - intros ind u mdecl idecl isdecl ? ? hcons Δ v e e'; invs e.
      econstructor ; eauto.
    - intros ind i u mdecl idecl cdecl isdecl ? ? ? Δ v e e'; invs e.
      econstructor ; eauto.
    - intros ind p c brs args ps mdecl idecl isdecl X X0 H Hpctx cpc wfp
        cup wfpctx Hret IHret
            wfcpc kelim Her HIHctxi Hc IHc iscof ptm wfbrs Hbrs Δ v e e'; invs e.
      have eqp := X1.
      eassert (ctx_inst _ _ _ _) as Hctxi by now eapply ctx_inst_impl with (1 := HIHctxi).
      eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as IHctxi.
      { eapply ctx_inst_impl with (1 := HIHctxi). intros ? ? [? r]. pattern Γ, t, T in r. exact r. }
      destruct X1 as [eqpars [eqinst [eqctx eqret]]].
      assert (wf_predicate mdecl idecl p').
      { destruct wfp. split; auto.
        { now rewrite <-(All2_length eqpars). }
        eapply Forall2_All2 in H1. eapply All2_Forall2.
        eapply All2_sym in eqctx.
        eapply (All2_trans' (@eq_binder_annot name name)); tea.
        2:{ eapply All2_map; tea. eapply All2_impl; tea.
            simpl; intros. destruct X1; simpl; now symmetry. }
        simpl. intros x y [] []; etransitivity; tea. }
      have wfcpc' := wfcpc (Δ ,,, case_predicate_context ind mdecl idecl p').
      forward wfcpc'. { eapply All2_app; auto.
      apply (case_predicate_context_equiv eqp). }
      assert (isType Σ Δ (mkApps ptm (args ++ [c]))).
      { eapply isType_eq_context_conversion. eapply validity. econstructor; eauto.
        constructor; eauto. constructor; eauto.
        solve_all. eapply a0; eauto; reflexivity. all:auto. }
      eapply type_Cumul'; tea.
      + have cu' : consistent_instance_ext Σ (ind_universes mdecl) (puinst p').
        { now rewrite -eqinst. }
        have convctx' : eq_context_upto_names (pcontext p') (ind_predicate_context ind mdecl idecl).
        { etransitivity; tea. now symmetry. }
        assert (eqp' : eq_context_upto_names (inst_case_predicate_context p')
          (case_predicate_context ind mdecl idecl p')).
        { rewrite /inst_case_predicate_context.
          rewrite /case_predicate_context /case_predicate_context_gen in wfcpc.
          symmetry. apply inst_case_predicate_context_eq; tea. now symmetry. }
        assert (wf_local Σ (Δ,,, inst_case_predicate_context p')).
        { eapply wf_local_eq_context_upto_names.
          exact wfcpc'. assumption. }
        have ty' : Σ;;; Δ,,, case_predicate_context ind mdecl idecl p' |- preturn p' : tSort ps.
        { eapply eq_context_conversion. eapply IHret. eauto. reflexivity. all:eauto.
          eapply All2_app; eauto. now eapply case_predicate_context_equiv. }
        have ctxinst' : ctx_inst Σ Δ (pparams p' ++ args)
          (List.rev
             (subst_instance (puinst p') (ind_params mdecl,,, ind_indices idecl))).
        { rewrite -eqinst.
          move: IHctxi => ctxi.
          destruct eqp.
          eapply ctx_inst_eq; tea.
          rewrite List.rev_involutive.
          * eapply weaken_wf_local; tea. now eapply All_local_env_app_inv in X4 as [].
            eapply (on_minductive_wf_params_indices_inst isdecl _ cup).
          * eapply ctx_inst_eq_context; tea. cbn; eauto.
          * eapply ctx_inst_eq_context; tea. cbn; intros; eauto.
            now exact (X6 _ u ltac:(reflexivity) X5).
          * eapply All2_app => //. apply All2_refl => //. reflexivity. }
        have wfbrs' : wf_branches idecl brs'.
        { move/Forall2_All2: wfbrs => wf.
          apply All2_Forall2. eapply All2_trans'; tea.
          intros cdecl br br'.
          intros [wfbr [eqbrctx eqbodies]].
          rewrite /wf_branch.
          red. do 2 red in wfbr.
          eapply Forall2_All2 in wfbr. eapply All2_Forall2.
          eapply All2_map_left.
          eapply All2_map_left_inv in wfbr.
          eapply All2_trans'; tea.
          2:{ eapply All2_symP; tea. tc. }
          intros ??? [[] ?]; try constructor; simpl; auto; now transitivity na'. }
        destruct (All_local_env_app_inv X4) as [wfΔ _].
        assert (clΔ := (wf_local_closed_context wfΔ)).
        econstructor; tea; eauto. 2,3: constructor; tea ; eauto.
        * eapply (type_ws_cumul_pb (pb:=Cumul)).
          eapply IHc; eauto.
          eapply has_sort_isType; eapply isType_mkApps_Ind; tea.
          unshelve eapply (ctx_inst_spine_subst _ ctxinst').
          eapply weaken_wf_local; tea.
          now eapply (on_minductive_wf_params_indices_inst isdecl).
          eapply ws_cumul_pb_eq_le. rewrite -eqinst.
          eapply ws_cumul_pb_mkApps; trea.
          eapply ws_cumul_pb_refl => //. eauto with fvs.
          eapply wf_local_closed_context in wfΓ.
          eapply isType_is_open_term in X1.
          rewrite on_free_vars_mkApps in X1. move/andP: X1 => [] _.
          rewrite forallb_app => /andP[] hargs hc.
          eapply All2_app.
          2:{ eapply eq_terms_ws_cumul_pb_terms => //.
              now eapply wf_local_closed_context in wfΔ. }
          eapply ctx_inst_closed, All_app in Hctxi as []; eauto.
          eapply ctx_inst_closed, All_app in ctxinst' as []; eauto.
          eapply eq_terms_ws_cumul_pb_terms => //.
          rewrite (All2_length e') in a, a0.
          solve_all. now eapply closedn_on_free_vars.
          solve_all. now eapply closedn_on_free_vars.
          eapply (All2_impl eqpars).
          intros. now eapply alpha_eq_term_impl_eq_term.
        * eapply All2i_All2_mix_left in Hbrs; tea.
          2:now eapply Forall2_All2 in wfbrs.
          epose proof (wf_case_branches_types' (p:=p') ps args brs' isdecl) as a.
          forward a.
          { eapply has_sort_isType; eapply isType_mkApps_Ind; tea.
            unshelve eapply (ctx_inst_spine_subst _ ctxinst').
            eapply weaken_wf_local; tea.
            eapply (on_minductive_wf_params_indices_inst isdecl _ cu'). }
          specialize (a H0). cbn in a.
          forward a.
          { eapply eq_context_conversion; tea.
            eapply All2_app; auto. reflexivity.
            eapply eq_context_upto_names_alpha_eq_context. now symmetry. }
          do 2 forward a by auto.
          eapply (All2i_All2_All2i_All2i Hbrs X3 a).
          intros n cdecl br br' [wfbr [wfbrctx wfbrty]].
          destruct wfbrty as (IHbrctx & (Hbbody & IHbbody) & (Hbty & IHbty)).
          intros [eqbctx eqbodies] [wfbr' wfcpars wfcparsn wfcbctx Hbr'ty].
          split; intuition auto.
          etransitivity. symmetry. exact eqbctx. assumption.
          eapply eq_context_upto_names_alpha_eq_context in eqbctx.
          assert (cbreq := case_branch_context_equiv (ind:=ind) (mdecl:=mdecl) (cdecl:=cdecl) eqp eqbctx).
          rewrite case_branch_type_fst.
          intuition auto.
          { eapply type_Cumul. eapply IHbbody; auto.
            eapply All2_app; auto. eapply Hbr'ty.
            eapply eq_term_upto_univ_cumulSpec, alpha_eq_term_impl_compare_term.
            rewrite /ptm /cpc. eapply case_branch_type_equiv; auto.
            now eapply case_predicate_context_equiv. }


      + apply eq_term_upto_univ_cumulSpec, alpha_eq_term_impl_compare_term.
        symmetry.
        apply alpha_eq_term_mkApps; tea.
        * eapply alpha_eq_term_it_mkLambda_or_LetIn; tas.
          now eapply case_predicate_context_equiv.
        * eapply All2_app. 1: apply All2_refl; reflexivity.
          repeat constructor. assumption.

    - intros p c u mdecl idecl cdecl pdecl isdecl args X X0 hc ihc H Δ v e e'; invs e.
      eapply type_Cumul'.
      + econstructor. all: try eassumption.
        eapply ihc; tea.
      + eapply validity ; eauto.
        econstructor ; eauto.
        eapply eq_context_conversion; tea; pcuic.
      + apply eq_term_upto_univ_cumulSpec, alpha_eq_term_impl_compare_term.
        symmetry.
        eapply alpha_eq_term_subst ; auto; try reflexivity.
        constructor ; auto.
        eapply All2_refl. reflexivity.

    - intros mfix n decl types hguard hnth hwf hmfix ihmfix hmfixb ihmfixb wffix Δ v e e'; invs e.
      eapply All2_nth_error_Some in hnth as hnth' ; eauto.
      destruct hnth' as [decl' [hnth' hh]].
      destruct hh as (ety & eqann & ebo & era).
      assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
      { apply PCUICWeakeningTyp.All_mfix_wf; auto.
        eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; constructor; simpl; auto.
        destruct r as (Hty & eqty & eqbod & eqrarg & eqann). rewrite -eqann.
        eapply lift_judgment_alpha with (1 := Hty _ ltac:(reflexivity)) => //. }
      assert (convctx : conv_context cumulAlgo_gen Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')).
      { eapply eq_context_upto_univ_conv_context.
        eapply alpha_eq_context_impl_compare_context.
        apply All2_app; trea.
        now apply alpha_eq_context_fix_context. }
      assert(#|fix_context mfix| = #|fix_context mfix'|).
      { now rewrite !fix_context_length (All2_length X). }
      specialize (hwf (Δ ,,, types)) as hwfΔ.
      forward hwfΔ.
      { apply All2_app; auto. reflexivity. }
      specialize (hwf (Γ ,,, types)).
      forward hwf. { apply All2_app; auto; reflexivity. }
      eapply All_local_env_app_inv in hwfΔ as [].
      eapply eq_context_conversion; tea.
      eapply type_Cumul'.
      + econstructor.
        * assumption.
        * eapply fix_guard_eq_term; eauto.
        * eassumption.
        * eapply (All2_All_mix_left ihmfix) in X.
          clear -X.
          induction X; constructor; simpl; auto.
          destruct r as (Hty & eqty & eqbod & eqrarg & eqann). rewrite /on_def_type -eqann.
          eapply lift_judgment_alpha with (1 := Hty _ ltac:(reflexivity)) => //.
        * unfold alpha_eq_mfixpoint in *. solve_all.
          rewrite /on_def_body -b.
          specialize (b1 (Γ ,,, types)) as IHb.
          forward IHb by eapply All2_app; reflexivity.
          eapply @lift_judgment_alpha with (tm' := Some _) in IHb; tea.
          1: apply lift_typing_impl with (1 := IHb) => t T HT.
          2: { rewrite -H. apply alpha_eq_term_lift; assumption. }
          eapply context_conversion; eauto.
        * revert wffix.
          unfold wf_fixpoint, wf_fixpoint_gen.
          move/andP => [] hm ho.
          apply/andP; split.
          { unfold alpha_eq_mfixpoint in *. solve_all. move: b0 a4.
            generalize (dbody x) (dbody y).
            clear=> t t' isL eq.
            destruct t => //. now depelim eq. }
          move: ho; enough (map check_one_fix mfix = map check_one_fix mfix') as ->; auto.
          apply upto_names_check_fix. unfold alpha_eq_mfixpoint in *. solve_all.
        + eapply isTypeRel_isType. eapply All_nth_error in hmfix; tea.
        + apply eq_term_upto_univ_cumulSpec, alpha_eq_term_impl_compare_term.
          now symmetry.

  - intros mfix n decl types hguard hnth hwf hmfix ihmfix hmfixb ihmfixb wffix Δ v e e'; invs e.
    eapply All2_nth_error_Some in hnth as hnth' ; eauto.
    destruct hnth' as [decl' [hnth' hh]].
    destruct hh as (ety & eqann & ebo & era).
    assert (hwf' : wf_local Σ (Γ ,,, fix_context mfix')).
    { apply PCUICWeakeningTyp.All_mfix_wf; auto.
      eapply (All2_All_mix_left ihmfix) in X.
      clear -X.
      induction X; constructor; simpl; auto.
      destruct r as (Hty & eqty & eqbod & eqrarg & eqann). rewrite -eqann.
      eapply lift_judgment_alpha with (1 := Hty _ ltac:(reflexivity)) => //. }
    assert (convctx : conv_context cumulAlgo_gen Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')).
    { eapply eq_context_upto_univ_conv_context, alpha_eq_context_impl_compare_context.
      eapply All2_app; trea.
      now apply alpha_eq_context_fix_context. }
    assert(#|fix_context mfix| = #|fix_context mfix'|).
    { now rewrite !fix_context_length (All2_length X). }
    specialize (hwf (Δ ,,, types)) as hwfΔ.
    forward hwfΔ.
    { apply All2_app; auto. reflexivity. }
    specialize (hwf (Γ ,,, types)).
    forward hwf. { apply All2_app; auto; reflexivity. }
    eapply All_local_env_app_inv in hwfΔ as [].
    eapply eq_context_conversion; tea.
    eapply type_Cumul'.
    + econstructor.
      * assumption.
      * eapply cofix_guard_eq_term; eauto.
      * eassumption.
      * eapply (All2_All_mix_left ihmfix) in X.
        clear -X.
        induction X; constructor; simpl; auto.
        destruct r as (Hty & eqty & eqbod & eqrarg & eqann). rewrite /on_def_type -eqann.
        eapply lift_judgment_alpha with (1 := Hty _ ltac:(reflexivity)) => //.
      * unfold alpha_eq_mfixpoint in *. solve_all.
        rewrite /on_def_body -b.
        specialize (b1 (Γ ,,, types)) as IHb.
        forward IHb by eapply All2_app; reflexivity.
        eapply @lift_judgment_alpha with (tm' := Some _) in IHb; tea.
        1: apply lift_typing_impl with (1 := IHb) => t T HT.
        2: { rewrite -H. apply alpha_eq_term_lift; assumption. }
        eapply context_conversion; eauto.
      * revert wffix.
        unfold wf_cofixpoint, wf_cofixpoint_gen.
        enough (map check_one_cofix mfix = map check_one_cofix mfix') as ->; auto.
        apply upto_names_check_cofix. unfold alpha_eq_mfixpoint in *. solve_all.
      + eapply isTypeRel_isType. eapply All_nth_error in hmfix; tea.
      + apply eq_term_upto_univ_cumulSpec, alpha_eq_term_impl_compare_term.
        now symmetry.
    - intros p prim_ty cdecl IH prim decl pinv pty ptyIH Δ v e e'.
      depelim e. depelim o. 1-2:econstructor; eauto; constructor.
      pose proof (validity (type_Prim Σ Γ _ _ _ wfΓ prim decl pinv pty)) as (_ & s & Hs & _).
      eapply type_Cumul. econstructor; eauto.
      * depelim ptyIH. constructor; eauto. now rewrite -e. rewrite -e; eauto.
        specialize (hty _ _ a1 e'); eauto. eapply type_Cumul; tea. eapply hdef; eauto.
        now eapply eq_term_upto_univ_cumulSpec, alpha_eq_term_impl_compare_term.
        solve_all.
        specialize (hty _ _ a1 e'); eauto. eapply type_Cumul; tea. eapply a2; eauto.
        now eapply eq_term_upto_univ_cumulSpec, alpha_eq_term_impl_compare_term.
      * eapply eq_context_conversion in Hs; eauto.
      * simp prim_type. eapply Universe.make'_inj in e. rewrite e.
        eapply eq_term_upto_univ_cumulSpec, alpha_eq_term_impl_compare_term.
        constructor. constructor. now symmetry.

    - intros t A B X wf ht iht har ihar hcu Δ v e e'.
      eapply (type_ws_cumul_pb (pb:=Cumul)).
      + eapply iht; tea.
      + eapply has_sort_isType.
        specialize (wf _ e'). now eapply eq_context_conversion.
      + eapply (ws_cumul_pb_ws_cumul_ctx (pb':=Conv)); tea.
        2:eapply PCUICInversion.into_ws_cumul; tea.
        specialize (wf _ e').
        apply wf_conv_context_closed => //.
        apply upto_names_conv_context. now symmetry. pcuic.
  Qed.

  Lemma typing_alpha {Σ : global_env_ext} {Γ u v A} {wfΣ : wf Σ.1} :
    Σ ;;; Γ |- u : A ->
    u ≡α v ->
    Σ ;;; Γ |- v : A.
  Proof using Type.
    intros. eapply (env_prop_typing typing_alpha_prop); eauto. reflexivity.
  Qed.

  Local Ltac inv H := inversion H; subst; clear H.

  Lemma upto_names_eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb napp t u :
    RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
    RelationClasses.PreOrder (cmp_universe Conv) ->
    RelationClasses.PreOrder (cmp_universe pb) ->
    RelationClasses.PreOrder (cmp_sort Conv) ->
    RelationClasses.PreOrder (cmp_sort pb) ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp t u ->
    forall t' u', t ≡α t' -> u ≡α u' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp t' u'.
  Proof using Type.
    intros.
    eapply symmetry, alpha_eq_term_impl in X0; tea.
    eapply alpha_eq_term_impl in X1; tea.
    eapply eq_term_upto_univ_trans; cycle -1.
    eapply eq_term_upto_univ_trans; cycle -1.
    all: tea; tc.
  Qed.

  Lemma upto_names_compare_term Σ φ Γ pb t u t' u'
    : t ≡α t' -> u ≡α u' -> compare_term Σ φ Γ pb t u -> compare_term Σ φ Γ pb t' u'.
  Proof using Type.
    intros; eapply upto_names_eq_term_upto_univ; try eassumption; tc.
  Qed.

  Lemma destArity_alpha Γ u v ctx s :
    destArity Γ u = Some (ctx, s) ->
    u ≡α v ->
    ∑ ctx', destArity Γ v = Some (ctx', s) × ctx ≡Γ ctx'.
  Proof using Type.
    induction u in v, Γ, ctx, s |- *; cbn; try discriminate.
    - intros X Y. destruct v; inv Y. inv X.
      eexists. split; reflexivity.
    - intros X Y. rewrite destArity_app in X.
      case_eq (destArity [] u2); [|intro e; rewrite e in X; discriminate].
      intros [ctx' s'] e; rewrite e in X; cbn in X; inv X.
      destruct v; inv Y.
      eapply IHu2 in e; tea. destruct e as [ctx'' [e1 e2]].
      eexists; split. cbn. rewrite destArity_app e1; reflexivity.
      apply All2_app; tas. constructor; trea.
      repeat split; tas. constructor; auto.
    - intros X Y. rewrite destArity_app in X.
      case_eq (destArity [] u3); [|intro e; rewrite e in X; discriminate].
      intros [ctx' s'] e; rewrite e in X; cbn in X; inv X.
      destruct v; inv Y.
      eapply IHu3 in e; tea. destruct e as [ctx'' [e1 e2]].
      eexists; split. cbn. rewrite destArity_app e1; reflexivity.
      apply All2_app; tas. constructor; trea.
      repeat split; tas. constructor; auto.
  Qed.

  Lemma wf_local_alpha {Σ} {wfΣ : wf Σ.1} {Γ Γ'} :
    wf_local Σ Γ -> Γ ≡Γ Γ' -> wf_local Σ Γ'.
  Proof using Type.
    intros; eapply (env_prop_wf_local typing_alpha_prop); tea.
  Qed.

  Lemma isType_alpha {Σ} {wfΣ : wf Σ.1} Γ u v :
    isType Σ Γ u ->
    u ≡α v ->
    isType Σ Γ v.
  Proof using Type.
    intros Hty eq.
    apply lift_sorting_it_impl_gen with Hty => // Hs.
    eapply typing_alpha; eauto.
  Qed.

  Lemma isType_alpha_ctx {Σ} {wfΣ : wf Σ.1} {Γ Δ u v} :
    isType Σ Γ u ->
    Γ ≡Γ Δ ->
    u ≡α v ->
    isType Σ Δ v.
  Proof using Type.
    intros Hty eqctx eqtm.
    apply lift_sorting_it_impl_gen with Hty => // Hs.
    eapply typing_alpha_prop; eauto.
  Qed.

  Lemma isWfArity_alpha {Σ} {wfΣ : wf Σ.1} {Γ u v} :
    isWfArity Σ Γ u ->
    u ≡α v ->
    isWfArity Σ Γ v.
  Proof using Type.
    intros [isTy [ctx [s X1]]] e.
    eapply destArity_alpha in X1; tea.
    split; [eapply isType_alpha; eauto|].
    destruct X1 as [ctx' [X1 X1']].
    exists ctx', s; auto.
  Qed.

End Alpha.
