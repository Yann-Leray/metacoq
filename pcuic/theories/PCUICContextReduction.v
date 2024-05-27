(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICTactics
     PCUICLiftSubst PCUICEquality PCUICUnivSubst PCUICInduction
     PCUICReduction PCUICCases PCUICWeakeningConv PCUICWeakeningTyp
     PCUICTyping PCUICClosed PCUICClosedTyp PCUICOnFreeVars PCUICSubstitution
     PCUICRenameDef PCUICRenameConv PCUICInstDef PCUICInstConv.

Require Import ssreflect ssrbool.
Require Import Equations.Prop.DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
Set Equations Transparent.
Set Default Goal Selector "!".

#[local] Instance All_decls_refl P :
  Reflexive P ->
  Reflexive (All_decls P).
Proof using Type.
  intros hP d.
  destruct d as [na [b|] ty]; constructor; auto.
Qed.

#[global] Instance red_context_refl Σ : Reflexive (red_context Σ).
Proof using Type.
  intro Γ.
  apply All2_fold_refl => ? ?.
  reflexivity.
Qed.

Section CtxReduction.
  Context {cf : checker_flags}.
  Context {Σ : global_env}.
  Context (wfΣ : wf Σ).

  Lemma red_prod_alt Γ na M M' N N' :
    red Σ Γ M M' -> red Σ (Γ ,, vass na M') N N' ->
    red Σ Γ (tProd na M N) (tProd na M' N').
  Proof using Type.
    intros. eapply (transitivity (y := tProd na M' N)).
    * now eapply (red_ctx_congr (tCtxProd_l _ tCtxHole _)).
    * now eapply (red_ctx_congr (tCtxProd_r _ _ tCtxHole)).
  Qed.

  Lemma red_context_app_same {Γ Δ Γ'} :
    red_context Σ Γ Δ ->
    red_context Σ (Γ ,,, Γ') (Δ ,,, Γ').
  Proof using Type.
    intros r.
    eapply All2_fold_app => //.
    apply All2_fold_refl => ? ?.
    reflexivity.
  Qed.
  Hint Rewrite inst_case_predicate_context_length : len.

  Lemma on_inst_case_context P Γ pars puinst ctx :
    on_ctx_free_vars P Γ ->
    on_free_vars_ctx (closedP #|pars| xpredT) ctx ->
    forallb (on_free_vars P) pars ->
    on_ctx_free_vars (shiftnP #|ctx| P) (Γ,,, PCUICCases.inst_case_context pars puinst ctx).
  Proof using Type.
    move=> onΓ onctx hpars.
    relativize #|ctx|; [erewrite on_ctx_free_vars_extend, onΓ|now len].
    eapply on_free_vars_ctx_inst_case_context; tea; auto.
  Qed.

  Lemma on_ctx_free_vars_cons P d Γ :
    on_ctx_free_vars P (d :: Γ) =
    on_ctx_free_vars (addnP 1 P) Γ && (P 0 ==> on_free_vars_decl (addnP 1 P) d).
  Proof using Type.
    rewrite (on_ctx_free_vars_app _ _ [_]) on_ctx_free_vars_tip /=.
    bool_congr.
  Qed.

  Lemma red_context_on_ctx_free_vars {P Γ Δ} :
    on_ctx_free_vars P Γ ->
    red_context Σ Γ Δ ->
    on_ctx_free_vars P Δ.
  Proof using wfΣ.
    intros onΓ.
    induction 1 in P, onΓ |- *; auto.
    rewrite on_ctx_free_vars_cons in onΓ.
    rewrite on_ctx_free_vars_cons.
    move/andP: onΓ => [] onΓ ond.
    rewrite (IHX _ onΓ) /=.
    case: (P 0) ond => //=.
    rewrite /on_free_vars_decl /test_decl /=.
    case: p; intros; eauto using red_on_free_vars.
    - move/andP: ond => [] /=; eauto using red_on_free_vars.
    - move/andP: ond => [] /=; eauto using red_on_free_vars.
      intros. apply /andP. eauto using red_on_free_vars.
  Qed.

  Lemma wf_term_red_context {Γ Δ} :
    wf_term_ctx Γ ->
    red_context Σ Γ Δ ->
    wf_term_ctx Δ.
  Proof.
    rewrite !wf_term_ctx_on_ctx_free_vars.
    apply red_context_on_ctx_free_vars.
  Qed.

  Lemma red1_red_ctx Γ Δ t u :
    wf_term_ctx Δ ->
    wf_term t ->
    red1 Σ Γ t u ->
    red_context Σ Δ Γ ->
    red Σ Δ t u.
  Proof using wfΣ.
    move=> onΔ ont r Hctx.
    revert ont Δ onΔ Hctx.
    induction r using red1_ind_all; intros ont Δ onΔ Hctx;
      try inv_wf_term;
      try solve [eapply red_step; repeat (constructor; eauto)].
    - red in Hctx.
      destruct nth_error eqn:hnth => //; simpl in H; noconf H.
      eapply All2_fold_nth_r in Hctx; eauto.
      destruct Hctx as [x' [? ?]].
      destruct p as [cr rd]. destruct c => //; simpl in *.
      depelim rd => //. noconf H.
      eapply red_step.
      * constructor. rewrite e => //.
      * rewrite -(firstn_skipn (S i) Δ).
        eapply weakening_red_0; auto.
        + rewrite firstn_length_le //.
          eapply nth_error_Some_length in e. lia.
        + move: onΔ.
          rewrite -{1}(firstn_skipn (S i) Δ) wf_term_ctx_app.
          move=> /andP [] //.
        + rewrite /wf_term_ctx test_context_forallb in onΔ.
          eapply nth_error_forallb in onΔ; tea. now inv_wf_term.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - eapply red_abs_alt; eauto.
    - eapply red_abs_alt; eauto.
      unshelve eapply IHr; tea.
      2:repeat (constructor; auto).
      rewrite /= onΔ /= //; auto with fvs.
    - eapply red_letin; eauto.
    - eapply red_letin; eauto.
    - unshelve eapply red_letin_alt; eauto.
      eapply IHr; tea.
      2:repeat (constructor; auto).
      rewrite /= onΔ /test_decl /= //; auto with fvs.
    - eapply red_case_pars; eauto; pcuic.
      solve_all. eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_All2; tea => /=; intuition eauto.
    - eapply red_case_p. eapply IHr; tea.
      2:now apply red_context_app_same.
      rewrite wf_term_ctx_app ?onΓ ?onΔ; eapply wf_term_inst_case_context; trea.
    - eapply red_case_c; eauto.
    - eapply red_case_brs.
      unfold on_Trel; pcuic.
      eapply forallb_All in b.
      eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_All2; eauto.
      simpl. intuition eauto. rtoProp.
      eapply b5; revgoals; tea.
      1:now apply red_context_app_same.
      rewrite wf_term_ctx_app ?onΓ ?onΔ; eapply wf_term_inst_case_context; trea.
    - eapply red_proj_c; eauto.
    - eapply red_app; eauto.
    - eapply red_app; eauto.
    - eapply red_prod_alt; eauto.
    - eapply red_prod_alt; eauto.
      eapply IHr; tea.
      * rewrite/= onΔ; auto with fvs.
      * constructor; auto. now constructor.
    - eapply red_evar. simpl in ont.
      solve_all. eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_All2; simpl; eauto. simpl. intuition eauto.
    - eapply red_fix_one_ty.
      apply forallb_All in ont as ont'.
      eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      intuition eauto. move/andP: H0 => [] /=. eauto.
    - eapply red_fix_one_body.
      apply forallb_All in ont as ont'.
      eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto. move/andP: H0 => /= []; intuition eauto.
      eapply X0; tea.
      * now apply wf_term_app_fix_context.
      * now eapply red_context_app_same.
    - eapply red_cofix_one_ty.
      apply forallb_All in ont as ont'.
      eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      move/andP: H0 => []; intuition eauto.
    - eapply red_cofix_one_body.
      apply forallb_All in ont as ont'.
      eapply OnOne2_All_mix_left in X; tea.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto.
      move/andP: H0 => []; intuition auto.
      eapply X0; tea.
      * now apply wf_term_app_fix_context.
      * now eapply red_context_app_same.
    - eapply red_primArray_one_value. toAll. eapply OnOne2_All_mix_left in X; tea. solve_all.
    - eapply red_primArray_default; eauto.
    - eapply red_primArray_type; eauto.
  Qed.

  Lemma red_red_ctx Γ Δ t u :
    wf_term_ctx Δ ->
    wf_term t ->
    red Σ Γ t u ->
    red_context Σ Δ Γ ->
    red Σ Δ t u.
  Proof using wfΣ.
    intros onΔ ont.
    induction 1; eauto using red1_red_ctx.
    intros H.
    transitivity y; eauto.
    eapply IHX2; tea.
    eapply red_wf_term in X1; tea.
    eapply wf_term_red_context; tea.
  Qed.

  Lemma red_context_app {Γ Γ' Δ Δ'} :
    red_context Σ Γ Δ ->
    red_context_rel Σ Γ Γ' Δ' ->
    red_context Σ (Γ ,,, Γ') (Δ ,,, Δ').
  Proof using Type.
    intros r r'.
    eapply All2_fold_app => //.
  Qed.

  Lemma red_context_app_same_left {Γ Γ' Δ'} :
    red_context_rel Σ Γ Γ' Δ' ->
    red_context Σ (Γ ,,, Γ') (Γ ,,, Δ').
  Proof using Type.
    intros h.
    eapply All2_fold_app => //.
    apply red_context_refl.
  Qed.

  Lemma red_context_rel_on_ctx_free_vars {P Γ Δ Δ'} :
    on_ctx_free_vars (addnP #|Δ| P) Γ ->
    on_ctx_free_vars P Δ ->
    red_context_rel Σ Γ Δ Δ' ->
    on_ctx_free_vars P Δ'.
  Proof using wfΣ.
    intros onΓ onΔ.
    induction 1 in onΓ, P, onΔ |- *; auto.
    rewrite /= on_ctx_free_vars_cons in onΔ.
    rewrite on_ctx_free_vars_cons.
    move/andP: onΔ => [] onΔ ond.
    rewrite (IHX _ _ onΔ) /=.
    { rewrite addnP_add Nat.add_1_r //. }
    case: (P 0) ond => //=.
    rewrite /on_free_vars_decl /test_decl /=.
    case: p; intros; eauto using red_on_free_vars.
    - move/andP: ond => [] /=; eauto using red_on_free_vars.
      intros _ ond. eapply red_on_free_vars; tea.
      now rewrite on_ctx_free_vars_app onΔ onΓ.
    - move/andP: ond => [] /=; eauto using red_on_free_vars.
      intros. apply /andP. split.
      * eapply red_on_free_vars; tea.
        now rewrite on_ctx_free_vars_app onΔ onΓ.
      * eapply red_on_free_vars; tea.
        now rewrite on_ctx_free_vars_app onΔ onΓ.
  Qed.

  Definition on_ctx_free_vars_fold P ctx :=
    All_fold (fun Γ d =>
      let k := Nat.pred #|ctx| - #|Γ| in
      P k ==> on_free_vars_decl (addnP (S k) P) d) ctx.

  Lemma addnP_closedP n P : addnP 1 (closedP (S n) P) =1 closedP n (addnP 1 P).
  Proof using Type.
    intros i. rewrite /addnP /closedP /shiftnP /=.
    repeat (PCUICSigmaCalculus.nat_compare_specs => //).
  Qed.

  Lemma red_context_trans Γ Δ Δ' :
    wf_term_ctx Γ ->
    red_context Σ Γ Δ -> red_context Σ Δ Δ' -> red_context Σ Γ Δ'.
  Proof using wfΣ.
    intros onctx H; induction H in onctx, Δ' |- *; auto.
    intros H'; depelim H'.
    move: onctx => /=/andP[] onΓ ond.
    intros.
    constructor; eauto.
    - eapply IHAll2_fold; tea.
    - destruct p; try move/andP: ond => [] onb ont; depelim a; constructor.
      * eapply red_trans; tea.
        eapply red_red_ctx. 3,4:tea. 1: tea.
        eapply red_wf_term; tea; auto with fvs.
      * eapply red_trans; tea.
        eapply red_red_ctx. 3,4:tea. 1:tea.
        eapply red_wf_term; tea; auto with fvs.
      * eapply red_trans; tea.
        eapply red_red_ctx. 3,4:tea. 1:tea.
        eapply red_wf_term; tea; auto with fvs.
  Qed.

  Lemma red_context_app_right {Γ Γ' Δ Δ'} :
    wf_term_ctx (Γ ,,, Γ') ->
    red_context Σ Γ Δ ->
    red_context_rel Σ Δ Γ' Δ' ->
    red_context Σ (Γ ,,, Γ') (Δ ,,, Δ').
  Proof using wfΣ.
    intros onf red red'.
    eapply red_context_trans; tea.
    - eapply red_context_app_same. tea.
    - eapply red_context_app; [apply red_context_refl|tas].
  Qed.

  Lemma red_context_rel_inv {Γ Γ' Δ'} :
    red_context Σ (Γ ,,, Γ') (Γ ,,, Δ') ->
    red_context_rel Σ Γ Γ' Δ'.
  Proof using Type.
    intros r.
    apply All2_fold_length in r as hlen.
    apply All2_fold_app_inv in r as []; tas.
    move: hlen. len.
  Qed.

  (*
    intros onΓ r r'.
    eapply All2_fold_app => //.
    * now rewrite (All2_fold_length r').
    * move: onΓ; rewrite on_ctx_free_vars_app => /andP [] onΓ' onΓ.
      have onΔ := red_context_on_ctx_free_vars onΓ r.
      have onΔ' := red_context_rel_on_ctx_free_vars onΔ onΓ' r'.
      induction r' in P, onΓ, onΔ, onΓ', onΔ' |- *; simpl; constructor; auto.
      - move: onΓ'; rewrite on_ctx_free_vars_cons => /andP[] onΓ0 ond; tea.
        move: onΔ'; rewrite on_ctx_free_vars_cons => /andP[] onΓ'' ond'; tea.
        eapply IHr'; tea.
      - destruct p.
        + constructor.
          move: onΓ'; rewrite on_ctx_free_vars_cons => /andP[] onΓ0 ond; tea.
          move: onΔ'; rewrite on_ctx_free_vars_cons => /andP[] onΓ'' ond'; tea.
          simpl in onΓ, onΔ.
          eapply red_red_ctx.
          5:now eapply red_context_app_same.
          4:tea.
          { rewrite on_ctx_free_vars_app. erewrite onΓ0. now rewrite addnP_add Nat.add_1_r onΔ. }
          { rewrite on_ctx_free_vars_app. erewrite onΓ0. now rewrite addnP_add Nat.add_1_r onΓ. }
  Abort. *)

  Lemma OnOne2_local_env_All2_fold {P Q Γ Δ} :
    OnOne2_local_env P Γ Δ ->
    (forall Γ d d', P Γ d d' -> Q Γ Γ d d') ->
    (forall Γ Δ d, Q Γ Δ d d) ->
    All2_fold Q Γ Δ.
  Proof using Type.
    intros onc HPQ HQ.
    induction onc; try constructor; auto.
    - apply All2_fold_refl => //.
    - apply All2_fold_refl => //.
  Qed.

  Lemma red_context_rel_red_ctx_rel Δ Γ Γ' :
    red_context_rel Σ Δ Γ Γ' -> red_ctx_rel Σ Δ Γ Γ'.
  Proof using wfΣ.
    induction 1; try solve [constructor].
    depelim p.
    - transitivity (Γ ,, vass na t').
      + eapply red_one_decl_red_ctx_rel.
        do 2 constructor; auto.
      + clear -IHX.
        induction IHX; try now do 2 constructor.
        econstructor 3; tea.
    - transitivity (Γ ,, vdef na b' t).
      2: transitivity (Γ ,, vdef na b' t').
      + eapply red_one_decl_red_ctx_rel.
        do 2 constructor; auto.
      + eapply red_one_decl_red_ctx_rel.
        do 2 constructor; auto.
      + clear -IHX.
        induction IHX; try now do 2 constructor.
        econstructor 3; tea.
  Qed.

  Lemma red_ctx_rel_red_context_rel Γ Δ Δ' :
    wf_term_ctx (Γ,,, Δ) ->
    red_ctx_rel Σ Γ Δ Δ' <~> red_context_rel Σ Γ Δ Δ'.
  Proof using wfΣ.
    intros cl.
    split.
    - rewrite /red_ctx_rel /red_context_rel; induction 1.
      * eapply OnOne2_local_env_All2_fold; tea => ? d d'.
        2: reflexivity.
        destruct d as [na [b|] ty], d' as [na' [b'|] ty']; cbn; intuition auto;
          subst; constructor; auto.
      * eapply All2_fold_refl => Δ [na [b|] ty]; constructor; auto; constructor 2.
      * rewrite - !/(red_ctx_rel _ _ _ _) - !/(red_context_rel _ _ _ _) in X1 X2 IHX1 IHX2 *.
        eapply red_context_app_same_left in IHX1 => //.
        eapply red_context_app_same_left in IHX2 => //.
        2:{ eapply wf_term_red_context; tea. }
        eapply red_context_rel_inv.
        eapply red_context_trans; tea.
    - apply red_context_rel_red_ctx_rel.
  Qed.

  Lemma red_ctx_red_ctx_rel Γ Γ' :
    red_ctx Σ Γ Γ' <~> red_ctx_rel Σ [] Γ Γ'.
  Proof.
    unfold red_ctx, red_ctx_rel, red1_ctx, red1_ctx_rel.
    split; induction 1; try now econstructor; eauto.
    all: constructor.
    all: eapply OnOne2_local_env_impl; tea.
    all: intros Δ d d'; now rewrite app_context_nil_l.
  Qed.

  Lemma red_context_red_context_rel Γ Γ' :
    red_context Σ Γ Γ' <~> red_context_rel Σ [] Γ Γ'.
  Proof.
    unfold red_context_rel, red_context.
    split; intro h; eapply All2_fold_impl; tea.
    all: intros ?Γ ?Γ' d d'; cbn; now rewrite !app_context_nil_l.
  Qed.

  Lemma red_context_red_ctx Δ Δ' :
    red_context Σ Δ Δ' -> red_ctx Σ Δ Δ'.
  Proof using wfΣ.
    move/red_context_red_context_rel/red_context_rel_red_ctx_rel/red_ctx_red_ctx_rel.
    apply.
  Qed.

  Lemma red_ctx_red_context Δ Δ' :
    wf_term_ctx Δ ->
    red_ctx Σ Δ Δ' <~> red_context Σ Δ Δ'.
  Proof using wfΣ.
    intro wfΔ.
    etransitivity.
    1: apply red_ctx_red_ctx_rel.
    etransitivity.
    2: symmetry; apply red_context_red_context_rel.
    apply red_ctx_rel_red_context_rel.
    by rewrite app_context_nil_l //.
  Qed.

End CtxReduction.
