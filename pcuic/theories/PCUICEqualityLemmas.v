(* Distributed under the terms of the MIT license. *)
From Coq Require Import CMorphisms.
From MetaCoq.Utils Require Import LibHypsNaming utils.
From MetaCoq.Common Require Import config Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
    PCUICEquality PCUICClosed PCUICOnFreeVars PCUICLiftSubst PCUICSigmaCalculus PCUICTyping PCUICClosedTyp
    PCUICReduction PCUICCumulativity PCUICUnivSubstitutionConv PCUICWeakeningConv PCUICSubstitution.

Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags).

Lemma untyped_subslet_lift (Γ Δ : context) s Δ' :
  untyped_subslet Γ s Δ' ->
  untyped_subslet (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ').
Proof.
  induction 1; rewrite ?lift_context_snoc /=; try constructor; auto.
  simpl.
  rewrite -(untyped_subslet_length X).
  rewrite distr_lift_subst. constructor; auto.
Qed.

Lemma untyped_subslet_extended_subst Γ Δ :
  untyped_subslet (Γ ,,, smash_context [] Δ)
    (extended_subst Δ 0)
    (lift_context (context_assumptions Δ) 0 Δ).
Proof.
  induction Δ as [|[na [d|] ?] ?]; simpl; try constructor.
  * rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    len.
    constructor => //.
  * rewrite smash_context_acc. simpl.
    rewrite /map_decl /= /map_decl /=. simpl.
    rewrite lift_context_snoc /lift_decl /= /map_decl /=.
    constructor.
    rewrite (lift_extended_subst _ 1).
    rewrite -(lift_context_lift_context 1 _).
    eapply (untyped_subslet_lift _ [_]); eauto.
Qed.

Lemma untyped_subslet_ass {Γ s Δ} :
  is_assumption_context Δ ->
  #|s| = #|Δ| ->
  untyped_subslet Γ s Δ.
Proof.
  induction Δ as [|[na [b|] ty] Δ] in s |- *; destruct s; simpl; try discriminate.
  - constructor.
  - intros h [=]. constructor. apply IHΔ => //.
Qed.

Lemma untyped_subslet_fix_subst Γ mfix :
  untyped_subslet Γ (fix_subst mfix) (fix_context mfix).
Proof.
  apply untyped_subslet_ass.
  - apply is_assumption_context_fix_context.
  - len.
Qed.

Lemma untyped_subslet_cofix_subst Γ mfix :
  untyped_subslet Γ (cofix_subst mfix) (fix_context mfix).
Proof.
  apply untyped_subslet_ass.
  - apply is_assumption_context_fix_context.
  - len.
Qed.

Definition fake_params n : context :=
  repeat {| decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
            decl_body := None;
            decl_type := tVar "dummy" |} n.

Lemma closed_fake_params k n :
  closedn_ctx k (fake_params n).
Proof.
  induction n in k |- * => //=.
  cbn. rewrite IHn //.
Qed.

Lemma closedu_fake_params u n :
  (fake_params n)@[u] = fake_params n.
Proof.
  induction n => //=.
  cbn. f_equal.
  apply IHn.
Qed.

Lemma is_assumption_context_fake_params n :
  is_assumption_context (fake_params n).
Proof.
  induction n => //=.
Qed.

Lemma contexts_pres_eq_inst_case_context pars pars' puinst puinst' pctx pctx' :
  eq_context_upto_names pctx pctx' ->
  contexts_pres_eq
    (inst_case_context pars puinst pctx)
    (inst_case_context pars' puinst' pctx').
Proof.
  unfold inst_case_context.
  intro X.
  apply All2_map_inv, All2_eq_eq.
  rewrite -!map_map !map_decl_name_fold_context_k !map_map //=.
  apply All2_eq, All2_map.
  induction X; constructor; auto.
  destruct r => //.
Qed.

Lemma contexts_pres_eq_fix_context P Γ mfix mfix' :
  eq_mfixpoint P Γ mfix mfix' ->
  contexts_pres_eq (fix_context mfix) (fix_context mfix').
Proof.
  unfold fix_context.
  intro X.
  apply All2_rev, All2_mapi. cbn.
  induction X; constructor; auto.
  intro; apply r.
Qed.

Lemma eq_context_inst_case_context Σ cmp_universe cmp_sort Γ pars pars' puinst puinst' pctx pctx' :
  SubstUnivPreserving (cmp_universe Conv) (cmp_universe Conv) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_sort Conv) ->
  forallb wf_term pars ->
  closedn_ctx #|pars| pctx ->
  All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) pars pars' ->
  cmp_universe_instance (cmp_universe Conv) puinst puinst' ->
  eq_context_upto_names pctx pctx' ->
  eq_context_upto_rel Σ cmp_universe cmp_sort Conv Γ
    (inst_case_context pars puinst pctx)
    (inst_case_context pars' puinst' pctx').
Proof using Type.
  intros subu subs onpars onpctx eqpars eqinst eqctx.
  rewrite /inst_case_context.
  eapply eq_context_upto_subst_context0 with (Γ' := fake_params #|pars|); eauto.
  1-2: reflexivity.
  - now apply All2_rev.
  - now rewrite forallb_rev.
  - rewrite wf_term_ctx_subst_instance.
    now eapply closedn_ctx_wf_term_ctx.
  - apply weaken_ctx_eq_context_upto; tea.
    + apply closed_fake_params.
    + len. rewrite closedn_subst_instance_context //.
    + len. rewrite closedn_subst_instance_context //.
      erewrite <-eq_context_upto_names_closedn_ctx; tea.
    + rewrite -(closedu_fake_params puinst).
      eapply eq_context_upto_names_subst_instance; eauto.
Qed.

Lemma eq_term_upto_univ_napp_expand_lets Σ cmp_universe cmp_sort Γ Δ Δ' pb napp u v :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  wf_term_ctx Δ ->
  wf_term u ->
  eq_context_upto_rel Σ cmp_universe cmp_sort Conv Γ Δ Δ' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort (Γ ,,, Δ) pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort (Γ ,,, smash_context [] Δ) pb napp (expand_lets Δ u) (expand_lets Δ' v).
Proof using Type.
  intros ?? onΔ onu eqctx eq.
  induction Δ as [|d Δ] in Γ, onΔ, Δ', eqctx, u, v, onu, eq |- * using PCUICInduction.ctx_length_rev_ind.
  - depelim eqctx. simpl. now rewrite !expand_lets_nil.
  - destruct Δ' using rev_case.
    { apply All2_fold_length in eqctx. len in eqctx. cbn in eqctx. lia. }
    apply All2_fold_app_inv in eqctx as (eqd & eqctx0).
    2: { apply All2_fold_length in eqctx. len in eqctx. cbn in eqctx. lia. }
    depelim eqd. clear eqd.
    rewrite wf_term_ctx_app in onΔ. move/andP: onΔ => [ond onΔ]. cbn in ond.
    assert (eq_context_upto_rel Σ cmp_universe cmp_sort Conv (Γ ,, d) Δ Δ') as eqctx.
    { eapply All2_fold_impl; tea. move => ???? /=. rewrite app_context_assoc //=. }
    clear eqctx0.
    rewrite app_context_assoc /= -/(snoc Γ d) in eq.
    rewrite smash_context_app.
    destruct c.
    + rewrite !expand_lets_vass app_context_assoc.
      specialize (X Δ ltac:(reflexivity) _ _ _ _ onΔ onu eqctx eq).
      now apply X.
    + rewrite !expand_lets_vdef /=.
      rewrite (expand_lets_subst_comm Δ [b] u).
      rewrite (expand_lets_subst_comm Δ' [b'] v).
      specialize (X Δ ltac:(reflexivity) _ _ _ _ onΔ onu eqctx eq).
      relativize (context_assumptions Δ). 1: relativize (context_assumptions Δ').
      1: eapply eq_term_upto_univ_napp_subst' with (Γ' := [_]); eauto.
      * move/andP: ond => /= [onb ont]. auto.
      * now apply wf_term_expand_lets_k.
      * len. now apply eq_context_gen_context_assumptions in eqctx.
      * len.
Qed.


Lemma eq_term_upto_univ_iota_red Σ cmp_universe cmp_sort Γ pb napp ci p p' args args' br br' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_universe Conv) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_sort Conv) ->
  #|args| = ci_npar ci + context_assumptions (bcontext br) ->
  closedn_ctx #|pparams p| (bcontext br) ->
  wf_term (bbody br) ->
  forallb wf_term (pparams p) ->
  forallb wf_term args ->
  eq_predicate (fun Γ t u => eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv t u) (cmp_universe Conv) Γ p p' ->
  All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) args args' ->
  eq_context_upto_names (bcontext br) (bcontext br') ->
  eq_term_upto_univ Σ cmp_universe cmp_sort (Γ ,,, inst_case_branch_context p br) Conv (bbody br) (bbody br') ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp (iota_red (ci_npar ci) p args br) (iota_red (ci_npar ci) p' args' br').
Proof.
  intros ???? Hargs wfbctx wfbb wfpars wfargs eqpred eqargs eqbctx eqbb.
  eapply eq_term_upto_univ_napp_subst0 with (Γ' := smash_context [] (inst_case_branch_context p br)); eauto.
  - now apply All2_rev, All2_skipn.
  - rewrite forallb_rev. now apply forallb_skipn.
  - apply wf_term_expand_lets_k; tas.
    eapply wf_term_inst_case_context; trea.
  - apply eq_term_upto_univ_napp_expand_lets; eauto.
    + eapply wf_term_inst_case_context; trea.
    + destruct eqpred as (?&?&?&?).
      apply eq_context_inst_case_context; eauto.
    + eapply eq_term_upto_univ_leq; tea. auto with arith.
Qed.

Lemma eq_context_fix_context Σ cmp_universe cmp_sort Γ mfix mfix' :
  wf_term_mfix mfix ->
  eq_mfixpoint (fun Γ t t' => eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv t t') Γ mfix mfix' ->
  eq_context_upto_rel Σ cmp_universe cmp_sort Conv Γ (fix_context mfix) (fix_context mfix').
Proof.
  intros wfmfix eqmfix.
  apply All2_length in eqmfix as hlen.
  eapply All2_impl in eqmfix. 2: { intros d d' (eqty & eqbod & eqrarg & eqannot). exact (eqty, eqannot). }
  apply All2_rev in eqmfix. rewrite -forallb_rev in wfmfix.
  rewrite /fix_context !rev_mapi -hlen.
  assert (forall n, Nat.pred #|mfix| - n = #|mfix| - S n) as HM by lia.
  erewrite mapi_ext. 2: intros; rewrite HM; reflexivity.
  erewrite (mapi_ext _ _ (List.rev mfix')). 2: intros; rewrite HM; reflexivity.
  rewrite /mapi -List.rev_length.
  induction eqmfix in wfmfix |- * => //=.
  1: now constructor.
  rewrite !mapi_rec_Sk -!/(mapi _ _).
  cbn in wfmfix. move/andP: wfmfix => [] /andP[] wfb wft wfmfix.
  constructor. 1: now eapply IHeqmfix.
  rewrite Nat.sub_0_r.
  clear IHeqmfix wfmfix.
  destruct r as (eqty & eqannot).
  constructor; tas.
  eapply @weakening_eq_term_upto_univ_napp with (Γ'' := mapi _ _) (Γ' := []) in eqty; tas.
  cbn in eqty. simpl in eqty. len in eqty.
  apply eqty.
Qed.

Lemma eq_term_upto_univ_napp_fix_subst Σ cmp_universe cmp_sort Γ mfix mfix' pb napp u v :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  wf_term_mfix mfix ->
  wf_term u ->
  eq_mfixpoint (fun Γ t t' => eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv t t') Γ mfix mfix' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort (Γ ,,, fix_context mfix) Conv 0 u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp (subst0 (fix_subst mfix) u) (subst0 (fix_subst mfix') v).
Proof.
  intros ?? wfmfix wfu eqmfix equ.
  eapply eq_term_upto_univ_napp_subst0 with (Γ' := fix_context mfix); eauto.
  - eapply All2_from_nth_error. 1: len; now eapply All2_length.
    intros n d d' _ hnth hnth'.
    apply nth_error_fix_subst in hnth as ->.
    apply nth_error_fix_subst in hnth' as ->.
    rewrite -(All2_length eqmfix).
    now constructor.
  - now apply wf_term_fix_subst.
  - eapply eq_term_upto_univ_leq; tea. auto with arith.
Qed.

Lemma eq_term_upto_univ_napp_cofix_subst Σ cmp_universe cmp_sort Γ mfix mfix' pb napp u v :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  wf_term_mfix mfix ->
  wf_term u ->
  eq_mfixpoint (fun Γ t t' => eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv t t') Γ mfix mfix' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort (Γ ,,, fix_context mfix) Conv 0 u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp (subst0 (cofix_subst mfix) u) (subst0 (cofix_subst mfix') v).
Proof.
  intros ?? wfmfix wfu eqmfix equ.
  eapply eq_term_upto_univ_napp_subst0 with (Γ' := fix_context mfix); eauto.
  - eapply All2_from_nth_error. 1: len; now eapply All2_length.
    intros n d d' _ hnth hnth'.
    apply nth_error_cofix_subst in hnth as ->.
    apply nth_error_cofix_subst in hnth' as ->.
    rewrite -(All2_length eqmfix).
    now constructor.
  - now apply wf_term_cofix_subst.
  - eapply eq_term_upto_univ_leq; tea. auto with arith.
Qed.


Lemma eq_binder_relevances_refl (x : list aname) : All2 (on_rel eq binder_relevance) x x.
Proof. now eapply All_All2_refl, All_refl. Qed.
#[global]
Hint Resolve eq_binder_relevances_refl : core.

Lemma onctx_eq_ctx P ctx cmp_term pb :
  onctx P ctx ->
  (forall Γ x, P x -> cmp_term Γ Conv x x) ->
  (forall Γ x, P x -> cmp_term Γ pb x x) ->
  eq_context_gen cmp_term pb ctx ctx.
Proof.
  intros onc HP HP'.
  induction onc.
  - constructor; auto.
  - constructor; auto; simpl.
    destruct x as [na [b|] ty]; destruct p; simpl in *;
    constructor; auto.
Qed.

Lemma onctx_eq_ctx_sym P ctx ctx' cmp_term pb :
  onctx P ctx ->
  (forall pb0 Γ Γ', eq_context_gen cmp_term pb0 Γ Γ' -> forall pb, subrelation (cmp_term Γ pb) (cmp_term Γ' pb)) ->
  (forall Γ x, P x -> forall y, cmp_term Γ Conv x y -> cmp_term Γ Conv y x) ->
  (forall Γ x, P x -> forall y, cmp_term Γ pb x y -> cmp_term Γ pb y x) ->
  eq_context_gen cmp_term pb ctx ctx' ->
  eq_context_gen cmp_term pb ctx' ctx.
Proof.
  intros onc HΓ HP HP' H1.
  induction H1; depelim onc; constructor; intuition auto; simpl in *.
  specialize (HΓ _ _ _ H1).
  destruct p; depelim o; constructor; eauto; try symmetry; eauto.
  all: try eapply HP; try eapply HP'; eauto.
  all: now eapply HΓ.
Qed.

Lemma eq_term_upto_univ_sym0 Σ cmp_universe cmp_sort Γ Γ' pb napp u v :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_sort Conv) ->
  RelationClasses.Symmetric (cmp_sort pb) ->
  contexts_pres_eq Γ Γ' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ' pb napp v u.
Proof.
  intros sym_univ sym_univ' sym_sort sym_sort' eqctx e.
  pose proof (@RelationClasses.symmetry _ (@eq_binder_annot name name) _).
  induction e in Γ', eqctx, sym_univ', sym_sort' |- *.
  all: try solve [
    econstructor ; eauto ;
    try eapply Forall2_symP ; eauto ; easy
  ].
  - econstructor.
    apply All2_sym. solve_all.
  - econstructor; eauto.
    eapply IHe2; tea.
    constructor; tas.
  - econstructor; eauto.
    eapply IHe2; tea.
    constructor; tas.
  - econstructor; eauto.
    eapply IHe3; tea.
    constructor; tas.
  - destruct X as (Xp & Xu & Xc & _ & Xr).
    econstructor; rewrite ?e; unfold eq_branches, eq_branch in *; repeat split; eauto.
    2,3: now symmetry.
    + eapply All2_sym; solve_all.
    + eapply Xr; tea.
      apply All2_app; tas.
      apply contexts_pres_eq_inst_case_context; auto.
    + eapply All2_sym; solve_all.
      1: now symmetry.
      eapply b0; tea.
      apply All2_app; tas.
      apply contexts_pres_eq_inst_case_context; auto.
      all: solve_all.
  - have X' : contexts_pres_eq (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix').
    { apply All2_app; tas. eapply contexts_pres_eq_fix_context; tea. }
    econstructor. unfold eq_mfixpoint in *.
    apply All2_sym. solve_all; inv_wf_term; eauto.
  - have X' : contexts_pres_eq (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix').
    { apply All2_app; tas. eapply contexts_pres_eq_fix_context; tea. }
    econstructor. unfold eq_mfixpoint in *.
    apply All2_sym. solve_all; inv_wf_term; eauto.
  - econstructor.
    destruct X; constructor; intuition eauto.
    apply All2_sym.
    solve_all.
Qed.

#[global] Instance eq_term_upto_univ_sym Σ Γ cmp_universe cmp_sort pb napp :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_sort Conv) ->
  RelationClasses.Symmetric (cmp_sort pb) ->
  Symmetric (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp).
Proof.
  intros ** u v.
  eapply eq_term_upto_univ_sym0; eauto.
  reflexivity.
Qed.

#[global] Instance compare_term_sym {cf} Σ φ Γ :
  Symmetric (compare_term Σ φ Γ Conv).
Proof.
  apply eq_term_upto_univ_sym; tc.
Qed.

#[global] Instance conv_sym {cf} (Σ : global_env_ext) Γ :
  Symmetric (convAlgo Σ Γ).
Proof.
  intros u v X. induction X.
  - constructor. now apply compare_term_sym.
  - eapply red_conv_conv_inv; tea.
    eapply red1_red in r. eauto.
  - eapply red_conv_conv; tea.
    eapply red1_red in r. eauto.
Qed.

Lemma eq_term_upto_univ_trans0 Σ cmp_universe cmp_sort Γ Γ' pb napp u v w :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_universe Conv) ->
  RelationClasses.Transitive (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_sort Conv) ->
  RelationClasses.Transitive (cmp_sort pb) ->
  contexts_pres_eq Γ Γ' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ' pb napp v w ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u w.
Proof.
  intros subr trans_univ trans_univ' trans_sort trans_sort' eqctx e1 e2.
  pose proof (@RelationClasses.transitivity _ (@eq_binder_annot name name) _).
  assert (RelationClasses.subrelation (cmp_universe Conv) (cmp_universe Conv)) by reflexivity.
  induction e1 in Γ', subr, eqctx, w, e2, trans_univ', trans_sort' |- *.
  all: try solve [
    dependent destruction e2 ; econstructor ; eauto ;
    try now etransitivity
  ].
  all: dependent destruction e2.
  - econstructor.
    eapply All2_trans'; tea. cbn.
    intros u v w IH. now eapply IH; eauto.
  - econstructor; eauto.
    eapply IHe1_2; eauto.
    constructor; tas.
  - econstructor; eauto.
    eapply IHe1_2; eauto.
    constructor; tas.
  - econstructor; eauto.
    eapply IHe1_3; eauto.
    constructor; tas.
  - unfold eq_predicate, eq_branches, eq_branch in *.
    solve_all.
    econstructor; unfold eq_predicate, eq_branches, eq_branch in *; solve_all; eauto.
    2-3: etransitivity; eassumption.
    + eapply All2_trans'; tea; intros ??? IH; now eapply IH; eauto.
    + eapply b; eauto.
      apply All2_app; tas.
      apply contexts_pres_eq_inst_case_context; auto.
      all: solve_all.
    + eapply All2_trans'; tea; intros br br' br'' ((eqctx' & eqb & IH) & (eqctx'' & eqb')).
      split.
      1: etransitivity; eassumption.
      eapply IH; eauto.
      apply All2_app; tas.
      apply contexts_pres_eq_inst_case_context; auto.
  - have X' : contexts_pres_eq (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix').
    { apply All2_app; tas. eapply contexts_pres_eq_fix_context; tea. }
    econstructor. unfold eq_mfixpoint in *.
    solve_all.
    eapply All2_trans'; tea; intros ??? (((eqty & IHty) & (eqb & IHb) & eqrarg & eqannot) & (eqty' & eqb' & eqrarg' & eqannot')).
    repeat split; try now etransitivity.
    1: now eapply IHty; eauto.
    eapply IHb; eauto.
  - have X' : contexts_pres_eq (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix').
    { apply All2_app; tas. eapply contexts_pres_eq_fix_context; tea. }
    econstructor. unfold eq_mfixpoint in *.
    solve_all.
    eapply All2_trans'; tea; intros ??? (((eqty & IHty) & (eqb & IHb) & eqrarg & eqannot) & (eqty' & eqb' & eqrarg' & eqannot')).
    repeat split; try now etransitivity.
    1: now eapply IHty; eauto.
    eapply IHb; eauto.
  - constructor.
    destruct X; depelim o; constructor; intuition eauto.
    solve_all.
    eapply All2_trans'; tea.
    intros ??? ((eqxy & IH) & eqyz).
    repeat split; eauto.
Qed.

#[global] Instance eq_term_upto_univ_trans Σ cmp_universe cmp_sort Γ pb napp :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_universe Conv) ->
  RelationClasses.Transitive (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_sort Conv) ->
  RelationClasses.Transitive (cmp_sort pb) ->
  Transitive (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp).
Proof.
  intros ** u v w.
  eapply eq_term_upto_univ_trans0; eauto.
  reflexivity.
Qed.

#[global] Instance compare_term_trans {cf} Σ φ Γ :
  Transitive (compare_term Σ φ Γ Conv).
Proof.
  apply eq_term_upto_univ_trans; tc.
Qed.

Lemma eq_term_upto_univ_antisym Σ cmp_universe cmp_sort Γ Γ' pb napp u v
  (univ_equi : RelationClasses.Equivalence (cmp_universe Conv))
  (sort_equi : RelationClasses.Equivalence (cmp_sort Conv)) :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Antisymmetric _ (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Antisymmetric _ (cmp_sort Conv) (cmp_sort pb) ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ' pb napp v u ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv napp u v.
Proof.
  intros univ_sub univ_antisym sort_antisym e1 e2.
  induction e2 in univ_sub, univ_antisym, sort_antisym, Γ, e1 |- *.
  all: try solve [ econstructor; eauto ].
  all: try solve [ dependent elimination e1; econstructor; eauto ].
  all: dependent elimination e1; constructor; now apply RelationClasses.antisymmetry.
Qed.

Lemma leq_term_antisym {cf:checker_flags} Σ φ Γ pb napp u v :
  compare_term_napp Σ φ Γ pb napp u v ->
  compare_term_napp Σ φ Γ pb napp v u ->
  compare_term_napp Σ φ Γ Conv napp u v.
Proof.
  eapply eq_term_upto_univ_antisym; tc.
Qed.

#[global] Lemma flip_SubstUnivPreserving P T Q `(H : SubstUnivPreserving P T Q) : SubstUnivPreserving (flip P) (flip Q).
Proof.
  intros u ui ui'.
  move/cmp_universe_instance_flip.
  apply H.
Qed.

Lemma eq_term_upto_univ_napp_flip0 Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' Γ Γ' napp u v :
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  RelationClasses.subrelation (cmp_sort Conv) (flip (cmp_sort' Conv)) ->
  RelationClasses.subrelation (cmp_sort pb) (flip (cmp_sort' pb')) ->
  contexts_pres_eq Γ Γ' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' Γ' pb' napp v u.
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb eqctx e.
  pose proof (@RelationClasses.symmetry _ (@eq_binder_annot name name) _).
  induction e in Γ', eqctx, pb', univ_sub_pb, sort_sub_pb |- *.
  all: try solve [ econstructor ; eauto ].
  - constructor.
    eapply All2_sym. solve_all.
  - constructor. now eapply sort_sub_pb.
  - constructor. eapply cmp_universe_instance_flip; eassumption.
  - constructor.
    eapply cmp_global_instance_flip. 3:eauto. all:auto.
  - constructor.
    eapply cmp_global_instance_flip. 3:eauto. all:eauto.
  - econstructor; eauto.
    eapply IHe2; tea.
    constructor; tas.
  - econstructor; eauto.
    eapply IHe2; tea.
    constructor; tas.
  - econstructor; eauto.
    eapply IHe3; tea.
    constructor; tas.
  - constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto.
    solve_all.
    * apply All2_sym; solve_all.
    * eapply cmp_universe_instance_flip; eauto.
    * now symmetry.
    * eapply b0; tea.
      apply All2_app; tas.
      apply contexts_pres_eq_inst_case_context; auto.
    * apply All2_sym. solve_all.
      1: now symmetry.
      eapply b1; tea.
      apply All2_app; tas.
      apply contexts_pres_eq_inst_case_context; auto.
  - have X' : contexts_pres_eq (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix').
    { apply All2_app; tas. eapply contexts_pres_eq_fix_context; tea. }
    econstructor. unfold eq_mfixpoint in *.
    apply All2_sym. solve_all; inv_wf_term; eauto using eq_context_upto_cat.
  - have X' : contexts_pres_eq (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix').
    { apply All2_app; tas. eapply contexts_pres_eq_fix_context; tea. }
    econstructor. unfold eq_mfixpoint in *.
    apply All2_sym. solve_all; inv_wf_term; eauto using eq_context_upto_cat.
  - econstructor.
    destruct X; constructor; intuition eauto.
    1: now eapply univ_sub_conv.
    apply All2_sym.
    solve_all.
Qed.

Lemma eq_term_upto_univ_napp_flip Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' Γ napp u v :
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  RelationClasses.subrelation (cmp_sort Conv) (flip (cmp_sort' Conv)) ->
  RelationClasses.subrelation (cmp_sort pb) (flip (cmp_sort' pb')) ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' Γ pb' napp v u.
Proof.
  intros.
  eapply eq_term_upto_univ_napp_flip0; eauto.
  reflexivity.
Qed.

#[global] Instance eq_context_upto_sym Σ cmp_universe cmp_sort pb :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_sort Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_sort pb) ->
  Symmetric (eq_context_upto Σ cmp_universe cmp_sort pb).
Proof.
  intros ???? Γ Γ' e.
  induction e. 1: constructor.
  constructor. 1: now apply IHe.
  destruct p; constructor; try symmetry; eauto.
  all: eapply eq_term_upto_univ_contexts_pres_eq; tea.
  all: symmetry; now eapply eq_context_upto_pres_eq.
Qed.

#[global] Instance eq_context_sym {cf} Σ φ :
  Symmetric (eq_context Σ φ).
Proof.
  apply eq_context_upto_sym; exact _.
Qed.

Lemma eq_context_upto_flip Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' Γ Δ :
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  RelationClasses.subrelation (cmp_sort Conv) (flip (cmp_sort' Conv)) ->
  RelationClasses.subrelation (cmp_sort pb) (flip (cmp_sort' pb')) ->
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
  eq_context_upto Σ cmp_universe' cmp_sort' pb' Δ Γ.
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb e.
  induction e. 1: constructor.
  constructor. 1: now apply IHe.
  destruct p; constructor; try symmetry; eauto.
  all: eapply eq_term_upto_univ_napp_flip0; tea.
  all: symmetry; now eapply eq_context_upto_pres_eq.
Qed.





(* Lemma eq_context_extended_subst {Σ cmp_universe cmp_sort pb Γ Δ Ξ k} :
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
  All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Ξ Conv) (extended_subst Γ k) (extended_subst Δ k).
Proof.
  intros Heq.
  induction Heq in k |- *; simpl.
  - constructor; auto.
  - destruct p => /=.
    * constructor; eauto. now constructor.
    * constructor; eauto.
      relativize Ξ. 2: admit.
      rewrite -(eq_context_gen_context_assumptions Heq).
      len. rewrite -(All2_fold_length Heq).
      eapply eq_term_upto_univ_napp_subst0.
      7: eapply weakening_eq_term_upto_univ_napp.
      eapply eq_term_upto_univ_substs; eauto; tc.
      eapply eq_term_upto_univ_lift, eqb.
      + eapply IHHeq.
Qed. *)

From MetaCoq.PCUIC Require Import PCUICOnOne.

Lemma red1_ctx_eq_term_upto {cf : checker_flags} {Σ} {cmp_universe cmp_sort pb napp Γ Δ u v} :
  red1_ctx Σ Γ Δ ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Δ pb napp u v.
Proof.
  intro.
  apply eq_term_upto_univ_contexts_pres_eq.
  induction X; constructor; cbnr; auto.
  all: destruct p; congruence.
Qed.

Lemma cored1_ctx_eq_term_upto {cf : checker_flags} {Σ} {cmp_universe cmp_sort pb napp Γ Δ u v} :
  red1_ctx Σ Γ Δ ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Δ pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v.
Proof.
  intro.
  apply eq_term_upto_univ_contexts_pres_eq.
  induction X; constructor; cbnr; auto.
  all: destruct p; congruence.
Qed.

Lemma red_ctx_eq_term_upto {cf : checker_flags} {Σ} {cmp_universe cmp_sort pb napp Γ Δ u v} :
  red_ctx Σ Γ Δ ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Δ pb napp u v.
Proof.
  induction 1; auto.
  now apply red1_ctx_eq_term_upto.
Qed.

Lemma red_context_eq_term_upto {cf : checker_flags} {Σ} {cmp_universe cmp_sort pb napp Γ Δ u v} :
  red_context Σ Γ Δ ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Δ pb napp u v.
Proof.
  intro.
  apply eq_term_upto_univ_contexts_pres_eq.
  induction X; constructor; auto.
  destruct p; cbnr.
Qed.

Lemma cored_context_eq_term_upto {cf : checker_flags} {Σ} {cmp_universe cmp_sort pb napp Γ Δ u v} :
  red_context Σ Γ Δ ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Δ pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v.
Proof.
  intro.
  apply eq_term_upto_univ_contexts_pres_eq.
  induction X; constructor; auto.
  destruct p; cbnr.
Qed.

(*Lemma eq_context_upto_eq_univ_subst_instance {cf:checker_flags} Σ φ Re Rle :
  RelationClasses.Reflexive (Re φ) ->
  RelationClasses.Transitive (Re φ) ->
  RelationClasses.Transitive (Rle φ) ->
  SubstUnivPreserving (Re φ) (Re φ) ->
  RelationClasses.subrelation (Re φ) (Rle φ) ->
  SubstUnivPreserved Re ->
  SubstUnivPreserved Rle ->
  forall x y u1 u2,
    cmp_universe_instance (Re φ) u1 u2 ->
    valid_constraints φ (subst_instance_cstrs u1 φ) ->
    eq_context_upto Σ eq eq x y ->
    eq_context_upto Σ (Re φ) (Rle φ) (subst_instance u1 x) (subst_instance u2 y).
Proof.
  intros ref tr trle hRe subr p p' x y u1 u2 ru vcstr eqxy.
  eapply All2_fold_trans.
  intros ?????????. eapply compare_decl_trans.
  eapply eq_term_upto_univ_trans; tc.
  eapply eq_term_upto_univ_trans; tc.
  apply (eq_context_upto_univ_subst_preserved Σ Re Rle φ φ u1) => //.

  tea.
  eapply eq_context_upto_univ_subst_instance; tc. tea.
Qed.*)
