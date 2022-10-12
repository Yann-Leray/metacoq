(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICRelevance PCUICGlobalEnv
  PCUICReduction PCUICOnOne PCUICTyping PCUICRelevanceTerm PCUICWeakeningConv
  PCUICUnivSubstitutionConv PCUICSubstitution.

Require Import ssreflect.

Require Import Equations.Prop.DepElim.

Lemma OnOne2_apply {A B} (P : B -> A -> A -> Type) l l' : 
  OnOne2 (fun x y => forall a : B, P a x y) l l' ->
  forall a : B, OnOne2 (P a) l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2_apply_left {A B} (P : B -> A -> A -> Type) Q l l' : 
  OnOne2 (fun x y => (forall a : B, P a x y) × Q x y) l l' ->
  forall a : B, OnOne2 (fun x y => P a x y × Q x y) l l'.
Proof.
  induction 1; constructor; auto.
  destruct p; now split.
Qed.

Lemma OnOne2_prod {A} (P Q : A -> A -> Type) l l' : 
  OnOne2 P l l' × OnOne2 Q l l' ->
  (forall x, Q x x) ->
  OnOne2 (fun x y => P x y × Q x y) l l'.
Proof.
  intros [] Hq. induction o. depelim o0. constructor; intuition eauto.
  constructor. split; auto.
  constructor. depelim o0. apply IHo.
  induction tl. depelim o. constructor. auto.
  auto.
Qed.

Lemma OnOne2_prod_assoc {A} (P Q R : A -> A -> Type) l l' : 
  OnOne2 (fun x y => (P x y × Q x y) × R x y) l l' ->
  OnOne2 P l l' × OnOne2 (fun x y => Q x y × R x y) l l'.
Proof.
  induction 1; split; constructor; intuition eauto.
Qed.

Lemma mfix_eqdname_binder_relevance {A B} P (f1: _ -> A) (f2: _ -> B) (l l' : mfixpoint term) :
  OnOne2 (fun x y => P x y × (dname x, f1 x, f2 x) = (dname y, f1 y, f2 y)) l l' ->
  forall n d, nth_error l n = Some d -> ∑ d', nth_error l' n = Some d' × d.(dname).(binder_relevance) = d'.(dname).(binder_relevance).
Proof.
  induction 1; intros.
  - destruct p as [_ p]; noconf p.
    destruct n; eexists; cbn; eauto.
    depelim H2. split; cbnr.
    now f_equal.
  - destruct n; cbn; eauto.
Qed.

Lemma mfix_eqdname_marks_fix_context {A B} P (f1: _ -> A) (f2: _ -> B) (mfix mfix' : mfixpoint term) :
  OnOne2 (fun x y => P x y × (dname x, f1 x, f2 x) = (dname y, f1 y, f2 y)) mfix mfix' ->
  marks_of_context (fix_context mfix) = marks_of_context (fix_context mfix').
Proof.
  rewrite /marks_of_context /fix_context !map_rev !map_mapi /= !mapi_cst_map.
  intro H.
  f_equal; apply All2_eq, All2_map.
  apply OnOne2_All2 with (1 := H); auto.
  intros ??[].
  now noconf e.
Qed.

Lemma isTermRel_lift {Σ n Γ ty rel}
  (isdecl : n <= #|Γ|):
  isTermRel Σ (skipn n Γ) ty rel ->
  isTermRel Σ Γ (lift0 n ty) rel.
Proof.
  intros wfty.
  assert (n = #|firstn n Γ|).
  { rewrite firstn_length_le; auto with arith. }
  replace Γ with (skipn n Γ ,,, firstn n Γ ,,, [])
  by apply (firstn_skipn n Γ).
  rewrite {3}H.
  change 0 with #|@nil relevance|.
  eapply weakening_isTermRel, wfty.
Qed.

Lemma marks_subslet_fix_subst {Σ Γ mfix} :
  wfTermRel_mfix isTermRel Σ Γ (marks_of_context (fix_context mfix)) mfix ->
  marks_subslet Σ Γ (fix_subst mfix) (marks_of_context (fix_context mfix)).
Proof.
  intro wf.
  rewrite /fix_subst /fix_context /marks_of_context rev_mapi map_mapi /= mapi_cst_map.
  remember mfix as mfixfix in wf |- * at 1.
  rewrite -(app_nil_r mfix) in Heqmfixfix.
  clear -wf Heqmfixfix. revert Heqmfixfix.
  generalize ([] : mfixpoint term) as mfix1.
  induction mfix using rev_ind.
  1: constructor.
  intros.
  rewrite rev_app_distr app_length /= Nat.add_1_r.
  cbn; constructor.
  1: eapply IHmfix; now rewrite -app_assoc in Heqmfixfix.
  constructor; tas.
  rewrite Heqmfixfix nth_error_app1.
  1: rewrite app_length /= Nat.add_1_r; constructor.
  rewrite nth_error_app2; [constructor|].
  rewrite Nat.sub_diag //.
Qed.

Lemma marks_subslet_cofix_subst {Σ Γ mfix} :
  wfTermRel_mfix isTermRel Σ Γ (marks_of_context (fix_context mfix)) mfix ->
  marks_subslet Σ Γ (cofix_subst mfix) (marks_of_context (fix_context mfix)).
Proof.
  intro wf.
  rewrite /cofix_subst /fix_context /marks_of_context rev_mapi map_mapi /= mapi_cst_map.
  remember mfix as mfixfix in wf |- * at 1.
  rewrite -(app_nil_r mfix) in Heqmfixfix.
  clear -wf Heqmfixfix. revert Heqmfixfix.
  generalize ([] : mfixpoint term) as mfix1.
  induction mfix using rev_ind.
  1: constructor.
  intros.
  rewrite rev_app_distr app_length /= Nat.add_1_r.
  cbn; constructor.
  1: eapply IHmfix; now rewrite -app_assoc in Heqmfixfix.
  constructor; tas.
  rewrite Heqmfixfix nth_error_app1.
  1: rewrite app_length /= Nat.add_1_r; constructor.
  rewrite nth_error_app2; [constructor|].
  rewrite Nat.sub_diag //.
Qed.

Lemma isTermRel_red1 {cf: checker_flags} {Pr P P' Σ Γ t u rel} :
  on_global_env Pr (lift_relation isTermRelOpt P P') Σ ->
  wfTermRel_ctx Σ Γ ->
  red1 Σ Γ t u ->
  isTermRel Σ (marks_of_context Γ) t rel -> isTermRel Σ (marks_of_context Γ) u rel.
Proof.
  intros HΣ HΓ X Ht. revert rel Ht.
  induction X in HΓ using red1_ind_all; intros rel Ht.
  all: try solve [ inv Ht; econstructor; eauto ].
  all: try solve [ inv Ht; (forward IHX by constructor; [assumption|constructor => //]); econstructor; eauto ].
  - inv Ht. inv X0.
    eapply subst_isTermRel with (Γ' := []) (Δ := [_]) (2 := X2).
    constructor; [constructor|assumption].
  - inv Ht.
    eapply subst_isTermRel with (Γ' := []) (Δ := [_]) (2 := X).
    constructor; [constructor|assumption].
  - inv Ht.
    destruct nth_error eqn:Heq => //. depelim H.
    destruct c; cbn in H. subst.
    eapply nth_error_All_local_env in HΓ as (Hb & Ht); tea.
    cbn in Hb, Ht.
    rewrite nth_error_map Heq /= in H0. depelim H0; subst.
    eapply isTermRel_lift.
    { apply nth_error_Some_length in Heq. rewrite map_length. lia. }
    rewrite skipn_map //.
  - inv Ht.
    unfold iota_red.
    enough (isTermRel Σ (marks_of_context (Γ ,,, inst_case_branch_context p br)) (bbody br) (ci_relevance ci)).
    { eapply subst_isTermRel' with (Γ' := []). { admit. } admit. }
    apply All_nth_error with (2 := H) in X1 as [? (rbod & Hbod)].
    assert (rbod = ci_relevance ci) as <- by admit.
    rewrite marks_of_context_app //.
  - apply isTermRel_mkApps_inv in Ht as (Ht & Hargs).
    apply isTermRel_mkApps with (2 := Hargs).
    unfold unfold_fix in H.
    inv Ht.
    rewrite H1 in H; depelim H.
    change (marks_of_context Γ) with (marks_of_context Γ ,,, []).
    apply subst_isTermRel with (Γ' := []) (Δ := marks_of_context (fix_context mfix)).
    { now apply marks_subslet_fix_subst. }
    apply All_nth_error with (2 := H1) in X as (X & _) => //.
  - inv Ht. rename X1 into Ht.
    econstructor; tas. instantiate (1 := r). clear X X0.
    apply isTermRel_mkApps_inv in Ht as (Ht & Hargs).
    apply isTermRel_mkApps with (2 := Hargs).
    unfold unfold_cofix in H.
    inv Ht.
    rewrite H0 in H; depelim H.
    change (marks_of_context Γ) with (marks_of_context Γ ,,, []).
    apply subst_isTermRel with (Γ' := []) (Δ := marks_of_context (fix_context mfix)).
    { now apply marks_subslet_cofix_subst. }
    apply All_nth_error with (2 := H0) in X as (X & _) => //.
  - inv Ht. rename X into Ht.
    econstructor; tea. instantiate (1 := rel'). clear H0.
    apply isTermRel_mkApps_inv in Ht as (Ht & Hargs).
    apply isTermRel_mkApps with (2 := Hargs).
    unfold unfold_cofix in H.
    inv Ht.
    rewrite H0 in H; depelim H.
    change (marks_of_context Γ) with (marks_of_context Γ ,,, []).
    apply subst_isTermRel with (Γ' := []) (Δ := marks_of_context (fix_context mfix)).
    { now apply marks_subslet_cofix_subst. }
    apply All_nth_error with (2 := H0) in X as (X & _) => //.
  - inv Ht.
    apply declared_constant_inj with (1 := H) in H1 as <-.
    apply isTermRel_subst_instance.
    apply declared_constant_lookup in H.
    unfold lookup_constant in H.
    destruct lookup_env eqn:H' => //. destruct g => //. depelim H.
    destruct decl. depelim H0. cbn.
    pose proof HΣ.
    eapply lookup_on_global_env with (2 := H') in HΣ as (Σ' & [ext _ ((_ & Hb) & _)]).
    cbn in Hb.
    eapply extends_isTermRel; tea.
    eapply weaken_ctx_isTermRel in Hb.
    apply Hb.
  - inv Ht.
    admit.
  - eapply OnOne2_prod_inv in X as [_ X].
    eapply OnOne2_apply in X; tea.
    eapply OnOne2_All2 in X.
    2: { exact (fun x y f => f). }
    2: { exact (fun x r H => H). }
    inv Ht. econstructor; eauto.
    + destruct X0 as (X0 & X0' & X0'').
      repeat split; cbn.
      * solve_all.
        destruct a; now eexists.
      * rewrite -(All2_length X) //.
      * rewrite !mark_inst_case_predicate_context // in X0'' |- *.
    + solve_all.
      unfold wfTermRel_branch in X1 |- *.
      rewrite -(All2_length X) !mark_inst_case_branch_context // in X1 |- *.
  - inv Ht. econstructor; eauto.
    destruct X0 as (X0 & X0' & X0'').
    repeat split; tas. cbn.
    rewrite -marks_of_context_app // in X0'' |- *.
    apply IHX; auto.
    apply All_local_rel_app; tas.
    admit. (* apply wfTermRel_ctx_rel_inst_case_predicate_context; assumption. *)
  - eapply OnOne2_All2 in X.
    2: { exact (fun x y '((_, f), e) => fun H => (f H, e)). }
    2: { exact (fun x _ => (fun r H => H, eq_refl)). }
    inv Ht. econstructor; eauto.
    solve_all.
    destruct a.
    forward b.
    { apply All_local_rel_app; tas. admit. (* apply wfTermRel_ctx_rel_inst_case_branch_context; assumption. *) }
    destruct b; split; auto.
    1: now rewrite -e.
    rewrite /inst_case_branch_context -!marks_of_context_app -e in s |- *.
    destruct s; eexists; eauto.
  - depelim Ht.
    eapply mfix_eqdname_binder_relevance with (1 := X) in e as (def' & e & ->).
    apply mfix_eqdname_marks_fix_context in X as eqΓ.
    econstructor; tas.
    eapply OnOne2_prod_assoc in X as [_ X].
    eapply OnOne2_apply_left in X; tea.
    eapply OnOne2_All2 in X.
    2: { exact (fun x y f => f). }
    2: { exact (fun x => (fun r H => H, eq_refl)). }
    unfold wfTermRel_mfix in w |- *. solve_all.
    noconf b1.
    rewrite -eqΓ -H -H0 //.
  - depelim Ht.
    eapply mfix_eqdname_binder_relevance with (1 := X) in e as (def' & e & ->).
    apply mfix_eqdname_marks_fix_context in X as eqΓ.
    econstructor; tas.
    eapply OnOne2_prod_assoc in X as [_ X].
    eapply OnOne2_apply_left in X; tea.
    2: { apply All_local_rel_app; tas. apply wfTermRel_mfix_wfTermRel_ctx_rel, w. }
    eapply OnOne2_All2 in X.
    2: { exact (fun x y f => f). }
    2: { exact (fun x => (fun r H => H, eq_refl)). }
    unfold wfTermRel_mfix in w |- *. solve_all.
    all: noconf b1; rewrite -?eqΓ -?H -?H0 -?marks_of_context_app //.
    rewrite -marks_of_context_app in a0; auto.
  - depelim Ht.
    eapply mfix_eqdname_binder_relevance with (1 := X) in e as (def' & e & ->).
    apply mfix_eqdname_marks_fix_context in X as eqΓ.
    econstructor; tas.
    eapply OnOne2_prod_assoc in X as [_ X].
    eapply OnOne2_apply_left in X; tea.
    eapply OnOne2_All2 in X.
    2: { exact (fun x y f => f). }
    2: { exact (fun x => (fun r H => H, eq_refl)). }
    unfold wfTermRel_mfix in w |- *. solve_all.
    noconf b1.
    rewrite -eqΓ -H -H0 //.
  - depelim Ht.
    eapply mfix_eqdname_binder_relevance with (1 := X) in e as (def' & e & ->).
    apply mfix_eqdname_marks_fix_context in X as eqΓ.
    econstructor; tas.
    eapply OnOne2_prod_assoc in X as [_ X].
    eapply OnOne2_apply_left in X; tea.
    2: { apply All_local_rel_app; tas. apply wfTermRel_mfix_wfTermRel_ctx_rel, w. }
    eapply OnOne2_All2 in X.
    2: { exact (fun x y f => f). }
    2: { exact (fun x => (fun r H => H, eq_refl)). }
    unfold wfTermRel_mfix in w |- *. solve_all.
    all: noconf b1; rewrite -?eqΓ -?H -?H0 -?marks_of_context_app //.
    rewrite -marks_of_context_app in a0; auto.
Admitted.

Lemma red_relevance {cf: checker_flags} {Pr P P'} {Σ Γ t u rel} :
  on_global_env Pr (lift_relation isTermRelOpt P P') Σ ->
  wfTermRel_ctx Σ Γ ->
  red Σ Γ t u -> isTermRel Σ (marks_of_context Γ) t rel -> isTermRel Σ (marks_of_context Γ) u rel.
Proof.
  induction 3 using red_rect'; auto.
  intro; eapply isTermRel_red1; eauto.
Qed.

(* 
Lemma red_one_param_rel :
forall ci p c brs pars' r,
  isTermRel Σ (marks_of_context Γ) (tCase ci p c brs) r ->
  red1_one_term Γ (map (fun x => (x, tt)) p.(pparams)) pars' ->
  isTermRel Σ (marks_of_context Γ) (tCase ci (set_pparams p (map (fun '(x, _) => x) pars')) c brs) r.
Proof using Type.
intros ci p c brs pars' r hrel h.
inv hrel.
econstructor; tea.
- rewrite /wfTermRel_pred /= !mark_inst_case_predicate_context in X |- *.
  destruct X as (X & X' & X''); repeat split; auto.
  + replace (pparams p) with (map (fun '(x, _) => x) (map (fun x => (x, tt)) (pparams p))) in X by rewrite map_map map_id //.
    clear -X h. induction h as [[][]?[]|]; unfold on_Trel in *; cbn in *.
  * inv X; destruct X0; constructor => //.
    eexists. now inv o.
  * inv X. constructor; auto.
  + apply OnOne2_length in h. len in h; len. congruence.
- unfold wfTermRel_branch in *; solve_all.
  + apply OnOne2_length in h. len in h; len. congruence.
  + rewrite !mark_inst_case_branch_context // in b |- *.
Qed.

Lemma red_case_one_brs_rel :
forall ci p c brs brs' r,
  isTermRel Σ (marks_of_context Γ) (tCase ci p c (map recomp_branch brs)) r ->
  red1_one_branch p Γ brs (map decomp_branch brs') ->
  isTermRel Σ (marks_of_context Γ) (tCase ci p c brs') r.
Proof using Type.
intros ci p c brs brs' r hrel h.
inv hrel.
econstructor; tea.
rewrite /wfTermRel_branch /= in X0 |- *.
rewrite (map_decomp_recomp brs').
clear -X0 h. induction h as [[][]?[]|]; unfold on_Trel in *; cbn in *; subst.
* inv X0; destruct X; constructor => //.
  split; auto.
  eexists. rewrite -marks_of_context_app. now inv o.
* inv X0. constructor; auto.
Qed.


Lemma red_fix_one_ty_rel :
forall mfix idx mfix' r,
  isTermRel Σ (marks_of_context Γ) (tFix (map recomp_def mfix) idx) r ->
  red1_one_term Γ mfix (map decomp_def mfix') ->
  isTermRel Σ (marks_of_context Γ) (tFix mfix' idx) r.
Proof using Type.
intros mfix idx mfix' r hrel h.
inv hrel.
eassert (∑ d, binder_relevance (dname def) = binder_relevance (dname d) × nth_error mfix' idx = Some d) as (d & -> & ?).
1: {
  rewrite nth_error_map in H; destruct nth_error eqn: Heq => //.
  edestruct (red1_one_term_binder_relevance _ _ h) as (d' & Heq2 & e); tea.
  rewrite nth_error_map in Heq2; destruct (nth_error mfix' _) eqn: Heq3 => //.
  eexists; split; [|reflexivity].
  inversion H; inversion Heq2; subst. rewrite -e. destruct p as (? & (? & ?) & ?) => //.
}
econstructor; tea.
rewrite /wfTermRel_mfix /= in X |- *.
remember (marks_of_context (fix_context mfix')) as mfixcontext eqn:HH.
rewrite (map_decomp_recomp_def mfix') in HH |- *.
assert (mfixcontext = marks_of_context (fix_context (map recomp_def mfix))).
{
  rewrite HH /marks_of_context /fix_context !map_rev !map_mapi mapi_map /= mapi_cst_map mapi_map /= mapi_cst_map.
  f_equal. clear -h. induction h as [(?&(?&?)&?)(?&(?&?)&?)?[]|]; unfold on_Trel in *; cbn in *.
  all: f_equal; auto.
  now noconf o0. } rewrite -H0 in X. clear HH H0.
clear -X h. induction h as [(?&(?&?)&?)(?&(?&?)&?)?[]|]; unfold on_Trel in *; cbn in *; try noconf o0; subst.
* inv X; destruct X0; constructor => //.
  split; auto.
  now inv o.
* inv X. constructor; auto.
Qed.

Lemma red_fix_one_body_rel :
forall mfix idx mfix' r,
  isTermRel Σ (marks_of_context Γ) (tFix (map recomp_def' mfix) idx) r ->
  red1_one_term (Γ ,,, fix_context (map recomp_def' mfix)) mfix (map decomp_def' mfix') ->
  isTermRel Σ (marks_of_context Γ) (tFix mfix' idx) r.
Proof using Type.
intros mfix idx mfix' r hrel h.
inv hrel.
eassert (∑ d, binder_relevance (dname def) = binder_relevance (dname d) × nth_error mfix' idx = Some d) as (d & -> & ?).
1: {
  rewrite nth_error_map in H; destruct nth_error eqn: Heq => //.
  edestruct (red1_one_term_binder_relevance _ _ h) as (d' & Heq2 & e); tea.
  rewrite nth_error_map in Heq2; destruct (nth_error mfix' _) eqn: Heq3 => //.
  eexists; split; [|reflexivity].
  inversion H; inversion Heq2; subst. rewrite -e. destruct p as (? & (? & ?) & ?) => //.
}
econstructor; tea.
rewrite /wfTermRel_mfix /= in X |- *.
apply fix_context_red1 in h as Heqmfix.
remember (fix_context mfix') as fixcontext eqn:HH.
rewrite Heqmfix in X, h.
clear HH Heqmfix.
rewrite (map_decomp_recomp_def' mfix').
clear -X h. induction h as [(?&(?&?)&?)(?&(?&?)&?)?[]|]; unfold on_Trel in *; cbn in *; try noconf o0; subst.
* inv X; destruct X0; constructor => //=.
  cbn in i.
  split; auto.
  inv o. rewrite marks_of_context_app in X, X0.
  eapply isTermRel_inj with (1 := X) in i as <- => //.
* inv X. constructor; auto.
Qed.


Lemma red_cofix_one_ty_rel :
forall mfix idx mfix' r,
  isTermRel Σ (marks_of_context Γ) (tCoFix (map recomp_def mfix) idx) r ->
  red1_one_term Γ mfix (map decomp_def mfix') ->
  isTermRel Σ (marks_of_context Γ) (tCoFix mfix' idx) r.
Proof using Type.
intros mfix idx mfix' r hrel h.
inv hrel.
eapply red_fix_one_ty_rel in h.
2: econstructor; tea.
inv h; econstructor; tea.
Qed.

Lemma red_cofix_one_body_rel :
forall mfix idx mfix' r,
  isTermRel Σ (marks_of_context Γ) (tCoFix (map recomp_def' mfix) idx) r ->
  red1_one_term (Γ ,,, fix_context (map recomp_def' mfix)) mfix (map decomp_def' mfix') ->
  isTermRel Σ (marks_of_context Γ) (tCoFix mfix' idx) r.
Proof using Type.
intros mfix idx mfix' r hrel h.
inv hrel.
eapply red_fix_one_body_rel in h.
2: econstructor; tea.
inv h; econstructor; tea.
Qed. *)

