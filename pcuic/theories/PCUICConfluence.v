(* Distributed under the terms of the MIT license. *)
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICTactics PCUICLiftSubst PCUICTyping
     PCUICReduction PCUICEquality PCUICEqualityLemmas PCUICUnivSubstitutionConv
     PCUICSigmaCalculus PCUICContextReduction
     PCUICParallelReduction PCUICParallelReductionConfluence PCUICClosedConv PCUICClosedTyp
     PCUICRedTypeIrrelevance PCUICClosed PCUICOnFreeVars PCUICInstDef PCUICInstConv PCUICWeakeningConv PCUICWeakeningTyp PCUICSubstitution.


(* We show that conversion/cumulativity starting from well-typed terms is transitive.
  We first use typing to decorate the reductions/comparisons with invariants
  showing that all the considered contexts/terms are well-scoped. In a second step
  we use confluence of reduction on well-scoped terms [ws_red_confluence], which also
  commutes with alpha,universe-equivalence of contexts and terms [red1_eq_context_upto_l].
  We can drop the invariants on free variables at each step as reduction preserves free-variables,
  so we also have [red_confluence]: as long as the starting contexts and terms are well-scoped
  confluence holds. *)

Require Import ssreflect ssrbool.

From Equations Require Import Equations.
Require Import CRelationClasses CMorphisms.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Local Ltac intuition_solver ::= auto with *.

#[global]
Instance red_Refl Σ Γ : Reflexive (red Σ Γ) := refl_red Σ Γ.

#[global]
Instance red_Trans Σ Γ : Transitive (red Σ Γ) := red_trans Σ Γ.

#[global]
Instance All_decls_refl P :
  Reflexive P ->
  Reflexive (All_decls P).
Proof. intros hP d; destruct d as [na [b|] ty]; constructor; auto. Qed.

#[global]
Instance All_decls_sym P :
  Symmetric P ->
  Symmetric (All_decls P).
Proof. intros hP d d' []; constructor; now symmetry. Qed.

#[global]
Instance All_decls_trans P :
  Transitive P ->
  Transitive (All_decls P).
Proof. intros hP d d' d'' [] h; depelim h; constructor; now etransitivity. Qed.

#[global]
Instance All_decls_equivalence P :
  Equivalence P ->
  Equivalence (All_decls P).
Proof.
  intros []; split; tc.
Qed.

#[global]
Instance All_decls_preorder P :
  PreOrder P ->
  PreOrder (All_decls P).
Proof.
  intros []; split; tc.
Qed.

#[global]
Instance All_decls_alpha_refl P :
  Reflexive P ->
  Reflexive (All_decls_alpha P).
Proof. intros hP d; destruct d as [na [b|] ty]; constructor; auto. Qed.

#[global]
Instance All_decls_alpha_sym P :
  Symmetric P ->
  Symmetric (All_decls_alpha P).
Proof. intros hP d d' []; constructor; now symmetry. Qed.

#[global]
Instance All_decls_alpha_trans P :
  Transitive P ->
  Transitive (All_decls_alpha P).
Proof. intros hP d d' d'' [] h; depelim h; constructor; now etransitivity. Qed.

#[global]
Instance All_decls_alpha_equivalence P :
  Equivalence P ->
  Equivalence (All_decls_alpha P).
Proof.
  intros []; split; tc.
Qed.

Lemma clos_rt_OnOne2_local_env_incl R :
inclusion (OnOne2_local_env (fun Δ => on_one_decl (clos_refl_trans (R Δ))))
          (clos_refl_trans (OnOne2_local_env (fun Δ => on_one_decl1 R Δ))).
Proof.
  intros x y H.
  induction H; firstorder; try subst na'.
  - induction b. repeat constructor. pcuicfo.
    constructor 2.
    econstructor 3 with (Γ ,, vass na y); auto.
  - subst.
    induction a0. repeat constructor. pcuicfo.
    constructor 2.
    econstructor 3 with (Γ ,, vdef na b' y); auto.
  - subst t'.
    induction a0. constructor. constructor. red. simpl. pcuicfo.
    constructor 2.
    econstructor 3 with (Γ ,, vdef na y t); auto.
  - clear H. induction IHOnOne2_local_env. constructor. now constructor 3.
    constructor 2.
    eapply transitivity. eauto. auto.
Qed.

Lemma All2_fold_refl {A} {P : list A -> list A -> A -> A -> Type} :
  (forall Γ, Reflexive (P Γ Γ)) ->
  Reflexive (All2_fold P).
Proof.
  intros HR x.
  apply All2_fold_refl; intros. apply HR.
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

Lemma OnOne2_apply {A B} (P : B -> A -> A -> Type) l l' :
  OnOne2 (fun x y => forall a : B, P a x y) l l' ->
  forall a : B, OnOne2 (P a) l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2_apply_All {A} (Q : A -> Type) (P : A -> A -> Type) l l' :
  OnOne2 (fun x y => Q x -> P x y) l l' ->
  All Q l ->
  OnOne2 P l l'.
Proof.
  induction 1; constructor; auto.
  now depelim X. now depelim X0.
Qed.

Lemma OnOne2_apply_forallb {A} (p : A -> bool) (P : A -> A -> Type) l l' :
  OnOne2 (fun x y => p x -> P x y) l l' ->
  forallb p l ->
  OnOne2 P l l'.
Proof.
  induction 1; constructor; auto.
  all: now move/andP: H => [].
Qed.

Lemma OnOne2_apply_left {A B} (P : B -> A -> A -> Type) Q l l' :
  OnOne2 (fun x y => (forall a : B, P a x y) × Q x y) l l' ->
  forall a : B, OnOne2 (Trel_conj (P a) Q) l l'.
Proof.
  induction 1 as [??? []|]; constructor; auto.
Qed.

Lemma OnOne2_apply_left_All {A} (Q : A -> Type) (P R : A -> A -> Type) l l' :
  OnOne2 (fun x y => (Q x -> P x y) × R x y) l l' ->
  All Q l ->
  OnOne2 (Trel_conj P R) l l'.
Proof.
  induction 1 as [??? []|??? X0]; constructor; auto.
  all: now depelim X.
Qed.

Lemma OnOne2_apply_left_forallb {A} (p : A -> bool) (P R : A -> A -> Type) l l' :
  OnOne2 (fun x y => (p x -> P x y) × R x y) l l' ->
  forallb p l ->
  OnOne2 (Trel_conj P R) l l'.
Proof.
  induction 1 as [??? []|]; constructor; auto.
  all: now move/andP: H => [].
Qed.

Lemma OnOne2_sigma {A B} (P : B -> A -> A -> Type) l l' :
  OnOne2 (fun x y => ∑ a : B, P a x y) l l' ->
  ∑ a : B, OnOne2 (P a) l l'.
Proof.
  induction 1.
  - exists p.π1. constructor; auto. exact p.π2.
  - exists IHX.π1. constructor; auto. exact IHX.π2.
Qed.

Lemma OnOne2_local_env_apply {B} {P : B -> context -> term -> term -> Type} {l l'}
  (f : context -> term -> term -> B) :
  OnOne2_local_env (fun Γ => on_one_decl (fun x y => forall a : B, P a Γ x y)) l l' ->
  OnOne2_local_env (fun Γ => on_one_decl (fun x y => P (f Γ x y) Γ x y)) l l'.
Proof.
  intros; eapply OnOne2_local_env_impl; tea.
  intros Δ x y. eapply on_one_decl_impl; intros Γ ? ?; eauto.
Qed.

Lemma OnOne2_local_env_apply_dep {B : context -> term -> term -> Type}
  {P : context -> term -> term -> Type} {l l'} :
  (forall Γ' x y, B Γ' x y) ->
  OnOne2_local_env (fun Γ => on_one_decl (fun x y => B Γ x y -> P Γ x y)) l l' ->
  OnOne2_local_env (fun Γ => on_one_decl (fun x y => P Γ x y)) l l'.
Proof.
  intros; eapply OnOne2_local_env_impl; tea.
  intros Δ x y. eapply on_one_decl_impl; intros Γ ? ?; eauto.
Qed.

Lemma OnOne2_exist' {A} (P Q R : A -> A -> Type) (l l' : list A) :
  OnOne2 P l l' ->
  (forall x y : A, P x y -> ∑ z : A, Q x z × R y z) ->
  ∑ r : list A, OnOne2 Q l r × OnOne2 R l' r.
Proof.
  intros o Hp. induction o.
  - specialize (Hp _ _ p) as [? []].
    eexists; split; constructor; eauto.
  - exists (hd :: IHo.π1). split; constructor; auto; apply IHo.π2.
Qed.

Lemma OnOne2_local_env_exist' (P Q R : context -> term -> term -> Type) (l l' : context) :
  OnOne2_local_env (fun Γ => on_one_decl1 P Γ) l l' ->
  (forall Γ x y, P Γ x y -> ∑ z : term, Q Γ x z × R Γ y z) ->
  ∑ r : context, OnOne2_local_env (fun Γ => on_one_decl1 Q Γ) l r × OnOne2_local_env (fun Γ => on_one_decl1 R Γ) l' r.
Proof.
  intros o Hp. induction o.
  - destruct p; subst. specialize (Hp _ _ _ p) as [? []].
    eexists; split; constructor; red; cbn; eauto.
  - destruct p; subst.
    destruct s as [[p ->]|[p ->]]; specialize (Hp _ _ _ p) as [? []];
    eexists; split; constructor; red; cbn; eauto.
  - exists (d :: IHo.π1). split; constructor; auto; apply IHo.π2.
Qed.

Lemma OnOne2_local_env_All2_fold (P : context -> term -> term -> Type)
  (Q : context -> context -> context_decl -> context_decl -> Type)
  (l l' : context) :
  OnOne2_local_env (fun Γ => on_one_decl1 P Γ) l l' ->
  (forall Γ x y, on_one_decl1 P Γ x y -> Q Γ Γ x y) ->
  (forall Γ Γ' d, OnOne2_local_env (fun Γ => on_one_decl1 P Γ) Γ Γ' -> Q Γ Γ' d d) ->
  (forall Γ x, Q Γ Γ x x) ->
  All2_fold Q l l'.
Proof.
  intros onc HP IHQ HQ. induction onc; simpl; try constructor; eauto.
  now eapply All2_fold_refl.
  now eapply All2_fold_refl.
Qed.

Lemma OnOne2_disj {A} (P Q : A -> A -> Type) (l l' : list A) :
  OnOne2 (fun x y => P x y + Q x y)%type l l' <~>
  OnOne2 P l l' + OnOne2 Q l l'.
Proof.
  split.
  - induction 1; [destruct p|destruct IHX]; try solve [(left + right); constructor; auto].
  - intros []; eapply OnOne2_impl; tea; eauto.
Qed.

Notation red1_ctx_rel Σ Δ :=
  (OnOne2_local_env
    (fun (Γ : context) => on_one_decl
      (fun (t u : term) => red1 Σ (Δ ,,, Γ) t u))).

Notation eq_one_decl Σ cmp_universe cmp_sort pb :=
  (OnOne2_local_env
    (fun _ => on_one_decl
      (fun (t u : term) =>
        eq_term_upto_univ Σ cmp_universe cmp_sort pb t u))).

Lemma red_context_rel_inst_case_context {cf : checker_flags} Σ (wfΣ : wf Σ) Γ pars pars' puinst pctx :
  wf_term_ctx Γ ->
  forallb wf_term pars ->
  closedn_ctx #|pars| pctx ->
  All2 (red Σ Γ) pars pars' ->
  red_context_rel Σ Γ
    (inst_case_context pars puinst pctx)
    (inst_case_context pars' puinst pctx).
Proof using Type.
  intros wfΓ onpars onpctx a.
  rewrite /inst_case_context.
  eapply @red_red_ctx_rel0; eauto.
  instantiate (1 := fake_params #|pars|).
  - rewrite wf_term_ctx_app wfΓ.
    eapply closedn_ctx_wf_term_ctx with (n := 0).
    apply closed_fake_params.
  - rewrite wf_term_ctx_subst_instance.
    now eapply closedn_ctx_wf_term_ctx.
  - now apply All2_rev.
  - rewrite forallb_rev //.
  - apply untyped_subslet_ass.
    + apply is_assumption_context_fake_params.
    + len.
Qed.

Lemma red_context_rel_fix_context {cf : checker_flags} Σ (wfΣ : wf Σ) Γ mfix mfix' :
  wf_term_ctx Γ ->
  wf_term_mfix mfix ->
  All2 (fun d d' => red Σ Γ (dtype d) (dtype d') × dname d = dname d') mfix mfix' ->
  red_context_rel Σ Γ (fix_context mfix) (fix_context mfix').
Proof.
  intros wfΓ wfmfix Hmfix.
  apply All2_length in Hmfix as hlen.
  apply All2_rev in Hmfix. rewrite -forallb_rev in wfmfix.
  rewrite /fix_context !rev_mapi -hlen.
  assert (forall n, Nat.pred #|mfix| - n = #|mfix| - S n) as HM by lia.
  erewrite mapi_ext. 2: intros; rewrite HM; reflexivity.
  erewrite (mapi_ext _ _ (List.rev mfix')). 2: intros; rewrite HM; reflexivity.
  rewrite /mapi -List.rev_length.
  induction Hmfix in wfmfix |- * => //=.
  1: now constructor.
  rewrite !mapi_rec_Sk -!/(mapi _ _).
  cbn in wfmfix. move/andP: wfmfix => [] /andP[] wfb wft wfmfix.
  constructor. 1: now eapply IHHmfix.
  rewrite Nat.sub_0_r.
  clear IHHmfix wfmfix.
  destruct r as (redty & <-).
  constructor; tas.
  eapply weakening_red_0; trea.
  len.
Qed.

Lemma red_context_rel_eq_term_upto {cf : checker_flags} {Σ : global_env} {wfΣ : wf Σ} {cmp_universe cmp_sort pb napp Γ Δ Δ' u v} :
  red_context_rel Σ Γ Δ Δ' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort (Γ ,,, Δ) pb napp u v ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort (Γ ,,, Δ') pb napp u v.
Proof.
  intro X.
  apply red_context_eq_term_upto.
  apply red_context_app; tas.
  reflexivity.
Qed.

Lemma red_context_rel_eq_mfixpoint {cf : checker_flags} {Σ : global_env} {wfΣ : wf Σ} {cmp_universe cmp_sort pb napp Γ Δ Δ' mfix mfix'} :
  red_context_rel Σ Γ Δ Δ' ->
  eq_mfixpoint0 (fun Γ u v => eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v) Γ Δ mfix mfix' ->
  eq_mfixpoint0 (fun Γ u v => eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v) Γ Δ' mfix mfix'.
Proof.
  intros.
  solve_all.
  now eapply red_context_rel_eq_term_upto.
Qed.


Lemma red1_eq_context_upto_l {cf : checker_flags} {Σ} {wfΣ : wf Σ} {cmp_universe cmp_sort pb Γ Δ u v} :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  wf_term_ctx Γ ->
  wf_term u ->
  red1 Σ Γ u v ->
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
  ∑ v', red1 Σ Δ u v' *
        eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv v v'.
Proof.
  intros refl_univ_conv refl_univ_pb refl_sort_conv refl_sort_pb wfΓ wfu h e.
  induction h in wfΓ, wfu, Δ, e |- * using red1_ind_all; inv_wf_term.
  all: try solve [
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | eapply eq_term_upto_univ_refl ; eauto
    ]
  ].
  all: try solve [
    destruct (IHh _ wfΓ ltac:(assumption) e) as [? [? ?]] ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor; eauto ;
      eapply eq_term_upto_univ_refl ; eauto
    ]
  ].
  all: try solve [
    match goal with
    | r : red1 _ (?Γ ,, ?d) _ _ |- _ =>
      assert (e' : eq_context_upto Σ cmp_universe cmp_sort pb (Γ,, d) (Δ,, d))
      ; [
        constructor ; [ eauto | constructor; eauto ] ;
        eapply eq_term_upto_univ_refl ; eauto
      |
      ]
    end;
    destruct (IHh _ ltac:(eauto with fvs) ltac:(assumption) e') as [? [? ?]] ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor ; eauto ;
      eapply eq_term_upto_univ_refl ; eauto
    ]
  ].
  - eapply eq_context_upto_nth_error with (n := i) in e.
    depelim e; rewrite H0 // in H.
    destruct e as ((eqna & eqb) & eqt) => //.
    injection H as [=]. rewrite H in eqb.
    depelim eqb.
    eexists; split.
    + constructor. rewrite H1 /= H2 //.
    + rewrite -(firstn_skipn (S i) Γ) -/(app_context _ _).
      assert (Hlen : #|firstn (S i) Γ| = S i).
      { apply firstn_length_le. now eapply nth_error_Some_length. }
      rewrite -{3 4}Hlen.
      eapply @weakening_eq_term_upto_univ_napp with (Γ' := []) ; eauto.
      rewrite /wf_term_ctx test_context_forallb in wfΓ.
      eapply nth_error_forallb in wfΓ as [X0]%andb_and; tea.
      now rewrite H in X0.

  - eapply OnOne2_prod_inv in X as [_ X].
    eapply OnOne2_apply, OnOne2_apply, OnOne2_apply_forallb, OnOne2_apply in X; tea.
    eapply OnOne2_exist' in X as [pars' [parred pareq]]; intros; tea.
    eexists. split. 1: now eapply case_red_param; tea.
    econstructor; eauto.
    + red. intuition; eauto.
    + reflexivity.
    + reflexivity.
  - specialize (IHh (Δ ,,, inst_case_predicate_context p)).
    forward IHh by now apply wf_term_ctx_app_inst_case_context.
    forward IHh by tas.
    forward IHh.
    { eapply eq_context_upto_cat => //.
      now apply eq_context_upto_rel_refl. }
    destruct IHh as [? [? ?]].
    eexists. split.
    + solve [ econstructor ; eauto ].
    + econstructor; try reflexivity.
      red; intuition auto; try reflexivity.
      now eapply All2_same.
  - specialize (IHh _ wfΓ ltac:(assumption) e) as [? [? ?]].
    eexists. split.
    + solve [ econstructor ; eauto ].
    + econstructor; try reflexivity.
      assumption.
  - apply forallb_All in b.
    apply OnOne2_prod_assoc in X as [_ X].
    eapply OnOne2_All_mix_left in X; tea.
    eapply (OnOne2_impl (Q:=fun x y => (∑ v', _) × bcontext x = bcontext y)) in X; tea.
    2:{ intros x y [[IH eq] [wfbrctx wfb]%andb_and]. split; tas.
        specialize (IH (Δ ,,, inst_case_branch_context p x)).
        forward IH by now apply wf_term_ctx_app_inst_case_context.
        forward IH by tas.
        forward IH by now apply eq_context_upto_cat. exact IH. }
    eapply (OnOne2_exist' _ (fun x y => on_Trel_eq (red1 Σ (Δ ,,, inst_case_branch_context p x)) bbody bcontext x y)
      (fun x y => on_Trel_eq (eq_term_upto_univ Σ cmp_universe cmp_sort (Γ ,,, inst_case_branch_context p x) Conv) bbody bcontext x y)) in X as [brr [Hred Heq]]; tea.
    2:{ intros x y [[v' [redv' eq]] eqctx].
        exists {| bcontext := bcontext x; bbody := v' |}.
        intuition auto. rewrite /inst_case_branch_context -eqctx //. }
    eexists; split.
    eapply case_red_brs; tea.
    econstructor; eauto; try reflexivity.
    eapply OnOne2_All2; tea => /=; unfold eq_branch; intuition eauto; try reflexivity.
    now rewrite b3.

  - destruct (IHh _ wfΓ ltac:(assumption) e) as [x [redl redr]].
    exists (tApp x M2).
    split. constructor; auto.
    constructor. 2: reflexivity.
    eapply eq_term_upto_univ_impl. 6:eauto.
    all:auto. 1-4:typeclasses eauto.

  - eapply OnOne2_prod_inv in X as [_ X].
    eapply OnOne2_apply, OnOne2_apply, OnOne2_apply_forallb, OnOne2_apply in X; tea.
    eapply OnOne2_exist' in X as [l'' [Hred Heq]]; intros; tea.
    eexists. split.
    + eapply evar_red. eassumption.
    + constructor. eapply OnOne2_All2; tea => //. reflexivity.

  - apply forallb_All in wfu. eapply OnOne2_All_mix_left in X; tea. cbn in X.
    set (Q d d' := red1 Σ Δ d.(dtype) d'.(dtype) × (d.(dname), d.(dbody), d.(rarg)) = (d'.(dname), d'.(dbody), d'.(rarg))).
    set (R d d' := eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv d.(dtype) d'.(dtype) × eq_term_upto_univ Σ cmp_universe cmp_sort (Γ ,,, fix_context mfix1) Conv d.(dbody) d'.(dbody) × d.(rarg) = d'.(rarg) × eq_binder_annot d.(dname) d'.(dname)).
    eapply (OnOne2_exist' _ Q R) in X as [mfix' [Hred Heq]]; tea.
    2: { intros d d' [[[_ IH] eq] [wft wfb]%andb_and].
      specialize (IH _ wfΓ wft e) as (t' & Hred & Heq).
      eexists {| dtype := t' |}; split; [split|].
      1-2: eassumption.
      repeat split; auto. reflexivity. }
    eexists. split.
    + eapply fix_red_ty. eassumption.
    + constructor. eapply OnOne2_All2; tea. 1: unfold R; auto. intro; repeat split; reflexivity.

  - apply OnOne2_eq_fixcontext in X as eqfixc.
    assert (wfmfix: wf_term_ctx (Γ ,,, fix_context mfix0)) by now apply wf_term_app_fix_context.
    apply forallb_All in wfu. eapply OnOne2_All_mix_left in X; tea. cbn in X.
    set (Q d d' := red1 Σ (Δ ,,, fix_context mfix0) d.(dbody) d'.(dbody) × (d.(dname), d.(dtype), d.(rarg)) = (d'.(dname), d'.(dtype), d'.(rarg))).
    set (R d d' := eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv d.(dtype) d'.(dtype) × eq_term_upto_univ Σ cmp_universe cmp_sort (Γ ,,, fix_context mfix1) Conv d.(dbody) d'.(dbody) × d.(rarg) = d'.(rarg) × eq_binder_annot d.(dname) d'.(dname)).
    eapply (OnOne2_exist' _ Q R) in X as [mfix' [Hred Heq]]; tea.
    2: { intros d d' [[[_ IH] eq] [wft wfb]%andb_and].
      specialize (IH (Δ ,,, fix_context mfix0) wfmfix wfb).
      forward IH. { eapply eq_context_upto_cat; tas. reflexivity. }
      destruct IH as (b' & Hred & Heq).
      eexists {| dbody := b' |}; split; [split|].
      1-2: eassumption.
      repeat split; auto. 1: reflexivity. eapply eq_term_upto_univ_eq_ctx; tea. rewrite -eqfixc. reflexivity. }
    eexists. split.
    + eapply fix_red_body. eassumption.
    + constructor. eapply OnOne2_All2; tea. 1: unfold R; auto. intro; repeat split; reflexivity.


  - apply forallb_All in wfu. eapply OnOne2_All_mix_left in X; tea. cbn in X.
    set (Q d d' := red1 Σ Δ d.(dtype) d'.(dtype) × (d.(dname), d.(dbody), d.(rarg)) = (d'.(dname), d'.(dbody), d'.(rarg))).
    set (R d d' := eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv d.(dtype) d'.(dtype) × eq_term_upto_univ Σ cmp_universe cmp_sort (Γ ,,, fix_context mfix1) Conv d.(dbody) d'.(dbody) × d.(rarg) = d'.(rarg) × eq_binder_annot d.(dname) d'.(dname)).
    eapply (OnOne2_exist' _ Q R) in X as [mfix' [Hred Heq]]; tea.
    2: { intros d d' [[[_ IH] eq] [wft wfb]%andb_and].
      specialize (IH _ wfΓ wft e) as (t' & Hred & Heq).
      eexists {| dtype := t' |}; split; [split|].
      1-2: eassumption.
      repeat split; auto. reflexivity. }
    eexists. split.
    + eapply cofix_red_ty. eassumption.
    + constructor. eapply OnOne2_All2; tea. 1: unfold R; auto. intro; repeat split; reflexivity.

  - apply OnOne2_eq_fixcontext in X as eqfixc.
    assert (wfmfix: wf_term_ctx (Γ ,,, fix_context mfix0)) by now apply wf_term_app_fix_context.
    apply forallb_All in wfu. eapply OnOne2_All_mix_left in X; tea. cbn in X.
    set (Q d d' := red1 Σ (Δ ,,, fix_context mfix0) d.(dbody) d'.(dbody) × (d.(dname), d.(dtype), d.(rarg)) = (d'.(dname), d'.(dtype), d'.(rarg))).
    set (R d d' := eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv d.(dtype) d'.(dtype) × eq_term_upto_univ Σ cmp_universe cmp_sort (Γ ,,, fix_context mfix1) Conv d.(dbody) d'.(dbody) × d.(rarg) = d'.(rarg) × eq_binder_annot d.(dname) d'.(dname)).
    eapply (OnOne2_exist' _ Q R) in X as [mfix' [Hred Heq]]; tea.
    2: { intros d d' [[[_ IH] eq] [wft wfb]%andb_and].
      specialize (IH (Δ ,,, fix_context mfix0) wfmfix wfb).
      forward IH. { eapply eq_context_upto_cat; tas. reflexivity. }
      destruct IH as (b' & Hred & Heq).
      eexists {| dbody := b' |}; split; [split|].
      1-2: eassumption.
      repeat split; auto. 1: reflexivity. eapply eq_term_upto_univ_eq_ctx; tea. rewrite -eqfixc. reflexivity. }
    eexists. split.
    + eapply cofix_red_body. eassumption.
    + constructor. eapply OnOne2_All2; tea. 1: unfold R; auto. intro; repeat split; reflexivity.

  - eapply OnOne2_prod_inv in X as [_ X].
    eapply OnOne2_apply, OnOne2_apply, OnOne2_apply_forallb, OnOne2_apply in X; tea.
    eapply OnOne2_exist' in X as [ll' [llred lleq]]; intros; tea.
    eexists. split.
    + eapply array_red_val; tea.
    + do 2 constructor; cbn; trea.
      eapply OnOne2_All2; tea; auto. reflexivity.
  - specialize (IHh _ wfΓ ltac:(assumption) e) as [v' []].
    eexists; split.
    + eapply array_red_def; eauto.
    + do 2 constructor; cbn; eauto. reflexivity.
      eapply All2_refl; reflexivity.
  - specialize (IHh _ wfΓ ltac:(assumption) e) as [v' []].
    eexists; split.
    + eapply array_red_type; eauto.
    + do 2 constructor; cbn; trea.
      eapply All2_refl; reflexivity.
Qed.

(* Lemma red1_eq_context_upto_univ_l {Σ Σ' cmp_universe cmp_sort Γ ctx ctx' ctx''} :
  RelationClasses.PreOrder (cmp_universe Conv) ->
  RelationClasses.PreOrder (cmp_sort Conv) ->
  eq_context_gen (fun pb => eq_term_upto_univ Σ' cmp_universe cmp_sort pb) Conv ctx ctx' ->
  OnOne2_local_env (fun (Γ' : context) => on_one_decl
    (fun (u v : term) => forall (pb : conv_pb) (napp : nat) (u' : term),
    eq_term_upto_univ_napp Σ' cmp_universe cmp_sort pb napp u u' ->
    ∑ v' : term,
      red1 Σ (Γ ,,, Γ') u' v'
      × eq_term_upto_univ_napp Σ' cmp_universe cmp_sort pb napp v v')) ctx ctx'' ->
  ∑ pctx,
    red1_ctx_rel Σ Γ ctx' pctx *
    eq_context_gen (fun pb => eq_term_upto_univ Σ' cmp_universe cmp_sort pb) Conv ctx'' pctx.
Proof.
  intros preorder_univ_conv preorder_sort_conv e X.
  induction X in e, ctx' |- *.
  - red in p. simpl in p.
    depelim e. depelim c.
    destruct p as [-> p].
    eapply p in eqt as hh ; eauto.
    destruct hh as [? [? ?]].
    eapply red1_eq_context_upto_l in r; cycle -1.
    { eapply eq_context_upto_cat; tea.
      reflexivity. }
    all:try tc.
    destruct r as [v' [redv' eqv']].
    eexists; split.
    + constructor; tea. red. cbn. split; tea. reflexivity.
    + constructor. all: eauto. constructor; auto.
      now transitivity x.
  - depelim e.
    depelim c.
    destruct p as [-> [[p ->]|[p ->]]].
    { eapply p in eqt as hh ; eauto.
      destruct hh as [? [? ?]].
      eapply red1_eq_context_upto_l in r; cycle -1.
      { eapply eq_context_upto_cat; tea.
        reflexivity. }
      all:try tc.
      destruct r as [v' [redv' eqv']].
      eexists; split.
      + constructor; tea. red. cbn. split; tea. reflexivity.
        left. split; tea. reflexivity.
      + constructor. all: eauto. constructor; auto.
        now transitivity x. }
    { eapply p in eqb as hh ; eauto.
      destruct hh as [? [? ?]].
      eapply red1_eq_context_upto_l in r; cycle -1.
      { eapply eq_context_upto_cat; tea.
        reflexivity. }
      all:try tc.
      destruct r as [v' [redv' eqv']].
      eexists; split.
      + constructor; tea. red. cbn. split; tea. reflexivity.
        right. split; tea. reflexivity.
      + constructor. all: eauto. constructor; auto.
        now transitivity x. }
  - depelim e.
    destruct (IHX _ e) as [? [? ?]].
    eexists. split.
    + now eapply onone2_localenv_cons_tl.
    + constructor. all: eauto.
Qed. *)


Lemma red1_eq_term_upto_univ_l {cf : checker_flags} {Σ : global_env} {wfΣ : wf Σ} cmp_universe cmp_sort pb napp Γ u v u' :
  RelationClasses.PreOrder (cmp_universe Conv) ->
  RelationClasses.PreOrder (cmp_universe pb) ->
  RelationClasses.PreOrder (cmp_sort Conv) ->
  RelationClasses.PreOrder (cmp_sort pb) ->
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_universe Conv) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_sort Conv) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_sort pb) ->
  wf_term_ctx Γ ->
  wf_term u ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u u' ->
  red1 Σ Γ u v ->
  ∑ v', red1 Σ Γ u' v' *
        eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp v v'.
Proof.
  intros preorder_univ_conv preorder_univ_pb preorder_sort_conv preorder_sort_pb
    sub_univ sub_sort substu_univ substu_sort_conv substu_sort_pb wfΓ wfu e h.
  induction h in pb, napp, u', e, preorder_univ_pb, preorder_sort_pb, sub_univ, sub_sort, substu_sort_pb, wfΓ, wfu |- * using red1_ind_all.
  all: inv_wf_term.

  - dependent destruction e. dependent destruction e1.
    eexists. split.
    + constructor.
    + eapply eq_term_upto_univ_napp_subst0 with (Γ' := [_]) ; eauto ; cycle -1.
      * eapply leq_term_leq_term_napp; eauto.
      * now cbn; auto.
  - dependent destruction e.
    eexists. split.
    + constructor.
    + eapply eq_term_upto_univ_napp_subst0 with (Γ' := [_]) ; eauto ; cycle -1.
      * eapply leq_term_leq_term_napp; eauto.
      * now cbn; auto.
  - dependent destruction e.
    eexists. split.
    + constructor. eassumption.
    + eapply eq_term_upto_univ_refl ; tc.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e0 as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    eapply All2_nth_error_Some in e1 as [t' [hnth [eqctx eqbod]]]; tea.
    have lenctxass := eq_context_upto_names_context_assumptions eqctx.
    have lenctx := All2_length eqctx.
    eexists. split.
    + constructor; tea.
      epose proof (All2_length h2). congruence.
    + eapply nth_error_forallb in b as []%andb_and; tea.
      apply eq_term_upto_univ_iota_red; eauto.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in e as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    unfold unfold_fix in H.
    destruct (nth_error mfix idx) as [d|] eqn:hnth => //. noconf H.
    eapply All2_nth_error_Some in e as hh ; try eassumption.
    destruct hh as [d' [e' (? & ? & erarg & eann)]].
    unfold is_constructor in H0.
    destruct (nth_error args (rarg d)) as [a'|] eqn:ea => //.
    eapply All2_nth_error_Some in ea as hh ; try eassumption.
    destruct hh as [a'' [ea' ?]].
    eexists. split.
    + eapply red_fix.
      * unfold unfold_fix. rewrite e'; eauto.
      * unfold is_constructor. rewrite <- erarg. rewrite ea'.
        eapply isConstruct_app_eq_term_l ; eassumption.
    + eapply eq_term_upto_univ_napp_mkApps; tas.
      apply eq_term_upto_univ_napp_fix_subst; eauto.
      eapply nth_error_forallb in a; tea.
      move/andP: a => [] //.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e0 as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    unfold unfold_cofix in H.
    destruct (nth_error mfix idx) eqn:hnth; noconf H.
    eapply All2_nth_error_Some in e0 as hh ; tea.
    destruct hh as [d' [e' (? & ? & erarg & eann)]].
    eexists. split.
    + eapply red_cofix_case.
      unfold unfold_cofix. rewrite e'. reflexivity.
    + constructor. all: eauto.
      eapply eq_term_upto_univ_napp_mkApps; tas.
      apply eq_term_upto_univ_napp_cofix_subst; eauto. 1-2: reflexivity.
      eapply nth_error_forallb in a0; tea.
      move/andP: a0 => [] //.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    unfold unfold_cofix in H.
    case_eq (nth_error mfix idx) ;
      try (intros hnth ; rewrite hnth in H ; discriminate H).
    intros d hnth. rewrite hnth in H. inversion H. subst. clear H.
    eapply All2_nth_error_Some in e as hh ; try eassumption.
    destruct hh as [d' [e' (? & ? & erarg & eann)]].
    eexists. split.
    + eapply red_cofix_proj.
      unfold unfold_cofix. rewrite e'. reflexivity.
    + constructor.
      eapply eq_term_upto_univ_napp_mkApps; tas.
      apply eq_term_upto_univ_napp_cofix_subst; eauto. 1-2: reflexivity.
      eapply nth_error_forallb in a; tea.
      move/andP: a => [] //.
  - dependent destruction e.
    eexists. split.
    + econstructor. all: eauto.
    + eapply eq_term_upto_univ_leq with (napp := 0); tea. auto with arith.
      now apply eq_term_upto_univ_subst_instance.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    eapply All2_nth_error_Some in h2 as hh ; try eassumption.
    destruct hh as [arg' [e' ?]].
    eexists. split.
    + constructor. eassumption.
    + eapply eq_term_upto_univ_leq; tea. auto with arith.
  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc.
    eexists; split.
    + now constructor.
    + constructor; tas.
      eapply red1_ctx_eq_term_upto; eauto.
      constructor. constructor; trea.
  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc. 2: eauto with fvs.
    eapply @red1_eq_context_upto_l with (cmp_universe := cmp_universe) (cmp_sort := cmp_sort) in r as [? [? ?]]; cbn; tc; eauto; revgoals.
    { constructor. 1: reflexivity. econstructor; tea. eapply eq_term_upto_univ_leq; eauto. }
    1: eapply eq_term_upto_univ_napp_wf_term; eassumption.
    eexists; split.
    + now constructor.
    + constructor; tas.
      eapply eq_term_upto_univ_trans; tea; tc.
      eapply eq_term_upto_univ_leq; eauto.
  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc.
    eexists; split.
    + now apply letin_red_def.
    + constructor; tas.
      eapply red1_ctx_eq_term_upto; eauto.
      constructor. constructor; trea. right; split; trea.
  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc.
    eexists; split.
    + now apply letin_red_ty.
    + constructor; tas.
      eapply red1_ctx_eq_term_upto; eauto.
      constructor. constructor; trea. left; split; trea.
  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc. 2: eauto with fvs.
    eapply @red1_eq_context_upto_l with (cmp_universe := cmp_universe) (cmp_sort := cmp_sort) in r0 as [? [? ?]]; tc; eauto with fvs; revgoals.
    { constructor. 1: reflexivity. econstructor; tea. eapply eq_term_upto_univ_leq; eauto. }
    1: eapply eq_term_upto_univ_napp_wf_term; eassumption.
    eexists; split.
    + now apply letin_red_body.
    + constructor; tas.
      eapply eq_term_upto_univ_trans; tea; tc.
      eapply eq_term_upto_univ_leq; eauto.
  - dependent destruction e.
    destruct e as [? [? [? ?]]].
    eapply OnOne2_prod_inv in X as [X0 X].
    assert (∑ args,
        OnOne2 (red1 Σ Γ) (pparams p') args *
        All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) params' args
    ) as [pars0 [? ?]].
    { eapply OnOne2_All2_forallb_exists; tea. cbn.
      intros ??? IH ??. apply IH; tea; cbnr. }
    eexists. split.
    + eapply case_red_param. eassumption.
    + constructor; tea.
      * red; intuition eauto.
        eapply red_context_rel_eq_term_upto; tea.
        eapply red_context_rel_inst_case_context; tea.
        apply OnOne2_All2 with (1 := X0) => //. apply red1_red.
      * unfold eq_branches, eq_branch in *. change (is_true ?q) with (is_true (false || q)) in a. clear a0. solve_all.
        eapply red_context_rel_eq_term_upto; tea.
        eapply red_context_rel_inst_case_context; tea.
        apply OnOne2_All2 with (1 := X0) => //. apply red1_red.
  - depelim e.
    destruct e as [? [? [? ?]]].
    assert (wf_term_ctx (Γ ,,, inst_case_predicate_context p)).
      by apply wf_term_ctx_app_inst_case_context.
    assert (wf_term (preturn p')). by eapply eq_term_upto_univ_napp_wf_term; tea.
    edestruct IHh as (v' & red & eq); revgoals; tea; tc.
    eapply red1_eq_context_upto_l in red; revgoals; tea.
    1:{ eapply eq_context_upto_cat.
        2: apply eq_context_inst_case_context.
        all: tea.
        reflexivity. }
    all:tc.
    destruct red as [ret' [redret eqret]].
    eexists; split.
    + eapply case_red_return; tea.
    + econstructor; eauto.
      red; simpl; intuition eauto.
      eapply eq_term_upto_univ_trans; tea; tc.
  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc.
    eexists; split.
    + eapply case_red_discr; tea.
    + constructor; tas.

  - depelim e.
    assert (h : ∑ brs0,
      OnOne2 (fun br br' =>
        on_Trel_eq (red1 Σ (Γ ,,, inst_case_branch_context p' br)) bbody bcontext br br') brs' brs0 ×
      eq_branches (fun Γ t u => eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv t u) Γ p brs'0 brs0
    ).
    { eapply OnOne2_All2_forallb_exists; tea. cbn.
      intros br br' br'' [[? IH] ?] (?&?)%andb_and [].
      assert (wf_term_ctx (Γ,,, inst_case_branch_context p br)).
        by apply wf_term_ctx_app_inst_case_context.

      edestruct IH as [t [r' e']]; revgoals; tea; cbnr.

      eapply (red1_eq_context_upto_l (Δ := Γ ,,, inst_case_branch_context p' br'')) in r' as (t' & r'' & e''); cycle -1.
      1: { destruct e as (ep & eu & ec & er).
        eapply eq_context_upto_cat.
        2: apply eq_context_inst_case_context.
        all: tea.
        reflexivity. }
      all: tea; tc.
      2: { eapply eq_term_upto_univ_napp_wf_term; eauto with fvs. }

      eexists {| bbody := t' |}; repeat (split; cbn; tas).
      all: rewrite /inst_case_branch_context -e2 //.

      eapply eq_term_upto_univ_trans; tea; tc.
    }
    destruct h as [brs0 [? ?]].
    eexists. split.
    * eapply case_red_brs; tea.
    * constructor. all: eauto.

  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc.
    eexists; split.
    + eapply proj_red; tea.
    + constructor; tas.

  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc.
    eexists; split.
    + eapply app_red_l; tea.
    + constructor; tas.

  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc.
    eexists; split.
    + eapply app_red_r; tea.
    + constructor; tas.

  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc.
    eexists; split.
    + eapply prod_red_l; tea.
    + constructor; tas.
      eapply red1_ctx_eq_term_upto; tea.
      constructor. now constructor.

  - dependent destruction e.
    edestruct IHh as (? & ? & ?); revgoals; tea; tc. 2: eauto with fvs.
    eapply @red1_eq_context_upto_l with (cmp_universe := cmp_universe) (cmp_sort := cmp_sort) in r as [? [? ?]]; cbn; tc; eauto; revgoals.
    { constructor. 1: reflexivity. econstructor; tea. eapply eq_term_upto_univ_leq; eauto. }
    1: eapply eq_term_upto_univ_napp_wf_term; eassumption.
    eexists; split.
    + now apply prod_red_r.
    + constructor; tas.
      eapply eq_term_upto_univ_trans; tea; tc.
      eapply eq_term_upto_univ_leq; eauto.

  - dependent destruction e.
    assert (∑ args,
        OnOne2 (red1 Σ Γ) args' args *
        All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) l' args
    ) as (args & ? & ?).
    { eapply OnOne2_All2_forallb_exists; tea. cbn.
      intros ??? IH ??. apply IH; tea; cbnr. }
    eexists. split.
    + eapply evar_red. eassumption.
    + constructor. all: eauto.

  - dependent destruction e.
    assert (h : ∑ mfix,
      OnOne2 (fun d0 d1 =>
          red1 Σ Γ d0.(dtype) d1.(dtype) ×
          (d0.(dname), d0.(dbody), d0.(rarg)) =
          (d1.(dname), d1.(dbody), d1.(rarg))
        ) mfix' mfix ×
      eq_mfixpoint0 (fun Γ t t' => eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv t t') Γ (fix_context mfix0) mfix1 mfix
    ).
    { eapply OnOne2_All2_forallb_exists; tea. cbn.
      intros d d' d'' [[hr IH] eq] (wft & wfb)%andb_and (et & eb & en & er).
      noconf eq.
      edestruct IH as (t & r1 & e1); revgoals; tea; cbnr.
      eexists {| dtype := t |}; rdest; cbn; trea.
      all: congruence.
    }
    destruct h as [mfix1' [? ?]].
    eexists. split.
    + eapply fix_red_ty. eassumption.
    + constructor.
      eapply red_context_rel_eq_mfixpoint; tea.
      apply red_context_rel_fix_context; tea.
      eapply OnOne2_All2; tea; auto; intros d d' [[H _] [= eq eq' eq'']]. auto.

  - dependent destruction e.
    assert (wf_term_ctx (Γ ,,, fix_context mfix0)) as wfΓmfix by now apply wf_term_app_fix_context.
    assert (h : ∑ mfix,
      OnOne2 (fun d d' =>
          red1 Σ (Γ ,,, fix_context mfix') d.(dbody) d'.(dbody) ×
          (dname d, dtype d, rarg d) = (dname d', dtype d', rarg d')
        ) mfix' mfix *
      eq_mfixpoint0 (fun Γ t u => eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv t u) Γ (fix_context mfix0) mfix1 mfix
    ).
    { eapply OnOne2_All2_forallb_exists; tea. cbn.
      intros d d' d'' [[hr IH] eq] (wft & wfb)%andb_and (et & eb & en & er).
      noconf eq.
      edestruct IH as (t & r1 & e1); revgoals; tea; cbnr.

      eapply red1_eq_context_upto_l in r1 as [t' [r1' e1']]; cycle -1.
      1:{ eapply eq_context_upto_cat.
          2: apply eq_context_fix_context.
          3: exact e.
          all: tea.
          reflexivity. }
      all: eauto; tc.
      2: now eapply eq_term_upto_univ_napp_wf_term; tea.

      eexists {| dbody := t' |}; rdest; cbn; trea.
      1,3,4: congruence.

      eapply eq_term_upto_univ_trans; tea; tc.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply fix_red_body. eassumption.
    + constructor.
      eapply red_context_rel_eq_mfixpoint; tea.
      apply red_context_rel_fix_context; tea.
      eapply OnOne2_All2; tea; auto; intros d d' [[H _] [= eq eq' eq'']]. rewrite -eq -eq'. split; reflexivity.

  - dependent destruction e.
    assert (h : ∑ mfix,
      OnOne2 (fun d0 d1 =>
          red1 Σ Γ d0.(dtype) d1.(dtype) ×
          (d0.(dname), d0.(dbody), d0.(rarg)) =
          (d1.(dname), d1.(dbody), d1.(rarg))
        ) mfix' mfix ×
      eq_mfixpoint0 (fun Γ t t' => eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv t t') Γ (fix_context mfix0) mfix1 mfix
    ).
    { eapply OnOne2_All2_forallb_exists; tea. cbn.
      intros d d' d'' [[hr IH] eq] (wft & wfb)%andb_and (et & eb & en & er).
      noconf eq.
      edestruct IH as (t & r1 & e1); revgoals; tea; cbnr.
      eexists {| dtype := t |}; rdest; cbn; trea.
      all: congruence.
    }
    destruct h as [mfix1' [? ?]].
    eexists. split.
    + eapply cofix_red_ty. eassumption.
    + constructor.
      eapply red_context_rel_eq_mfixpoint; tea.
      apply red_context_rel_fix_context; tea.
      eapply OnOne2_All2; tea; auto; intros d d' [[H _] [= eq eq' eq'']]. auto.

  - dependent destruction e.
    assert (wf_term_ctx (Γ ,,, fix_context mfix0)) as wfΓmfix by now apply wf_term_app_fix_context.
    assert (h : ∑ mfix,
      OnOne2 (fun d d' =>
          red1 Σ (Γ ,,, fix_context mfix') d.(dbody) d'.(dbody) ×
          (dname d, dtype d, rarg d) = (dname d', dtype d', rarg d')
        ) mfix' mfix *
      eq_mfixpoint0 (fun Γ t u => eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv t u) Γ (fix_context mfix0) mfix1 mfix
    ).
    { eapply OnOne2_All2_forallb_exists; tea. cbn.
      intros d d' d'' [[hr IH] eq] (wft & wfb)%andb_and (et & eb & en & er).
      noconf eq.
      edestruct IH as (t & r1 & e1); revgoals; tea; cbnr.

      eapply red1_eq_context_upto_l in r1 as [t' [r1' e1']]; cycle -1.
      1:{ eapply eq_context_upto_cat.
          2: apply eq_context_fix_context.
          3: exact e.
          all: tea.
          reflexivity. }
      all: eauto; tc.
      2: now eapply eq_term_upto_univ_napp_wf_term; tea.

      eexists {| dbody := t' |}; rdest; cbn; trea.
      1,3,4: congruence.

      eapply eq_term_upto_univ_trans; tea; tc.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply cofix_red_body. eassumption.
    + constructor.
      eapply red_context_rel_eq_mfixpoint; tea.
      apply red_context_rel_fix_context; tea.
      eapply OnOne2_All2; tea; auto; intros d d' [[H _] [= eq eq' eq'']]. rewrite -eq -eq'. split; reflexivity.

  - depelim e. depelim o.
    assert (∑ args,
        OnOne2 (red1 Σ Γ) (array_value a') args *
        All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) value args
    ) as (value' & r' & e').
    { eapply OnOne2_All2_forallb_exists; tea. cbn.
      intros ??? IH ??. apply IH; tea; cbnr. }
    eexists. split.
    + eapply array_red_val. eassumption.
    + constructor. constructor. all: eauto.
  - depelim e. depelim o.
    edestruct IHh as [v' []]; revgoals; tea; tc.
    eexists; split.
    + now eapply array_red_def.
    + do 2 constructor; eauto.
  - depelim e. depelim o. eapply IHh in e0 as [v' []]; tea; tc.
    eexists; split.
    + now eapply array_red_type.
    + do 2 constructor; eauto.
Qed.

Lemma red1_eq_context_upto_r {cf : checker_flags} {Σ} {wfΣ : wf Σ} {cmp_universe cmp_sort pb Γ Δ u v} :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  wf_term_ctx Δ ->
  wf_term u ->
  red1 Σ Γ u v ->
  eq_context_upto Σ cmp_universe cmp_sort pb Δ Γ ->
  ∑ v', red1 Σ Δ u v' *
        eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv v' v.
Proof.
  intros.
  destruct (@red1_eq_context_upto_l _ Σ _ (fun pb => flip (cmp_universe pb)) (fun pb => flip (cmp_sort pb)) pb Γ Δ u v) as (v' & r & e); tas.
  - eapply eq_context_upto_wf_term; tea.
  - eapply eq_context_upto_flip; [..|eassumption]; tc; tas.
  - exists v'; split; tas.
    eapply eq_term_upto_univ_napp_flip; [..|eassumption]; cbn; tc.
Qed.

Lemma red1_eq_term_upto_univ_r {cf : checker_flags} {Σ} {wfΣ : wf Σ} {cmp_universe cmp_sort pb napp Γ u v u'} :
  RelationClasses.PreOrder (cmp_universe Conv) ->
  RelationClasses.PreOrder (cmp_universe pb) ->
  RelationClasses.PreOrder (cmp_sort Conv) ->
  RelationClasses.PreOrder (cmp_sort pb) ->
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_universe Conv) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_sort Conv) ->
  SubstUnivPreserving (cmp_universe Conv) (cmp_sort pb) ->
  wf_term_ctx Γ ->
  wf_term u' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u' u ->
  red1 Σ Γ u v ->
  ∑ v', red1 Σ Γ u' v' ×
        eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp v' v.
Proof.
  intros.
  assert (wf_term u). by eapply eq_term_upto_univ_napp_wf_term; tea.
  destruct (@red1_eq_term_upto_univ_l _ Σ _ (fun pb => flip (cmp_universe pb)) (fun pb => flip (cmp_sort pb)) pb napp Γ u v u') as (v' & r & e).
  all: eauto using RelationClasses.flip_PreOrder.
  1,2: intros ??; unfold flip; cbn; eauto.
  1-3: now apply flip_SubstUnivPreserving.
  - eapply eq_term_upto_univ_napp_flip; [..|eassumption]. all: tc.
  - exists v'. split; tas.
    eapply eq_term_upto_univ_napp_flip; [..|eassumption]; cbn; tc.
Qed.

Section RedEq.
  Context {cf : checker_flags} (Σ : global_env_ext) {wfΣ : wf Σ}.
  Context {cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop} {cmp_sort : conv_pb -> sort -> sort -> Prop} {pb : conv_pb}
          {preorder_univ_conv : RelationClasses.PreOrder (cmp_universe Conv)}
          {preorder_univ_pb   : RelationClasses.PreOrder (cmp_universe pb)}
          {preorder_sort_conv : RelationClasses.PreOrder (cmp_sort Conv)}
          {preorder_sort_pb   : RelationClasses.PreOrder (cmp_sort pb)}
          {sub_univ           : RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb)}
          {sub_sort           : RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb)}
          {hsubst_univ        : SubstUnivPreserving (cmp_universe Conv) (cmp_universe Conv)}
          {hsubst_sort_conv   : SubstUnivPreserving (cmp_universe Conv) (cmp_sort Conv)}
          {hsubst_sort_pb     : SubstUnivPreserving (cmp_universe Conv) (cmp_sort pb)}.

  Lemma red_eq_term_upto_univ_l {Γ u v u'} :
    wf_term_ctx Γ ->
    wf_term u ->
    eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb u u' ->
    red Σ Γ u v ->
    ∑ v',
    red Σ Γ u' v' * eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb v v'.
  Proof using wfΣ preorder_univ_conv preorder_univ_pb preorder_sort_conv preorder_sort_conv preorder_sort_pb sub_univ sub_sort hsubst_univ hsubst_sort_conv hsubst_sort_pb.
    intros wfΓ wfu eq r.
    induction r in wfu, u', eq |- *.
    - eapply red1_eq_term_upto_univ_l in eq as [v' [r' eq']]; eauto.
    - exists u'. split; auto.
    - edestruct IHr1 as (T' & r' & eq'); tea.
      edestruct IHr2 as (T'' & r'' & eq''); tea.
      { eapply red_wf_term; tea. }
      exists T''. split=>//.
      now transitivity T'.
  Qed.

  Lemma red_eq_term_upto_univ_r {Γ u v u'} :
    wf_term_ctx Γ ->
    wf_term u' ->
    eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb u' u ->
    red Σ Γ u v ->
    ∑ v', red Σ Γ u' v' * eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb v' v.
  Proof using wfΣ preorder_univ_conv preorder_univ_pb preorder_sort_conv preorder_sort_conv preorder_sort_pb sub_univ sub_sort hsubst_univ hsubst_sort_conv hsubst_sort_pb.
    intros wfΓ wfu eq r.
    induction r in wfu, u', eq |- *.
    - eapply red1_eq_term_upto_univ_r in eq as [v' [r' eq']]; eauto.
    - exists u'. split; auto.
    - edestruct IHr1 as (T' & r' & eq'); tea.
      edestruct IHr2 as (T'' & r'' & eq''); cycle 1; tea.
      2:{ eapply red_wf_term; tea. }
      exists T''. split=>//.
      now transitivity T'.
  Qed.
End RedEq.

Section RedEqContext.
  Context {cf : checker_flags} (Σ : global_env_ext) {wfΣ : wf Σ}.
  Context {cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop} {cmp_sort : conv_pb -> sort -> sort -> Prop} {pb : conv_pb}
          {preorder_univ_conv : RelationClasses.PreOrder (cmp_universe Conv)}
          {preorder_univ_pb   : RelationClasses.PreOrder (cmp_universe pb)}
          {preorder_sort_conv : RelationClasses.PreOrder (cmp_sort Conv)}
          {preorder_sort_pb   : RelationClasses.PreOrder (cmp_sort pb)}
          {sub_univ           : RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb)}
          {sub_sort           : RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb)}
          {hsubst_univ        : SubstUnivPreserving (cmp_universe Conv) (cmp_universe Conv)}
          {hsubst_sort_conv   : SubstUnivPreserving (cmp_universe Conv) (cmp_sort Conv)}
          {hsubst_sort_pb     : SubstUnivPreserving (cmp_universe Conv) (cmp_sort pb)}.

  Lemma red_eq_context_upto_l {Γ Δ} {u} {v} :
    wf_term_ctx Γ ->
    wf_term u ->
    eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
    red Σ Γ u v ->
    ∑ v',
    red Σ Δ u v' *
    eq_term_upto_univ Σ cmp_universe cmp_sort Δ Conv v v'.
  Proof using wfΣ preorder_univ_conv preorder_univ_pb preorder_sort_conv preorder_sort_conv preorder_sort_pb hsubst_univ hsubst_sort_conv hsubst_sort_pb.
    intros wfΓ wfu eq r.
    induction r in wfu |- *.
    - eapply red1_eq_context_upto_l in r as [v' [r' eq']]; eauto; tc.
      eapply eq_term_upto_univ_eq_ctx in eq'; eauto. all: tc.
    - exists x. split; auto. reflexivity.
    - assert (wf_term y). 1: by eapply red_wf_term; tea.
      assert (wf_term z). 1: by eapply red_wf_term; tea.
      assert (wf_term_ctx Δ). 1: by eapply eq_context_upto_wf_term; tea.
      edestruct IHr1 as (T' & r' & eq'); tea.
      edestruct IHr2 as (T'' & r'' & eq''); tea.
      eapply (red_eq_term_upto_univ_l _ (pb := Conv) (u:=y) (v:=T'') (u':=T')) in r'' as (T''' & r'' & eq'''); tc; tea.
      exists T'''; split.
      + now transitivity T'.
      + eapply eq_term_upto_univ_trans; tc; tea.
  Qed.

  Lemma red_eq_context_upto_r {Γ Δ} {u} {v} :
    wf_term_ctx Δ ->
    wf_term u ->
    eq_context_upto Σ cmp_universe cmp_sort pb Δ Γ ->
    red Σ Γ u v ->
    ∑ v',
    red Σ Δ u v' *
    eq_term_upto_univ Σ cmp_universe cmp_sort Δ Conv v' v.
  Proof using wfΣ preorder_univ_conv preorder_univ_pb preorder_sort_conv preorder_sort_conv preorder_sort_pb hsubst_univ hsubst_sort_conv hsubst_sort_pb.
    intros wfΓ wfu eq r.
    induction r in wfu |- *.
    - eapply red1_eq_context_upto_r in r as [v' [r' eq']]; eauto; tc.
      eapply eq_term_upto_univ_eq_ctx with (pb0 := pb) in eq'; eauto; revgoals.
      1: eapply eq_context_upto_flip with (cmp_universe' := fun pb => flip (cmp_universe pb)) (cmp_sort' := fun pb => flip (cmp_sort pb)); revgoals; tea.
      all: tc.
    - exists x. split; auto. reflexivity.
    - assert (wf_term_ctx Γ). 1: by eapply eq_context_upto_wf_term; tea.
      assert (wf_term y). 1: by eapply red_wf_term; tea.
      assert (wf_term z). 1: by eapply red_wf_term; tea.
      edestruct IHr1 as (T' & r' & eq'); tea.
      assert (wf_term T'). 1: by eapply red_wf_term; tea.
      edestruct IHr2 as (T'' & r'' & eq''); tea.
      eapply (red_eq_term_upto_univ_r _ (pb := Conv) (u:=y) (v:=T'') (u':=T')) in r'' as (T''' & r'' & eq'''); tc; tea.
      exists T'''; split.
      + now transitivity T'.
      + eapply eq_term_upto_univ_trans; tc; tea.
  Qed.
End RedEqContext.


Polymorphic Derive Signature for Relation.clos_refl_trans.

Derive Signature for red1.

Lemma local_env_telescope P Γ Γ' Δ Δ' :
  All2_telescope (on_decls P) Γ Γ' Δ Δ' ->
  on_contexts_over P Γ Γ' (List.rev Δ) (List.rev Δ').
Proof.
  induction 1. simpl. constructor.
  - depelim p. simpl. eapply on_contexts_over_app. repeat constructor => //.
    simpl.
    revert IHX.
    generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
    constructor; auto. depelim p0; constructor; auto;
    now rewrite !app_context_assoc.
  - simpl. eapply on_contexts_over_app. constructor. 2:auto. constructor.
    simpl. depelim p.
    revert IHX.
    generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
    constructor; auto. depelim p1; constructor; auto;
    now rewrite !app_context_assoc.
Qed.

Lemma All_All2_telescopei_gen P (Γ Γ' Δ Δ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    on_contexts_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  on_contexts_over P Γ Γ' Δ Δ' ->
  All2_telescope_n (on_decls P) (fun n : nat => lift0 n)
                   (Γ ,,, Δ) (Γ' ,,, Δ') #|Δ|
    (map (fun def : def term => vass (dname def) (dtype def)) m)
    (map (fun def : def term => vass (dname def) (dtype def)) m').
Proof.
  intros weakP.
  induction 1 in Δ, Δ' |- *; cbn. constructor.
  intros. destruct r. rewrite e. constructor.
  constructor.
  rewrite {2}(All2_fold_length X0).
  now eapply weakP.
  specialize (IHX (vass (dname y) (lift0 #|Δ| (dtype x)) :: Δ)
                  (vass (dname y) (lift0 #|Δ'| (dtype y)) :: Δ')).
  forward IHX.
  constructor; auto. constructor. now eapply weakP. simpl in IHX.
  rewrite {2}(All2_fold_length X0).
  apply IHX.
Qed.

Lemma All_All2_telescopei P (Γ Γ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    on_contexts_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_telescope_n (on_decls P) (fun n => lift0 n)
                   Γ Γ' 0
                   (map (fun def => vass (dname def) (dtype def)) m)
                   (map (fun def => vass (dname def) (dtype def)) m').
Proof.
  specialize (All_All2_telescopei_gen P Γ Γ' [] [] m m'). simpl.
  intros. specialize (X X0 X1). apply X; constructor.
Qed.

Lemma All2_All2_fold_fix_context P (Γ Γ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    on_contexts_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_fold (on_decls (on_decls_over P Γ Γ')) (fix_context m) (fix_context m').
Proof.
  intros Hweak a. unfold fix_context.
  eapply local_env_telescope.
  cbn.
  rewrite - !(mapi_mapi
                (fun n def => vass (dname def) (dtype def))
                (fun n decl => lift_decl n 0 decl)).
  eapply All2_telescope_mapi.
  rewrite !mapi_cst_map.
  eapply All_All2_telescopei; eauto.
Qed.

Lemma OnOne2_pars_pred1_ctx_over {cf : checker_flags} {Σ} {wfΣ : wf Σ} Γ params params' puinst pctx :
  wf_term_ctx Γ ->
  forallb wf_term params ->
  closedn_ctx #|params| pctx ->
  OnOne2 (pred1 Σ Γ Γ) params params' ->
  pred1_ctx_over Σ Γ Γ (inst_case_context params puinst pctx) (inst_case_context params' puinst pctx).
Proof.
  intros onΓ onpars onpctx redp.
  eapply OnOne2_All2 in redp.
  eapply pred1_ctx_over_inst_case_context; tea.
  all:pcuic.
Qed.

Lemma pred_on_free_vars {cf : checker_flags} {Σ} {wfΣ : wf Σ} {P Γ Δ t u} :
  on_ctx_free_vars P Γ ->
  clos_refl_trans (pred1 Σ Γ Δ) t u ->
  on_free_vars P t -> on_free_vars P u.
Proof.
  intros onΓ.
  induction 1; eauto with fvs. intros o.
  eapply pred1_on_free_vars; tea.
Qed.

Lemma pred_wf_term {cf : checker_flags} {Σ} {wfΣ : wf Σ} {Γ Δ t u} :
  wf_term_ctx Γ ->
  clos_refl_trans (pred1 Σ Γ Δ) t u ->
  wf_term t -> wf_term u.
Proof.
  intros onΓ.
  induction 1; eauto with fvs. intros o.
  eapply pred1_wf_term; tea.
Qed.

#[global] Hint Resolve red1_on_free_vars red_on_free_vars red1_wf_term red_wf_term : fvs.
#[global] Hint Resolve pred1_on_free_vars pred1_on_ctx_free_vars pred1_wf_term pred1_wf_term_ctx : fvs.
#[global] Hint Extern 4 => progress (unfold PCUICCases.inst_case_predicate_context) : fvs.
#[global] Hint Extern 4 => progress (unfold PCUICCases.inst_case_branch_context) : fvs.
#[global] Hint Extern 3 (is_true (on_ctx_free_vars xpredT _)) =>
  rewrite on_ctx_free_vars_xpredT_snoc : fvs.
#[global] Hint Extern 3 (is_true (on_free_vars_ctx (shiftnP _ xpredT) _)) =>
  rewrite shiftnP_xpredT : fvs.
#[global] Hint Resolve wf_term_ctx_app_inst_case_context : fvs.
#[global] Hint Resolve wf_term_app_fix_context : fvs.
#[global] Hint Extern 3 (is_true (on_free_vars (shiftnP _ xpredT) _)) => rewrite shiftnP_xpredT : fvs.

Section RedPred.
  Context {cf : checker_flags}.
  Context {Σ : global_env}.
  Context (wfΣ : wf Σ).

  Hint Resolve pred1_ctx_over_refl : pcuic.
  Hint Unfold All2_prop2_eq : pcuic.
  Hint Transparent context : pcuic.
  Hint Transparent mfixpoint : pcuic.

  Hint Mode pred1 ! ! ! ! - : pcuic.

  Ltac pcuic := simpl; try typeclasses eauto with pcuic.

  (** Strong substitutivity gives context conversion of reduction!
      It cannot be strenghtened to deal with let-ins: pred1 is
      precisely not closed by arbitrary reductions in contexts with let-ins.
   *)

  (* Unused, should be changed to use closedn *)
  Lemma pred1_ctx_pred1 P Γ Γ' Δ Δ' t u :
    #|Γ| = #|Γ'| ->
    on_free_vars (closedP #|Γ ,,, Δ| P) t ->
    on_ctx_free_vars (closedP #|Γ ,,, Δ| P) (Γ ,,, Δ) ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ) t u ->
    assumption_context Δ ->
    pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ') ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') t u.
  Proof using wfΣ.
    intros Hlen ont onctx X H X0.
    epose proof (fst strong_substitutivity _ _ _ _ X _ _ (Γ ,,, Δ) (Γ' ,,, Δ') ids ids ont).
    forward X1. now rewrite subst_ids.
    rewrite !subst_ids in X1.
    apply X1.
    red. split => //. split => //.
    intros x px. rewrite {1}/ids /=. split => //.
    split => //. eapply pred1_refl_gen => //.
    move=> [na [b|] ty] => /= //.
    destruct (leb_spec_Set (S x) #|Δ|).
    rewrite !nth_error_app_lt; try lia.
    intros hnth; rewrite hnth. eexists; split => //.
    apply nth_error_assumption_context in hnth => //.
    rewrite !nth_error_app_ge //; try lia.
    intros hnth.
    pose proof (on_contexts_app_inv _ _ _ _ _ X0) as [predΓ _] => //.
    pose proof (All2_fold_length X0). len in H0.
    eapply nth_error_pred1_ctx_l in predΓ; tea.
    2:erewrite hnth => //.
    destruct predΓ as [body' [hnth' pred]].
    exists body'; split=> //.
    rewrite -lift0_inst /ids /=.
    econstructor => //.
    rewrite nth_error_app_ge. lia.
    now replace #|Δ'| with #|Δ| by lia.
  Qed.

  Lemma pred1_ctx_assumption_context Γ Γ' :
    pred1_ctx Σ Γ Γ' ->
    assumption_context Γ -> assumption_context Γ'.
  Proof using Type.
    induction 1; auto.
    intros h; depelim h. depelim p; constructor; auto.
  Qed.

  Lemma pred1_ctx_over_assumption_context Γ Γ' Δ Δ' :
    pred1_ctx_over Σ Γ Γ' Δ Δ' ->
    assumption_context Δ -> assumption_context Δ'.
  Proof using Type.
    induction 1; auto.
    intros h; depelim h. depelim p; constructor; auto.
  Qed.

  (* Unused, should be changed to use closedn *)
  Lemma pred1_ctx_pred1_inv P Γ Γ' Δ Δ' t u :
    #|Γ| = #|Γ'| ->
    on_free_vars (closedP #|Γ ,,, Δ| P) t ->
    on_ctx_free_vars (closedP #|Γ ,,, Δ| P) (Γ ,,, Δ) ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') t u ->
    assumption_context Δ ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ) t u.
  Proof using wfΣ.
    intros Hlen ont onctx X H.
    assert(pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ)).
    { apply pred1_pred1_ctx in X.
      apply on_contexts_app_inv in X as [] => //.
      apply All2_fold_app => //. now eapply pred1_ctx_over_refl_gen. }
    assert(lenΔ : #|Δ| = #|Δ'|).
    { eapply pred1_pred1_ctx in X. eapply All2_fold_length in X.
      rewrite !app_context_length in X. lia. }
    epose proof (fst strong_substitutivity _ _ _ _ X _ _ (Γ ,,, Δ) (Γ' ,,, Δ) ids ids ont).
    forward X1. now rewrite subst_ids.
    rewrite !subst_ids in X1.
    apply X1; red; split => //; split => //.
    intros x px. rewrite {1}/ids /=. split => //.
    split => //. eapply pred1_refl_gen => //.
    move=> [na [b|] ty] => /= //.
    destruct (leb_spec_Set (S x) #|Δ|).
    rewrite !nth_error_app_lt; try lia.
    intros hnth.
    apply nth_error_assumption_context in hnth => //.
    rewrite !nth_error_app_ge //; try lia.
    intros hnth.
    pose proof (on_contexts_app_inv _ _ _ _ _ X0) as [predΓ _] => //.
    pose proof (All2_fold_length X0). len in H0.
    eapply nth_error_pred1_ctx_l in predΓ; tea.
    2:erewrite hnth => //.
    destruct predΓ as [body' [hnth' pred]].
    replace #|Δ'| with #|Δ| by lia.
    exists body'; split=> //.
    rewrite -lift0_inst /ids /=.
    econstructor => //.
    rewrite nth_error_app_ge //. lia.
  Qed.

  Ltac noconf H := repeat (DepElim.noconf H; simpl NoConfusion in * ).

  Hint Extern 1 (eq_binder_annot _ _) => reflexivity : pcuic.
  Hint Resolve pred1_refl_gen : pcuic.
  Hint Extern 4 (All_decls _ _ _) => constructor : pcuic.
  Hint Extern 4 (All2_fold _ _ _) => constructor : pcuic.

  Lemma OnOne2_local_env_pred1_ctx_over Γ Δ Δ' :
     OnOne2_local_env (fun Δ => on_one_decl (fun M N => pred1 Σ (Γ ,,, Δ) (Γ ,,, Δ) M N)) Δ Δ' ->
     pred1_ctx_over Σ Γ Γ Δ Δ'.
  Proof using Type.
    induction 1.
    1-2:constructor; destruct p; subst; intuition eauto.
    - eapply pred1_pred1_ctx in p. pcuic.
    - now constructor.
    - eapply pred1_pred1_ctx in a0. pcuic.
    - eapply pred1_pred1_ctx in a. pcuic.
    - constructor; simpl; subst; intuition auto.
      eapply pred1_refl.
    - constructor; simpl; subst; intuition auto.
      eapply pred1_refl.
    - eapply (All2_fold_app (Γ' := [d]) (Γr := [_])); pcuic.
      destruct d as [na [b|] ty]; constructor; pcuic.
      constructor; simpl; subst; auto; intuition pcuic.
      eapply pred1_refl_gen. eapply All2_fold_app; pcuic. apply IHX.
      eapply pred1_refl_gen. eapply All2_fold_app; pcuic. apply IHX.
      simpl; subst; intuition pcuic.
      constructor.
      eapply pred1_refl_gen. eapply All2_fold_app; pcuic. apply IHX.
  Qed.

  Lemma prod_ind {A B} : A -> (A -> B) -> A × B.
  Proof using Type.
    intuition.
  Qed.

  Lemma red1_pred1 Γ M N :
    wf_term_ctx Γ ->
    wf_term M ->
    red1 Σ Γ M N -> pred1 Σ Γ Γ M N.
  Proof using wfΣ.
    intros onΓ onM r.
    induction r using red1_ind_all; intros.
    all:repeat inv_wf_term.
    all:try solve [econstructor; pcuic;
      (eapply All_All2_refl, All_refl || eapply OnOne2_All2 || idtac); eauto 7 using pred1_refl, pred1_ctx_over_refl with fvs ].

    - eapply OnOne2_prod_inv in X as [_ X].
      eapply OnOne2_apply in X => //.
      eapply OnOne2_apply_forallb in X => //.
      assert (pred1_ctx_over Σ Γ Γ (inst_case_predicate_context p)
        (inst_case_predicate_context (set_pparams p params'))).
        by eapply OnOne2_pars_pred1_ctx_over => //.
      econstructor; pcuic; eauto with fvs.
      + eapply OnOne2_All2; pcuic.
      + eapply pred1_refl_gen. eapply All2_fold_app => //; pcuic.
      + eapply All_All2_refl; solve_all; inv_wf_term.
        1: eapply OnOne2_pars_pred1_ctx_over => //; eauto with fvs; solve_all.
        eapply pred1_refl_gen. eapply All2_fold_app => //; pcuic.
        eapply OnOne2_pars_pred1_ctx_over => //; eauto with fvs; solve_all.

    - econstructor; pcuic.
      unfold inst_case_branch_context in *.
      eapply OnOne2_All_mix_left in X. 2: now apply forallb_All in b.
      eapply OnOne2_All2; tea. 2: by pcuic.
      simpl. intros x y [[[? IH] e]]; unfold on_Trel; inv_wf_term.
      rewrite -!e. repeat split; auto.
      + apply pred1_ctx_over_refl.
      + apply IH; tas.
        eauto with fvs.

    - constructor; pcuic.
      eapply OnOne2_prod_inv in X as [_ X].
      eapply OnOne2_apply in X => //.
      eapply OnOne2_apply_forallb in X => //.
      eapply OnOne2_All2; eauto. pcuic.

    - eapply OnOne2_prod_assoc in X as [_ X].
      apply OnOne2_apply_left in X; tea.
      eapply OnOne2_All_mix_left in X. 2: now apply forallb_All in onM.
      assert (pred1_ctx_over Σ Γ Γ (fix_context mfix0) (fix_context mfix1)).
      { eapply pred1_fix_context; tea. pcuic.
        eapply OnOne2_All2; pcuic.
        simpl. intros d d' [[IH e] wfd]; inv_wf_term.
        noconf e. split => //.
        now apply IH. }
      constructor; pcuic.
      eapply OnOne2_All2; unfold on_Trel; pcuic; simpl.
      + intros d d' [[IH e] wfd]; inv_wf_term.
        injection e as [= <- <- <-].
        split; auto.
        split; auto.
        eapply pred1_refl_gen => //.
        eapply All2_fold_app; pcuic. apply X0.
      + intro; repeat split; auto.
        all: eapply pred1_refl_gen; pcuic.
        eapply All2_fold_app; pcuic. apply X0.

    - assert (fix_context mfix0 = fix_context mfix1).
      { eapply OnOne2_eq_fixcontext. apply X. }
      assert (pred1_ctx_over Σ Γ Γ (fix_context mfix0) (fix_context mfix0)).
        by apply pred1_ctx_over_refl.
      constructor; pcuic; rewrite -H //.
      eapply OnOne2_prod_assoc in X as [_ X].
      eapply OnOne2_All_mix_left in X; tea. 2: now eapply forallb_All.
      eapply OnOne2_All2; unfold on_Trel; pcuic; simpl.
      intros d d' [[IH e] wfd]; inv_wf_term.
      injection e as [= <- <- <-].
      split; pcuic.
      split; auto.
      apply IH; tas.
      eauto with fvs.

    - eapply OnOne2_prod_assoc in X as [_ X].
      apply OnOne2_apply_left in X; tea.
      eapply OnOne2_All_mix_left in X. 2: now apply forallb_All in onM.
      assert (pred1_ctx_over Σ Γ Γ (fix_context mfix0) (fix_context mfix1)).
      { eapply pred1_fix_context; tea. pcuic.
        eapply OnOne2_All2; pcuic.
        simpl. intros d d' [[IH e] wfd]; inv_wf_term.
        noconf e. split => //.
        now apply IH. }
      constructor; pcuic.
      eapply OnOne2_All2; unfold on_Trel; pcuic; simpl.
      + intros d d' [[IH e] wfd]; inv_wf_term.
        injection e as [= <- <- <-].
        split; auto.
        split; auto.
        eapply pred1_refl_gen => //.
        eapply All2_fold_app; pcuic. apply X0.
      + intro; repeat split; auto.
        all: eapply pred1_refl_gen; pcuic.
        eapply All2_fold_app; pcuic. apply X0.

    - assert (fix_context mfix0 = fix_context mfix1).
      { eapply OnOne2_eq_fixcontext. apply X. }
      assert (pred1_ctx_over Σ Γ Γ (fix_context mfix0) (fix_context mfix0)).
        by apply pred1_ctx_over_refl.
      constructor; pcuic; rewrite -H //.
      eapply OnOne2_prod_assoc in X as [_ X].
      eapply OnOne2_All_mix_left in X; tea. 2: now eapply forallb_All.
      eapply OnOne2_All2; unfold on_Trel; pcuic; simpl.
      intros d d' [[IH e] wfd]; inv_wf_term.
      injection e as [= <- <- <-].
      split; pcuic.
      split; auto.
      apply IH; tas.
      eauto with fvs.

    - constructor; pcuic. constructor; cbn; pcuic.
      apply OnOne2_prod_inv in X as [_ X].
      apply OnOne2_apply, OnOne2_apply_forallb in X; tea.
      eapply OnOne2_All2; pcuic.

    - constructor; pcuic. constructor; cbn; pcuic.
    - constructor; pcuic. constructor; cbn; pcuic.
  Qed.

  Lemma red_pred Γ M N :
    wf_term_ctx Γ ->
    wf_term M ->
    red Σ Γ M N -> clos_refl_trans (pred1 Σ Γ Γ) M N.
  Proof.
    intros wfΓ wfM.
    induction 1 in wfM |- *.
    - constructor. now apply red1_pred1.
    - reflexivity.
    - eapply red_wf_term in wfM as wfN; eauto.
      transitivity y; auto.
  Qed.

  Lemma red1_ctx_pred1_ctx Γ Γ' :
    wf_term_ctx Γ ->
    red1_ctx Σ Γ Γ' ->
    pred1_ctx Σ Γ Γ'.
  Proof using wfΣ.
    intros wfΓ h.
    induction h in wfΓ |- *; cbn in wfΓ; inv_wf_term.
    1-2: depelim p; subst na'.
    - constructor; pcuic.
      constructor.
      now apply red1_pred1.
    - constructor; pcuic.
      destruct s as [[s <-]|[s <-]];
      constructor; pcuic.
      all: now apply red1_pred1.
    - constructor; auto.
      eapply All_decls_refl. intros x; apply pred1_refl_gen; eauto.
  Qed.

End RedPred.

Lemma on_contexts_apply_wf_term P Γ Γ' :
  All2_fold (fun Γ Γ' => All_decls (fun M N => wf_term_ctx Γ -> wf_term M -> P Γ Γ' M N)) Γ Γ' ->
  wf_term_ctx Γ ->
  on_contexts P Γ Γ'.
Proof.
  induction 1; cbn; intros; try by constructor.
  move/andP: H => [H] /andP [] hb ht.
  constructor; auto.
  destruct p; constructor; auto.
Qed.

Lemma on_contexts_apply_wf_term' P Γ0 Γ Γ' :
  All2_fold (fun Γ Γ' => All_decls (fun M N => wf_term_ctx (Γ0 ,,, Γ) -> wf_term M -> P Γ Γ' M N)) Γ Γ' ->
  wf_term_ctx (Γ0 ,,, Γ) ->
  on_contexts P Γ Γ'.
Proof.
  induction 1; cbn; intros; try by constructor.
  move/andP: H => [H] /andP [] hb ht.
  constructor; auto.
  destruct p; constructor; auto.
Qed.

Section PredRed.
  Context {cf : checker_flags}.
  Context {Σ : global_env}.
  Context (wfΣ : wf Σ).

  (** Parallel reduction is included in the reflexive transitive closure of 1-step reduction *)
  Lemma pred1_red Γ Γ' M N :
    wf_term_ctx Γ ->
    wf_term M ->
    pred1 Σ Γ Γ' M N ->
    red Σ Γ M N.
  Proof using cf Σ wfΣ.
    intros wfΓ wfM h.
    revert Γ Γ' M N h wfΓ wfM.
    eapply (@pred1_ind_all_ctx Σ
      (fun Γ Γ' M N => wf_term_ctx Γ -> wf_term M -> red Σ Γ M N)
      (fun Γ Γ' => wf_term_ctx Γ -> All2_fold (on_decls (fun Γ Γ' M N => red Σ Γ M N)) Γ Γ')%type
      (fun Γ Γ' Δ Δ' => wf_term_ctx (Γ ,,, Δ) -> on_contexts_over (fun Γ Γ' M N => red Σ Γ M N) Γ Γ' Δ Δ')%type);
      intros; try reflexivity; inv_wf_term; try solve [pcuic].

    - (* Contexts *)
      apply on_contexts_apply_wf_term in X0; tas.

    - (* Contexts over *)
      apply on_contexts_apply_wf_term' in X3; tas.

    - (* Beta *)
      intuition auto.
      transitivity (tApp (tLambda na t0 b1) a1).
      + eapply red_app; [apply red_abs|]; eauto with fvs.
      + apply red1_red. constructor.

    - (* Zeta *)
      transitivity (tLetIn na d0 t0 b1).
      1: by eapply red_letin; eauto with fvs.
      transitivity (tLetIn na d1 t1 b1).
      1: by eapply red_letin; eauto with pcuic.
      eapply red1_red; constructor.

    - (* Rel in context *)
      eapply nth_error_pred1_ctx in X0; eauto.
      destruct X0 as [body' [Hnth Hpred]].
      transitivity (lift0 (S i) body').
      eapply red1_red; constructor; auto.
      rewrite -(firstn_skipn (S i) Γ).
      eapply weakening_red_0 => //.
      + rewrite firstn_length_le //.
        destruct (nth_error Γ i) eqn:Heq => //.
        eapply nth_error_Some_length in Heq. lia.
      + rewrite wf_term_ctx_skipn //.
      + eapply nth_error_decl_body_wf_term_ctx; tea.

    - (* Iota *)
      transitivity (tCase ci (set_pparams p0 pparams1) (mkApps (tConstruct ci.(ci_ind) c u) args1) brs1).
      2: eapply red1_red; now constructor.
      etransitivity.
      { eapply red_case_c. eapply red_mkApps. 1: auto. solve_all. }
      etransitivity.
      { eapply red_case_brs. red. change (is_true ?p) with (is_true (false || p)) in a. solve_all;
        unfold on_Trel in *; intuition auto; repeat inv_wf_term.
        eauto with fvs. }
      { eapply red_case_pars. solve_all. }

    - transitivity (mkApps (tFix mfix1 idx) args1).
      2: { apply red1_red; econstructor; tea.
        eapply is_constructor_pred1; tea.
        solve_all.
      }
      have ? : wf_term_ctx (Γ ,,, fix_context mfix0)
        by eauto with fvs.
      eapply red_mkApps.
      2: now solve_all.
      eapply red_fix_congr. red in X3. unfold on_Trel in *.
      solve_all; inv_wf_term; auto.

    - transitivity (tCase ci p1 (mkApps (tCoFix mfix1 idx) args1) brs1).
      2: apply red1_red; now econstructor.
      destruct p1; unfold on_Trel in *; cbn in *.
      subst puinst pcontext.
      eapply red_case; eauto.
      * solve_all.
      * eauto with fvs.
      * eapply red_mkApps; [|now solve_all].
        have ? : wf_term_ctx (Γ ,,, fix_context mfix0)
          by eauto with fvs.
        eapply red_cofix_congr. red in X3. unfold on_Trel in *.
        solve_all; inv_wf_term; auto.
      * red. change (is_true ?p) with (is_true (false || p)) in a.
        solve_all.
        eauto with fvs.

    - transitivity (tProj p (mkApps (tCoFix mfix1 idx) args1)).
      2: eapply red1_red; now econstructor.
      eapply red_proj_c; eauto.
      eapply red_mkApps; [|now solve_all].
      have ? : wf_term_ctx (Γ ,,, fix_context mfix0)
        by eauto with fvs.
      eapply red_cofix_congr. red in X3. unfold on_Trel in *.
      solve_all; inv_wf_term; auto.

    - transitivity (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args1)).
      2: eapply red1_red; now constructor.
      eapply red_proj_c.
      eapply red_mkApps; [|now solve_all].
      reflexivity.

    - eapply PCUICSubstitution.red_abs_alt; eauto with fvs.
    - now eapply red_app.
    - now eapply PCUICSubstitution.red_letin_alt => //; eauto with fvs.
    - unfold on_Trel in *; destruct p1; cbn in *. subst puinst pcontext.
      eapply red_case => //.
      * solve_all.
      * eapply X4; eauto with fvs.
      * eauto.
      * red. change (is_true ?p) with (is_true (false || p)) in a.
        solve_all.
        eauto with fvs.

    - now eapply red_proj_c.
    - eapply red_fix_congr.
      have ? : wf_term_ctx (Γ ,,, fix_context mfix0)
        by eauto with fvs.
      red in X3. unfold on_Trel in *.
      solve_all; inv_wf_term; auto.
    - eapply red_cofix_congr.
      have ? : wf_term_ctx (Γ ,,, fix_context mfix0)
        by eauto with fvs.
      red in X3. unfold on_Trel in *.
      solve_all; inv_wf_term; auto.
    - eapply red_prod; eauto with fvs.
    - eapply red_evar; eauto with fvs. solve_all.
    - depelim X1; try solve [repeat constructor]; eauto.
      depelim X2; cbn in H0; rtoProp.
      eapply red_primArray_congr; eauto.
      + now eapply Universe.make'_inj in e.
      + solve_all.
  Qed.

  Lemma pred1_ctx_red_context Γ Γ' :
    wf_term_ctx Γ ->
    pred1_ctx Σ Γ Γ' ->
    red_context Σ Γ Γ'.
  Proof using wfΣ.
    intros wfΓ h.
    induction h in wfΓ |- *; cbn in wfΓ; inv_wf_term.
    1: now constructor.
    constructor. 1: apply IHh; assumption.
    destruct p; inv_wf_term.
    - constructor.
      now eapply pred1_red.
    - constructor.
      all: now eapply pred1_red.
  Qed.

  (* Unused, should be changed to use closedn *)
  Lemma pred1_red_r_gen P Γ Γ' Δ Δ' : forall M N,
    on_free_vars (closedP #|Γ ,,, Δ| P) M ->
    on_ctx_free_vars (closedP #|Γ ,,, Δ| P) (Γ' ,,, Δ) ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') M N ->
    #|Γ| = #|Γ'| ->
    pred1_ctx Σ (Γ' ,,, Δ) (Γ' ,,, Δ') ->
    pred1 Σ (Γ' ,,, Δ) (Γ' ,,, Δ') M N.
  Proof using wfΣ.
    intros M N onM onctx pred hlen predctx.
    epose proof (fst strong_substitutivity _ _ _ _ pred _ _ (Γ' ,,, Δ) (Γ' ,,, Δ') ids ids onM).
    forward X. now rewrite subst_ids.
    rewrite !subst_ids in X.
    apply X.
    red. split => //. split => //.
    intros x px. rewrite {1}/ids /=. split => //.
    split => //. eapply pred1_refl_gen => //.
    assert (#|Δ| = #|Δ'|).
    { apply pred1_pred1_ctx in pred. eapply All2_fold_length in pred. len in pred. }
    move=> [na [b|] ty] => /= //.
    destruct (leb_spec_Set (S x) #|Δ|).
    - rewrite !nth_error_app_lt; try lia.
      intros hnth.
      destruct (on_contexts_app_inv _ _ _ _ _ predctx) as []. lia.
      eapply nth_error_pred1_ctx_l in a0; tea.
      2:erewrite hnth; rewrite /= //.
      destruct a0 as [body' [heq hpred]]. exists body'; split => //.
      rewrite -lift0_inst /ids.
      econstructor; eauto.
      rewrite nth_error_app_lt //; try lia.
    - rewrite !nth_error_app_ge //; try lia.
      intros hnth.
      pose proof (on_contexts_app_inv _ _ _ _ _ (pred1_pred1_ctx _ pred)) as [predΓ _] => //.
      eapply nth_error_pred1_ctx_l in predΓ; tea.
      2:erewrite hnth => //.
      destruct predΓ as [body' [hnth' pred']].
      rewrite -H.
      exists body'; split=> //.
      rewrite -lift0_inst /ids /=.
      econstructor => //.
      rewrite nth_error_app_ge. lia.
      now replace #|Δ'| with #|Δ| by lia.
  Qed.

  (* Unused, should be changed to use closedn *)
  Lemma pred1_red_r_gen' P Γ Γ' Δ Δ' : forall M N,
    on_free_vars (shiftnP #|Γ ,,, Δ| P) M ->
    on_free_vars_ctx P (Γ' ,,, Δ) ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') M N ->
    #|Γ| = #|Γ'| ->
    pred1_ctx Σ (Γ' ,,, Δ) (Γ' ,,, Δ') ->
    pred1 Σ (Γ' ,,, Δ) (Γ' ,,, Δ') M N.
  Proof using wfΣ.
    intros M N onM onctx pred hlen predctx.
    epose proof (fst strong_substitutivity _ _ _ _ pred _ _ (Γ' ,,, Δ) (Γ' ,,, Δ') ids ids onM).
    forward X. now rewrite subst_ids.
    rewrite !subst_ids in X.
    apply X.
    pose proof (All2_fold_length predctx). len in H.
    red. split => //. split => //.
    relativize #|Γ ,,, Δ|; [erewrite on_free_vars_ctx_on_ctx_free_vars|] => //; len.
    intros x px. rewrite {1}/ids /=. split => //.
    split => //. eapply pred1_refl_gen => //.
    assert (#|Δ| = #|Δ'|).
    { apply pred1_pred1_ctx in pred. eapply All2_fold_length in pred. len in pred. }
    move=> [na [b|] ty] => /= //.
    destruct (leb_spec_Set (S x) #|Δ|).
    - rewrite !nth_error_app_lt; try lia.
      intros hnth.
      destruct (on_contexts_app_inv _ _ _ _ _ predctx) as []. lia.
      eapply nth_error_pred1_ctx_l in a0; tea.
      2:erewrite hnth; rewrite /= //.
      destruct a0 as [body' [heq hpred]]. exists body'; split => //.
      rewrite -lift0_inst /ids.
      econstructor; eauto.
      rewrite nth_error_app_lt //; try lia.
    - rewrite !nth_error_app_ge //; try lia.
      intros hnth.
      pose proof (on_contexts_app_inv _ _ _ _ _ (pred1_pred1_ctx _ pred)) as [predΓ _] => //.
      eapply nth_error_pred1_ctx_l in predΓ; tea.
      2:erewrite hnth => //.
      destruct predΓ as [body' [hnth' pred']].
      rewrite -H0.
      exists body'; split=> //.
      rewrite -lift0_inst /ids /=.
      econstructor => //.
      rewrite nth_error_app_ge. lia.
      now replace #|Δ'| with #|Δ| by lia.
  Qed.

  (* Unused, should be changed to use closedn *)
  Lemma pred1_pred1_r P Γ Γ' : forall M N, pred1 Σ Γ Γ' M N ->
    on_ctx_free_vars (closedP #|Γ| P) Γ' ->
    on_free_vars (closedP #|Γ| P) M ->
    pred1 Σ Γ' Γ' M N.
  Proof using wfΣ.
    intros M N pred onctx onM.
    apply (pred1_red_r_gen P _ _ [] [] M N onM onctx pred).
    eapply pred1_pred1_ctx in pred. apply (length_of pred).
    simpl. eapply pred1_ctx_refl.
  Qed.

  (* Unused, should be changed to use closedn *)
  Lemma pred1_pred1_r' P Γ Γ' : forall M N, pred1 Σ Γ Γ' M N ->
    on_free_vars_ctx P Γ' ->
    on_free_vars (shiftnP #|Γ| P) M ->
    pred1 Σ Γ' Γ' M N.
  Proof using wfΣ.
    intros M N pred onctx onM.
    apply (pred1_red_r_gen' P _ _ [] [] M N onM onctx pred).
    eapply pred1_pred1_ctx in pred. apply (length_of pred).
    simpl. eapply pred1_ctx_refl.
  Qed.

  (* Unused, should be changed to use closedn *)
  Lemma pred1_red_r {P Γ Γ' M N} :
    pred1 Σ Γ Γ' M N ->
    on_free_vars_ctx P Γ' ->
    on_free_vars (shiftnP #|Γ| P) M ->
    red Σ Γ' M N.
  Proof using wfΣ.
    intros p onctx onM.
    pose proof (pred1_pred1_ctx _ p). eapply All2_fold_length in X.
    eapply pred1_pred1_r' in p; tea.
    eapply pred1_red in p; tea.
    rewrite wf_term_ctx_on_free_vars_ctx.
    eapply on_free_vars_ctx_impl; tea => //.
    rewrite wf_term_on_free_vars.
    eapply on_free_vars_impl; tea => //.
  Qed.

End PredRed.

#[global] Hint Resolve on_free_vars_ctx_any_xpredT on_free_vars_ctx_wf_term_ctx : fvs.

#[global] Hint Extern 4 (is_true (on_ctx_free_vars xpredT _)) =>
  rewrite on_ctx_free_vars_xpredT : fvs.

#[global] Hint Resolve on_free_vars_any_xpredT on_free_vars_wf_term : fvs.

Generalizable Variables A B R S.

Section AbstractConfluence.
  Section Definitions.

    Context {A : Type}.
    Definition joinable (R : A -> A -> Type) (x y : A) := ∑ z, R x z * R y z.
    Definition diamond (R : A -> A -> Type) := forall x y z, R x y -> R x z -> joinable R y z.
    Definition confluent (R : relation A) := diamond (clos_refl_trans R).

  End Definitions.

  Global Instance joinable_proper A :
    Proper (relation_equivalence ==> relation_equivalence)%signatureT (@joinable A).
  Proof.
    reduce_goal. split; unfold joinable; intros.
    destruct X0. exists x1. intuition eauto. setoid_rewrite (X x0 x1) in a. auto.
    specialize (X y0 x1). now apply X in b.
    red in X.
    destruct X0 as [z [rl rr]].
    apply X in rl. apply X in rr.
    exists z; split; auto.
  Qed.

  Global Instance diamond_proper A : Proper (relation_equivalence ==> iffT)%signatureT (@diamond A).
  Proof.
    reduce_goal.
    rewrite /diamond.
    split; intros.
    setoid_rewrite <- (X x0 y0) in X1.
    setoid_rewrite <- (X x0 z) in X2.
    specialize (X0 _ _ _ X1 X2).
    pose (joinable_proper _ _ _ X).
    now apply r in X0.
    setoid_rewrite (X x0 y0) in X1.
    setoid_rewrite (X x0 z) in X2.
    specialize (X0 _ _ _ X1 X2).
    pose (joinable_proper _ _ _ X).
    now apply r in X0.
  Qed.

  Lemma clos_rt_proper A : Proper (relation_equivalence ==> relation_equivalence) (@clos_refl_trans A).
  Proof.
    reduce_goal. split; intros.
    induction X0; try apply X in r; try solve [econstructor; eauto].
    induction X0; try apply X in r; try solve [econstructor; eauto].
  Qed.

  Global Instance confluent_proper A : Proper (relation_equivalence ==> iffT)%signatureT (@confluent A).
  Proof.
    reduce_goal.
    split; rewrite /confluent; auto.
    pose proof (diamond_proper A). apply X0. apply clos_rt_proper.
    now symmetry.
    pose proof (diamond_proper A). apply X0. apply clos_rt_proper.
    now symmetry.
  Qed.

  Lemma sandwich {A} (R S : A -> A -> Type) :
    inclusion R S -> inclusion S (clos_refl_trans R) ->
    (iffT (confluent S) (confluent R)).
  Proof.
    intros inclR inclS.
    apply clos_rt_monotone in inclR.
    apply clos_rt_monotone in inclS.
    assert (inclusion (clos_refl_trans S) (clos_refl_trans R)).
    etransitivity; eauto.
    apply clos_rt_idempotent.
    rewrite /confluent.
    apply diamond_proper.
    now apply relation_equivalence_inclusion.
  Qed.

  Section Diamond.
    Context {A} {R S : relation A}.
    Context (sc : diamond R).

    Lemma diamond_t1n_t_confluent t u v :
      trans_clos_1n R t u ->
      R t v ->
      ∑ t', trans_clos_1n R u t' * trans_clos_1n R v t'.
    Proof using sc.
      move => tu.
      revert v.
      induction tu.
      intros.
      - destruct (sc _ _ _ r X); auto.
        eexists; split; constructor; intuition eauto.
      - move => v xv.
        destruct (sc _ _ _ r xv); auto.
        destruct p. specialize (IHtu _ r0).
        destruct IHtu as [nf [redl redr]].
        exists nf. split; auto.
        econstructor 2; eauto.
    Qed.

    Lemma diamond_t1n_t1n_confluent {t u v} :
      trans_clos_1n R t u ->
      trans_clos_1n R t v ->
      ∑ t', trans_clos_1n R u t' * trans_clos_1n R v t'.
    Proof using sc.
      move => tu tv.
      induction tv in u, tu |- *.
      - eapply diamond_t1n_t_confluent; eauto.
      - eapply diamond_t1n_t_confluent in r; eauto.
        destruct r as [nf [redl redr]].
        specialize (IHtv _ redr) as [nf' [redl' redr']].
        exists nf'; intuition auto.
        apply trans_clos_t1n_iff.
        econstructor 2; eapply trans_clos_t1n_iff; eauto.
    Qed.

    Lemma diamond_t_t_confluent {t u v} :
      trans_clos R t u ->
      trans_clos R t v ->
      ∑ t', trans_clos R u t' * trans_clos R v t'.
    Proof using sc.
      move => tu tv.
      apply trans_clos_t1n_iff in tu;
        apply trans_clos_t1n_iff in tv.
      destruct (diamond_t1n_t1n_confluent tu tv).
      exists x. split; apply trans_clos_t1n_iff; intuition auto.
    Qed.

    Lemma commutes_diamonds_diamond :
      commutes R S -> diamond S -> diamond (relation_disjunction R S).
    Proof using sc.
      intros HRS HS x y z xy xz.
      destruct xy, xz.
      destruct (sc _ _ _ r r0).
      eexists; intuition auto. now left. now left.
      destruct (HRS _ _ _ r s).
      exists x0.
      intuition auto. right; auto. left; auto.
      destruct (HRS _ _ _ r s).
      eexists; intuition auto. left; eauto. right; auto.
      destruct (HS _ _ _ s s0). intuition auto.
      eexists. split; right; eauto.
    Qed.

    Lemma commutes_disj_joinable :
      commutes R S -> confluent R -> confluent S ->
      forall x y z, relation_disjunction R S x y ->
                    relation_disjunction R S x z ->
                    joinable (clos_refl_trans (relation_disjunction R S)) y z.
    Proof using Type.
      intros.
      destruct X2. destruct X3.
      destruct (X0 _ _ _ (rt_step r) (rt_step r0)).
      exists x0; intuition auto. now eapply clos_rt_disjunction_left.
      now apply clos_rt_disjunction_left.
      destruct (X _ _ _ r s).
      exists x0.
      intuition auto. now eapply clos_rt_disjunction_right, rt_step.
      now apply clos_rt_disjunction_left, rt_step.
      destruct X3.
      destruct (X _ _ _ r s).
      exists x0.
      intuition auto. now eapply clos_rt_disjunction_left, rt_step.
      now apply clos_rt_disjunction_right, rt_step.
      destruct (X1 _ _ _ (rt_step s) (rt_step s0)).
      exists x0; intuition auto. now eapply clos_rt_disjunction_right.
      now apply clos_rt_disjunction_right.
    Qed.

  End Diamond.

  Theorem diamond_confluent `{Hrefl : Reflexive A R} : diamond R -> confluent R.
  Proof.
    move=> Hdia x y z H H'.
    apply clos_rt_t_incl in H.
    apply clos_rt_t_incl in H'.
    pose proof (clos_t_rt_equiv (R:=R)).
    apply (joinable_proper _ _ _ X).
    apply (diamond_t_t_confluent Hdia H H').
  Qed.

  Corollary confluent_union {A} {R S : relation A} :
    Reflexive R ->
    commutes R S -> diamond R -> diamond S -> confluent (relation_disjunction R S).
  Proof.
    intros HRR HRS Hcom HR HS. apply diamond_confluent.
    now apply commutes_diamonds_diamond.
  Qed.

End AbstractConfluence.

Unset Universe Minimization ToSet.

Section RedConfluence.
  Context {cf : checker_flags}.
  Context {Σ : global_env} (wfΣ : wf Σ).

  Let wf_term' := ∑ t, wf_term t.
  Let wf_term_ctx' := ∑ Γ, wf_term_ctx Γ.

  Let wf_pair := wf_term_ctx' × wf_term'.

  Definition wf_pair_pred1 (Γt Δu : wf_pair) := pred1 Σ Γt.1.π1 Δu.1.π1 Γt.2.π1 Δu.2.π1.
  Hint Unfold wf_pair_pred1 : core.

  #[local] Instance wf_pair_pred1_refl : Reflexive wf_pair_pred1.
  Proof.
    intros [[Γ] [t]].
    apply pred1_refl.
  Qed.

  Lemma diamond_wf_pair_pred1 : diamond wf_pair_pred1.
  Proof using wfΣ.
    intros [[Γ] [t]] [[Δ] [u]] [[Ξ] [v]] tu tv.
    eapply pred1_diamond in tu as res; tea. simpl in res.
    destruct res as (vz & uz).
    unfold wf_pair_pred1.
    unshelve eexists ((_; _), (_; _)); repeat split; simpl; revgoals; tea.
    all: eauto with pcuic fvs.
  Qed.

  Lemma confluent_wf_pair_pred1 : confluent wf_pair_pred1.
  Proof using wfΣ.
    eapply diamond_confluent. apply diamond_wf_pair_pred1.
  Qed.

  Definition wf_pair_red1 (Γt Δu : wf_pair) : Type :=
      (Γt.1.π1 = Δu.1.π1 × red1 Σ Γt.1.π1 Γt.2.π1 Δu.2.π1) +
      (red1_ctx Σ Γt.1.π1 Δu.1.π1 × Γt.2.π1 = Δu.2.π1).

  Definition wf_pair_red (Γt Δu : wf_pair) : Type :=
    (red_context Σ Γt.1.π1 Δu.1.π1 × red Σ Γt.1.π1 Γt.2.π1 Δu.2.π1).


  Lemma wf_pred1_wf_red Γt Δu : wf_pair_pred1 Γt Δu -> wf_pair_red Γt Δu.
  Proof using wfΣ.
    intros * Hred.
    split.
    - eapply pred1_ctx_red_context; tas.
      { apply Γt.1.π2. }
      eapply pred1_pred1_ctx, Hred.
    - eapply pred1_red, Hred; tas.
      { apply Γt.1.π2. }
      { apply Γt.2.π2. }
  Qed.

  Lemma wf_pair_red_clos_trans (Γt Δu : wf_pair) :
    wf_pair_red Γt Δu -> clos_refl_trans wf_pair_red1 Γt Δu.
  Proof using wfΣ.
    unfold wf_pair_red, wf_pair_red1.
    cbn; intro h.
    move: Γt Δu h => [[Γ hΓ] [t ht]] [[Δ hΔ] [u hu]] /= h.
    destruct h as (hΓΔ & htu).
    econstructor 3 with ((Γ; hΓ), (u; hu)).
    - induction htu in ht, hu |- *.
      + constructor; simpl.
        auto.
      + have <- : ht = hu by apply uip.
        reflexivity.
      + etransitivity; unshelve eauto; cbn.
        eauto with fvs.
    - apply red_ctx_red_context in hΓΔ; tas.
      clear htu.
      induction hΓΔ in hΓ, hΔ |- *.
      + constructor; simpl.
        auto.
      + have <- : hΓ = hΔ by apply uip.
        reflexivity.
      + etransitivity; unshelve eauto.
        apply red_ctx_red_context in hΓΔ1; tea.
        cbn. eapply wf_term_red_context; revgoals; tea.
  Qed.

  Lemma clos_trans_wf_pair_red Γt Δu :
    clos_refl_trans wf_pair_red1 Γt Δu ->
    wf_pair_red Γt Δu.
  Proof using wfΣ.
    intros H.
    eapply clos_rt_rt1n_iff in H.
    induction H as [Γt|[Γ t] [Δ u] [Ξ v] X ? [ihrctx ihr]]; cbn in *.
    - split => //. apply red_context_refl.
    - destruct X as [[e X]|[X e]]; cbn in *.
      + split => //=. 1: now rewrite e //.
        transitivity u.π1; auto.
        now rewrite e.
      + have X' : red_context Σ Γ.π1 Δ.π1.
        { apply red_ctx_red_context; tas.
          { apply Γ.π2. }
          now constructor. }
        split; cbn.
        * eapply red_context_trans; tea.
          apply Γ.π2.
        * rewrite e.
          eapply red_red_ctx; tea.
          { apply Γ.π2. }
          { apply u.π2. }
  Qed.

  Lemma pred_rel_confluent : confluent wf_pair_red1.
  Proof using wfΣ.
    notypeclasses refine (fst (sandwich _ _ _ _) _).
    3:eapply confluent_wf_pair_pred1; eauto.
    - intros [[Γ] [t]] [[Δ] [u]] h.
      unfold wf_pair_red1, wf_pair_pred1 in *. simpl in *.
      destruct h as [[<- h] | [h <-]].
      + now eapply red1_pred1.
      + eapply pred1_refl_gen.
        now eapply red1_ctx_pred1_ctx in h.
    - intros Γt Δt h.
      apply wf_pair_red_clos_trans.
      now apply wf_pred1_wf_red.
  Qed.

  Definition wf_red1 Γ (t u : wf_term') : Type :=
    red1 Σ Γ t.π1 u.π1.

  Lemma wf_red_wf_pair_red Γ t u :
    clos_refl_trans (wf_red1 Γ.π1) t u ->
    wf_pair_red (Γ, t) (Γ, u).
  Proof using Type.
    intro h.
    split. 1: now apply red_context_refl.
    induction h; try now econstructor.
    etransitivity; tea.
  Qed.

  Lemma red_wf_red Γ t u :
    wf_term_ctx Γ ->
    red Σ Γ t.π1 u.π1 ->
    clos_refl_trans (wf_red1 Γ) t u.
  Proof using wfΣ.
    intro wfΓ.
    destruct t as (t & ht), u as (u & hu). cbn.
    induction 1 in ht, hu |- *.
    - constructor. apply r.
    - have <- : ht = hu by apply uip.
      reflexivity.
    - etransitivity; unshelve eauto.
      cbn. eauto with fvs.
  Qed.

  Lemma wf_red1_confluent Γ :
    wf_term_ctx Γ ->
    confluent (wf_red1 Γ).
  Proof using wfΣ.
    intros wfΓ x y z xy xz.
    set Γ' : wf_term_ctx' := (Γ; wfΓ).
    pose proof (pred_rel_confluent (Γ', x) (Γ', y) (Γ', z)).
    forward X by now eapply wf_pair_red_clos_trans, wf_red_wf_pair_red.
    forward X by now eapply wf_pair_red_clos_trans, wf_red_wf_pair_red.
    destruct X as [[Δ w] [redl redr]].
    eapply clos_trans_wf_pair_red in redl as (_ & redl).
    eapply clos_trans_wf_pair_red in redr as (_ & redr). simpl in *.
    eexists; split; tas.
    all: apply red_wf_red; tea.
  Qed.

  Lemma wf_red_red Γ t u :
    clos_refl_trans (wf_red1 Γ) t u ->
    red Σ Γ t.π1 u.π1.
  Proof using Type.
    induction 1; try now econstructor.
    etransitivity; eauto.
  Qed.

  Lemma red1_confluent Γ t u v :
    wf_term_ctx Γ ->
    wf_term t ->
    red Σ Γ t u ->
    red Σ Γ t v ->
    ∑ w, red Σ Γ u w × red Σ Γ v w.
  Proof using wfΣ.
    intros wfΓ wft redl redr.
    unshelve epose proof (wf_red1_confluent Γ _ (t; _) (u; _) (v; _) _ _) as (w & redl' & redr'); cbn; tas.
    1,2: now eauto with fvs.
    1,2: now apply red_wf_red.
    eapply wf_red_red in redl', redr'.
    eexists; split; tea.
  Qed.
End RedConfluence.


Section RedInversion.
  Context {cf : checker_flags}.
  Context {Σ : global_env} (wfΣ : wf Σ).
  Context (Γ : context) (wfΓ : wf_term_ctx Γ).

  Lemma red_mkApps_tConstruct ind pars k args c :
    forallb wf_term args ->
    red Σ Γ (mkApps (tConstruct ind pars k) args) c ->
    ∑ args',
    c = mkApps (tConstruct ind pars k) args' × All2 (red Σ Γ) args args'.
  Proof using wfΣ wfΓ.
    intros wfargs redc.
    apply red_pred in redc; tas.
    2: { rewrite wf_term_mkApps //=. }
    depind redc.
    - eapply pred1_mkApps_tConstruct in r as [r' [-> redargs]].
      eexists; split; auto. solve_all. eapply pred1_red; eauto with fvs.
    - exists args; split; eauto. apply All2_same; auto.
    - specialize (IHredc1 wfargs) as [args' [-> redargs]].
      assert (forallb wf_term args').
      { solve_all. eauto with fvs. }
      edestruct IHredc2 as [args'' [-> redargs']]; cbnr; tas.
      eexists; split => //.
      eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
  Qed.

  Lemma red_mkApps_tInd ind u args c :
    forallb wf_term args ->
    red Σ Γ (mkApps (tInd ind u) args) c ->
    ∑ args',
      c = mkApps (tInd ind u) args' × All2 (red Σ Γ) args args'.
  Proof using wfΣ wfΓ.
    intros wfargs redc.
    apply red_pred in redc; tas.
    2: { rewrite wf_term_mkApps //=. }
    depind redc.
    - eapply pred1_mkApps_tInd in r as [r' [-> redargs]].
      eexists; split; auto. solve_all. eapply pred1_red; eauto with fvs.
    - exists args; split; eauto. apply All2_same; auto.
    - specialize (IHredc1 wfargs) as [args' [-> redargs]].
      assert (forallb wf_term args').
      { solve_all. eauto with fvs. }
      edestruct IHredc2 as [args'' [-> redargs']]; cbnr; tas.
      eexists; split => //.
      eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
  Qed.

  Lemma red_mkApps_tRel k b args c :
    forallb wf_term args ->
    nth_error Γ k = Some b -> decl_body b = None ->
    red Σ Γ (mkApps (tRel k) args) c ->
    ∑ args',
      c = mkApps (tRel k) args' × All2 (red Σ Γ) args args'.
  Proof using wfΣ wfΓ.
    intros wfargs hnth hbod redc.
    apply red_pred in redc; tas.
    2: { rewrite wf_term_mkApps //=. }
    depind redc.
    - eapply pred1_mkApps_tRel in r as [r' [-> redargs]]; tea.
      eexists; split; auto. solve_all. eapply pred1_red; eauto with fvs.
    - exists args; split; eauto. apply All2_same; auto.
    - edestruct IHredc1 as [args' [e redargs]]; cbnr; tea; subst.
      assert (forallb wf_term args').
      { solve_all. eauto with fvs. }
      edestruct IHredc2 as [args'' [-> redargs']]; cbnr; tea.
      eexists; split => //.
      eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
  Qed.

  Lemma red_mkApps_tConst_axiom cst u args cb c :
    forallb wf_term args ->
    declared_constant Σ cst cb -> cst_body cb = None ->
    red Σ Γ (mkApps (tConst cst u) args) c ->
    ∑ args',
      c = mkApps (tConst cst u) args' × All2 (red Σ Γ) args args'.
  Proof using wfΣ wfΓ.
    intros wfargs hdecl hbod redc.
    apply red_pred in redc; tas.
    2: { rewrite wf_term_mkApps //=. }
    depind redc.
    - eapply pred1_mkApps_tConst_axiom in r as [r' [-> redargs]]; tea.
      eexists; split; auto. solve_all. eapply pred1_red; eauto with fvs.
    - exists args; split; eauto. apply All2_same; auto.
    - edestruct IHredc1 as [args' [e redargs]]; cbnr; tea; subst.
      assert (forallb wf_term args').
      { solve_all. eauto with fvs. }
      edestruct IHredc2 as [args'' [-> redargs']]; cbnr; tea.
      eexists; split => //.
      eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
  Qed.
End RedInversion.

(** The red/pred relations are only well-behaved on the subset of properly scoped terms,
    we hence develop a higher-level interface on those. *)

(** A well-scoped term is a term with a proof that its free variables obey the predicate P *)
(** Note, it would be nicer to use SProp here to get more definitional equalities... *)
Definition ws_term P := { t : term | on_free_vars P t }.

Definition ws_term_proj {P} (t : ws_term P) : term := proj1_sig t.
Coercion ws_term_proj : ws_term >-> term.

Definition ws_term_prop {P} (t : ws_term P) : on_free_vars P t := proj2_sig t.
Coercion ws_term_prop : ws_term >-> is_true.
#[global] Hint Resolve ws_term_prop : fvs.

(** The subset of closed terms: no free-variables allowed *)
Notation closed_term := (ws_term xpred0).

Lemma ws_term_xpredT {P} {t : ws_term P} : on_free_vars xpredT t.
Proof.
  destruct t as [t ont].
  eapply on_free_vars_impl; tea => //.
Qed.

Lemma ws_term_wf_term {P} {t : ws_term P} : wf_term t.
Proof.
  destruct t as [t ont].
  rewrite wf_term_on_free_vars.
  eapply on_free_vars_impl; tea => //.
Qed.

#[global] Hint Resolve ws_term_xpredT ws_term_wf_term : fvs.

(** A well-scoped context is a context obeying a free-variables predicate.
    Note ths use of `on_free_vars_ctx` rather than `on_ctx_free_vars:
    we want a uniformly true predicate on the variables in the context. *)
Definition ws_context P := { t : context | on_free_vars_ctx P t }.

(* The subsect of closed contexts. *)
Notation closed_context := (ws_context xpred0).
Notation open_term Γ := (ws_term (shiftnP #|Γ| xpred0)).

Definition ws_context_proj {P} (t : ws_context P) : context := proj1_sig t.
Coercion ws_context_proj : ws_context >-> context.

Definition ws_context_proj' {P} (t : ws_context P) : list context_decl := proj1_sig t.
Coercion ws_context_proj' : ws_context >-> list.

Definition ws_context_on_free_vars {P} (t : ws_context P) : on_free_vars_ctx P t := proj2_sig t.
(* Coercion ws_context_on_free_vars : ws_context >-> is_true. *)
#[global] Hint Resolve ws_context_on_free_vars : fvs.

Lemma ws_context_xpredT {P} {Γ : ws_context P} : on_ctx_free_vars xpredT (Γ).
Proof.
  destruct Γ as [Γ onΓ].
  rewrite on_ctx_free_vars_xpredT.
  eapply on_free_vars_ctx_impl; tea => //.
Qed.

Lemma ws_context_wf_term_ctx {P} {Γ : ws_context P} : wf_term_ctx (Γ).
Proof.
  destruct Γ as [Γ onΓ].
  rewrite wf_term_ctx_on_free_vars_ctx.
  eapply on_free_vars_ctx_impl; tea => //.
Qed.

#[global] Hint Resolve ws_context_xpredT ws_context_wf_term_ctx : fvs.

Lemma ws_context_on_free_vars_xpredT {P} {Γ : ws_context P} : on_free_vars_ctx xpredT Γ.
Proof.
  destruct Γ as [Γ onΓ].
  eapply on_free_vars_ctx_impl; tea => //.
Qed.
#[global] Hint Resolve ws_context_on_free_vars_xpredT : fvs.

Definition ws_red1 Σ P (Γ : ws_context P) (t u : ws_term (shiftnP #|Γ| P)) :=
  red1 Σ Γ t u.

Definition ws_red Σ P (Γ : ws_context P) := clos_refl_trans (ws_red1 Σ P Γ).

Definition ws_pair :=
  ∑ Γ : ws_context xpred0, ws_term (shiftnP #|Γ| xpred0).

Definition ws_pair_context (t : ws_pair) : closed_context := t.π1.
Definition ws_pair_term (t : ws_pair) : ws_term (shiftnP #|ws_pair_context t| xpred0) := t.π2.
Coercion ws_pair_context : ws_pair >-> closed_context.
Coercion ws_pair_term : ws_pair >-> ws_term.

Definition ws_pred1_curry Σ P (Γ Γ' : ws_context P) (t u : ws_term (shiftnP #|Γ| P)) :=
  pred1 Σ Γ Γ' t u.

Definition ws_pred1 Σ (t u : ws_pair) := pred1 Σ t.π1 u.π1 t.π2 u.π2.

Definition ws_pred_curry Σ P (Γ Γ' : ws_context P) := clos_refl_trans (ws_pred1_curry Σ P Γ Γ').

Definition ws_pred Σ := clos_refl_trans (ws_pred1 Σ).

Lemma ws_red1_pred1_curry {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {P} {Γ : ws_context P}
  {t u : ws_term (shiftnP #|Γ| P)} :
  ws_red1 Σ P Γ t u -> ws_pred1_curry Σ P Γ Γ t u.
Proof.
  eapply red1_pred1; eauto with fvs.
Qed.

Lemma ws_red1_pred1 {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {Γ : closed_context}
  {t u : ws_term (shiftnP #|Γ| xpred0)} :
  ws_red1 Σ _ Γ t u -> ws_pred1 Σ (Γ; t) (Γ; u).
Proof.
  eapply red1_pred1; eauto with fvs.
Qed.

Lemma red_pred' {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {P} {Γ : ws_context P}
  {t u : ws_term (shiftnP #|Γ| P)} :
  ws_red Σ P Γ t u -> ws_pred_curry Σ P Γ Γ t u.
Proof.
  eapply clos_rt_monotone => x y H.
  eapply red1_pred1; eauto with fvs.
Qed.

Lemma ws_pred_ws_pred_curry {Σ} {Γ : closed_context} {t : ws_term (shiftnP #|Γ| xpred0)} {u : ws_term (shiftnP #|Γ| xpred0)} :
  ws_pred_curry Σ xpred0 Γ Γ t u -> ws_pred Σ (Γ; t) (Γ; u).
Proof.
  induction 1. constructor 1. apply r.
  constructor 2.
  econstructor 3; tea.
Qed.

Lemma ws_red_ws_pred {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {Γ : closed_context}
  {t u : ws_term (shiftnP #|Γ| xpred0)} :
  ws_red Σ _ Γ t u -> ws_pred Σ (Γ; t) (Γ; u).
Proof.
  intros r. now eapply ws_pred_ws_pred_curry, red_pred'.
Qed.

Lemma ws_pred1_red {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {P} {Γ Γ' : ws_context P}
  {t : ws_term (shiftnP #|Γ| P)} {u : ws_term (shiftnP #|Γ'| P)} :
  pred1 Σ Γ Γ' t u -> red Σ Γ t u.
Proof.
  intros p; eapply pred1_red; tea => //; eauto with fvs.
Qed.

#[program]
Definition rho_ws_pair {cf:checker_flags} (Σ : global_env) {wfΣ : wf Σ} (p : ws_pair) : ws_pair :=
  (rho_ctx Σ p; rho Σ (rho_ctx Σ p) p).
Next Obligation.
  destruct p as [Γ t]. cbn.
  pose proof (@triangle cf Σ wfΣ Γ Γ (tRel 0) (tRel 0)).
  forward X. eauto with fvs.
  forward X. trivial.
  forward X. apply pred1_refl.
  eapply pred1_pred1_ctx in X.
  eapply pred1_on_free_vars_ctx; tea. eauto with fvs.
Qed.
Next Obligation.
  destruct p as [Γ t]. cbn.
  pose proof (@triangle _ Σ wfΣ Γ Γ t t).
  forward X. eauto with fvs.
  forward X. eauto with fvs.
  rewrite fold_context_length.
  eapply pred1_on_free_vars; tea. eapply X. pcuic.
  all:eauto with fvs.
Qed.

Lemma ws_pred1_diamond {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ} {t u v : ws_pair} :
  ws_pred1 Σ t u -> ws_pred1 Σ t v ->
  ws_pred1 Σ u (rho_ws_pair Σ t) × ws_pred1 Σ v (rho_ws_pair Σ t).
Proof.
  intros p q.
  apply pred1_diamond; eauto with fvs.
Qed.

#[global] Hint Resolve pred1_on_free_vars_ctx : fvs.

Lemma pred1_on_free_vars_on_free_vars_ctx {cf:checker_flags} {Σ : global_env} {wfΣ : wf Σ}
  {P} {Γ Γ' : context} {t u : term} :
    pred1 Σ Γ Γ' t u ->
    on_free_vars_ctx P Γ ->
    on_free_vars (shiftnP #|Γ| P) t -> on_free_vars (shiftnP #|Γ| P) u.
Proof.
  intros pr.
  rewrite -on_free_vars_ctx_on_ctx_free_vars.
  intros onΓ.
  eapply pred1_on_free_vars; tea.
Qed.

Section RedConfluence.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext} (wfΣ : wf Σ).

  Instance pred1_refl Γ : Reflexive (pred1 Σ Γ Γ).
  Proof using Type. red; apply pred1_refl. Qed.

  Definition pred1_rel : ws_pair -> ws_pair -> Type :=
    fun t u => pred1 Σ t.π1 u.π1 t.π2 u.π2.

  Instance pred1_rel_refl : Reflexive pred1_rel.
  Proof using Type. red. intros [ctx x]. red. simpl. apply pred1_refl. Qed.

  Lemma red1_weak_confluence P {Γ : ws_context P} {t u v : ws_term (shiftnP #|Γ| P)} :
    red1 Σ Γ t u -> red1 Σ Γ t v ->
    ∑ t', red Σ Γ u t' * red Σ Γ v t'.
  Proof using wfΣ.
    move/ws_red1_pred1_curry => tu.
    move/ws_red1_pred1_curry => tv.
    eapply pred1_diamond in tu; eauto with fvs.
    destruct tu as [redl redr].
    eapply pred1_red in redl; eauto with fvs.
    eapply pred1_red in redr; eauto with fvs.
  Qed.

  Lemma diamond_pred1_rel : diamond pred1_rel.
  Proof using wfΣ.
    move=> t u v tu tv.
    exists (rho_ws_pair Σ t). apply (ws_pred1_diamond tu tv).
  Qed.

  Lemma pred1_rel_confluent : confluent pred1_rel.
  Proof using wfΣ.
    eapply diamond_confluent. apply diamond_pred1_rel.
  Qed.

  Lemma red_trans_clos_pred1 (Γ : ws_context xpred0) t u :
    ws_red Σ xpred0 Γ t u ->
    trans_clos pred1_rel (Γ; t) (Γ; u).
  Proof using wfΣ.
    induction 1.
    constructor. now eapply ws_red1_pred1 in r.
    constructor. pcuic.
    econstructor 2; eauto.
  Qed.

  Inductive clos_refl_trans_ctx_decl (R : relation context_decl) (x : context_decl) : context_decl -> Type :=
    rt_ctx_decl_step : forall y, R x y -> clos_refl_trans_ctx_decl R x y
  | rt_ctx_decl_refl y : eq_binder_annot x.(decl_name) y.(decl_name) ->
    decl_body x = decl_body y -> decl_type x = decl_type y -> clos_refl_trans_ctx_decl R x y
  | rt_ctx_decl_trans : forall y z, clos_refl_trans_ctx_decl R x y -> clos_refl_trans_ctx_decl R y z ->
                               clos_refl_trans_ctx_decl R x z.

  Inductive clos_refl_trans_ctx (R : relation context) (x : context) : context -> Type :=
  | rt_ctx_step : forall y, R x y -> clos_refl_trans_ctx R x y
  | rt_ctx_refl y : eq_context_upto_names x y -> clos_refl_trans_ctx R x y
  | rt_ctx_trans : forall y z, clos_refl_trans_ctx R x y -> clos_refl_trans_ctx R y z -> clos_refl_trans_ctx R x z.

  Global Instance clos_refl_trans_ctx_refl R :
    Reflexive (clos_refl_trans_ctx R).
  Proof using Type. intros HR. constructor 2. reflexivity. Qed.

  Global Instance clos_refl_trans_ctx_trans R : Transitive (clos_refl_trans_ctx R).
  Proof using Type.
    intros x y z; econstructor 3; eauto.
  Qed.

  Definition red1_rel : relation ws_pair :=
    relation_disjunction (A:=ws_pair) (fun '(Γ; t) '(Δ; u) => (red1 Σ Γ t u * (Γ = Δ)))%type
                         (fun '(Γ; t) '(Δ; u) => (red1_ctx Σ Γ Δ * (t = u :> term)))%type.

  Definition lift_ws (R : context -> context -> Type) : ws_context xpred0 -> ws_context xpred0 -> Type :=
    fun Γ Γ' => R Γ Γ'.

  Definition ws_red1_ctx := (lift_ws (OnOne2_local_env (fun Γ => on_one_decl (red1 Σ Γ)))).
  Definition ws_red_ctx := lift_ws (red_context Σ).
  Definition ws_pred1_ctx := (lift_ws (on_contexts (pred1 Σ))).

  Lemma ws_red1_ctx_ws_pred1_ctx {Γ Γ' : closed_context} : ws_red1_ctx Γ Γ' -> ws_pred1_ctx Γ Γ'.
  Proof using wfΣ.
    rewrite /ws_red1_ctx /ws_pred1_ctx /lift_ws /=.
    apply red1_ctx_pred1_ctx; eauto with fvs.
  Qed.

  Lemma ws_pred1_ctx_ws_red_ctx {Γ Γ' : closed_context} : ws_pred1_ctx Γ Γ' -> ws_red_ctx Γ Γ'.
  Proof using wfΣ.
    rewrite /ws_pred1_ctx /ws_red_ctx /lift_ws /=.
    intro X.
    apply pred1_ctx_red_context in X; eauto with fvs.
  Qed.

  Definition red_rel_ctx : ws_pair -> ws_pair -> Type :=
    fun t u =>
    (red Σ t.π1 t.π2 u.π2 * red_context Σ t.π1 u.π1)%type.

  Lemma pred1_red' M N : ws_pred1 Σ M N -> red_rel_ctx M N.
  Proof using wfΣ.
    intros * Hred.
    split. apply pred1_red in Hred; eauto with fvs.
    eapply pred1_pred1_ctx in Hred.
    now eapply ws_pred1_ctx_ws_red_ctx.
  Qed.

  Hint Constructors clos_refl_trans_ctx : pcuic.
  Hint Resolve alpha_eq_reflexive : pcuic.
  Set Firstorder Solver eauto with pcuic core typeclass_instances.

  Lemma clos_rt_OnOne2_local_env_ctx_incl R :
    inclusion (clos_refl_trans (OnOne2_local_env (fun Γ => on_one_decl1 R Γ)))
              (clos_refl_trans_ctx (OnOne2_local_env (fun Γ => on_one_decl1 R Γ))).
  Proof using wfΣ.
    intros x y H.
    induction H; firstorder; try solve[econstructor; eauto].
  Qed.

  Inductive clos_refl_trans_ctx_t (R : relation ws_pair) (x : ws_pair) : ws_pair -> Type :=
  | rt_ctx_t_step : forall y, R x y -> clos_refl_trans_ctx_t R x y
  | rt_ctx_t_refl (y : ws_pair) : eq_context_upto_names x.π1 y.π1 -> x.π2 = y.π2 :> term -> clos_refl_trans_ctx_t R x y
  | rt_ctx_t_trans : forall y z, clos_refl_trans_ctx_t R x y -> clos_refl_trans_ctx_t R y z ->
    clos_refl_trans_ctx_t R x z.

  Global Instance clos_refl_trans_ctx_t_refl R :
    Reflexive (clos_refl_trans_ctx_t R).
  Proof using Type. intros HR. constructor 2. reflexivity. auto. Qed.

  Global Instance clos_refl_trans_ctx_t_trans R : Transitive (clos_refl_trans_ctx_t R).
  Proof using Type.
    intros x y z; econstructor 3; eauto.
  Qed.

  Definition clos_rt_ctx_t_monotone (R S : relation _) :
    inclusion R S -> inclusion (clos_refl_trans_ctx_t R) (clos_refl_trans_ctx_t S).
  Proof using Type.
    move => incls x y.
    induction 1; solve [econstructor; eauto].
  Qed.

  Lemma clos_rt_ctx_t_disjunction_left (R S : relation _) :
    inclusion (clos_refl_trans_ctx_t R)
              (clos_refl_trans_ctx_t (relation_disjunction R S)).
  Proof using Type.
    apply clos_rt_ctx_t_monotone.
    intros x y H; left; exact H.
  Qed.

  Lemma clos_rt_ctx_t_disjunction_right (R S : relation _) :
    inclusion (clos_refl_trans_ctx_t S)
              (clos_refl_trans_ctx_t (relation_disjunction R S)).
  Proof using Type.
    apply clos_rt_ctx_t_monotone.
    intros x y H; right; exact H.
  Qed.

  Lemma clos_refl_trans_ctx_t_prod_l (R : relation context) (S : relation ws_pair) :
    (forall x y, on_free_vars_ctx xpred0 x -> clos_refl_trans_ctx R x y ->
      on_free_vars_ctx xpred0 y) ->
    (forall x y, clos_refl_trans_ctx R x y -> #|x| = #|y|) ->
    (forall (x y : closed_context) (b : ws_term (shiftnP #|x| xpred0)) (b' : ws_term (shiftnP #|y| xpred0)),
       R x y -> b = b' :> term -> S (x; b) (y; b')) ->
    forall (x y : closed_context)  (b : ws_term (shiftnP #|x| xpred0)) (b' : ws_term (shiftnP #|y| xpred0)),
      b = b' :> term ->
      clos_refl_trans_ctx R x y ->
      clos_refl_trans_ctx_t S (x; b) (y; b').
  Proof using Type.
    intros H' Hl H'' [] [] [] []; cbn. intros; subst.
    induction X; subst; try solve [econstructor; eauto].
    have ony:= (H' x y i X1).
    have hlen := (Hl x y X1).
    specialize (IHX1 i ony i1).
    assert (on_free_vars (shiftnP #|y| xpred0) x2).
    now rewrite -hlen.
    specialize (IHX1 H).
    etransitivity. exact IHX1.
    eapply IHX2.
  Qed.

  Lemma clos_refl_trans_ctx_t_prod_r (a : closed_context) (R : relation (ws_term (shiftnP #|a| xpred0))) (S : relation ws_pair) :
    (forall x y, R x y -> S (a; x) (a; y)) ->
    forall x y,
      clos_refl_trans R x y ->
      clos_refl_trans_ctx_t S (a; x) (a; y).
  Proof using Type.
    intros. induction X0; try solve [econstructor; eauto].
    constructor 2. simpl. apply reflexivity. reflexivity.
  Qed.

  Lemma ws_term_eq P t ht ht' : exist t ht = exist t ht' :> ws_term P.
  Proof using Type.
    now destruct (uip ht ht').
  Qed.

  Lemma clos_refl_trans_ctx_on_free_vars P Γ Δ :
    on_free_vars_ctx P Γ ->
    clos_refl_trans_ctx (red1_ctx Σ) Γ Δ ->
    on_free_vars_ctx P Δ.
  Proof using wfΣ.
    intros onp.
    induction 1 in onp |- *.
    - eapply red1_ctx_on_free_vars; tea.
    - now eapply eq_context_upto_names_on_free_vars; eassumption.
    - eauto.
  Qed.

  Lemma clos_refl_trans_ctx_length Γ Δ :
    clos_refl_trans_ctx (red1_ctx Σ) Γ Δ -> #|Γ| = #|Δ|.
  Proof using Type.
    induction 1.
    - now eapply OnOne2_local_env_length in r.
    - now eapply All2_length in a.
    - lia.
  Qed.

  Lemma clos_rt_red1_rel_ctx_rt_ctx_red1_rel : inclusion red_rel_ctx (clos_refl_trans_ctx_t red1_rel).
  Proof using wfΣ.
    move=> [[Γ hΓ] [t ht]] [[Δ hΔ] [u hu]] [redt redctx].
    eapply clos_rt_rt1n_iff in redt. cbn in *.
    induction redt in ht, hu |- *.
    induction redctx in hΓ, hΔ, ht, hu |- *.
    - econstructor 2; simpl; apply reflexivity.
    - pose proof hΔ. rewrite on_free_vars_ctx_snoc in H.
      move/andP: H => [] hΔ' Hd'.
      etransitivity.
      * eapply clos_rt_ctx_t_disjunction_right.
        instantiate (1:= (exist (d' :: Γ') hΔ; exist x hu)).
        eapply (clos_refl_trans_ctx_t_prod_l (red1_ctx Σ)). intros.
        { eapply clos_refl_trans_ctx_on_free_vars; tea. }
        { intros. now eapply clos_refl_trans_ctx_length. }
        { intros. split; eauto. }
        { now cbn. }
        transitivity (Γ ,, d).
        constructor 2. repeat constructor. reflexivity.
        reflexivity.
        apply clos_rt_OnOne2_local_env_ctx_incl.
        apply red_context_red_ctx; tas. constructor; auto.
      * clear p. eapply clos_rt_ctx_t_disjunction_right.
        constructor 2; simpl; reflexivity.
    - unshelve eapply transitivity.
      refine ((exist Γ hΓ; exist y _) : ws_pair). cbn.
      eapply red1_on_free_vars; tea. rewrite on_free_vars_ctx_on_ctx_free_vars //.
      all:cbn.
      * eapply clos_rt_ctx_t_disjunction_left.
        eapply clos_refl_trans_ctx_t_prod_r. intros. split; eauto.
        exact X.
        constructor. apply r.
      * apply IHredt.
  Qed.

  Definition pred1_rel_alpha : ws_pair -> ws_pair -> Type :=
    fun t u => (ws_pred1 Σ t u +
      (eq_context_upto_names t u × t = u :> term))%type.

  Definition red1_rel_alpha : relation ws_pair :=
    relation_disjunction (A:=ws_pair) (fun '(Γ; t) '(Δ; u) => (red1 Σ Γ t u * (Γ = Δ)))%type
     (relation_disjunction (A:=ws_pair)
        (fun '(Γ; t) '(Δ; u) => ((red1_ctx Σ Γ Δ * (t = u :> term))))
        (fun '(Γ; t) '(Δ; u) => ((eq_context_upto_names Γ Δ * (t = u :> term)))))%type.

  Lemma clos_rt_red1_rel_rt_ctx : inclusion (clos_refl_trans red1_rel) (clos_refl_trans_ctx_t red1_rel).
  Proof using Type.
    intros x y H.
    induction H.
    - destruct x, y. constructor. auto.
    - constructor 2; apply reflexivity.
    - econstructor 3; eauto.
  Qed.

  Lemma red1_rel_alpha_pred1_rel_alpha : inclusion red1_rel_alpha pred1_rel_alpha.
  Proof using wfΣ.
    intros [ctx [t ht]] [ctx' [t' ht']].
    rewrite /red1_rel_alpha /pred1_rel_alpha /=.
    intros [[l <-]|[[r eq]|[r eq]]].
    - left; now eapply ws_red1_pred1.
    - left. subst. simpl in eq. subst. eapply pred1_refl_gen. now apply ws_red1_ctx_ws_pred1_ctx.
    - right; split; auto.
  Qed.

  Lemma clos_refl_trans_prod_l_sigma {A B} {P : A -> B -> Prop} (R : relation A) (S : relation (∑ x : A, { y : B | P x y })) :
    (forall x b hb hb', clos_refl_trans S (x; exist b hb) (x; exist b hb')) ->
    (forall x y b, P x b -> clos_refl_trans R x y -> P y b) ->
    (forall x y b hb hb', R x y -> S (x; exist b hb) (y; exist b hb')) ->
    forall (x y : A) b hb hb',
      clos_refl_trans R x y ->
      clos_refl_trans S (x; exist b hb) (y; exist b hb').
  Proof using Type.
    intros. cbn in *.
    induction X1; try solve [econstructor; eauto].
    econstructor 3. unshelve eapply IHX1_1. cbn. now eapply (H x y b).
    eapply IHX1_2.
  Qed.

  Lemma clos_refl_trans_prod_r_sigma {A} {B : A -> Type} a (R :  relation (B a)) (S : relation (∑ x : A, B x)) :
    (forall x y, R x y -> S (a; x) (a; y)) ->
    forall (x y : B a),
      clos_refl_trans R x y ->
      clos_refl_trans S (a; x) (a; y).
  Proof using Type.
    intros. induction X0; try solve [econstructor; eauto].
  Qed.

  Lemma red_ws_red (Γ : closed_context) (x y : ws_term (shiftnP #|Γ| xpred0)) :
    red Σ Γ x y -> ws_red Σ xpred0 Γ x y.
  Proof using wfΣ.
    destruct Γ as [Γ hΓ].
    destruct x as [x hx], y as [y hy].
    cbn. rewrite /ws_red.
    induction 1.
    - constructor. exact r.
    - destruct (uip hx hy).
      constructor 2.
    - cbn in *.
      assert (on_free_vars (shiftnP #|Γ| xpred0) y).
      eapply red_on_free_vars; tea; eauto with fvs.
      econstructor 3. (* Bug if using eauto here, leaving a dangling evar *)
      eapply (IHX1 hx H).
      eauto.
  Qed.

  Lemma clos_refl_trans_red1_ctx_eq_length (Γ Δ : closed_context) :
    clos_refl_trans (fun x y : closed_context =>
      relation_disjunction (red1_ctx Σ) eq_context_upto_names x y) Γ Δ -> #|Γ| = #|Δ|.
  Proof using Type.
    induction 1.
    - destruct r.
      now eapply OnOne2_local_env_length in r.
      now eapply All2_length in a.
    - reflexivity.
    - lia.
  Qed.

  Lemma pred1_rel_alpha_red1_rel_alpha : inclusion pred1_rel_alpha (clos_refl_trans red1_rel_alpha).
  Proof using wfΣ.
    intros x y pred. red in pred.
    destruct pred as [pred|[pctx eq]].
    - eapply pred1_red' in pred; auto.
      destruct pred.
      destruct x as [Γ [x hx]], y as [Δ [y hy]]. simpl in *.
      assert (on_free_vars (shiftnP #|Γ| xpred0) y).
      now rewrite (All2_fold_length r0).
      transitivity ((Γ; exist y H) : ws_pair).
      + eapply clos_rt_disjunction_left.
        eapply clos_refl_trans_prod_r_sigma; tea. intros. split; eauto. exact X.
        now eapply red_ws_red.
      + eapply clos_rt_disjunction_right.
        eapply (clos_refl_trans_prod_l_sigma (P:=fun (Γ : closed_context) t => on_free_vars (shiftnP #|Γ| xpred0) t)
          (relation_disjunction (red1_ctx Σ) eq_context_upto_names)); tea.
        { intros. destruct (uip hb hb'). constructor 2. }
        { intros. eapply clos_refl_trans_red1_ctx_eq_length in X. now rewrite -X. }
        { intros. destruct X; [left|right]; split=> //. }
        clear r.
        destruct Γ as [Γ onΓ], Δ as [Δ onΔ].
        cbn in *. clear H. clear hx hy x y.
        eapply red_context_red_ctx, clos_rt_OnOne2_local_env_ctx_incl in r0; tas.
        induction r0 in onΓ, onΔ |- *.
        * constructor 1. now left.
        * constructor 1. now right.
        * specialize (IHr0_1 onΓ).
          assert (on_free_vars_ctx xpred0 y).
          { eapply clos_refl_trans_ctx_on_free_vars in r0_1; tea. }
          specialize (IHr0_1 H). specialize (IHr0_2 H onΔ).
          etransitivity; tea.
    - constructor. right. right. destruct x, y; cbn in *; auto.
  Qed.

  Lemma pred1_upto_names_gen {P Γ Γ' Δ Δ' t u} :
    on_free_vars_ctx P Γ ->
    on_free_vars (shiftnP #|Γ| P) t ->
    pred1 Σ Γ Δ t u ->
    eq_context_upto_names Γ Γ' ->
    eq_context_upto_names Δ Δ' ->
    pred1_ctx Σ Γ' Δ' ->
    pred1 Σ Γ' Δ' t u.
  Proof using wfΣ.
    intros onΓ ont pr eqctx eqctx' predctx.
    epose proof (fst (@strong_substitutivity _ Σ wfΣ) Γ Δ t u pr (shiftnP #|Γ| P) (shiftnP #|Γ| P) Γ' Δ' ids ids).
    forward X by eauto with fvs.
    forward X. rewrite subst_ids; eauto with fvs.
    rewrite !subst_ids in X. apply X.
    split => //. split => //.
    { rewrite (All2_length eqctx).
      rewrite on_free_vars_ctx_on_ctx_free_vars.
      eapply eq_context_upto_names_on_free_vars in onΓ; tea. }
    eauto with fvs.
    move=> x /= h. split => //. split.
    eapply pred1_refl_gen => //.
    intros decl hnth. destruct decl_body eqn:db => //.
    eapply pred1_pred1_ctx in pr.
    eapply nth_error_pred1_ctx_l in pr.
    2:erewrite hnth; rewrite /= db //.
    destruct pr as [body' [eq pr]].
    exists body'; split => //.
    rewrite -lift0_inst. econstructor; eauto.
    destruct (nth_error Δ x) eqn:hnth' => //.
    eapply All2_nth_error_Some in eqctx' as [d' [hnth'' eqd]]; tea.
    depelim eqd. subst. noconf eq. subst. noconf eq.
    rewrite hnth'' //.
  Qed.

  Lemma pred1_ctx_upto_names {P Γ Γ' Δ} :
    on_free_vars_ctx P Γ ->
    pred1_ctx Σ Γ Δ ->
    eq_context_upto_names Γ Γ' ->
    ∑ Δ', pred1_ctx Σ Γ' Δ' × eq_context_upto_names Δ Δ'.
  Proof using wfΣ.
    intros onfvs pr eqctx.
    induction eqctx in Δ, pr, onfvs |- *; depelim pr.
    - exists []; split; auto; pcuic.
    - move: onfvs; rewrite on_free_vars_ctx_snoc /on_free_vars_decl /test_decl /= => /andP[] /= onΓ ont.
      depelim a.
      * depelim r. cbn in ont. subst.
        destruct (IHeqctx _ onΓ pr) as [Δ' [pred' eq']].
        exists (vass na' t' :: Δ').
        split. constructor. apply pred'. constructor.
        eapply pred1_upto_names_gen; tea. eauto with fvs.
        constructor => //. constructor => //.
      * destruct (IHeqctx _ onΓ pr) as [Δ' [pred' eq']].
        depelim r; subst.
        exists (vdef na' b' t' :: Δ'). cbn in ont.
        move/andP: ont => [] onb onT'.
        split. constructor. apply pred'. constructor.
        eapply pred1_upto_names_gen; tea; eauto with fvs.
        eapply pred1_upto_names_gen; tea; eauto with fvs.
        constructor => //. constructor => //.
  Qed.

  Lemma pred1_upto_names {P Γ Γ' Δ t u} :
    on_free_vars_ctx P Γ ->
    on_free_vars (shiftnP #|Γ| P) t ->
    pred1 Σ Γ Δ t u ->
    eq_context_upto_names Γ Γ' ->
    ∑ Δ', pred1 Σ Γ' Δ' t u × eq_context_upto_names Δ Δ'.
  Proof using wfΣ.
    intros onΓ ont pr eqctx.
    pose proof (pred1_pred1_ctx _ pr).
    destruct (pred1_ctx_upto_names onΓ X eqctx) as [Δ' [pred' eq']].
    exists Δ'; split; auto.
    now eapply pred1_upto_names_gen.
  Qed.

  #[program]
  Definition ws_pair_eq_ctx (t : ws_pair) {Γ'} (H : eq_context_upto_names t Γ') : ws_pair :=
    (Γ'; t.π2).
    Next Obligation.
      eapply eq_context_upto_names_on_free_vars; tea.
      eauto with fvs.
    Qed.
    Next Obligation.
      destruct t as [Γ [t ht]]; cbn. cbn in H.
      now rewrite -(All2_length H).
    Qed.

  Lemma diamond_pred1_rel_alpha : diamond pred1_rel_alpha.
  Proof using wfΣ.
    move=> t u v tu tv.
    destruct tu as [tu|[tu eq]], tv as [tv|[tv eq']].
    - destruct (ws_pred1_diamond tu tv). eexists; split; left; tea.
    - destruct t as [ctxt [t ht]], v as [ctxv [v hv]]; cbn in *. subst v.
      eapply pred1_upto_names in tu as [Δ' [pred eqctx]]; cbn; tea; eauto with fvs.
      cbn in *. exists (ws_pair_eq_ctx u eqctx).
      unfold pred1_rel_alpha; cbn.
      firstorder auto.
    - destruct t as [ctxt [t ht]], u as [ctxu [u hu]]; cbn in *; subst u.
      eapply pred1_upto_names in tv as [Δ' [pred eqctx]]; tea.
      exists (ws_pair_eq_ctx v eqctx). unfold pred1_rel_alpha; cbn.
      firstorder auto. cbn. eauto with fvs.
    - exists t. unfold pred1_rel_alpha; cbn.
      split. right; split; auto. now symmetry.
      right. split; auto. now symmetry.
  Qed.

  Lemma pred1_rel_alpha_confluent : confluent pred1_rel_alpha.
  Proof using wfΣ.
    eapply diamond_confluent. apply diamond_pred1_rel_alpha.
  Qed.

  Lemma red1_rel_alpha_confluent : confluent red1_rel_alpha.
  Proof using wfΣ.
    notypeclasses refine (fst (sandwich _ _ _ _) _).
    3:eapply pred1_rel_alpha_confluent; eauto.
    - apply red1_rel_alpha_pred1_rel_alpha.
    - apply pred1_rel_alpha_red1_rel_alpha.
  Qed.

  Lemma clos_refl_trans_out (Γ : closed_context) (x y : ws_term (shiftnP #|Γ| xpred0)) :
    clos_refl_trans (red1 Σ Γ) x y -> clos_refl_trans red1_rel (Γ; x) (Γ; y).
  Proof using wfΣ.
    destruct x as [x hx], y as [y hy]; cbn.
    induction 1.
    - constructor. red. left. pcuicfo.
    - destruct (uip hx hy).
      constructor 2.
    - econstructor 3.
      unshelve eapply IHX1. cbn.
      eapply red_on_free_vars in X1; tea; eauto with fvs.
      cbn. eapply IHX2.
  Qed.

  Lemma clos_red_rel_out x y :
    clos_refl_trans red1_rel x y ->
    clos_refl_trans pred1_rel x y.
  Proof using wfΣ.
    eapply clos_rt_monotone. clear x y.
    intros [Γ t] [Δ u] hred.
    destruct hred as [[ht eq]|[hctx eq]]. subst.
    red. simpl. now eapply ws_red1_pred1.
    subst. red.
    simpl. destruct t as [t ht], u as [u hu].
    cbn in eq. subst t.
    eapply pred1_refl_gen. now eapply ws_red1_ctx_ws_pred1_ctx.
  Qed.

  Lemma red1_rel_alpha_red1_rel : inclusion (clos_refl_trans red1_rel_alpha) (clos_refl_trans_ctx_t red1_rel).
  Proof using wfΣ.
    intros x y H.
    induction H.
    - destruct x, y.
      destruct r. destruct p; subst.
      constructor. firstorder.
      destruct r. destruct p; subst.
      constructor. firstorder auto.
      destruct p; subst.
      constructor 2. simpl. auto. cbn. auto.
    - constructor 2; reflexivity.
    - econstructor 3; eauto.
  Qed.

  Lemma red1_rel_alpha_red1_rel_inv : inclusion (clos_refl_trans_ctx_t red1_rel) (clos_refl_trans red1_rel_alpha).
  Proof using wfΣ.
    intros x y H.
    induction H.
    - destruct x, y.
      destruct r. destruct p; subst.
      constructor. firstorder.
      destruct p. subst.
      constructor. firstorder auto.
    - destruct x, y. simpl in *.
      subst. constructor. firstorder auto.
    - econstructor 3; eauto.
  Qed.

  Definition transport_on_free_vars {n m : nat} {t} (p : on_free_vars (shiftnP n xpred0) t) (eq : n = m) :
    on_free_vars (shiftnP m xpred0) t.
  Proof. now destruct eq. Defined.

  Definition transport_ws_term {n m : nat} (t : ws_term (shiftnP n xpred0)) (eq : n = m) : ws_term (shiftnP m xpred0) :=
      exist (proj1_sig t) (transport_on_free_vars (proj2_sig t) eq).

  Definition move_ws_term {Γ Δ : closed_context} (t : ws_term (shiftnP #|Γ| xpred0)) (eq : #|Γ| = #|Δ|) : ws_pair :=
    (Δ; transport_ws_term t eq).

  Lemma clos_red_rel_out_inv x y :
    clos_refl_trans pred1_rel x y ->
    clos_refl_trans red1_rel_alpha x y.
  Proof using wfΣ.
    induction 1.
    red in r.
    destruct x as [Γ t], y as [Δ u]; simpl in *.
    pose proof (pred1_pred1_ctx _ r).
    apply red1_rel_alpha_red1_rel_inv.
    transitivity (move_ws_term u (symmetry (All2_fold_length X))); cbn.
    unfold move_ws_term; cbn.
    eapply (clos_refl_trans_ctx_t_prod_r Γ (fun x y => red1 Σ Γ x y)).
    { intros. red. left. split; eauto. }
    { apply pred1_red in r; tea; eauto with fvs.
      now eapply red_ws_red; cbn. }
    apply: (clos_refl_trans_ctx_t_prod_l (red1_ctx Σ)).
    { intros. eapply clos_refl_trans_ctx_on_free_vars in X0; tea. }
    { intros x y a. now eapply clos_refl_trans_ctx_length in a. }
    { intros x y [b hb] [b' hb'] re. cbn. intros <-. red. right. split; auto. }
    cbn. reflexivity.
    now apply clos_rt_OnOne2_local_env_ctx_incl, red_context_red_ctx, ws_pred1_ctx_ws_red_ctx.
    constructor 2.
    etransitivity; eauto.
  Qed.

  Hint Transparent context : typeclass_instances.

  Global Instance ws_red_ctx_refl : Reflexive ws_red_ctx.
  Proof using Type.
    intros Γ. red. red. reflexivity.
  Qed.

  Global Instance ws_red_ctx_trans : Transitive ws_red_ctx.
  Proof using wfΣ.
    intros Γ Δ Δ'. apply red_context_trans; eauto with fvs.
  Qed.

  Lemma ws_red_ctx_length {x y : closed_context} (r : ws_red_ctx x y) : #|x| = #|y|.
  Proof using Type.
    now apply All2_fold_length in r.
  Qed.

  Lemma ws_red_red Γ t u :
    ws_red Σ xpred0 Γ t u ->
    red Σ Γ t u.
  Proof using Type.
    rewrite /ws_red /red.
    destruct t as [t ht], u as [u hu]; cbn.
    intros H; depind H.
    red in r. now constructor.
    constructor 2.
    destruct y as [y hy].
    econstructor 3.
    eapply IHclos_refl_trans1. f_equal. eauto.
  Qed.

  Lemma ws_red_red_ctx_aux {Γ Δ : closed_context} {t u : ws_term (shiftnP #|Γ| xpred0)} :
    ws_red Σ xpred0 Γ t u ->
    forall rctx : ws_red_ctx Δ Γ,
    red Σ Δ (transport_ws_term t (symmetry (ws_red_ctx_length rctx))) (transport_ws_term u (symmetry (ws_red_ctx_length rctx))).
  Proof using wfΣ.
    intros.
    epose proof (red_red_ctx _ Γ Δ t u).
    forward X0 by eauto with fvs.
    forward X0 by eauto with fvs.
    forward X0. now eapply ws_red_red.
    forward X0. assumption.
    exact X0.
  Qed.

  Lemma ws_red_red_ctx {Γ Δ : closed_context} {t u : ws_term (shiftnP #|Γ| xpred0)} :
    ws_red Σ xpred0 Γ t u ->
    forall rctx : ws_red_ctx Δ Γ,
    ws_red Σ xpred0 Δ (transport_ws_term t (symmetry (ws_red_ctx_length rctx))) (transport_ws_term u (symmetry (ws_red_ctx_length rctx))).
  Proof using wfΣ.
    intros.
    pose proof (ws_red_red_ctx_aux X rctx).
    now eapply red_ws_red.
  Qed.

  Lemma ws_red_irrel P Γ t ht u hu ht' hu' :
    ws_red Σ P Γ (exist t ht) (exist u hu) ->
    ws_red Σ P Γ (exist t ht') (exist u hu').
  Proof using Type.
    cbn in *.
    now rewrite (uip ht ht') (uip hu hu').
  Qed.

  Lemma clos_rt_red1_rel_ws_red1 x y :
    clos_refl_trans red1_rel x y ->
    ∑ redctx : ws_red_ctx x.π1 y.π1,
      ws_red Σ xpred0 x.π1 x.π2 (transport_ws_term y.π2 (symmetry (ws_red_ctx_length redctx))).
  Proof using wfΣ.
    intros H.
    eapply clos_rt_rt1n_iff in H.
    induction H.
    - unshelve eexists. red; red. reflexivity.
      destruct x as [Γ [x h]]; cbn. unfold transport_ws_term; cbn.
      pose proof (uip h (transport_on_free_vars h (symmetry (ws_red_ctx_length (reflexivity (proj1_sig Γ)))))).
      red.
      rewrite {1}H.
      constructor 2.
    - destruct x as [Γ t], y as [Δ u], z as [Δ' u']; simpl in *.
      destruct IHclos_refl_trans_1n.
      red in r. destruct r.
      * destruct p. subst. exists x. red.
        transitivity u; auto.
      * destruct p. subst.
        apply ws_red1_ctx_ws_pred1_ctx in r.
        apply ws_pred1_ctx_ws_red_ctx in r.
        exists (transitivity r x).
        destruct t as [t ht], u as [u hu]; cbn. noconf e.
        unshelve eapply ws_red_red_ctx in w. shelve. exact r.
        eapply ws_red_irrel. exact w.
  Qed.

  Lemma clos_rt_red1_rel_red1 x y :
    clos_refl_trans red1_rel x y ->
    red_context Σ x.π1 y.π1 * clos_refl_trans (red1 Σ x.π1) x.π2 y.π2.
  Proof using wfΣ.
    move/clos_rt_red1_rel_ws_red1 => [redctx wsred].
    split => //.
    red in wsred.
    now eapply ws_red_red in wsred; cbn in wsred.
  Qed.

  Lemma decl_body_eq_context_upto_names Γ Γ' n d :
    option_map decl_body (nth_error Γ n) = Some d ->
    eq_context_upto_names Γ Γ' ->
    option_map decl_body (nth_error Γ' n) = Some d.
  Proof using Type.
    destruct nth_error as [decl|] eqn:hnth => //.
    intros [= <-] eqctx.
    eapply All2_nth_error_Some in eqctx as (decl' & -> & eqd); tea.
    destruct eqd; reflexivity.
  Qed.

  Lemma decl_type_eq_context_upto_names Γ Γ' n d :
    option_map decl_type (nth_error Γ n) = Some d ->
    eq_context_upto_names Γ Γ' ->
    option_map decl_type (nth_error Γ' n) = Some d.
  Proof using Type.
    destruct nth_error as [decl|] eqn:hnth => //.
    intros [= <-] eqctx.
    eapply All2_nth_error_Some in eqctx as (decl' & -> & eqd); tea.
    destruct eqd; reflexivity.
  Qed.

  Lemma eq_context_upto_names_app Γ Γ' Δ :
    eq_context_upto_names Γ Γ' ->
    eq_context_upto_names (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof using Type.
    intros. apply All2_app; cbnr; tas.
  Qed.

  Definition red_ctx_alpha : relation context :=
    All2_fold (fun Γ _ => All_decls_alpha (red Σ Γ)).

  Lemma eq_context_upto_names_red_ctx Γ Δ Γ' Δ' :
    eq_context_upto_names Γ Γ' ->
    eq_context_upto_names Δ Δ' ->
    red_context Σ Γ Δ ->
    red_ctx_alpha Γ' Δ'.
  Proof using Type.
    intros.
    induction X in X0, Δ, Δ', X1 |- *. depelim X1. depelim X0. constructor.
    depelim X1. depelim X0.
    constructor. eapply IHX; tea.
    destruct r; depelim e; depelim a; subst; try constructor; eauto.
    1,3:now etransitivity.
    all:eapply red_eq_context_upto_names; eauto.
  Qed.

  Lemma eq_context_upto_names_red_ctx_alpha {Γ Δ Γ' Δ'} :
    eq_context_upto_names Γ Γ' ->
    eq_context_upto_names Δ Δ' ->
    red_ctx_alpha Γ Δ ->
    red_ctx_alpha Γ' Δ'.
  Proof using Type.
    intros.
    induction X in X0, Δ, Δ', X1 |- *. depelim X1. depelim X0. constructor.
    depelim X1. depelim X0.
    constructor. eapply IHX; tea.
    destruct a; depelim e; depelim r; subst; try constructor; eauto.
    1,3:now etransitivity.
    all:eapply red_eq_context_upto_names; eauto.
  Qed.

  Instance proper_red_ctx :
    Proper (eq_context_upto_names ==> eq_context_upto_names ==> iffT) red_ctx_alpha.
  Proof using Type.
    reduce_goal.
    split.
    intros. eapply eq_context_upto_names_red_ctx_alpha; eauto.
    intros. symmetry in X, X0. eapply eq_context_upto_names_red_ctx_alpha; eauto.
  Qed.

  Instance red_ctx_alpha_refl : Reflexive red_ctx_alpha.
  Proof using Type.
    rewrite /red_ctx_alpha.
    intros x; apply All2_fold_refl; tc.
  Qed.

  Lemma red_ctx_red_ctx_alpha_trans {Γ Δ Δ'} :
    ws_red_ctx Γ Δ -> red_ctx_alpha Δ Δ' -> red_ctx_alpha Γ Δ'.
  Proof using wfΣ.
    destruct Γ as [Γ onΓ], Δ as [Δ onΔ]; cbn. rewrite /ws_red_ctx /lift_ws /=.
    intros r r'.
    induction r in onΓ, onΔ, Δ', r' |- *; depelim r'.
    - constructor; auto.
    - move: onΓ onΔ; rewrite !on_free_vars_ctx_snoc => /andP[] onΓ ond /andP[] onΓ' ond'.
      constructor; [now eapply IHr|].
      depelim p; depelim a; constructor; auto.
      all:etransitivity; tea.
      * cbn in ond, ond'.
        eapply red_red_ctx; revgoals. exact r. all:tea.
        + rewrite wf_term_on_free_vars; eauto with fvs.
        + rewrite wf_term_ctx_on_free_vars_ctx; eauto with fvs.
      * move/andP: ond ond' => [] /= onb ont /andP[] /= onb' ont'.
        eapply red_red_ctx; revgoals. exact r. all:tea.
        + rewrite wf_term_on_free_vars; eauto with fvs.
        + rewrite wf_term_ctx_on_free_vars_ctx; eauto with fvs.
      * move/andP: ond ond' => [] /= onb ont /andP[] /= onb' ont'.
        eapply red_red_ctx; revgoals. exact r. all:tea.
        + rewrite wf_term_on_free_vars; eauto with fvs.
        + rewrite wf_term_ctx_on_free_vars_ctx; eauto with fvs.
  Qed.

  Lemma ws_red_refl_irrel P (Γ : ws_context P) (x y : ws_term (shiftnP #|Γ| P)) :
    x = y :> term ->
    ws_red Σ P Γ x y.
  Proof using Type.
    destruct x as [x hx], y as [y hy]; cbn.
    intros ->. rewrite (uip hx hy).
    constructor 2.
  Qed.

  Lemma clos_rt_red1_alpha_out x y :
    clos_refl_trans red1_rel_alpha x y ->
    ∑ redctx : red_ctx_alpha x.π1 y.π1,
      ws_red Σ xpred0 x.π1 x.π2 (transport_ws_term y.π2 (symmetry (All2_fold_length redctx))).
  Proof using wfΣ.
    intros H.
    eapply clos_rt_rt1n_iff in H.
    induction H.
    - unshelve eexists. reflexivity. eapply ws_red_refl_irrel => //.
    - destruct x as [Γ t], y as [Δ u], z as [Δ' u']; simpl in *.
      destruct IHclos_refl_trans_1n.
      red in r. destruct r.
      * destruct p. subst. exists x.
        transitivity u; auto.
        now eapply red_ws_red.
      * destruct t as [t ht], u as [u hu];
        move: r; case; move => [] r eq; noconf eq.
        + apply ws_red1_ctx_ws_pred1_ctx in r.
          apply ws_pred1_ctx_ws_red_ctx in r.
          exists (red_ctx_red_ctx_alpha_trans r x).
          eapply ws_red_irrel.
          exact (ws_red_red_ctx w r).
        + exists (eq_context_upto_names_red_ctx_alpha (symmetry r) (reflexivity _) x).
          eapply red_ws_red. eapply ws_red_red in w. cbn in w |- *.
          eapply red_eq_context_upto_names; eauto. now symmetry.
  Qed.

  Lemma clos_rt_red1_alpha_out' x y :
    clos_refl_trans red1_rel_alpha x y ->
    red_ctx_alpha x.π1 y.π1 × red Σ x.π1 x.π2 y.π2.
  Proof using wfΣ.
    move/clos_rt_red1_alpha_out => [redctx redt].
    split => //. now eapply ws_red_red in redt.
  Qed.

  Inductive clos_refl_trans_ctx_1n (R : relation context) (x : context) : context -> Type :=
  | rt1n_ctx_eq : clos_refl_trans_ctx_1n R x x
  | rt1n_ctx_trans : forall y z, eq_context_upto_names x y + R x y -> clos_refl_trans_ctx_1n R y z -> clos_refl_trans_ctx_1n R x z.


  Lemma clos_refl_trans_ctx_to_1n (x y : context) :
    clos_refl_trans_ctx (red1_ctx Σ) x y <~> clos_refl_trans_ctx_1n (red1_ctx Σ) x y.
  Proof using Type.
    split.
    induction 1. econstructor 2. eauto. constructor; auto.
    econstructor 2. left; eauto. constructor.
    clear X1 X2.
    induction IHX1 in z, IHX2 |- *.
    destruct IHX2. constructor.
    destruct s. econstructor 2. left; eauto. auto.
    econstructor 2. right; eauto. eauto.
    specialize (IHIHX1 _ IHX2). econstructor 2; eauto.

    induction 1. constructor 2. reflexivity.
    destruct s. econstructor 3. constructor 2; eauto. eauto.
    econstructor 3. constructor 1; eauto. eauto.
  Qed.

  Lemma clos_rt_red1_red1_rel_alpha (Γ : closed_context) (x y : ws_term (shiftnP #|Γ| xpred0)) :
    clos_refl_trans (red1 Σ Γ) x y -> clos_refl_trans red1_rel_alpha (Γ; x) (Γ; y).
  Proof using wfΣ.
    destruct Γ as [Γ onΓ].
    destruct x as [x hx], y as [y hy].
    cbn.
    induction 1.
    - constructor. red. left. pcuicfo.
    - rewrite (uip hx hy).
      constructor 2.
    - cbn in *.
      assert (hy' : on_free_vars (shiftnP #|Γ| xpred0) y).
      { eapply red_on_free_vars; tea; eauto with fvs. }
      specialize (IHX1 hx hy').
      econstructor 3; eauto.
  Qed.

  Lemma ws_red1_confluent Γ : confluent (ws_red1 Σ xpred0 Γ).
  Proof using wfΣ.
    intros x y z xy xz.
    pose proof (red1_rel_alpha_confluent (Γ; x) (Γ; y) (Γ; z)).
    forward X by now eapply clos_rt_red1_red1_rel_alpha, ws_red_red.
    forward X by now eapply clos_rt_red1_red1_rel_alpha, ws_red_red.
    destruct X as [[Δ nf] [redl redr]].
    eapply clos_rt_red1_alpha_out' in redl.
    eapply clos_rt_red1_alpha_out' in redr. simpl in *.
    intuition auto. red.
    assert (on_free_vars (shiftnP #|Γ| xpred0) nf) by eauto with fvs.
    eexists (exist (proj1_sig nf) H : ws_term (shiftnP #|Γ| xpred0)).
    now split; apply red_ws_red; cbn.
  Qed.

  Lemma pred_red {Γ : closed_context} {t : open_term Γ} {u} :
    clos_refl_trans (pred1 Σ Γ Γ) t u ->
    clos_refl_trans (red1 Σ Γ) t u.
  Proof using wfΣ.
    intros pred.
    epose proof (pred_on_free_vars (P:=shiftnP #|Γ| xpred0) (Γ := Γ)).
    forward H. rewrite on_free_vars_ctx_on_ctx_free_vars. eauto with fvs.
    specialize (H pred t).
    eapply (clos_rt_red1_rel_red1 (Γ; t) (Γ; (exist u H))).
    apply clos_refl_trans_out.
    apply (clos_rt_red1_alpha_out' (Γ; t) (Γ; (exist u H))).
    apply clos_red_rel_out_inv.
    destruct t as [t ht]; cbn in *.
    induction pred.
    - constructor; auto.
    - rewrite (uip ht H). constructor 2.
    - specialize (IHpred1 ht).
      assert (on_free_vars (shiftnP #|Γ| xpred0) y).
      eapply pred_on_free_vars; tea; eauto with fvs.
      transitivity ((Γ; exist y H0) : ws_pair); eauto.
  Qed.

End RedConfluence.

Arguments red1_ctx _ _ _ : clear implicits.

Section ConfluenceFacts.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext} {wfΣ : wf Σ}.

  Lemma lift_to_ws_red {Γ : closed_context} {x : term} {p : on_free_vars (shiftnP #|Γ| xpred0) x} {y} :
    red Σ Γ x y ->
    ∑ x' y' : open_term Γ,
      x = x' :> term × y = y' :> term × ws_red Σ xpred0 Γ x' y'.
  Proof using wfΣ.
    intros r. exists (exist x p). unshelve eexists.
    refine (exist y (red_on_free_vars r p _)). eauto with fvs. split => //. split => //.
    now eapply red_ws_red.
  Qed.

  Lemma ws_pred_curry_red {Γ Δ t u} : ws_pred_curry Σ xpred0 Γ Δ t u -> red Σ Γ t u.
  Proof using wfΣ.
    intros ws. red in ws.
    induction ws. red in r.
    - apply pred1_red in r; eauto with fvs.
    - constructor 2.
    - etransitivity; tea.
  Qed.

  Lemma ws_pred_pred {Γ : closed_context} {t : open_term Γ} {u} :
    ws_pred_curry Σ xpred0 Γ Γ t u ->
    clos_refl_trans (pred1 Σ Γ Γ) t u.
  Proof using Type.
    rewrite /ws_pred_curry.
    induction 1.
    - now constructor.
    - constructor 2.
    - econstructor 3; tea.
  Qed.

  Lemma lift_to_pred {Γ : closed_context} {x : term} {p : on_free_vars (shiftnP #|Γ| xpred0) x} {y} :
    red Σ Γ x y ->
    ∑ x' y' : open_term Γ,
      x = x' :> term × y = y' :> term × clos_refl_trans (pred1 Σ Γ Γ) x' y'.
  Proof using wfΣ.
    move/(lift_to_ws_red (p := p)) => [x' [y' [eq [eq' pred]]]]. subst.
    exists x', y'; repeat split => //.
    eapply red_pred' in pred. red in pred.
    now eapply ws_pred_pred in pred; cbn in *.
  Qed.

  Lemma ws_red_confluence {Γ t u v} :
    ws_red Σ xpred0 Γ t u -> ws_red Σ xpred0 Γ t v ->
    ∑ v', ws_red Σ xpred0 Γ u v' * ws_red Σ xpred0 Γ v v'.
  Proof using wfΣ.
    move=> H H'.
    destruct (ws_red1_confluent wfΣ _ _ _ _ H H') as [nf [redl redr]].
    exists nf; intuition auto.
  Qed.

  Notation byfvs := (_ ltac:(eauto with fvs)) (only parsing).

  Lemma red_ws_red_left {Γ : closed_context} {x : ws_term (shiftnP #|Γ| xpred0)} {y} :
    red Σ Γ x y -> ∑ prf, ws_red Σ xpred0 Γ x (exist y prf).
  Proof using wfΣ.
    move=> r.
    have ony : on_free_vars (shiftnP #|Γ| xpred0) y by eauto with fvs.
    exists ony.
    now eapply red_ws_red.
  Qed.

  Lemma red_confluence {Γ : closed_context} {t : open_term Γ} {u v} :
    red Σ Γ t u -> red Σ Γ t v ->
    ∑ v', red Σ Γ u v' * red Σ Γ v v'.
  Proof using wfΣ.
    move/red_ws_red_left => [onu redu].
    move/red_ws_red_left => [onv redv].
    destruct (ws_red_confluence redu redv) as [nf [redl redr]].
    now exists nf; split; [eapply ws_red_red in redl | eapply ws_red_red in redr].
  Qed.

End ConfluenceFacts.

Arguments red1_confluent {cf} {Σ} {wfΣ} {Γ t u v} {wfΓ wft}.
Arguments red_confluence {cf} {Σ} {wfΣ} {Γ t u v}.
