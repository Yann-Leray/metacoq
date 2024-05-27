(* Distributed under the terms of the MIT license. *)
From Coq Require Import CMorphisms.
From MetaCoq.Utils Require Import LibHypsNaming utils.
From MetaCoq.Common Require Import config Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICEquality PCUICLiftSubst PCUICReflect.

Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

Definition alpha_eq_predicate (eq_term : term -> term -> Type) p p' :=
  All2 eq_term p.(pparams) p'.(pparams) ×
  p.(puinst) = p'.(puinst) ×
  eq_context_upto_names p.(pcontext) p'.(pcontext) ×
  eq_term p.(preturn) p'.(preturn).

Definition alpha_eq_branch (eq_term : term -> term -> Type) br br' :=
  eq_context_upto_names br.(bcontext) br'.(bcontext) ×
  eq_term br.(bbody) br'.(bbody).

Definition alpha_eq_branches eq_term brs brs' := All2 (alpha_eq_branch eq_term) brs brs'.

Definition alpha_eq_mfixpoint (eq_term : term -> term -> Type) mfix mfix' :=
  All2 (fun d d' =>
    eq_term d.(dtype) d'.(dtype) ×
    eq_term d.(dbody) d'.(dbody) ×
    d.(rarg) = d'.(rarg) ×
    eq_binder_annot d.(dname) d'.(dname)
  ) mfix mfix'.

Reserved Notation "`≡α`".
Reserved Notation " t ≡α u" (at level 60, u at next level, format "t  ≡α  u").

Inductive alpha_eq_term : term -> term -> Type :=
| aeq_Rel : forall n,
    tRel n ≡α tRel n

| aeq_Evar : forall e args args',
    All2 (fun arg arg' => arg ≡α arg') args args' ->
    tEvar e args ≡α tEvar e args'

| aeq_Var : forall id,
    tVar id ≡α tVar id

| aeq_Sort : forall s,
    tSort s ≡α tSort s

| aeq_App : forall t t' u u',
    t ≡α t' ->
    u ≡α u' ->
    tApp t u ≡α tApp t' u'

| aeq_Const : forall c u,
    tConst c u ≡α tConst c u

| aeq_Ind : forall i u,
    tInd i u ≡α tInd i u

| aeq_Construct : forall i k u,
    tConstruct i k u ≡α tConstruct i k u

| aeq_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    ty ≡α ty' ->
    t ≡α t' ->
    tLambda na ty t ≡α tLambda na' ty' t'

| aeq_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    a ≡α a' ->
    b ≡α b' ->
    tProd na a b ≡α tProd na' a' b'

| aeq_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    t ≡α t' ->
    ty ≡α ty' ->
    u ≡α u' ->
    tLetIn na t ty u ≡α tLetIn na' t' ty' u'

| aeq_Case : forall indn p p' c c' brs brs',
    alpha_eq_predicate (fun t t' => t ≡α t') p p' ->
    c ≡α c' ->
    alpha_eq_branches (fun t t' => t ≡α t') brs brs' ->
    tCase indn p c brs ≡α tCase indn p' c' brs'

| aeq_Proj : forall p c c',
    c ≡α c' ->
    tProj p c ≡α tProj p c'

| aeq_Fix : forall mfix mfix' idx,
    alpha_eq_mfixpoint (fun t t' => t ≡α t') mfix mfix' ->
    tFix mfix idx ≡α tFix mfix' idx

| aeq_CoFix : forall mfix mfix' idx,
    alpha_eq_mfixpoint (fun t t' => t ≡α t') mfix mfix' ->
    tCoFix mfix idx ≡α tCoFix mfix' idx

| aeq_Prim i i' :
    onPrims (fun t t' => t ≡α t') eq i i' ->
    tPrim i ≡α tPrim i'
where "`≡α`" := alpha_eq_term
and   " t ≡α u " := (alpha_eq_term t u) : type_scope.
Derive Signature for alpha_eq_term.

Definition alpha_eq_decl d d' :=
  eq_binder_annot d.(decl_name) d'.(decl_name) ×
  rel_option `≡α` d.(decl_body) d'.(decl_body) ×
  d.(decl_type) ≡α d'.(decl_type).

Notation "`≡Γ`" := (All2 alpha_eq_decl).
Infix "≡Γ" := (All2 alpha_eq_decl) (at level 20, no associativity).

#[global]
Instance alpha_eq_predicate_refl eq_term {H : Reflexive eq_term} : Reflexive (alpha_eq_predicate eq_term).
Proof.
  repeat split; trea.
  apply All2_refl. reflexivity.
Qed.

#[global]
Instance alpha_eq_branch_refl eq_term {H : Reflexive eq_term} : Reflexive (alpha_eq_branch eq_term).
Proof.
  repeat split; reflexivity.
Qed.

#[global]
Instance alpha_eq_branches_refl eq_term {H : Reflexive eq_term} : Reflexive (alpha_eq_branches eq_term).
Proof.
  intro. apply All2_refl. reflexivity.
Qed.

#[global]
Instance alpha_eq_mfixpoint_refl eq_term {H : Reflexive eq_term} : Reflexive (alpha_eq_mfixpoint eq_term).
Proof.
  intro.
  apply All2_refl.
  repeat split; reflexivity.
Qed.

#[global]
Instance alpha_eq_term_refl : Reflexive `≡α`.
Proof.
  intro t.
  induction t using term_forall_list_ind.
  all: try constructor.
  all: eauto.
  all: solve_all; unfold alpha_eq_predicate, alpha_eq_branches, alpha_eq_branch, alpha_eq_mfixpoint.
  - eapply All_All2 ; eauto.
  - repeat split; tas.
    + eapply All_All2 ; eauto.
    + reflexivity.
  - eapply All_All2 ; eauto.
    intros br [_ H]; split; auto. reflexivity.
  - eapply All_All2 ; eauto.
    intros br [H H0]; split; auto.
  - eapply All_All2 ; eauto.
    intros br [H H0]; split; auto.
  - destruct p as [? []]; constructor; cbn in X; intuition eauto.
    eapply All_All2; eauto.
Qed.

#[global]
Instance alpha_eq_context_refl : Reflexive `≡Γ`.
Proof. intro Γ. apply All2_refl. repeat split; trea. destruct decl_body; constructor. reflexivity. Qed.

#[global]
Instance alpha_eq_predicate_sym eq_term {H : Symmetric eq_term} : Symmetric (alpha_eq_predicate eq_term).
Proof.
  intros p p' (?&?&?&?).
  repeat split; now symmetry.
Qed.

#[global]
Instance alpha_eq_branch_sym eq_term {H : Symmetric eq_term} : Symmetric (alpha_eq_branch eq_term).
Proof.
  intros br br' (?&?).
  repeat split; now symmetry.
Qed.

#[global]
Instance alpha_eq_branches_sym eq_term {H : Symmetric eq_term} : Symmetric (alpha_eq_branches eq_term).
Proof.
  exact _.
Qed.

#[global]
Instance alpha_eq_mfixpoint_sym eq_term {H : Symmetric eq_term} : Symmetric (alpha_eq_mfixpoint eq_term).
Proof.
  apply All2_symP.
  intros d d' (?&?&?&?).
  repeat split; now symmetry.
Qed.

#[global]
Instance alpha_eq_names_sym : Symmetric `≡α`.
Proof.
  intros u v e.
  pose proof (@RelationClasses.symmetry _ (@eq_binder_annot name name) _).
  induction u in v, e |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [
    econstructor ; eauto ;
    try eapply Forall2_symP ; eauto ; easy
  ].
  - econstructor.
    apply All2_sym. solve_all.
  - solve_all. destruct a as (r & ? & eq & ?).
    econstructor; rewrite ?e; unfold alpha_eq_predicate, alpha_eq_branches, alpha_eq_branch in *; repeat split; eauto.
    2: now symmetry.
    + eapply All2_sym; solve_all.
    + eapply All2_sym; solve_all.
      apply All2_symP; solve_all; tc.
  - econstructor. unfold alpha_eq_mfixpoint in *.
    apply All2_sym. solve_all.
  - econstructor. unfold alpha_eq_mfixpoint in *.
    apply All2_sym. solve_all.
  - econstructor.
    depelim o; cbn in X; constructor; intuition eauto.
    eapply All2_All_mix_left in a2 as h; eauto. cbn in h.
    eapply All2_sym; solve_all.
Qed.

#[global]
Instance alpha_eq_context_sym : Symmetric `≡Γ`.
Proof. apply All2_symP. intros d d' (?&?&?). repeat split; try now symmetry. destruct r; constructor. now symmetry. Qed.

#[global]
Instance alpha_eq_predicate_trans eq_term {H : Transitive eq_term} : Transitive (alpha_eq_predicate eq_term).
Proof.
  intros p p' p'' (?&?&?&?) (?&?&?&?).
  repeat split; try now etransitivity; tea.
  now eapply All2_trans.
Qed.

#[global]
Instance alpha_eq_branch_trans eq_term {H : Transitive eq_term} : Transitive (alpha_eq_branch eq_term).
Proof.
  intros br br' br'' (?&?) (?&?).
  repeat split; now etransitivity; tea.
Qed.

#[global]
Instance alpha_eq_branches_trans eq_term {H : Transitive eq_term} : Transitive (alpha_eq_branches eq_term).
Proof.
  apply All2_trans. exact _.
Qed.

#[global]
Instance alpha_eq_mfixpoint_trans eq_term {H : Transitive eq_term} : Transitive (alpha_eq_mfixpoint eq_term).
Proof.
  apply All2_trans.
  intros d d' d'' (?&?&?&?) (?&?&?&?).
  repeat split; now etransitivity.
Qed.

#[global]
Instance alpha_eq_names_trans : Transitive `≡α`.
Proof.
  intros u v w e1 e2.
  pose proof (@RelationClasses.transitivity _ (@eq_binder_annot name name) _).
  induction u in v, w, e1, e2 |- * using term_forall_list_ind.
  all: dependent destruction e1.
  all: try solve [ eauto ].
  all: try solve [
    dependent destruction e2 ; econstructor ; eauto ;
    try now etransitivity
  ].
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    eapply All2_trans'; tea.
    intros u v w [[IH]]. now eapply IH.
  - dependent destruction e2.
    unfold alpha_eq_predicate, alpha_eq_branches, alpha_eq_branch in *.
    !!solve_all.
    econstructor; unfold alpha_eq_predicate, alpha_eq_branches, alpha_eq_branch in *; solve_all; eauto.
    2: now etransitivity.
    all: eapply All2_trans'; tea; intros ??? [[IH]]; repeat split; eauto.
    * etransitivity; eassumption.
    * destruct p0, p1; etransitivity; eassumption.
    * destruct IH, p0, p1; eauto.
  - dependent destruction e2.
    econstructor. unfold alpha_eq_mfixpoint in *.
    eapply All2_All_mix_left in X as h; eauto.
    eapply All2_trans'; tea.
    intros u v w [[[IHt IHb] (?&?&?&?)] (?&?&?&?)]. repeat split; eauto. now etransitivity.
  - dependent destruction e2.
    econstructor. unfold alpha_eq_mfixpoint in *.
    eapply All2_All_mix_left in X as h; eauto.
    eapply All2_trans'; tea.
    intros u v w [[[IHt IHb] (?&?&?&?)] (?&?&?&?)]. repeat split; eauto. now etransitivity.
  - dependent destruction e2; constructor.
    depelim o; tas. depelim o0. constructor; destruct X as (hty & hdef & harr); eauto.
    1: now etransitivity.
    eapply All2_All_mix_left in harr as h; eauto.
    eapply All2_trans'; tea.
    intros ??? [[IH]]; repeat split; eauto.
Qed.

#[global]
Instance alpha_eq_context_trans : Transitive `≡Γ`.
Proof. apply All2_trans. intros d d' d'' (?&?&?) (?&?&?). repeat split; try etransitivity; tea. destruct r; depelim r0; rewrite H; constructor. etransitivity; tea. Qed.

Lemma alpha_eq_term_impl Σ Γ cmp_universe cmp_sort pb napp :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  subrelation `≡α` (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp).
Proof.
  intros univ_refl univ_refl' sort_refl sort_refl' u v e.
  induction u in v, e, Γ, napp, pb, univ_refl', sort_refl' |- * using term_forall_list_ind.
  all: dependent elimination e.
  all: try solve [ econstructor ; cbnr; eauto ].
  - constructor. solve_all.
  - solve_all.
    econstructor; eauto.
    + destruct a10 as (ep & eu & ec & er).
      repeat split; eauto.
      1: now solve_all.
      rewrite eu; reflexivity.
    + unfold alpha_eq_branches, alpha_eq_branch, eq_branches, eq_branch in *.
      solve_all.
  - constructor.
    unfold alpha_eq_mfixpoint, eq_mfixpoint in *.
    solve_all.
  - constructor.
    unfold alpha_eq_mfixpoint, eq_mfixpoint in *.
    solve_all.
  - constructor.
    depelim o; tas; constructor; destruct X as (hty & hdef & harr); eauto.
    1: now rewrite e //.
    solve_all.
Qed.

Lemma alpha_eq_term_impl_compare_term {cf:checker_flags} Σ φ Γ pb u v :
    u ≡α v -> compare_term Σ φ Γ pb u v.
Proof.
  eapply alpha_eq_term_impl ; exact _.
Qed.

Lemma alpha_eq_term_impl_eq_term {cf:checker_flags} Σ φ Γ u v :
    u ≡α v -> eq_term Σ φ Γ u v.
Proof.
  eapply alpha_eq_term_impl ; exact _.
Qed.

Lemma alpha_eq_term_impl_leq_term {cf:checker_flags} Σ φ Γ u v :
    u ≡α v -> leq_term Σ φ Γ u v.
Proof.
  eapply alpha_eq_term_impl ; exact _.
Qed.

Lemma eq_context_upto_names_alpha_eq_context Γ Γ' :
  eq_context_upto_names Γ Γ' ->
  Γ ≡Γ Γ'.
Proof.
  intro a; eapply All2_impl; tea; cbn.
  intros. destruct X; subst; repeat constructor; auto; try reflexivity.
Qed.

Lemma alpha_eq_context_impl_compare_context {cf:checker_flags} Σ φ pb Γ Γ' :
    Γ ≡Γ Γ' -> compare_context Σ φ pb Γ Γ'.
Proof.
  move/All2_fold_All2.
  intros a; eapply All2_fold_impl; tea; cbn.
  move=> Γ0 _ [na bo ty] [na' bo' ty'] [] /= en [] eb et.
  destruct eb; subst; constructor; auto.
  all: eapply alpha_eq_term_impl_compare_term; tea ; exact _.
Qed.


Lemma cmp_universe_instance_eq {u u'} : cmp_universe_instance eq u u' -> u = u'.
Proof.
  intros H.
  unfold cmp_universe_instance, on_rel in H.
  apply Forall2_map in H.
  apply Forall2_eq in H. apply map_inj in H ; revgoals.
  { intros ?? e. now inv e. }
  subst. constructor ; auto.
Qed.

Lemma cmp_global_instance_eq {gref pb napp u u'} : cmp_global_instance empty_global_env (fun _ => eq) pb gref napp u u' -> u = u'.
Proof.
  unfold cmp_global_instance, cmp_opt_variance.
  assert (global_variance empty_global_env gref napp = AllEqual) as ->.
  { destruct gref => //=. }
  apply cmp_universe_instance_eq.
Qed.

Lemma alpha_eq_term_from_eq Γ pb napp :
  subrelation (eq_term_upto_univ_napp empty_global_env (fun _ => eq) (fun _ => eq) Γ pb napp) `≡α`.
Proof.
  intros u v e.
  induction e.
  all: try solve [ econstructor ; cbnr; eauto ].
  all: try solve [ econstructor ; cbnr; solve_all; eauto ].
  - subst; constructor.
  - apply cmp_universe_instance_eq in H as <-. constructor.
  - apply cmp_global_instance_eq in H as <-. constructor.
  - apply cmp_global_instance_eq in H as <-. constructor.
  - destruct X as (Xp & Xu & Xc & Xr & Xr').
    apply cmp_universe_instance_eq in Xu.
    constructor; tas.
    + repeat split; tas. solve_all.
    + unfold eq_branches, eq_branch, alpha_eq_branches, alpha_eq_branch in *.
      solve_all.
  - constructor.
    unfold alpha_eq_mfixpoint, eq_mfixpoint in *.
    solve_all.
  - constructor.
    unfold alpha_eq_mfixpoint, eq_mfixpoint in *.
    solve_all.
  - constructor.
    destruct X as [| |a a' e [][]]; constructor; eauto.
    solve_all.
Qed.

Lemma alpha_eq_term_mkApps t t' args args' :
t ≡α t' -> All2 `≡α` args args' -> mkApps t args ≡α mkApps t' args'.
Proof.
  intro e.
  induction 1 in t, t', e |- * => //=.
  apply IHX. now constructor.
Qed.

Lemma alpha_eq_term_it_mkLambda_or_LetIn Γ Γ' u v :
  Γ ≡Γ Γ' ->
  u ≡α v ->
  it_mkLambda_or_LetIn Γ u ≡α it_mkLambda_or_LetIn Γ' v.
Proof.
  intros eq h.
  induction eq in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply IHeq => //.
    destruct r as (eqna & eqb & eqty).
    unfold mkLambda_or_LetIn. destruct eqb.
    all: now constructor.
Qed.

Lemma alpha_eq_term_lift n k u v :
  u ≡α v ->
  lift n k u ≡α lift n k v.
Proof.
  intro e.
  induction u in k, v, e |- * using term_forall_list_ind.
  all: dependent destruction e; cbn.
  all: try solve [econstructor; eauto].
  all: try solve [econstructor; solve_all; eauto].
  - solve_all.
    econstructor; eauto.
    + destruct a as (ep & eu & ec & er).
      repeat split; cbn; eauto.
      1: now solve_all.
      now rewrite -(All2_length ec).
    + unfold alpha_eq_branches, alpha_eq_branch in *; cbn.
      solve_all.
      now rewrite -(All2_length a0).
  - constructor.
    unfold alpha_eq_mfixpoint in *.
    rewrite -(All2_length a).
    solve_all.
  - constructor.
    unfold alpha_eq_mfixpoint in *.
    rewrite -(All2_length a).
    solve_all.
  - constructor.
    depelim o; tas; constructor; destruct X as (hty & hdef & harr); cbn; eauto.
    solve_all.
Qed.

Lemma alpha_eq_term_subst s s' k u v :
  u ≡α v ->
  All2 `≡α` s s' ->
  subst s k u ≡α subst s' k v.
Proof.
  intros e hss'.
  induction u in k, v, e |- * using term_forall_list_ind.
  all: dependent destruction e; cbn.
  all: try solve [econstructor; eauto].
  all: try solve [econstructor; solve_all; eauto].
  - destruct Nat.leb => //=. 2: constructor.
    rewrite -(All2_length hss').
    destruct nth_error eqn:hnth.
    + eapply All2_nth_error_Some in hnth as (t' & -> & h); tea.
      now apply alpha_eq_term_lift.
    + eapply All2_nth_error_None in hnth as ->; tea.
      constructor.
  - solve_all.
    econstructor; eauto.
    + destruct a as (ep & eu & ec & er).
      repeat split; cbn; eauto.
      1: now solve_all.
      now rewrite -(All2_length ec).
    + unfold alpha_eq_branches, alpha_eq_branch in *; cbn.
      solve_all.
      now rewrite -(All2_length a0).
  - constructor.
    unfold alpha_eq_mfixpoint in *.
    rewrite -(All2_length a).
    solve_all.
  - constructor.
    unfold alpha_eq_mfixpoint in *.
    rewrite -(All2_length a).
    solve_all.
  - constructor.
    depelim o; tas; constructor; destruct X as (hty & hdef & harr); cbn; eauto.
    solve_all.
Qed.

Lemma alpha_eq_context_subst s s' k Γ Δ :
  Γ ≡Γ Δ ->
  All2 `≡α` s s' ->
  subst_context s k Γ ≡Γ subst_context s' k Δ.
Proof.
  intros e hss'.
  induction e in k => //=.
  rewrite !subst_context_snoc.
  econstructor; try eapply IHe.
  rewrite -(All2_length e).
  destruct x as [na b ty], y as [na' b' ty'], r as (eqna & eqbod & eqty); cbn in *.
  repeat split; cbn; tas.
  - depelim eqbod; constructor.
    now apply alpha_eq_term_subst.
  - now apply alpha_eq_term_subst.
Qed.

Lemma alpha_eq_context_smash_context Γ Γ' Δ Δ' :
  Γ ≡Γ Γ' -> Δ ≡Γ Δ' ->
  smash_context Δ Γ ≡Γ smash_context Δ' Γ'.
Proof.
  induction 1 in Δ, Δ' |- * => //= eqΔ.
  destruct x as [na [b|] ty], y as [na' [b'|] ty'], r as (eqna & eqbod & eqty); cbn in *; depelim eqbod.
  - apply IHX.
    apply alpha_eq_context_subst => //=.
    repeat constructor. assumption.
  - apply IHX.
    apply All2_app => //.
    repeat constructor => //.
Qed.

Lemma alpha_eq_context_fix_context mfix mfix' :
  alpha_eq_mfixpoint `≡α` mfix mfix' ->
  fix_context mfix ≡Γ fix_context mfix'.
Proof.
  unfold alpha_eq_mfixpoint. intro X.
  apply All2_rev, All2_mapi.
  solve_all.
  repeat split; cbn; try constructor; tas.
  now apply alpha_eq_term_lift.
Qed.
