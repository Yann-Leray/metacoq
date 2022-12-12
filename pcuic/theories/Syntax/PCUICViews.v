(* Distributed under the terms of the MIT license. *)
From Coq Require CMorphisms.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICPattern PCUICReflect.

Require Import ssreflect ssrbool.
Require Import Morphisms CRelationClasses.
From Equations Require Import Equations.
Set Equations Transparent.

Fixpoint isFixLambda_app (t : term) : bool :=
  match t with
  | tApp (tFix _ _) _ => true
  | tApp (tLambda _ _ _) _ => true
  | tApp f _ => isFixLambda_app f
  | _ => false
  end.

Inductive fix_lambda_app_view : term -> term -> Type :=
| fix_lambda_app_fix mfix i l a : fix_lambda_app_view (mkApps (tFix mfix i) l) a
| fix_lambda_app_lambda na ty b l a : fix_lambda_app_view (mkApps (tLambda na ty b) l) a
| fix_lambda_app_other t a : ~~ isFixLambda_app (tApp t a) -> fix_lambda_app_view t a.
Derive Signature for fix_lambda_app_view.

Lemma view_lambda_fix_app (t u : term) : fix_lambda_app_view t u.
Proof.
  induction t; try solve [apply fix_lambda_app_other; simpl; auto].
  apply (fix_lambda_app_lambda na t1 t2 [] u).
  destruct IHt1.
  pose proof (fix_lambda_app_fix mfix i (l ++ [t2]) a).
  change (tApp (mkApps (tFix mfix i) l) t2) with (mkApps (mkApps (tFix mfix i) l) [t2]).
  now rewrite -mkApps_app.
  pose proof (fix_lambda_app_lambda na ty b (l ++ [t2]) a).
  change (tApp (mkApps (tLambda na ty b) l) t2) with (mkApps (mkApps (tLambda na ty b) l) [t2]).
  now rewrite -mkApps_app.
  destruct t; try solve [apply fix_lambda_app_other; simpl; auto].
  apply (fix_lambda_app_fix mfix idx [] u).
Defined.

Lemma eq_pair_transport {A B} (x y : A) (t : B y) (eq : y = x) :
  (x; eq_rect _ (fun x => B x) t _ eq) = (y; t) :> ∑ x, B x.
Proof.
  now destruct eq.
Qed.

Lemma view_lambda_fix_app_fix_app_sigma mfix idx l a :
  ((mkApps (tFix mfix idx) l); view_lambda_fix_app (mkApps (tFix mfix idx) l) a) =
  ((mkApps (tFix mfix idx) l); fix_lambda_app_fix mfix idx l a) :> ∑ t, fix_lambda_app_view t a.
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite {1 2}mkApps_app.
  simpl. dependent rewrite IHl.
  change (tApp (mkApps (tFix mfix idx) l) x) with (mkApps (mkApps (tFix mfix idx) l) [x]).
  now rewrite eq_pair_transport.
Qed.

Lemma view_lambda_fix_app_lambda_app_sigma na ty b l a :
  ((mkApps (tLambda na ty b) l); view_lambda_fix_app (mkApps (tLambda na ty b) l) a) =
  ((mkApps (tLambda na ty b) l); fix_lambda_app_lambda na ty b l a) :> ∑ t, fix_lambda_app_view t a.
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite {1 2}mkApps_app.
  simpl. dependent rewrite IHl.
  change (tApp (mkApps (tLambda na ty b) l) x) with (mkApps (mkApps (tLambda na ty b) l) [x]).
  now rewrite eq_pair_transport.
Qed.

Set Equations With UIP.

Lemma view_lambda_fix_app_fix_app mfix idx l a :
  view_lambda_fix_app (mkApps (tFix mfix idx) l) a =
  fix_lambda_app_fix mfix idx l a.
Proof.
  pose proof (view_lambda_fix_app_fix_app_sigma mfix idx l a).
  now noconf H.
Qed.

Lemma view_lambda_fix_app_lambda_app na ty b l a :
  view_lambda_fix_app (mkApps (tLambda na ty b) l) a =
  fix_lambda_app_lambda na ty b l a.
Proof.
  pose proof (view_lambda_fix_app_lambda_app_sigma na ty b l a).
  now noconf H.
Qed.

#[global]
Hint Rewrite view_lambda_fix_app_fix_app view_lambda_fix_app_lambda_app : rho.

Equations construct_cofix_discr (t : term) : bool :=
construct_cofix_discr (tConstruct _ _ _) => true;
construct_cofix_discr (tCoFix _ _) => true;
construct_cofix_discr _ => false.
Transparent construct_cofix_discr.

Equations discr_construct_cofix (t : term) : Prop :=
  { | tConstruct _ _ _ => False;
    | tCoFix _ _ => False;
    | _ => True }.
Transparent discr_construct_cofix.

Inductive construct_cofix_view : term -> Type :=
| construct_cofix_construct ind u i : construct_cofix_view (tConstruct ind u i)
| construct_cofix_cofix mfix idx : construct_cofix_view (tCoFix mfix idx)
| construct_cofix_other t : discr_construct_cofix t -> construct_cofix_view t.

Equations view_construct_cofix (t : term) : construct_cofix_view t :=
{ | tConstruct ind u i => construct_cofix_construct ind u i;
  | tCoFix mfix idx => construct_cofix_cofix mfix idx;
  | t => construct_cofix_other t I }.

Lemma construct_cofix_discr_match {A} t cstr (cfix : mfixpoint term -> nat -> A) default :
  construct_cofix_discr t = false ->
  match t with
  | tConstruct ind c _ => cstr ind c
  | tCoFix mfix idx => cfix mfix idx
  | _ => default
  end = default.
Proof.
  destruct t => //.
Qed.

Equations discr_construct0_cofix (t : term) : Prop :=
  { | tConstruct _ u _ => u <> 0;
    | tCoFix _ _ => False;
    | _ => True }.
Transparent discr_construct0_cofix.

Inductive construct0_cofix_view : term -> Type :=
| construct0_cofix_construct ind i : construct0_cofix_view (tConstruct ind 0 i)
| construct0_cofix_cofix mfix idx : construct0_cofix_view (tCoFix mfix idx)
| construct0_cofix_other t : discr_construct0_cofix t -> construct0_cofix_view t.

Equations view_construct0_cofix (t : term) : construct0_cofix_view t :=
{ | tConstruct ind 0 i => construct0_cofix_construct ind i;
  | tCoFix mfix idx => construct0_cofix_cofix mfix idx;
  | t => construct0_cofix_other t _ }.

Lemma isFixLambda_app_mkApps t l : isFixLambda_app t -> isFixLambda_app (mkApps t l).
Proof.
  induction l using rev_ind; simpl; auto.
  rewrite mkApps_app.
  intros isf. specialize (IHl isf).
  simpl. rewrite IHl. destruct (mkApps t l); auto.
Qed.

Definition isFixLambda (t : term) : bool :=
  match t with
  | tFix _ _ => true
  | tLambda _ _ _ => true
  | _ => false
  end.

Inductive fix_lambda_view : term -> Type :=
| fix_lambda_lambda na b t : fix_lambda_view (tLambda na b t)
| fix_lambda_fix mfix i : fix_lambda_view (tFix mfix i)
| fix_lambda_other t : ~~ isFixLambda t -> fix_lambda_view t.

Lemma view_fix_lambda (t : term) : fix_lambda_view t.
Proof.
  destruct t; repeat constructor.
Qed.

Lemma isFixLambda_app_mkApps' t l x : isFixLambda t -> isFixLambda_app (tApp (mkApps t l) x).
Proof.
  induction l using rev_ind; simpl; auto.
  destruct t; auto. simpl => //.
  intros isl. specialize (IHl isl).
  simpl in IHl.
  now rewrite mkApps_app /=.
Qed.

Lemma bool_pirr (b b' : bool) (p q : b = b') : p = q.
Proof. noconf p. now noconf q. Qed.

Lemma view_lambda_fix_app_other t u (H : ~~ isFixLambda_app (tApp t u)) :
  view_lambda_fix_app t u = fix_lambda_app_other t u H.
Proof.
  induction t; simpl; f_equal; try apply uip.
  - simpl in H => //.
  - specialize (IHt1 H).
    rewrite IHt1. destruct t1; auto.
  - simpl in H => //.
Qed.

Import Equations.Prop.Logic.

Definition not_lhs Σ (t : term) :=
  (∑ k n rd x,
    symb_hd t = Some (k, n) ×
    lookup_rules Σ k = Some rd ×
    first_match (rd.(prules) ++ rd.(rules)) t = Some x
  ) ->
  False.

Variant lhs_view t :=
| is_lhs (k : kername) (rd : rewrite_decl)
    (r : rewrite_rule) (s : found_substitution)
    (H : PCUICDepth.list_depth s.(found_subst) < PCUICDepth.depth t) : lhs_view t

| is_not_lhs.

Arguments is_lhs {_}.
Arguments is_not_lhs {_}.

Definition lhs_viewc Σ (t : term) : lhs_view t :=
  match symb_hd t with
  | None => is_not_lhs
  | Some (k, n) =>
  match lookup_rules Σ k with
  | None => is_not_lhs
  | Some rd =>
  match inspect (first_match (rd.(prules) ++ rd.(rules)) t) with
  | exist None _ => is_not_lhs
  | exist (Some (r, s)) e => is_lhs k rd r s (first_match_subst_depth _ _ _ _ e)
  end end end.

Inductive lhs_view_spec Σ (t : term) : lhs_view t -> Type :=
| is_lhs_spec k rd r s H :
    lookup_rules Σ k = Some rd ->
    first_match (rd.(prules) ++ rd.(rules)) t = Some (r, s) ->
    lhs_view_spec Σ t (is_lhs k rd r s H)

| is_not_lhs_spec :
    not_lhs Σ t ->
    lhs_view_spec Σ t is_not_lhs.

Lemma lhs_viewc_sound Σ t : lhs_view_spec Σ t (lhs_viewc Σ t).
Proof.
  unfold lhs_viewc.
  1: destruct symb_hd as [[k n]|] eqn:e1.
  1: destruct lookup_rules eqn:e2.
  1: destruct inspect eqn:e3.
  1: destruct x as [[]|].
  all: econstructor; tea.
  all: intros (k' & n' & rd' & (r' & s') & e1' & e2' & e3').
  all: rewrite e1' in e1 => //; injection e1 as [= -> ->].
  all: rewrite e2' in e2 => //; injection e2 as [= ->].
  injection e3.
  rewrite e3' => //.
Qed.

Lemma rigid_arg_pattern_not_lhs Σ pat tm s :
  rigid_arg_pattern_match pat tm = Some s ->
  not_lhs Σ tm.
Proof using Type.
  intros e.
  enough (symb_hd tm = None).
  { intros (k & n & _ & _ & e' & _); congruence. }
  revert tm s e.
  induction pat using rigid_arg_pattern_ind with (P := fun _ => True) => //.
  all: intros; destruct tm => //=.
  cbn in e.
  destruct rigid_arg_pattern_match eqn:? => //.
  eapply IHpat => //.
  eassumption.
Qed.

Lemma rigid_arg_pattern_not_fixapp pat tm s :
  rigid_arg_pattern_match pat tm = Some s ->
  ~~ isFixLambda_app tm.
Proof using Type.
  intro H.
  cut (~~isFixLambda_app tm × ~~ isFixLambda tm). 1: now intros [].
  revert tm s H.
  induction pat using rigid_arg_pattern_ind with (P := fun _ => True) => //.
  all: intros; destruct tm => //=.
  cbn in H.
  destruct rigid_arg_pattern_match eqn:? => //.
  edestruct IHpat; tea.
  split; auto.
  now destruct tm1.
Qed.

Lemma not_lhs_matches Σ k n r rdecl decl tm s :
  declared_rules_gen (lookup_env Σ) k rdecl ->
  nth_error (prules rdecl ++ rules rdecl) r = Some decl ->
  symb_hd tm = Some (k, n) ->
  pattern_matches (pat_lhs decl) tm s ->
  not_lhs Σ tm -> False.
Proof.
  intros.
  apply declared_rules_lookup_gen in H.
  assert (∑ decl', first_match (rdecl.(prules) ++ rdecl.(rules)) tm = Some decl') as ((decl' & s') & Hfm).
  { unfold first_match.
    induction (prules rdecl ++ rules rdecl) in r, decl, H0, H2 |- *; cbn.
    1: now destruct r.
    destruct r; cbn in H0.
    1: { injection H0 as [= ->]. rewrite H2. eexists; reflexivity. }
    destruct pattern_match. 1: eexists; reflexivity.
    now eapply IHl. }
  apply H3.
  repeat eexists; tea.
Qed.
