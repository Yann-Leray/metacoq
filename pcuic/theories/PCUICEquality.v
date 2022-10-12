(* Distributed under the terms of the MIT license. *)
From Coq Require Import CMorphisms.
From MetaCoq.Template Require Import LibHypsNaming config utils Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICCases
     PCUICLiftSubst PCUICReflect PCUICRelevance PCUICRelevanceTerm.

Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

#[global]
Instance All2_fold_len {A} P (Γ Δ : list A) : HasLen (All2_fold P Γ Δ) #|Γ| #|Δ| :=
  All2_fold_length.

Implicit Types (cf : checker_flags).

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

(** Cumulative inductive types:

  To simplify the development, we allow the variance list to not exactly 
  match the instances, so as to keep syntactic ws_cumul_pb an equivalence relation
  even on ill-formed terms. It corresponds to the right notion on well-formed terms.
*)

Definition R_universe_variance (R : conv_pb -> Universe.t -> Universe.t -> Prop) pb v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => R pb   (Universe.make u) (Universe.make u')
  | Variance.Invariant => R Conv (Universe.make u) (Universe.make u')
  end.

Fixpoint R_universe_instance_variance R pb v u u' :=
  match u, u' return Prop with
  | u :: us, u' :: us' =>
    match v with
    | [] => R_universe_instance_variance R pb v us us' 
      (* Missing variance stands for irrelevance, we still check that the instances have
        the same length. *)
    | v :: vs => R_universe_variance R pb v u u' /\
        R_universe_instance_variance R pb vs us us'
    end
  | [], [] => True
  | _, _ => False
  end.

Definition global_variance Σ gr napp :=
  match gr with
  | IndRef ind =>
    match lookup_inductive Σ ind with
    | Some (mdecl, idecl) => 
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => if (context_assumptions ctx) <=? napp then mdecl.(ind_variance)
        else None
      | None => None
      end
    | None => None
    end
  | ConstructRef ind k =>
    match lookup_constructor Σ ind k with
    | Some (mdecl, idecl, cdecl) =>
      if (cdecl.(cstr_arity) + mdecl.(ind_npars))%nat <=? napp then
        (** Fully applied constructors are always compared at the same supertype, 
          which implies that no universe ws_cumul_pb needs to be checked here. *)
        Some []
      else None
    | _ => None
    end
  | _ => None
  end.

Definition R_opt_variance R pb v :=
  match v with 
  | Some v => R_universe_instance_variance R pb v
  | None => R_universe_instance (R Conv)
  end.

Definition R_global_instance Σ R pb gr napp :=
  R_opt_variance R pb (global_variance Σ gr napp).

Definition R_ind_universes {cf:checker_flags} (Σ : global_env_ext) pb ind n i i' :=
  R_global_instance Σ (fun pb => compare_universe pb (global_ext_constraints Σ)) pb (IndRef ind) n i i'.  

Lemma R_universe_instance_impl R R' :
  RelationClasses.subrelation R R' ->
  RelationClasses.subrelation (R_universe_instance R) (R_universe_instance R').
Proof.
  intros H x y xy. eapply Forall2_impl ; tea.
Qed.

Lemma R_universe_instance_impl' R R' :
  RelationClasses.subrelation R R' ->
  forall u u', R_universe_instance R u u' -> R_universe_instance R' u u'.
Proof.
  intros H x y xy. eapply Forall2_impl ; tea.
Qed.

Section compare_decls.
  (* Only the types are compared using cumulativity,
     the bodies are always compared for conversion.
   *)
  
  Context {compare_term : conv_pb -> term -> term -> Type} {pb : conv_pb}.
  Inductive compare_decls  : context_decl -> context_decl -> Type :=
  | compare_vass {na T na' T'} :
    eq_binder_annot na na' ->
    compare_term pb T T' ->
    compare_decls (vass na T) (vass na' T')
  | compare_vdef {na b T na' b' T'} :
    eq_binder_annot na na' ->
    compare_term Conv b b' ->
    compare_term pb T T' -> 
    compare_decls (vdef na b T) (vdef na' b' T').

  Derive Signature NoConfusion for compare_decls.
End compare_decls.
Arguments compare_decls : clear implicits.

Definition eq_context_gen compare_term pb (Γ0 : mark_context) :=
  (All2_fold (fun Γ _ => compare_decls (fun pb' => compare_term pb' (Γ0 ,,, marks_of_context Γ)) pb)).

Global Hint Unfold eq_context_gen : core.

Notation eq1 := (fun (pb : conv_pb) => @eq term).
Notation eq2 := (fun (pb : conv_pb) (Γ : mark_context) => @eq term).

Notation eq_context_upto_names := (All2 (compare_decls eq1 Conv)).

Definition eq_context_upto_names_gen := (eq_context_gen eq2 Conv []).

Lemma eq_context_upto_names_upto_names_gen Γ Γ' : eq_context_upto_names Γ Γ' <~> eq_context_upto_names_gen Γ Γ'.
Proof.
  split; intros e; depind e; constructor; auto.
Qed.

Lemma compare_decls_impl compare_term compare_term' pb pb' :
  subrelation (compare_term Conv) (compare_term' Conv) ->
  subrelation (compare_term pb)   (compare_term' pb') ->
  subrelation (compare_decls compare_term pb)
    (compare_decls compare_term' pb').
Proof.
  intros he hle x y []; constructor; auto.
Qed.

Lemma eq_context_gen_impl compare_term compare_term' pb pb' :
  (forall Γ, subrelation (compare_term Conv Γ) (compare_term' Conv Γ)) ->
  (forall Γ, subrelation (compare_term pb Γ)   (compare_term' pb' Γ)) ->
  forall Γ, subrelation (eq_context_gen compare_term pb Γ) (eq_context_gen compare_term' pb' Γ).
Proof.
  intros he hpb Γ0 x y eq.
  eapply All2_fold_impl; tea => /= Γ Γ' d d' H.
  eapply compare_decls_impl; tea; [eapply he | eapply hpb].
Qed.

Lemma compare_decl_impl_ondecl P compare_term compare_term' pb pb' d d' :
  ondecl P d ->
  (forall x y, P x -> compare_term Conv x y -> compare_term' Conv x y) ->
  (forall x y, P x -> compare_term pb   x y -> compare_term' pb'  x y) ->
  compare_decls compare_term pb d d' ->
  compare_decls compare_term' pb' d d'.
Proof.
  intros ond he hle cd; depelim cd; depelim ond; constructor => //; eauto.
Qed.

Lemma compare_decl_map compare_term pb f g d d' :
  compare_decls (fun pb' x y => compare_term pb' (f x) (g y)) pb d d' ->
  compare_decls compare_term pb (map_decl f d) (map_decl g d').
Proof.
  intros h; depelim h; constructor; intuition auto.
Qed.

Lemma compare_decls_eq_marks {compare_term pb} Γ0 Γ Γ' :
  eq_context_gen compare_term pb Γ0 Γ Γ' -> marks_of_context Γ = marks_of_context Γ'.
Proof.
  induction 1; cbnr.
  f_equal; [|apply IHX].
  now destruct p.
Qed.

Definition bcompare_decls (compare_term : conv_pb -> term -> term -> bool)
  pb (d d' : context_decl) : bool :=
  match d, d' with
  | {| decl_name := na; decl_body := None; decl_type := T |},
    {| decl_name := na'; decl_body := None; decl_type := T' |} =>
    eqb_binder_annot na na' && compare_term pb T T'
  | {| decl_name := na; decl_body := Some b; decl_type := T |},
    {| decl_name := na'; decl_body := Some b'; decl_type := T' |} =>
    eqb_binder_annot na na' && compare_term Conv b b' && compare_term pb T T'
  | _, _ => false
  end.

#[global] Polymorphic Instance compare_decl_refl compare_term pb :
  CRelationClasses.Reflexive (compare_term Conv) ->
  CRelationClasses.Reflexive (compare_term pb) ->
  CRelationClasses.Reflexive (compare_decls compare_term pb).
Proof.
  intros he hle [? []] ; constructor; auto ; reflexivity.
Qed.

#[global]
Polymorphic Instance compare_decl_refl_conv compare_term :
  CRelationClasses.Reflexive (compare_term Conv) ->
  CRelationClasses.Reflexive (compare_decls compare_term Conv).
Proof.
  tc.
Qed.

#[global] Polymorphic Instance compare_decl_sym compare_term pb :
  CRelationClasses.Symmetric (compare_term Conv) ->
  CRelationClasses.Symmetric (compare_term pb) ->
  CRelationClasses.Symmetric (compare_decls compare_term pb).
Proof.
  intros he hle d d' []; constructor ; symmetry ; auto.
Qed.

#[global]
Polymorphic Instance compare_decl_sym_conv compare_term :
  CRelationClasses.Symmetric (compare_term Conv) ->
  CRelationClasses.Symmetric (compare_decls compare_term Conv). 
Proof.
  tc.
Qed.

#[global]
Polymorphic Instance compare_decl_trans compare_term pb :
  CRelationClasses.Transitive (compare_term Conv) ->
  CRelationClasses.Transitive (compare_term pb) ->
  CRelationClasses.Transitive (compare_decls compare_term pb).
Proof.
  intros he hle x y z h h'; depelim h; depelim h'; constructor; auto;
  etransitivity; eauto.
Qed.

#[global]
Polymorphic Instance compare_decl_trans_conv compare_term :
  CRelationClasses.Transitive (compare_term Conv) ->
  CRelationClasses.Transitive (compare_decls compare_term Conv).
Proof.
  tc.
Qed.

#[global]
Instance alpha_eq_reflexive : CRelationClasses.Reflexive eq_context_upto_names.
Proof.
  intros x. eapply All2_refl. reflexivity.
Qed.

#[global]
Instance alpha_eq_symmmetric : CRelationClasses.Symmetric eq_context_upto_names.
Proof.
  intros x. eapply All2_symP. tc.
Qed.

#[global]
Instance alpha_eq_trans : CRelationClasses.Transitive eq_context_upto_names.
Proof.
  intros x y z. apply All2_trans. tc.
Qed.

#[global]
Polymorphic Instance eq_context_refl compare_term pb : 
  (forall Γ, CRelationClasses.Reflexive (compare_term Conv Γ)) ->
  (forall Γ, CRelationClasses.Reflexive (compare_term pb Γ)) ->
  forall Γ, CRelationClasses.Reflexive (eq_context_gen compare_term pb Γ).
Proof.
  intros heq hle Γ x.
  eapply All2_fold_refl.
  intros. reflexivity. 
Qed.

#[global]
Polymorphic Instance eq_context_refl_conv compare_term : 
  (forall Γ, CRelationClasses.Reflexive (compare_term Conv Γ)) ->
  forall Γ, CRelationClasses.Reflexive (eq_context_gen compare_term Conv Γ).
Proof.
  tc.
Qed.

#[global]
Polymorphic Instance eq_context_sym compare_term pb : 
  (forall Γ, CRelationClasses.Symmetric (compare_term Conv Γ)) ->
  (forall Γ, CRelationClasses.Symmetric (compare_term pb Γ)) ->
  forall Γ, CRelationClasses.Symmetric (eq_context_gen compare_term pb Γ).
Proof.
  intros heq hle Γ x.
  eapply All2_fold_sym.
  intros. erewrite <- compare_decls_eq_marks; tea. now symmetry. 
Qed.

#[global]
Polymorphic Instance eq_context_sym_conv compare_term : 
  (forall Γ, CRelationClasses.Symmetric (compare_term Conv Γ)) ->
  forall Γ, CRelationClasses.Symmetric (eq_context_gen compare_term Conv Γ).
Proof.
  tc.
Qed.

#[global]
Polymorphic Instance eq_context_trans compare_term pb : 
  (forall Γ, CRelationClasses.Transitive (compare_term Conv Γ)) ->
  (forall Γ, CRelationClasses.Transitive (compare_term pb Γ)) ->
  forall Γ, CRelationClasses.Transitive (eq_context_gen compare_term pb Γ).
Proof.
  intros he hle Γ x y z.
  eapply All2_fold_trans; intros.
  transitivity y0 => //.
  erewrite compare_decls_eq_marks; tea.
Qed.

#[global]
Polymorphic Instance eq_context_trans_conv compare_term : 
  (forall Γ, CRelationClasses.Transitive (compare_term Conv Γ)) ->
  forall Γ, CRelationClasses.Transitive (eq_context_gen compare_term Conv Γ).
Proof.
  tc.
Qed.

Definition eq_predicate (eq_term : mark_context -> term -> term -> Type) Re Γ p p' :=
  All2 (eq_term Γ) p.(pparams) p'.(pparams) ×
  R_universe_instance Re p.(puinst) p'.(puinst) ×
  eq_context_upto_names_gen p.(pcontext) p'.(pcontext) ×
  eq_term (Γ ,,, marks_of_context (inst_case_predicate_context p)) p.(preturn) p'.(preturn).

Definition eq_branch (eq_term : mark_context -> term -> term -> Type) Γ p br br' :=
  eq_context_upto_names_gen br.(bcontext) br'.(bcontext) ×
  eq_term (Γ ,,, marks_of_context (inst_case_branch_context p br)) br.(bbody) br'.(bbody).

Definition eq_branches (eq_term : mark_context -> term -> term -> Type) Γ p brs brs' :=
  All2 (eq_branch eq_term Γ p) brs brs'.

Definition eq_mfix (eq_term : mark_context -> term -> term -> Type) Γ mfix mfix' :=
  All2 (fun d d' =>
    eq_binder_annot d.(dname) d'.(dname) ×
    d.(rarg) = d'.(rarg) ×
    eq_term Γ d.(dtype) d'.(dtype) ×
    eq_term (Γ ,,, marks_of_context (fix_context mfix)) d.(dbody) d'.(dbody)
  ) mfix mfix'.

Lemma eq_predicate_inst_case_predicate_context_marks {eq_term Re Γ p p'} :
  eq_predicate eq_term Re Γ p p' -> marks_of_context (inst_case_predicate_context p) = marks_of_context (inst_case_predicate_context p').
Proof.
  intros (_ & _ & Hctxt & _).
  eapply @compare_decls_eq_marks in Hctxt.
  rewrite !mark_inst_case_predicate_context; apply Hctxt.
Qed.

Lemma eq_branch_inst_case_branch_context_marks {eq_term Γ p p' br br'} :
  eq_branch eq_term Γ p br br' ->
  marks_of_context (inst_case_branch_context p br) = marks_of_context (inst_case_branch_context p' br').
Proof.
  rewrite !mark_inst_case_branch_context.
  intros [Hctxt _].
  now apply compare_decls_eq_marks in Hctxt.
Qed.

Lemma eq_mfix_fix_context_marks {eq_term Γ mfix mfix'} :
  eq_mfix eq_term Γ mfix mfix' -> marks_of_context (fix_context mfix) = marks_of_context (fix_context mfix').
Proof.
  rewrite /fix_context /marks_of_context !map_rev !map_mapi //= !mapi_cst_map.
  intro H. f_equal. revert H.
  induction 1; cbnr.
  f_equal; tas.
  now destruct r as (e & _).
Qed.


(** ** Syntactic ws_cumul_pb up-to universes
  We don't look at printing annotations *)

(** ws_cumul_pb is indexed by a natural number that counts the number of applications
  that surround the current term, used to implement cumulativity of inductive types
  correctly (only fully applied constructors and inductives benefit from it). *)  

Reserved Notation " Σ ;;; Γ ⊢ t <==[ pb , napp ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  <==[ pb , napp ]  u").


Inductive compare_term_upto_univ_napp_rel Σ (R : conv_pb -> Universe.t -> Universe.t -> Prop) (isTermIrrel : global_env -> mark_context -> term -> Type)
  (pb : conv_pb) (napp : nat) (Γ : mark_context) : term -> term -> Type :=
| eq_Rel : forall n,
    Σ ;;; Γ ⊢ tRel n <==[ pb , napp ] tRel n

| eq_Evar : forall e args args',
    All2 (compare_term_upto_univ_napp_rel Σ R isTermIrrel Conv 0 Γ) args args' ->
    Σ ;;; Γ ⊢ tEvar e args <==[ pb , napp ] tEvar e args'

| eq_Var : forall id,
    Σ ;;; Γ ⊢ tVar id <==[ pb , napp ] tVar id

| eq_Sort : forall s s',
    R pb s s' ->
    Σ ;;; Γ ⊢ tSort s  <==[ pb , napp ] tSort s'

| eq_App : forall t t' u u',
    Σ ;;; Γ ⊢ t <==[ pb , S napp ] t' ->
    Σ ;;; Γ ⊢ u <==[ Conv , 0 ] u' ->
    Σ ;;; Γ ⊢ tApp t u <==[ pb , napp ] tApp t' u'

| eq_Const : forall c u u',
    R_universe_instance (R Conv) u u' ->
    Σ ;;; Γ ⊢ tConst c u <==[ pb , napp ] tConst c u'

| eq_Ind : forall i u u',
    R_global_instance Σ R pb (IndRef i) napp u u' ->
    Σ ;;; Γ ⊢ tInd i u <==[ pb , napp ] tInd i u'

| eq_Construct : forall i k u u',
    R_global_instance Σ R pb (ConstructRef i k) napp u u' ->
    Σ ;;; Γ ⊢ tConstruct i k u <==[ pb , napp ] tConstruct i k u'

| eq_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ ty <==[ Conv , 0 ] ty' ->
    Σ ;;; Γ ,, na.(binder_relevance) ⊢ t <==[ pb , 0 ] t' ->
    Σ ;;; Γ ⊢ tLambda na ty t <==[ pb , napp ] tLambda na' ty' t'

| eq_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ a <==[ Conv , 0 ] a' ->
    Σ ;;; Γ ,, na.(binder_relevance) ⊢ b <==[ pb , 0 ] b' ->
    Σ ;;; Γ ⊢ tProd na a b <==[ pb , napp ] tProd na' a' b'

| eq_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ t <==[ Conv , 0 ] t' ->
    Σ ;;; Γ ⊢ ty <==[ Conv , 0 ] ty' ->
    Σ ;;; Γ ,, na.(binder_relevance) ⊢ u <==[ pb , 0 ] u' ->
    Σ ;;; Γ ⊢ tLetIn na t ty u <==[ pb , napp ] tLetIn na' t' ty' u'

| eq_Case : forall indn p p' c c' brs brs',
    eq_predicate (compare_term_upto_univ_napp_rel Σ R isTermIrrel Conv 0) (R Conv) Γ p p' ->
    Σ ;;; Γ ⊢ c <==[ Conv , 0 ] c' ->
    eq_branches (compare_term_upto_univ_napp_rel Σ R isTermIrrel Conv 0) Γ p brs brs' ->
    Σ ;;; Γ ⊢ tCase indn p c brs <==[ pb , napp ] tCase indn p' c' brs'

| eq_Proj : forall p c c',
    Σ ;;; Γ ⊢ c <==[ Conv , 0 ] c' ->
    Σ ;;; Γ ⊢ tProj p c <==[ pb , napp ] tProj p c'

| eq_Fix : forall mfix mfix' idx,
    eq_mfix (compare_term_upto_univ_napp_rel Σ R isTermIrrel Conv 0) Γ mfix mfix' ->
    Σ ;;; Γ ⊢ tFix mfix idx <==[ pb , napp ] tFix mfix' idx

| eq_CoFix : forall mfix mfix' idx,
    eq_mfix (compare_term_upto_univ_napp_rel Σ R isTermIrrel Conv 0) Γ mfix mfix' ->
    Σ ;;; Γ ⊢ tCoFix mfix idx <==[ pb , napp ] tCoFix mfix' idx

| eq_Irrel : forall t t',
    isTermIrrel Σ Γ t -> isTermIrrel Σ Γ t' ->
    Σ ;;; Γ ⊢ t <==[ pb , napp ] t'

(* | eq_Prim i : compare_term_upto_univ_napp_rel Σ R pb napp (tPrim i) (tPrim i) *)
where " Σ ;;; Γ ⊢ t <==[ pb , napp ] u " := (compare_term_upto_univ_napp_rel Σ _ _ pb napp Γ t u) : type_scope.

Derive Signature for compare_term_upto_univ_napp_rel.

Notation compare_term_upto_univ_rel Σ R isTermIrrel pb := (compare_term_upto_univ_napp_rel Σ R isTermIrrel pb 0).

(* ** Syntactic comparison up-to universes *)

Definition compare_term_napp `{checker_flags} (pb : conv_pb) Σ φ napp Γ (t u : term) :=
  compare_term_upto_univ_napp_rel Σ (fun pb => compare_universe pb φ) isTermIrrel pb napp Γ t u.
  
Definition compare_term `{checker_flags} (pb : conv_pb) Σ φ Γ (t u : term) :=
  compare_term_upto_univ_rel Σ (fun pb => compare_universe pb φ) isTermIrrel pb Γ t u.

(* ** Syntactic conversion up-to universes *)

Notation eq_term := (compare_term Conv).

(* ** Syntactic cumulativity up-to universes *)

Notation leq_term := (compare_term Cumul).

Definition compare_opt_term `{checker_flags} (pb : conv_pb) Σ φ Γ (t u : option term) :=
  match t, u with
  | Some t, Some u => compare_term pb Σ φ Γ t u
  | None, None => True
  | _, _ => False
  end.

Definition compare_decl `{checker_flags} pb Σ φ Γ (d d' : context_decl) :=
  compare_decls (fun pb => compare_term pb Σ φ Γ) pb d d'.

Notation eq_decl := (compare_decl Conv).
Notation leq_decl := (compare_decl Cumul).

Definition compare_context `{checker_flags} pb Σ φ Γ0 (Γ Δ : context) :=
  eq_context_gen (fun pb => compare_term pb Σ φ) pb Γ0 Γ Δ.
  
Notation eq_context := (compare_context Conv).
Notation leq_context := (compare_context Cumul).

Notation NoTermIrrel := (fun (_ : global_env) (_ : mark_context) (_ : term) => False).

Definition compatible_with_compare_term isTermIrrel :=
  forall Σ R pb napp Γ t u,
  compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ t u ->
  isTermIrrel Σ Γ t <~> isTermIrrel Σ Γ u.

Existing Class compatible_with_compare_term.

Lemma compare_term_upto_univ_napp_rel_relevance {Σ R pb napp Γ t u r} :
  compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ t u ->
  isTermRel Σ Γ t r <~> isTermRel Σ Γ u r.
Proof.
  induction t in Γ, napp, pb, u, r |- * using term_forall_list_ind.
  all: intro e; depelim e.
  all: try solve [ split; intros; eauto ].
  all: try solve [ split; intros; assert (r = Irrelevant) by (eapply isTermRel_inj; tea); congruence ].
  all: try solve [ split; intro _e; inv _e; econstructor; tea ].
  - split; intro H; inversion H; subst; constructor; rewrite -?e1; eauto.
    + eapply IHt1; tea.
    + eapply IHt2; tea.
    + eapply IHt1; tea.
    + eapply IHt2; tea. now rewrite -e1 in X0.
  - split; intro H; inversion H; subst; constructor; rewrite -?e1; eauto.
    + eapply IHt2; tea.
    + eapply IHt1; tea.
    + eapply IHt2; tea. now rewrite -e1 in X.
    + eapply IHt1; tea.
  - split; intro H; inversion H; subst; constructor; rewrite -?e1; eauto.
    + eapply IHt3; tea.
    + eapply IHt2; tea.
    + eapply IHt1; tea.
    + eapply IHt3; tea. now rewrite -e1 in X.
    + eapply IHt2; tea.
    + eapply IHt1; tea. now rewrite -e1 in X1.
  - split; intro H; inversion H; subst; econstructor; eauto.
    + eapply IHt1; tea.
    + eapply IHt2; tea.
    + eapply IHt1; tea.
    + eapply IHt2; tea.
  - split; intro _e; inversion _e; subst; apply eq_predicate_inst_case_predicate_context_marks in e as eqmks;
    destruct X as (X & X' & X''), X1 as (X1 & X1' & X1''), e as (e & e' & e'' & e''');
    apply All2_length in e as eqmksp; econstructor; repeat split; eauto; rewrite -?eqmks -?eqmksp.
    + solve_all.
      destruct b0; eexists; eapply a0; tea.
    + apply compare_decls_eq_marks in e'' as eqmks'.
      apply All2_eq_eq, All2_map_inv in eqmks'.
      induction e''. 1: constructor.
      inv X'; inv eqmks'; inversion X1'; subst; inversion p0; subst.
      all: constructor; [apply IHe''|]; eauto.
      all: apply All2_map, All2_eq in X6 as eqmks'.
      * rewrite -H.
        destruct X8 as (tt & X8).
        split; auto.
        rewrite /marks_of_context -eqmks'.
        eapply X8.
      * rewrite -H.
        destruct X8 as (X8' & X8).
        split; auto;
        rewrite /marks_of_context -eqmks'.
        all: eauto.
    + eapply X''; tea.
    + solve_all.
      eapply All2_All_mix_left in e1; tea.
      clear -e1 eqmksp.
      induction e1; constructor; auto.
      destruct r as (((? & ?) & ? & ? & ?) & ?).
      apply (eq_branch_inst_case_branch_context_marks (p' := p')) in e as eqmk.
      destruct e.
      split.
      * rewrite -eqmksp.
        clear -w e.
        apply compare_decls_eq_marks in e as eqmks'.
        apply All2_eq_eq, All2_map_inv in eqmks'.
        induction e. 1: constructor.
        inv eqmks'; inversion w; subst; inversion p0; subst.
        all: constructor; [apply IHe|]; eauto.
        all: apply All2_map, All2_eq in X as eqmks'.
     -- rewrite -H.
        destruct X1 as (tt & X1).
        split; auto.
        rewrite /marks_of_context -eqmks'.
        eapply X1.
     -- rewrite -H.
        destruct X1 as (X1' & X1).
        split; auto;
        rewrite /marks_of_context -eqmks'.
        all: eauto.
      * rewrite -eqmk.
        eexists.
        eapply i; tea.
    + eapply IHt; tea.
    + solve_all.
      destruct b; eexists; eapply a0; tea.
    + rewrite eqmksp.
      apply compare_decls_eq_marks in e'' as eqmks'.
      apply All2_eq_eq, All2_map_inv in eqmks'.
      induction e''. 1: constructor.
      inv X'; inv eqmks'; inversion X1'; subst; inversion p0; subst.
      all: constructor; [apply IHe''|]; eauto.
      all: apply All2_map, All2_eq in X6 as eqmks'.
      * rewrite H.
        destruct X8 as (tt & X8).
        split; auto.
        rewrite /marks_of_context eqmks'.
        eapply X8.
      * rewrite H.
        destruct X8 as (X8' & X8).
        split; auto;
        rewrite /marks_of_context eqmks'.
        all: eauto.
    + eapply X''; tea. now rewrite eqmks.
    + unfold wfTermRel_branch; rewrite eqmksp.
      eapply All2_All_mix_right in e1; tea.
      solve_all; destruct b as (Hc & Hb).
      * destruct a0.
        clear -e1 Hc.
        apply compare_decls_eq_marks in e1 as eqmks'.
        apply All2_eq_eq, All2_map_inv in eqmks'.
        induction e1. 1: constructor.
        inv eqmks'; inversion Hc; subst; inversion p; subst.
        all: constructor; [apply IHe1|]; eauto.
        all: apply All2_map, All2_eq in X as eqmks'.
     -- rewrite H.
        destruct X1 as (tt & X1).
        split; auto.
        rewrite /marks_of_context eqmks'.
        eapply X1.
     -- rewrite H.
        destruct X1 as (X1' & X1).
        split; auto;
        rewrite /marks_of_context eqmks'.
        all: eauto.
      * apply (eq_branch_inst_case_branch_context_marks (p' := p')) in a0 as eqmk.
        destruct a0.
        destruct Hb.
        eexists.
        eapply b1; tea.
        now rewrite eqmk.
    + eapply IHt; tea.
  - split; intro H; inversion H; subst; econstructor; tea; eapply IHt; eauto.
  - split; intro _e; inv _e.
    all: apply eq_mfix_fix_context_marks in e as eqmks.
    eapply All2_nth_error_Some in e as e'; tea; destruct e' as (def' & H' & -> & _); econstructor => //.
    2: apply All2_sym in e as e'; eapply All2_nth_error_Some in e' as (def' & H' & <- & _); tea; econstructor => //.
    1: eapply All2_All_mix_left in e; tea; apply All2_sym in e.
    2: eapply All2_All_mix_right in e; tea.
    all: unfold wfTermRel_mfix in *; solve_all; rewrite -?eqmks.
    + eapply b0; tea. now rewrite -a0.
    + eapply a2; tea.
    + eapply b; tea. now rewrite a2.
    + eapply a1; tea.
  - split; intro _e; inv _e.
    all: apply eq_mfix_fix_context_marks in e as eqmks.
    eapply All2_nth_error_Some in e as e'; tea; destruct e' as (def' & H' & -> & _); econstructor => //.
    2: apply All2_sym in e as e'; eapply All2_nth_error_Some in e' as (def' & H' & <- & _); tea; econstructor => //.
    1: eapply All2_All_mix_left in e; tea; apply All2_sym in e.
    2: eapply All2_All_mix_right in e; tea.
    all: unfold wfTermRel_mfix in *; solve_all; rewrite -?eqmks.
    + eapply b0; tea. now rewrite -a0.
    + eapply a2; tea.
    + eapply b; tea. now rewrite a2.
    + eapply a1; tea.
Qed.

Lemma eq_term_isTermRel_1 {Σ R pb napp Γ t u r} :
  compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ t u ->
  isTermRel Σ Γ t r -> isTermRel Σ Γ u r.
Proof. intros H H'; eapply compare_term_upto_univ_napp_rel_relevance in H; now apply H. Qed.

Lemma eq_term_isTermRel_2 {Σ R pb napp Γ t u r} :
  compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ t u ->
  isTermRel Σ Γ u r -> isTermRel Σ Γ t r.
Proof. intros; now eapply compare_term_upto_univ_napp_rel_relevance. Qed.

#[global] Instance compare_term_upto_univ_napp_rel_irrelevant : compatible_with_compare_term isTermIrrel.
Proof. intros until u. apply compare_term_upto_univ_napp_rel_relevance. Qed.

Notation eq_context_upto Σ R isTermIrrel pb := 
  (eq_context_gen (fun pb' => compare_term_upto_univ_rel Σ R isTermIrrel pb') pb).


Lemma global_variance_napp_mon {Σ gr napp napp' v} : 
  napp <= napp' ->
  global_variance Σ gr napp = Some v ->
  global_variance Σ gr napp' = Some v.
Proof.
  intros hnapp.
  rewrite /global_variance.
  destruct gr; try congruence.
  - destruct lookup_inductive as [[mdecl idec]|] => //.
    destruct destArity as [[ctx s]|] => //.
    elim: Nat.leb_spec => // cass indv.
    elim: Nat.leb_spec => //. lia.
  - destruct lookup_constructor as [[[mdecl idecl] cdecl]|] => //.
    elim: Nat.leb_spec => // cass indv.
    elim: Nat.leb_spec => //. lia.
Qed.

#[global]
Instance R_global_instance_impl_same_napp Σ R R' pb pb' gr napp :
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R pb) (R' pb') ->
  subrelation (R_global_instance Σ R pb gr napp) (R_global_instance Σ R' pb' gr napp).
Proof.
  intros he hle t t'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [v|] eqn:glob.
  induction t in v, t' |- *; destruct v, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
  now eapply R_universe_instance_impl'.
Qed.

#[global]
Instance R_global_instance_impl Σ R R' pb pb' gr napp napp' :
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R Conv) (R' pb') ->
  RelationClasses.subrelation (R pb) (R' pb') ->
  napp <= napp' ->
  subrelation (R_global_instance Σ R pb gr napp) (R_global_instance Σ R' pb' gr napp').
Proof.
  intros he hle hele hnapp t t'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [v|] eqn:glob.
  rewrite (global_variance_napp_mon hnapp glob).
  induction t in v, t' |- *; destruct v, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
  destruct (global_variance _ _ napp') as [v|] eqn:glob'; eauto using R_universe_instance_impl'.
  induction t in v, t' |- *; destruct v, t'; simpl; auto; intros H; inv H.
  eauto.
  split; auto.
  destruct t0; simpl; auto.
Qed.

Lemma global_variance_empty gr napp env : env.(declarations) = [] -> global_variance env gr napp = None.
Proof.
  destruct env; cbn => ->. destruct gr; auto.
Qed.

(** Pure syntactic equality, without cumulative inductive types subtyping *)

#[global]
Instance R_global_instance_empty_impl Σ R R' pb pb' gr napp napp' :
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R Conv) (R' pb') ->
  RelationClasses.subrelation (R pb) (R' pb') ->
  subrelation (R_global_instance empty_global_env R pb gr napp) (R_global_instance Σ R' pb' gr napp').
Proof.
  intros he hle hele t t'.
  rewrite /R_global_instance /R_opt_variance. simpl.
  rewrite global_variance_empty //.
  destruct global_variance as [v|]; eauto using R_universe_instance_impl'.
  induction t in v, t' |- *; destruct v, t'; simpl; intros H; inv H; auto.
  simpl.
  split; auto.
  destruct t0; simpl; auto.
Qed.

Lemma onctx_eq_ctx_impl P Γ0 ctx ctx' eq_term eq_term' :
  onctx P ctx ->
  (forall x, P x -> forall Γ y, eq_term Conv Γ x y -> eq_term' Conv Γ x y) ->
  eq_context_gen eq_term  Conv Γ0 ctx ctx' ->
  eq_context_gen eq_term' Conv Γ0 ctx ctx'.
Proof.
  intros onc HP H1.
  induction H1; depelim onc; constructor; eauto; intuition auto; simpl in *.
  destruct o; depelim p; constructor; auto.
Qed.

#[global]
Instance compare_term_upto_univ_impl Σ R R' isTermIrrel isTermIrrel' pb pb' napp napp' Γ :
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R Conv) (R' pb') ->
  RelationClasses.subrelation (R pb) (R' pb') ->
  napp <= napp' ->
  (forall Γ t, isTermIrrel Σ Γ t -> isTermIrrel' Σ Γ t) ->
  subrelation (compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ) (compare_term_upto_univ_napp_rel Σ R' isTermIrrel' pb' napp' Γ).
Proof.
  intros he hle hele hnapp hirrel t t'.
  induction t in napp, napp', hnapp, t', pb, pb', hle, hele, Γ |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor; auto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor; auto.
    eapply IHt1. 4:eauto. all:auto with arith. eauto.
  - inversion 1; subst; constructor; auto.
    eapply R_global_instance_impl. 5:eauto. all:auto.
  - inversion 1; subst; constructor; auto.
    eapply R_global_instance_impl. 5:eauto. all:eauto.
  - inversion 1; subst; constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
    * eapply R_universe_instance_impl'; eauto.
  - inversion 1; subst; constructor; auto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (? & ? & ? & ?). repeat split; eauto.
  - inversion 1; subst; constructor; auto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (? & ? & ? & ?). repeat split; eauto.
Qed.

#[global]
Instance compare_term_upto_univ_empty_impl Σ R R' isTermIrrel isTermIrrel' pb pb' napp napp' Γ Γ' :
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R Conv) (R' pb') ->
  RelationClasses.subrelation (R pb) (R' pb') ->
  (forall Γ'' t, isTermIrrel empty_global_env (Γ ,,, Γ'') t -> isTermIrrel' Σ (Γ' ,,, Γ'') t) ->
  subrelation (compare_term_upto_univ_napp_rel empty_global_env R isTermIrrel pb napp Γ) (compare_term_upto_univ_napp_rel Σ R' isTermIrrel' pb' napp' Γ').
Proof.
  assert (forall Γ (r : relevance) Γ', Γ ,, r ,,, Γ' = Γ ,,, ([r] ,,, Γ')) by (intros; rewrite app_context_assoc => //).
  intros he hle hele hirrel t t'.
  induction t in napp, napp', t', pb, pb', hle, hele, Γ, Γ', hirrel |- * using term_forall_list_ind; pose proof (hirrel0 := hirrel []);
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor; auto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor; auto.
    + eapply IHt1; tea.
    + eapply IHt2; tea.
      intros Γ'' t.
      do 2 rewrite H.
      eapply hirrel.
  - inversion 1; subst; constructor; auto.
    + eapply IHt1; tea.
    + eapply IHt2; tea.
      intros Γ'' t.
      do 2 rewrite H.
      eapply hirrel.
  - inversion 1; subst; constructor; auto.
    + eapply IHt1; tea.
    + eapply IHt2; tea.
    + eapply IHt3; tea.
      intros Γ'' t.
      do 2 rewrite H.
      eapply hirrel.
  - inversion 1; subst; constructor; auto. 
    (* eapply shelf bug... fixed in unifall *)
    eapply R_global_instance_empty_impl. 4:eauto. all:eauto.
  - inversion 1; subst; constructor; auto.
    eapply R_global_instance_empty_impl. 4:eauto. all:eauto.
  - inversion 1; subst; constructor; auto; unfold eq_predicate, eq_branches, eq_branch in *; solve_all.
    * eapply R_universe_instance_impl'; eauto.
    * eapply c; tea.
      intros Γ'' t'.
      do 2 rewrite -app_context_assoc.
      eapply hirrel.
    * eapply b1; tea.
      intros Γ'' t'.
      do 2 rewrite -app_context_assoc.
      eapply hirrel.
  - inversion 1; subst; constructor; auto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (? & ? & ? & ?). repeat split; eauto.
    eapply c0; tea.
    intros Γ'' t'.
    do 2 rewrite -app_context_assoc.
    eapply hirrel.
  - inversion 1; subst; constructor; auto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (? & ? & ? & ?). repeat split; eauto.
    eapply c0; tea.
    intros Γ'' t'.
    do 2 rewrite -app_context_assoc.
    eapply hirrel.
Qed.

#[global]
Instance compare_term_upto_univ_NoTermIrrel_ctx Σ R pb napp Γ Γ' :
  subrelation (compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb napp Γ) (compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb napp Γ').
Proof.
  intros t t'.
  induction t in napp, t', pb, Γ, Γ' |- * using term_forall_list_ind; inversion 1; subst; constructor; eauto.
  - eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
  - unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
  - eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (? & ? & ? & ?). repeat split; eauto.
  - eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y (? & ? & ? & ?). repeat split; eauto.
Qed.

#[global]
Instance eq_term_upto_univ_leq Σ R isTermIrrel pb napp napp' Γ :
  RelationClasses.subrelation (R Conv) (R pb) ->
  napp <= napp' ->
  subrelation (compare_term_upto_univ_napp_rel Σ R isTermIrrel Conv napp Γ) (compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp' Γ).
Proof.
  intros H Hnapp. eapply compare_term_upto_univ_impl; auto; exact _.
Qed.

#[global]
Instance eq_term_leq_term {cf:checker_flags} Σ φ Γ
  : subrelation (eq_term Σ φ Γ) (leq_term Σ φ Γ).
Proof.
  eapply eq_term_upto_univ_leq; auto; exact _.
Qed.

Lemma upto_eq_impl Σ R isTermIrrel pb Γ :
  RelationClasses.Reflexive (R Conv) ->
  RelationClasses.Reflexive (R pb) ->
  subrelation (compare_term_upto_univ_rel Σ (fun _ => eq) (fun _ _ _ => False) pb Γ) (compare_term_upto_univ_rel Σ R isTermIrrel pb Γ).
Proof.
  intros he hle. eapply compare_term_upto_univ_impl ; auto.
  all: move => ? ? -> //.
Qed.

Lemma compare_term_upto_univ_cst_ Σ R isTermIrrel napp pb Γ t t' :
  (compare_term_upto_univ_napp_rel Σ (fun _ => R Conv) isTermIrrel pb napp Γ t t') <~>
  (compare_term_upto_univ_napp_rel Σ R isTermIrrel Conv napp Γ t t').
Proof.
  split ; intros.
  all: eapply compare_term_upto_univ_impl ; [..|eassumption] ; eauto.
  all: now red.
Qed.

#[global]
Instance R_global_instance_refl Σ R pb gr napp : 
  RelationClasses.Reflexive (R Conv) ->
  RelationClasses.Reflexive (R pb) ->
  RelationClasses.Reflexive (R_global_instance Σ R pb gr napp).
Proof.
  intros rRE rRle u.
  rewrite /R_global_instance.
  destruct global_variance as [v|] eqn:lookup.
  - induction u in v |- *; simpl; auto;
    unfold R_opt_variance in IHu; destruct v; simpl; auto.
    split; auto.
    destruct t; simpl; auto.
  - apply Forall2_same; eauto.
Qed.

#[global]
Instance eq_binder_annot_equiv {A} : RelationClasses.Equivalence (@eq_binder_annot A A).
Proof.
  split. 
  - red. reflexivity.
  - red; now symmetry.
  - intros x y z; unfold eq_binder_annot.
    apply transitivity.
Qed. 

Definition eq_binder_annot_refl {A} x : @eq_binder_annot A A x x.
Proof. reflexivity. Qed.

#[global]
Hint Resolve eq_binder_annot_refl : core.

(* TODO MOVE *)
#[global]
Existing Instance All2_symP.

(* TODO MOVE *)
#[global]
Instance Forall2_symP :
  forall A (P : A -> A -> Prop),
    RelationClasses.Symmetric P ->
    Symmetric (Forall2 P).
Proof.
  intros A P h l l' hl.
  induction hl. all: auto.
Qed.

Lemma eq_binder_relevances_refl (x : list aname) : All2 (on_rel eq binder_relevance) x x.
Proof. now eapply All_All2_refl, All_refl. Qed.
#[global]
Hint Resolve eq_binder_relevances_refl : core.

#[global]
Instance R_universe_instance_refl Re : RelationClasses.Reflexive Re -> 
  RelationClasses.Reflexive (R_universe_instance Re).
Proof. intros tRe x. eapply Forall2_map. 
  induction x; constructor; auto.
Qed.

#[global]
Instance R_universe_instance_sym Re : RelationClasses.Symmetric Re -> 
  RelationClasses.Symmetric (R_universe_instance Re).
Proof. intros tRe x y. now eapply Forall2_symP. Qed.
 
#[global]
Instance R_universe_instance_trans Re : RelationClasses.Transitive Re -> 
  RelationClasses.Transitive (R_universe_instance Re).
Proof. intros tRe x y z. now eapply Forall2_trans. Qed.

Lemma onctx_eq_ctx P ctx Γ0 compare_term :
  onctx P ctx ->
  (forall Γ x, P x -> compare_term Conv Γ x x) ->
  eq_context_gen compare_term Conv Γ0 ctx ctx.
Proof.
  intros onc HP.
  induction onc.
  - constructor; auto.
  - constructor; auto; simpl.
    destruct x as [na [b|] ty]; destruct p; simpl in *;
    constructor; auto.
Qed.

#[global]
Polymorphic Instance creflexive_eq A : CRelationClasses.Reflexive (@eq A).
Proof. intro x. constructor. Qed.

#[global]
Polymorphic Instance eq_predicate_refl Re Ru :
  (forall Γ, CRelationClasses.Reflexive (Re Γ)) ->
  RelationClasses.Reflexive Ru ->
  forall Γ, CRelationClasses.Reflexive (eq_predicate Re Ru Γ).
Proof.
  intros hre hru Γ.
  intros p. unfold eq_predicate; intuition auto; try reflexivity.
  eapply All2_same; reflexivity.
Qed.

#[global]
Polymorphic Instance eq_branch_refl Re :
  (forall Γ, CRelationClasses.Reflexive (Re Γ)) ->
  forall Γ p, CRelationClasses.Reflexive (eq_branch Re Γ p).
Proof.
  intros hre Γ p.
  intros br. unfold eq_branch; intuition auto; reflexivity.
Qed.

#[global]
Polymorphic Instance eq_branches_refl Re :
  (forall Γ, CRelationClasses.Reflexive (Re Γ)) ->
  forall Γ p, CRelationClasses.Reflexive (eq_branches Re Γ p).
Proof.
  intros hre Γ p.
  intros brs. apply All2_same; reflexivity.
Qed.

#[global]
Polymorphic Instance eq_mfix_refl Re :
  (forall Γ, CRelationClasses.Reflexive (Re Γ)) ->
  forall Γ, CRelationClasses.Reflexive (eq_mfix Re Γ).
Proof.
  intros hre Γ.
  intros mfix. unfold eq_mfix; eapply All2_same.
  intuition auto; try reflexivity.
Qed.

#[global]
Polymorphic Instance compare_term_upto_univ_refl Σ R isTermRel pb napp Γ :
  RelationClasses.Reflexive (R Conv) ->
  RelationClasses.Reflexive (R pb) ->
  Reflexive (compare_term_upto_univ_napp_rel Σ R isTermRel pb napp Γ).
Proof.
  intros he hpb t.
  induction t in Γ, napp, pb, hpb |- * using term_forall_list_ind.
  all: simpl.
  all: try constructor. all: eauto.
  all: try solve [eapply All_All2 ; eauto].
  all: try solve [eapply Forall2_same ; eauto].
  - apply R_global_instance_refl; auto.
  - apply R_global_instance_refl; auto.
  - destruct X as [? [? ?]].
    unfold eq_predicate; solve_all.
    eapply All_All2; eauto. reflexivity.
    eapply onctx_eq_ctx in a0; eauto. reflexivity.
  - eapply All_All2; unfold eq_branch; eauto; simpl; intuition eauto.
    eapply onctx_eq_ctx in a; eauto. reflexivity.
  - eapply All_All2; eauto; simpl; intuition eauto.
  - eapply All_All2; eauto; simpl; intuition eauto.
Qed.

#[global]
Polymorphic Instance compare_term_upto_univ_refl_conv Σ R isTermRel napp Γ :
  RelationClasses.Reflexive (R Conv) ->
  Reflexive (compare_term_upto_univ_napp_rel Σ R isTermRel Conv napp Γ).
Proof. tc. Qed.

#[global]
Instance compare_term_refl {cf} pb {Σ : global_env} φ Γ : Reflexive (compare_term pb Σ φ Γ).
Proof. eapply compare_term_upto_univ_refl; tc. Qed.

#[global]
Polymorphic Instance R_global_instance_sym Σ R pb gr napp : 
  RelationClasses.Symmetric (R Conv) ->
  RelationClasses.Symmetric (R pb) ->
  RelationClasses.Symmetric (R_global_instance Σ R pb gr napp).
Proof.
  intros rRE rRle u u'.
  rewrite /R_global_instance.
  destruct global_variance as [v|] eqn:lookup.
  - induction u in u', v |- *; destruct u'; simpl; auto;
    destruct v as [|v vs]; unfold R_opt_variance in IHu; simpl; auto.
    intros [Ra Ru']. split.
    destruct v; simpl; auto.
    apply IHu; auto.
  - apply Forall2_symP; eauto.
Qed.
 
Lemma onctx_eq_ctx_sym P ctx ctx' Γ0 compare_term :
  onctx P ctx ->
  (forall x : term, P x -> forall Γ y, compare_term Conv Γ x y -> compare_term Conv Γ y x) ->
  eq_context_gen compare_term Conv Γ0 ctx ctx' ->
  eq_context_gen compare_term Conv Γ0 ctx' ctx.
Proof.
  intros onc HP H1.
  induction H1; depelim onc; constructor; intuition auto; simpl in *.
  erewrite <- compare_decls_eq_marks; tea.
  depelim p; depelim o; constructor; auto; try now symmetry.
Qed.

#[global]
Polymorphic Instance compare_term_upto_univ_sym Σ R isTermIrrel pb napp Γ :
  RelationClasses.Symmetric (R Conv) ->
  RelationClasses.Symmetric (R pb) ->
  Symmetric (compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ).
Proof.
  intros he hle u v e.
  pose proof (@RelationClasses.symmetry _ (@eq_binder_annot name name) _).
  induction u in Γ, pb, hle, v, napp, e |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [ econstructor ; symmetry ; eauto ].
  all: try solve [
    econstructor ; eauto using R_global_instance_sym ;
    try eapply Forall2_symP ; eauto
  ].
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [h1 h2]. eapply h1 in h2 ; auto.
  - econstructor; eauto. rewrite -e1. eauto.
  - econstructor; eauto. rewrite -e1. eauto.
  - econstructor; eauto. rewrite -e1. eauto.
  - solve_all.
    pose proof (eq_inst := eq_predicate_inst_case_predicate_context_marks e).
    destruct e as (r & ? & eq & ?).
    econstructor; rewrite ?e; unfold eq_predicate, eq_branches, eq_branch in *; solve_all; eauto.
    eapply All2_sym; solve_all.
    unfold R_universe_instance in r |- *.
    eapply Forall2_symP; eauto.
    eapply onctx_eq_ctx_sym in eq; eauto.
    rewrite -eq_inst. auto.
    eapply All2_sym. solve_all.
    eapply onctx_eq_ctx_sym in a; eauto.
    erewrite <- eq_branch_inst_case_branch_context_marks.
    now apply b0.
    constructor; tea.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    erewrite eq_mfix_fix_context_marks in h; tea.
    clear e X.
    rewrite /eq_mfix. remember (fix_context mfix'). clear Heqc.
    induction h.
    + constructor.
    + destruct r as ((h1 & h2) & (han & hrarg & hty & hbod)).
      eapply h1 in hty; auto. constructor; auto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    erewrite eq_mfix_fix_context_marks in h; tea.
    clear e X.
    rewrite /eq_mfix. remember (fix_context mfix'). clear Heqc.
    induction h.
    + constructor.
    + destruct r as ((h1 & h2) & (han & hrarg & hty & hbod)).
      eapply h1 in hty; auto. constructor; auto.
Qed.

#[global]
Instance compare_term_upto_univ_sym_conv Σ R isTermIrrel napp Γ :
  RelationClasses.Symmetric (R Conv) ->
  Symmetric (compare_term_upto_univ_napp_rel Σ R isTermIrrel Conv napp Γ).
Proof.
  tc.
Qed.

#[global]
Instance compare_term_sym {cf} Σ φ Γ : Symmetric (compare_term Conv Σ φ Γ).
Proof.
  intros t u e.
  eapply compare_term_upto_univ_sym_conv; tea.
  tc.
Qed.

#[global]
Instance eq_term_sym {cf} Σ φ Γ : Symmetric (eq_term Σ φ Γ).
Proof. tc. Qed.

#[global]
Polymorphic Instance eq_predicate_sym R Re :
  (forall Γ, CRelationClasses.Symmetric (R Γ)) ->
  RelationClasses.Symmetric Re ->
  forall Γ, CRelationClasses.Symmetric (eq_predicate R Re Γ).
Proof.
  intros hr hre Γ.
  intros p p' Hp. pose proof (eq_predicate_inst_case_predicate_context_marks Hp).
  destruct Hp as (Hparams & Huinst & Hctxt & Hret); repeat split; try now symmetry.
Qed.

#[global]
Polymorphic Instance eq_branch_sym Re p :
  (forall Γ, CRelationClasses.Symmetric (Re Γ)) ->
  forall Γ, CRelationClasses.Symmetric (eq_branch Re Γ p).
Proof.
  intros hre Γ.
  intros br br' Hbr.
  epose proof (eq_branch_inst_case_branch_context_marks Hbr).
  destruct Hbr as (Hctxt & Hbod). rewrite H in Hbod.
  split; now symmetry.
Qed.

#[global]
Polymorphic Instance eq_branches_sym Re p :
  (forall Γ, CRelationClasses.Symmetric (Re Γ)) ->
  forall Γ, CRelationClasses.Symmetric (eq_branches Re Γ p).
Proof.
  intros hre Γ.
  intros brs. unfold eq_branches; intuition auto; try now symmetry.
Qed.

#[global]
Polymorphic Instance eq_mfix_sym Re :
  (forall Γ, CRelationClasses.Symmetric (Re Γ)) ->
  forall Γ, CRelationClasses.Symmetric (eq_mfix Re Γ).
Proof.
  intros hre Γ.
  intros mfix mfix' Hmfix.
  pose proof (eq_mfix_fix_context_marks Hmfix).
  unfold eq_mfix; apply All2_sym, All2_impl with (1 := Hmfix).
  intuition auto; try now symmetry.
Qed.

#[global]
Instance R_global_instance_trans Σ R pb gr napp :
  RelationClasses.Transitive (R Conv) ->
  RelationClasses.Transitive (R pb) ->
  RelationClasses.Transitive (R_global_instance Σ R pb gr napp).
Proof.
  intros he hle x y z.
  unfold R_global_instance, R_opt_variance.
  destruct global_variance as [v|].
  clear -he hle.
  induction x in y, z, v |- *; destruct y, z, v; simpl; auto => //. eauto.
  intros [Ra Rxy] [Rt Ryz].
  split; eauto.
  destruct t1; simpl in *; auto.
  now etransitivity; eauto.
  now etransitivity; eauto.
  eapply Forall2_trans; auto.
Qed.

Lemma onctx_eq_ctx_trans P ctx ctx' ctx'' Γ0 compare_term :
  onctx P ctx ->
  (forall x, P x -> forall Γ y z, compare_term Conv Γ x y -> compare_term Conv Γ y z -> compare_term Conv Γ x z) ->
  eq_context_gen compare_term Conv Γ0 ctx ctx' ->
  eq_context_gen compare_term Conv Γ0 ctx' ctx'' ->
  eq_context_gen compare_term Conv Γ0 ctx ctx''.
Proof.
  intros onc HP H1; revert ctx''. unfold eq_context_gen in *.
  induction H1; depelim onc; intros ctx'' H; depelim H; constructor; intuition auto; simpl in *.
  erewrite <- compare_decls_eq_marks in c; tea.
  depelim o. depelim p0.
  - depelim c0; constructor; [now etransitivity|eauto].
  - depelim c1; constructor; [now etransitivity|eauto ..].
Qed.

#[global]
Polymorphic Instance eq_predicate_trans R Re :
  (forall Γ, CRelationClasses.Transitive (R Γ)) ->
  RelationClasses.Transitive Re ->
  forall Γ, CRelationClasses.Transitive (eq_predicate R Re Γ).
Proof.
  intros hre hru Γ p p' p'' e1 e2.
  pose proof (eq_predicate_inst_case_predicate_context_marks e1).
  destruct e1 as (Hparams1 & Huinst1 & Hctxt1 & Hreturn1), e2 as (Hparams2 & Hunist2 & Hctxt2 & Hreturn2).
  repeat split; try now etransitivity; tea.
  eapply All2_trans; eauto.
Qed.

#[global]
Polymorphic Instance eq_branch_trans Re p :
  (forall Γ, CRelationClasses.Transitive (Re Γ)) ->
  forall Γ, CRelationClasses.Transitive (eq_branch Re Γ p).
Proof.
  intros hre Γ.
  intros br br' br'' Hbr Hbr'.
  epose proof (eq_branch_inst_case_branch_context_marks (p' := p) Hbr).
  destruct Hbr as (Hctxt & Hbod), Hbr' as (Hctxt' & Hbod'). rewrite -H in Hbod'.
  split; etransitivity; tea.
Qed.

#[global]
Polymorphic Instance eq_branches_trans Re p :
  (forall Γ, CRelationClasses.Transitive (Re Γ)) ->
  forall Γ, CRelationClasses.Transitive (eq_branches Re Γ p).
Proof.
  intros hre.
  intros brs. unfold eq_branches; intros.
  eapply All2_trans; tea. tc.
Qed.

#[global]
Polymorphic Instance eq_mfix_trans Re :
  (forall Γ, CRelationClasses.Transitive (Re Γ)) ->
  forall Γ, CRelationClasses.Transitive (eq_mfix Re Γ).
Proof.
  intros hre Γ.
  intros mfix. unfold eq_mfix; intros.
  rewrite -(eq_mfix_fix_context_marks X) in X0.
  eapply All2_trans; tea.
  intros d d' d'' [] []; repeat split; now etransitivity.
Qed.

Lemma All_All2_All2_trans {A} (P : A -> Type) (Q : A -> A -> Type) l l' l'' :
  All P l -> All2 Q l l' -> All2 Q l' l'' ->
  (forall x, P x -> forall y z, Q x y -> Q y z -> Q x z) ->
  All2 Q l l''.
Proof.
  induction 1 in l', l'' |- *; intros X1 X2;
  dependent destruction X1; dependent destruction X2; constructor.
  + eapply X0; tea.
  + eapply IHX; tea.
Qed.

#[global]
Polymorphic Instance compare_term_upto_univ_trans Σ R isTermIrrel pb napp Γ :
  RelationClasses.Transitive (R Conv) ->
  RelationClasses.Transitive (R pb) ->
  compatible_with_compare_term isTermIrrel ->
  Transitive (compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ).
Proof.
  intros he hle hirrel u v w e1 e2.
  pose proof (@RelationClasses.transitivity _ (@eq_binder_annot name name) _).
  induction u in pb, hle, v, w, napp, e1, e2, Γ |- * using term_forall_list_ind.
  all: pose proof (e1' := e1); dependent destruction e1.
  all: try solve [ eauto ].
  all: try solve [ assert (isTermIrrel Σ Γ w) by (eapply hirrel in e2; apply e2 => //); constructor => // ].
  all: dependent destruction e2.
  all: try solve [ eassert (isTermIrrel Σ Γ _) by (eapply hirrel in e1'; apply e1' => //); constructor => // ].
  all: try solve [ econstructor ; eauto ; try eapply Forall2_trans ; eauto ].
  all: try solve [ econstructor ; eauto ; try eapply R_global_instance_trans ; eauto ].
  - econstructor.
    eapply All_All2_All2_trans; tea.
    intros; eauto.
  - econstructor ; eauto. rewrite -e in e2_2. eauto.
  - econstructor ; eauto. rewrite -e in e2_2. eauto.
  - econstructor ; eauto. rewrite -e in e2_3. eauto.
  - pose proof (eq_predicate_inst_case_predicate_context_marks e).
    econstructor.
    * destruct e as (Hparams & Huinst & Hcontext & Hreturn),
               e2 as (Hparams1 & Huinst1 & Hcontext1 & Hreturn1),
               X as (IHparams & IHcontext & IHreturn).
      rewrite -H0 in Hreturn1.
      repeat split.
      + eapply All_All2_All2_trans; tea.
        intros; eauto.
      + etransitivity; eauto.
      + eapply onctx_eq_ctx_trans in IHcontext; tea.
        etransitivity; cbn in *; tea.
      + eapply IHreturn; eauto.
    * eapply IHu; eauto.
    * eapply All_All2_All2_trans; tea.
      + apply All2_impl with (1 := e4) => br br' Hbr.
        destruct Hbr as [Hctxt Hbod].
        split; eauto. rewrite mark_inst_case_branch_context in Hbod. rewrite mark_inst_case_branch_context. tea.
      + intros br [] br' br'' ebr.
        epose proof (eq_branch_inst_case_branch_context_marks (p' := p) ebr).
        move: ebr => [? ?] [? ebod1].
        split; eauto.
        eapply onctx_eq_ctx_trans; tea. etransitivity; tea.
        rewrite -H1 in ebod1. eauto.
  - econstructor.
    eapply All_All2_All2_trans; tea.
    + apply eq_mfix_fix_context_marks in e.
      rewrite e. assumption.
    + intros d (IHty & IHbo) d' d'' (Hnam & Hrarg & Hty & Hbo) (Hnam1 & Hrarg1 & Hty1 & Hbo1).
      repeat split; try etransitivity; eauto.
  - econstructor.
    eapply All_All2_All2_trans; tea.
    + apply eq_mfix_fix_context_marks in e.
      rewrite e. assumption.
    + intros d (IHty & IHbo) d' d'' (Hnam & Hrarg & Hty & Hbo) (Hnam1 & Hrarg1 & Hty1 & Hbo1).
      repeat split; try etransitivity; eauto.
  Qed.

#[global]
Instance compare_term_trans {cf} pb Σ φ Γ : Transitive (compare_term pb Σ φ Γ).
Proof. apply compare_term_upto_univ_trans; tc. Qed.

#[global]
Polymorphic Instance compare_term_upto_univ_equiv Σ R isTermIrrel Γ
  (hR : RelationClasses.Equivalence (R Conv)) (hirrel : compatible_with_compare_term isTermIrrel)
  : Equivalence (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ).
Proof.
  constructor; tc.
Defined.

#[global]
Polymorphic Instance eq_context_equiv {cf} Σ φ Γ0 : Equivalence (eq_context_gen (fun pb : conv_pb => compare_term pb Σ φ) Conv Γ0).
Proof.
  constructor; tc.
Qed.

#[global]
Polymorphic Instance leq_context_preord {cf} Σ φ Γ0 : PreOrder (eq_context_gen (fun pb : conv_pb => compare_term pb Σ φ) Conv Γ0).
Proof.
  constructor; try exact _.
Qed.

#[global]
Polymorphic Instance compare_term_preord {cf} pb Σ φ Γ :
  PreOrder (compare_term pb Σ φ Γ).
Proof.
  constructor;tc.
Qed.

#[global]
Polymorphic Instance eq_term_equiv {cf:checker_flags} Σ φ Γ : Equivalence (eq_term Σ φ Γ).
Proof. split; tc. Qed.

#[global]
Polymorphic Instance leq_term_preorder {cf:checker_flags} Σ φ Γ : PreOrder (leq_term Σ φ Γ).
Proof. tc. Qed. 

#[global]
Instance R_universe_instance_equiv R (hR : RelationClasses.Equivalence R)
  : RelationClasses.Equivalence (R_universe_instance R).
Proof.
  split; tc.
Qed.

Lemma R_universe_instance_antisym Re Rle (hRe : RelationClasses.Equivalence Re) :
  RelationClasses.Antisymmetric _ Re Rle ->
  RelationClasses.Antisymmetric _ (R_universe_instance Re) (R_universe_instance Rle).
Proof.
  intros H x y H1 H2.
  eapply Forall2_sym in H2.
  eapply Forall2_impl; [eapply Forall2_and|]; [exact H1|exact H2|].
  cbn; intros ? ? [? ?]. eapply H; assumption.
Qed.

#[global]
Instance R_global_instance_equiv Σ R (hR : RelationClasses.Equivalence (R Conv)) gr napp
  : RelationClasses.Equivalence (R_global_instance Σ R Conv gr napp).
Proof.
  split; tc.
Qed.

#[global]
Instance R_global_instance_antisym Σ R pb (hRe : RelationClasses.Equivalence (R Conv)) gr napp :
  RelationClasses.Antisymmetric _ (R Conv) (R pb) ->
  RelationClasses.Antisymmetric _ (R_global_instance Σ R Conv gr napp) (R_global_instance Σ R pb gr napp).
Proof.
  intros hR u v.
  unfold R_global_instance, R_opt_variance.
  destruct global_variance; auto.
  induction u in l, v |- *; destruct v, l; simpl; auto.
  intros [at' uv] [ta vu]. split; auto.
  destruct t0; simpl in *; auto.
Qed.  

Lemma eq_term_upto_univ_antisym Σ R pb Γ (hRe : RelationClasses.Equivalence (R Conv)) :
  RelationClasses.Antisymmetric _ (R Conv) (R pb) ->
  Antisymmetric (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) (compare_term_upto_univ_rel Σ R isTermIrrel pb Γ).
Proof.
  intros hR u v. generalize 0; intros n h h'.
  induction u in v, n, h, h', Γ |- * using term_forall_list_ind.
  all: simpl ; inversion h ; subst; try solve [ constructor; auto ].
  all: simpl ; inversion h'; subst; try solve [ constructor; auto ].
  all: try solve [ constructor ; eapply RelationClasses.antisymmetry ; eauto ].
  - rewrite -H3 in X2. constructor; auto.
  - rewrite -H3 in X2. constructor; auto.
  - rewrite -H4 in X4. constructor; auto.
Qed.

#[global]
Instance leq_term_antisym {cf:checker_flags} Σ φ Γ
  : Antisymmetric (eq_term Σ φ Γ) (leq_term Σ φ Γ).
Proof.
  eapply eq_term_upto_univ_antisym; exact _.
Qed.

#[global]
Instance leq_term_partial_order {cf:checker_flags} Σ φ Γ
  : PartialOrder (eq_term Σ φ Γ) (leq_term Σ φ Γ).
Proof.
  split. intros eqxy; split; now eapply eq_term_leq_term.
  intros [xy yx].
  now eapply leq_term_antisym.
Qed.

#[global]
Hint Constructors compare_decls : pcuic.

Local Ltac lih :=
  lazymatch goal with
  | ih : forall pb n n' k v, compare_term_upto_univ_napp_rel _ _ _ _ _ _ ?u _ -> _
    |- compare_term_upto_univ_rel _ _ _ _ _ (lift _ _ ?u) _ =>
    eapply compare_term_upto_univ_NoTermIrrel_ctx; eapply ih; try eapply compare_term_upto_univ_NoTermIrrel_ctx
  end.

Lemma eq_term_upto_univ_lift Σ R pb n n' Γ k :
  Proper (compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb n' Γ ==> compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb n' Γ) (lift n k).
Proof.
  intros u v e.
  induction u in n', v, n, k, e, pb |- * using term_forall_list_ind.
  all: dependent destruction e => //.
  all: try solve [cbn ; constructor ; try lih ; try assumption; solve_all].
  - cbn. destruct e as (? & ? & e & ?).
    constructor; unfold eq_predicate, eq_branches, eq_branch in *; simpl; !!solve_all.
    * rewrite -?(All2_fold_length e). lih. tea.
    * rewrite (All2_fold_length a0). lih. tea.
  - cbn. constructor. unfold eq_mfix in *.
    pose proof (All2_length e).
    solve_all. rewrite H. lih. eauto.
  - cbn. constructor. unfold eq_mfix in *.
    pose proof (All2_length e).
    solve_all. rewrite H. lih. eauto.
Qed.

(* Lemma lift_compare_term `{checker_flags} pb Σ ϕ n k t t' :
  compare_term pb Σ ϕ t t' -> compare_term pb Σ ϕ (lift n k t) (lift n k t').
Proof.
  now apply eq_term_upto_univ_lift.
Qed.

Lemma lift_compare_decls `{checker_flags} pb Σ ϕ n k d d' :
  compare_decl pb Σ ϕ d d' -> compare_decl pb Σ ϕ (lift_decl n k d) (lift_decl n k d').
Proof.
  intros []; constructor; cbn; intuition auto using lift_compare_term.
Qed.

Lemma lift_compare_context `{checker_flags} pb Σ φ l l' n k :
  compare_context pb Σ φ l l' ->
  compare_context pb Σ φ (lift_context n k l) (lift_context n k l').
Proof.
  unfold compare_context.
  induction 1; rewrite -> ?lift_context_snoc0. constructor.
  constructor; auto. 
  eapply lift_compare_decls in p.
  now rewrite (All2_fold_length X).
Qed.

Lemma lift_eq_term {cf:checker_flags} Σ φ n k T U :
  eq_term Σ φ T U -> eq_term Σ φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_lift.
Qed.

Lemma lift_leq_term {cf:checker_flags} Σ φ n k T U :
  leq_term Σ φ T U -> leq_term Σ φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_lift.
Qed. *)

Local Ltac sih :=
  lazymatch goal with
  | ih : forall pb n n' k v, compare_term_upto_univ_napp_rel _ _ _ _ _ _ ?u _ -> _ -> _
    |- compare_term_upto_univ_rel _ _ _ _ _ (subst _ _ ?u) _ => eapply ih
  end.

(* Lemma eq_term_upto_univ_substs Σ R isTermIrrel pb napp :
  RelationClasses.subrelation (R Conv) (R pb) ->
  forall Γ Δ u v n l l',
    True ->
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ u v ->
    All2 (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) l l' ->
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Δ (subst l n u) (subst l' n v).
Proof.
  unfold RelationClasses.subrelation; intros hR Γ Δ u v n l l' hs hu hl.
  induction u in napp, Γ, Δ, v, n, l, l', hu, hl, pb, hR |- * using term_forall_list_ind.
  all: dependent destruction hu.
  all: try solve [ cbn ; constructor ; try sih ; eauto ].
  - cbn. destruct (Nat.leb_spec0 n n0).
    + case_eq (nth_error l (n0 - n)).
      * intros t e. eapply All2_nth_error_Some in e as h ; eauto.
        destruct h as [t' [e' h]].
        rewrite e'.
        eapply eq_term_upto_univ_lift.
        eapply eq_term_upto_univ_leq. 3:eauto. all:auto with arith.  
      * intros h. eapply All2_nth_error_None in h as hh ; eauto.
        rewrite hh.
        apply All2_length in hl as e. rewrite <- e.
        constructor.
    + constructor.
  - cbn. constructor. solve_all.
  - cbn.
    destruct e as (? & ? & e & ?).
    constructor ; unfold eq_predicate, eq_branches, eq_branch in *; simpl; try sih ; solve_all.
    * rewrite -(All2_fold_length e). eapply e2; eauto.
    * rewrite (All2_fold_length a0). now eapply b0.
  - cbn. constructor ; unfold eq_mfix in *; try sih ; eauto.
    pose proof (All2_length e).
    solve_all. now rewrite H.
  - cbn. constructor ; unfold eq_mfix in *; try sih ; eauto.
    pose proof (All2_length e).
    solve_all. now rewrite H.
Qed.

Lemma eq_term_upto_univ_subst Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n x y,
    compare_term_upto_univ Σ R pb u v ->
    eq_term_upto_univ Σ Re Re x y ->
    compare_term_upto_univ Σ R pb (u{n := x}) (v{n := y}).
Proof.
  intros hR u v n x y e1 e2.
  eapply eq_term_upto_univ_substs; eauto.
Qed.

Lemma subst_eq_term {cf:checker_flags} Σ φ l k T U :
  eq_term Σ φ T U ->
  eq_term Σ φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_substs; try easy.
  now eapply All2_same.
Qed.

Lemma subst_leq_term {cf:checker_flags} Σ φ l k T U :
  leq_term Σ φ T U ->
  leq_term Σ φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_substs; try easy.
  intro; apply eq_universe_leq_universe.
  now eapply All2_same.
Qed. *)

(** ** Behavior on mkApps and it_mkLambda_or_LetIn **  *)

Lemma compare_term_compare_term_napp Σ R isTermIrrel pb napp Γ t t' :
  RelationClasses.subrelation (R Conv) (R pb) ->
  compare_term_upto_univ_rel Σ R isTermIrrel pb Γ t t' -> 
  compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ t t'.
Proof.
  intros. eapply compare_term_upto_univ_impl. 6:eauto. 5: auto.
  4:auto with arith. all:typeclasses eauto.
Qed.

Lemma compare_term_upto_univ_napp_rel_mkApps Σ R isTermIrrel pb u1 l1 u2 l2 napp Γ :
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb (#|l1| + napp) Γ u1 u2 ->
    All2 (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) l1 l2 ->
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros hu hl. induction l1 in napp, u1, u2, l2, hu, hl, Γ |- *.
  - inversion hl. subst. assumption.
  - inversion hl. subst. simpl.
    eapply IHl1.
    + constructor. all: assumption.
    + assumption.
Qed.


Lemma compare_term_upto_univ_napp_rel_mkApps_l_inv_rel Σ R pb napp Γ u l t :
    isTermRelevant Σ Γ u ->
    All (wfTermRel Σ Γ) l ->
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ (mkApps u l) t ->
    ∑ u' l',
      compare_term_upto_univ_napp_rel Σ R isTermIrrel pb (#|l| + napp) Γ u u' *
      All2 (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) l l' *
      (t = mkApps u' l').
Proof.
  intros Hrel Hrelargs h.
  eapply isTermRel_mkApps in Hrel as Hrell; tea.
  induction l in napp, u, Hrel, Hrell, t, h, pb, Γ |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h.
    assert (isTermRel Σ Γ (tApp u a) Relevant).
    { apply isTermRel_mkApps_inv in Hrell as (_ & H). inv H. destruct X; now econstructor. }
    apply IHl in h as [u' [l' [[h1 h2] h3]]]; tea.
    dependent destruction h1.
    2: { eapply isTermRel_inj in i. 2: apply X. inv i. }
    subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma compare_term_upto_univ_napp_rel_mkApps_r_inv_rel Σ R pb napp Γ u l t :
    isTermRelevant Σ Γ u ->
    All (wfTermRel Σ Γ) l ->
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ t (mkApps u l) ->
    ∑ u' l',
      compare_term_upto_univ_napp_rel Σ R isTermIrrel pb (#|l| + napp) Γ u' u *
      All2 (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) l' l *
      (t = mkApps u' l').
Proof.
  intros Hrel Hrelargs h.
  eapply isTermRel_mkApps in Hrel as Hrell; tea.
  eapply eq_term_isTermRel_2 in Hrell as Hrelr; tea.
  induction l in napp, u, Hrel, Hrell, t, Hrelr, h, pb, Γ |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h.
    assert (isTermRel Σ Γ (tApp u a) Relevant).
    { apply isTermRel_mkApps_inv in Hrell as (_ & H). inv H. destruct X; now econstructor. }
    apply IHl in h as [u' [l' [[h1 h2] h3]]]; tea.
    dependent destruction h1.
    2: { eapply isTermRel_inj in i0. 2: apply X. inv i0. }
    subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma compare_term_upto_univ_mkApps_l_inv_rel Σ R pb Γ u l t :
    isTermRelevant Σ Γ u ->
    All (wfTermRel Σ Γ) l ->
    compare_term_upto_univ_rel Σ R isTermIrrel pb Γ (mkApps u l) t ->
    ∑ u' l',
      compare_term_upto_univ_napp_rel Σ R isTermIrrel pb #|l| Γ u u' *
      All2 (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) l l' *
      (t = mkApps u' l').
Proof.
  intros Hrel Hrelargs H; apply compare_term_upto_univ_napp_rel_mkApps_l_inv_rel in H; rewrite ?Nat.add_0_r in H; auto.
Qed.

Lemma compare_term_upto_univ_mkApps_r_inv_rel Σ R pb Γ u l t :
    isTermRelevant Σ Γ u ->
    All (wfTermRel Σ Γ) l ->
    compare_term_upto_univ_rel Σ R isTermIrrel pb Γ t (mkApps u l) ->
    ∑ u' l',
      compare_term_upto_univ_napp_rel Σ R isTermIrrel pb #|l| Γ u' u *
      All2 (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) l' l *
      (t = mkApps u' l').
Proof.
  intros Hrel Hrelargs H; apply compare_term_upto_univ_napp_rel_mkApps_r_inv_rel in H;
    rewrite ?Nat.add_0_r in H; auto.
Qed.

Lemma compare_term_upto_univ_isApp_rel Σ R pb napp Γ u v :
  isTermRelevant Σ Γ u ->
  compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ u v ->
  isApp u = isApp v.
Proof.
  intro.
  induction 1 => //.
  apply isTermRel_inj with (1 := i) in X => //.
Qed.

Lemma compare_term_upto_univ_mkApps_inv_rel Σ R pb Γ u l u' l' :
  isTermRelevant Σ Γ u ->
  All (wfTermRel Σ Γ) l ->
  isApp u = false ->
  isApp u' = false ->
  compare_term_upto_univ_rel Σ R isTermIrrel pb Γ (mkApps u l) (mkApps u' l') ->
  compare_term_upto_univ_napp_rel Σ R isTermIrrel pb #|l| Γ u u' * All2 (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) l l'.
Proof.
  intros hrel hrelargs hu hu' h.
  apply compare_term_upto_univ_mkApps_l_inv_rel in h as hh => //.
  destruct hh as [v [args [[h1 h2] h3]]].
  apply compare_term_upto_univ_isApp_rel in h1 as hh1 => //. rewrite hu in hh1.
  apply mkApps_notApp_inj in h3 ; auto.
  destruct h3 as [? ?]. subst. split ; auto.
Qed.


Lemma compare_term_upto_univ_napp_rel_mkApps_l_inv Σ R pb napp Γ u l t :
    compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb napp Γ (mkApps u l) t ->
    ∑ u' l',
      compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb (#|l| + napp) Γ u u' *
      All2 (compare_term_upto_univ_rel Σ R NoTermIrrel Conv Γ) l l' *
      (t = mkApps u' l').
Proof.
  intros h. induction l in napp, u, t, h, pb, Γ |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1 => //. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma compare_term_upto_univ_napp_rel_mkApps_r_inv Σ R pb napp Γ u l t :
    compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb napp Γ t (mkApps u l) ->
    ∑ u' l',
      compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb (#|l| + napp) Γ u' u *
      All2 (compare_term_upto_univ_rel Σ R NoTermIrrel Conv Γ) l' l *
      (t = mkApps u' l').
Proof.
  intros h. induction l in napp, u, t, h, pb, Γ |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1 => //. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma compare_term_upto_univ_mkApps Σ R isTermIrrel pb Γ u1 l1 u2 l2 :
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb #|l1| Γ u1 u2 ->
    All2 (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) l1 l2 ->
    compare_term_upto_univ_rel Σ R isTermIrrel pb Γ (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros; apply compare_term_upto_univ_napp_rel_mkApps; rewrite ?Nat.add_0_r; auto.
Qed.

Lemma compare_term_upto_univ_mkApps_l_inv Σ R pb Γ u l t :
    compare_term_upto_univ_rel Σ R NoTermIrrel pb Γ (mkApps u l) t ->
    ∑ u' l',
      compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb #|l| Γ u u' *
      All2 (compare_term_upto_univ_rel Σ R NoTermIrrel Conv Γ) l l' *
      (t = mkApps u' l').
Proof.
  intros H; apply compare_term_upto_univ_napp_rel_mkApps_l_inv in H; rewrite ?Nat.add_0_r in H; auto.
Qed.

Lemma compare_term_upto_univ_mkApps_r_inv Σ R pb Γ u l t :
    compare_term_upto_univ_rel Σ R NoTermIrrel pb Γ t (mkApps u l) ->
    ∑ u' l',
      compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb #|l| Γ u' u *
      All2 (compare_term_upto_univ_rel Σ R NoTermIrrel Conv Γ) l' l *
      (t = mkApps u' l').
Proof.
  intros H; apply compare_term_upto_univ_napp_rel_mkApps_r_inv in H;
    rewrite Nat.add_0_r in H; auto.
Qed.

Lemma compare_term_upto_univ_isApp Σ R pb napp Γ u v :
  compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb napp Γ u v ->
  isApp u = isApp v.
Proof.
  induction 1 => //.
  all: reflexivity.
Qed.

Lemma compare_term_upto_univ_mkApps_inv Σ R pb Γ u l u' l' :
  isApp u = false ->
  isApp u' = false ->
  compare_term_upto_univ_rel Σ R NoTermIrrel pb Γ (mkApps u l) (mkApps u' l') ->
  compare_term_upto_univ_napp_rel Σ R NoTermIrrel pb #|l| Γ u u' * All2 (compare_term_upto_univ_rel Σ R NoTermIrrel Conv Γ) l l'.
Proof.
  intros hu hu' h.
  apply compare_term_upto_univ_mkApps_l_inv in h as hh.
  destruct hh as [v [args [[h1 h2] h3]]].
  apply compare_term_upto_univ_isApp in h1 as hh1. rewrite hu in hh1.
  apply mkApps_notApp_inj in h3 ; auto.
  destruct h3 as [? ?]. subst. split ; auto.
Qed.

Lemma compare_term_upto_univ_it_mkLambda_or_LetIn Σ R pb Γ :
  RelationClasses.Reflexive (R Conv) ->
  Proper (eq_context_upto Σ R NoTermIrrel Conv Γ ==> compare_term_upto_univ_rel Σ R NoTermIrrel pb Γ ==> compare_term_upto_univ_rel Σ R NoTermIrrel pb Γ) it_mkLambda_or_LetIn.
Proof.
  intros he Γ' Δ' eq u v h.
  induction eq in u, v, h, he |- *.
  - assumption.
  - simpl. cbn. apply IHeq => //.
    destruct p; cbn; constructor ; tas; try reflexivity. all: now eapply compare_term_upto_univ_NoTermIrrel_ctx.
Qed.

Lemma compare_term_upto_univ_it_mkLambda_or_LetIn_r Σ R isTermIrrel pb Γ Δ :
  RelationClasses.Reflexive (R Conv) ->
  respectful (compare_term_upto_univ_rel Σ R isTermIrrel pb (Γ ,,, marks_of_context Δ)) (compare_term_upto_univ_rel Σ R isTermIrrel pb Γ)
            (it_mkLambda_or_LetIn Δ) (it_mkLambda_or_LetIn Δ).
Proof.
  intros he u v h.
  induction Δ as [| [na [b|] A] Δ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try reflexivity.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try reflexivity.
    all: auto.
Qed.

Lemma compare_term_it_mkLambda_or_LetIn {cf:checker_flags} Σ pb φ Γ Δ :
  respectful (compare_term pb Σ φ (Γ ,,, marks_of_context Δ)) (compare_term pb Σ φ Γ)
            (it_mkLambda_or_LetIn Δ) (it_mkLambda_or_LetIn Δ).
Proof.
  apply compare_term_upto_univ_it_mkLambda_or_LetIn_r; exact _.
Qed.

Lemma compare_term_upto_univ_it_mkProd_or_LetIn Σ R isTermIrrel pb Γ Δ :
  RelationClasses.Reflexive (R Conv) ->
  respectful (compare_term_upto_univ_rel Σ R isTermIrrel pb (Γ ,,, marks_of_context Δ)) (compare_term_upto_univ_rel Σ R isTermIrrel pb Γ)
            (it_mkProd_or_LetIn Δ) (it_mkProd_or_LetIn Δ).
Proof.
  intros he u v h.
  induction Δ as [| [na [b|] A] Δ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try reflexivity.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try reflexivity.
    all: auto.
Qed.

Lemma compare_term_it_mkProd_or_LetIn {cf:checker_flags} Σ pb φ Γ Δ :
  respectful (compare_term pb Σ φ (Γ ,,, marks_of_context Δ)) (compare_term pb Σ φ Γ)
            (it_mkProd_or_LetIn Δ) (it_mkProd_or_LetIn Δ).
Proof.
  eapply compare_term_upto_univ_it_mkProd_or_LetIn ; exact _.
Qed.

Lemma compare_term_it_mkLambda_or_LetIn_inv {cf:checker_flags} Σ pb φ Γ Δ u v :
    compare_term Σ pb φ Γ (it_mkLambda_or_LetIn Δ u) (it_mkLambda_or_LetIn Δ v) ->
    compare_term Σ pb φ (Γ ,,, marks_of_context Δ) u v.
Proof.
  revert u v. induction Δ as [| [na [b|] A] Δ ih ] ; intros u v h.
  - assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
    inv X. inv X0. constructor => //.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
    inv X. inv X0. constructor => //.
Qed.

Lemma R_universe_instance_eq {u u'} : R_universe_instance eq u u' -> u = u'.
Proof.
  intros H.
  apply Forall2_eq in H. apply map_inj in H ; revgoals.
  { apply Universe.make_inj. }
  subst. constructor ; auto.
Qed.

Lemma valid_constraints_empty {cf} i : 
  valid_constraints (empty_ext empty_global_env) (subst_instance_cstrs i (empty_ext empty_global_env)).
Proof.
  red. destruct check_univs => //.
Qed.

(** ** Syntactic ws_cumul_pb up to printing anotations ** *)

Notation StrictUnivEq := (fun (_ : conv_pb) => @eq Universe.t).
Notation upto_names := (compare_term_upto_univ_rel empty_global_env StrictUnivEq NoTermIrrel Conv []).
Notation ctx_upto_names := (eq_context_upto empty_global_env StrictUnivEq NoTermIrrel Conv []).

Notation "`≡α`" := upto_names.
Infix "≡α" := upto_names (at level 60).
Notation "`≡Γ`" := ctx_upto_names.
Infix "≡Γ" := ctx_upto_names (at level 20, no associativity).

#[global]
Instance upto_names_ref : Reflexive upto_names.
Proof.
  tc.
Qed.

#[global]
Instance upto_names_sym : Symmetric upto_names.
Proof.
  tc.
Qed.

#[global]
Instance upto_names_trans : Transitive upto_names.
Proof.
  eapply compare_term_upto_univ_trans; tc.
  intros Σ **; split => //.
Qed.

(* todo: rename *)
(* Definition nleq_term t t' := *)
(*   eqb_term_upto_univ eqb eqb t t'. *)

(* Corollary reflect_upto_names : *)
(*   forall t t', reflectT (upto_names t t') (nleq_term t t'). *)
(* Proof. *)
(*   intros t t'. eapply reflect_eq_term_upto_univ. *)
(*   all: intros u u'; eapply reflect_reflectT, eqb_spec. *)
(* Qed. *)

Lemma upto_names_impl Σ R isTermIrrel pb Γ :
  RelationClasses.Reflexive (R Conv) ->
  RelationClasses.Reflexive (R pb) ->
  subrelation upto_names (compare_term_upto_univ_rel Σ R isTermIrrel pb Γ).
Proof.
  intros he hle. eapply compare_term_upto_univ_empty_impl; auto.
  all: intros ? ? []; eauto.
Qed.

Lemma upto_names_impl_compare_term {cf:checker_flags} Σ φ pb Γ u v :
    u ≡α v -> compare_term Σ φ pb Γ u v.
Proof.
  eapply upto_names_impl ; exact _.
Qed.

Lemma upto_names_impl_eq_term {cf:checker_flags} Σ φ Γ u v :
    u ≡α v -> eq_term Σ φ Γ u v.
Proof. eapply upto_names_impl_compare_term. Qed.

Lemma upto_names_impl_leq_term {cf:checker_flags} Σ φ Γ u v :
    u ≡α v -> leq_term Σ φ Γ u v.
Proof. eapply upto_names_impl_compare_term. Qed.

(** ** ws_cumul_pb on contexts ** *)

Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
| rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
| rel_none : rel_option R None None.

Derive Signature NoConfusion for rel_option.

Definition compare_decl_upto_gen Σ R isTermIrrel pb Γ d d' : Type :=
  eq_binder_annot d.(decl_name) d'.(decl_name) *
  rel_option (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) d.(decl_body) d'.(decl_body) *
  compare_term_upto_univ_rel Σ R isTermIrrel pb Γ d.(decl_type) d'.(decl_type).

(* TODO perhaps should be def *)
Lemma All2_eq_context_upto Σ R isTermIrrel pb Γ0:
  subrelation (All2_fold (fun Γ _ => (compare_decl_upto_gen Σ R isTermIrrel pb (Γ0 ,,, marks_of_context Γ)))) (eq_context_upto Σ R isTermIrrel pb Γ0).
Proof.
  intros Γ Δ h.
  induction h.
  - constructor.
  - destruct p as [[h1 h2] h3].
    destruct d as [na bo ty], d' as [na' bo' ty'].
    simpl in h1, h2.
    destruct h2.
    + constructor ; eauto. constructor; auto.
    + constructor ; eauto. constructor; auto.
Qed.

Lemma eq_context_upto_refl Σ R isTermIrrel pb Γ0 :
  RelationClasses.Reflexive (R Conv) ->
  RelationClasses.Reflexive (R pb) ->
  Reflexive (eq_context_upto Σ R isTermIrrel pb Γ0).
Proof. exact _. Qed.

Lemma eq_context_upto_sym Σ R isTermIrrel pb Γ0 :
  RelationClasses.Symmetric (R Conv) ->
  RelationClasses.Symmetric (R pb) ->
  Symmetric (eq_context_upto Σ R isTermIrrel pb Γ0).
Proof. exact _. Qed.

Lemma eq_context_upto_cat Σ R isTermIrrel pb Γ0 Γ Δ Γ' Δ' :
  eq_context_upto Σ R isTermIrrel pb Γ0 Γ Γ' ->
  eq_context_upto Σ R isTermIrrel pb (Γ0 ,,, marks_of_context Γ) Δ Δ' ->
  eq_context_upto Σ R isTermIrrel pb Γ0 (Γ ,,, Δ) (Γ' ,,, Δ').
Proof.
  intros. eapply All2_fold_app; eauto.
  eapply All2_fold_impl with (1 := X0) => γ γ' d d' H.
  unfold All_over. rewrite /marks_of_context map_app app_context_assoc. apply H.
Qed.

Lemma eq_context_upto_rev Σ R pb Γ0 Γ Δ :
  eq_context_upto Σ R NoTermIrrel pb Γ0 Γ Δ ->
  eq_context_upto Σ R NoTermIrrel pb Γ0 (rev Γ) (rev Δ).
Proof.
  induction 1.
  - constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    2: { apply All2_fold_impl with (1 := IHX) => ???? H. depelim H => //=; constructor => //; eapply compare_term_upto_univ_NoTermIrrel_ctx; tea. }
    constructor. constructor.
    depelim p => //=; constructor => //; eapply compare_term_upto_univ_NoTermIrrel_ctx; tea.
Qed.

Lemma eq_context_upto_rev' :
  forall Σ Γ Δ R pb Γ0,
    eq_context_upto Σ R NoTermIrrel pb Γ0 Γ Δ ->
    eq_context_upto Σ R NoTermIrrel pb Γ0 (List.rev Γ) (List.rev Δ).
Proof.
  intros Σ Γ Δ R pb Γ0 h.
  induction h.
  - constructor.
  - simpl. eapply eq_context_upto_cat.
    + repeat constructor. depelim p => //=; constructor => //; eapply compare_term_upto_univ_NoTermIrrel_ctx; tea.
    + apply All2_fold_impl with (1 := IHh) => ???? H. depelim H => //=; constructor => //; eapply compare_term_upto_univ_NoTermIrrel_ctx; tea.
Qed.

Lemma eq_context_upto_length :
  forall {Σ R isTermIrrel pb Γ0 Γ Δ},
    eq_context_upto Σ R isTermIrrel pb Γ0 Γ Δ ->
    #|Γ| = #|Δ|.
Proof.
  intros Σ R isTermIrrel pb Γ0 Γ Δ h.
  apply All2_fold_length in h => //.
Qed.

(* Lemma eq_context_upto_subst_context Σ R isTermIrrel pb Γ :
  RelationClasses.subrelation (R Conv) (R pb) ->
  forall u v n l l',
    eq_context_upto Σ R isTermIrrel pb Γ u v ->
    All2 (compare_term_upto_univ_rel Σ R isTermIrrel Conv Γ) l l' ->
    eq_context_upto Σ R isTermIrrel pb Γ (subst_context l n u) (subst_context l' n v).
Proof.
  intros re u v n l l'.
  induction 1; intros Hl.
  - rewrite !subst_context_nil. constructor.
  - rewrite !subst_context_snoc; constructor; eauto.
    depelim p; constructor; simpl; intuition auto;
    rewrite -(length_of X);
    apply eq_term_upto_univ_substs; auto. reflexivity.
Qed. *)

#[global]
Hint Resolve All2_fold_nil : pcuic.

(* Lemma eq_context_upto_smash_context Σ ctx ctx' x y :
  eq_context_upto Σ eq eq ctx ctx' -> eq_context_upto Σ eq eq x y -> 
  eq_context_upto Σ eq eq (smash_context ctx x) (smash_context ctx' y).
Proof.
  induction x in ctx, ctx', y |- *; intros eqctx eqt; inv eqt; simpl; 
    try split; auto; try constructor; auto. depelim X0 => /=.
  - apply IHx; auto. apply eq_context_upto_cat; auto.
    constructor; pcuic.
  - apply IHx; auto. eapply eq_context_upto_subst_context; eauto.
    typeclasses eauto.
Qed. *)

(* Lemma eq_context_upto_nth_error Σ R isTermIrrel pb Γ0 ctx ctx' n :
  eq_context_upto Σ R isTermIrrel pb Γ0 ctx ctx' -> 
  rel_option (compare_decl_upto_gen Σ R isTermIrrel pb (Γ0 ,,, marks_of_context (firstn (#|ctx| - n) ctx))) (nth_error ctx n) (nth_error ctx' n).
Proof.
  induction 1 in n |- *.
  - rewrite nth_error_nil. constructor.
  - destruct n; simpl; auto. 
    constructor. depelim p; constructor; intuition auto;
    now constructor.
Qed. *)

Lemma eq_context_impl Σ R R' pb Γ0:
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R Conv) (R' pb) ->
  RelationClasses.subrelation (R pb) (R' pb) ->
  subrelation (eq_context_upto Σ R isTermIrrel pb Γ0) (eq_context_upto Σ R' isTermIrrel pb Γ0).
Proof.
  intros hR hReR' hR' Γ Δ h.
  induction h.
  - constructor.
  - constructor; auto. 
    depelim p; constructor; auto.
    all:eapply compare_term_upto_univ_impl. 6,12,18:tea. all:eauto.
Qed.

Lemma isLambda_compare_term_l Σ R pb Γ u v :
    isLambda u ->
    compare_term_upto_univ_rel Σ R NoTermIrrel pb Γ u v ->
    isLambda v.
Proof.
  intros h e.
  destruct u; try discriminate.
  depelim e => //.
Qed.

Lemma isLambda_eq_term_r Σ R pb Γ u v :
    isLambda v ->
    compare_term_upto_univ_rel Σ R NoTermIrrel pb Γ u v ->
    isLambda u.
Proof.
  intros h e.
  destruct v ; try discriminate.
  depelim e => //.
Qed.

Lemma isConstruct_app_eq_term_l Σ R pb Γ u v :
    isConstruct_app u ->
    compare_term_upto_univ_rel Σ R NoTermIrrel pb Γ u v ->
    isConstruct_app v.
Proof.
  intros h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e1 in h. cbn in h.
  rewrite e2. cbn.
  destruct t1 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply compare_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1 => //.
  - reflexivity.
  - eapply decompose_app_notApp. eassumption.
Qed.

Lemma isConstruct_app_eq_term_r Σ R pb Γ u v :
    isConstruct_app v ->
    compare_term_upto_univ_rel Σ R NoTermIrrel pb Γ u v ->
    isConstruct_app u.
Proof.
  intros h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e2 in h. cbn in h.
  rewrite e1. cbn.
  destruct t2 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply compare_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1 => //.
  - eapply decompose_app_notApp. eassumption.
  - reflexivity.
Qed.

Lemma R_global_instance_flip Σ gr napp (R R' : conv_pb -> Universe.t -> Universe.t -> Prop) pb pb' u v:
  RelationClasses.Reflexive (R Conv) ->
  RelationClasses.Reflexive (R pb) ->
  RelationClasses.Symmetric (R' Conv) ->
  RelationClasses.Transitive (R Conv) ->
  RelationClasses.Transitive (R pb) ->
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R Conv) (R pb') ->
  (forall x y, R pb x y -> R' pb' y x) ->
  R_global_instance Σ R pb gr napp u v ->
  R_global_instance Σ R' pb' gr napp v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans inclc inclp incl'.
  rewrite /R_global_instance /R_opt_variance.
  destruct global_variance as [vs|] eqn:var.  
  - induction u in vs, v |- *; destruct v; simpl; auto;
    destruct vs as [|v' vs]; simpl; auto.
    intros [Ra Ru']. split.
    destruct v'; simpl; auto.
    apply IHu; auto.
  - intros.
    apply Forall2_symP; eauto.
    eapply Forall2_impl; eauto.
Qed.

Lemma compare_term_upto_univ_napp_rel_flip Σ (R R' : conv_pb -> Universe.t -> Universe.t -> Prop) isTermIrrel pb pb' napp Γ u v :
  RelationClasses.Reflexive (R Conv) ->
  RelationClasses.Reflexive (R pb) ->
  RelationClasses.Symmetric (R' Conv) ->
  RelationClasses.Transitive (R Conv) ->
  RelationClasses.Transitive (R pb) ->
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R Conv) (R pb') ->
  (forall x y, R pb x y -> R' pb' y x) ->
  compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ u v ->
  compare_term_upto_univ_napp_rel Σ R' isTermIrrel pb' napp Γ v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans inclc inclp incl' H.
  induction H in Rlerefl, Rletrans, incl', H, Γ |- *.
  all: intros; constructor.
  all: intuition auto.
  all:try solve [symmetry ; eapply compare_term_upto_univ_impl ; [..|eassumption] ; auto ].
  all:try solve [symmetry ; eapply R_universe_instance_impl ; [..|eassumption] ; auto].
  all: try solve [now symmetry].
  all:eauto using R_global_instance_flip.
  - eapply All2_sym. solve_all.
    symmetry.
    eapply compare_term_upto_univ_impl ; [..|eassumption] ; auto with arith.
  - rewrite -e; eauto.
  - rewrite -e; eauto.
  - rewrite -e; eauto.
  - pose proof (eq_predicate_inst_case_predicate_context_marks e).
    unfold eq_predicate in * ; intuition auto.
    all: symmetry ; auto.
    + solve_all.
      now eapply compare_term_upto_univ_impl ; [..|eassumption].
    + now eapply R_universe_instance_impl ; [..|eassumption].
    + rewrite -H0.
      now eapply compare_term_upto_univ_impl ; [..|eassumption].
  - eapply All2_sym. eapply All2_impl with (1 := e0) => br br' e1.
    epose proof (eq_branch_inst_case_branch_context_marks (p' := p') e1).
    destruct e1; split.
    + now symmetry.
    + symmetry. rewrite -H0. now eapply compare_term_upto_univ_impl ; [..|eassumption].
  - eapply All2_sym. pose proof (eq_mfix_fix_context_marks e). unfold eq_mfix in e. solve_all.
    3: rewrite -H.
    all: symmetry ; auto.
    all: now eapply compare_term_upto_univ_impl ; [..|eassumption].
  - eapply All2_sym. pose proof (eq_mfix_fix_context_marks e). unfold eq_mfix in e. solve_all.
    3: rewrite -H.
    all: symmetry ; auto.
    all: now eapply compare_term_upto_univ_impl ; [..|eassumption].
Qed.

Lemma eq_univ_make u u' :
    Forall2 eq (map Universe.make u) (map Universe.make u') ->
    u = u'.
Proof.
  intros H. eapply Forall2_map' in H.
  eapply Forall2_eq. eapply Forall2_impl; tea.
  clear. intros [] [] H; now inversion H.
Qed.

(** ws_cumul_pb of binder annotations *)
Notation eq_annots Γ Δ :=
  (Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ Δ).

Lemma eq_context_gen_binder_annot R isTermIrrel pb Γ Δ : 
  eq_context_gen R isTermIrrel pb Γ Δ -> eq_annots (forget_types Γ) Δ.
Proof.
  induction 1; constructor; auto.
  destruct p; auto.
Qed.

Lemma eq_annots_fold (Γ : list aname) (f : nat -> term -> term) (Δ : context) : 
  eq_annots Γ (fold_context_k f Δ) <-> eq_annots Γ Δ.
Proof.
  induction Δ in Γ |- *.
  - cbn; auto. reflexivity.
  - rewrite fold_context_k_snoc0 /=.
    destruct Γ; split; intros H; depelim H; constructor; auto;
    now apply IHΔ.
Qed.

Lemma eq_annots_subst_context (Γ : list aname) s k (Δ : context) : 
  eq_annots Γ (subst_context s k Δ) <-> eq_annots Γ Δ.
Proof.
  apply eq_annots_fold.
Qed.

Lemma eq_annots_lift_context (Γ : list aname) n k (Δ : context) : 
  eq_annots Γ (lift_context n k Δ) <-> eq_annots Γ Δ.
Proof.
  apply eq_annots_fold.
Qed.

#[global]
Instance Forall2_ext {A B} :
  Proper (pointwise_relation A (pointwise_relation B iff) ==> eq ==> eq ==> iff) (@Forall2 A B).
Proof.
  intros f g Hfg ?? -> ?? ->.
  split; intro; eapply Forall2_impl; tea; apply Hfg.
Qed.

Lemma eq_annots_subst_instance_ctx (Γ : list aname) u (Δ : context) : 
  eq_annots Γ Δ@[u] <-> eq_annots Γ Δ.
Proof.
  etransitivity. eapply Forall2_map_right.
  eapply Forall2_ext; auto.
  intros x y; reflexivity.
Qed.

Lemma eq_annots_inst_case_context (Γ : list aname) pars puinst (ctx : context) :
  eq_annots Γ ctx <->
  eq_annots Γ (PCUICCases.inst_case_context pars puinst ctx).
Proof.
  etransitivity. symmetry; eapply (eq_annots_subst_instance_ctx _ puinst).
  etransitivity.
  symmetry; eapply (eq_annots_subst_context _ (List.rev pars) 0). 
  reflexivity.
Qed.

Lemma eq_annots_expand_lets_ctx (Γ : list aname) (Δ Δ' : context) :
  eq_annots Γ (expand_lets_ctx Δ Δ') <-> eq_annots Γ Δ'.
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  etransitivity. eapply eq_annots_subst_context.
  eapply eq_annots_lift_context.
Qed.

Lemma eq_annots_ind_predicate_context ind mdecl idecl (pctx : list aname) :
  eq_annots pctx (ind_predicate_context ind mdecl idecl) ->
  eq_annots pctx (idecl_binder idecl :: ind_indices idecl).
Proof.
  rewrite /ind_predicate_context.
  intros eq. depelim eq; cbn in *.
  constructor => //.
  now eapply eq_annots_expand_lets_ctx.
Qed.
