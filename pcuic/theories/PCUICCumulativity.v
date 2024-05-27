(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config BasicAst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICEquality PCUICUnivSubst
     PCUICReduction.

Set Default Goal Selector "!".

(** * Definition of cumulativity and conversion relations *)

Reserved Notation " Σ ;;; Γ |- t <=[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  |-  t  <=[ pb ] u").

Notation " Σ ;;; Γ ⊢ t <===[ pb ] u" := (compare_term Σ Σ Γ pb t u) (at level 50, Γ, t, u at next level).

(** ** Cumulativity *)

Inductive cumulAlgo_gen `{checker_flags} (Σ : global_env_ext) (Γ : context) (pb : conv_pb) : term -> term -> Type :=
| cumul_refl t u : Σ ;;; Γ ⊢ t <===[ pb ] u -> Σ ;;; Γ |- t <=[pb] u
| cumul_red_l t u v : Σ ;;; Γ |- t ⇝ v -> Σ ;;; Γ |- v <=[pb] u -> Σ ;;; Γ |- t <=[pb] u
| cumul_red_r t u v : Σ ;;; Γ |- t <=[pb] v -> Σ ;;; Γ |- u ⇝ v -> Σ ;;; Γ |- t <=[pb] u
where " Σ ;;; Γ |- t <=[ pb ] u " := (cumulAlgo_gen Σ Γ pb t u) : type_scope.

Notation " Σ ;;; Γ |- t = u " := (cumulAlgo_gen Σ Γ Conv t u) (at level 50, Γ, t, u at next level) : type_scope.
Notation " Σ ;;; Γ |- t <= u " := (cumulAlgo_gen Σ Γ Cumul t u) (at level 50, Γ, t, u at next level) : type_scope.

Notation cumulAlgo Σ Γ := (cumulAlgo_gen Σ Γ Cumul).
Notation convAlgo Σ Γ := (cumulAlgo_gen Σ Γ Conv).

#[global]
Hint Resolve cumul_refl : pcuic.

Include PCUICConversion.

Module PCUICConversionParAlgo <: EnvironmentTyping.ConversionParSig PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping.
  Definition cumul_gen := @cumulAlgo_gen.
End PCUICConversionParAlgo.

#[global]
Instance cumul_pb_decls_refl {cf:checker_flags} pb Σ Γ Γ' : Reflexive (cumul_pb_decls cumulAlgo_gen pb Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; reflexivity.
Qed.

#[global]
Instance conv_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (conv_decls cumulAlgo_gen Σ Γ Γ') := _.
#[global]
Instance cumul_decls_refl {cf:checker_flags} Σ Γ Γ' : Reflexive (cumul_decls cumulAlgo_gen Σ Γ Γ') := _.

Lemma cumul_alt `{cf : checker_flags} Σ Γ pb t u :
  Σ ;;; Γ |- t <=[pb] u <~> ∑ v v', red Σ Γ t v × red Σ Γ u v' × Σ ;;; Γ ⊢ v <===[ pb ] v'.
Proof.
  split.
  - induction 1.
    + exists t, u. intuition auto.
    + destruct IHX as (v' & v'' & redv & redv' & leqv).
      exists v', v''. intuition auto. now eapply red_step.
    + destruct IHX as (v' & v'' & redv & redv' & leqv).
      exists v', v''. intuition auto. now eapply red_step.
  - intros (v & v' & redv & redv' & Hleq).
    apply clos_rt_rt1n in redv.
    apply clos_rt_rt1n in redv'.
    induction redv.
    * induction redv'.
    ** constructor; auto.
    ** econstructor 3; eauto.
    * econstructor 2; eauto.
Qed.

#[global]
Instance cumul_refl' {cf:checker_flags} Σ Γ pb : Reflexive (cumulAlgo_gen Σ Γ pb).
Proof.
  intro; constructor; reflexivity.
Qed.

#[global]
Instance conv_refl' {cf:checker_flags} Σ Γ : Reflexive (convAlgo Σ Γ).
Proof.
  intro; constructor. reflexivity.
Qed.

Lemma red_cumul_pb `{cf : checker_flags} {Σ : global_env_ext} {pb} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- t <=[pb] u.
Proof.
  intros. apply clos_rt_rt1n in X.
  induction X.
  - reflexivity.
  - econstructor 2. all: eauto.
Qed.

Lemma red_cumul_pb_inv `{cf : checker_flags} {Σ : global_env_ext} {pb} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- u <=[pb] t.
Proof.
  intros. apply clos_rt_rt1n in X.
  induction X.
  - reflexivity.
  - econstructor 3. all: eauto.
Qed.

Lemma red_cumul_pb_cumul_pb `{cf : checker_flags} {Σ : global_env_ext} {pb} {Γ t u v} :
  red Σ Γ t u -> Σ ;;; Γ |- u <=[pb] v -> Σ ;;; Γ |- t <=[pb] v.
Proof.
  intros. apply clos_rt_rt1n in X.
  induction X. 1: auto.
  econstructor 2; eauto.
Qed.

Lemma red_cumul_pb_cumul_pb_inv `{cf : checker_flags} {Σ : global_env_ext} {pb} {Γ t u v} :
  red Σ Γ t v -> Σ ;;; Γ |- u <=[pb] v -> Σ ;;; Γ |- u <=[pb] t.
Proof.
  intros. apply clos_rt_rt1n in X.
  induction X. 1: auto.
  econstructor 3.
  - eapply IHX. eauto.
  - eauto.
Qed.

Lemma red_cumul `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- t <= u.
Proof.
  apply red_cumul_pb.
Qed.

Lemma red_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- u <= t.
Proof.
  apply red_cumul_pb_inv.
Qed.

Lemma red_cumul_cumul `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  red Σ Γ t u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t <= v.
Proof.
  apply red_cumul_pb_cumul_pb.
Qed.

Lemma red_cumul_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  red Σ Γ t v -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- u <= t.
Proof.
  apply red_cumul_pb_cumul_pb_inv.
Qed.

Lemma conv_cumul {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u -> Σ ;;; Γ |- t <= u.
Proof.
  induction 1.
  - constructor; now eapply eq_term_leq_term.
  - econstructor 2; eassumption.
  - econstructor 3; eassumption.
Qed.

Lemma red_conv {cf:checker_flags} (Σ : global_env_ext) Γ t u
  : red Σ Γ t u -> Σ ;;; Γ |- t = u.
Proof.
  apply red_cumul_pb.
Qed.

#[global]
Hint Resolve red_conv : core.

Lemma eq_term_eq_term_napp {cf:checker_flags} Σ ϕ Γ napp t t' :
  eq_term Σ ϕ Γ t t' ->
  eq_term_upto_univ_napp Σ (compare_universe ϕ) (compare_sort ϕ) Γ Conv napp t t'.
Proof.
  intros. eapply eq_term_upto_univ_impl. 6:eauto.
  5:auto with arith. all:typeclasses eauto.
Qed.

Lemma leq_term_leq_term_napp {cf:checker_flags} Σ ϕ Γ napp t t' :
  leq_term Σ ϕ Γ t t' ->
  eq_term_upto_univ_napp Σ (compare_universe ϕ) (compare_sort ϕ) Γ Cumul napp t t'.
Proof.
  intros. eapply eq_term_upto_univ_impl. 6:eauto.
  5:auto with arith. all:typeclasses eauto.
Qed.

Lemma eq_term_mkApps `{checker_flags} Σ φ Γ f l f' l' :
  eq_term Σ φ Γ f f' ->
  All2 (eq_term Σ φ Γ) l l' ->
  eq_term Σ φ Γ (mkApps f l) (mkApps f' l').
Proof.
  intros Hf Hargs.
  apply eq_term_upto_univ_napp_mkApps; tas.
  now apply eq_term_eq_term_napp.
Qed.

Lemma leq_term_mkApps `{checker_flags} Σ φ Γ f l f' l' :
  leq_term Σ φ Γ f f' ->
  All2 (eq_term Σ φ Γ) l l' ->
  leq_term Σ φ Γ (mkApps f l) (mkApps f' l').
Proof.
  intros Hf Hargs.
  apply eq_term_upto_univ_napp_mkApps; tas.
  now apply leq_term_leq_term_napp.
Qed.

#[global]
Hint Resolve cumul_refl' : core.

Lemma red_conv_conv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- u = v -> Σ ;;; Γ |- t = v.
Proof.
  apply red_cumul_pb_cumul_pb.
Qed.

Lemma red_conv_conv_inv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- v = t.
Proof.
  apply red_cumul_pb_cumul_pb_inv.
Qed.

Definition eq_termp_napp {cf:checker_flags} (Σ : global_env_ext) Γ (pb: conv_pb) napp :=
  compare_term_napp Σ Σ Γ pb napp.

Notation eq_termp Σ := (compare_term Σ Σ).

Lemma eq_term_eq_termp {cf:checker_flags} pb (Σ : global_env_ext) Γ x y :
  eq_term Σ Σ Γ x y ->
  eq_termp Σ Γ pb x y.
Proof.
  apply eq_term_compare_term.
Qed.

Lemma cumul_App_l {cf:checker_flags} :
  forall {Σ Γ f g x},
    Σ ;;; Γ |- f <= g ->
    Σ ;;; Γ |- tApp f x <= tApp g x.
Proof.
  intros Σ Γ f g x h.
  induction h.
  - eapply cumul_refl. constructor.
    + apply leq_term_leq_term_napp. assumption.
    + reflexivity.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
Qed.

Section ContextConversion.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).

  Notation conv_context Γ Γ' := (All2_fold (conv_decls cumulAlgo_gen Σ) Γ Γ').
  Notation cumul_context Γ Γ' := (All2_fold (cumul_decls cumulAlgo_gen Σ) Γ Γ').

  Global Instance conv_ctx_refl : Reflexive (All2_fold (conv_decls cumulAlgo_gen Σ)).
  Proof using Type.
    intro Γ; induction Γ; try econstructor; auto.
    destruct a as [na [b|] ty]; constructor; auto; pcuic; eapply conv_refl'.
  Qed.

  Global Instance cumul_ctx_refl : Reflexive (All2_fold (cumul_decls cumulAlgo_gen Σ)).
  Proof using Type.
    intro Γ; induction Γ; try econstructor; auto.
    destruct a as [na [b|] ty];
     econstructor; eauto; pcuic; try eapply conv_refl'; eapply cumul_refl'.
  Qed.

  Definition conv_ctx_refl' Γ : conv_context Γ Γ
  := conv_ctx_refl Γ.

  Definition cumul_ctx_refl' Γ : cumul_context Γ Γ
    := cumul_ctx_refl Γ.

End ContextConversion.
