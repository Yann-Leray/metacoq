(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config BasicAst Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICEquality
     PCUICLiftSubst PCUICUnivSubst PCUICCases PCUICClosed PCUICOnFreeVars PCUICCumulativitySpec PCUICTyping PCUICWeakeningTyp PCUICConversion.

Require Import ssreflect.
From Equations Require Import Equations.


Lemma weakening_cumulSpec `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ Γ' Γ'' pb A B :
  is_closed_context (Γ ,,, Γ') ->
  is_open_term (Γ ,,, Γ') A ->
  is_open_term (Γ ,,, Γ') B ->
  is_closed_context (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ' ⊢ A ≤s[pb] B ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' ⊢ lift #|Γ''| #|Γ'| A ≤s[pb] lift #|Γ''| #|Γ'| B.
Proof.
  intros ????.
  rewrite !PCUICSigmaCalculus.lift_rename.
  eapply (PCUICRenameTyp.cumulSpec_renameP) with (P := fun _ => false); eauto.
  - now apply PCUICWeakeningConv.weakening_renaming.
  - now eapply PCUICConversion.is_closed_context_lift.
Qed.

Section context_conversion.

Context {cf : checker_flags}.

Parameter P : forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (pb : conv_pb) (t t' : term), Type.

Parameter P_to_cumul : forall (Σ : global_env_ext) (Γ : context) (pb : conv_pb) (t t' : term), P Σ Γ pb t t' -> cumulSpec0 Σ Γ pb t t'.

Parameter Reflexive_P : forall (Σ : global_env_ext) (Γ : context) (pb : conv_pb) (t T : term), Σ ;;; Γ |- t : T -> P Σ Γ pb t t.

Lemma context_cumul_app Σ Γ Γ' Δ :
  cumul_context P Σ Γ' Γ ->
  wf_local Σ Γ' ->
  wf_local_rel Σ Γ' Δ ->
  cumul_context P Σ (Γ' ,,, Δ) (Γ ,,, Δ).
Proof.
  intros.
  eapply All2_fold_app => //.
  induction X1; repeat constructor; eauto; cbn.
  all: eapply Reflexive_P.
  { apply (t0).2.π2. }
  { apply t0. }
  { apply t0.2.π2. }
Qed.

Lemma context_cumulativity_wf_app Σ Γ Γ' Δ :
  cumul_context P Σ Γ' Γ ->
  wf_local Σ Γ' ->
  All_local_env (fun Γ j =>
    forall Γ' : context,
    cumul_context P Σ Γ' Γ -> wf_local Σ Γ' ->
    (lift_typing0 (fun t T => Σ;;; Γ' |- t : T)) j)
    (Γ,,, Δ) ->
  wf_local Σ (Γ' ,,, Δ).
Proof.
  intros.
  eapply All_local_env_app => //.
  eapply All_local_env_app_inv in X1 as [X1a X1].
  eapply All_local_env_impl_ind; tea => /=. clear Δ X1.
  intros Δ j H HT.
  eapply HT; clear j HT.
  - apply context_cumul_app; tas.
  - eapply All_local_env_app; auto.
Qed.

Lemma context_cumulativity_prop :
  env_prop
    (fun Σ Γ t T =>
       forall Γ', cumul_context P Σ Γ' Γ -> wf_local Σ Γ' -> Σ ;;; Γ' |- t : T)
    (fun Σ Γ j =>
       forall Γ', cumul_context P Σ Γ' Γ -> wf_local Σ Γ' -> lift_typing0 (fun t T => Σ ;;; Γ' |- t : T) j)
    (fun Σ Γ =>
    All_local_env (fun Γ j =>
       forall Γ' : context, cumul_context P Σ Γ' Γ -> wf_local Σ Γ' ->
       (lift_typing0 (fun t T => Σ;;; Γ' |- t : T) j)) Γ).
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; intros **; rename_all_hyps;
    try solve [econstructor; eauto].

  - apply lift_typing_impl with (1 := X) => ?? [_ IH].
    now apply IH.

  - assumption.

  - pose proof heq_nth_error.
    eapply (All2_fold_nth_r X0) in H as [d' [Hnth [Hrel Hconv]]].
    eapply All_local_env_nth_error in X; tea.
    red in X. specialize (X _ Hrel).
    forward X by now eapply All_local_env_skipn.
    destruct X as (_ & s & Hty & _).
    eapply type_Cumul with _ s.
    * econstructor. auto. eauto.
    * rewrite -(firstn_skipn (S n) Γ').
      change (tSort s) with (lift0 (S n) (tSort s)).
      eapply weakening_length. auto.
      rewrite firstn_length_le. eapply nth_error_Some_length in Hnth. lia. auto.
      now rewrite /app_context firstn_skipn.
      assumption.
    * replace (S n) with #|firstn (S n) Γ'|.
      2: { apply nth_error_Some_length in Hnth. rewrite firstn_length. lia. }
      rewrite -{1}(firstn_skipn (S n) Γ').
      eapply weakening_cumulSpec with (Γ' := []); simpl; eauto with fvs.
      + eapply All_local_env_nth_error in X1 as (_ & ? & Hty' & _); tea.
        now eapply PCUICClosedTyp.subject_closed, closedn_on_free_vars in Hty'.
      + now eapply PCUICClosedTyp.subject_closed, closedn_on_free_vars in Hty.
      + rewrite /app_context (firstn_skipn (S n) Γ'). fvs.
      + apply P_to_cumul.
        now destruct Hconv; cbn.

  - constructor; pcuic.
    specialize (forall_Γ' _ ltac:(tea) ltac:(tea)).
    eapply forall_Γ'0; constructor; pcuic.
    + constructor; eauto.
      eapply Reflexive_P. apply forall_Γ'.2.π2.
    + eapply lift_sorting_forget_univ. now eapply forall_Γ'.
  - econstructor; pcuic.
    eapply forall_Γ'0; repeat (constructor; pcuic).
    eapply Reflexive_P. apply (forall_Γ' _ ltac:(tea) ltac:(tea)).2.π2.
  - econstructor; pcuic.
    eapply forall_Γ'0; repeat (constructor; pcuic).
    { eapply Reflexive_P. apply (forall_Γ' _ ltac:(tea) ltac:(tea)). }
    { eapply Reflexive_P. apply (forall_Γ' _ ltac:(tea) ltac:(tea)).2.π2. }
  - econstructor; eauto. 2,3: constructor; eauto.
    * eapply IHp0. rewrite /predctx.
      eapply All2_fold_app => //.
      admit.
      eapply context_cumulativity_wf_app; tea.
    * eapply context_cumulativity_wf_app; tea.
    * revert X5.
      clear -Γ' X9 X10. induction 1; constructor; eauto. now destruct t0.
    * eapply All2i_impl; tea => i cdecl br. cbv beta.
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _). cbn.
      move=> [] hbctx [] ihbctxty [] [] hbody IHbody [] hbty IHbty.
      intuition eauto; solve_all.
      eapply context_cumulativity_wf_app; tea.
      eapply IHbody. apply context_cumul_app; tas. apply All_local_env_app_inv.
      eauto using context_cumulativity_wf_app.
      eauto using context_cumulativity_wf_app.
      eapply IHbty.
      apply context_cumul_app; tas. apply All_local_env_app_inv.
      eauto using context_cumulativity_wf_app.
      eapply context_cumulativity_wf_app; tea.
  - econstructor.
    all:pcuic.
    * admit.
    * eapply (All_impl X1).
      intros d Ht. now apply Ht.
    * eapply (All_impl X3).
      intros d Hb. apply Hb.
      1: apply context_cumul_app; tas. 1: apply All_local_env_app_inv.
      eapply (All_mfix_wf); auto.
      apply (All_impl X1); simpl.
      intros d' Ht. now apply Ht.
      eapply (All_mfix_wf); auto.
      apply (All_impl X1); simpl.
      intros d' Ht. now apply Ht.
  - econstructor.
    all:pcuic.
    * admit.
    * eapply (All_impl X1).
      intros d Ht. now apply Ht.
      * eapply (All_impl X3).
      intros d Hb. apply Hb.
      1: apply context_cumul_app; tas. 1: apply All_local_env_app_inv.
      eapply (All_mfix_wf); auto.
      apply (All_impl X1); simpl.
      intros d' Ht. now apply Ht.
      eapply (All_mfix_wf); auto.
      apply (All_impl X1); simpl.
      intros d' Ht. now apply Ht.
  - econstructor; tea.
    depelim X1; constructor; eauto. solve_all.
  - econstructor; eauto.

Qed.



End context_conversion.





























Local Unset Elimination Schemes.

Reserved Notation " Σ ;;; Γ ⊢ t ≤s[ pb ] u : T" (at level 50, Γ, t, u, T at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤s[ pb ]  u  :  T").

Inductive typedCumul (P : global_env_ext -> context -> term -> term -> sort -> Type)
  {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (pb : conv_pb) : term -> term -> term -> Type :=

(* transitivity *)

| typed_cumul_Trans : forall t u v T,
    Σ ;;; Γ ⊢ t ≤s[pb] u : T ->
    Σ ;;; Γ ⊢ u ≤s[pb] v : T ->
    Σ ;;; Γ ⊢ t ≤s[pb] v : T

(* symmetry *)

| typed_cumul_Sym : forall t u T,
    Σ ;;; Γ ⊢ t ≤s[Conv] u : T ->
    Σ ;;; Γ ⊢ u ≤s[pb] t : T

(* type cumul *)

| typed_cumul_Type : forall t t' T T' s,
  P Σ Γ T T' s ->
  Σ ;;; Γ ⊢ t ≤s[pb] t' : T ->
  Σ ;;; Γ ⊢ t ≤s[pb] t' : T'

(** Reductions *)

(** Beta red *)
| typed_cumul_beta : forall na t b b' a a' s T s',
    Σ ;;; Γ ⊢ t ≤s[Conv] t : tSort s ->
    Σ ;;; Γ ,, vass na t ⊢ T ≤s[Conv] T : tSort s' ->
    Σ ;;; Γ ⊢ a ≤s[Conv] a' : t ->
    Σ ;;; Γ ,, vass na t ⊢ b ≤s[pb] b' : T ->
    Σ ;;; Γ ⊢ tApp (tLambda na t b) a ≤s[pb] b' {0 := a'} : T {0 := a}

(** Congruences *)
| typed_cumul_Rel n decl :
    All_local_env (lift_typing1 (fun Γ t T => Σ ;;; Γ ⊢ t ≤s[Conv] t : T)) Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ ⊢ tRel n ≤s[pb] tRel n : lift0 (S n) decl.(decl_type)

| typed_cumul_app : forall f f' na A B s arg arg',
    Σ ;;; Γ ,, vass na A ⊢ B ≤s[Conv] B : tSort s ->
    Σ ;;; Γ ⊢ f ≤s[pb] f' : tProd na A B ->
    Σ ;;; Γ ⊢ arg ≤s[Conv] arg' : A ->
    Σ ;;; Γ ⊢ tApp f arg ≤s[pb] tApp f' arg' : B {0 := arg}

| typed_cumul_lambda : forall na na' A A' s t t' B,
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ A ≤s[Conv] A' : tSort s ->
    Σ ;;; Γ ,, vass na A ⊢ t ≤s[pb] t' : B ->
    Σ ;;; Γ ⊢ tLambda na A t ≤s[pb] tLambda na' A' t' : tProd na A B

| typed_cumul_Prod : forall na na' A A' s B B' s',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ A ≤s[Conv] A' : tSort s ->
    Σ ;;; Γ ,, vass na A ⊢ B ≤s[pb] B' : tSort s' ->
    Σ ;;; Γ ⊢ tProd na A B ≤s[pb] tProd na' A' B' : tSort (Sort.sort_of_product s s')

| typed_cumul_Fix mfix mfix' idx decl :
    All_local_env (lift_typing1 (fun Γ t T => Σ ;;; Γ ⊢ t ≤s[Conv] t : T)) Γ ->
    fix_guard Σ Γ mfix ->
    fix_guard Σ Γ mfix' ->
    wf_fixpoint Σ mfix ->
    wf_fixpoint Σ mfix' ->
    nth_error mfix idx = Some decl ->
    All2 (fun d d' => eq_binder_annot d.(dname) d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix' ->
    All2 (fun d d' => ∑ s, Σ ;;; Γ ⊢ d.(dtype) ≤s[Conv] d'.(dtype) : tSort s × relevance_of_sort s = d.(dname).(binder_relevance)) mfix mfix' ->
    All2 (fun d d' => Σ ;;; Γ ,,, fix_context mfix ⊢ d.(dbody) ≤s[Conv] d'.(dbody) : lift0 #|mfix| d.(dtype)) mfix mfix' ->
    Σ ;;; Γ ⊢ tFix mfix idx ≤s[pb] tFix mfix' idx : decl.(dtype)

where " Σ ;;; Γ ⊢ t ≤s[ pb ] u : T " := (@typedCumul _ _ Σ Γ pb t u T) : type_scope.

Disable Notation " Σ ;;; Γ ⊢ t ≤s[ pb ] u : T ".

Inductive typed_cumulSpec_self {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (pb : conv_pb) t t' T :=
  | tscself : typedCumul (fun Σ Γ T T' s => typed_cumulSpec_self Σ Γ Cumul T T' (tSort s)) Σ Γ pb t t' T -> typed_cumulSpec_self Σ Γ pb t t' T.


Lemma typedCumul_rect0 cumulType :
  forall cf (Σ : global_env_ext)
         (P : forall cf Σ Γ pb u v T, @typedCumul cumulType cf Σ Γ pb u v T -> Type),

    (* beta *)
    (forall (Γ : context) (pb : conv_pb) (na : aname) (t b b' a a' T : term) (s s' : sort)
        (redt : typedCumul cumulType Σ Γ Conv t t (tSort s)) (Ht : P cf Σ Γ Conv t t (tSort s) redt)
        (redT : typedCumul cumulType Σ (Γ ,, vass na t) Conv T T (tSort s')) (HT : P cf Σ (Γ ,, vass na t) Conv T T (tSort s') redT)
        (reda : typedCumul cumulType Σ Γ Conv a a' t) (Ha : P cf Σ Γ Conv a a' t reda)
        (redb : typedCumul cumulType Σ (Γ ,, vass na t) pb b b' T) (Hb : P cf Σ (Γ ,, vass na t) pb b b' T redb),
        P cf Σ Γ pb (tApp (tLambda na t b) a) (b' {0 := a'}) (T {0 := a}) (typed_cumul_beta _ _ _ _ _ _ _ _ _ _ _ _ _ redt redT reda redb)) ->

    (* transitivity *)
    (forall (Γ : context) (pb : conv_pb) (t u v T : term)
        (Htu : typedCumul cumulType Σ Γ pb t u T) (_ : P cf Σ Γ pb t u T Htu)
        (Huv : typedCumul cumulType Σ Γ pb u v T) (_ : P cf Σ Γ pb u v T Huv),
        P cf Σ Γ pb t v T
          (typed_cumul_Trans _ _ _ _ _ _ _ _ Htu Huv)) ->

    (* symmetry *)
    (forall (Γ : context) (pb : conv_pb) (t u T : term)
            (Hut : typedCumul cumulType Σ Γ Conv u t T) (_ : P cf Σ Γ Conv u t T Hut),
        P cf Σ Γ pb t u T
          (typed_cumul_Sym _ _ _ _ _ _ _ Hut)) ->

    (* type cumul *)
    (forall (Γ : context) (pb : conv_pb) (t t' T T' : term) (s : sort)
        (redt : typedCumul cumulType Σ Γ pb t t' T) (Ht : P cf Σ Γ pb t t' T redt)
        (cumulT : cumulType Σ Γ T T' s),
        P cf Σ Γ pb t t' T'
          (typed_cumul_Type _ _ _ _ _ _ _ _ _ cumulT redt)) ->

    (forall (Γ : context) (wfΓ : All_local_env (lift_typing1 (fun Γ t T => typedCumul cumulType Σ Γ Conv t t T)) Γ) (pb : conv_pb) (n : nat) decl,
        forall (hnth : nth_error Γ n = Some decl),
        P cf Σ Γ pb (tRel n) (tRel n) (lift0 (S n) decl.(decl_type)) (typed_cumul_Rel _ _ _ _ _ _ wfΓ hnth)) ->

    (forall (Γ : context) (pb : conv_pb) (na : aname) (f f' A B arg arg' : term) (s : sort)
        (redB : typedCumul cumulType Σ (Γ ,, vass na A) Conv B B (tSort s)) (HB : P cf Σ (Γ ,, vass na A) _ _ _ _ redB)
        (redf : typedCumul cumulType Σ Γ pb f f' (tProd na A B)) (Hf : P cf Σ Γ _ _ _ _ redf)
        (redarg : typedCumul cumulType Σ Γ Conv arg arg' A) (Harg : P cf Σ Γ Conv _ _ _ redarg),
        P cf Σ Γ pb (tApp f arg) (tApp f' arg') (B { 0 := arg }) (typed_cumul_app _ _ _ _ _ _ _ _ _ _ _ _ redB redf redarg)) ->

    (forall (Γ : context) (pb : conv_pb) (na na' : aname) (s : sort) (A A' t t' B : term)
        (eqna : eq_binder_annot na na')
        (redA : typedCumul cumulType Σ Γ Conv A A' (tSort s)) (HA : P cf Σ Γ _ _ _ _ redA)
        (redt : typedCumul cumulType Σ (Γ ,, vass na A) pb t t' B) (HT : P cf Σ _ _ _ _ _ redt),
        P cf Σ Γ pb (tLambda na A t) (tLambda na' A' t') (tProd na A B) (typed_cumul_lambda _ _ _ _ _ _ _ _ _ _ _ _ eqna redA redt)) ->

    (forall (Γ : context) (pb : conv_pb) (na na' : aname) (s s' : sort) (A A' B B' : term)
        (eqna : eq_binder_annot na na')
        (redA : typedCumul cumulType Σ Γ Conv A A' (tSort s)) (HA : P cf Σ Γ _ _ _ _ redA)
        (redB : typedCumul cumulType Σ (Γ ,, vass na A) pb B B' (tSort s')) (HB : P cf Σ _ _ _ _ _ redB),
        P cf Σ Γ pb (tProd na A B) (tProd na' A' B') (tSort (Sort.sort_of_product s s')) (typed_cumul_Prod _ _ _ _ _ _ _ _ _ _ _ _ eqna redA redB)) ->

    (forall (Γ : context) (wfΓ : All_local_env (lift_typing1 (fun Γ t T => typedCumul cumulType Σ Γ Conv t t T)) Γ) (pb : conv_pb) (mfix mfix' : mfixpoint term) (idx : nat) decl,
        forall hguard : fix_guard Σ Γ mfix,
        forall hguard' : fix_guard Σ Γ mfix',
        forall wf_fix : wf_fixpoint Σ mfix,
        forall wf_fix' : wf_fixpoint Σ mfix',
        forall hnth : nth_error mfix idx = Some decl,
        forall eqfixannot : All2 (fun d d' => eq_binder_annot d.(dname) d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix',
        forall redty : All2 (fun d d' => ∑ s, typedCumul cumulType Σ Γ Conv d.(dtype) d'.(dtype) (tSort s) × relevance_of_sort s = d.(dname).(binder_relevance)) mfix mfix',
        forall redbod : All2 (fun d d' => typedCumul cumulType Σ (Γ ,,, fix_context mfix) Conv d.(dbody) d'.(dbody) (lift0 #|mfix| d.(dtype))) mfix mfix',
        All2_dep (fun d d' H => P cf Σ Γ Conv d.(dtype) d'.(dtype) (tSort H.π1) H.π2.1) redty ->
        All2_dep (fun d d' H => P cf Σ (Γ ,,, fix_context mfix) Conv d.(dbody) d'.(dbody) (lift0 #|mfix| d.(dtype)) H) redbod ->
        P cf Σ Γ pb (tFix mfix idx) (tFix mfix' idx) decl.(dtype) (typed_cumul_Fix _ _ _ _ _ _ _ _ wfΓ hguard hguard' wf_fix wf_fix' hnth eqfixannot redty redbod)) ->

    forall (Γ : context) (pb : conv_pb) (t t' T : term) (Ht : @typedCumul cumulType cf Σ Γ pb t t' T), P cf Σ Γ pb t t' T Ht.
Proof.
  intros. rename Ht into Xlast.
  revert Γ pb t t' T Xlast.
  fix aux 6. intros Γ pb t u T Xlast.
  move aux at top.
  destruct Xlast.
  - eapply X0; eauto.
  - eapply X1; eauto.
  - eapply X2; eauto.
  - eapply X; eauto.
  - eapply X3; eauto.
  - eapply X4; eauto.
  - eapply X5; eauto.
  - eapply X6; eauto.
  - eapply X7; eauto.
    + clear -a1 aux.
      induction a1; constructor; eauto.
    + clear -a2 aux.
      induction a2; constructor; eauto.
Defined.



Lemma All_local_env_impl_transparent P Q Γ :
  (forall Γ t T, P Γ t T -> Q Γ t T) ->
  All_local_env (lift_typing1 P) Γ -> All_local_env (lift_typing1 Q) Γ.
Proof.
  intro X.
  induction 1; constructor => //.
  all: destruct t0 as (Hb & s & HT & e).
  all: repeat (eexists; tea); cbn in *; eauto.
Defined.


Lemma typedCumul_rect cumulType :
  forall cf (Σ : global_env_ext) P,

    (* beta *)
    (forall (Γ : context) (pb : conv_pb) (na : aname) (t b b' a a' T : term) (s s' : sort)
        (redt : typedCumul cumulType Σ Γ Conv t t (tSort s)) (Ht : P cf Σ Γ Conv t t (tSort s))
        (redT : typedCumul cumulType Σ (Γ ,, vass na t) Conv T T (tSort s')) (HT : P cf Σ (Γ ,, vass na t) Conv T T (tSort s'))
        (reda : typedCumul cumulType Σ Γ Conv a a' t) (Ha : P cf Σ Γ Conv a a' t)
        (redb : typedCumul cumulType Σ (Γ ,, vass na t) pb b b' T) (Hb : P cf Σ (Γ ,, vass na t) pb b b' T),
        P cf Σ Γ pb (tApp (tLambda na t b) a) (b' {0 := a'}) (T {0 := a})) ->

    (* transitivity *)
    (forall (Γ : context) (pb : conv_pb) (t u v T : term)
        (Htu : typedCumul cumulType Σ Γ pb t u T) (_ : P cf Σ Γ pb t u T)
        (Huv : typedCumul cumulType Σ Γ pb u v T) (_ : P cf Σ Γ pb u v T),
        P cf Σ Γ pb t v T) ->

    (* symmetry *)
    (forall (Γ : context) (pb : conv_pb) (t u T : term)
            (Hut : typedCumul cumulType Σ Γ Conv u t T) (_ : P cf Σ Γ Conv u t T),
        P cf Σ Γ pb t u T) ->

    (* type cumul *)
    (forall (Γ : context) (pb : conv_pb) (t t' T T' : term) (s : sort)
        (redt : typedCumul cumulType Σ Γ pb t t' T) (Ht : P cf Σ Γ pb t t' T)
        (cumulT : cumulType Σ Γ T T' s),
        P cf Σ Γ pb t t' T') ->

    (forall (Γ : context) (wfΓ : All_local_env (lift_typing1 (fun Γ t T => typedCumul cumulType Σ Γ Conv t t T)) Γ) (pb : conv_pb) (n : nat) decl,
        forall (hnth : nth_error Γ n = Some decl),
        All_local_env (lift_typing1 (fun Γ t T => P cf Σ Γ Conv t t T)) Γ ->
        P cf Σ Γ pb (tRel n) (tRel n) (lift0 (S n) decl.(decl_type))) ->

    (forall (Γ : context) (pb : conv_pb) (na : aname) (f f' A B arg arg' : term) (s :  sort)
        (redB : typedCumul cumulType Σ (Γ ,, vass na A) Conv B B (tSort s)) (HB : P cf Σ (Γ ,, vass na A) Conv B B (tSort s))
        (redf : typedCumul cumulType Σ Γ pb f f' (tProd na A B)) (Hf : P cf Σ Γ pb f f' (tProd na A B))
        (redarg : typedCumul cumulType Σ Γ Conv arg arg' A) (Harg : P cf Σ Γ Conv arg arg' A),
        P cf Σ Γ pb (tApp f arg) (tApp f' arg') (B { 0 := arg })) ->

    (forall (Γ : context) (pb : conv_pb) (na na' : aname) (s : sort) (A A' t t' B : term)
        (eqna : eq_binder_annot na na')
        (redA : typedCumul cumulType Σ Γ Conv A A' (tSort s)) (HA : P cf Σ Γ Conv A A' (tSort s))
        (redt : typedCumul cumulType Σ (Γ ,, vass na A) pb t t' B) (Ht : P cf Σ (Γ ,, vass na A) pb t t' B),
        P cf Σ Γ pb (tLambda na A t) (tLambda na' A' t') (tProd na A B)) ->

    (forall (Γ : context) (pb : conv_pb) (na na' : aname) (s s' : sort) (A A' B B' : term)
        (eqna : eq_binder_annot na na')
        (redA : typedCumul cumulType Σ Γ Conv A A' (tSort s)) (HA : P cf Σ Γ Conv A A' (tSort s))
        (redB : typedCumul cumulType Σ (Γ ,, vass na A) pb B B' (tSort s')) (HB : P cf Σ (Γ ,, vass na A) pb B B' (tSort s')),
        P cf Σ Γ pb (tProd na A B) (tProd na' A' B') (tSort (Sort.sort_of_product s s'))) ->


    (forall (Γ : context) (wfΓ : All_local_env (lift_typing1 (fun Γ t T => typedCumul cumulType Σ Γ Conv t t T)) Γ) (pb : conv_pb) (mfix mfix' : mfixpoint term) (idx : nat) decl,
        All_local_env (lift_typing1 (fun Γ t T => P cf Σ Γ Conv t t T)) Γ ->
        forall hguard : fix_guard Σ Γ mfix,
        forall hguard' : fix_guard Σ Γ mfix',
        forall wf_fix : wf_fixpoint Σ mfix,
        forall wf_fix' : wf_fixpoint Σ mfix',
        forall hnth : nth_error mfix idx = Some decl,
        forall eqfixannot : All2 (fun d d' => eq_binder_annot d.(dname) d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix',
        forall redty : All2 (fun d d' => ∑ s, typedCumul cumulType Σ Γ Conv d.(dtype) d'.(dtype) (tSort s) × P cf Σ Γ Conv d.(dtype) d'.(dtype) (tSort s) × relevance_of_sort s = d.(dname).(binder_relevance)) mfix mfix',
        forall redbod : All2 (fun d d' => typedCumul cumulType Σ (Γ ,,, fix_context mfix) Conv d.(dbody) d'.(dbody) (lift0 #|mfix| d.(dtype))) mfix mfix',
        All2 (fun d d' => P cf Σ (Γ ,,, fix_context mfix) Conv d.(dbody) d'.(dbody) (lift0 #|mfix| d.(dtype))) mfix mfix' ->
        P cf Σ Γ pb (tFix mfix idx) (tFix mfix' idx) decl.(dtype)) ->

    forall (Γ : context) (pb : conv_pb) (t t' T : term) (Ht : @typedCumul cumulType cf Σ Γ pb t t' T), P cf Σ Γ pb t t' T.
Proof.
  intros. rename Ht into Xlast.
  revert Γ pb t t' T Xlast.
  fix aux 6. intros Γ pb t u T Xlast.
  move aux at top.
  destruct Xlast.
  - eapply X0; eauto.
  - eapply X1; eauto.
  - eapply X2; eauto.
  - eapply X; eauto.
  - eapply X3; eauto.
    eapply All_local_env_impl_transparent with (2 := a). auto.
  - eapply X4; eauto.
  - eapply X5; eauto.
  - eapply X6; eauto.
  - unshelve eapply X7; eauto.
    + eapply All_local_env_impl_transparent with (2 := a). auto.
    + clear -a1 aux.
      induction a1; constructor; eauto.
      destruct r as (s & H & e); eauto.
    + clear -a2 aux.
      apply All2_impl with (1 := a2).
      eauto.
Defined.


Lemma typed_cumulSpec_self_rect :
  forall cf (Σ : global_env_ext)
         (P : forall cf Σ Γ pb u v T, Type),

  (forall (Γ : context) (pb : conv_pb) (t u T : term),
      typedCumul (fun Σ Γ T T' s => P cf Σ Γ Cumul T T' (tSort s)) Σ Γ pb t u T ->
      P cf Σ Γ pb t u T) ->

  forall (Γ : context) (pb : conv_pb) (t t' T : term) (Ht : @typed_cumulSpec_self cf Σ Γ pb t t' T), P cf Σ Γ pb t t' T.
Proof.
  intros cf Σ P X.
  fix aux 6.
  intros Γ pb t u T [redt].
  eapply X. clear X.
  induction redt.
  all: try solve [ econstructor; eauto ].
  - eapply typed_cumul_Fix; tas.
    clear -redty aux.
    induction redty; constructor; eauto.
    destruct r as (s & H & e); eauto.
Qed.


Lemma All_All2 T (P : T -> T -> Type) l : All (fun x => P x x) l -> All2 P l l.
Proof.
  intro X.
  apply All_All2 with (1 := X). auto.
Qed.

Section A.
  Parameter (cumulType : global_env_ext -> context -> conv_pb -> term -> term -> term -> Type).

  Notation " Σ ;;; Γ |- t '≤T[' pb ] u : s " := (cumulType Σ Γ pb t u s) (at level 50, Γ, t, pb, u, s at next level) : type_scope.

  Parameter right_reflexivityT : forall Σ Γ pb t u T,
  Σ ;;; Γ |- t ≤T[pb] u : T ->
  Σ ;;; Γ |- u ≤T[ Conv ] u : T.

  Parameter substitutivityT0 : forall Σ Γ pb t u T na A a b,
    Σ ;;; Γ ,, vass na A |- t ≤T[pb] u : T ->
    Σ ;;; Γ |- a ≤T[ Conv ] b : A ->
    Σ ;;; Γ |- t {0 := a} ≤T[pb] u {0 := b} : T {0 := a}.

  Context {cf : checker_flags} (Σ : global_env_ext).

  Notation " Σ ;;; Γ ⊢ t '≤s[' pb ] u : T " := (@typedCumul (fun Σ0 Γ0 t0 u0 s0 => cumulType Σ0 Γ0 Cumul t0 u0 (tSort s0)) _ Σ Γ pb t u T) : type_scope.


  Parameter inclT : forall Γ pb t u T,
    Σ ;;; Γ ⊢ t ≤s[ pb ] u : T -> Σ ;;; Γ |- t ≤T[ pb ] u : T.

  Lemma conv_lift0 Γ Γ' pb t u T :
    Σ ;;; Γ ⊢ t ≤s[ pb ] u : T ->
    Σ ;;; Γ ,,, Γ' ⊢ lift0 #|Γ'| t ≤s[ pb ] lift0 #|Γ'| u : lift0 #|Γ'| T.
  Proof. Admitted.

  Lemma substitutivity0 Γ pb t u T na A a b :
    Σ ;;; Γ ,, vass na A ⊢ t ≤s[ pb ] u : T ->
    Σ ;;; Γ ⊢ a ≤s[ Conv ] b : A ->
    Σ ;;; Γ ⊢ t {0 := a} ≤s[ pb ] u {0 := b} : T {0 := a}.
  Proof. Admitted.

  Lemma context_conversion Γ Γ' pb t u T :
    Σ ;;; Γ ⊢ t ≤s[ pb ] u : T ->
    Σ ;;; Γ' ⊢ t ≤s[ pb ] u : T.
  Proof. Admitted.

  Lemma validity Γ pb t u T : Σ ;;; Γ ⊢ t ≤s[ pb ] u : T -> ∑ s, Σ ;;; Γ ⊢ T ≤s[ Conv ] T : tSort s.
  Proof.
    induction 1; eauto.
    all: repeat match goal with H : ∑ s, _ |- _ => destruct H as (?s & H) end.
    all: try solve [ eexists; econstructor; eauto ].
    - eexists. change (tSort ?s) with ((tSort s) {0 := a}).
      eapply substitutivity0; tea.
      admit.
    - apply right_reflexivityT in cumulT.
      admit.
    - eapply All_local_env_nth_error in wfΓ; tea. cbn in wfΓ.
      destruct wfΓ as (_ & ss & XX & _).
      eapply conv_lift0 with (Γ' := firstn (S n) Γ) in XX.
      rewrite /app_context firstn_skipn in XX.
      apply nth_error_Some_length in hnth.
      replace #|firstn _ _| with (S n) in XX by (rewrite firstn_length; lia).
      eexists; apply XX.
    - eexists. change (tSort ?s) with ((tSort s) {0 := arg}) at 2.
      eapply substitutivity0; tea.
      admit.
    -
    Admitted.


  Lemma side_reflexivity Γ pb t u T : Σ ;;; Γ ⊢ t ≤s[ pb ] u : T -> Σ ;;; Γ ⊢ t ≤s[ Conv ] t : T × Σ ;;; Γ ⊢ u ≤s[ Conv ] u : T.
  Proof.
    induction 1.
    all: repeat match goal with H : _ × _ |- _ => let H' := fresh H "'" in destruct H as (H & H') end.
    all: split.
    all: try solve [ econstructor; eauto ].
    - eapply typed_cumul_app; eauto.
      eapply typed_cumul_lambda; eauto.
    - eapply typed_cumul_Type; revgoals.
      + eapply substitutivity0; eauto.
      + eapply substitutivityT0 with (T := tSort _).
        * apply inclT. now constructor.
        * apply inclT. now constructor.
    - eapply typed_cumul_Type; revgoals.
      + eapply typed_cumul_app; eauto.
      + eapply substitutivityT0 with (T := tSort _).
        * apply inclT. now constructor.
        * apply inclT. now constructor.
    - eapply typed_cumul_Type; revgoals.
      + eapply typed_cumul_lambda; eauto.
        eapply context_conversion. eassumption.
      + apply inclT.
        constructor.
        eapply typed_cumul_Prod; eauto.
        admit.
    - eapply typed_cumul_Prod; eauto.
      eapply context_conversion. eassumption.
    - apply typed_cumul_Fix; eauto.
      + apply All_All2.
        solve_all.
      + apply All_All2.
        solve_all.
        destruct a as (s & ? & (? & ?) & ?).
        repeat eexists; tea.
      + apply All_All2.
        solve_all.
    - eapply All2_nth_error_Some with (1 := redty) in hnth as hnth'.
      destruct hnth' as (decl' & hnth' & Hdecl).
      have hlen := (All2_length redty).
      eapply typed_cumul_Type; revgoals.
      1: apply typed_cumul_Fix; eauto.
      + apply All_All2.
        solve_all.
      + apply All_All2.
        solve_all.
        destruct a as (s & ? & (? & ?) & ?).
        repeat eexists; tea.
        rewrite -a0 //.
      + apply All_All2.
        solve_all.
        rewrite -hlen.
        destruct a as (s & H & _).
        eapply typed_cumul_Type; revgoals.
        1: eapply context_conversion; eassumption.
        apply inclT.
        rewrite hlen -fix_context_length.
        apply conv_lift0 with (T := tSort _).
        do 2 constructor. eassumption.
      + instantiate (1 := Hdecl.π1).
        destruct Hdecl as (s & Hdecl & ?); cbn.
        apply inclT.
        now constructor.
    Admitted.



End A.
