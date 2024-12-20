(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses CMorphisms.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config BasicAst Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
  PCUICLiftSubst PCUICSigmaCalculus PCUICUnivSubst PCUICCases PCUICOnFreeVars.

Require Import ssreflect ssrbool.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Notation "[( H : T )] -> U" :=
  (forall H : T, U)
  (at level 0, T at next level, U at level 200, H ident, only parsing) : type_scope.
Notation "[( H x1 .. xn  : T )] -> U" :=
  (forall H : (forall x1, .. (forall xn, T) .. ), U)
  (at level 0, T at next level, U at level 200, H ident, x1 closed binder, xn closed binder, only parsing) : type_scope.

Notation "⌈ constr ⌋" := ltac:(eapply constr; eassumption) (only parsing).

Implicit Types (cf : checker_flags) (Σ : global_env_ext) (Γ : context).




Local Unset Elimination Schemes.

Include PCUICEnvTyping.

Create HintDb fmap.




(* Reserved Notations *)
  Reserved Notation "Σ  ;;; Γ ⊢ T ≤T T'" (at level 50, Γ, T, T' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ T ≤T T' 'with' TC" (at level 50, Γ, T, T', TC at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t : T 'wellsubst'" (at level 50, Γ, t, T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t : T 'wellsubst' 'with' R" (at level 50, Γ, t, T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t = t' : T 'wellsubst'" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t = t' : T 'wellsubst' 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t : T" (at level 50, Γ, t, T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t : T 'with' TC" (at level 50, Γ, t, T at next level).
  Reserved Notation "'wf_local' Σ Γ" (at level 9, Σ, Γ at next level).
  Reserved Notation "'wf_local' Σ Γ 'with' TC" (at level 9, Σ, Γ, TC at next level).
  Reserved Notation "'wf_local_rel' Σ Γ Δ" (at level 9, Σ, Γ, Δ at next level).
  Reserved Notation "'wf_local_rel' Σ Γ Δ 'with' TC" (at level 9, Σ, Γ, Δ, TC at next level).
  Reserved Notation "Σ ;;; Γ ⊢ t ≤[ pb ] t' : T" (at level 50, Γ, pb, t, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤[ pb ]  t'  :  T").
  Reserved Notation "Σ  ;;; Γ ⊢ t = t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≤ t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ ;;; Γ ⊢ t ≤[ pb ] t' : T 'with' TC" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤[ pb ]  t'  :  T  'with'  TC").
  Reserved Notation "Σ  ;;; Γ ⊢ t ▹ T" (at level 50, Γ, t, T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▹□ u" (at level 50, Γ, t, u at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▹Π ( na : A ) , B" (at level 50, Γ, t, na, A, B at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▹Ind( ind , u ) args" (at level 50, Γ, t, ind, u, args at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ◃ T" (at level 50, Γ, t, T at next level).
  Reserved Notation "'wf_local_bd' Σ Γ" (at level 9, Σ, Γ at next level).
  Reserved Notation "'wf_local_bd_rel' Σ Γ Γ'" (at level 9, Σ, Γ, Γ' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▷ T" (at level 50, Γ, t, T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▷□ u" (at level 50, Γ, t, u at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▷Π ( na : A ) , B" (at level 50, Γ, t, na, A, B at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▷Π" (at level 50, Γ, t at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▷Π^ n" (at level 50, Γ, t, n at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▷Ind( ind , u ) args" (at level 50, Γ, t, ind, u, args at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>0 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>0 t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>0 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>0 t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>0 t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>0 t' ▷ T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>0 t' : T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>0 t' ▷ T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ext t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ext t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ext t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ext t' ▷ T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ext t' : T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ext t' ▷ T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' ▷ T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' : T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' ▷ T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R' t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R' t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R' t' : T 'on' H" (at level 50, Γ, t, t', T, H at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R' t' ▷ T 'on' H" (at level 50, Γ, t, t', T, H at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R t'" (at level 50, Γ, t, t' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R' t'" (at level 50, Γ, t, t' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R' t' 'on' H" (at level 50, Γ, t, t', H at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =R t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =R' t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ ;;; Γ ⊢ t ≤R[ pb ] t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤R[ pb ]  t'  :  T").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤R[ pb ] t' ▷ T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤R[ pb ]  t'  ▷  T").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤R'[ pb ] t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤R'[ pb ]  t'  :  T").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤R'[ pb ] t' ▷ T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤R'[ pb ]  t'  ▷  T").
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' ▷ T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' : T 'with' R , R' , R''" (at level 50, Γ, t, t', T, R, R', R'' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' ▷ T 'with' R , R' , R''" (at level 50, Γ, t, t', T, R, R', R'' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~1 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~1 t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~1 t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~1 t' ▷ T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~1 t' : T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~1 t' ▷ T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~h1 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~h1 t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~h1 t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~h1 t' ▷ T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~h1 t' : T 'with' R " (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~h1 t' ▷ T 'with' R " (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>1 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>1 t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>1 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>1 t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~> t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~> t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡> t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡> t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =>s t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =>s t' : T 'on' H 'with' R" (at level 50, Γ, t, t', T, H, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =>s t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =>s t' ▷ T 'on' H 'with' R" (at level 50, Γ, t, t', T, H, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>h t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>h t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>h* t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>h* t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t h~> t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t h~> t' ▷ T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  :  T").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' ▷ T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  ▷  T").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'on' p 'with' R'" (at level 50, Γ, t, pb, t', T, p, R' at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  :  T  'on'  p  'with'  R'").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' ▷ T 'on' p 'with' R'" (at level 50, Γ, t, pb, t', T, p, R' at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  ▷  T  'on'  p  'with'  R'").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'with' R " (at level 50, Γ, t, pb, t', T, R at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  :  T  'with'  R").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' ▷ T 'with' R " (at level 50, Γ, t, pb, t', T, R at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  ▷  T  'with'  R").
  Reserved Notation "Σ  ;;; Γ ⊢ t == t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t <= t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ] t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]  t'  :  T").
  Reserved Notation "Σ  ;;; Γ ⊢ t === t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t <== t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ ;;; Γ ⊢ t <==[ pb ] t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  <==[ pb ]  t'  :  T").
  Reserved Notation "Σ ;;; Γ ⊢ t <===[ pb ] t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  <===[ pb ]  t'  :  T").
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡ t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≦ t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ ;;; Γ ⊢ t ≦[ pb ] t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≦[ pb ]  t'  :  T").
(* End Reserved Notations *)


Module Export typing_utils.
  Lemma subst_idsn_lift n t :
    subst0 (idsn n) (lift n n t) = t.
  Proof.
    sigma.
    rewrite -[X in _ = X]subst_ids.
    apply proper_inst => // i /=.

    rewrite /up /Upn /Up /subst_cons/subst_consn /shiftk/shift /subst_compose /ids/= idsn_length.
    destruct nth_error eqn:hnth.
    - apply nth_error_idsn_eq_Some in hnth as heq. subst t0. cbn. rewrite hnth //.
    - apply nth_error_None in hnth. len in hnth. cbn.
      rewrite nth_error_idsn_None //=. 1: lia.
      lia_f_equal.
  Qed.

  Lemma subst_rel0_lift t :
    (lift 1 1 t) {0 := tRel 0} = t.
  Proof.
    apply subst_idsn_lift with (n := 1).
  Qed.

  Definition lift_sortingε {Pc Ps Qc Qs j} :
    lift_sorting Pc Ps j ->
    (forall t T, Pc t T -> Qc t T) ->
    (forall T s, Ps T s -> Qs T s) ->
    lift_sorting Qc Qs j.
  Proof.
    intros H X X'.
    destruct H as (Ht & s & HT & Hs).
    split; eauto.
    destruct j_term; cbn in * => //. auto.
  Defined.

  Definition lift_typingε {P Q j} :
    lift_typing0 P j ->
    (forall t T, P t T -> Q t T) ->
    lift_typing0 Q j.
  Proof.
    intros H X.
    destruct H as (Ht & s & HT & Hs).
    split; eauto.
    destruct j_term; cbn in * => //. auto.
  Defined.

  Hint Resolve lift_sortingε lift_typingε : fmap.

  Hint Extern 1 => match goal with
    | H : lift_typing1 _ _ _ |- _  => cbn beta in H
    | H : lift_typing _ _ _ |- _ => cbn beta in H end : core.

  Definition All_foldε {P Q Γ} :
    All_fold P Γ ->
    (forall Γ decl, All_fold P Γ -> All_fold Q Γ -> P Γ decl -> Q Γ decl) ->
    All_fold Q Γ.
  Proof.
    intros H X.
    induction H; constructor; eauto.
  Defined.

  Hint Resolve All_foldε : fmap.

  Definition All_local_envε {P Q Γ} :
    All_local_env P Γ ->
    (forall Γ decl, All_local_env P Γ -> All_local_env Q Γ -> P Γ decl -> Q Γ decl) ->
    All_local_env Q Γ.
  Proof.
    intros H X.
    induction H; constructor; eauto.
  Defined.

  Hint Resolve All_local_envε : fmap. Hint Unfold All_local_rel : fmap.

  Lemma wf_local_snoc_vass_s P Γ na t s :
    lift_typing1 P Γ (j_vass_s na t s) ->
    All_local_env (lift_typing1 P) Γ ->
    All_local_env (lift_typing1 P) (Γ ,, vass na t).
  Proof.
    intros.
    constructor; tas.
    now eapply lift_sorting_forget_univ.
  Qed.

  Lemma wf_local_snoc_vass P Γ na t :
    lift_typing1 P Γ (j_vass na t) ->
    All_local_env (lift_typing1 P) Γ ->
    All_local_env (lift_typing1 P) (Γ ,, vass na t).
  Proof.
    intros.
    constructor; tas.
  Qed.

  Lemma wf_local_snoc_vdef P Γ na b t :
    lift_typing1 P Γ (j_vdef na b t) ->
    All_local_env (lift_typing1 P) Γ ->
    All_local_env (lift_typing1 P) (Γ ,, vdef na b t).
  Proof.
    intros.
    constructor; tas.
  Qed.

  Hint Resolve wf_local_snoc_vass_s wf_local_snoc_vass wf_local_snoc_vdef : pcuic.

End typing_utils.

Module Export unlift.

  Definition unlift_renaming n k :=
    shiftn k (fun i => i - n).

  Lemma shiftn_unlift_renaming n k k' :
    shiftn k' (unlift_renaming n k) =1 unlift_renaming n (k' + k).
  Proof.
    intro. unfold unlift_renaming, shiftn.
    repeat nat_compare_specs.
  Qed.

  Definition unlift n k t :=
    rename (unlift_renaming n k) t.

  Theorem lift_unlift n k t : unlift n k (lift n k t) = t.
  Proof.
    rewrite /unlift lift_rename (rename_compose _ _ t).
    rewrite <-(rename_ren_id t) at 2.
    apply rename_proper => //. intro x.
    cbv -[leb plus minus].
    repeat nth_leb_simpl.
  Qed.

  Lemma noccur_unlift n k t :
    noccur_between k n t ->
    lift n k (unlift n k t) = t.
  Proof.
    induction t in k |- * using PCUICInduction.term_forall_list_ind; cbn; auto.
    all: intros; rtoProp; autorewrite with map; rewrite ?shiftn_unlift_renaming; try solve [ f_equal; solve_all ].
    - unfold unlift_renaming, shiftn.
      toProp. destruct H; toProp.
      + apply Nat.ltb_lt in H as H'; rewrite {}H'.
        apply Nat.leb_gt in H as -> => //.
      + unfold Nat.ltb.
        have H' : k < S n0 by lia.
        apply Nat.leb_gt in H' as ->.
        have H' : k <= k + (n0 - k - n) by lia.
        apply Nat.leb_le in H' as ->.
        f_equal. lia.

    - f_equal; auto.
      * solve_all.
        unfold test_predicate_k, map_predicate_k, rename_predicate in *; cbn; destruct p; f_equal; eauto; solve_all; cbn in *.
        + now rewrite shiftn_unlift_renaming.
      * solve_all.
        unfold test_branch_k, map_branch_k, map_branch_shift in *; destruct x; cbn in *; f_equal; eauto; solve_all.
        + unfold shiftf. now rewrite shiftn_unlift_renaming.
    - f_equal; auto.
      red in X. unfold test_def in H. solve_all.
      now rewrite shiftn_unlift_renaming.
    - f_equal; auto.
      red in X. unfold test_def in H. solve_all.
      now rewrite shiftn_unlift_renaming.
  Qed.

  Lemma unlift_lift2 p' k p i t₀ t :
    lift p i t₀ = lift p' k t ->
    p + i <= k ->
    lift p i (unlift p i t) = t.
  Proof.
    intros H H'. unfold unlift.
    (* symmetry; eapply noccur_unlift. *)
    revert t₀ k i H H'.
    induction t using PCUICInduction.term_forall_list_ind;
      destruct t₀ => //= k i [=]; intros; subst.
    all: repeat match goal with H : map _ _ = map _ _ |- _ => apply All2_eq_eq, All2_map_equiv, All2_swap in H; cbn in H
      | |- context [map _ (map _ _) ] => rewrite map_map /=
      | |- context [shiftn _ (unlift_renaming _ _) ] => rewrite shiftn_unlift_renaming /= end.
    all: try solve [f_equal; solve_all].
    - f_equal. unfold unlift_renaming, shiftn, Nat.ltb. revert H.
      repeat nth_leb_simpl.
    - f_equal; solve_all.
      + destruct p0; unfold map_predicate_k, rename_predicate; cbn in *; f_equal.
        * rewrite map_map. solve_all.
        * rewrite H2 in H3. rewrite shiftn_unlift_renaming. eapply e; tea. lia.
      + destruct x as [bctx br]; unfold map_branch_k, rename_branch in *; cbn in *; f_equal.
        apply (f_equal bcontext) in b as b1. cbn in b1. unfold id in *. rewrite b1 in b.
        apply (f_equal bbody) in b. cbn in b. rewrite shiftn_unlift_renaming. eapply b0; tea. lia.
    - len.
      rewrite /map_def /=.
      apply All2_length in H as Xlen. destruct Xlen.
      f_equal; solve_all.
      apply (f_equal dtype) in b as b1. apply (f_equal dbody) in b as b2.
      destruct x; cbn in *; f_equal; eauto.
      rewrite shiftn_unlift_renaming. eapply b0; tea. lia.
    - len.
      rewrite /map_def /=.
      apply All2_length in H as Xlen. destruct Xlen.
      f_equal; solve_all.
      apply (f_equal dtype) in b as b1. apply (f_equal dbody) in b as b2.
      destruct x; cbn in *; f_equal; eauto.
      rewrite shiftn_unlift_renaming. eapply b0; tea. lia.
    - f_equal.
      destruct p0 as [[] p0]; depelim p0; cbnr. destruct X as (? & ? & ?).
      destruct prim as [[] p0']; depelim p0' => //; cbn in H. injection H as [=].
      repeat f_equal. unfold map_array_model, id.
      destruct a; f_equal; cbn in *; eauto.
      apply All2_eq_eq, All2_map_equiv, All2_swap in H2; cbn in H2.
      rewrite map_map; solve_all.
  Qed.

  Lemma unlift_lift_commut n k p i t :
    i <= k ->
    unlift n (p + k) (lift p i t) = lift p i (unlift n k t).
  Proof.
    intro.
    rewrite /unlift/unlift_renaming !lift_rename /lift_renaming !(rename_compose _ _ _) /shiftn.
    apply rename_proper; cbnr.
    intro x.
    repeat nat_compare_specs.
  Qed.

End unlift.

Module Export Substs.
  Definition usubst (Γ : context) σ (Δ : context) :=
    forall n decl,
      nth_error Γ n = Some decl ->
    forall b,
      decl.(decl_body) = Some b ->
      (σ n = (lift0 (S n) b).[σ]) +
      (∑ n' decl' b',
        σ n = tRel n' ×
        nth_error Δ n' = Some decl' ×
        decl_body decl' = Some b' ×
        (** This is let-preservation *)
        lift0 (S n') b' = (lift0 (S n) b).[σ]).

  Definition welltyped_inst typing (Γ : context) σ (Δ : context) :=
    (forall n decl,
      [(Hnth : nth_error Γ n = Some decl)] ->
      typing Δ (σ n) (lift0 (S n) (decl_type decl)).[ σ ]) ×
    usubst Γ σ Δ.

  Notation "Σ ;;; Δ ⊢ σ : Γ 'wellsubst'" := (welltyped_inst (_ Σ) Γ σ Δ).
  Notation "Σ ;;; Δ ⊢ σ : Γ 'wellsubst' 'with' R" := (welltyped_inst (R Σ) Γ σ Δ) (only parsing).

  Definition wellconv_inst conv (Γ : context) (σ σ' : substitutionT) (Δ : context) :=
    (forall n decl,
      [(Hnth : nth_error Γ n = Some decl)] ->
      conv Δ (σ n) (σ' n) (lift0 (S n) (decl_type decl)).[ σ ]) ×
    usubst Γ σ Δ × usubst Γ σ' Δ.

  Notation "Σ ;;; Δ ⊢ σ = σ' : Γ 'wellsubst'" := (wellconv_inst (_ Σ) Γ σ σ' Δ).
  Notation "Σ ;;; Δ ⊢ σ = σ' : Γ 'wellsubst' 'with' R" := (wellconv_inst (R Σ) Γ σ σ' Δ) (only parsing).

  Lemma usubst_ext Γ σ σ' Δ : σ =1 σ' -> usubst Γ σ Δ -> usubst Γ σ' Δ.
  Proof.
    unfold usubst.
    intros e X n decl hnth' b hb; specialize (X n decl hnth' b hb).
    now rewrite <- !(inst_ext _ _ e), <- e.
  Qed.

  Instance usubst_proper : Proper (Logic.eq ==> `=1` ==> Logic.eq ==> iffT) usubst.
  Proof.
    intros Γ Γ' <- σ σ' eq Δ ? <-.
    split; apply usubst_ext; tas.
    symmetry. assumption.
  Qed.

  Lemma welltyped_inst_ext typing Γ σ σ' Δ : σ =1 σ' -> welltyped_inst typing Γ σ Δ -> welltyped_inst typing Γ σ' Δ.
  Proof.
    unfold welltyped_inst.
    intros e [X X']; split.
    - intros n decl hnth'; specialize (X n decl hnth').
      now rewrite <- !(inst_ext _ _ e), <- e.
    - rewrite -e //.
  Qed.

  Instance welltyped_inst_proper typing : Proper (Logic.eq ==> `=1` ==> Logic.eq ==> iffT) (welltyped_inst typing).
  Proof.
    intros Γ Γ' <- σ σ' eq Δ ? <-.
    split; apply welltyped_inst_ext; tas.
    symmetry. assumption.
  Qed.

  Lemma wellconv_inst_ext conv Γ σ σ' τ τ' Δ : σ =1 σ' -> τ =1 τ' ->
    wellconv_inst conv Γ σ τ Δ -> wellconv_inst conv Γ σ' τ' Δ.
  Proof.
    unfold wellconv_inst.
    intros e e' (X & X' & X''); split.
    - intros n decl hnth'; specialize (X n decl hnth').
      now rewrite <- !(inst_ext _ _ e), <- e, <- e'.
    - split; rewrite -?e -?e' //.
  Qed.

  Instance wellconv_inst_proper conv : Proper (Logic.eq ==> `=1` ==> `=1` ==> Logic.eq ==> iffT) (wellconv_inst conv).
  Proof.
    intros Γ Γ' <- σ σ' eq τ τ' eq' Δ ? <-.
    split; apply wellconv_inst_ext; tas.
    all: symmetry; assumption.
  Qed.

  Lemma lift_rename_usubst Γ Δ Γ' :
    usubst (Γ,,, Γ') (⇑^#|Γ'| ↑^#|Δ|) (Γ,,, Δ,,, lift_context #|Δ| 0 Γ').
  Proof.
    set Ξ := Γ,,, Δ,,, lift_context #|Δ| 0 Γ'. cbn.
    intros n decl.
    case: (nth_error_app_context Γ Γ' n) => // x hnth hlt [=] hx; subst x => b hb.
    - right; eexists n, _, _.
      have X t : (lift0 (S n) t).[⇑^#|Γ'| ↑^#|Δ|] = lift0 (S n) (lift #|Δ| (#|Γ'| - S n + 0) t).
      { rewrite -ren_lift_renaming -rename_inst -lift_rename.
        replace #|Γ'| with ((#|Γ'| - S n + 0) + S n) at 1 by lia.
        symmetry. apply permute_lift. lia. }
      eassert (nth_error Ξ n = Some ?[decl'] × decl_body ?decl' = _) as [H H'].
      1: split.
      3: repeat split; tea.
      + rewrite nth_error_app_lt; len => //.
        rewrite nth_error_lift_context_eq hnth /= //.
      + rewrite /= hb //.
      + rewrite /Upn /subst_consn idsn_lt //.
      + rewrite !X.
        reflexivity.
    - right; exists (n + #|Δ|), decl, b.
      have X t : (lift0 (S n) t).[⇑^#|Γ'| (↑^#|Δ|) ] = lift0 (S (n + #|Δ|)) t.
      { rewrite -ren_lift_renaming -rename_inst -lift_rename.
        relativize (S (n + _)).
        1: apply simpl_lift. all: lia. }
      eassert (nth_error Ξ (n + #|Δ|) = Some ?[decl'] × decl_body ?decl' = _) as [H H'].
      1: split.
      3: repeat split; tea.
      + rewrite nth_error_app_ge; len; try lia.
        rewrite nth_error_app_ge; len; try lia.
        rewrite -hnth. lia_f_equal.
      + assumption.
      + rewrite Upn_eq /shiftk /subst_consn nth_error_idsn_None //; try lia.
        cbn. f_equal. len. lia.
      + rewrite !X.
        reflexivity.
  Qed.

  Lemma welltyped_lift_rename_inst typing Γ Γ' Δ :
    [(onrel n decl : nth_error (Γ,,, Δ,,, lift_context #|Δ| 0 Γ') n = Some decl -> typing (Γ,,, Δ,,, lift_context #|Δ| 0 Γ') (tRel n) (lift0 (S n) (decl_type decl)))] ->
    welltyped_inst typing (Γ,,, Γ') (⇑^#|Γ'| ↑^#|Δ|) (Γ,,, Δ,,, lift_context #|Δ| 0 Γ').
  Proof.
    split.
    2: now apply lift_rename_usubst.
    intros n decl.
    case: (nth_error_app_context Γ Γ' n) => // x hnth hlt [=] hx; subst x.
    - rewrite {1}/Upn {1}/subst_consn nth_error_idsn_Some //=.
      relativize (_.[_]).
      1: eapply onrel.
      { rewrite nth_error_app_lt ?lift_context_length // nth_error_lift_context_eq hnth /= //. }
      cbn.
      rewrite !lift0_rename lift_rename !rename_inst !ren_lift_renaming ren_rshiftk !inst_assoc.
      apply inst_ext.
      rewrite -shiftn_Upn -Upn_Upn.
      now replace (S n + _) with #|Γ'| by lia.
    - rewrite {1}Upn_eq subst_consn_ge ?{1}/subst_compose ?subst_consn_ge /=; len => //; try lia.
      rewrite {1}/shiftk.
      replace (_ + _) with (n + #|Δ|) by lia.
      relativize (_.[_]).
      1: apply onrel.
      { rewrite nth_error_app_ge ?nth_error_app_ge ?lift_context_length. 1,2: lia.
        relativize (_ - _). 1: tea. lia. }
      rewrite !lift0_rename !rename_inst !ren_rshiftk inst_assoc.
      apply inst_ext.
      replace (S n) with (S n - #|Γ'| + #|Γ'|) by lia.
      rewrite -shiftk_compose subst_compose_assoc shiftn_Upn.
      rewrite !shiftk_compose.
      now replace (S n - _ + _) with (S (n + #|Δ|)) by lia.
  Qed.

  Lemma welltyped_lift0_inst typing Γ Δ :
    [(onrel n decl : nth_error (Γ,,, Δ) n = Some decl -> typing (Γ,,, Δ) (tRel n) (lift0 (S n) (decl_type decl)))] ->
    welltyped_inst typing Γ (↑^#|Δ|) (Γ ,,, Δ).
  Proof.
    intros.
    rewrite -[↑^_]Upn_0.
    apply welltyped_lift_rename_inst with (Γ' := []); tas.
  Qed.

  Lemma wellconv_lift_rename_inst {conv Γ Γ' Δ} :
    [(onrel n decl : nth_error (Γ,,, Δ,,, lift_context #|Δ| 0 Γ') n = Some decl -> conv (Γ,,, Δ,,, lift_context #|Δ| 0 Γ') (tRel n) (tRel n) (lift0 (S n) (decl_type decl)))] ->
    wellconv_inst conv (Γ,,, Γ') (⇑^#|Γ'| (↑^#|Δ|)) (⇑^#|Γ'| (↑^#|Δ|)) (Γ,,, Δ,,, lift_context #|Δ| 0 Γ').
  Proof.
    split.
    2: split; now apply lift_rename_usubst.
    intros n decl.
    case: (nth_error_app_context Γ Γ' n) => // x hnth hlt [=] hx; subst x.
    - rewrite {1 2}/Upn {1 2}/subst_consn nth_error_idsn_Some //=.
      relativize (_.[_]).
      1: eapply onrel.
      { rewrite nth_error_app_lt ?lift_context_length // nth_error_lift_context_eq hnth /= //. }
      cbn.
      rewrite !lift0_rename lift_rename !rename_inst !ren_lift_renaming ren_rshiftk !inst_assoc.
      apply inst_ext.
      rewrite -shiftn_Upn -Upn_Upn.
      now replace (S n + _) with #|Γ'| by lia.
    - rewrite {1 2}Upn_eq subst_consn_ge ?{1 2}/subst_compose ?subst_consn_ge /=; len => //; try lia.
      rewrite {1 2}/shiftk.
      replace (_ + _) with (n + #|Δ|) by lia.
      relativize (_.[_]).
      1: apply onrel.
      { rewrite nth_error_app_ge ?nth_error_app_ge ?lift_context_length. 1,2: lia.
        relativize (_ - _). 1: tea. lia. }
      rewrite !lift0_rename !rename_inst !ren_rshiftk inst_assoc.
      apply inst_ext.
      replace (S n) with (S n - #|Γ'| + #|Γ'|) by lia.
      rewrite -shiftk_compose subst_compose_assoc shiftn_Upn.
      rewrite !shiftk_compose.
      now replace (S n - _ + _) with (S (n + #|Δ|)) by lia.
  Qed.

  Local Set Elimination Schemes.
  Inductive wellformed_subst : list term -> context -> Type :=
  | wfs_empty : wellformed_subst [] []
  | wfs_ass s Γ na t T :
      wellformed_subst s Γ ->
      wellformed_subst (t :: s) (Γ ,, vass na T)
  | wfs_def s Γ na t T :
      wellformed_subst s Γ ->
      wellformed_subst (subst0 s t :: s) (Γ ,, vdef na t T).

  Inductive welltyped_subst typing : list term -> context -> Type :=
  | wts_empty : welltyped_subst typing [] []
  | wts_ass s Γ na t T :
      welltyped_subst typing s Γ ->
      typing t (subst0 s T) ->
      welltyped_subst typing (t :: s) (Γ ,, vass na T)
  | wts_def s Γ na t T :
      welltyped_subst typing s Γ ->
      typing (subst0 s t) (subst0 s T) ->
      welltyped_subst typing (subst0 s t :: s) (Γ ,, vdef na t T).

  Inductive wellconv_subst conv : list term -> list term -> context -> Type :=
  | wcs_empty : wellconv_subst conv [] [] []
  | wcs_ass s s' Γ na t t' T :
      wellconv_subst conv s s' Γ ->
      conv t t' (subst0 s T) ->
      wellconv_subst conv (t :: s) (t' :: s') (Γ ,, vass na T)
  | wcs_def s s' Γ na t T :
      wellconv_subst conv s s' Γ ->
      conv (subst0 s t) (subst0 s' t) (subst0 s T) ->
      wellconv_subst conv (subst0 s t :: s) (subst0 s' t :: s') (Γ ,, vdef na t T).


  Lemma welltyped_subst_well_formed typing s Γ :
    welltyped_subst typing s Γ -> wellformed_subst s Γ.
  Proof. induction 1; now constructor. Qed.
  Lemma wellconv_subst_well_formed conv s s' Γ :
    wellconv_subst conv s s' Γ -> wellformed_subst s Γ × wellformed_subst s' Γ.
  Proof. induction 1; split; constructor; eauto. all: apply IHX. Qed.

  Lemma nth_error_subst_context (Γ' : context) s (v : nat) k :
    nth_error (subst_context s k Γ') v =
    option_map (subst_decl s (#|Γ'| - S v + k)) (nth_error Γ' v).
  Proof.
  induction Γ' in v |- *; intros.
  - simpl. unfold subst_context, fold_context_k; simpl; rewrite nth_error_nil. easy.
  - simpl. destruct v; rewrite subst_context_snoc.
    + simpl. repeat f_equal; try lia.
    + simpl. rewrite IHΓ'; simpl in *. lia_f_equal.
  Qed.

  Lemma wellformed_subst_length {s Γ} :
    wellformed_subst s Γ -> #|s| = #|Γ|.
  Proof. induction 1 => //=; congruence. Qed.

  Lemma wellformed_subst_def {s Γ n decl b} :
    wellformed_subst s Γ ->
    nth_error Γ n = Some decl ->
    decl_body decl = Some b ->
    nth_error s n = Some (subst0 (skipn (S n) s) b).
  Proof.
    induction 1 in n |- *; destruct n => //=; eauto.
    - intros [= <-] [=].
    - now intros [= <-] [= ->].
  Qed.

  Lemma welltyped_subst_nth {typing s Γ n decl} :
    welltyped_subst typing s Γ ->
    nth_error Γ n = Some decl ->
    ∑ t,
    nth_error s n = Some t ×
    typing t (subst0 (skipn (S n) s) (decl_type decl)).
  Proof.
    induction 1 in n |- *; destruct n => //=; eauto.
    - intros [= <-].
      now eexists _.
    - intros [= <-].
      now eexists _.
  Qed.

  Lemma wellconv_subst_nth {conv s' s Γ n decl} :
    wellconv_subst conv s s' Γ ->
    nth_error Γ n = Some decl ->
    ∑ t t',
    nth_error s n = Some t × nth_error s' n = Some t' ×
    conv t t' (subst0 (skipn (S n) s) (decl_type decl)).
  Proof.
    induction 1 in n |- *; destruct n => //=; eauto.
    - intros [= <-]. now eexists _, _.
    - intros [= <-]. now eexists _, _.
  Qed.

  (* Let-expanding substitution *)
  Lemma wellformed_usubst Γ Δ Γ' s :
    wellformed_subst s Δ ->
    usubst (Γ,,, Δ,,, Γ') (⇑^#|Γ'| (s ⋅n ids)) (Γ,,, subst_context s 0 Γ').
  Proof.
    set Ξ := Γ,,, subst_context s 0 Γ'. cbn.
    intros subs n decl.
    apply wellformed_subst_length in subs as Hlen.
    case: (nth_error_app_context (Γ ,,, Δ) Γ' n) => // x hnth hlt [=] hx; subst x => b hb.
    2: move: hnth.
    2: case: (nth_error_app_context Γ Δ _) => // x' hnth hn' [=] eq; subst x'.
    - right; eexists n, _, _.
      have X t : (lift0 (S n) t).[⇑^#|Γ'| (s ⋅n ids) ] = lift0 (S n) (subst s (#|Γ'| - S n + 0) t).
      { rewrite -subst_inst.
        replace #|Γ'| with ((#|Γ'| - S n + 0) + S n) at 1 by lia.
        symmetry. apply commut_lift_subst_rec. lia. }
      eassert (nth_error Ξ n = Some ?[decl'] × decl_body ?decl' = _) as [H H'].
      1: split.
      3: repeat split; tea.
      + rewrite nth_error_app_lt; len => //.
        rewrite nth_error_subst_context hnth /= //.
      + rewrite /= hb //.
      + rewrite /Upn /subst_consn idsn_lt //.
      + rewrite !X.
        reflexivity.
    - left.
      eapply wellformed_subst_def in hb; tea.
      rewrite /Upn {1}/subst_consn nth_error_idsn_None ?idsn_length; try lia.
      rewrite {1}/subst_consn {1}/subst_compose hb.
      rewrite subst_inst Upn_0 inst_assoc.
      (rewrite skipn_subst; try by lia); [].
      rewrite !subst_compose_assoc.
      rewrite subst_consn_compose. sigma.
      rewrite -subst_compose_assoc -shiftk_shift -subst_compose_assoc.
      rewrite -shiftk_shift.
      (rewrite (shift_subst_consn_ge (S n)); try by len; lia); [].
      now len.
    - right; exists (n - #|s|), decl, b.
      have X t : (lift0 (S n) t).[⇑^#|Γ'| (s ⋅n ids) ] = lift0 (S (n - #|s|)) t.
      { rewrite -subst_inst.
        relativize (S n).
        1: apply simpl_subst. all: lia. }
      eassert (nth_error Ξ (n - #|s|) = Some ?[decl'] × decl_body ?decl' = _) as [H H'].
      1: split.
      3: repeat split; tea.
      + rewrite nth_error_app_ge; len; try lia.
        rewrite -hnth. lia_f_equal.
      + assumption.
      + rewrite Upn_eq /subst_consn nth_error_idsn_None /shiftk //; try lia.
        cbn.
        rewrite (proj2 (nth_error_None _ _)); try (len; lia).
        len. lia_f_equal.
      + rewrite !X.
        reflexivity.
  Qed.

  Lemma wellformed_usubst0 {Γ Δ s} :
    wellformed_subst s Δ ->
    usubst (Γ,,, Δ) (s ⋅n ids) Γ.
  Proof.
    intro Hs.
    eapply wellformed_usubst with (Γ' := []) in Hs.
    rewrite /= Upn_0 in Hs.
    eassumption.
  Qed.

  Lemma welltyped_subst_inst typing Γ Γ' s Δ :
    welltyped_subst (typing Γ) s Δ ->
    [(onrel n decl : nth_error (Γ ,,, subst_context s 0 Γ') n = Some decl -> typing (Γ ,,, subst_context s 0 Γ') (tRel n) (lift0 (S n) (decl_type decl)))] ->
    [(shift_typing t T : typing Γ t T -> typing (Γ ,,, subst_context s 0 Γ') t.[↑^#|Γ'|] T.[↑^#|Γ'|])] ->
    welltyped_inst typing (Γ ,,, Δ ,,, Γ') (⇑^#|Γ'| (s ⋅n ids)) (Γ ,,, subst_context s 0 Γ').
  Proof.
    intros hs onrel shift_typing.
    apply welltyped_subst_well_formed in hs as hus.
    apply wellformed_subst_length in hus as hlen.
    split.
    2: now eapply wellformed_usubst.
    intros n decl.
    case: (nth_error_app_context (Γ ,,, Δ) Γ' n) => // x hnth hlt [=] hx; subst x.
    2: move: hnth.
    2: case: (nth_error_app_context Γ Δ _) => // x' hnth hn' [=] eq; subst x'.
    - rewrite {1}/Upn {1}/subst_consn nth_error_idsn_Some //=.
      relativize (_.[_]).
      1: eapply onrel.
      { rewrite nth_error_app_lt ?subst_context_length // nth_error_subst_context hnth /= //. }
      cbn.
      rewrite lift0_rename rename_inst subst_inst !inst_assoc ren_rshiftk. apply inst_ext.
      rewrite /= Nat.add_0_r.
      replace #|Γ'| with (S n + (#|Γ'| - S n)) at 2 by lia.
      rewrite Upn_Upn shiftn_Upn //.
    - eapply welltyped_subst_nth in hnth as (t & hnth & hty); tea.
      apply shift_typing in hty.
      rewrite subst0_inst inst_assoc in hty.
      rewrite {1}Upn_eq subst_consn_ge; len => //; try lia.
      rewrite subst_consn_compose {1}/subst_consn nth_error_map hnth /=.
      relativize (lift0 _ _).[_]; tea.
      rewrite lift0_rename rename_inst inst_assoc ren_rshiftk.
      rewrite skipn_subst. 1: lia.
      rewrite subst_compose_assoc -shiftn_Upn -subst_compose_assoc shiftk_compose.
      lia_f_equal.
    - rewrite {1}Upn_eq subst_consn_ge ?{1}/subst_compose ?subst_consn_ge /=; len => //; try lia.
      rewrite /shiftk.
      replace (_ + _) with (n - #|s|) by lia.
      relativize (_.[_]).
      1: apply onrel.
      { rewrite nth_error_app_ge ?subst_context_length //. 1: lia.
        relativize (_ - _). 1: tea. lia. }
      rewrite !lift0_rename !rename_inst !ren_rshiftk inst_assoc.
      replace (S n) with (S n - #|s| - #|Γ'| + #|s| + #|Γ'|) by lia.
      rewrite -shiftk_compose subst_compose_assoc shiftn_Upn -subst_compose_assoc.
      rewrite -shiftk_compose [_ ∘s (_ ⋅n _) ]subst_compose_assoc subst_consn_shiftn // compose_ids_r shiftk_compose.
      lia_f_equal.
  Qed.

  Lemma welltyped_subst0_inst typing Γ s Δ :
    welltyped_subst (typing Γ) s Δ ->
    [(onrel n decl : nth_error Γ n = Some decl -> typing Γ (tRel n) (lift0 (S n) (decl_type decl)))] ->
    welltyped_inst typing (Γ ,,, Δ) (s ⋅n ids) Γ.
  Proof.
    intros.
    rewrite -[_ ⋅n _]Upn_0.
    apply welltyped_subst_inst with (Γ := Γ) (Δ := Δ) (Γ' := []); tas.
    intros.
    rewrite /= !subst_ids //.
  Qed.


  Lemma wellconv_subst_inst {conv Γ Γ' s s' Δ} :
    wellconv_subst (conv Γ) s s' Δ ->
    [(onrel n decl : nth_error (Γ ,,, subst_context s 0 Γ') n = Some decl -> conv (Γ ,,, subst_context s 0 Γ') (tRel n) (tRel n) (lift0 (S n) (decl_type decl)))] ->
    [(shift_conv t t' T : conv Γ t t' T -> conv (Γ ,,, subst_context s 0 Γ') t.[↑^#|Γ'|] t'.[↑^#|Γ'|] T.[↑^#|Γ'|])] ->
    wellconv_inst conv (Γ ,,, Δ ,,, Γ') (⇑^#|Γ'| (s ⋅n ids)) (⇑^#|Γ'| (s' ⋅n ids)) (Γ ,,, subst_context s 0 Γ').
  Proof.
    (* intros hs onrel shift_conv.
    apply wellconv_subst_well_formed in hs as hus.
    destruct hus as [hus hus'].
    apply wellformed_subst_length in hus as hlen, hus' as hlen'.
    split.
    2: split; now eapply wellformed_usubst.
    intros n decl.
    case: (nth_error_app_context (Γ ,,, Δ) Γ' n) => // x hnth hlt [=] hx; subst x.
    2: move: hnth.
    2: case: (nth_error_app_context Γ Δ _) => // x' hnth hn' [=] eq; subst x'.
    - rewrite {1 2}/Upn {1 3}/subst_consn !nth_error_idsn_Some //=.
      relativize (_.[_]).
      1: eapply onrel.
      { rewrite nth_error_app_lt ?subst_context_length // nth_error_subst_context hnth /= //. }
      cbn.
      rewrite lift0_rename rename_inst subst_inst !inst_assoc ren_rshiftk. apply inst_ext.
      rewrite /= Nat.add_0_r.
      replace #|Γ'| with (S n + (#|Γ'| - S n)) at 2 by lia.
      rewrite Upn_Upn shiftn_Upn //.
    - eapply wellconv_subst_nth in hnth as (t & t' & hnth & hnth' & hty); tea.
      apply shift_conv in hty.
      rewrite subst0_inst inst_assoc in hty.
      rewrite {1 2}/Upn !subst_consn_ge; len => //; try lia.
      rewrite !subst_consn_compose {1 2}/subst_consn !nth_error_map hnth hnth' /=.
      relativize (lift0 _ _).[_]; tea.
      rewrite lift0_rename rename_inst inst_assoc ren_rshiftk.
      rewrite skipn_subst. 1: lia.
      rewrite subst_compose_assoc -shiftn_Upn -subst_compose_assoc shiftk_compose.
      lia_f_equal.
    - rewrite {1 2}/Upn !subst_consn_ge ?{1 2}/subst_compose ?subst_consn_ge /=; len => //; try lia.
      rewrite /shiftk.
      do 2 replace (_ + _) with (n - #|s|) by lia.
      relativize (_.[_]).
      1: apply onrel.
      { rewrite nth_error_app_ge ?subst_context_length //. 1: lia.
        relativize (_ - _). 1: tea. lia. }
      rewrite !lift0_rename !rename_inst !ren_rshiftk inst_assoc.
      replace (S n) with (S n - #|s| - #|Γ'| + #|s| + #|Γ'|) by lia.
      rewrite -shiftk_compose subst_compose_assoc shiftn_Upn -subst_compose_assoc.
      rewrite -shiftk_compose [_ ∘s (_ ⋅n _) ]subst_compose_assoc subst_consn_shiftn // compose_ids_r shiftk_compose.
      lia_f_equal. *)
  Abort.

  Lemma wellconv_subst0_inst conv Γ s s' Δ :
    wellconv_subst (conv Γ) s s' Δ ->
    [(onrel n decl : nth_error Γ n = Some decl -> conv Γ (tRel n) (tRel n) (lift0 (S n) (decl_type decl)))] ->
    wellconv_inst conv (Γ ,,, Δ) (s ⋅n ids) (s' ⋅n ids) Γ.
  Proof.
    intros hs onrel.
    apply wellconv_subst_well_formed in hs as hus.
    destruct hus as [hus hus'].
    apply wellformed_subst_length in hus as hlen, hus' as hlen'.
    split.
    2: split; now eapply wellformed_usubst0.
    intros n decl.
    case: (nth_error_app_context Γ Δ _) => // x' hnth hn' [=] eq; subst x'.
    - eapply wellconv_subst_nth in hnth as (t & t' & hnth & hnth' & hty); tea.
      rewrite subst0_inst in hty.
      rewrite {1 2}/subst_consn hnth hnth' /=.
      relativize (lift0 _ _).[_]; tea.
      rewrite skipn_subst. 1: lia.
      rewrite lift0_rename rename_inst inst_assoc ren_rshiftk //.
    - rewrite !subst_consn_ge ?{1 2}/subst_compose ?subst_consn_ge /=; len => //; try lia.
      rewrite hlen' -hlen {1 2}/ids.
      relativize (_.[_]).
      1: apply onrel.
      1: now rewrite hlen //.
      rewrite !lift0_rename !rename_inst !ren_rshiftk inst_assoc.
      replace (S n) with (S n - #|s| + #|s|) by lia.
      rewrite -shiftk_compose subst_compose_assoc subst_consn_shiftn // compose_ids_r //=.
      lia_f_equal.
  Qed.

End Substs.




(* Abstract relation to compare types, to reduce to products and to sorts *)


Class TypeComparator := { TCit : forall (Σ : global_env_ext) (Γ : context) (T T' : term), Type }.
Class RedtoPi := { RTPit : forall (Σ : global_env_ext) (Γ : context) (T : term) (na : aname) (A B : term), Type }.
Class RedtoSort := { RTSit : forall (Σ : global_env_ext) (Γ : context) (T : term) (s : sort), Type }.
Coercion TCit : TypeComparator >-> Funclass.
Coercion RTPit : RedtoPi >-> Funclass.
Coercion RTSit : RedtoSort >-> Funclass.

Implicit Types (TC : TypeComparator) (RtP : RedtoPi) (RtS : RedtoSort).

Notation "Σ  ;;; Γ ⊢ T ≤T T'" := (@TCit _ Σ Γ T T') (at level 50, Γ, T, T' at next level).
Notation "Σ  ;;; Γ ⊢ T ≤T T' 'with' TC" := (@TCit TC Σ Γ T T') (at level 50, Γ, T, T', TC at next level, only parsing).
Notation "Σ  ;;; Γ ⊢ T ~>Π ( na : A ) , B" := (@RTPit _ Σ Γ T na A B) (at level 50, Γ, T, na, A, B at next level).
Notation "Σ  ;;; Γ ⊢ T ~>Π ( na : A ) , B 'with' RtP" := (@RTPit RtP Σ Γ T na A B) (at level 50, Γ, T, na, A, B, RtP at next level, only parsing).
Notation "Σ  ;;; Γ ⊢ T ~>□ s" := (@RTSit _ Σ Γ T s) (at level 50, Γ, T, s at next level).
Notation "Σ  ;;; Γ ⊢ T ~>□ s 'with' RtS" := (@RTSit RtS Σ Γ T s) (at level 50, Γ, T, s, RtS at next level, only parsing).

Class RevImpliesTC {TC} Σ P := { rto_tc Γ T T' s : P Γ T T' (tSort s) -> Σ ;;; Γ ⊢ T' ≤T T }.

Module TCI.
Local Set Elimination Schemes.

  Reserved Notation "Σ  ;;; Γ ⊢ T '≤*' U" (at level 50, Γ, T, U at next level).
  Inductive TCI TC Σ Γ : term -> term -> Type :=
    | TCI_refl T : Σ ;;; Γ ⊢ T ≤* T
    | TCI_step T T' U : Σ ;;; Γ ⊢ T ≤T T' -> Σ ;;; Γ ⊢ T' ≤* U -> Σ ;;; Γ ⊢ T ≤* U
  where "Σ  ;;; Γ ⊢ A '≤*' T" := (TCI _ Σ Γ A T).

  Lemma TCI_one TC Σ Γ T U : Σ ;;; Γ ⊢ T ≤T U -> Σ ;;; Γ ⊢ T ≤* U.
  Proof.
    intro; repeat econstructor; tea.
  Defined.

  Lemma TCI_trans TC Σ Γ T U V : Σ ;;; Γ ⊢ T ≤* U -> Σ ;;; Γ ⊢ U ≤* V -> Σ ;;; Γ ⊢ T ≤* V.
  Proof.
    intros XTU XUV.
    induction XTU; eauto.
    econstructor; eauto.
  Defined.

  Lemma TCI_rstep TC Σ Γ T U U' : Σ ;;; Γ ⊢ U ≤T U' -> Σ ;;; Γ ⊢ T ≤* U -> Σ ;;; Γ ⊢ T ≤* U'.
  Proof.
    intros.
    eapply TCI_trans; tea. now eapply TCI_one.
  Defined.

  Instance TCI_refl' TC Σ Γ : Reflexive (TCI TC Σ Γ). Proof. constructor; apply TCI_refl. Qed.
  Instance TCI_trans' TC Σ Γ : Transitive (TCI TC Σ Γ). Proof. intro; apply TCI_trans. Qed.

  Class TC_compat TC Σ Γ R := tc_compat : forall T U, Σ ;;; Γ ⊢ T ≤T U -> R T -> R U.

  Lemma TCI_elim TC Σ Γ R (Pre : TC_compat TC Σ Γ R) T U :
    R T ->
    Σ ;;; Γ ⊢ T ≤* U ->
    R U.
  Proof.
    intros H.
    induction 1 => //.
    eauto.
  Defined.

  Lemma TCI_elim' TC Σ Γ R R' (Pre : TC_compat TC Σ Γ R) T :
    (∑ T₀, R' T₀ × Σ ;;; Γ ⊢ T₀ ≤* T) ->
    [(X T : R' T -> R T)] ->
    R T.
  Proof.
    intros (T₀ & H & XT) X.
    eapply TCI_elim in XT; tea.
    eauto.
  Defined.
End TCI. Include TCI.




(* Specification inductives: typing and typed cumulativity *)


Inductive typing {TC} (Σ : global_env_ext) Γ : forall (t T : term), Type :=
  | type_Rel n decl :
      [(wfΓ : wf_local Σ Γ)] ->
      [(Hnth: nth_error Γ n = Some decl)] ->
      Σ ;;; Γ ⊢ tRel n : lift0 (S n) decl.(decl_type)

  | type_Sort s :
      [(wfΓ : wf_local Σ Γ)] ->
      wf_sort Σ s ->
      Σ ;;; Γ ⊢ tSort s : tSort (Sort.super s)

  | type_Prod na A B s1 s2 :
      [(HTA : lift_typing typing Σ Γ (j_vass_s na A s1))] ->
      Σ ;;; Γ ,, vass na A ⊢ B : tSort s2 ->
      Σ ;;; Γ ⊢ tProd na A B : tSort (Sort.sort_of_product s1 s2)

  | type_Lambda na A t B :
      [(HTA : lift_typing typing Σ Γ (j_vass na A))] ->
      Σ ;;; Γ ,, vass na A ⊢ t : B ->
      Σ ;;; Γ ⊢ tLambda na A t : tProd na A B

  | type_App t na A B (* s *) u :
      (* Paranoid assumption, allows to show equivalence with template-coq,
        but eventually unnecessary thanks to validity. *)
      (* Σ ;;; Γ ⊢ tProd na A B : tSort s -> *)
      Σ ;;; Γ ⊢ t : tProd na A B ->
      Σ ;;; Γ ⊢ u : A ->
      Σ ;;; Γ ⊢ tApp t u : B {0 := u}

  | type_cumul t A B :
      Σ ;;; Γ ⊢ t : A ->
      Σ ;;; Γ ⊢ A ≤T B ->
      Σ ;;; Γ ⊢ t : B

where " Σ ;;; Γ ⊢ t : T " := (typing Σ Γ t T)
and "'wf_local' Σ Γ " := (All_local_env (lift_typing1 (typing Σ)) Γ).
Derive Signature for typing.

Notation " Σ  ;;; Γ ⊢ t : T 'with' TC" := (@typing TC Σ Γ t T) (only parsing).
Notation "'wf_local' Σ Γ 'with' TC" := (All_local_env (lift_typing1 (@typing TC Σ)) Γ) (only parsing).
Notation "'wf_local_rel' Σ Γ Δ" := (All_local_rel (lift_typing1 (typing Σ)) Γ Δ).
Notation "'wf_local_rel' Σ Γ Δ 'with' TC" := (All_local_rel (lift_typing1 (@typing TC Σ)) Γ Δ) (only parsing).

Instance TC_compat_typing TC Σ Γ t : TC_compat TC Σ Γ (typing Σ Γ t). by now econstructor. Defined.

Definition typing_rect TC Σ P Pj PΓ :
  [(Xj Γ j : lift_typing1 (fun Γ t T => Σ ;;; Γ ⊢ t : T × P Γ t T) Γ j -> lift_typing1 P Γ j -> Pj Γ j)] ->
  [(XΓ Γ   : wf_local Σ Γ -> All_local_env Pj Γ -> PΓ Γ)] ->
  [(XRel Γ n decl :
      wf_local Σ Γ -> PΓ Γ -> nth_error Γ n = Some decl ->
      P Γ (tRel n) (lift0 (S n) decl.(decl_type)))] ->
  [(XSort Γ s :
      wf_local Σ Γ -> PΓ Γ ->
      wf_sort Σ s ->
      P Γ (tSort s) (tSort (Sort.super s)))] ->

  [(XProd Γ na A B s1 s2 :
      lift_typing typing Σ Γ (j_vass_s na A s1) ->
      Pj Γ (j_vass_s na A s1) ->
      Σ ;;; Γ ,, vass na A ⊢ B : tSort s2 ->
      P (Γ ,, vass na A) B (tSort s2) ->
      P Γ (tProd na A B) (tSort (Sort.sort_of_product s1 s2)))] ->

  [(XLambda Γ na A t B :
      lift_typing typing Σ Γ (j_vass na A) ->
      Pj Γ (j_vass na A) ->
      Σ ;;; Γ ,, vass na A ⊢ t : B ->
      P (Γ ,, vass na A) t B ->
      P Γ (tLambda na A t) (tProd na A B))] ->

  [(XApp Γ t na A B (* s *) u :
      (* Paranoid assumption, allows to show equivalence with template-coq,
        but eventually unnecessary thanks to validity. *)
      (* Σ ;;; Γ ⊢ tProd na A B : tSort s -> *)
      (* P Γ (tProd na A B) (tSort s) -> *)
      Σ ;;; Γ ⊢ t : tProd na A B ->
      P Γ t (tProd na A B) ->
      Σ ;;; Γ ⊢ u : A ->
      P Γ u A ->
      P Γ (tApp t u) (B {0 := u}))] ->

  [(XCumul Γ t A B :
      Σ ;;; Γ ⊢ t : A ->
      P Γ t A ->
      Σ ;;; Γ ⊢ A ≤T B ->
      P Γ t B )] ->

  forall Γ t T, [(X : Σ ;;; Γ ⊢ t : T)] -> P Γ t T.
Proof.
  intros.
  revert Γ t T X.
  fix Xrec 4.
  move XCumul at top. move Xrec at top.
  have {} Xj Γ j : lift_typing typing Σ Γ j -> Pj Γ j.
  { eauto 7 with fmap. }
  have {} XΓ Γ : wf_local Σ Γ -> PΓ Γ.
  { eauto with fmap. }
  intros Γ t T X. destruct X.
  all: try solve [ match goal with h : _ |- _ => eapply h; eauto end ].
Defined.

Definition typing_elim TC Σ P :
  [(XRel Γ n decl T :
      wf_local Σ Γ -> nth_error Γ n = Some decl ->
      let ty := lift0 (S n) decl.(decl_type) in
      Σ ;;; Γ ⊢ ty ≤* T ->
      P Γ (tRel n) T)] ->
  [(XSort Γ s T :
      wf_local Σ Γ ->
      wf_sort Σ s ->
      let ty := tSort (Sort.super s) in
      Σ ;;; Γ ⊢ ty ≤* T ->
      P Γ (tSort s) T)] ->

  [(XProd Γ na A B s1 s2 T :
      lift_typing typing Σ Γ (j_vass_s na A s1) ->
      Σ ;;; Γ ,, vass na A ⊢ B : tSort s2 ->
      (* P (Γ ,, vass na A) B (tSort s2) -> *)
      let ty := tSort (Sort.sort_of_product s1 s2) in
      Σ ;;; Γ ⊢ ty ≤* T ->
      P Γ (tProd na A B) T)] ->

  [(XLambda Γ na A t B T :
      lift_typing typing Σ Γ (j_vass na A) ->
      Σ ;;; Γ ,, vass na A ⊢ t : B ->
      (* P (Γ ,, vass na A) t B -> *)
      let ty := tProd na A B in
      Σ ;;; Γ ⊢ ty ≤* T ->
      P Γ (tLambda na A t) T)] ->

  [(XApp Γ t na A B (* s *) u T :
      (* Paranoid assumption, allows to show equivalence with template-coq,
        but eventually unnecessary thanks to validity. *)
      (* Σ ;;; Γ ⊢ tProd na A B : tSort s -> *)
      (* P Γ (tProd na A B) (tSort s) -> *)
      Σ ;;; Γ ⊢ t : tProd na A B ->
      (* P Γ t (tProd na A B) -> *)
      Σ ;;; Γ ⊢ u : A ->
      (* P Γ u A -> *)
      let ty := B {0 := u} in
      Σ ;;; Γ ⊢ ty ≤* T ->
      P Γ (tApp t u) T)] ->

  forall Γ t T, [(X : Σ ;;; Γ ⊢ t : T)] -> P Γ t T.
Proof.
  intros.
  set (T0 := T) in X.
  have : Σ ;;; Γ ⊢ T0 ≤* T by reflexivity.
  clearbody T0. move: T.
  induction X using typing_rect with (Pj := fun _ _ => True) (PΓ := fun _ => True) => // T.
  all: try match goal with H : _ |- _ => eapply H; eauto using TCI_refl end.
  intro; apply IHX.
  now eapply TCI_step.
Defined.

Lemma typing_wf_local {TC} Σ Γ t T : Σ ;;; Γ ⊢ t : T -> wf_local Σ Γ.
Proof.
  revert Γ t T. fix rec 4.
  intros ???[]; eauto.
  all: now destruct HTA as (_ & ? & HTA & ?).
Defined.

Lemma lift_typing_wf_local {TC} Σ Γ j : lift_typing typing Σ Γ j -> wf_local Σ Γ.
Proof.
  intro. eapply typing_wf_local.
  apply X.2.π2.
Defined.

Definition typing_TC (TC TC' : TypeComparator) Σ Γ t T :
  Σ ;;; Γ ⊢ t : T with TC ->
  [(X Γ t T : TC Σ Γ t T -> TC' Σ Γ t T)] ->
  Σ ;;; Γ ⊢ t : T with TC'.
Proof.
  intros H X.
  induction H using typing_rect with (Pj := lift_typing (@typing TC') Σ) (PΓ := fun Γ => wf_local Σ Γ with TC').
  all: eauto.
  all: try now econstructor.
Defined.

Hint Resolve typing_TC : fmap.

Class TypedReflexivity {TC} R Σ := {
  trefl Γ t T : Σ ;;; Γ ⊢ t : T -> R Γ t t T;
}.
Class TypedConvReflexivity {TC} R Σ (pb : conv_pb) := {
  treflpb Γ t T : Σ ;;; Γ ⊢ t : T -> R Γ pb t t T;
}.
Lemma TypedConvReflexivity_to TC R Σ pb : TypedConvReflexivity R Σ pb -> TypedReflexivity (fun Γ => R Γ pb) Σ.
Proof. intro. constructor. intro. apply treflpb. Qed.
Instance TypedConvReflexivity_of {TC R Σ pb} : TypedReflexivity (fun Γ => R Γ pb) Σ -> TypedConvReflexivity R Σ pb.
Proof. intro. constructor. intros ?. now apply @trefl with (R := fun Γ => R Γ pb). Qed.

Class LeftTyping {TC} R Σ := {
  typing_left Γ (t u : term) T : R Γ t u T -> Σ ;;; Γ ⊢ t : T;
}.
Class LeftConvTyping {TC} R Σ (pb : conv_pb) := {
  typing_leftpb Γ (t u : term) T : R Γ pb t u T -> Σ ;;; Γ ⊢ t : T;
}.
Lemma LeftConvTyping_to TC R Σ pb : LeftConvTyping R Σ pb -> LeftTyping (fun Γ => R Γ pb) Σ.
Proof. intro. constructor. intro. apply typing_leftpb. Qed.
Instance LeftConvTyping_of {TC R Σ pb} : LeftTyping (fun Γ => R Γ pb) Σ -> LeftConvTyping R Σ pb.
Proof. intro. constructor. intros ?. now apply @typing_left with (R := fun Γ => R Γ pb). Qed.

Class RightTyping {TC} R Σ := {
  typing_right Γ (t u : term) T : R Γ t u T -> Σ ;;; Γ ⊢ u : T;
}.
Class RightConvTyping {TC} R Σ (pb : conv_pb) := {
  typing_rightpb Γ (t u : term) T : R Γ pb t u T -> Σ ;;; Γ ⊢ u : T;
}.
Lemma RightTyping_to TC R Σ pb : RightConvTyping R Σ pb -> RightTyping (fun Γ => R Γ pb) Σ.
Proof. intro. constructor. intro. apply typing_rightpb. Qed.
Instance RightConvTyping_of {TC R Σ pb} : RightTyping (fun Γ => R Γ pb) Σ -> RightConvTyping R Σ pb.
Proof. intro. constructor. intros ?. now apply @typing_right with (R := fun Γ => R Γ pb). Qed.


Class ToWFLocal {TC} Σ P := {
  to_wf_local Γ (t T : term) : P Γ t T -> wf_local Σ Γ
}.
Class ToWFLocal2 {TC} Σ P := {
  to_wf_local2 Γ (t u T : term) : P Γ t u T -> wf_local Σ Γ
}.
Class ToWFLocal2Pb {TC} Σ P (pb : conv_pb) := {
  to_wf_local2pb Γ (t u T : term) : P Γ pb t u T -> wf_local Σ Γ
}.

Instance typing_wf_local' TC Σ : ToWFLocal Σ (typing Σ) := {| to_wf_local := typing_wf_local Σ |}.


Module Export ContextConversion.

  Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
  | rel_some a b : R a b -> rel_option R (Some a) (Some b)
  | rel_none : rel_option R None None.

  Derive Signature NoConfusion for rel_option.

  Definition convertible_decls R R' (decl decl' : context_decl) :=
    eq_binder_annot decl.(decl_name) decl'.(decl_name) ×
    rel_option (fun t u => R t u decl.(decl_type)) decl.(decl_body) decl'.(decl_body) ×
    R' decl.(decl_type) decl'.(decl_type).

  Definition convertible_contexts R R' : crelation context := All2_fold (fun Γ _ => convertible_decls (R Γ) (R' Γ)).
  Definition convertible_contexts_rel R R' Γ : crelation context := All2_fold (fun Δ _ => convertible_decls (R (Γ ,,, Δ)) (R' (Γ ,,, Δ))).

  Class ContextComparator := {
    cmp_term Σ Γ (t t' T : term) : Type;
    cmp_type Σ Γ (T T' : term) : Type;
  }.
  Implicit Types (CC : ContextComparator).

  Notation "Σ  ;;; Γ ⊢ Δ ≤Γ Δ'" := (convertible_contexts_rel (@cmp_term _ Σ) (@cmp_type _ Σ) Γ Δ Δ') (at level 50, Γ, Δ, Δ' at next level).
  Notation "Σ  ;;; Γ ⊢ Δ ≤Γ Δ' 'with' CC" := (convertible_contexts_rel (@cmp_term CC Σ) (@cmp_type CC Σ) Γ Δ Δ') (at level 50, Γ, Δ, Δ', CC at next level, only parsing).
  Notation "Σ  ;;; Γ ⊢ d ≤d d'" := (convertible_decls (cmp_term Σ Γ) (cmp_type Σ Γ) d d') (at level 50, Γ, d, d' at next level).
  Notation "Σ  ;;; Γ ⊢ d ≤d d' 'with' CC" := (convertible_decls (@cmp_term CC Σ Γ) (@cmp_type CC Σ Γ) d d') (at level 50, Γ, d, d', CC at next level, only parsing).
  Notation "Σ ⊢ Δ ≤Γ Δ'" := (convertible_contexts (cmp_term Σ) (cmp_type Σ) Δ Δ') (at level 50, Δ, Δ' at next level).
  Notation "Σ ⊢ Δ ≤Γ Δ' 'with' CC" := (convertible_contexts (@cmp_term CC Σ) (@cmp_type CC Σ) Δ Δ') (at level 50, Δ, Δ', CC at next level, only parsing).

  Lemma nth_error_convertible_context0 {CC} Σ Γ Δ n decl :
    Σ ⊢ Γ ≤Γ Δ ->
    nth_error Δ n = Some decl ->
    ∑ decl', nth_error Γ n = Some decl' ×
    Σ ;;; skipn (S n) Γ ⊢ decl' ≤d decl.
  Proof.
    intros.
    induction X in n, H.
    - rewrite nth_error_nil // in H.
    - destruct n; cbn in *.
      + eexists; split; trea.
        injection H as [= <-].
        assumption.
      + by apply IHX.
  Qed.

  Class CmpContextLiftable {TC CC} Σ := {
    cmp_ctx_lift Γ Δ decl decl' : wf_local Σ (Γ ,,, Δ) ->
      Σ ;;; Γ ⊢ decl ≤d decl' ->
      Σ ;;; Γ ,,, Δ ⊢ map_decl (lift0 #|Δ|) decl ≤d map_decl (lift0 #|Δ|) decl'
  }.

  Lemma nth_error_convertible_context {TC CC} Σ (Pre : CmpContextLiftable Σ) Γ Δ n decl :
    Σ ⊢ Γ ≤Γ Δ ->
    wf_local Σ Γ ->
    nth_error Δ n = Some decl ->
    ∑ decl', nth_error Γ n = Some decl' ×
    Σ ;;; Γ ⊢ map_decl (lift0 (S n)) decl' ≤d map_decl (lift0 (S n)) decl.
  Proof.
    intros XΓ wfΓ hnth.
    eapply nth_error_convertible_context0 in hnth as (decl' & hnth & X); tea.
    exists decl'; split; tas.
    rewrite -(firstn_skipn (S n) Γ) in wfΓ |- *.
    eapply cmp_ctx_lift with (Δ := firstn (S n) Γ) in X.
    2: apply wfΓ.
    rewrite firstn_length_le // in X.
    apply nth_error_Some_length in hnth. lia.
  Qed.


  Class TCIsCmpType {TC CC} Σ := {
    to_cmp_type Γ T T' : Σ ;;; Γ ⊢ T ≤T T' -> cmp_type Σ Γ T T';
    rto_tci Γ T T' : cmp_type Σ Γ T T' -> Σ ;;; Γ ⊢ T ≤* T';
  }.

  Lemma nth_error_convertible_context_TC {TC CC} Σ (Pre : CmpContextLiftable Σ) (Pre' : TCIsCmpType Σ) Γ Δ n decl :
    Σ ⊢ Γ ≤Γ Δ ->
    wf_local Σ Γ ->
    nth_error Δ n = Some decl ->
    ∑ decl', nth_error Γ n = Some decl' ×
    Σ ;;; Γ ⊢ lift0 (S n) decl'.(decl_type) ≤* lift0 (S n) decl.(decl_type).
  Proof.
    intros XΓ wfΓ hnth.
    eapply nth_error_convertible_context in hnth as (decl' & hnth & X); tea.
    exists decl'; split; tas.
    apply rto_tci. apply X.
  Qed.


  Class CmpWFLocal {TC CC} Σ := {
    cmp_wf_local Γ Δ : Σ ⊢ Γ ≤Γ Δ -> wf_local Σ Δ -> wf_local Σ Γ
  }.

  Class ContextChangeable {CC} P Σ := {
    change_context : forall Γ Δ (t T : term),
      P Δ t T ->
      Σ ⊢ Γ ≤Γ Δ ->
      P Γ t T
  }.

  Class ContextChangeable2 {CC} P Σ := {
    change_context2 : forall Γ Δ (t u T : term),
      P Δ t u T ->
      Σ ⊢ Γ ≤Γ Δ ->
      P Γ t u T
  }.

  Class ContextChangeable2Pb {CC} P Σ (pb : conv_pb) := {
    change_context2pb : forall Γ Δ (t u T : term),
      P Δ pb t u T ->
      Σ ⊢ Γ ≤Γ Δ ->
      P Γ pb t u T
  }.

  Lemma convertible_contexts_snoc {CC} Σ Γ Δ d d' :
    Σ ⊢ Γ ≤Γ Δ ->
    Σ ;;; Γ ⊢ d ≤d d' ->
    Σ ⊢ Γ ,, d ≤Γ Δ ,, d'.
  Proof.
    intros.
    constructor; tas.
  Qed.

  Lemma convertible_contexts_rel_snoc {CC} Σ Γ Δ Δ' d d' :
    Σ ;;; Γ ⊢ Δ ≤Γ Δ' ->
    Σ ;;; Γ ,,, Δ ⊢ d ≤d d' ->
    Σ ;;; Γ ⊢ Δ ,, d ≤Γ Δ' ,, d'.
  Proof.
    intros.
    constructor; tas.
  Qed.

  Lemma convertible_contexts_app {CC} Σ Γ Γ' Δ Δ' :
    Σ ⊢ Γ ≤Γ Γ' ->
    Σ ;;; Γ ⊢ Δ ≤Γ Δ' ->
    Σ ⊢ Γ ,,, Δ ≤Γ Γ' ,,, Δ'.
  Proof.
    induction 2; tas.
    constructor; auto.
  Qed.

  Lemma convertible_contexts_rel_app {CC} Σ Ξ Γ Γ' Δ Δ' :
    Σ ;;; Ξ ⊢ Γ ≤Γ Γ' ->
    Σ ;;; Ξ ,,, Γ ⊢ Δ ≤Γ Δ' ->
    Σ ;;; Ξ ⊢ Γ ,,, Δ ≤Γ Γ' ,,, Δ'.
  Proof.
    induction 2; tas.
    cbn; constructor; cbn; auto.
    rewrite app_context_assoc //.
  Qed.


  Class CCTypedRefl CC TC Σ := {
    cmp_term_refl Γ t T : Σ ;;; Γ ⊢ t : T -> cmp_term Σ Γ t t T;
    cmp_type_refl Γ T s : Σ ;;; Γ ⊢ T : tSort s -> cmp_type Σ Γ T T;
  }.


  Lemma convertible_contexts_refl {CC TC} Σ Γ :
    CCTypedRefl CC TC Σ ->
    wf_local Σ Γ -> Σ ⊢ Γ ≤Γ Γ.
  Proof.
    intro.
    induction 1; try apply convertible_contexts_snoc; auto.
    1: constructor.
    all: destruct t0 as (Hb & s & HT & Hs).
    all: repeat split; cbn; eauto.
    all: try constructor.
    1,3: eapply cmp_type_refl; tea.
    eapply cmp_term_refl; tea.
  Qed.

  Lemma convertible_contexts_rel_refl {CC TC} Σ Γ Δ :
    CCTypedRefl CC TC Σ ->
    wf_local_rel Σ Γ Δ -> Σ ;;; Γ ⊢ Δ ≤Γ Δ.
  Proof.
    intro.
    induction 1; try apply convertible_contexts_rel_snoc; auto.
    1: constructor.
    all: destruct t0 as (Hb & s & HT & Hs).
    all: repeat split; cbn; eauto.
    all: try constructor.
    1,3: eapply cmp_type_refl; tea.
    eapply cmp_term_refl; tea.
  Qed.

  Lemma convertible_contexts_snoc_refl {CC TC} Σ Γ Γ' d :
    CCTypedRefl CC TC Σ ->
    Σ ⊢ Γ ≤Γ Γ' ->
    lift_typing typing Σ Γ (j_decl d) ->
    Σ ⊢ Γ ,, d ≤Γ Γ' ,, d.
  Proof.
    intros ?Pre H X.
    apply convertible_contexts_snoc; tas.
    destruct X as (Xb & s & Xt & Xs); cbn in *.
    repeat split; cbn; eauto.
    - destruct decl_body; constructor.
      apply cmp_term_refl, Xb.
    - eapply cmp_type_refl, Xt.
  Qed.

  Lemma convertible_contexts_app_refl {CC TC} Σ Γ Γ' Δ :
    CCTypedRefl CC TC Σ ->
    Σ ⊢ Γ ≤Γ Γ' ->
    wf_local_rel Σ Γ Δ ->
    Σ ⊢ Γ ,,, Δ ≤Γ Γ' ,,, Δ.
  Proof.
    intros.
    apply convertible_contexts_app; tas.
    by apply convertible_contexts_rel_refl.
  Qed.


  Lemma convertible_contexts_of_rel {CC TC} Σ Γ Δ Δ' :
    CCTypedRefl CC TC Σ ->
    wf_local Σ Γ -> Σ ;;; Γ ⊢ Δ ≤Γ Δ' ->
    Σ ⊢ Γ ,,, Δ ≤Γ Γ ,,, Δ'.
  Proof.
    intros.
    apply convertible_contexts_app; tas.
    by apply convertible_contexts_refl.
  Qed.

End ContextConversion.
Implicit Types (CC : ContextComparator).

Instance typing_CC {TC CC} Σ : CCTypedRefl CC TC Σ -> CmpWFLocal Σ -> CmpContextLiftable Σ -> TCIsCmpType Σ -> ContextChangeable (TC Σ) Σ -> ContextChangeable (typing Σ) Σ.
Proof.
  intros ?Pre?Pre?Pre?Pre?Pre.
  constructor.
  intros Δ Γ ?? X XΓ.
  induction X using typing_rect with (PΓ := fun Γ => forall Δ, Σ ⊢ Δ ≤Γ Γ -> True) (Pj := fun Γ j => forall Δ, Σ ⊢ Δ ≤Γ Γ -> lift_typing typing Σ Δ j) in Δ, XΓ.
  all: try auto.
  - eapply lift_typingε; tea.
    cbn; eauto.
  - eapply cmp_wf_local in X; tea.
    eapply nth_error_convertible_context_TC in H as (decl' & hnth & XT); tea.
    eapply TCI_elim; tc; tea.
    constructor; tea.
  - eapply cmp_wf_local in X; tea.
    by econstructor.
  - specialize (IHX _ XΓ).
    econstructor; eauto.
    eapply IHX0; tea.
    eapply convertible_contexts_snoc_refl; tas. cbn.
    now eapply lift_sorting_forget_univ.
  - specialize (IHX _ XΓ).
    econstructor; eauto.
    eapply IHX0; tea.
    eapply convertible_contexts_snoc_refl; tas.
  - econstructor; eauto.
  - econstructor; eauto.
    eapply change_context; tea.
Qed.

Lemma lift_typing_CC {TC CC} Σ P : ContextChangeable P Σ ->
  forall Γ Δ j, Σ ⊢ Δ ≤Γ Γ -> lift_typing1 P Γ j -> lift_typing1 P Δ j.
Proof.
  intros ?Pre ??? XΓ X.
  eapply lift_typingε. 1: apply X.
  intros; now eapply change_context.
Qed.



Inductive typed_conversion_spec {cf : checker_flags} {TC} (Σ : global_env_ext) (Γ : context) pb : forall (t t' T : term), Type :=
  | tc_sym t u T :
      Σ ;;; Γ ⊢ t = u : T ->
      Σ ;;; Γ ⊢ u ≤[pb] t : T

  | tc_trans t u v T :
      Σ ;;; Γ ⊢ t ≤[pb] u : T ->
      Σ ;;; Γ ⊢ u ≤[pb] v : T ->
      Σ ;;; Γ ⊢ t ≤[pb] v : T

  | tc_beta na A s t u T :
      Σ ;;; Γ ⊢ A = A : tSort s ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ t = t : T ->
      Σ ;;; Γ ⊢ u = u : A ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ≤[pb] t { 0 := u } : T { 0 := u }

  | tc_eta t na A B s :
      Σ ;;; Γ ⊢ A = A : tSort s ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ⊢ t = t : tProd na A B ->
      Σ ;;; Γ ⊢ t ≤[pb] tLambda na A (tApp (lift0 1 t) (tRel 0)) : tProd na A B

  | tc_rel n decl :
      wf_local Σ Γ ->
      nth_error Γ n = Some decl ->
      Σ ;;; Γ ⊢ tRel n ≤[pb] tRel n : lift0 (S n) decl.(decl_type)

  | tc_lambda na na' A A' s t t' T :
      eq_binder_annot na na' ->
      Σ ;;; Γ ⊢ A = A' : tSort s ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ t = t' : T ->
      Σ ;;; Γ ⊢ tLambda na A t ≤[pb] tLambda na' A' t' : tProd na A T

  | tc_app t t' u u' na A B :
      Σ ;;; Γ ⊢ t = t' : tProd na A B ->
      Σ ;;; Γ ⊢ u = u' : A ->
      Σ ;;; Γ ⊢ tApp t u ≤[pb] tApp t' u' : B { 0 := u }

  | tc_prod na na' A A' B B' s s' :
      eq_binder_annot na na' ->
      Σ ;;; Γ ⊢ A = A' : tSort s ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ B ≤[pb] B' : tSort s' ->
      Σ ;;; Γ ⊢ tProd na A B ≤[pb] tProd na' A' B' : tSort (Sort.sort_of_product s s')

  | tc_sort s s' :
      wf_local Σ Γ ->
      wf_sort Σ s ->
      wf_sort Σ s' ->
      compare_sort Σ pb s s' ->
      Σ ;;; Γ ⊢ tSort s ≤[pb] tSort s' : tSort (Sort.super s')

  | tc_sprop t u T :
      Σ ;;; Γ ⊢ t = t : T ->
      Σ ;;; Γ ⊢ u = u : T ->
      Σ ;;; Γ ⊢ T = T : tSort sSProp ->
      Σ ;;; Γ ⊢ t ≤[pb] u : T

  | tc_cumul t u T U :
      Σ ;;; Γ ⊢ t ≤[pb] u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t ≤[pb] u : U

where " Σ ;;; Γ ⊢ t ≤[ pb ] t' : T " := (typed_conversion_spec Σ Γ pb t t' T)
and " Σ ;;; Γ ⊢ t = t' : T " := (typed_conversion_spec Σ Γ Conv t t' T)
and " Σ ;;; Γ ⊢ t ≤ t' : T " := (typed_conversion_spec Σ Γ Cumul t t' T).

Notation " Σ  ;;; Γ ⊢ t ≤[ pb ] t' : T 'with' TC" := (@typed_conversion_spec _ TC Σ Γ pb t t' T) (only parsing).

Instance TC_compat_tc_spec cf TC Σ Γ pb t u : TC_compat TC Σ Γ (typed_conversion_spec Σ Γ pb t u). by now econstructor. Defined.

Definition tc_eq_pb {cf} {TC} Σ Γ pb t u T : Σ ;;; Γ ⊢ t = u : T -> Σ ;;; Γ ⊢ t ≤[pb]  u : T.
Proof. intro; now do 2 apply tc_sym. Defined.

Definition typed_conversion_spec_rect cf TC Σ P :
  [(XSym Γ pb t u T :
      Σ ;;; Γ ⊢ u = t : T ->
      P Γ Conv u t T ->
      P Γ pb t u T)] ->
  [(XTrans Γ pb t u v T :
      Σ ;;; Γ ⊢ t ≤[pb] u : T ->
      P Γ pb t u T ->
      Σ ;;; Γ ⊢ u ≤[pb] v : T ->
      P Γ pb u v T ->
      P Γ pb t v T)] ->
  [(XBeta Γ pb na A s t u T :
      Σ ;;; Γ ⊢ A = A : tSort s ->
      P Γ Conv A A (tSort s) ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ t = t : T ->
      P (Γ ,, vass na A) Conv t t T ->
      Σ ;;; Γ ⊢ u = u : A ->
      P Γ Conv u u A ->
      P Γ pb (tApp (tLambda na A t) u) (t { 0 := u }) (T { 0 := u }) )] ->
  [(XEta Γ pb t na A B s :
      Σ ;;; Γ ⊢ A = A : tSort s ->
      P Γ Conv A A (tSort s) ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ⊢ t = t : tProd na A B ->
      P Γ Conv t t (tProd na A B) ->
      P Γ pb t (tLambda na A (tApp (lift0 1 t) (tRel 0))) (tProd na A B))] ->
  [(XRel Γ pb n decl :
      wf_local Σ Γ ->
      nth_error Γ n = Some decl ->
      P Γ pb (tRel n) (tRel n) (lift0 (S n) decl.(decl_type)))] ->
  [(XLambda Γ pb na na' A A' s t t' T :
      eq_binder_annot na na' ->
      Σ ;;; Γ ⊢ A = A' : tSort s ->
      P Γ Conv A A' (tSort s) ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ t = t' : T ->
      P (Γ ,, vass na A) Conv t t' T ->
      P Γ pb (tLambda na A t) (tLambda na' A' t') (tProd na A T))] ->
  [(XApp Γ pb t t' u u' na A B :
      Σ ;;; Γ ⊢ t = t' : tProd na A B ->
      P Γ Conv t t' (tProd na A B) ->
      Σ ;;; Γ ⊢ u = u' : A ->
      P Γ Conv u u' A ->
      P Γ pb (tApp t u) (tApp t' u') (B { 0 := u }))] ->
  [(XProd Γ pb na na' A A' B B' s s' :
      eq_binder_annot na na' ->
      Σ ;;; Γ ⊢ A = A' : tSort s ->
      P Γ Conv A A' (tSort s) ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ B ≤[pb] B' : tSort s' ->
      P (Γ ,, vass na A) pb B B' (tSort s') ->
      P Γ pb (tProd na A B) (tProd na' A' B') (tSort (Sort.sort_of_product s s')))] ->
  [(XSort Γ pb s s' :
      wf_local Σ Γ ->
      wf_sort Σ s ->
      wf_sort Σ s' ->
      compare_sort Σ pb s s' ->
      P Γ pb (tSort s) (tSort s') (tSort (Sort.super s')))] ->
  [(XSProp Γ pb t u T :
      Σ ;;; Γ ⊢ t = t : T ->
      P Γ Conv t t T ->
      Σ ;;; Γ ⊢ u = u : T ->
      P Γ Conv u u T ->
      Σ ;;; Γ ⊢ T = T : tSort sSProp ->
      P Γ Conv T T (tSort sSProp) ->
      P Γ pb t u T)] ->
  [(XCumul Γ pb t u T U :
      Σ ;;; Γ ⊢ t ≤[pb] u : T ->
      P Γ pb t u T ->
      Σ ;;; Γ ⊢ T ≤T U with TC ->
      P Γ pb t u U )] ->

  forall Γ pb t u T, [(X : Σ ;;; Γ ⊢ t ≤[pb] u : T)] -> P Γ pb t u T.
Proof.
  intros.
  revert Γ pb t u T X.
  fix Xrec 6.
  intros Γ pb_ t_ u_ T_ []; try clear pb_; try clear t_; try clear u_; try clear T_.
  - eapply XSym; eauto.
  - eapply XTrans; eauto.
  - eapply XBeta; eauto.
  - eapply XEta; eauto.
  - eapply XRel; eauto.
  - eapply XLambda; eauto.
  - eapply XApp; eauto.
  - eapply XProd; eauto.
  - eapply XSort; eauto.
  - eapply XSProp; eauto.
  - eapply XCumul; eauto.
Defined.

Definition typed_conversion_spec_TC {cf} (TC TC' : TypeComparator) Σ Γ pb t t' T
  (X : forall Γ t T, TC Σ Γ t T -> TC' Σ Γ t T) :
  Σ ;;; Γ ⊢ t ≤[pb] t' : T with TC ->
  Σ ;;; Γ ⊢ t ≤[pb] t' : T with TC'.
Proof.
  destruct TC' as [TC'].
  induction 1.
  all: try now econstructor; eauto with fmap.
Qed.

Hint Resolve typing_TC : fmap.

Instance typing_to_typed_conv {cf} {TC} Σ :
  TypedReflexivity (fun Γ t u T => Σ ;;; Γ ⊢ t = u : T) Σ.
Proof.
  constructor.
  induction 1 using typing_rect with (Pj := lift_typing1 (fun Γ t T => Σ ;;; Γ ⊢ t = t : T)) (PΓ := fun Γ => True) => //=.
  all: try now econstructor; eauto.
  - destruct IHX as (_ & s & HT & e & ?); cbn in *.
    subst s.
    eapply tc_prod; eauto.
  - destruct IHX as (_ & s & HT & _ & ?); cbn in *.
    eapply tc_lambda; eauto.
Qed.

Instance typing_to_typed_conv' {cf} {TC} Σ :
  TypedConvReflexivity (typed_conversion_spec Σ) Σ Conv.
Proof.
  apply TypedConvReflexivity_of.
  change (fun Γ => typed_conversion_spec Σ Γ Conv) with (fun Γ t u T => Σ ;;; Γ ⊢ t = u : T).
  exact _.
Qed.

(* Bidirectional typing *)


Section BD.
Context {TC} {RtP} {RtS} Σ.

Section Inner.
Context (infering : context -> term -> term -> Type) Γ.
Notation "Σ ;;; Γ ⊢ t ▹ T" := (infering Γ t T) (only parsing).

Inductive infering_sort t s :=
  | infer_sort_Sort T :
    [(X : Σ ;;; Γ ⊢ t ▹ T)] ->
    [(XR : Σ ;;; Γ ⊢ T ~>□ s)] ->
    Σ ;;; Γ ⊢ t ▹□ s
where "Σ ;;; Γ ⊢ t ▹□ s" := (infering_sort t s) (only parsing).

Inductive infering_prod t na A B :=
  | infer_prod_Prod T:
    [(X : Σ ;;; Γ ⊢ t ▹ T)] ->
    [(XR : Σ ;;; Γ ⊢ T ~>Π (na: A), B)] ->
    Σ ;;; Γ ⊢ t ▹Π (na : A), B
where "Σ ;;; Γ ⊢ t ▹Π ( na : A ) , B" := (infering_prod t na A B) (only parsing).

Inductive infering_prod_1 t :=
  | infer_prod_1_Prod T na A B :
    [(X : Σ ;;; Γ ⊢ t ▹ T)] ->
    [(XR : RtP Σ Γ T na A B)] ->
    Σ ;;; Γ ⊢ t ▷Π
where "Σ ;;; Γ ⊢ t ▷Π" := (infering_prod_1 t) (only parsing).

Inductive RtP_n Γ T : nat -> Type :=
  | RTP_0 : RtP_n Γ T 0
  | RTP_S na A B n :
    [(XR : RtP Σ Γ T na A B)] ->
    [(XB : RtP_n (Γ ,, vass na A) B n)] ->
    RtP_n Γ T (S n).

Inductive infering_prod_n t n :=
  | infer_prod_n T :
    [(X : Σ ;;; Γ ⊢ t ▹ T)] ->
    [(XR : RtP_n Γ T n)] ->
    Σ ;;; Γ ⊢ t ▷Π^ n
where "Σ ;;; Γ ⊢ t ▷Π^ n" := (infering_prod_n t n) (only parsing).

Inductive checking t T :=
  | check_Cumul T₀ :
    [(X : Σ ;;; Γ ⊢ t ▹ T₀)] ->
    [(XR : Σ ;;; Γ ⊢ T₀ ≤T T)] ->
    Σ ;;; Γ ⊢ t ◃ T
where "Σ ;;; Γ ⊢ t ◃ T" := (checking t T) (only parsing).

End Inner.

Notation on_judgment infering := (lift_sorting1 (checking infering) (infering_sort infering)).

Inductive infering Γ : term -> term -> Type :=
  | infer_Rel n decl :
    nth_error Γ n = Some decl ->
    Σ ;;; Γ ⊢ tRel n ▹ lift0 (S n) (decl_type decl)

  | infer_Sort s :
    wf_sort Σ s ->
    Σ ;;; Γ ⊢ tSort s ▹ tSort (Sort.super s)

  | infer_Prod na A B s1 s2 :
    on_judgment infering Γ (j_vass_s na A s1) ->
    Σ ;;; Γ ,, vass na A ⊢ B ▹□ s2 ->
    Σ ;;; Γ ⊢ tProd na A B ▹ tSort (Sort.sort_of_product s1 s2)

  | infer_Lambda na A t B :
    on_judgment infering Γ (j_vass na A) ->
    Σ ;;; Γ ,, vass na A ⊢ t ▹ B ->
    Σ ;;; Γ ⊢ tLambda na A t ▹ tProd na A B

  | infer_App t na A B u :
    Σ ;;; Γ ⊢ t ▹Π (na : A), B ->
    Σ ;;; Γ ⊢ u ◃ A ->
    Σ ;;; Γ ⊢ tApp t u ▹ B {0 := u}

where "Σ ;;; Γ ⊢ t ▹ T" := (infering Γ t T) (only parsing)
and "Σ ;;; Γ ⊢ t ▹□ u" := (infering_sort infering Γ t u) (only parsing)
and "Σ ;;; Γ ⊢ t ▹Π ( na : A ) , B" := (@infering_prod infering Γ t na A B) (only parsing)
and "Σ ;;; Γ ⊢ t ◃ T" := (@checking infering Γ t T) (only parsing).
(* and "'wf_local_bd' Σ Γ" := (All_local_env (on_judgment infering) Γ) *)
(* and "'wf_local_bd_rel' Σ Γ Γ'" := (All_local_rel (on_judgment infering) Γ Γ'). *)


Inductive infering_nocheck Γ : term -> term -> Type :=
  | infer_nc_Rel n decl :
    nth_error Γ n = Some decl ->
    Σ ;;; Γ ⊢ tRel n ▷ lift0 (S n) (decl_type decl)

  | infer_nc_Sort s :
    Σ ;;; Γ ⊢ tSort s ▷ tSort (Sort.super s)

  | infer_nc_Prod na A B s1 s2 :
    Σ ;;; Γ ⊢ A ▷□ s1 ->
    Σ ;;; Γ ,, vass na A ⊢ B ▷□ s2 ->
    Σ ;;; Γ ⊢ tProd na A B ▷ tSort (Sort.sort_of_product s1 s2)

  | infer_nc_Lambda na A t B :
    Σ ;;; Γ ,, vass na A ⊢ t ▷ B ->
    Σ ;;; Γ ⊢ tLambda na A t ▷ tProd na A B

  | infer_nc_App t na A B u :
    Σ ;;; Γ ⊢ t ▷Π (na : A), B ->
    Σ ;;; Γ ⊢ tApp t u ▷ B {0 := u}

where "Σ ;;; Γ ⊢ t ▷ T" := (infering_nocheck Γ t T) (only parsing)
and "Σ ;;; Γ ⊢ t ▷□ u" := (infering_sort infering_nocheck Γ t u) (only parsing)
and "Σ ;;; Γ ⊢ t ▷Π ( na : A ) , B" := (@infering_prod infering_nocheck Γ t na A B) (only parsing).
End BD.
Derive Signature for infering.

(* BD Renotations *)
  Notation "Σ ;;; Γ ⊢ t ▹ T" := (infering Σ Γ t T) : type_scope.
  Notation "Σ ;;; Γ ⊢ t ▹□ u" := (infering_sort Σ (infering Σ) Γ t u) : type_scope.
  Notation "Σ ;;; Γ ⊢ t ▹Π ( na : A ) , B" := (infering_prod Σ (infering Σ) Γ t na A B) : type_scope.
  Notation "Σ ;;; Γ ⊢ t ◃ T" := (checking Σ (infering Σ) Γ t T) : type_scope.
  Notation wf_judgment_bd Σ := (lift_sorting1 (checking Σ (infering Σ)) (infering_sort Σ (infering Σ))).
  Notation "'wf_local_bd' Σ Γ" := (All_local_env (wf_judgment_bd Σ) Γ).
  Notation "'wf_local_bd_rel' Σ Γ Γ'" := (All_local_rel (wf_judgment_bd Σ) Γ Γ').
  Notation "Σ ;;; Γ ⊢ t ▷ T" := (infering_nocheck Σ Γ t T) : type_scope.
  Notation "Σ ;;; Γ ⊢ t ▷□ u" := (infering_sort Σ (infering_nocheck Σ) Γ t u) : type_scope.
  Notation "Σ ;;; Γ ⊢ t ▷Π ( na : A ) , B" := (infering_prod Σ (infering_nocheck Σ) Γ t na A B) : type_scope.
  Notation "Σ ;;; Γ ⊢ t ▷Π" := (infering_prod_1 Σ (infering_nocheck Σ) Γ t) : type_scope.
(* End BD Renotations *)

Class BidirTypingElimType := {
  Pinfer : forall (Γ : context) (t T : term), Type;
  Pcheck : forall (Γ : context) (t T : term), Type;
  Pinferprod : forall (Γ : context) (T : term) (na : aname) (A B : term), Type;
  Pinfersort : forall (Γ : context) (T : term) (s : sort), Type;
  Pj : forall (Γ : context) (j : judgment), Type;
  PΓ : forall (Γ : context), Type;
  PΓrel : forall (Γ Δ : context), Type;
}.

Record BidirTypingElimResult {TC RtP RtS} Σ (P : BidirTypingElimType) := {
  BDXinfer : forall Γ t T, Σ ;;; Γ ⊢ t ▹ T -> Pinfer Γ t T;
  BDXcheck : forall Γ t T, Σ ;;; Γ ⊢ t ◃ T -> Pcheck Γ t T;
  BDXinferprod : forall Γ T na A B, Σ ;;; Γ ⊢ T ▹Π (na : A), B -> Pinferprod Γ T na A B;
  BDXinfersort : forall Γ T s, Σ ;;; Γ ⊢ T ▹□ s -> Pinfersort Γ T s;
  BDXΓ : forall Γ, wf_local_bd Σ Γ -> PΓ Γ;
  BDXΓrel : forall Γ Δ, wf_local_bd_rel Σ Γ Δ -> PΓrel Γ Δ;
}.

Definition bidir_ind TC RtP RtS Σ (P : BidirTypingElimType) :
  [(Xj Γ j : wf_judgment_bd Σ Γ j -> lift_sorting (Pcheck Γ) (Pinfersort Γ) j -> Pj Γ j)] ->
  [(XΓ Γ   : wf_local_bd Σ Γ -> All_local_env Pj Γ -> PΓ Γ)] ->
  [(XΓrel Γ Δ : wf_local_bd_rel Σ Γ Δ -> All_local_rel Pj Γ Δ -> PΓrel Γ Δ)] ->
  [(XRel Γ n decl :
      nth_error Γ n = Some decl ->
      Pinfer Γ (tRel n) (lift0 (S n) decl.(decl_type)))] ->
  [(XSort Γ s :
      wf_sort Σ s ->
      Pinfer Γ (tSort s) (tSort (Sort.super s)))] ->

  [(XProd Γ na A B s1 s2 :
      wf_judgment_bd Σ Γ (j_vass_s na A s1) ->
      Pj Γ (j_vass_s na A s1) ->
      Σ ;;; Γ ,, vass na A ⊢ B ▹□ s2 ->
      Pinfersort (Γ ,, vass na A) B s2 ->
      Pinfer Γ (tProd na A B) (tSort (Sort.sort_of_product s1 s2)))] ->

  [(XLambda Γ na A t B :
      wf_judgment_bd Σ Γ (j_vass na A) ->
      Pj Γ (j_vass na A) ->
      Σ ;;; Γ ,, vass na A ⊢ t ▹ B ->
      Pinfer (Γ ,, vass na A) t B ->
      Pinfer Γ (tLambda na A t) (tProd na A B))] ->

  [(XApp Γ t na A B u :
      Σ ;;; Γ ⊢ t ▹Π (na: A), B ->
      Pinferprod Γ t na A B ->
      Σ ;;; Γ ⊢ u ◃ A ->
      Pcheck Γ u A ->
      Pinfer Γ (tApp t u) (B {0 := u}))] ->

  [(XInferProd Γ t T na A B :
      Σ ;;; Γ ⊢ t ▹ T ->
      Pinfer Γ t T ->
      RtP Σ Γ T na A B ->
      Pinferprod Γ t na A B)] ->

  [(XInferSort Γ T S s :
      Σ ;;; Γ ⊢ T ▹ S ->
      Pinfer Γ T S ->
      RtS Σ Γ S s ->
      Pinfersort Γ T s)] ->

  [(XCumul Γ t A B :
      Σ ;;; Γ ⊢ t ▹ A ->
      Pinfer Γ t A ->
      Σ ;;; Γ ⊢ A ≤T B ->
      Pcheck Γ t B )] ->

BidirTypingElimResult Σ P.
Proof.
  intros.
  pose (XrecT := forall Γ t T, Σ ;;; Γ ⊢ t ▹ T -> Pinfer Γ t T).
  assert (XInferProd' : XrecT -> forall Γ t na A B, Σ ;;; Γ ⊢ t ▹Π (na : A), B -> Pinferprod Γ t na A B).
  { intros Xrec Γ t na A B []. eauto. }
  assert (XInferSort' : XrecT -> forall Γ T s, Σ ;;; Γ ⊢ T ▹□ s -> Pinfersort Γ T s).
  { intros Xrec Γ t s []. eauto. }
  assert (XCumul' : XrecT -> forall Γ t T, Σ ;;; Γ ⊢ t ◃ T -> Pcheck Γ t T).
  { intros Xrec Γ t T []. eauto. }
  assert (Xj' : XrecT -> forall Γ j, wf_judgment_bd Σ Γ j -> Pj Γ j).
  { intros Xrec Γ j. eauto with fmap. }
  assert (XΓ' : XrecT -> forall Γ, wf_local_bd Σ Γ -> PΓ Γ).
  { eauto with fmap. }
  assert (XΓrel' : XrecT -> forall Γ Δ, wf_local_bd_rel Σ Γ Δ -> PΓrel Γ Δ).
  { eauto with fmap. }
  suff Xrec : XrecT; subst XrecT.
  { now split. }
  fix Xrec 4. move Xrec at top.
  intros ??? []; try clear t; try clear T.
  all: try solve [ match goal with h : _ |- _ => eapply h; eauto end ].
Qed.

Class LeftInfer {TC RtP RtS} R Σ := {
  infer_left Γ (t u : term) T : R Γ t u T -> Σ ;;; Γ ⊢ t ▹ T;
}.


Class BidirToTypingPrecondition {TC RtP RtS} Σ := {
    RtP_TC : forall Γ T na A B, RtP Σ Γ T na A B -> Σ ;;; Γ ⊢ T ≤T tProd na A B;
    RtS_TC : forall Γ T s, RtS Σ Γ T s -> Σ ;;; Γ ⊢ T ≤T tSort s;
  }.
Arguments BidirToTypingPrecondition : clear implicits.

Definition infer_to_typing_ElimType {TC} Σ := {|
  Pinfer Γ t T := wf_local Σ Γ -> Σ ;;; Γ ⊢ t : T;
  Pcheck Γ t T := wf_local Σ Γ -> Σ ;;; Γ ⊢ t : T;
  Pinferprod Γ t na A B := wf_local Σ Γ -> Σ ;;; Γ ⊢ t : tProd na A B;
  Pinfersort Γ t s := wf_local Σ Γ -> Σ ;;; Γ ⊢ t : tSort s;
  Pj Γ j := wf_local Σ Γ -> lift_typing typing Σ Γ j;
  PΓ Γ := wf_local Σ Γ;
  PΓrel Γ Δ := wf_local Σ Γ -> wf_local Σ (Γ ,,, Δ);
|}.

Theorem infer_to_typing {TC} {RtP} {RtS} Σ (X : BidirToTypingPrecondition TC RtP RtS Σ) :
  BidirTypingElimResult Σ (infer_to_typing_ElimType Σ).
Proof.
  eapply bidir_ind.
  all: rewrite /infer_to_typing_ElimType /=.
  all: intros.
  all: try now (econstructor; eauto with fmap pcuic).
  - unfold lift_typing0. eauto with fmap.
  - eauto with fmap.
  - apply All_local_env_app; tas.
    eapply All_local_envε; tea.
    intros ???? IH. apply IH.
    apply All_local_env_app; tas.
  (* - econstructor; eauto.
    Unshelve. all: todo "decide whether we keep additional hypothesis in tApp". *)
  - econstructor; eauto.
    now apply RtP_TC.
  - econstructor; eauto.
    now apply RtS_TC.
Qed.

Class TypingBidirPrecondition {TC RtP RtS} Σ := {
    TC_refl Γ t T : Σ ;;; Γ ⊢ t : T -> Σ ;;; Γ ⊢ T ≤T T;
    TC_trans Γ T T' T'' : Σ ;;; Γ ⊢ T ≤T T' -> Σ ;;; Γ ⊢ T' ≤T T'' -> Σ ;;; Γ ⊢ T ≤T T'';
    TC_subst Γ na A u T T' : Σ ;;; Γ ,, vass na A ⊢ T ≤T T' -> Σ ;;; Γ ⊢ u : A -> Σ ;;; Γ ⊢ T {0 := u} ≤T T' {0 := u};
    TC_sort_of_product Γ Γ' s1 s2 s1' s2' : Σ ;;; Γ ⊢ tSort s1 ≤T tSort s1' -> Σ ;;; Γ' ⊢ tSort s2 ≤T tSort s2' -> Σ ;;; Γ ⊢ tSort (Sort.sort_of_product s1 s2) ≤T tSort (Sort.sort_of_product s1' s2');
    TC_sort_relevance Γ s s' : Σ ;;; Γ ⊢ tSort s ≤T tSort s' -> relevance_of_sort s = relevance_of_sort s';
    TC_prod_construct Γ na A B B' : lift_typing typing Σ Γ (j_vass na A) -> Σ ;;; Γ ,, vass na A ⊢ B ≤T B' -> Σ ;;; Γ ⊢ tProd na A B ≤T tProd na A B';
    TC_prod_invert Γ T na' A' B' : Σ ;;; Γ ⊢ T ≤T tProd na' A' B' -> ∑ na A B, RtP Σ Γ T na A B × Σ ;;; Γ ⊢ A' ≤T A × Σ ;;; Γ ,, vass na A ⊢ B ≤T B';
    TC_sort_invert Γ T s' : Σ ;;; Γ ⊢ T ≤T tSort s' -> ∑ s, RtS Σ Γ T s × Σ ;;; Γ ⊢ tSort s ≤T tSort s'
  }.
Arguments TypingBidirPrecondition : clear implicits.

Theorem typing_to_check {TC} {RtP} {RtS} Σ (Pre : TypingBidirPrecondition TC RtP RtS Σ) :
  forall Γ t T,
  Σ ;;; Γ ⊢ t : T -> Σ ;;; Γ ⊢ t ◃ T.
Proof.
  intros Γ t T H.
  induction H using typing_rect with (Pj := lift_sorting1 (fun Γ t T => Σ ;;; Γ ⊢ t ◃ T) (fun Γ T s => Σ ;;; Γ ⊢ T ◃ tSort s)) (PΓ := fun Γ => wf_local Σ Γ).
  all: eauto.
  - econstructor. 1: now econstructor.
    eapply TC_refl; tea. now constructor.
  - econstructor. 1: now econstructor.
    eapply TC_refl; tea. now constructor.
  - destruct IHtyping as (_ & s & [T XT XR] & <- & Hrel); cbn in *.
    apply TC_sort_invert in XR as (s10 & HRtS0 & HT0).
    destruct IHtyping0.
    apply TC_sort_invert in XR as (s20 & HRtS & HT).
    econstructor. 1: econstructor.
    + repeat (eexists; cbn; tea).
      rewrite -Hrel.
      now eapply TC_sort_relevance.
    + econstructor; tea.
    + now eapply TC_sort_of_product.
  - destruct IHtyping as (_ & s & [T XT XR] & _ & Hrel); cbn in *.
    apply TC_sort_invert in XR as (s10 & HRtS0 & HT0).
    destruct IHtyping0.
    econstructor. 1: econstructor.
    + repeat (eexists; cbn; tea).
      rewrite -Hrel.
      now eapply TC_sort_relevance.
    + eassumption.
    + now eapply TC_prod_construct.
  - destruct IHtyping1, IHtyping2.
    apply TC_prod_invert in XR as (na0 & A0' & B0 & HRtS & HTA & HTB).
    econstructor. 1: econstructor.
    + econstructor; tea.
    + econstructor; tea.
      eapply TC_trans; tea.
    + eapply TC_subst; tea.
      econstructor; tea.
  - depelim IHtyping.
    econstructor; tea.
    now eapply TC_trans.
Qed.



Class BidirUniquePrecondition {RtP RtS} Σ := {
  RtP_inj Γ T na na' A A' B B' : RtP Σ Γ T na A B -> RtP Σ Γ T na' A' B' -> tProd na A B = tProd na' A' B';
  RtS_inj Γ T s s' : RtS Σ Γ T s -> RtS Σ Γ T s' -> tSort s = tSort s';
  }.
Arguments BidirUniquePrecondition : clear implicits.
Definition infer_unique_ElimType {TC RtP RtS} Σ :=
  let Pinfersort Γ t s := forall s', Σ ;;; Γ ⊢ t ▹□ s' -> tSort s = tSort s' in
{|
  Pinfer Γ t T := forall T', Σ ;;; Γ ⊢ t ▹ T' -> T = T';
  Pcheck Γ t T := True;
  Pinferprod Γ t na A B := forall na' A' B', Σ ;;; Γ ⊢ t ▹Π (na' : A'), B' -> tProd na A B = tProd na' A' B';
  Pinfersort := Pinfersort;
  Pj Γ j := lift_sorting (fun _ _ => True) (Pinfersort Γ) j;
  PΓ Γ := True;
  PΓrel Γ Δ := True;
|}.

Theorem infer_unique_all {TC} {RtP} {RtS} Σ (Pre : BidirUniquePrecondition RtP RtS Σ) :
  BidirTypingElimResult Σ (infer_unique_ElimType Σ).
Proof.
  eapply bidir_ind.
  all: rewrite /infer_to_typing_ElimType //=.
  all: intros.
  all: try now (econstructor; eauto with fmap pcuic).
  - depelim X. congruence.
  - depelim X. congruence.
  - depelim X2.
    specialize (H _ i) as [= <-].
    destruct X0 as (_ & ? & X0 & <- & _).
    destruct l as (_ & ? & X0' & <- & _).
    specialize (X0 _ X0') as [= <-].
    reflexivity.
  - depelim X2. by specialize (H _ X2) as <-.
  - depelim X1. by specialize (H _ _ _ i) as [= <- <- <-].
  - destruct X1.
    specialize (H _ X1) as <-.
    eapply RtP_inj; eassumption.
  - destruct X1.
    specialize (H _ X1) as <-.
    eapply RtS_inj; eassumption.
Qed.

Theorem infer_unique {TC RtP RtS} Σ {Pre : BidirUniquePrecondition RtP RtS Σ} Γ t T T' :
  Σ ;;; Γ ⊢ t ▹ T -> Σ ;;; Γ ⊢ t ▹ T' -> T = T'.
Proof.
  intros H H'.
  apply infer_unique_all in H; tas.
  by eapply H.
Qed.

Class TypingPrincipalPrecondition {TC} Σ := {
  TypPrin_RtP : RedtoPi;
  TypPrin_RtS : RedtoSort;
  TypPrin_TyptoBD ::> TypingBidirPrecondition TC TypPrin_RtP TypPrin_RtS Σ;
  TypPrin_BDtoTyp ::> BidirToTypingPrecondition TC TypPrin_RtP TypPrin_RtS Σ;
  TypPrin_BDuniq ::> BidirUniquePrecondition TypPrin_RtP TypPrin_RtS Σ;
  }.
Arguments TypingPrincipalPrecondition : clear implicits.

Theorem typing_principality {TC} Σ (Pre : TypingPrincipalPrecondition TC Σ) Γ t T :
  Σ ;;; Γ ⊢ t : T ->
  ∑ T, Σ ;;; Γ ⊢ t : T ×
  forall U,
  Σ ;;; Γ ⊢ t : U -> Σ ;;; Γ ⊢ T ≤T U.
Proof.
  intro.
  eapply typing_wf_local in X as wfΓ.
  eapply typing_to_check in X as [T₀ X _]. 2: tc.
  clear T.
  exists T₀.
  split.
  - unshelve epose proof (infer_to_typing Σ _) as X'; tc.
    eapply BDXinfer in X'; tea. now cbn in X'.
  - intros U X'.
    eapply typing_to_check in X' as [T₀' X' XR]. 2: tc.
    eapply infer_unique with (2 := X) in X' as <-. 2: tc.
    assumption.
Qed.

Theorem typing_two {TC} Σ (Pre : TypingPrincipalPrecondition TC Σ) Γ t T₁ T₂ :
  Σ ;;; Γ ⊢ t : T₁ ->
  Σ ;;; Γ ⊢ t : T₂ ->
  ∑ T, Σ ;;; Γ ⊢ t : T ×
  Σ ;;; Γ ⊢ T ≤T T₁ ×
  Σ ;;; Γ ⊢ T ≤T T₂.
Proof.
  intros.
  apply typing_principality in X as X'; tas.
  destruct X' as (T & HT & Hm).
  exists T; split; tas.
  split; auto.
Qed.




Section Closure.
Local Set Elimination Schemes.

Context {TC} Σ (R R' : forall (Γ : context) (t t' T : term), Type).

Notation " Σ ;;; Γ ⊢ t ~R t' : T " := (R Γ t t' T) (only parsing).
Notation " Σ ;;; Γ ⊢ t ~R' t' : T " := (R' Γ t t' T) (only parsing).

Inductive red0 Γ : forall (t t' T : term), Type :=
  | red0_beta na A t T u :
      lift_typing typing Σ Γ (j_vass na A) ->
      Σ ;;; Γ ,, vass na A ⊢ t : T ->
      Σ ;;; Γ ⊢ u : A ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ~>0 t { 0 := u } : T { 0 := u }
where " Σ ;;; Γ ⊢ t ~>0 t' : T " := (@red0 Γ t t' T) (only parsing).
Derive Signature for red0.

Inductive pred0 Γ : forall (t t' T : term), Type :=
  | pred0_beta na A t t' T u u' :
      lift_typing typing Σ Γ (j_vass na A) ->
      Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T ->
      Σ ;;; Γ ⊢ u ~R u' : A ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ≡>0 t' { 0 := u' } : T { 0 := u }
where " Σ ;;; Γ ⊢ t ≡>0 t' : T " := (@pred0 Γ t t' T) (only parsing).
Derive Signature for pred0.

Inductive pred0ε Γ : forall (t t' T : term), Σ ;;; Γ ⊢ t ≡>0 t' : T -> Type :=
  | pred0ε_beta na A t t' T u u' :
      [(Xj: lift_typing typing Σ Γ (j_vass na A))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T)] ->
      [(IXt : Σ ;;; Γ ,, vass na A ⊢ t ~R' t' : T)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' : A)] ->
      [(IXu : Σ ;;; Γ ⊢ u ~R' u' : A)] ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ≡>0 t' { 0 := u' } : T { 0 := u } on ⌈pred0_beta⌋ with R'
where " Σ ;;; Γ ⊢ t ≡>0 t' : T 'on' p 'with' R'" := (@pred0ε Γ t t' T p) (only parsing).
Derive Signature for pred0ε.

Inductive ext_conv Γ : forall (t u T : term), Type :=
  | ext_eta t u na A B :
      lift_typing typing Σ Γ (j_vass na A) ->
      Σ ;;; Γ ⊢ t : tProd na A B ->
      Σ ;;; Γ ⊢ u : tProd na A B ->
      Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ~R tApp (lift0 1 u) (tRel 0) : B ->
      Σ ;;; Γ ⊢ t ~ext u : tProd na A B

  | ext_sprop t u T :
      Σ ;;; Γ ⊢ t : T ->
      Σ ;;; Γ ⊢ u : T ->
      Σ ;;; Γ ⊢ T : tSort sSProp ->
      Σ ;;; Γ ⊢ t ~ext u : T
where " Σ ;;; Γ ⊢ t ~ext t' : T " := (@ext_conv Γ t t' T) (only parsing).
Derive Signature for ext_conv.

Inductive ext_convε Γ : forall (t u T : term), Σ ;;; Γ ⊢ t ~ext u : T -> Type :=
  | extε_eta t u na A B :
      [(Xj : lift_typing typing Σ Γ (j_vass na A))] ->
      [(Xt : Σ ;;; Γ ⊢ t : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ⊢ u : tProd na A B)] ->
      [(XR : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ~R tApp (lift0 1 u) (tRel 0) : B)] ->
      [(IXR : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ~R' tApp (lift0 1 u) (tRel 0) : B)] ->
      Σ ;;; Γ ⊢ t ~ext u : tProd na A B on ⌈ext_eta⌋ with R'

  | extε_sprop t u T :
      [(Xt : Σ ;;; Γ ⊢ t : T)] ->
      [(Xu : Σ ;;; Γ ⊢ u : T)] ->
      [(XT : Σ ;;; Γ ⊢ T : tSort sSProp)] ->
      Σ ;;; Γ ⊢ t ~ext u : T on ⌈ext_sprop⌋ with R'
where " Σ ;;; Γ ⊢ t ~ext t' : T 'on' p 'with' R'" := (@ext_convε Γ t t' T p) (only parsing).

Inductive ext_eq Γ : forall (t u T : term), Type :=
  | ext_eta_l t u na A B :
      [(Xj : lift_typing typing Σ Γ (j_vass na A))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t : B)] ->
      [(Xu : Σ ;;; Γ ⊢ u : tProd na A B)] ->
      [(XR : Σ ;;; Γ ,, vass na A ⊢ t ~R tApp (lift0 1 u) (tRel 0) : B)] ->
      Σ ;;; Γ ⊢ tLambda na A t =ext u : tProd na A B

  | ext_eta_r t u na A B :
      [(Xj : lift_typing typing Σ Γ (j_vass na A))] ->
      [(Xt : Σ ;;; Γ ⊢ t : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ,, vass na A ⊢ u : B)] ->
      [(XR : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ~R u : B)] ->
      Σ ;;; Γ ⊢ t =ext tLambda na A u : tProd na A B

  | ext_eq_sprop t u T :
      [(Xt : Σ ;;; Γ ⊢ t : T)] ->
      [(Xu : Σ ;;; Γ ⊢ u : T)] ->
      [(XT : Σ ;;; Γ ⊢ T : tSort sSProp)] ->
      Σ ;;; Γ ⊢ t =ext u : T
where " Σ ;;; Γ ⊢ t =ext t' : T " := (@ext_eq Γ t t' T) (only parsing).
Derive Signature for ext_eq.

Inductive ext_eqε Γ : forall (t u T : term), Σ ;;; Γ ⊢ t =ext u : T -> Type :=
  | extε_eta_l t u na A B :
      [(Xj : lift_typing typing Σ Γ (j_vass na A))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t : B)] ->
      [(Xu : Σ ;;; Γ ⊢ u : tProd na A B)] ->
      [(XR : Σ ;;; Γ ,, vass na A ⊢ t ~R tApp (lift0 1 u) (tRel 0) : B)] ->
      [(IXR : Σ ;;; Γ ,, vass na A ⊢ t ~R' tApp (lift0 1 u) (tRel 0) : B)] ->
      Σ ;;; Γ ⊢ tLambda na A t =ext u : tProd na A B on ⌈ext_eta_l⌋ with R'

  | extε_eta_r t u na A B :
      [(Xj : lift_typing typing Σ Γ (j_vass na A))] ->
      [(Xt : Σ ;;; Γ ⊢ t : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ,, vass na A ⊢ u : B)] ->
      [(XR : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ~R u : B)] ->
      [(IXR : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ~R' u : B)] ->
      Σ ;;; Γ ⊢ t =ext tLambda na A u : tProd na A B on ⌈ext_eta_r⌋ with R'

  | extε_eq_sprop t u T :
      [(Xt : Σ ;;; Γ ⊢ t : T)] ->
      [(Xu : Σ ;;; Γ ⊢ u : T)] ->
      [(XT : Σ ;;; Γ ⊢ T : tSort sSProp)] ->
      Σ ;;; Γ ⊢ t =ext u : T on ⌈ext_eq_sprop⌋ with R'
where " Σ ;;; Γ ⊢ t =ext t' : T 'on' p 'with' R'" := (@ext_eqε Γ t t' T p) (only parsing).
Derive Signature for ext_eqε.

Inductive context_closure Rα Rs Γ : forall (t t' T : term), Type :=
  | clos_rel n decl :
      [(wfΓ : wf_local Σ Γ)] ->
      [(hnth : nth_error Γ n = Some decl)] ->
      Σ ;;; Γ ⊢ tRel n ~ tRel n : lift0 (S n) decl.(decl_type)

  | clos_lambda na na' A A' t t' T s :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' : tProd na A T

  | clos_app na A B t t' u u' :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' : A)] ->
      Σ ;;; Γ ⊢ tApp t u ~ tApp t' u' : B { 0 := u }

  | clos_prod na na' A A' B B' s s' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B' : tSort s')] ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B' : tSort (Sort.sort_of_product s s')

  | clos_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' : tSort (Sort.super s')
where " Σ ;;; Γ ⊢ t ~ t' : T " := (context_closure _ _ Γ t t' T) (only parsing).
Notation " Σ ;;; Γ ⊢ t ~ t' : T 'with' R , R' , R'' " := (@context_closure R' R'' Γ t t' T) (only parsing).
Derive Signature for context_closure.

Inductive context_closureε Rα Rs Γ : forall (t t' T : term), Σ ;;; Γ ⊢ t ~ t' : T with R, Rα, Rs -> Type :=
  | closε_rel n decl :
      [(wfΓ : wf_local Σ Γ)] ->
      [(hnth : nth_error Γ n = Some decl)] ->
      Σ ;;; Γ ⊢ tRel n ~ tRel n : lift0 (S n) decl.(decl_type) on ⌈clos_rel⌋ with R'

  | closε_lambda na na' A A' t t' T s :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T)] ->
      [(IXt : Σ ;;; Γ ,, vass na A ⊢ t ~R' t' : T)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' : tProd na A T on ⌈clos_lambda⌋ with R'

  | closε_app na A B t t' u u' :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' : tProd na A B)] ->
      [(IXt : Σ ;;; Γ ⊢ t ~R' t' : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' : A)] ->
      [(IXu : Σ ;;; Γ ⊢ u ~R' u' : A)] ->
      Σ ;;; Γ ⊢ tApp t u ~ tApp t' u' : B { 0 := u } on ⌈clos_app⌋ with R'

  | closε_prod na na' A A' B B' s s' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B' : tSort s')] ->
      [(IXB : Σ ;;; Γ ,, vass na A ⊢ B ~R' B' : tSort s')] ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B' : tSort (Sort.sort_of_product s s') on ⌈clos_prod⌋ with R'

  | closε_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' : tSort (Sort.super s') on ⌈clos_sort⌋ with R'
where " Σ ;;; Γ ⊢ t ~ t' : T 'on' p 'with' R'" := (context_closureε _ _ Γ t t' T p) (only parsing).
Derive Signature for context_closureε.

Inductive context1_closure Γ : forall (t t' T : term), Type :=
  | clos1_lamty na A A' t T s :
      Σ ;;; Γ ⊢ A ~R A' : tSort s ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ t : T ->
      Σ ;;; Γ ⊢ tLambda na A t ~1 tLambda na A' t : tProd na A T

  | clos1_lamtm na A t t' T :
      lift_typing typing Σ Γ (j_vass na A) ->
      Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T ->
      Σ ;;; Γ ⊢ tLambda na A t ~1 tLambda na A t' : tProd na A T

  | clos1_appl na A B t t' u :
      Σ ;;; Γ ⊢ t ~R t' : tProd na A B ->
      Σ ;;; Γ ⊢ u : A ->
      Σ ;;; Γ ⊢ tApp t u ~1 tApp t' u : B { 0 := u }

  | clos1_appr na A B t u u' :
      Σ ;;; Γ ⊢ t : tProd na A B ->
      Σ ;;; Γ ⊢ u ~R u' : A ->
      Σ ;;; Γ ⊢ tApp t u ~1 tApp t u' : B { 0 := u }

  | clos1_proddom na A A' B s s' :
      Σ ;;; Γ ⊢ A ~R A' : tSort s ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ B : tSort s' ->
      Σ ;;; Γ ⊢ tProd na A B ~1 tProd na A' B : tSort (Sort.sort_of_product s s')

  | clos1_prodcodom na A B B' s s' :
      lift_typing typing Σ Γ (j_vass_s na A s) ->
      Σ ;;; Γ ,, vass na A ⊢ B ~R B' : tSort s' ->
      Σ ;;; Γ ⊢ tProd na A B ~1 tProd na A B' : tSort (Sort.sort_of_product s s')
where " Σ ;;; Γ ⊢ t ~1 t' : T " := (context1_closure Γ t t' T) (only parsing).

Inductive context1_closureε Γ : forall (t t' T : term), Σ ;;; Γ ⊢ t ~1 t' : T -> Type :=
  | clos1ε_lamty na A A' t T s :
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(Xtt : Σ ;;; Γ ,, vass na A ⊢ t : T)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~1 tLambda na A' t : tProd na A T on ⌈clos1_lamty⌋ with R'

  | clos1ε_lamtm na A t t' T :
      [(Xj : lift_typing typing Σ Γ (j_vass na A))] ->
      [(XA : Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T)] ->
      [(IXA : Σ ;;; Γ ,, vass na A ⊢ t ~R' t' : T)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~1 tLambda na A t' : tProd na A T on ⌈clos1_lamtm⌋ with R'

  | clos1ε_appl na A B t t' u :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' : tProd na A B)] ->
      [(IXt : Σ ;;; Γ ⊢ t ~R' t' : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ⊢ u : A)] ->
      Σ ;;; Γ ⊢ tApp t u ~1 tApp t' u : B { 0 := u } on ⌈clos1_appl⌋ with R'

  | clos1ε_appr na A B t u u' :
      [(Xt : Σ ;;; Γ ⊢ t : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' : A)] ->
      [(IXu : Σ ;;; Γ ⊢ u ~R' u' : A)] ->
      Σ ;;; Γ ⊢ tApp t u ~1 tApp t u' : B { 0 := u } on ⌈clos1_appr⌋ with R'

  | clos1ε_proddom na A A' B s s' :
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B : tSort s')] ->
      Σ ;;; Γ ⊢ tProd na A B ~1 tProd na A' B : tSort (Sort.sort_of_product s s') on ⌈clos1_proddom⌋ with R'

  | clos1ε_prodcodom na A B B' s s' :
      [(Xj : lift_typing typing Σ Γ (j_vass_s na A s))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B' : tSort s')] ->
      [(IXB : Σ ;;; Γ ,, vass na A ⊢ B ~R' B' : tSort s')] ->
      Σ ;;; Γ ⊢ tProd na A B ~1 tProd na A B' : tSort (Sort.sort_of_product s s') on ⌈clos1_prodcodom⌋ with R'
where " Σ ;;; Γ ⊢ t ~1 t' : T 'on' p 'with' R'" := (context1_closureε Γ t t' T p) (only parsing).


Inductive head_context1_closure Γ : forall (t t' T : term), Type :=
  | hclos1_appl na A B t t' u :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ⊢ u : A)] ->
      Σ ;;; Γ ⊢ tApp t u ~h1 tApp t' u : B { 0 := u }
where " Σ ;;; Γ ⊢ t ~h1 t' : T " := (head_context1_closure Γ t t' T) (only parsing).
Derive Signature for head_context1_closure.

Inductive head_context1_closureε Γ : forall (t t' T : term), Σ ;;; Γ ⊢ t ~h1 t' : T -> Type :=
  | hclos1ε_appl na A B t t' u :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' : tProd na A B)] ->
      [(IXt : Σ ;;; Γ ⊢ t ~R' t' : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ⊢ u : A)] ->
      Σ ;;; Γ ⊢ tApp t u ~h1 tApp t' u : B { 0 := u } on ⌈hclos1_appl⌋ with R'
where " Σ ;;; Γ ⊢ t ~h1 t' : T 'on' p 'with' R'" := (head_context1_closureε Γ t t' T p) (only parsing).
End Closure.

(* Begin Closure renotations *)
  Notation " Σ ;;; Γ ⊢ t ~>0 t' : T " := (@red0 _ Σ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ≡>0 t' : T " := (@pred0 _ Σ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ≡>0 t' : T 'on' p 'with' R'" := (@pred0ε _ Σ _ R' Γ t t' T p).
  Notation " Σ ;;; Γ ⊢ t ≡>0 t' : T 'with' R " := (@pred0 _ Σ R Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t ~ext t' : T " := (@ext_conv _ Σ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ~ext t' : T 'on' p 'with' R'" := (@ext_convε _ Σ _ R' Γ t t' T p).
  Notation " Σ ;;; Γ ⊢ t ~ext t' : T 'with' R " := (@ext_conv _ Σ R Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t =ext t' : T " := (@ext_eq _ Σ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t =ext t' : T 'on' p 'with' R'" := (@ext_eqε _ Σ _ R' Γ t t' T p).
  Notation " Σ ;;; Γ ⊢ t =ext t' : T 'with' R " := (@ext_eq _ Σ R Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t ~ t' : T " := (@context_closure _ Σ _ _ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ~ t' : T 'on' p 'with' R'" := (@context_closureε _ Σ _ R' _ _ Γ t t' T p).
  Notation " Σ ;;; Γ ⊢ t ~ t' : T 'with' R , R' , R'' " := (@context_closure _ Σ R R' R'' Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t ~1 t' : T " := (@context1_closure _ Σ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ~1 t' : T 'on' p 'with' R'" := (@context1_closureε _ Σ _ R' Γ t t' T p).
  Notation " Σ ;;; Γ ⊢ t ~1 t' : T 'with' R " := (@context1_closure _ Σ R Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t ~h1 t' : T " := (@head_context1_closure _ Σ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ~h1 t' : T 'on' p 'with' R'" := (@head_context1_closureε _ Σ _ R' Γ t t' T p).
  Notation " Σ ;;; Γ ⊢ t ~h1 t' : T 'with' R " := (@head_context1_closure _ Σ R Γ t t' T) (only parsing).
(* End Closure notations *)

Lemma pred0_toε {TC} Σ R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ≡>0 t' : T with R)] ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ≡>0 t' : T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma pred0_ofε {TC} Σ R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ≡>0 t' : T with R)] ->
  [(X : Σ ;;; Γ ⊢ t ≡>0 t' : T on p with R')] ->
  Σ ;;; Γ ⊢ t ≡>0 t' : T with R'.
Proof.
  intros.
  induction X.
  all: now econstructor.
Defined.

Lemma pred0ε_fmap {TC} Σ R R' R'' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ≡>0 t' : T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ≡>0 t' : T on p with R')] ->
  [(X Γ t t' T : R' Γ t t' T -> R'' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ≡>0 t' : T on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma ext_conv_toε {TC} Σ R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ext t' : T with R)] ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~ext t' : T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma ext_conv_ofε {TC} Σ R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ext t' : T with R)] ->
  [(X : Σ ;;; Γ ⊢ t ~ext t' : T on p with R')] ->
  Σ ;;; Γ ⊢ t ~ext t' : T with R'.
Proof.
  intros.
  induction X.
  all: try now econstructor.
Defined.

Lemma ext_conv_fmap {TC} Σ R R' Γ t t' T :
  [(H : Σ ;;; Γ ⊢ t ~ext t' : T with R)] ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~ext t' : T with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma ext_convε_fmap {TC} Σ R R' R'' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ext t' : T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ~ext t' : T on p with R')] ->
  [(X Γ t t' T : R' Γ t t' T -> R'' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~ext t' : T on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma ext_eq_toε {TC} Σ R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t =ext t' : T with R)] ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t =ext t' : T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma ext_eq_ofε {TC} Σ R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t =ext t' : T with R)] ->
  [(X : Σ ;;; Γ ⊢ t =ext t' : T on p with R')] ->
  Σ ;;; Γ ⊢ t =ext t' : T with R'.
Proof.
  intros.
  induction X.
  all: try now econstructor.
Defined.

Lemma ext_eq_fmap {TC} Σ R R' Γ t t' T :
  [(H : Σ ;;; Γ ⊢ t =ext t' : T with R)] ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t =ext t' : T with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma ext_eqε_fmap {TC} Σ R R' R'' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t =ext t' : T with R)] ->
  [(H : Σ ;;; Γ ⊢ t =ext t' : T on p with R')] ->
  [(X Γ t t' T : R' Γ t t' T -> R'' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t =ext t' : T on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closure_toε {TC} Σ R R' Rα Rs Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ t' : T with R, Rα, Rs)] ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~ t' : T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closure_ofε {TC} Σ R R' Rα Rs Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ t' : T with R, Rα, Rs)] ->
  [(X : Σ ;;; Γ ⊢ t ~ t' : T on p with R')] ->
  Σ ;;; Γ ⊢ t ~ t' : T with R', Rα, Rs.
Proof.
  intros.
  induction X.
  all: try now econstructor.
Defined.

Lemma context_closureε_fmap {TC} Σ R R' R'' Rα Rs Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ t' : T with R, Rα, Rs)] ->
  [(H : Σ ;;; Γ ⊢ t ~ t' : T on p with R')] ->
  [(X Γ t t' T : R' Γ t t' T -> R'' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~ t' : T on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closure_fmap {TC} Σ R R' Rα Rs Rα' Rs' Γ t t' T :
  [(H : Σ ;;; Γ ⊢ t ~ t' : T with R, Rα, Rs)] ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  [(Xα na na' : Rα na na' -> Rα' na na')] ->
  [(Xs s s' : Rs s s' -> Rs' s s')] ->
  Σ ;;; Γ ⊢ t ~ t' : T with R', Rα', Rs'.
Proof.
  intros H X Xα Xs.
  induction H.
  all: try now econstructor.
Defined.

Lemma context1_closure_toε {TC} Σ R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~1 t' : T with R)] ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~1 t' : T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context1_closure_ofε {TC} Σ R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~1 t' : T with R)] ->
  [(X : Σ ;;; Γ ⊢ t ~1 t' : T on p with R')] ->
  Σ ;;; Γ ⊢ t ~1 t' : T with R'.
Proof.
  intros.
  induction X.
  all: try now econstructor.
Defined.

Lemma context1_closureε_fmap {TC} Σ R R' R'' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~1 t' : T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ~1 t' : T on p with R')] ->
  [(X Γ t t' T : R' Γ t t' T -> R'' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~1 t' : T on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma head_context1_closure_toε {TC} Σ R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~h1 t' : T with R)] ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~h1 t' : T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma head_context1_closure_ofε {TC} Σ R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~h1 t' : T with R)] ->
  [(X : Σ ;;; Γ ⊢ t ~h1 t' : T on p with R')] ->
  Σ ;;; Γ ⊢ t ~h1 t' : T with R'.
Proof.
  intros.
  induction X.
  all: try now econstructor.
Defined.

Lemma head_context1_closureε_fmap {TC} Σ R R' R'' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~h1 t' : T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ~h1 t' : T on p with R')] ->
  [(X Γ t t' T : R' Γ t t' T -> R'' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~h1 t' : T on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.


Hint Resolve pred0_toε pred0_ofε pred0ε_fmap ext_conv_toε ext_conv_ofε ext_convε_fmap
  ext_eq_toε ext_eq_ofε ext_eqε_fmap
  context_closure_toε context_closure_ofε context_closureε_fmap
  context1_closure_toε context1_closure_ofε context1_closureε_fmap
  head_context1_closure_toε head_context1_closure_ofε head_context1_closureε_fmap
  : fmap.



Inductive hred1 {TC} Σ Γ : forall (t t' T : term), Type :=
  | hred1_red0 t u T :
      Σ ;;; Γ ⊢ t ~>0 u : T ->
      Σ ;;; Γ ⊢ t ~>h u : T

  | hred1_cumul t u T U :
      Σ ;;; Γ ⊢ t ~>h u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t ~>h u : U

  | hred1_clos1 t u T :
      Σ ;;; Γ ⊢ t ~h1 u : T with hred1 Σ ->
      Σ ;;; Γ ⊢ t ~>h u : T
where " Σ ;;; Γ ⊢ t ~>h t' : T " := (@hred1 _ Σ Γ t t' T).
Derive Signature for hred1.

Instance TC_compat_hred1 TC Σ Γ t u : TC_compat TC Σ Γ (hred1 Σ Γ t u). by now econstructor. Defined.

Definition hred1_rect TC Σ P :
  [(Xred0 Γ t u T : Σ ;;; Γ ⊢ t ~>0 u : T -> P Γ t u T)] ->
  [(XCumul Γ t u A B :
      Σ ;;; Γ ⊢ t ~>h u : A ->
      P Γ t u A ->
      Σ ;;; Γ ⊢ A ≤T B with TC ->
      P Γ t u B )] ->
  [(XClosure Γ t u T :
      [(Htu : Σ ;;; Γ ⊢ t ~h1 u : T with hred1 Σ)] ->
      [(Xtu : Σ ;;; Γ ⊢ t ~h1 u : T on Htu with P)] ->
      P Γ t u T )] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t ~>h u : T)] -> P Γ t u T.
Proof.
  intros.
  revert Γ t u T X.
  fix Xrec 5.
  intros Γ t_ u_ T_ []; try clear t_; try clear u_; try clear T_.
  - apply Xred0; eauto.
  - eapply XCumul; eauto.
  - unshelve eapply XClosure; eauto with fmap.
Defined.
Definition hred1_ind := hred1_rect.

Inductive red1 {TC} Σ Γ : forall (t t' T : term), Type :=
  | red1_red0 t u T :
      Σ ;;; Γ ⊢ t ~>0 u : T ->
      Σ ;;; Γ ⊢ t ~>1 u : T

  | red1_cumul t u T U :
      Σ ;;; Γ ⊢ t ~>1 u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t ~>1 u : U

  | red1_clos1 t u T :
      Σ ;;; Γ ⊢ t ~1 u : T with red1 Σ ->
      Σ ;;; Γ ⊢ t ~>1 u : T
where " Σ ;;; Γ ⊢ t ~>1 t' : T " := (@red1 _ Σ Γ t t' T).

Instance TC_compat_red1 TC Σ Γ t u : TC_compat TC Σ Γ (red1 Σ Γ t u). by now econstructor. Defined.

Definition red1_rect cf TC Σ P :
  [(Xred0 Γ t u T : Σ ;;; Γ ⊢ t ~>0 u : T -> P Γ t u T)] ->
  [(XCumul Γ t u A B :
      Σ ;;; Γ ⊢ t ~>1 u : A ->
      P Γ t u A ->
      Σ ;;; Γ ⊢ A ≤T B with TC ->
      P Γ t u B )] ->
  [(XClosure Γ t u T :
      Σ ;;; Γ ⊢ t ~1 u : T with P ->
      P Γ t u T )] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t ~>1 u : T)] -> P Γ t u T.
Proof.
  intros.
  revert Γ t u T X.
  fix Xrec 5.
  intros Γ t_ u_ T_ []; try clear t_; try clear u_; try clear T_.
  - apply Xred0; eauto.
  - eapply XCumul; eauto.
  - eapply XClosure. now unshelve eauto with fmap.
Defined.

Inductive pred1 {TC} Σ Γ t u T : Type :=
  | pred1_pred0 :
      Σ ;;; Γ ⊢ t ≡>0 u : T with pred1 Σ ->
      Σ ;;; Γ ⊢ t ≡>1 u : T

  | pred1_cumul T' :
      Σ ;;; Γ ⊢ t ≡>1 u : T' ->
      Σ ;;; Γ ⊢ T' ≤T T ->
      Σ ;;; Γ ⊢ t ≡>1 u : T

  | pred1_clos :
      Σ ;;; Γ ⊢ t ~ u : T with pred1 Σ, eq, eq ->
      Σ ;;; Γ ⊢ t ≡>1 u : T
where " Σ ;;; Γ ⊢ t ≡>1 t' : T " := (@pred1 _ Σ Γ t t' T).
Derive Signature for pred1.

Instance TC_compat_pred1 TC Σ Γ t u : TC_compat TC Σ Γ (pred1 Σ Γ t u). by now econstructor. Defined.

Definition pred1_rect TC Σ P :
  [(Xpred0 Γ t u T :
      [(H : Σ ;;; Γ ⊢ t ≡>0 u : T with pred1 Σ)] ->
      [(X : Σ ;;; Γ ⊢ t ≡>0 u : T on H with P)] ->
      P Γ t u T)] ->
  [(XCumul Γ t u A B :
      Σ ;;; Γ ⊢ t ≡>1 u : A ->
      P Γ t u A ->
      Σ ;;; Γ ⊢ A ≤T B with TC ->
      P Γ t u B )] ->
  [(XClosure Γ t u T :
      [(H : Σ ;;; Γ ⊢ t ~ u : T with pred1 Σ, eq, eq)] ->
      [(X : Σ ;;; Γ ⊢ t ~ u : T on H with P)] ->
      P Γ t u T )] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t ≡>1 u : T)] -> P Γ t u T.
Proof.
  intros.
  revert Γ t u T X.
  fix Xrec 5.
  intros Γ t_ u_ T_ []; try clear t_; try clear u_; try clear T_.
  - unshelve eapply Xpred0; eauto with fmap.
  - eapply XCumul; eauto.
  - unshelve eapply XClosure; tea. now eauto with fmap.
Defined.

Definition pred1_elim TC Σ Γ t u P :
  [(Xpred0 T U :
      [(X : Σ ;;; Γ ⊢ t ≡>0 u : T with pred1 Σ)] ->
      [(XT : Σ ;;; Γ ⊢ T ≤* U)] ->
      P U)] ->
  [(XClosure T U :
      [(X : Σ ;;; Γ ⊢ t ~ u : T with pred1 Σ, eq, eq)] ->
      [(XT : Σ ;;; Γ ⊢ T ≤* U)] ->
      P U)] ->

  forall T, [(X : Σ ;;; Γ ⊢ t ≡>1 u : T)] -> P T.
Proof.
  intros.
  set U := T.
  have : Σ ;;; Γ ⊢ T ≤* U by reflexivity.
  move: U.
  induction X => // U.
  - now apply Xpred0.
  - intro; apply IHX; tas.
    now eapply TCI_step.
  - now apply XClosure.
Defined.

Inductive hred {TC} Σ Γ : forall (t t' T : term), Type :=
  | hred_refl t T :
      Σ ;;; Γ ⊢ t : T ->
      Σ ;;; Γ ⊢ t ~>h* t : T

  | hred_step t u v T :
      Σ ;;; Γ ⊢ t ~>h u : T ->
      Σ ;;; Γ ⊢ u ~>h* v : T ->
      Σ ;;; Γ ⊢ t ~>h* v : T

  | hred_cumul t u T U :
      Σ ;;; Γ ⊢ t ~>h* u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t ~>h* u : U
where " Σ ;;; Γ ⊢ t ~>h* t' : T " := (@hred _ Σ Γ t t' T).

Derive Signature for hred.

Instance TC_compat_hred TC Σ Γ t u : TC_compat TC Σ Γ (hred Σ Γ t u). by now econstructor. Defined.

Definition hred_rect TC Σ P :
  [(Xrefl Γ t T :
      Σ ;;; Γ ⊢ t : T ->
      P Γ t t T)] ->
  [(Xstep Γ t u v T :
      Σ ;;; Γ ⊢ t ~>h u : T ->
      Σ ;;; Γ ⊢ u ~>h* v : T ->
      P Γ u v T ->
      P Γ t v T)] ->
  [(XCumul Γ t u A B :
      Σ ;;; Γ ⊢ t ~>h* u : A ->
      P Γ t u A ->
      Σ ;;; Γ ⊢ A ≤T B with TC ->
      P Γ t u B )] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t ~>h* u : T)] -> P Γ t u T.
Proof.
  intros.
  revert Γ t u T X.
  fix Xrec 5.
  intros Γ t_ u_ T_ []; try clear t_; try clear u_; try clear T_.
  - apply Xrefl; eauto with fmap.
  - eapply Xstep; eauto.
  - eapply XCumul; eauto.
Defined.


Inductive red {TC} Σ Γ : forall (t t' T : term), Type :=
  | red_red0 t u T :
      Σ ;;; Γ ⊢ t ~>0 u : T ->
      Σ ;;; Γ ⊢ t ~> u : T

  | red_trans t u v T :
      Σ ;;; Γ ⊢ t ~> u : T ->
      Σ ;;; Γ ⊢ u ~> v : T ->
      Σ ;;; Γ ⊢ t ~> v : T

  | red_cumul t u T U :
      Σ ;;; Γ ⊢ t ~> u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t ~> u : U

  | red_clos t u T :
      Σ ;;; Γ ⊢ t ~ u : T with red Σ, eq, eq ->
      Σ ;;; Γ ⊢ t ~> u : T
where " Σ ;;; Γ ⊢ t ~> t' : T " := (@red _ Σ Γ t t' T).

Instance TC_compat_red TC Σ Γ t u : TC_compat TC Σ Γ (red Σ Γ t u). by now econstructor. Defined.

Definition red_rect cf TC Σ P :
  [(Xred0 Γ t u T :
      Σ ;;; Γ ⊢ t ~>0 u : T ->
      P Γ t u T)] ->
  [(Xtrans Γ t u v T :
      Σ ;;; Γ ⊢ t ~> u : T ->
      P Γ t u T ->
      Σ ;;; Γ ⊢ u ~> v : T ->
      P Γ u v T ->
      P Γ t v T)] ->
  [(XCumul Γ t u A B :
      Σ ;;; Γ ⊢ t ~> u : A ->
      P Γ t u A ->
      Σ ;;; Γ ⊢ A ≤T B with TC ->
      P Γ t u B )] ->
  [(XClosure Γ t u T :
      [(p : Σ ;;; Γ ⊢ t ~ u : T with red Σ, eq, eq)] ->
      [(IX : Σ ;;; Γ ⊢ t ~ u : T on p with P)] ->
      P Γ t u T )] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t ~> u : T)] -> P Γ t u T.
Proof.
  intros.
  revert Γ t u T X.
  fix Xrec 5.
  intros Γ t_ u_ T_ []; try clear t_; try clear u_; try clear T_.
  - apply Xred0; eauto with fmap.
  - eapply Xtrans; eauto.
  - eapply XCumul; eauto.
  - unshelve eapply XClosure; eauto with fmap.
Defined.

Section CumulAddon.
Local Set Elimination Schemes.

Context {cf} {TC} Σ (R R' : forall (Γ : context) (pb : conv_pb) (t t' T : term), Type).

Notation "Σ ;;; Γ ⊢ t ≤R[ pb ] t' : T" := (R Γ pb t t' T) (only parsing).
Notation "Σ ;;; Γ ⊢ t ≤R'[ pb ] t' : T" := (R' Γ pb t t' T) (only parsing).
Notation "Σ ;;; Γ ⊢ t =R t' : T" := (R Γ Conv t t' T) (only parsing).
Notation "Σ ;;; Γ ⊢ t =R' t' : T" := (R' Γ Conv t t' T) (only parsing).

Inductive cumul_addon Γ pb : forall (t t' T : term), Type :=
  | cumul_prod na na' A A' B B' s s' :
      [(Xα : eq_binder_annot na na')] ->
      [(XA : Σ ;;; Γ ⊢ A =R A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ≤R[pb] B' : tSort s')] ->
      Σ ;;; Γ ⊢ tProd na A B ≤c[pb] tProd na' A' B' : tSort (Sort.sort_of_product s s')

  | cumul_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs' : wf_sort Σ s')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      Σ ;;; Γ ⊢ tSort s ≤c[pb] tSort s' : tSort (Sort.super s')
  (* | (indapp) *)
where "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T" := (@cumul_addon Γ pb t t' T) (only parsing).
Derive Signature for cumul_addon.

Inductive cumul_addonε Γ pb : forall (t t' T : term), Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T -> Type :=
  | cumulε_prod na na' A A' B B' s s' :
      [(Xα : eq_binder_annot na na')] ->
      [(XA : Σ ;;; Γ ⊢ A =R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A =R' A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ≤R[pb] B' : tSort s')] ->
      [(IXB : Σ ;;; Γ ,, vass na A ⊢ B ≤R'[pb] B' : tSort s')] ->
      Σ ;;; Γ ⊢ tProd na A B ≤c[pb] tProd na' A' B' : tSort (Sort.sort_of_product s s') on ⌈cumul_prod⌋ with R'

  | cumulε_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs' : wf_sort Σ s')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      Σ ;;; Γ ⊢ tSort s ≤c[pb] tSort s' : tSort (Sort.super s') on ⌈cumul_sort⌋ with R'
  (* | (indapp) *)
where "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'on' p 'with' R'" := (@cumul_addonε Γ pb t t' T p) (only parsing).

End CumulAddon.
Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T" := (@cumul_addon _ _ Σ _ Γ pb t t' T).
Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'with' R" := (@cumul_addon _ _ Σ R Γ pb t t' T) (only parsing).
Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'on' p 'with' R'" := (@cumul_addonε _ _ Σ _ R' Γ pb t t' T p).

Lemma cumul_addon_toε {cf} {TC} Σ R R' Γ pb t u T :
  [(H : Σ ;;; Γ ⊢ t ≤c[pb] u : T with R)] ->
  [(X Γ pb t u T : R Γ pb t u T -> R' Γ pb t u T)] ->
  Σ ;;; Γ ⊢ t ≤c[pb] u : T on H with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_ofε {cf} {TC} Σ R R' Γ pb t u T :
  [(p : Σ ;;; Γ ⊢ t ≤c[pb] u : T with R)] ->
  [(X : Σ ;;; Γ ⊢ t ≤c[pb] u : T on p with R')] ->
  Σ ;;; Γ ⊢ t ≤c[pb] u : T with R'.
Proof.
  intros.
  induction X.
  all: try now econstructor.
Defined.

Lemma cumul_addonε_fmap {cf} {TC} Σ R R' R'' Γ pb t u T :
  [(p : Σ ;;; Γ ⊢ t ≤c[pb] u : T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ≤c[pb] u : T on p with R')] ->
  [(X Γ pb t u T : R' Γ pb t u T -> R'' Γ pb t u T)] ->
  Σ ;;; Γ ⊢ t ≤c[pb] u : T on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_fmap {cf} {TC} Σ R R' Γ pb t u T :
  [(H : Σ ;;; Γ ⊢ t ≤c[pb] u : T with R)] ->
  [(X Γ pb t u T : R Γ pb t u T -> R' Γ pb t u T)] ->
  Σ ;;; Γ ⊢ t ≤c[pb] u : T with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_clos {cf} {TC} Σ R Γ t u T :
  Σ ;;; Γ ⊢ t ≤c[Conv] u : T with R ->
  Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => R Γ Conv), eq_binder_annot, eq_sort Σ.
Proof.
  induction 1.
  all: now econstructor.
Defined.

Lemma cumul_addon_clos_fmap {cf} {TC} Σ R R' Γ t u T :
  [(H : Σ ;;; Γ ⊢ t ≤c[Conv] u : T with R)] ->
  [(X Γ t u T : R Γ Conv t u T -> R' Γ t u T)] ->
  Σ ;;; Γ ⊢ t ~ u : T with R', eq_binder_annot, eq_sort Σ.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_clos_on {cf} {TC} Σ R R' Γ t u T :
  [(p : Σ ;;; Γ ⊢ t ≤c[Conv] u : T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ≤c[Conv] u : T on p with R')] ->
  Σ ;;; Γ ⊢ t ~ u : T on (ltac:(apply cumul_addon_clos with (1 := p))) with (fun Γ => R' Γ Conv).
Proof.
  intros p H.
  induction H.
  all: now econstructor.
Qed.


Lemma cumul_addon_clos_onε {cf} {TC} Σ R R' R'' Γ t u T :
  [(p : Σ ;;; Γ ⊢ t ≤c[Conv] u : T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ≤c[Conv] u : T on p with R')] ->
  [(X Γ t u T : R' Γ Conv t u T -> R'' Γ t u T)] ->
  Σ ;;; Γ ⊢ t ~ u : T on (ltac:(apply cumul_addon_clos with (1 := p))) with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Hint Resolve cumul_addon_toε cumul_addon_ofε cumul_addonε_fmap : fmap.

Inductive equality {cf} {TC} Σ Γ pb t t' T  :=
  | eq_ext :
      [(X : Σ ;;; Γ ⊢ t =ext t' : T with (fun Γ => equality Σ Γ Conv))] ->
      Σ ;;; Γ ⊢ t <=[pb] t' : T
  | eq_cumul_addon :
      [(X : Σ ;;; Γ ⊢ t ≤c[pb] t' : T with equality Σ)] ->
      Σ ;;; Γ ⊢ t <=[pb] t' : T
  | eq_cumul T₀ :
      [(X : Σ ;;; Γ ⊢ t <=[pb] t' : T₀)] ->
      [(XT : Σ ;;; Γ ⊢ T₀ ≤T T)] ->
      Σ ;;; Γ ⊢ t <=[pb] t' : T
  | eq_clos :
      [(X : Σ ;;; Γ ⊢ t ~ t' : T with (fun Γ => equality Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
      Σ ;;; Γ ⊢ t <=[pb] t' : T
where " Σ ;;; Γ ⊢ t <=[ pb ] t' : T " := (@equality _ _ Σ Γ pb t t' T).
Derive Signature for equality.

Instance TC_compat_equality cf TC Σ Γ pb t u : TC_compat TC Σ Γ (equality Σ Γ pb t u). by now econstructor. Defined.

Definition equality_rect cf TC Σ P :
  [(Xext Γ pb t u T :
      [(X : Σ ;;; Γ ⊢ t =ext u : T with (fun Γ => equality Σ Γ Conv))] ->
      [(IX : Σ ;;; Γ ⊢ t =ext u : T on X with (fun Γ => P Γ Conv))] ->
      P Γ pb t u T)] ->
  [(XCumulAddon Γ pb t u T :
      [(X : Σ ;;; Γ ⊢ t ≤c[pb] u : T with equality Σ)] ->
      [(IX : Σ ;;; Γ ⊢ t ≤c[pb] u : T on X with P)] ->
      P Γ pb t u T)] ->
  [(XCumul Γ pb t u T U :
      Σ ;;; Γ ⊢ t <=[pb] u : T ->
      P Γ pb t u T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      P Γ pb t u U )] ->
  [(XClosure Γ pb t u T :
      [(X : Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => equality Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
      [(IX : Σ ;;; Γ ⊢ t ~ u : T on X with (fun Γ => P Γ Conv))] ->
      P Γ pb t u T )] ->

  forall Γ pb t u T, [(X : Σ ;;; Γ ⊢ t <=[pb] u : T)] -> P Γ pb t u T.
Proof.
  intros.
  revert Γ pb t u T X.
  fix Xrec 6.
  intros Γ pb_ t_ u_ T_ []; try clear pb_; try clear t_; try clear u_; try clear T_.
  - unshelve eapply Xext; eauto with fmap.
  - unshelve eapply XCumulAddon; eauto with fmap.
  - eapply XCumul; eauto.
  - unshelve eapply XClosure; eauto with fmap.
Defined.

Definition equality_elim cf TC Σ Γ pb t u P :
  [(Xext T U :
      [(X : Σ ;;; Γ ⊢ t =ext u : T with (fun Γ => equality Σ Γ Conv))] ->
      Σ ;;; Γ ⊢ T ≤* U ->
      P U)] ->
  [(XCumulAddon T U :
      [(X : Σ ;;; Γ ⊢ t ≤c[pb] u : T with equality Σ)] ->
      Σ ;;; Γ ⊢ T ≤* U ->
      P U)] ->
  [(XClosure T U :
      [(X : Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => equality Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
      Σ ;;; Γ ⊢ T ≤* U ->
      P U )] ->

  forall T, [(X : Σ ;;; Γ ⊢ t <=[pb] u : T)] -> P T.
Proof.
  intros.
  set U := T.
  have : Σ ;;; Γ ⊢ T ≤* U by reflexivity.
  move: U.
  induction X => ?.
  - eapply Xext; eauto.
  - eapply XCumulAddon; eauto.
  - intro. apply IHX; tas. now eapply TCI_step.
  - eapply XClosure; eauto.
Defined.

Definition equality_Conv_rect cf TC Σ P :
  [(Xext Γ t u T :
      [(X : Σ ;;; Γ ⊢ t =ext u : T with (fun Γ => equality Σ Γ Conv))] ->
      [(IX : Σ ;;; Γ ⊢ t =ext u : T on X with P)] ->
      P Γ t u T)] ->
  [(XCumul Γ t u T U :
      Σ ;;; Γ ⊢ t <=[Conv] u : T ->
      P Γ t u T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      P Γ t u U )] ->
  [(XClosure Γ t u T :
      [(X : Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => equality Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
      [(IX : Σ ;;; Γ ⊢ t ~ u : T on X with P)] ->
      P Γ t u T )] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t <=[Conv] u : T)] -> P Γ t u T.
Proof.
  intros.
  remember Conv as pb eqn:e in X. revert e.
  induction X => e; subst pb.
  - unshelve eapply Xext; eauto with fmap.
  - eapply cumul_addon_clos_on in IX.
    eapply XClosure.
    now eapply context_closureε_fmap in IX.
  - eapply XCumul; eauto.
  - eapply XClosure. eauto with fmap.
Defined.

Definition equality_Conv_elim cf TC Σ Γ t u P :
  [(Xext T U :
      [(X : Σ ;;; Γ ⊢ t =ext u : T with (fun Γ => equality Σ Γ Conv))] ->
      Σ ;;; Γ ⊢ T ≤* U ->
      P U)] ->
  [(XClosure T U :
      [(X : Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => equality Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
      Σ ;;; Γ ⊢ T ≤* U ->
      P U )] ->

  forall T, [(X : Σ ;;; Γ ⊢ t <=[Conv] u : T)] -> P T.
Proof.
  intros.
  set U := T.
  have : Σ ;;; Γ ⊢ T ≤* U by reflexivity.
  move: Γ t u T X Xext XClosure U.
  apply (equality_Conv_rect _ _ Σ (fun Γ t u T => _ -> _ -> forall U, Σ ;;; Γ ⊢ T ≤* U -> P U)); intros.
  - eapply X0; eauto.
  - apply X0; tas. now eapply TCI_step.
  - eapply X1; eauto.
Defined.

Inductive conv {cf} {TC} Σ Γ (pb : conv_pb) : forall (t t' T : term), Type :=
  | conv_hred_l t t' u T :
      Σ ;;; Γ ⊢ t ~>h t' : T ->
      Σ ;;; Γ ⊢ t' <==[pb] u : T ->
      Σ ;;; Γ ⊢ t <==[pb] u : T

  | conv_hred_r t u u' T :
      Σ ;;; Γ ⊢ u ~>h u' : T ->
      Σ ;;; Γ ⊢ t <==[pb] u' : T ->
      Σ ;;; Γ ⊢ t <==[pb] u : T

  | conv_ext t u T :
      Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ => conv Σ Γ Conv) ->
      Σ ;;; Γ ⊢ t <==[pb] u : T

  | conv_cumul_addon t u T :
      Σ ;;; Γ ⊢ t ≤c[pb] u : T with conv Σ ->
      Σ ;;; Γ ⊢ t <==[pb] u : T

  | conv_cumul t u T U :
      Σ ;;; Γ ⊢ t <==[pb] u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t <==[pb] u : U

  | conv_clos t u T :
      Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ ->
      Σ ;;; Γ ⊢ t <==[pb] u : T
where " Σ ;;; Γ ⊢ t <==[ pb ] t' : T " := (@conv _ _ Σ Γ pb t t' T)
and " Σ ;;; Γ ⊢ t <== t' : T " := (@conv _ _ Σ Γ Cumul t t' T)
and " Σ ;;; Γ ⊢ t === t' : T " := (@conv _ _ Σ Γ Conv t t' T).
Derive Signature for conv.

Instance TC_compat_conv cf TC Σ Γ pb t u : TC_compat TC Σ Γ (conv Σ Γ pb t u). by now econstructor. Defined.

Definition conv_rect cf TC Σ P :
  [(XRed0L Γ pb t t' u T :
      Σ ;;; Γ ⊢ t ~>h t' : T ->
      Σ ;;; Γ ⊢ t' <==[pb] u : T ->
      P Γ pb t' u T ->
      P Γ pb t u T)] ->
  [(XRed0R Γ pb t u u' T :
      Σ ;;; Γ ⊢ u ~>h u' : T ->
      Σ ;;; Γ ⊢ t <==[pb] u' : T ->
      P Γ pb t u' T ->
      P Γ pb t u T)] ->
  [(Xext Γ pb t u T :
      [(H : Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ => conv Σ Γ Conv))] ->
      [(X : Σ ;;; Γ ⊢ t ~ext u : T on H with (fun Γ => P Γ Conv))] ->
      P Γ pb t u T)] ->
  [(XCumulAddon Γ pb t u T :
      [(H : Σ ;;; Γ ⊢ t ≤c[pb] u : T with conv Σ)] ->
      [(X : Σ ;;; Γ ⊢ t ≤c[pb] u : T on H with P)] ->
      P Γ pb t u T)] ->
  [(XCumul Γ pb t u T U :
      Σ ;;; Γ ⊢ t <==[pb] u : T ->
      P Γ pb t u T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      P Γ pb t u U )] ->
  [(XClosure Γ pb t u T :
      [(H : Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
      [(X : Σ ;;; Γ ⊢ t ~ u : T on H with (fun Γ => P Γ Conv))] ->
      P Γ pb t u T )] ->

  forall Γ pb t u T, [(X : Σ ;;; Γ ⊢ t <==[pb] u : T)] -> P Γ pb t u T.
Proof.
  intros.
  revert Γ pb t u T X.
  fix Xrec 6.
  intros Γ pb_ t_ u_ T_ []; try clear pb_; try clear t_; try clear u_; try clear T_.
  - eapply XRed0L; eauto.
  - eapply XRed0R; eauto.
  - unshelve eapply Xext; eauto with fmap.
  - unshelve eapply XCumulAddon; eauto with fmap.
  - eapply XCumul; eauto.
  - unshelve eapply XClosure; eauto with fmap.
Defined.

Definition conv_Conv_rect cf TC Σ P :
  [(XRed0L Γ t t' u T :
      Σ ;;; Γ ⊢ t ~>h t' : T ->
      Σ ;;; Γ ⊢ t' === u : T ->
      P Γ t' u T ->
      P Γ t u T)] ->
  [(XRed0R Γ t u u' T :
      Σ ;;; Γ ⊢ u ~>h u' : T ->
      Σ ;;; Γ ⊢ t === u' : T ->
      P Γ t u' T ->
      P Γ t u T)] ->
  [(Xext Γ t u T :
      [(p : Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ => conv Σ Γ Conv))] ->
      [(IX : Σ ;;; Γ ⊢ t ~ext u : T on p with P)] ->
      P Γ t u T)] ->
  [(XCumul Γ t u T U :
      Σ ;;; Γ ⊢ t === u : T ->
      P Γ t u T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      P Γ t u U )] ->
  [(XClosure Γ t u T :
      [(p : Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
      [(IX : Σ ;;; Γ ⊢ t ~ u : T on p with P)] ->
      P Γ t u T )] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t === u : T)] -> P Γ t u T.
Proof.
  intros.
  remember Conv as pb eqn:e in X.
  induction X in e; subst pb.
  - eapply XRed0L; eauto.
  - eapply XRed0R; eauto.
  - unshelve eapply Xext; eauto with fmap.
  - eapply cumul_addon_clos_on in X.
    eapply XClosure.
    now eapply context_closureε_fmap in X.
  - eapply XCumul; eauto.
  - eapply XClosure. eauto with fmap.
Defined.

Local Set Elimination Schemes.
Inductive conv' {cf} {TC} Σ Γ (pb : conv_pb) : forall (t t' T : term), Type :=
  | conv'_pred1_l t t' u T :
      Σ ;;; Γ ⊢ t ≡>1 t' : T ->
      Σ ;;; Γ ⊢ t' <===[pb] u : T ->
      Σ ;;; Γ ⊢ t <===[pb] u : T

  | conv'_pred1_r t u u' T :
      Σ ;;; Γ ⊢ u ≡>1 u' : T ->
      Σ ;;; Γ ⊢ t <===[pb] u' : T ->
      Σ ;;; Γ ⊢ t <===[pb] u : T

  | conv'_eq t u T :
      Σ ;;; Γ ⊢ t <=[pb] u : T ->
      Σ ;;; Γ ⊢ t <===[pb] u : T
where " Σ ;;; Γ ⊢ t <===[ pb ] t' : T " := (@conv' _ _ Σ Γ pb t t' T).
Unset Elimination Schemes.
Derive Signature for conv'.

Instance TC_compat_conv' cf TC Σ Γ pb t u : TC_compat TC Σ Γ (conv' Σ Γ pb t u).
Proof. intros T U X. induction 1. 1,2: econstructor; [|eapply IHX0]; tea. 3: constructor. all: eapply tc_compat; tc; tea. Defined.

Inductive conv_spec_alt {cf} {TC} Σ Γ (pb : conv_pb) : forall (t t' T : term), Type :=
  | conv_alt_sym t u T :
      Σ ;;; Γ ⊢ u ≡ t : T ->
      Σ ;;; Γ ⊢ t ≦[pb] u : T

  | conv_alt_trans t u v T :
      Σ ;;; Γ ⊢ t ≦[pb] u : T ->
      Σ ;;; Γ ⊢ u ≦[pb] v : T ->
      Σ ;;; Γ ⊢ t ≦[pb] v : T

  | conv_alt_red0 t u T :
      Σ ;;; Γ ⊢ t ~>0 u : T ->
      Σ ;;; Γ ⊢ t ≦[pb] u : T

  | conv_alt_ext t u T :
      Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ => conv_spec_alt Σ Γ Conv) ->
      Σ ;;; Γ ⊢ t ≦[pb] u : T

  | conv_alt_cumul_addon t u T :
      Σ ;;; Γ ⊢ t ≤c[pb] u : T with conv_spec_alt Σ ->
      Σ ;;; Γ ⊢ t ≦[pb] u : T

  | conv_alt_cumul t u T U :
      Σ ;;; Γ ⊢ t ≦[pb] u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t ≦[pb] u : U

  | conv_alt_clos t u T :
      Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => conv_spec_alt Σ Γ Conv), eq_binder_annot, eq_sort Σ ->
      Σ ;;; Γ ⊢ t ≦[pb] u : T
where " Σ ;;; Γ ⊢ t ≦[ pb ] t' : T " := (@conv_spec_alt _ _ Σ Γ pb t t' T)
and " Σ ;;; Γ ⊢ t ≦ t' : T " := (@conv_spec_alt _ _ Σ Γ Cumul t t' T)
and " Σ ;;; Γ ⊢ t ≡ t' : T " := (@conv_spec_alt _ _ Σ Γ Conv t t' T).

Instance TC_compat_conv_spec_alt cf TC Σ Γ pb t u : TC_compat TC Σ Γ (conv_spec_alt Σ Γ pb t u). by now econstructor. Defined.

Notation "`≡`" := (fun Σ Γ t t' T => Σ ;;; Γ ⊢ t ≡ t' : T).

Lemma conv_alt_eq_pb {cf} {TC} Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t ≡ u : T ->
  Σ ;;; Γ ⊢ t ≦[ pb ] u : T.
Proof. intro; now do 2 apply conv_alt_sym. Defined.

Lemma conv_alt_pb_Cumul {cf} {TC} Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t ≦[ pb ] u : T ->
  Σ ;;; Γ ⊢ t ≦ u : T.
Proof. destruct pb => //. apply conv_alt_eq_pb. Defined.

Definition conv_spec_alt_rect cf TC Σ P :
  [(XSym Γ pb t u T :
      Σ ;;; Γ ⊢ u ≡ t : T ->
      P Γ Conv u t T ->
      P Γ pb t u T)] ->
  [(XTrans Γ pb t u v T :
      Σ ;;; Γ ⊢ t ≦[pb] u : T ->
      P Γ pb t u T ->
      Σ ;;; Γ ⊢ u ≦[pb] v : T ->
      P Γ pb u v T ->
      P Γ pb t v T)] ->
  [(XRed0 Γ pb t u T :
      Σ ;;; Γ ⊢ t ~>0 u : T ->
      P Γ pb t u T)] ->
  [(Xext Γ pb t u T :
      [(H : Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ => conv_spec_alt Σ Γ Conv))] ->
      [(X : Σ ;;; Γ ⊢ t ~ext u : T on H with (fun Γ => P Γ Conv))] ->
      P Γ pb t u T)] ->
  [(XCumulAddon Γ pb t u T :
      [(H : Σ ;;; Γ ⊢ t ≤c[pb] u : T with conv_spec_alt Σ)] ->
      [(X : Σ ;;; Γ ⊢ t ≤c[pb] u : T on H with P)] ->
      P Γ pb t u T)] ->
  [(XCumul Γ pb t u T U :
      Σ ;;; Γ ⊢ t ≦[pb] u : T ->
      P Γ pb t u T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      P Γ pb t u U )] ->
  [(XClosure Γ pb t u T :
      [(H : Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => conv_spec_alt Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
      [(X : Σ ;;; Γ ⊢ t ~ u : T on H with (fun Γ => P Γ Conv))] ->
      P Γ pb t u T )] ->

  forall Γ pb t u T, [(X : Σ ;;; Γ ⊢ t ≦[pb] u : T)] -> P Γ pb t u T.
Proof.
  intros.
  revert Γ pb t u T X.
  fix Xrec 6.
  intros Γ pb_ t_ u_ T_ []; try clear pb_; try clear t_; try clear u_; try clear T_.
  - eapply XSym; eauto.
  - eapply XTrans; eauto.
  - eapply XRed0; eauto.
  - unshelve eapply Xext; eauto with fmap.
  - unshelve eapply XCumulAddon; eauto with fmap.
  - eapply XCumul; eauto.
  - unshelve eapply XClosure; eauto with fmap.
Defined.

Lemma conv_spec_alt_wf_local {cf TC} Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t ≦[ pb ] u : T ->
  wf_local Σ Γ.
Proof.
  induction 1; auto.
  - induction X; eauto using typing_wf_local.
  - induction X; eauto using typing_wf_local.
  - induction X; eauto using typing_wf_local.
  - induction X; eauto using typing_wf_local.
Qed.

Definition typing_alt_rect TC Σ P :
  [(XClosure Γ t T :
      [(H : Σ ;;; Γ ⊢ t ~ t : T with (fun Γ t _ T => typing Σ Γ t T), eq, eq)] ->
      [(X : Σ ;;; Γ ⊢ t ~ t : T on H with P)] ->
      P Γ t t T )] ->
  [(XCumul Γ t T U :
      Σ ;;; Γ ⊢ t : T ->
      P Γ t t T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      P Γ t t U )] ->
  forall Γ t T, [(X : Σ ;;; Γ ⊢ t : T)] -> P Γ t t T.
Proof.
  intros.
  revert Γ t T X.
  induction 1 using typing_rect with (Pj := lift_typing1 (fun Γ t T => Σ ;;; Γ ⊢ t : T × P Γ t t T)) (PΓ := fun _ => True).
  all: try eauto with fmap.
  - eapply XClosure.
    constructor.
    Unshelve. all: eassumption.
  - eapply XClosure.
    constructor.
    Unshelve. all: tea; cbnr.
  - destruct IHX as (_ & ? & (X' & IHX) & <- & Hs2).
    eapply XClosure.
    constructor.
    Unshelve. all: tea; cbnr.
  - destruct IHX as (_ & s & (X' & IHX) & _ & Hs2).
    eapply XClosure.
    constructor.
    Unshelve. all: tea; cbnr.
  - eapply XClosure.
    constructor.
    Unshelve. all: tea; cbnr.
Defined.

Class Instantiable typing := {
  instantiate : forall Γ t T σ Δ,
    typing Γ t T ->
    welltyped_inst typing Γ σ Δ ->
    typing Δ t.[σ] T.[σ]
}.

Notation TypingInst Σ := (Instantiable (typing Σ)).

Class TCFromCompareSort {TC} Σ R := {
  TC_from_compare_sort Γ s s' :
    wf_local Σ Γ -> wf_sort Σ s -> wf_sort Σ s' ->
    R s s' ->
    Σ ;;; Γ ⊢ tSort s ≤T tSort s';
  TC_super s s' : R s s' -> R (Sort.super s) (Sort.super s')
}.

Class TCFromCompareProd {TC} Σ R := {
  TC_from_compare_prod Γ na na' A A' s T :
      eq_binder_annot na na' -> R Γ A A' (tSort s) ->
      Σ ;;; Γ ⊢ tProd na' A' T ≤T tProd na A T;
}.

Class TCFromCompareSubst10 {TC} Σ R := {
  TC_from_compare_subst10 Γ (A B u u' : term) :
      R Γ u u' A ->
      Σ ;;; Γ ⊢ B {0 := u'} ≤T B {0 := u};
}.

Class ConvToTypPrecondition {cf TC} Σ := {
    CTT_typing_inst :: TypingInst Σ;
    CTT_CC :: ContextComparator;
    CTT_context_change :: ContextChangeable (typing Σ) Σ;
    CTT_typed_refl :: CCTypedRefl CTT_CC TC Σ;
    CTT_TCIsCmpType :: TCIsCmpType Σ;
    CTT_cmp_type :: RevImpliesTC Σ (fun Γ t u T => Σ ;;; Γ ⊢ t ≡ u : T);
    CTT_cmp_sort pb :: TCFromCompareSort Σ (compare_sort Σ pb);
    CTT_cmp_prod :: TCFromCompareProd Σ (fun Γ t u T => Σ ;;; Γ ⊢ t ≡ u : T);
    CTT_cmp_inst :: TCFromCompareSubst10 Σ (fun Γ t u T => Σ ;;; Γ ⊢ t ≡ u : T);
  }.
Arguments ConvToTypPrecondition : clear implicits.

Instance red0_typing_left {TC} Σ : LeftTyping (fun Γ t u T => Σ ;;; Γ ⊢ t ~>0 u : T) Σ.
Proof.
  constructor.
  induction 1.
  - econstructor; tea.
    (* 1: by todo "Additional hypothesis for tApp". *)
    econstructor; tea.
    (* Unshelve. by todo "Additional hypothesis for tApp". *)
Qed.

Instance red0_typing_right {TC} Σ (Pre : TypingInst Σ) : RightTyping (fun Γ t u T => Σ ;;; Γ ⊢ t ~>0 u : T) Σ.
Proof.
  constructor.
  induction 1.
  - rewrite /subst1 !subst_inst.
    eapply instantiate; tea.
    eapply @welltyped_subst_inst with (Γ' := []) (Δ := [_]).
    + repeat constructor. rewrite subst_empty //.
    + apply typing_wf_local in t1 as wfΓ.
      constructor; tas.
    + clear. intros. rewrite /=/shiftk/= !subst_ids //.
Qed.

Lemma head_context1_closure_typing_left {TC} Σ P Γ t u T :
  [(onP Γ t u T : P Γ t u T -> Σ ;;; Γ ⊢ t : T)] ->
  [(X : Σ ;;; Γ ⊢ t ~h1 u : T with P)] ->
  Σ ;;; Γ ⊢ t : T.
Proof.
  intros.
  induction X.
  - apply onP in Xt.
    econstructor; tea.
    (* Unshelve. all: by todo "Additional hypothesis for tApp". *)
Qed.

Lemma head_context1_closure_typing_right {TC} Σ P Γ t u T :
  [(onP Γ t u T : P Γ t u T -> Σ ;;; Γ ⊢ u : T)] ->
  [(X : Σ ;;; Γ ⊢ t ~h1 u : T with P)] ->
  Σ ;;; Γ ⊢ u : T.
Proof.
  intros.
  induction X.
  - apply onP in Xt.
    econstructor; tea.
    (* Unshelve. all: by todo "Additional hypothesis for tApp". *)
Qed.

Instance hred1_typing_left {TC} Σ : LeftTyping (fun Γ t u T => Σ ;;; Γ ⊢ t ~>h u : T) Σ.
Proof.
  constructor.
  induction 1.
  - now eapply typing_left.
  - now econstructor.
  - now apply head_context1_closure_ofε, head_context1_closure_typing_left in Xtu.
Qed.

Instance hred1_typing_right {TC} Σ (Pre : TypingInst Σ) : RightTyping (fun Γ t u T => Σ ;;; Γ ⊢ t ~>h u : T) Σ.
Proof.
  constructor.
  induction 1.
  - now eapply typing_right.
  - now econstructor.
  - now apply head_context1_closure_ofε, head_context1_closure_typing_right in Xtu.
Qed.

From MetaCoq.PCUIC Require Import PCUICWfUniverses.

Lemma cumul_addon_typing_left {cf TC} Σ (Pre : forall pb, TCFromCompareSort Σ (compare_sort Σ pb)) P Γ pb t u T :
  [(onP Γ pb t u T : P Γ pb t u T -> Σ ;;; Γ ⊢ t : T)] ->
  [(X : Σ ;;; Γ ⊢ t ≤c[pb] u : T with P)] ->
  Σ ;;; Γ ⊢ t : T.
Proof.
  intros.
  induction X.
  - apply onP in XA, XB.
    have Xj : lift_typing typing Σ Γ (j_vass_s na A s).
    { repeat eexists; tea. }
    constructor; tas.
  - econstructor.
    1: now constructor.
    eapply TC_from_compare_sort; tas.
    1,2: by apply wf_sort_super.
    now apply compare_sort_super.
Qed.

Lemma convertible_contexts_snoc_vass {TC CC} Σ P Γ na na' A A' s :
  [(CCR : CCTypedRefl CC TC Σ)] ->
  [(ITC : RevImpliesTC Σ P)] ->
  [(TCCC : TCIsCmpType Σ)] ->
  wf_local Σ Γ ->
  eq_binder_annot na na' ->
  P Γ A A' (tSort s) ->
  Σ ⊢ Γ,, vass na' A' ≤Γ Γ,, vass na A.
Proof.
  intros.
  apply convertible_contexts_snoc.
  1: apply convertible_contexts_refl; tea.
  repeat constructor; cbn; tea.
  1: by symmetry.
  now eapply to_cmp_type, rto_tc.
Qed.




Lemma cumul_addon_typing_right {cf TC CC} Σ P P'
  (CCH : ContextChangeable (typing Σ) Σ)
  (CCR : CCTypedRefl CC TC Σ)
  (ITC : RevImpliesTC Σ (fun Γ t u T => P Γ Conv t u T))
  (TCCC : TCIsCmpType Σ)
    Γ pb t u T :
  [(onP' Γ pb t u T : P' Γ pb t u T -> Σ ;;; Γ ⊢ u : T)] ->
  [(X : Σ ;;; Γ ⊢ t ≤c[pb] u : T with P)] ->
  [(IX : Σ ;;; Γ ⊢ t ≤c[pb] u : T on X with P')] ->
  Σ ;;; Γ ⊢ u : T.
Proof.
  intros.
  induction IX.
  - apply onP' in IXA, IXB.
    have Xj' : lift_typing typing Σ Γ (j_vass_s na' A' s).
    { repeat eexists; tea. rewrite /= -Xα //. }
    constructor; tas.
    eapply change_context; tea.
    eapply convertible_contexts_snoc_vass with (P := fun Γ => P Γ Conv); tea.
    now eapply typing_wf_local.
  - econstructor; tas.
Qed.

Lemma context_closure_typing_left {TC} Σ Pα Ps P (Pre : TCFromCompareSort Σ Ps) Γ t u T :
  [(onP Γ t u T : P Γ t u T -> Σ ;;; Γ ⊢ t : T)] ->
  [(X : Σ ;;; Γ ⊢ t ~ u : T with P, Pα, Ps)] ->
  Σ ;;; Γ ⊢ t : T.
Proof.
  intros.
  induction X.
  - now econstructor.
  - apply onP in XA, Xt.
    have Xj : lift_typing typing Σ Γ (j_vass na A).
    { repeat eexists; tea. }
    econstructor; tea.
  - econstructor; eauto.
    (* * todo "Additional hypothesis for tApp". *)
      (* Unshelve. all: todo "Additional hypothesis for tApp". *)
  - apply onP in XA, XB.
    have Xj : lift_typing typing Σ Γ (j_vass_s na A s).
    { repeat eexists; tea. }
    econstructor; tea.
  - econstructor.
    1: now constructor.
    eapply TC_from_compare_sort; tas.
    1,2: by apply wf_sort_super.
    now apply TC_super.
Qed.

Lemma context_closure_typing_right {cf TC CC} Σ P P'
  (CCH : ContextChangeable (typing Σ) Σ)
  (CCR : CCTypedRefl CC TC Σ)
  (ITC : RevImpliesTC Σ P)
  (TCCC : TCIsCmpType Σ)
  (TCP : TCFromCompareProd Σ P)
  (TCS : TCFromCompareSubst10 Σ P)
  Γ t u T :
  [(onP' Γ t u T : P' Γ t u T -> Σ ;;; Γ ⊢ u : T)] ->
  [(X : Σ ;;; Γ ⊢ t ~ u : T with P, eq_binder_annot, eq_sort Σ)] ->
  [(IX : Σ ;;; Γ ⊢ t ~ u : T on X with P')] ->
  Σ ;;; Γ ⊢ u : T.
Proof.
  intros.
  induction IX.
  - now econstructor.
  - apply onP' in IXA, IXt.
    have Xj' : lift_typing typing Σ Γ (j_vass na' A').
    { repeat eexists; tea. rewrite /= -Xα //. }
    econstructor; tea.
    + econstructor; tea.
      eapply change_context; tea.
      eapply convertible_contexts_snoc_vass; tea.
      now eapply typing_wf_local.
    + now eapply TC_from_compare_prod.
  - econstructor; eauto.
    1: econstructor; eauto.
    (* * todo "Additional hypothesis for tApp". *)
      (* Unshelve. all: todo "Additional hypothesis for tApp". *)
    * now eapply TC_from_compare_subst10.
  - apply onP' in IXA, IXB.
    have Xj' : lift_typing typing Σ Γ (j_vass_s na' A' s).
    { repeat eexists; tea. rewrite /= -Xα //. }
    constructor; tas.
    eapply change_context; tea.
    eapply convertible_contexts_snoc_vass; tea.
    now eapply typing_wf_local.
  - now constructor.
Qed.

Lemma conv_spec_alt_typing {cf TC} Σ (Pre : ConvToTypPrecondition cf TC Σ) Γ pb t u T :
  Σ ;;; Γ ⊢ t ≦[pb] u : T ->
  Σ ;;; Γ ⊢ t : T × Σ ;;; Γ ⊢ u : T.
Proof.
  induction 1.
  - destruct IHX as [IHX IHX'].
    now split.
  - destruct IHX1 as [IHX1 IHX1'], IHX2 as [IHX2 IHX2'].
    now split.
  - split.
    + now eapply red0_typing_left.
    + eapply red0_typing_right; tea. exact _.
  - induction X.
    + now split.
    + now split.
  - split.
    + apply cumul_addon_ofε, cumul_addon_typing_left in X; tea; tc.
      cbn. now intros ?????[].
    + eapply cumul_addon_typing_right; tea; tc.
      cbn. now intros ?????[].
  - destruct IHX as [IHX IHX'].
    split.
    all: eapply type_cumul; tea.
  - split.
    + apply context_closure_ofε, context_closure_typing_left in X; tea.
      1: apply CTT_cmp_sort with (pb := Conv).
      cbn. now intros ????[].
    + eapply context_closure_typing_right; tea.
      all: change (fun Γ => conv_spec_alt Σ Γ Conv) with (fun Γ t u T => Σ ;;; Γ ⊢ t ≡ u : T).
      all: try exact _.
      cbn; now intros ????[].
Qed.

Instance ConvSpecAltLeft cf TC Σ pb : ConvToTypPrecondition cf TC Σ -> LeftTyping (fun Γ t u T => Σ ;;; Γ ⊢ t ≦[pb] u : T) Σ.
Proof.
  constructor. intros. now eapply fst, conv_spec_alt_typing.
Qed.
Instance ConvSpecAltLeftConv cf TC Σ pb : ConvToTypPrecondition cf TC Σ -> LeftConvTyping (conv_spec_alt Σ) Σ pb.
Proof.
  constructor. intros. now eapply fst, conv_spec_alt_typing.
Qed.
Instance ConvSpecAltRight cf TC Σ pb : ConvToTypPrecondition cf TC Σ -> RightTyping (fun Γ t u T => Σ ;;; Γ ⊢ t ≦[pb] u : T) Σ.
Proof.
  constructor. intros. now eapply snd, conv_spec_alt_typing.
Qed.
Instance ConvSpecAltRightConv cf TC Σ pb : ConvToTypPrecondition cf TC Σ -> RightConvTyping (conv_spec_alt Σ) Σ pb.
Proof.
  constructor. intros. now eapply snd, conv_spec_alt_typing.
Qed.




(* Spec Alt to regular spec *)

Class AltToSpecPrecondition cf TC Σ := {
  ATS_typed_refl :: TypedConvReflexivity (typed_conversion_spec Σ) Σ Conv
}.

Instance AltSoundPreconditionI {cf TC} Σ : AltToSpecPrecondition cf TC Σ := {| ATS_typed_refl := _ |}.

Lemma red0_to_spec {cf TC} Σ (PC : AltToSpecPrecondition cf TC Σ) Γ t u T :
  Σ ;;; Γ ⊢ t ~>0 u : T -> Σ ;;; Γ ⊢ t = u : T.
Proof.
  induction 1.
  - destruct l as (_ & s & HA & _ & Hs); cbn in *.
    econstructor 3; eauto.
    all: now eapply treflpb.
Qed.

Lemma ext_to_spec {cf TC} Σ (PC : AltToSpecPrecondition cf TC Σ) P Γ t u T :
  Σ ;;; Γ ⊢ t ~ext u : T with P ->
  [(XP Γ t u T : P Γ t u T -> Σ ;;; Γ ⊢ t = u : T)] ->
  Σ ;;; Γ ⊢ t = u : T.
Proof.
  intros H XP.
  induction H.
  - destruct l as (_ & s & HA & _ & Hs); cbn in *.
    econstructor 2.
    2: econstructor 2; revgoals.
    + eapply tc_eta; tea.
      all: now eapply treflpb.
    + eapply tc_sym, tc_eta; tea.
      all: now eapply treflpb.
    + eapply tc_lambda; trea.
      { now eapply treflpb. }
      now eapply XP.
    all: try eapply treflpb => //=.
  - eapply tc_sprop.
    all: try eapply treflpb => //=.
Qed.

Lemma cumul_addon_to_spec {cf TC} Σ P Γ pb t u T :
  Σ ;;; Γ ⊢ t ≤c[pb] u : T with P ->
  [(XP Γ pb t u T : P Γ pb t u T -> Σ ;;; Γ ⊢ t ≤[pb] u : T)] ->
  Σ ;;; Γ ⊢ t ≤[pb] u : T.
Proof.
  intros H XP.
  induction H.
  - eapply tc_prod; eauto.
  - eapply tc_sort; eauto.
Qed.

Lemma closure_to_spec {cf TC} Σ P Γ t u T :
  Σ ;;; Γ ⊢ t ~ u : T with P, eq_binder_annot, eq_sort Σ ->
  [(XP Γ t u T : P Γ t u T -> Σ ;;; Γ ⊢ t = u : T)] ->
  Σ ;;; Γ ⊢ t = u : T.
Proof.
  intros H XP.
  induction H.
  - now apply tc_rel.
  - eapply tc_lambda; eauto.
  - eapply tc_app; eauto.
  - eapply tc_prod; eauto.
  - eapply tc_sort; eauto.
Qed.

Lemma alt_sound {cf} {TC} Σ (PC : AltToSpecPrecondition cf TC Σ) Γ pb t u T :
  Σ ;;; Γ ⊢ t ≦[pb] u : T ->
  Σ ;;; Γ ⊢ t ≤[pb] u : T.
Proof.
  induction 1.
  - apply tc_sym; eauto.
  - eapply tc_trans; eauto.
  - apply tc_eq_pb.
    apply red0_to_spec; eauto.
  - apply tc_eq_pb.
    apply ext_conv_ofε in X.
    eapply ext_to_spec; eauto.
  - apply cumul_addon_ofε in X.
    eapply cumul_addon_to_spec; eauto.
  - eapply tc_cumul; eauto.
  - apply tc_eq_pb.
    apply context_closure_ofε in X.
    eapply closure_to_spec; eauto.
Qed.


(* Regular Spec to alt *)

Class SpecToAltPrecondition {cf TC} Σ := {
    STA_alt_typing :: LeftConvTyping (conv_spec_alt Σ) Σ Conv;
    STA_alt_inst : forall Γ pb t u T σ Δ,
      Σ ;;; Γ ⊢ t ≦[pb] u : T ->
      Σ ;;; Δ ⊢ σ : Γ wellsubst with typing ->
      Σ ;;; Δ ⊢ t.[σ] ≦[pb] u.[σ] : T.[σ];
    STA_typing_inst :: TypingInst Σ;
  }.
Arguments SpecToAltPrecondition : clear implicits.

Lemma beta_alt_complete {cf} {TC} Σ (PC : SpecToAltPrecondition cf TC Σ) Γ t na A T u s :
  isSortRel s (binder_relevance na) ->
  Σ ;;; Γ ⊢ A ≡ A : tSort s ->
  Σ ;;; Γ,, vass na A ⊢ t ≡ t : T ->
  Σ ;;; Γ ⊢ u ≡ u : A ->
  Σ ;;; Γ ⊢ tApp (tLambda na A t) u ≡ t {0 := u} : T {0 := u}.
Proof.
  intros Hs XA Xt Xu.
  eapply conv_alt_trans.
  - apply conv_alt_red0.
    econstructor.
    all: try now eapply typing_leftpb.
    repeat (eexists; cbn; tea).
    now eapply typing_leftpb.
  - unfold subst1. sigma.
    eapply STA_alt_inst; tea.
    rewrite Upn_0.
    eapply welltyped_subst0_inst with (Δ := [_]).
    + constructor. 1: constructor.
      rewrite subst_empty //.
      now eapply typing_leftpb.
    + intros.
      econstructor; tea.
      now eapply conv_spec_alt_wf_local.
Qed.

Lemma eta_alt_complete {cf} {TC} Σ (PC : SpecToAltPrecondition cf TC Σ) Γ t na A B s :
  Σ ;;; Γ ⊢ A : tSort s ->
  isSortRel s na.(binder_relevance) ->
  Σ ;;; Γ ⊢ t : tProd na A B ->
  Σ ;;; Γ ⊢ t ≡ tLambda na A (tApp (lift0 1 t) (tRel 0)) : tProd na A B.
Proof.
  intros X1 Hs X2.
  have wfΓ : wf_local Σ Γ by now eapply typing_wf_local.
  have wfj : lift_typing typing Σ Γ (j_vass na A).
  { repeat (eexists; cbn; tea). }
  eapply wf_local_snoc_vass in wfΓ as wfΓ'; tea.
  (* have [s' XProd] : ∑ s', Σ ;;; Γ ⊢ tProd na A B : tSort s'.
  { todo "Additional hypothesis for app". } *)
  have XL u T : Σ ;;; Γ ⊢ u : T -> Σ ;;; Γ ,, vass na A ⊢ lift0 1 u : lift0 1 T.
  { intro X.
    rewrite -> !lift0_rename, !rename_inst.
    eapply STA_typing_inst; tea.
    rewrite ren_rshiftk.
    eapply @welltyped_lift0_inst with (Δ := [_]).
    now constructor. }
  have XL' u T : Σ ;;; Γ ,, vass na A ⊢ u : T -> Σ ;;; (Γ ,, vass na A),, vass na (lift0 1 A) ⊢ lift 1 1 u : lift 1 1 T.
  { intro X.
    rewrite -> !(lift_rename 1 1), !rename_inst.
    eapply STA_typing_inst; tea.
    rewrite ren_lift_renaming.
    eapply @welltyped_lift_rename_inst with (Γ' := [vass na A]) (Δ := [_]).
    constructor; tea.
    cbn.
    constructor; tas.
    repeat eexists; cbn; tea.
    now apply XL in X1. }
  have /= X2b : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) : B.
  { replace B with ((lift 1 1 B) {0 := tRel 0}) by rewrite subst_rel0_lift //.
    econstructor; revgoals.
    - constructor; cbnr; eauto.
    - eapply XL in X2. eassumption. }
    (* - now apply XL in XProd. } *)

  apply conv_alt_sym.
  eapply conv_alt_ext, ext_eta; tea.
  { constructor; tea. }
  set (t' := tApp (lift0 1 t) (tRel 0)) in *.
  cbn -[t'].
  replace B with ((lift 1 1 B) {0 := tRel 0}) by rewrite subst_rel0_lift //.
  replace t' with ((lift 1 1 t') {0 := tRel 0}) at 2 by rewrite subst_rel0_lift //.
  eapply conv_alt_red0, red0_beta with (na := na); eauto.
  + repeat (eexists; cbnr; tea).
    change (tSort s) with (lift0 1 (tSort s)).
    now apply XL.
  + relativize (lift0 1 A).
    1: constructor. all: cbnr; eauto.
Qed.

Lemma alt_complete {cf} {TC} Σ (PC : SpecToAltPrecondition cf TC Σ) Γ pb t u T :
  Σ ;;; Γ ⊢ t ≤[pb] u : T ->
  Σ ;;; Γ ⊢ t ≦[pb] u : T.
Proof.
  induction 1.
  - apply conv_alt_sym; eauto.
  - eapply conv_alt_trans; eauto.
  - apply conv_alt_eq_pb. now eapply beta_alt_complete.
  - apply conv_alt_eq_pb.
    eapply eta_alt_complete; tea.
    all: now eapply typing_leftpb.
  - apply conv_alt_clos. eapply clos_rel; tas.
  - apply conv_alt_clos. eapply clos_lambda; tea.
  - apply conv_alt_clos. eapply clos_app; tea.
  - apply conv_alt_cumul_addon. eapply cumul_prod; tea.
  - apply conv_alt_cumul_addon. eapply cumul_sort; tea.
  - apply conv_alt_ext. apply ext_sprop.
    all: now eapply typing_leftpb.
  - now eapply conv_alt_cumul.
Qed.





Lemma head_context1_closure_context1_closure TC R Σ Γ t u T :
  Σ ;;; Γ ⊢ t ~h1 u : T with R ->
  Σ ;;; Γ ⊢ t ~1 u : T with R.
Proof.
  induction 1.
  all: try now econstructor.
Defined.

Lemma context1_closure_context_closure TC R Σ (Pre : TypedReflexivity R Σ) Γ t u T :
  Σ ;;; Γ ⊢ t ~1 u : T with R ->
  Σ ;;; Γ ⊢ t ~ u : T with R, eq, eq.
Proof.
  induction 1.
  all: try solve [ econstructor; trea; eauto using trefl ].
  - destruct l as (_ & s & HT & _ & Hs).
    econstructor; trea; eauto using trefl.
  - destruct l as (_ & ? & HT & <- & Hs).
    econstructor; trea; eauto using trefl.
Defined.

Lemma conv_alt_hred0 {cf} {TC} Σ (Pre : TypedConvReflexivity (conv_spec_alt Σ) Σ Conv) Γ t u T :
  Σ ;;; Γ ⊢ t ~>h u : T ->
  Σ ;;; Γ ⊢ t ≡ u : T.
Proof.
  induction 1.
  - apply conv_alt_red0. assumption.
  - now eapply conv_alt_cumul.
  - apply head_context1_closure_ofε, head_context1_closure_context1_closure, context1_closure_context_closure in Xtu.
    + apply conv_alt_clos.
      eapply context_closure_fmap; eauto.
      1,2: intros ?? <-; reflexivity.
    + now apply TypedConvReflexivity_to.
Qed.

Lemma conv_sound {cf} {TC} Σ (Pre : TypedConvReflexivity (conv_spec_alt Σ) Σ Conv) Γ pb t u T :
  Σ ;;; Γ ⊢ t <==[pb] u : T ->
  Σ ;;; Γ ⊢ t ≦[pb] u : T.
Proof.
  induction 1.
  - eapply conv_alt_trans; tea.
    apply conv_alt_eq_pb.
    apply conv_alt_hred0; assumption.
  - eapply conv_alt_trans; tea.
    apply conv_alt_sym.
    apply conv_alt_hred0; assumption.
  - apply conv_alt_ext.
    eauto with fmap.
  - apply conv_alt_cumul_addon.
    eauto with fmap.
  - now eapply conv_alt_cumul.
  - apply conv_alt_clos.
    eauto with fmap.
Qed.



Class SpecToConvPrecondition {cf TC} Σ := {
  STC_sym : forall Γ pb t u T, Σ ;;; Γ ⊢ u === t : T -> Σ ;;; Γ ⊢ t <==[pb] u : T;
  STC_trans : forall Γ pb t u v T, Σ ;;; Γ ⊢ t <==[pb] u : T -> Σ ;;; Γ ⊢ u <==[pb] v : T -> Σ ;;; Γ ⊢ t <==[pb] v : T;
  STC_SR_diag : forall Γ pb t u T, Σ ;;; Γ ⊢ t ~>0 u : T -> Σ ;;; Γ ⊢ u <==[pb] u : T;
  }.
Arguments SpecToConvPrecondition : clear implicits.

Lemma conv_complete {cf} {TC} Σ (PC : SpecToConvPrecondition cf TC Σ) Γ pb t u T :
  Σ ;;; Γ ⊢ t ≦[pb] u : T ->
  Σ ;;; Γ ⊢ t <==[pb] u : T.
Proof.
  induction 1.
  - now apply STC_sym.
  - now eapply STC_trans.
  - eapply conv_hred_l.
    1: now constructor.
    now eapply STC_SR_diag.
  - apply conv_ext.
    eauto with fmap.
  - apply conv_cumul_addon.
    eauto with fmap.
  - now eapply conv_cumul.
  - apply conv_clos.
    eauto with fmap.
Qed.


Instance TypedConvReflexivity_conv cf TC Σ : TypedConvReflexivity (conv Σ) Σ Conv.
Proof.
  constructor.
  induction 1 using typing_alt_rect with (P := fun Γ => conv Σ Γ Conv).
  - apply conv_clos.
    eapply context_closure_ofε, context_closure_fmap in X; tea; cbn; eauto.
    all: intros ?? <-; reflexivity.
  - now eapply conv_cumul.
Qed.


Lemma conv_eq_pb {cf} {TC} Σ Γ (pb : conv_pb) (t u T : term) :
  Σ ;;; Γ ⊢ t === u : T ->
  Σ ;;; Γ ⊢ t <==[pb] u : T.
Proof.
  intro H. revert Γ t u T H pb.
  apply (conv_Conv_rect _ _ Σ (fun Γ t u T => forall pb, Σ ;;; Γ ⊢ t <==[pb] u : T)).
  all: intros.
  all: try now econstructor.
Qed.

Lemma equality_eq_pb {cf} {TC} Σ Γ (pb : conv_pb) (t u T : term) :
  Σ ;;; Γ ⊢ t <=[Conv] u : T ->
  Σ ;;; Γ ⊢ t <=[pb] u : T.
Proof.
  intro H. revert Γ t u T H pb.
  apply (equality_Conv_rect _ _ Σ (fun Γ t u T => forall pb, Σ ;;; Γ ⊢ t <=[pb] u : T)).
  all: intros.
  all: try now econstructor.
Qed.

Class ConvSymPrecondition {cf TC} Σ := {
  CSP_CC :: ContextComparator;
  CSP_typed_refl :: CCTypedRefl CSP_CC TC Σ;
  CSP_TCCC :: TCIsCmpType Σ;
  CSP_context_change :: ContextChangeable2 (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T) Σ;
  CSP_implies_cmp_type :: RevImpliesTC Σ (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T);
  CSP_cmp_sort :: TCFromCompareSort Σ (eq_sort Σ);
  CSP_cmp_prod :: TCFromCompareProd Σ (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T);
  CSP_cmp_inst :: TCFromCompareSubst10 Σ (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T);
  }.
Arguments ConvSymPrecondition : clear implicits.

Lemma conv_wf_local {cf TC} Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t <==[pb] u : T ->
  wf_local Σ Γ.
Proof.
  induction 1; auto.
  - induction X; eauto using typing_wf_local.
  - induction X; eauto using typing_wf_local.
  - induction X; eauto using typing_wf_local.
Qed.

Instance conv_wf_local' cf TC Σ pb : ToWFLocal2Pb Σ (conv Σ) pb.
Proof.
  constructor. intro. apply conv_wf_local.
Qed.

Instance conv_wf_local'' cf TC Σ pb : ToWFLocal2 Σ (fun Γ => conv Σ Γ pb).
Proof.
  constructor. intro. apply conv_wf_local.
Qed.

Lemma eta_ext_sym {TC} Σ R Γ t u T :
  Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ t u T => R Γ u t T) ->
  Σ ;;; Γ ⊢ u ~ext t : T with R.
Proof.
  induction 1.
  all: try now econstructor.
Qed.

Definition map_term1 f Γ t :=
  match t with
  | tLambda na A t => tLambda na (f Γ A) (f (Γ ,, vass na A) t)
  | tProd na A B => tProd na (f Γ A) (f (Γ ,, vass na A) B)
  | tApp t u => tApp (f Γ t) (f Γ u)
  | _ => t
  end.


Lemma context_closure_sym_map_term1 {TC CC} Σ f P Pα Ps P'(* (PC : ConvSymPrecondition cf TC Σ) *) Γ t u T :
  [(CCH : ContextChangeable2 P Σ)] ->
  [(CCR : CCTypedRefl CC TC Σ)] ->
  [(TCCC : TCIsCmpType Σ)] ->
  [(CCP : RevImpliesTC Σ (fun Γ t u T => P Γ t u T))] ->
  [(PWF : ToWFLocal2 Σ P)] ->
  [(SymPα : Symmetric Pα)] ->
  [(onPα na na' : Pα na na' -> eq_binder_annot na na')] ->
  [(SymPs : Symmetric Ps)] ->
  [(PsTC : TCFromCompareSort Σ Ps)] ->
  [(PrTC : TCFromCompareProd Σ P)] ->
  [(STC : TCFromCompareSubst10 Σ P)] ->
  [(onP' Γ t u T : P' Γ t u T -> P Γ u (f Γ t) T)] ->
  [(X : Σ ;;; Γ ⊢ t ~ u : T with P, Pα, Ps)] ->
  [(IX : Σ ;;; Γ ⊢ t ~ u : T on X with (fun Γ t u T => P' Γ t u T))] ->
  ∑ T₀, Σ ;;; Γ ⊢ u ~ map_term1 f Γ t : T₀ with P, Pα, Ps × Σ ;;; Γ ⊢ T₀ ≤* T.
Proof.
  intros ???????????? X IX.
  induction IX.
  - eexists; split; trea.
    now apply clos_rel.
  - apply onPα in Xα as Xα'.
    eexists; split.
    1: eapply clos_lambda; tea; try by symmetry.
    + now eapply onP'.
    + rewrite -Xα' //.
    + eapply change_context2.
      1: now eapply onP'.
      eapply convertible_contexts_snoc_vass; tea.
      now eapply to_wf_local2.
    + apply TCI_one.
      eapply TC_from_compare_prod; tea.
  - eexists; split.
    1: eapply clos_app; tea.
    + now eapply onP'.
    + now eapply onP'.
    + apply TCI_one.
      now eapply TC_from_compare_subst10.
  - apply onPα in Xα as Xα'.
    eexists; split; trea.
    eapply clos_prod; tea; try by symmetry.
    + now eapply onP'.
    + rewrite -Xα' //.
    + eapply change_context2.
      1: now eapply onP'.
      eapply convertible_contexts_snoc_vass; tea.
      now eapply to_wf_local2.
  - eexists; split.
    1: eapply clos_sort; tea.
    + now symmetry in Xs.
    + apply TCI_one.
      eapply TC_from_compare_sort; tea.
      1,2: by apply wf_sort_super.
      now apply TC_super.
Qed.

Lemma map_term1_id Γ t : map_term1 (fun _ x => x) Γ t = t. by destruct t. Qed.

Lemma context_closure_sym {TC CC} Σ P (Pα := eq_binder_annot) Ps P'(* (PC : ConvSymPrecondition cf TC Σ) *) Γ t u T :
  [(CCH : ContextChangeable2 P Σ)] ->
  [(CCR : CCTypedRefl CC TC Σ)] ->
  [(TCCC : TCIsCmpType Σ)] ->
  [(CCP : RevImpliesTC Σ (fun Γ t u T => P Γ t u T))] ->
  [(PWF : ToWFLocal2 Σ P)] ->
  [(SymPs : Symmetric Ps)] ->
  [(PsTC : TCFromCompareSort Σ Ps)] ->
  [(PrTC : TCFromCompareProd Σ P)] ->
  [(STC : TCFromCompareSubst10 Σ P)] ->
  [(onP' Γ t u T : P' Γ t u T -> P Γ u t T)] ->
  [(X : Σ ;;; Γ ⊢ t ~ u : T with P, Pα, Ps)] ->
  [(IX : Σ ;;; Γ ⊢ t ~ u : T on X with (fun Γ t u T => P' Γ t u T))] ->
  ∑ T₀, Σ ;;; Γ ⊢ u ~ t : T₀ with P, Pα, Ps × Σ ;;; Γ ⊢ T₀ ≤* T.
Proof.
  intros ?????????? X IX.
  rewrite -(map_term1_id Γ t).
  eapply context_closure_sym_map_term1; tea.
  - unfold Pα. intros na na' H. by symmetry.
  - auto.
Qed.

Lemma conv_sym {cf} {TC} Σ (PC : ConvSymPrecondition cf TC Σ) Γ t u T :
  Σ ;;; Γ ⊢ t === u : T ->
  Σ ;;; Γ ⊢ u === t : T.
Proof.
  intro H. revert Γ t u T H.
  apply (conv_Conv_rect _ _ Σ (fun Γ t u T => Σ ;;; Γ ⊢ u === t : T)).
  all: intros.
  all: try now econstructor.
  - apply conv_ext.
    now apply ext_conv_ofε, eta_ext_sym in IX.
  - eapply context_closure_sym in IX; tc; try apply PC; auto.
    2: by apply eq_sort_sym.
    eapply TCI_elim' in IX; tea; tc.
    by apply conv_clos.
Qed.

Lemma head_context_CC {TC CC} Σ P P' :
  ContextChangeable (typing Σ) Σ ->
  [(onP' Γ Δ t u T : P' Γ t u T -> Σ ⊢ Δ ≤Γ Γ -> P Δ t u T)] ->
  forall Γ Δ t u T,
  Σ ⊢ Δ ≤Γ Γ ->
  [(H : Σ ;;; Γ ⊢ t ~h1 u : T with P)] ->
  Σ ;;; Γ ⊢ t ~h1 u : T on H with P' ->
  Σ ;;; Δ ⊢ t ~h1 u : T with P.
Proof.
  intros ?Pre onP'.
  intros ????? XΓ H X.
  induction X.
  - eapply change_context in Xu; tea.
    eapply onP' in IXt; tea.
    now econstructor.
Qed.

Lemma context_closure_CC {TC CC} Σ P Pα Ps P' :
  CCTypedRefl CC TC Σ -> CmpWFLocal Σ -> CmpContextLiftable Σ -> LeftTyping P Σ -> TCIsCmpType Σ ->
  [(onP' Γ Δ t u T : P' Γ t u T -> Σ ⊢ Δ ≤Γ Γ -> P Δ t u T)] ->
  forall Γ Δ t u T,
  Σ ⊢ Δ ≤Γ Γ ->
  [(H : Σ ;;; Γ ⊢ t ~ u : T with P, Pα, Ps)] ->
  Σ ;;; Γ ⊢ t ~ u : T on H with P' ->
  ∑ T₀, Σ ;;; Δ ⊢ t ~ u : T₀ with P, Pα, Ps × Σ ;;; Δ ⊢ T₀ ≤* T.
Proof.
  intros ?Pre?Pre?Pre?Pre?Pre onP'.
  intros ????? XΓ H X.
  induction X in Δ, XΓ.
  - eapply cmp_wf_local in wfΓ; tea.
    eapply nth_error_convertible_context_TC in hnth as (decl' & hnth & XT); tea.
    eexists; split; tea.
    constructor; tea.
  - eapply onP' in IXA; tea.
    eexists; split; trea.
    econstructor; eauto.
    eapply onP'; tea.
    eapply convertible_contexts_snoc_refl; tas.
    repeat (eexists; cbn; tea).
    now eapply typing_left.
  - eapply onP' in IXt, IXu; tea.
    eexists; split; trea.
    econstructor; eauto.
  - eapply onP' in IXA; tea.
    eexists; split; trea.
    econstructor; eauto.
    eapply onP'; tea.
    eapply convertible_contexts_snoc_refl; tas.
    repeat (eexists; cbn; tea).
    now eapply typing_left.
  - eapply cmp_wf_local in wfΓ; tea.
    eexists; split; trea.
    by econstructor.
Qed.

Lemma cumul_addon_CC {cf TC CC} Σ P P' :
  CCTypedRefl CC TC Σ -> CmpWFLocal Σ -> CmpContextLiftable Σ -> (forall pb, LeftConvTyping P Σ pb) -> TCIsCmpType Σ ->
  [(onP' Γ Δ pb t u T : P' Γ pb t u T -> Σ ⊢ Δ ≤Γ Γ -> P Δ pb t u T)] ->
  forall Γ Δ pb t u T,
  Σ ⊢ Δ ≤Γ Γ ->
  [(H : Σ ;;; Γ ⊢ t ≤c[pb] u : T with P)] ->
  Σ ;;; Γ ⊢ t ≤c[pb] u : T on H with P' ->
  ∑ T₀, Σ ;;; Δ ⊢ t ≤c[pb] u : T₀ with P × Σ ;;; Δ ⊢ T₀ ≤* T.
Proof.
  intros ?Pre?Pre?Pre?Pre?Pre onP'.
  intros ?????? XΓ H X.
  induction X in Δ, XΓ.
  - eapply onP' in IXA; tea.
    eexists; split; trea.
    econstructor; eauto.
    eapply onP'; tea.
    eapply convertible_contexts_snoc_refl; tas.
    repeat (eexists; cbn; tea).
    now eapply typing_leftpb.
  - eapply cmp_wf_local in wfΓ; tea.
    eexists; split; trea.
    by econstructor.
Qed.

Lemma ext_CC {TC CC} Σ P P' :
  CCTypedRefl CC TC Σ -> ContextChangeable (typing Σ) Σ ->
  [(onP' Γ Δ t u T : P' Γ t u T -> Σ ⊢ Δ ≤Γ Γ -> P Δ t u T)] ->
  forall Γ Δ t u T,
  Σ ⊢ Δ ≤Γ Γ ->
  [(H : Σ ;;; Γ ⊢ t ~ext u : T with P)] ->
  Σ ;;; Γ ⊢ t ~ext u : T on H with P' ->
  Σ ;;; Δ ⊢ t ~ext u : T with P.
Proof.
  intros ?Pre?Pre onP'.
  intros ????? XΓ H X.
  induction X.
  - eapply lift_typing_CC in Xj; tea.
    eapply change_context in Xt, Xu; tea.
    eapply ext_eta; tas.
    eapply onP' in IXR; tea.
    by eapply convertible_contexts_snoc_refl.
  - eapply change_context in Xt, Xu, XT; tea.
    by eapply ext_sprop.
Qed.

Instance red0_CC {TC CC} Σ : CCTypedRefl CC TC Σ -> ContextChangeable (typing Σ) Σ ->
  ContextChangeable2 (red0 Σ) Σ.
Proof.
  intros ?Pre?Pre.
  constructor.
  intros Δ Γ ??? X XΓ.
  induction X in Δ, XΓ.
  - eapply lift_typing_CC in l; tea.
    constructor; tas.
    + eapply change_context; tea.
      by eapply convertible_contexts_snoc_refl.
    + eapply change_context; tea.
Qed.

Instance hred_CC {cf TC CC} Σ : CCTypedRefl CC TC Σ -> CmpWFLocal Σ -> CmpContextLiftable Σ -> TCIsCmpType Σ ->
  ContextChangeable (TC Σ) Σ -> ContextChangeable (typing Σ) Σ ->
  ContextChangeable2 (hred1 Σ) Σ.
Proof.
  intros ?Pre?Pre?Pre?Pre?Pre?Pre.
  constructor.
  intros Δ Γ ??? X XΓ.
  induction X in Δ, XΓ.
  - apply hred1_red0.
    eapply change_context2; tea; tc.
  - eapply change_context in X0; tea.
    eapply hred1_cumul; tea.
    eauto.
  - eapply hred1_clos1.
    eapply head_context_CC; tea.
    auto.
Qed.


Instance conv_CC {cf TC CC} Σ pb : CCTypedRefl CC TC Σ -> CmpWFLocal Σ -> CmpContextLiftable Σ -> TCIsCmpType Σ -> (forall pb, LeftConvTyping (conv Σ) Σ pb) -> ContextChangeable (TC Σ) Σ ->
  ContextChangeable2Pb (fun Γ pb t u T => Σ ;;; Γ ⊢ t <==[pb] u : T) Σ pb.
Proof.
  intros ?Pre?Pre?Pre?Pre?Pre?Pre.
  constructor.
  intros Δ Γ ??? X XΓ.
  induction X in Δ, XΓ.
  - eapply conv_hred_l; eauto.
    eapply change_context2; tea; tc.
  - eapply conv_hred_r; eauto.
    eapply change_context2; tea; tc.
  - eapply conv_ext.
    eapply ext_CC; tea; tc.
    auto.
  - eapply cumul_addon_CC in X; tea; auto.
    eapply TCI_elim' in X; tea; tc.
    by apply conv_cumul_addon.
  - eapply change_context in X0; tea.
    eapply conv_cumul; tea.
    eauto.
  - eapply context_closure_CC in X; tea; auto.
    2: by apply LeftConvTyping_to.
    eapply TCI_elim' in X; tea; tc.
    by apply conv_clos.
Qed.




Definition red0_discr t :=
  match t with
  | tApp (tLambda na A t) u => true
  | _ => false
  end.
Lemma red0_discriminate TC Σ Γ t u T :
  Σ ;;; Γ ⊢ t ~>0 u : T ->
  red0_discr t.
Proof.
  induction 1 => //=.
Qed.

Fixpoint hred1_discr t :=
  match t with
  | tApp (tLambda na A t) u => true
  | tApp t u => hred1_discr t
  | _ => false
  end.
Lemma hred1_discriminate TC Σ Γ t u T :
  Σ ;;; Γ ⊢ t ~>h u : T ->
  hred1_discr t.
Proof.
  induction 1 => //=.
  - induction X => //.
  - induction Xtu => //=.
    now destruct t.
Qed.
Lemma hred_discriminate TC Σ Γ t u T :
  Σ ;;; Γ ⊢ t ~>h* u : T ->
  ~~ hred1_discr t ->
  t = u.
Proof.
  induction 1 using hred_rect => //=.
  apply hred1_discriminate in X as ->.
  intro => //.
Qed.

Definition head_context1_discr t :=
  match t with
  | tApp t u => hred1_discr t
  | _ => false
  end.
Lemma head_context1_discriminate TC Σ Γ t u T :
  Σ ;;; Γ ⊢ t ~h1 u : T with hred1 Σ ->
  head_context1_discr t.
Proof.
  induction 1 => //=.
  now eapply hred1_discriminate.
Qed.

Definition cumul_addon_discr t :=
  match t with
  | tProd na A B => true
  | tSort s => true
  | _ => false
  end.
Lemma cumul_addon_discriminate cf TC R Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t ≤c[pb] u : T with R ->
  cumul_addon_discr t.
Proof.
  destruct 1 => //=.
Qed.
Lemma cumul_addon_discriminate_r cf TC R Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t ≤c[pb] u : T with R ->
  cumul_addon_discr u.
Proof.
  destruct 1 => //=.
Qed.

Lemma red0_inj TC Σ Σ' Γ Γ' t u u' T T' :
  Σ ;;; Γ ⊢ t ~>0 u : T ->
  Σ' ;;; Γ' ⊢ t ~>0 u' : T' ->
  u = u'.
Proof.
  induction 1 in Γ', u', T' => //=; eauto.
  intro H.
  depind H; eauto.
Qed.

Lemma hred1_inj TC Σ Σ' Γ Γ' t u u' T T' :
  Σ ;;; Γ ⊢ t ~>h u : T ->
  Σ' ;;; Γ' ⊢ t ~>h u' : T' ->
  u = u'.
Proof.
  intros X X'.
  induction X in Γ', u', T', X' => //=; eauto.
  - apply red0_discriminate in X as H.
    induction X' => //=; eauto.
    + now eapply red0_inj.
    + apply head_context1_discriminate in Htu as H'.
      destruct t => //. destruct t1 => //.
  - apply head_context1_discriminate in Htu as H.
    destruct Xtu.
    depind X' => //=; eauto.
    + apply red0_discriminate in X as H'.
      destruct t0 => //.
    + depelim Htu.
      f_equal. now eapply IXt.
Qed.

Lemma hred_inj TC Σ Γ t u u' T U :
  Σ ;;; Γ ⊢ t ~>h* u : T ->
  Σ ;;; Γ ⊢ t ~>h* u' : U ->
  ~~ hred1_discr u -> ~~ hred1_discr u' ->
  u = u'.
Proof.
  intros X X' H H'.
  induction X in u', U, H, X', H' using hred_rect.
  - by apply hred_discriminate in X'.
  - have {}IHX U' X := IHX u' U' X H H'.
    clear X0 H.
    induction X' in H', X, IHX using hred_rect; eauto.
    { apply hred1_discriminate in X. now rewrite X in H'. }
    eapply IHX.
    eapply hred1_inj in X0 as ->; tea.
  - now eapply IHX.
Qed.


Lemma red0_cumul_addon cf TC R Σ Σ' Γ Γ' pb t u u' T T' :
  Σ ;;; Γ ⊢ t ~>0 u : T ->
  Σ' ;;; Γ' ⊢ t ≤c[pb] u' : T' with R ->
  False.
Proof.
  move=> /red0_discriminate H /cumul_addon_discriminate H'.
  now destruct t.
Qed.

Lemma hred1_cumul_addon cf TC R Σ Σ' Γ Γ' pb t u u' T T' :
  Σ ;;; Γ ⊢ t ~>h u : T ->
  Σ' ;;; Γ' ⊢ t ≤c[pb] u' : T' with R ->
  False.
Proof.
  move=> /hred1_discriminate H /cumul_addon_discriminate H'.
  now destruct t.
Qed.

Lemma hred1_cumul_addon_r cf TC R Σ Σ' Γ Γ' pb t u u' T T' :
  Σ ;;; Γ ⊢ u ~>h u' : T ->
  Σ' ;;; Γ' ⊢ t ≤c[pb] u : T' with R ->
  False.
Proof.
  move=> /hred1_discriminate H /cumul_addon_discriminate_r H'.
  now destruct u.
Qed.





Inductive isTermRel Σ (Γ : list relevance) : [(t : term)] -> [(rel : relevance)] -> Type :=
  | is_term_rel_rel n rel :
    nth_error Γ n = Some rel ->
    isTermRel _ _ (tRel n) rel

  | isterm_rel_lambda na A t r :
    isTermRel _ (Γ ,, na.(binder_relevance)) t r ->
    isTermRel _ _ (tLambda na A t) r

  | isterm_rel_app t u r :
    isTermRel _ Γ t r ->
    isTermRel _ _ (tApp t u) r

  | isterm_rel_prod na A B :
    isTermRel _ _ (tProd na A B) Relevant

  | isterm_rel_sort s :
    isTermRel _ _ (tSort s) Relevant.

Definition marks_of_relevance Γ := map (fun decl => decl.(decl_name).(binder_relevance)) Γ.

Notation isTypeRel := (on_type_rel (lift_typing typing)).

Class ConvInjectivityPrecondition cf TC Σ := {
  CInj_type_left pb :: LeftConvTyping (conv Σ) Σ pb;
  CInj_cmp_sort pb :: TCFromCompareSort Σ (compare_sort Σ pb);
  CInj_prod_injectivity Γ T na' A' B' : Σ ;;; Γ ⊢ T ≤T tProd na' A' B' -> ∑ na A B, T = tProd na A B;
  CInj_relevance_correct Γ t T : Σ ;;; Γ ⊢ t : T -> forall rel, isTermRel Σ (marks_of_context Γ) t rel <~> isTypeRel Σ Γ T rel;
}.

Lemma conv_injectivity_prod cf TC Σ (CIPre : ConvInjectivityPrecondition cf TC Σ) Γ pb t T na' A' B' :
  Σ ;;; Γ ⊢ t <==[pb] tProd na' A' B' : T ->
  ∑ na A B sA sB,
  Σ ;;; Γ ⊢ t ~>h* tProd na A B : T ×
  eq_binder_annot na na' ×
  isSortRel sA na.(binder_relevance) ×
  Σ ;;; Γ ⊢ A === A' : tSort sA ×
  Σ ;;; Γ ,, vass na A ⊢ B <==[pb] B' : tSort sB.
Proof.
  intro X.
  remember (tProd na' A' B') as t' eqn:e.
  induction X in e |- *.
  - destruct IHX as (na & A & B & sA & sB & hred & hna & hsA & hA & hB) => //.
    exists na, A, B, sA, sB; repeat split; tea.
    econstructor; tea.
  - clear X0 IHX. exfalso.
    apply hred1_discriminate in X. now subst u.
  - clear X. exfalso.
    induction H.
    + clear -CIPre e t1.
      remember (tProd na A B) as t eqn:e'.
      revert na na' A A' B B' e e'.
      induction t1 using typing_rect with (Pj := fun _ _ => True) (PΓ := fun _ => True) => //.
      intros ?????? -> ->.
      eapply CInj_prod_injectivity in X as (na_ & A_ & B_ & X).
      now eapply IHt1 => //.
    + eapply CInj_relevance_correct, snd in t1 as X.
      forward X. { repeat eexists; tea. }
      subst u.
      inversion X.
  - clear X.
    induction H => //.
    injection e as [= -> -> ->].
    exists na, A, B, s, s'.
    repeat split; tas.
    constructor.
    constructor.
    1: repeat eexists; cbn; tea.
    all: eapply typing_leftpb; tea.
  - destruct IHX as (na & A & B & sA & sB & hred & hna & hsA & hA & hB) => //.
    exists na, A, B, sA, sB; repeat split; tea.
    now eapply hred_cumul.
  - clear X.
    induction H => //.
    injection e as [= -> -> ->].
    exists na, A, B, s, s'.
    repeat split; tas.
    2: now apply conv_eq_pb.
    constructor.
    constructor.
    1: repeat eexists; cbn; tea.
    all: eapply typing_leftpb; tea.
Qed.


Lemma conv_injectivity_sort cf TC Σ (CIPre : ConvInjectivityPrecondition cf TC Σ) Γ pb t T s' :
  Σ ;;; Γ ⊢ t <==[pb] tSort s' : T ->
  ∑ s,
  Σ ;;; Γ ⊢ t ~>h* tSort s : T ×
  compare_sort Σ pb s s'.
Proof.
  intro X.
  remember (tSort s') as t' eqn:e.
  induction X in e |- *.
  - destruct IHX as (s & hred & hS) => //.
    exists s; split; tea.
    econstructor; tea.
  - clear X0 IHX. exfalso.
    apply hred1_discriminate in X. now subst u.
  - clear X. exfalso.
    induction H.
    + clear -CIPre e t1.
      remember (tProd na A B) as t eqn:e'.
      revert na A B s' e e'.
      induction t1 using typing_rect with (Pj := fun _ _ => True) (PΓ := fun _ => True) => //.
      intros ???? -> ->.
      eapply CInj_prod_injectivity in X as (na_ & A_ & B_ & X).
      now eapply IHt1 => //.
    + eapply CInj_relevance_correct, snd in t1 as X.
      forward X. { repeat eexists; tea. }
      subst u.
      inversion X.
  - clear X.
    induction H => //.
    injection e as [= ->].
    exists s.
    split; tas.
    constructor.
    econstructor.
    1: now constructor.
    eapply TC_from_compare_sort; tas.
    1,2: by apply wf_sort_super.
    now apply compare_sort_super.
  - destruct IHX as (s & hred & hs) => //.
    exists s; split; tea.
    now eapply hred_cumul.
  - clear X.
    induction H => //.
    injection e as [= ->].
    exists s.
    split; tas.
    2: now apply compare_sort_subrel.
    constructor.
    econstructor.
    1: now constructor.
    eapply TC_from_compare_sort; tas.
    1,2: by apply wf_sort_super.
    instantiate (1 := Conv).
    now apply compare_sort_super.
Qed.



Class PredConfluencePrecondition {TC} Σ := {
  PC_pred_subst10 Γ na A t t' u u' T :
    Σ ;;; Γ ,, vass na A ⊢ t ≡>1 t' : T ->
    Σ ;;; Γ ⊢ u ≡>1 u' : A ->
    Σ ;;; Γ ⊢ t {0 := u} ≡>1 t' {0 := u'} : T {0 := u};
  (* PC_TypedRefl :: TypedReflexivity (pred1 Σ) Σ; *)
  PC_LeftTyping :: LeftTyping (pred1 Σ) Σ;
  PC_cmp_subst10 :: TCFromCompareSubst10 Σ (pred1 Σ);
  PC_CC :: ContextComparator;
  PC_change_context :: ContextChangeable2 (pred1 Σ) Σ;
  PC_trefl :: CCTypedRefl PC_CC TC Σ;
  PC_TCCC :: TCIsCmpType Σ;
  PC_imp_cmp_type :: RevImpliesTC Σ (pred1 Σ);
  PC_TCFromCompareSort :: TCFromCompareSort Σ eq;
  PC_prod_injectivity Γ T na' A' B' : Σ ;;; Γ ⊢ T ≤* tProd na' A' B' ->
    ∑ na A B, T = tProd na A B × eq_binder_annot na na' × Σ ;;; Γ ⊢ A' ≤* A × Σ ;;; Γ ,, vass na A ⊢ B ≤* B';
  PC_TCFromCompareProd :: TCFromCompareProd Σ (pred1 Σ);
  PC_TCFromCompareSubst10 :: TCFromCompareSubst10 Σ (pred1 Σ);
  }.
Arguments PredConfluencePrecondition : clear implicits.

Class ProdInjectivity TC Σ := {
  Prod_invert Γ na na' A A' B B' :
    Σ ;;; Γ ⊢ tProd na A B ≤* tProd na' A' B' ->
    eq_binder_annot na na' × Σ ;;; Γ ⊢ A' ≤* A × Σ ;;; Γ ⊢ A ≤* A' × Σ ;;; Γ ,, vass na A ⊢ B ≤* B';
}.

Lemma pred1_wf_local TC Σ Γ t u T :
  Σ ;;; Γ ⊢ t ≡>1 u : T ->
  wf_local Σ Γ.
Proof.
  induction 1 => //.
  - induction X => //.
  - induction X => //.
Qed.

Lemma pred1_trefl TC Σ Γ t T :
  Σ ;;; Γ ⊢ t : T ->
  Σ ;;; Γ ⊢ t ≡>1 t : T.
Proof.
  induction 1 using typing_alt_rect with (P := pred1 Σ).
  - eapply pred1_clos; eauto with fmap.
  - now eapply pred1_cumul.
Qed.

Lemma pred1_left_typing TC Σ (Pre : TCFromCompareSort Σ eq) Γ t u T :
  Σ ;;; Γ ⊢ t ≡>1 u : T ->
  Σ ;;; Γ ⊢ t : T.
Proof.
  induction 1.
  - induction X => //.
    + econstructor; tea.
      (* 1: todo "Additional argument to tApp". *)
      constructor; tas.
      (* Unshelve. 1: todo "Additional argument to tApp". *)
  - now econstructor.
  - apply context_closure_ofε in X; clear H.
    eapply context_closure_typing_left; tea.
    auto.
Qed.

Lemma context_closure_retyping {TC} Σ Ps Pα P P' Γ t u T T' :
  [(onP Γ t u T T' : P Γ t u T -> Σ ;;; Γ ⊢ t : T' -> P' Γ t u T')] ->
  [(onPs Γ s s' : Ps s s' -> wf_sort Σ s -> wf_sort Σ s' -> Σ ;;; Γ ⊢ tSort (Sort.super s') ≤* tSort (Sort.super s))] ->
  [(X : Σ ;;; Γ ⊢ t ~ u : T with P, Pα, Ps)] ->
  Σ ;;; Γ ⊢ t : T' ->
  ∑ T0, Σ ;;; Γ ⊢ T0 ≤* T' ×
  Σ ;;; Γ ⊢ t ~ u : T0 with P', Pα, Ps.
Proof.
  intros onP onPs X X'.
  induction X in X', T'.
  all: dependent induction X' using typing_elim.
  1-4: eexists; split; [eassumption|].
  - now econstructor.
  - destruct X as (_ & s' & XA' & _ & Xs').
    econstructor; now eauto.
  - econstructor; eauto.
  - destruct X as (_ & s1' & XA' & <- & Xs').
    econstructor; now eauto.
  - eexists; split.
    2: now econstructor.
    eapply TCI_trans; tea.
    now eapply onPs.
Qed.

Lemma pred1_retyping TC Σ (Pre : ProdInjectivity TC Σ) Γ t u T T' :
  Σ ;;; Γ ⊢ t ≡>1 u : T ->
  Σ ;;; Γ ⊢ t : T' ->
  Σ ;;; Γ ⊢ t ≡>1 u : T'.
Proof.
  induction 1 in T'.
  - intro X'.
    induction X => //.
    + dependent induction X' using typing_elim.
      eapply TCI_elim; tc; tea.
      apply pred1_pred0, pred0_beta; tas.
      dependent induction X'1 using typing_elim.
      apply Prod_invert in X0 as (_ & _ & _ & X0).
      eapply TCI_elim; tc; revgoals; tea.
      eauto.
  - eauto.
  - apply context_closure_ofε in X; clear H.
    intro X'.
    eapply context_closure_retyping in X as (T0 & HT & X); tea.
    + eapply TCI_elim; tc; tea.
      now apply pred1_clos.
    + auto.
    + intros ??? <- ??. constructor.
Qed.

Fixpoint ρ t :=
  match t with
  | tApp (tLambda na A t) u => (ρ t) {0 := ρ u}
  | tApp t u => tApp (ρ t) (ρ u)
  | tLambda na A t => tLambda na (ρ A) (ρ t)
  | tProd na A B => tProd na (ρ A) (ρ B)
  | tSort s => tSort s
  | t => t
  end.


Lemma pred1_rho TC Σ (Pre : PredConfluencePrecondition TC Σ) Γ t T :
  Σ ;;; Γ ⊢ t ≡>1 t : T ->
  Σ ;;; Γ ⊢ t ≡>1 ρ t : T.
Proof.
  generalize t at 2 as t'.
  induction 1.
  - apply pred1_pred0.
    induction X.
    all: try now econstructor.
  - now econstructor.
  - induction X.
    all: try solve [ apply pred1_clos; now econstructor ].
    + cbn.
      have Xdef : Σ ;;; Γ ⊢ tApp t u ≡>1 tApp (ρ t) (ρ u) : B {0 := u}
        by now eapply pred1_clos, clos_app.
      destruct t => //.
      dependent induction IXt using pred1_elim.
      1: by depelim X.
      depelim X.
      apply PC_prod_injectivity in XT as (?&?&? & [= <- <- <-] & eqna & XTA & XTB).
      apply typing_left in XA as XAt.
      apply pred1_pred0, pred0_beta; tas.
      * by repeat (eexists; cbn; tea).
      * eapply TCI_elim; tea.
        1: now econstructor.
      * eapply TCI_elim; tea.
        1: now econstructor.
    + subst s'.
      apply pred1_clos; now econstructor.
Qed.


Lemma pred1_triangle TC Σ (Pre : PredConfluencePrecondition TC Σ) Γ t u T :
  Σ ;;; Γ ⊢ t ≡>1 u : T ->
  Σ ;;; Γ ⊢ u ≡>1 ρ t : T.
Proof.
  induction 1.
  - induction X.
    + cbn.
      eapply pred1_cumul.
      * now eapply PC_pred_subst10.
      * eapply PC_cmp_subst10; tea.
  - now eapply pred1_cumul.
  - have Xdef : Σ ;;; Γ ⊢ u ≡>1 map_term1 (fun _ => ρ) Γ t : T.
    {
      eapply context_closure_sym_map_term1 with (f := fun _ => ρ) in X; tc; try apply Pre; auto.
      - eapply TCI_elim'; tea; tc.
        by apply pred1_clos.
      - constructor; intros. now eapply pred1_wf_local.
      - by intros ?? ->.
    }
    induction X; cbn in Xdef |- *; try by apply Xdef.

    + destruct t => //.
      dependent induction Xt using pred1_elim.
      1: by depelim X.
      depelim X. subst na'.
      dependent induction IXt using pred1_elim.
      1: by depelim X.
      depelim X.
      apply PC_prod_injectivity in XT as (?&?&? & [= <- <- <-] & eqna & XTA & XTB).
      apply PC_prod_injectivity in XT0 as (?&?&? & [= <- <- <-] & eqna' & XTA' & XTB').
      apply typing_left in XA as XAt.
      cbn.
      eapply pred1_cumul.
      2: by eapply TC_from_compare_subst10; eassumption.
      apply pred1_pred0, pred0_beta; tas.
      * by repeat (eexists; cbn; tea).
      * eapply TCI_elim; tea.
        1: now econstructor.
      * eapply TCI_elim; tea.
        1: now econstructor.
Qed.









Class PredEqPrecondition {cf TC} Σ := {
  PE_pred1_trefl :: TypedReflexivity (pred1 Σ) Σ;
  PE_pred1_typing_left :: LeftTyping (pred1 Σ) Σ;
  PE_pred1_typing_right :: RightTyping (pred1 Σ) Σ;
  PE_eq_treflpb pb :: TypedConvReflexivity (equality Σ) Σ pb;
  PE_eq_typing_left pb :: LeftConvTyping (equality Σ) Σ pb;
  PE_eq_typing_right pb :: RightConvTyping (equality Σ) Σ pb;

  (* PE_context_change_eq :: ContextChangeable (typing Σ) (fun Γ t u T => Σ ;;; Γ ⊢ t <=[Conv] u : T);
  PE_context_change_pred_eq :: ContextChangeable2 (pred1 Σ) (fun Γ t u T => Σ ;;; Γ ⊢ t <=[Conv] u : T); *)

  PE_cmp_sort pb :: TCFromCompareSort Σ (compare_sort Σ pb);
  PE_cmp_prod :: TCFromCompareProd Σ (fun Γ t u T => Σ ;;; Γ ⊢ t <=[Conv] u : T);
  PE_cmp_inst :: TCFromCompareSubst10 Σ (fun Γ t u T => Σ ;;; Γ ⊢ t <=[Conv] u : T);

  (* CTP_conv_sym Γ t u T : Σ ;;; Γ ⊢ t === u : T -> Σ ;;; Γ ⊢ u === t : T; *)

  PE_sort_relevance Γ s s' : Σ ;;; Γ ⊢ tSort s ≤* tSort s' -> relevance_of_sort s = relevance_of_sort s';

  PE_type_relevance Γ T T' r : Σ ;;; Γ ⊢ T ≤* T' -> isTypeRel Σ Γ T r <~> isTypeRel Σ Γ T' r;

  PE_cmp_inst' Γ na (A B B' u : term) :
    Σ ;;; Γ ,, vass na A ⊢ B ≤* B' ->
    Σ ;;; Γ ⊢ B {0 := u} ≤* B' {0 := u};

  PE_shared_max_type Γ t T T' :
    Σ ;;; Γ ⊢ t : T ->
    Σ ;;; Γ ⊢ t : T' ->
    ∑ TT, Σ ;;; Γ ⊢ T ≤* TT × Σ ;;; Γ ⊢ T' ≤* TT;

  PE_shared_max_type_subst Γ na A t u T T' T1 :
    Σ ;;; Γ ,, vass na A ⊢ t : T ->
    Σ ;;; Γ ,, vass na A ⊢ t : T' ->
    Σ ;;; Γ ⊢ T {0 := u} ≤* T1 ->
    Σ ;;; Γ ⊢ T' {0 := u} ≤* T1 ->
    ∑ TT, Σ ;;; Γ ,, vass na A ⊢ T ≤* TT × Σ ;;; Γ ,, vass na A ⊢ T' ≤* TT × Σ ;;; Γ ⊢ TT {0 := u} ≤* T1;

  PE_shared_max_prod_type Γ t na na' A A' B B' :
    Σ ;;; Γ ⊢ t : tProd na A B ->
    Σ ;;; Γ ⊢ t : tProd na' A' B' ->
    ∑ na'' A0 B0, Σ ;;; Γ ⊢ tProd na A B ≤* tProd na'' A0 B0 × Σ ;;; Γ ⊢ tProd na' A' B' ≤* tProd na'' A0 B0;

  PE_shared_max_sort_type Γ t s s' :
    Σ ;;; Γ ⊢ t : tSort s ->
    Σ ;;; Γ ⊢ t : tSort s' ->
    ∑ s0, Σ ;;; Γ ⊢ tSort s ≤* tSort s0 × Σ ;;; Γ ⊢ tSort s' ≤* tSort s0;

  PE_shared_max_prod_type' Γ t na na' u u' A A' B B' T :
    Σ ;;; Γ ⊢ t : tProd na A B ->
    Σ ;;; Γ ⊢ t : tProd na' A' B' ->
    Σ ;;; Γ ⊢ B {0 := u} ≤* T ->
    Σ ;;; Γ ⊢ B'{0 := u'} ≤* T ->
    Σ ;;; Γ ⊢ u <=[Conv] u' : A ->
    ∑ na'' A0 B0, Σ ;;; Γ ⊢ tProd na A B ≤* tProd na'' A0 B0 × Σ ;;; Γ ⊢ tProd na' A' B' ≤* tProd na'' A0 B0 ×
      Σ ;;; Γ ⊢ B {0 := u} ≤* B0 {0 := u} × Σ ;;; Γ ⊢ B' {0 := u'} ≤* B0 {0 := u} × Σ ;;; Γ ⊢ B0 {0 := u} ≤* T;

  PE_shared_max_prod Γ na na' A A' B B' T :
    Σ ;;; Γ ⊢ tProd na A B ≤* T ->
    Σ ;;; Γ ⊢ tProd na' A' B' ≤* T ->
    lift_typing typing Σ Γ (j_vass na A) ->
    ∑ B0, Σ ;;; Γ ,, vass na A ⊢ B ≤* B0 × Σ ;;; Γ ,, vass na A ⊢ B' ≤* B0 × Σ ;;; Γ ⊢ tProd na A B0 ≤* T;

  PE_shared_max_sort Γ na A sA sA' sB sB' T :
    Σ ;;; Γ ⊢ tSort (Sort.sort_of_product sA sB) ≤* T ->
    Σ ;;; Γ ⊢ tSort (Sort.sort_of_product sA' sB') ≤* T ->
    lift_typing typing Σ Γ (j_vass na A) ->
    ∑ sA0 sB0, Σ ;;; Γ ⊢ tSort sA ≤* tSort sA0 × Σ ;;; Γ ⊢ tSort sA' ≤* tSort sA0 × Σ ;;; Γ ,, vass na A ⊢ tSort sB ≤* tSort sB0 × Σ ;;; Γ ,, vass na A ⊢ tSort sB' ≤* tSort sB0 ×
      Σ ;;; Γ ⊢ tSort (Sort.sort_of_product sA0 sB0) ≤* T;

  PE_Prod_invert :: ProdInjectivity TC Σ;

  (* CTP_sym_conv Γ pb t u T : Σ ;;; Γ ⊢ t === u : T -> Σ ;;; Γ ⊢ u <==[pb] t : T; *)
  PE_incl_conv Γ A B s : Σ ;;; Γ ⊢ A <=[Conv] B : tSort s -> Σ ;;; Γ ⊢ A ≤* B × Σ ;;; Γ ⊢ B ≤* A;

  PE_eq_subst Γ na A pb t t' T u u' : Σ ;;; Γ ,, vass na A ⊢ t <=[pb] t' : T -> Σ ;;; Γ ⊢ u <=[Conv] u' : A -> Σ ;;; Γ ⊢ t {0 := u} <=[pb] t' {0 := u'} : T {0 := u};

  PE_change_subst_eq Γ T U u u' A : Σ ;;; Γ ⊢ T {0 := u} ≤* U -> Σ ;;; Γ ⊢ u <=[Conv] u' : A -> Σ ;;; Γ ⊢ T {0 := u'} ≤* U;
  PE_change_subst_pred Γ T U u u' A : Σ ;;; Γ ⊢ T {0 := u} ≤* U -> Σ ;;; Γ ⊢ u ≡>1 u' : A -> Σ ;;; Γ ⊢ T {0 := u'} ≤* U;

  PE_change_proddom_pred Γ na A A' TT T : Σ ;;; Γ ⊢ A ≡>1 A' : TT -> Σ ;;; Γ ⊢ tProd na A T ≤* tProd na A' T × Σ ;;; Γ ⊢ tProd na A' T ≤* tProd na A T;
  PE_construct_prod_cumul Γ na na' A A' B B' : eq_binder_annot na na' -> Σ ;;; Γ ⊢ A' ≤* A -> Σ ;;; Γ ,, vass na A ⊢ B ≤* B' -> Σ ;;; Γ ⊢ tProd na A B ≤* tProd na' A' B';

  PE_strengthening_pred Γ Γ' na A n t u T : Σ ;;; (Γ ,, vass na A) ,,, lift_context n 0 Γ' ⊢ lift 1 n t ≡>1 u : T ->
    ∑ u' T', u = lift 1 n u' × Σ ;;; Γ ,,, Γ' ⊢ t ≡>1 u' : T' × Σ ;;; (Γ ,, vass na A) ,,, lift_context n 0 Γ' ⊢ lift 1 n T' ≤* T;

  PE_inv_eta_lift Γ na A t t' T : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ≡>1 t' : T -> ~~ isLambda t -> ∑ u, t' = tApp (lift0 1 u) (tRel 0) × Σ ;;; Γ ⊢ t ≡>1 u : tProd na A T;

  PE_change_context_self Γ na na' A A' T U : eq_binder_annot na na' -> Σ ;;; Γ ⊢ A ≤* A' -> Σ ;;; Γ ⊢ A' ≤* A -> Σ ;;; Γ ,, vass na A ⊢ T ≤* U -> Σ ;;; Γ ,, vass na' A' ⊢ T ≤* U;

  (* CTP_conv_subst10 Γ na (A B t t' u u' : term) :
    Σ ;;; Γ ,, vass na A ⊢ t === t' : B ->
    Σ ;;; Γ ⊢ u === u' : A ->
    Σ ;;; Γ ⊢ t {0 := u} === t' {0 := u'} : B {0 := u}; *)

  (* CTP_insert_red0_left Γ pb t t' u A B T : Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T -> Σ ;;; Γ ⊢ t <==[pb] u : T -> Σ ;;; Γ ⊢ t ~>0 t' : T -> Σ ;;; Γ ⊢ t' <==[pb] u : T; *)
  (* CTP_lift_red0_left Γ pb na A B t t' u T : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t') (tRel 0) <==[pb] u : T -> Σ ;;; Γ ⊢ t ~>0 t' : B -> Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) <==[pb] u : T; *)
  }.
Arguments PredEqPrecondition : clear implicits.

Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' | ~ u : T" (at level 50, Γ, t, t', u, T at next level).
Inductive context_closure_tri {cf TC} Σ R Γ : forall (t t' u T : term), Type :=
  | clos_tri_rel n decl :
      [(wfΓ : wf_local Σ Γ)] ->
      [(hnth : nth_error Γ n = Some decl)] ->
      Σ ;;; Γ ⊢ tRel n ~ tRel n | ~ tRel n : lift0 (S n) decl.(decl_type)

  | clos_tri_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : eq_sort Σ s s')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' | ~ tSort s : tSort (Sort.super s')

  | clos_tri_lambda na na' A A' B t t' u T s :
      [(Xα : eq_binder_annot na na')] ->
      [(XA : R Γ A A' B (tSort s))] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(Xt : R (Γ ,, vass na A) t t' u T)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' | ~ tLambda na B u : tProd na A T

  | clos_tri_app na A B f f' g a a' b :
      [(Xt : R Γ f f' g (tProd na A B))] ->
      [(Xu : R Γ a a' b A)] ->
      Σ ;;; Γ ⊢ tApp f a ~ tApp f' a' | ~ tApp g b : B { 0 := a }

  | clos_tri_prod na na' A A' B T T' U s s' :
      [(Xα : eq_binder_annot na na')] ->
      [(XA : R Γ A A' B (tSort s))] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XT : R (Γ ,, vass na A) T T' U (tSort s'))] ->
      Σ ;;; Γ ⊢ tProd na A T ~ tProd na' A' T' | ~ tProd na B U : tSort (Sort.sort_of_product s s')
where "Σ ;;; Γ ⊢ t ~ t' | ~ u : T" := (context_closure_tri Σ _ Γ t t' u T).
Derive Signature for context_closure_tri.

Reserved Notation "Σ  ;;; Γ ⊢ t ≤c[ pb ] t' | ~ u : T" (at level 50, Γ, t, t', pb, u, T at next level).
Inductive cumul_addon_tri {cf TC} Σ R Γ pb : forall (t t' u T : term), Type :=
  | cumul_tri_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      Σ ;;; Γ ⊢ tSort s ≤c[pb] tSort s' | ~ tSort s : tSort (Sort.super s')

  | cumul_tri_prod na na' A A' B T T' U s s' :
      [(Xα : eq_binder_annot na na')] ->
      [(XA : R Γ Conv A A' B (tSort s))] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XT : R (Γ ,, vass na A) pb T T' U (tSort s'))] ->
      Σ ;;; Γ ⊢ tProd na A T ≤c[pb] tProd na' A' T' | ~ tProd na B U : tSort (Sort.sort_of_product s s')
where "Σ ;;; Γ ⊢ t ≤c[ pb ] t' | ~ u : T" := (cumul_addon_tri Σ _ Γ pb t t' u T).
Derive Signature for cumul_addon_tri.


Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' : T 'ondep' H 'with' R'" (at level 50, Γ, t, t', T, H, R' at next level).

Section εε.
Context {TC} Σ.
Variable (R : context -> term -> term -> term -> Type).
Variable (R' : forall Γ t u T, R Γ t u T -> Type).

Reserved Notation "Σ  ;;; Γ ⊢ t ~R' t' : T 'on' H" (at level 50, Γ, t, t', T, H at next level).

Notation "Σ ;;; Γ ⊢ t ~R u : T" := (R Γ t u T) (only parsing).
Notation "Σ ;;; Γ ⊢ t ~R' u : T 'on' H" := (R' Γ t u T H) (only parsing).
Local Set Elimination Schemes.
Inductive context_closureεε Rα Rs Γ : forall (t t' T : term), Σ ;;; Γ ⊢ t ~ t' : T with R, Rα, Rs -> Type :=
  | closεε_rel n decl :
      [(wfΓ : wf_local Σ Γ)] ->
      [(hnth : nth_error Γ n = Some decl)] ->
      Σ ;;; Γ ⊢ tRel n ~ tRel n : lift0 (S n) decl.(decl_type) ondep ⌈clos_rel⌋ with R'

  | closεε_lambda na na' A A' t t' T s :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s on XA)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T)] ->
      [(IXt : Σ ;;; Γ ,, vass na A ⊢ t ~R' t' : T on Xt)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' : tProd na A T ondep ⌈clos_lambda⌋ with R'

  | closεε_app na A B t t' u u' :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' : tProd na A B)] ->
      [(IXt : Σ ;;; Γ ⊢ t ~R' t' : tProd na A B on Xt)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' : A)] ->
      [(IXu : Σ ;;; Γ ⊢ u ~R' u' : A on Xu)] ->
      Σ ;;; Γ ⊢ tApp t u ~ tApp t' u' : B { 0 := u } ondep ⌈clos_app⌋ with R'

  | closεε_prod na na' A A' B B' s s' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s on XA)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B' : tSort s')] ->
      [(IXB : Σ ;;; Γ ,, vass na A ⊢ B ~R' B' : tSort s' on XB)] ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B' : tSort (Sort.sort_of_product s s') ondep ⌈clos_prod⌋ with R'

  | closεε_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' : tSort (Sort.super s') ondep ⌈clos_sort⌋ with R'
where "Σ ;;; Γ ⊢ t ~ t' : T 'ondep' p 'with' R'" := (context_closureεε _ _ Γ t t' T p) (only parsing).
Derive Signature for context_closureεε.
Unset Elimination Schemes.
End εε.

Notation "Σ ;;; Γ ⊢ t ~ t' : T 'ondep' p 'with' R'" := (context_closureεε Σ _ R' _ _ Γ t t' T p).
Reserved Notation "Σ  ;;; Γ ⊢ t ≤c[ pb ] t' : T 'ondep' H 'with' R'" (at level 50, Γ, t, t', pb, T, H, R' at next level).

Section CumulAddon.
Local Set Elimination Schemes.

Context {cf} {TC} Σ (R : forall (Γ : context) (pb : conv_pb) (t t' T : term), Type).
Variable (R' : forall Γ pb t u T, R Γ pb t u T -> Type).

Reserved Notation "Σ  ;;; Γ ⊢ t ≤R'[ pb ] t' : T 'on' H" (at level 50, Γ, t, t', pb, T, H at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =R' t' : T 'on' H" (at level 50, Γ, t, t', T, H at next level).

Notation "Σ ;;; Γ ⊢ t ≤R[ pb ] t' : T" := (R Γ pb t t' T) (only parsing).
Notation "Σ ;;; Γ ⊢ t ≤R'[ pb ] t' : T 'on' H" := (R' Γ pb t t' T H) (only parsing).
Notation "Σ ;;; Γ ⊢ t =R t' : T" := (R Γ Conv t t' T) (only parsing).
Notation "Σ ;;; Γ ⊢ t =R' t' : T 'on' H" := (R' Γ Conv t t' T H) (only parsing).

Inductive cumul_addonεε Γ pb : forall (t t' T : term), Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T -> Type :=
  | cumulεε_prod na na' A A' B B' s s' :
      [(Xα : eq_binder_annot na na')] ->
      [(XA : Σ ;;; Γ ⊢ A =R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A =R' A' : tSort s on XA)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ≤R[pb] B' : tSort s')] ->
      [(IXB : Σ ;;; Γ ,, vass na A ⊢ B ≤R'[pb] B' : tSort s' on XB)] ->
      Σ ;;; Γ ⊢ tProd na A B ≤c[pb] tProd na' A' B' : tSort (Sort.sort_of_product s s') ondep ⌈cumul_prod⌋ with R'

  | cumulεε_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs' : wf_sort Σ s')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      Σ ;;; Γ ⊢ tSort s ≤c[pb] tSort s' : tSort (Sort.super s') ondep ⌈cumul_sort⌋ with R'
  (* | (indapp) *)
where "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'ondep' p 'with' R'" := (cumul_addonεε Γ pb t t' T p) (only parsing).
Derive Signature for cumul_addonεε.
End CumulAddon.

Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'ondep' p 'with' R'" := (cumul_addonεε Σ _ R' Γ pb t t' T p).

Lemma context_closure_toεε {TC} Σ R R' Rα Rs Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ t' : T with R, Rα, Rs)] ->
  [(X Γ t t' T : [(H : R Γ t t' T)] -> R' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ t ~ t' : T ondep p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closure_ofεε {TC} Σ R R' R'' Rα Rs Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ t' : T with R, Rα, Rs)] ->
  [(H : Σ ;;; Γ ⊢ t ~ t' : T ondep p with R')] ->
  [(X Γ t t' T : [(H : R Γ t t' T)] -> R' Γ t t' T H -> R'' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~ t' : T with R'', Rα, Rs.
Proof.
  intros p H.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closureεε_fmap {TC} Σ R R' R'' Rα Rs Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ t' : T with R, Rα, Rs)] ->
  [(H : Σ ;;; Γ ⊢ t ~ t' : T ondep p with R')] ->
  [(X Γ t t' T : [(H : R Γ t t' T)] -> R' Γ t t' T H -> R'' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ t ~ t' : T ondep p with R''.
Proof.
  intros.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_toεε {cf TC} Σ R R' Γ pb t t' T :
  [(p : Σ ;;; Γ ⊢ t ≤c[pb] t' : T with R)] ->
  [(X Γ pb t t' T : [(H : R Γ pb t t' T)] -> R' Γ pb t t' T H)] ->
  Σ ;;; Γ ⊢ t ≤c[pb] t' : T ondep p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_ofεε {cf TC} Σ R R' Γ pb t t' T :
  [(p : Σ ;;; Γ ⊢ t ≤c[pb] t' : T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ≤c[pb] t' : T ondep p with (fun Γ pb t t' T _ => R' Γ pb t t' T))] ->
  Σ ;;; Γ ⊢ t ≤c[pb] t' : T with R'.
Proof.
  intros p H.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addonεε_fmap {cf TC} Σ R R' R'' Γ pb t t' T :
  [(p : Σ ;;; Γ ⊢ t ≤c[pb] t' : T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ≤c[pb] t' : T ondep p with R')] ->
  [(X Γ pb t t' T : [(H : R Γ pb t t' T)] -> R' Γ pb t t' T H -> R'' Γ pb t t' T H)] ->
  Σ ;;; Γ ⊢ t ≤c[pb] t' : T ondep p with R''.
Proof.
  intros.
  induction H.
  all: try now econstructor.
Defined.

Hint Resolve context_closure_toεε context_closureεε_fmap cumul_addon_toεε cumul_addonεε_fmap : fmap.




















































































Module Export InferTypeTrial.

Section Closure.
Local Set Elimination Schemes.

Context {TC RtP RtS} Σ.
Variable (R : forall (Γ : context) (t t' T : term), Type).
Notation "Σ ;;; Γ ⊢ t ~R t' ▷ T " := (R Γ t t' T) (only parsing).
Variable (R' : forall Γ t t' T, Σ ;;; Γ ⊢ t ~R t' ▷ T -> Type).
Notation "Σ ;;; Γ ⊢ t ~R' t' ▷ T 'on' H" := (R' Γ t t' T H) (only parsing).

Inductive red0 Γ : forall (t t' T : term), Type :=
  | red0_beta na A t T u :
      [(Xj : wf_judgment_bd Σ Γ (j_vass na A))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ▹ T)] ->
      [(Xu : Σ ;;; Γ ⊢ u ◃ A)] ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ~>0 t { 0 := u } ▷ T { 0 := u }
where " Σ ;;; Γ ⊢ t ~>0 t' ▷ T " := (@red0 Γ t t' T) (only parsing).
Derive Signature for red0.

Inductive pred0 Γ : forall (t t' T : term), Type :=
  | pred0_beta na A₀ A t t' T u u' :
      [(Xj : wf_judgment_bd Σ Γ (j_vass na A))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t' ▷ T)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' ▷ A₀)] ->
      [(XTA : Σ ;;; Γ ⊢ A₀ ≤T A)] ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ≡>0 t' { 0 := u' } ▷ T { 0 := u }
where " Σ ;;; Γ ⊢ t ≡>0 t' ▷ T " := (@pred0 Γ t t' T) (only parsing).
Derive Signature for pred0.
Locate pred0_beta.
Inductive pred0ε Γ : forall (t t' T : term), Σ ;;; Γ ⊢ t ≡>0 t' ▷ T -> Type :=
  | pred0ε_beta na A₀ A t t' T u u' :
      [(Xj: wf_judgment_bd Σ Γ (j_vass na A))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t' ▷ T)] ->
      [(IXt : Σ ;;; Γ ,, vass na A ⊢ t ~R' t' ▷ T on Xt)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' ▷ A₀)] ->
      [(IXu : Σ ;;; Γ ⊢ u ~R' u' ▷ A₀ on Xu)] ->
      [(XT : Σ ;;; Γ ⊢ A₀ ≤T A)] ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ≡>0 t' { 0 := u' } ▷ T { 0 := u } on ⌈pred0_beta⌋ with R'
where " Σ ;;; Γ ⊢ t ≡>0 t' ▷ T 'on' p 'with' R'" := (@pred0ε Γ t t' T p) (only parsing).
Derive Signature for pred0ε.


Inductive context_closure Rα Rs Γ : forall (t t' T : term), Type :=
  | clos_rel n decl :
      [(wfΓ : wf_local_bd Σ Γ)] ->
      [(hnth : nth_error Γ n = Some decl)] ->
      Σ ;;; Γ ⊢ tRel n ~ tRel n ▷ lift0 (S n) decl.(decl_type)

  | clos_lambda na na' A A' t t' T S s :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' ▷ S)] ->
      [(XT : Σ ;;; Γ ⊢ S ~>□ s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t' ▷ T)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' ▷ tProd na A T

  | clos_app A₀ T na A B t t' u u' :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' ▷ T)] ->
      [(XT : Σ ;;; Γ ⊢ T ~>Π(na : A), B)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' ▷ A₀)] ->
      [(XTA : Σ ;;; Γ ⊢ A₀ ≤T A)] ->
      Σ ;;; Γ ⊢ tApp t u ~ tApp t' u' ▷ B { 0 := u }

  | clos_prod na na' A A' B B' S s S' s' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' ▷ S)] ->
      [(XT : Σ ;;; Γ ⊢ S ~>□ s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B' ▷ S')] ->
      [(XT' : Σ ;;; Γ ,, vass na A ⊢ S' ~>□ s')] ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B' ▷ tSort (Sort.sort_of_product s s')

  | clos_sort s s' :
      [(wfΓ : wf_local_bd Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' ▷ tSort (Sort.super s)
where " Σ ;;; Γ ⊢ t ~ t' ▷ T " := (context_closure _ _ Γ t t' T) (only parsing).
Notation " Σ ;;; Γ ⊢ t ~ t' ▷ T 'with' R , R' , R'' " := (@context_closure R' R'' Γ t t' T) (only parsing).
Derive Signature for context_closure.

Inductive context_closureε Rα Rs Γ : forall (t t' T : term), Σ ;;; Γ ⊢ t ~ t' ▷ T with R, Rα, Rs -> Type :=
  | closε_rel n decl :
      [(wfΓ : wf_local_bd Σ Γ)] ->
      [(hnth : nth_error Γ n = Some decl)] ->
      Σ ;;; Γ ⊢ tRel n ~ tRel n ▷ lift0 (S n) decl.(decl_type) on ⌈clos_rel⌋ with R'

  | closε_lambda na na' A A' t t' T S s :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' ▷ S)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' ▷ S on XA)] ->
      [(XT : Σ ;;; Γ ⊢ S ~>□ s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t' ▷ T)] ->
      [(IXt : Σ ;;; Γ ,, vass na A ⊢ t ~R' t' ▷ T on Xt)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' ▷ tProd na A T on ⌈clos_lambda⌋ with R'

  | closε_app A₀ T na A B t t' u u' :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' ▷ T)] ->
      [(IXt : Σ ;;; Γ ⊢ t ~R' t' ▷ T on Xt)] ->
      [(XT : Σ ;;; Γ ⊢ T ~>Π(na : A), B)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' ▷ A₀)] ->
      [(IXu : Σ ;;; Γ ⊢ u ~R' u' ▷ A₀ on Xu)] ->
      [(XTA : Σ ;;; Γ ⊢ A₀ ≤T A)] ->
      Σ ;;; Γ ⊢ tApp t u ~ tApp t' u' ▷ B { 0 := u } on ⌈clos_app⌋ with R'

  | closε_prod na na' A A' B B' S s S' s' :
      [(Xα : Rα na na')] ->
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' ▷ S)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' ▷ S on XA)] ->
      [(XT : Σ ;;; Γ ⊢ S ~>□ s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B' ▷ S')] ->
      [(IXB : Σ ;;; Γ ,, vass na A ⊢ B ~R' B' ▷ S' on XB)] ->
      [(XT' : Σ ;;; Γ ,, vass na A ⊢ S' ~>□ s')] ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B' ▷ tSort (Sort.sort_of_product s s') on ⌈clos_prod⌋ with R'

  | closε_sort s s' :
      [(wfΓ : wf_local_bd Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' ▷ tSort (Sort.super s) on ⌈clos_sort⌋ with R'
where " Σ ;;; Γ ⊢ t ~ t' ▷ T 'on' p 'with' R'" := (context_closureε _ _ Γ t t' T p) (only parsing).
Derive Signature for context_closureε.


Inductive head_context1_closure Γ : forall (t t' T : term), Type :=
  | hclos1_app T na A B t t' u :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' ▷ T)] ->
      [(XT : Σ ;;; Γ ⊢ T ~>Π(na : A), B)] ->
      [(Xu : Σ ;;; Γ ⊢ u ◃ A)] ->
      Σ ;;; Γ ⊢ tApp t u ~h1 tApp t' u ▷ B { 0 := u }
where " Σ ;;; Γ ⊢ t ~h1 t' ▷ T " := (head_context1_closure Γ t t' T) (only parsing).
Derive Signature for head_context1_closure.

Inductive head_context1_closureε Γ : forall (t t' T : term), Σ ;;; Γ ⊢ t ~h1 t' ▷ T -> Type :=
  | hclos1ε_app T na A B t t' u :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' ▷ T)] ->
      [(IXt : Σ ;;; Γ ⊢ t ~R' t' ▷ T on Xt)] ->
      [(XT : Σ ;;; Γ ⊢ T ~>Π(na : A), B)] ->
      [(Xu : Σ ;;; Γ ⊢ u ◃ A)] ->
      Σ ;;; Γ ⊢ tApp t u ~h1 tApp t' u ▷ B { 0 := u } on ⌈hclos1_app⌋ with R'
where " Σ ;;; Γ ⊢ t ~h1 t' ▷ T 'on' p 'with' R'" := (head_context1_closureε Γ t t' T p) (only parsing).
End Closure.

(* Begin Closure renotations *)
  Notation " Σ ;;; Γ ⊢ t ~>0 t' ▷ T " := (red0 Σ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ≡>0 t' ▷ T " := (pred0 Σ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ≡>0 t' ▷ T 'on' p 'with' R'" := (pred0ε Σ _ R' Γ t t' T p).
  Notation " Σ ;;; Γ ⊢ t ≡>0 t' ▷ T 'with' R " := (pred0 Σ R Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t ~ t' ▷ T " := (context_closure Σ _ _ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ~ t' ▷ T 'with' R , R' , R'' " := (context_closure Σ R R' R'' Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t ~ t' ▷ T 'on' p 'with' R'" := (context_closureε Σ _ R' _ _ Γ t t' T p).
  Notation " Σ ;;; Γ ⊢ t ~h1 t' ▷ T " := (head_context1_closure Σ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ~h1 t' ▷ T 'with' R " := (head_context1_closure Σ R Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t ~h1 t' ▷ T 'on' p 'with' R'" := (head_context1_closureε Σ _ R' Γ t t' T p).
(* End Closure notations *)

Section InferClasses.
Context {TC RtP RtS} Σ.

Lemma pred0_toε R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ≡>0 t' ▷ T with R)] ->
  [(X Γ t t' T : [(H : R Γ t t' T)] -> R' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ t ≡>0 t' ▷ T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma pred0_ofε R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ≡>0 t' ▷ T with R)] ->
  [(X : Σ ;;; Γ ⊢ t ≡>0 t' ▷ T on p with (fun Γ t t' T _ => R' Γ t t' T))] ->
  Σ ;;; Γ ⊢ t ≡>0 t' ▷ T with R'.
Proof.
  intros.
  induction X.
  all: now econstructor.
Defined.

Lemma pred0ε_fmap R R' R'' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ≡>0 t' ▷ T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ≡>0 t' ▷ T on p with R')] ->
  [(X Γ t t' T H : R' Γ t t' T H -> R'' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ t ≡>0 t' ▷ T on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closure_toε R R' Rα Rs Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ t' ▷ T with R, Rα, Rs)] ->
  [(X Γ t t' T : [(H : R Γ t t' T)] -> R' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ t ~ t' ▷ T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closure_ofε R R' Rα Rs Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ t' ▷ T with R, Rα, Rs)] ->
  [(X : Σ ;;; Γ ⊢ t ~ t' ▷ T on p with (fun Γ t t' T _ => R' Γ t t' T))] ->
  Σ ;;; Γ ⊢ t ~ t' ▷ T with R', Rα, Rs.
Proof.
  intros.
  induction X.
  all: try now econstructor.
Defined.

Lemma context_closureε_fmap R R' R'' Rα Rs Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~ t' ▷ T with R, Rα, Rs)] ->
  [(H : Σ ;;; Γ ⊢ t ~ t' ▷ T on p with R')] ->
  [(X Γ t t' T H : R' Γ t t' T H -> R'' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ t ~ t' ▷ T on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closure_fmap R R' Rα Rs Rα' Rs' Γ t t' T :
  [(H : Σ ;;; Γ ⊢ t ~ t' ▷ T with R, Rα, Rs)] ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  [(Xα na na' : Rα na na' -> Rα' na na')] ->
  [(Xs s s' : Rs s s' -> Rs' s s')] ->
  Σ ;;; Γ ⊢ t ~ t' ▷ T with R', Rα', Rs'.
Proof.
  intros H X Xα Xs.
  induction H.
  all: try now econstructor.
Defined.

Lemma head_context1_closure_toε R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~h1 t' ▷ T with R)] ->
  [(X Γ t t' T : [(H : R Γ t t' T)] -> R' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ t ~h1 t' ▷ T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma head_context1_closure_ofε R R' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~h1 t' ▷ T with R)] ->
  [(X : Σ ;;; Γ ⊢ t ~h1 t' ▷ T on p with fun Γ t t' T _ => R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~h1 t' ▷ T with R'.
Proof.
  intros.
  induction X.
  all: try now econstructor.
Defined.

Lemma head_context1_closureε_fmap R R' R'' Γ t t' T :
  [(p : Σ ;;; Γ ⊢ t ~h1 t' ▷ T with R)] ->
  [(H : Σ ;;; Γ ⊢ t ~h1 t' ▷ T on p with R')] ->
  [(X Γ t t' T H : R' Γ t t' T H -> R'' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ t ~h1 t' ▷ T on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.
End InferClasses.

Hint Resolve pred0_toε pred0_ofε pred0ε_fmap
  context_closure_toε context_closure_ofε context_closureε_fmap
  head_context1_closure_toε head_context1_closure_ofε head_context1_closureε_fmap
  : fmap.


Inductive hred1 {TC RtP RtS} Σ Γ t u T :=
  | hred1_red0 :
      [(X : Σ ;;; Γ ⊢ t ~>0 u ▷ T)] ->
      Σ ;;; Γ ⊢ t ~>h u ▷ T

  | hred1_clos1 :
      [(X : Σ ;;; Γ ⊢ t ~h1 u ▷ T with hred1 Σ)] ->
      Σ ;;; Γ ⊢ t ~>h u ▷ T
where "Σ ;;; Γ ⊢ t ~>h t' ▷ T" := (hred1 Σ Γ t t' T).
Derive Signature for hred1.

Definition hred1_rect TC RtP RtS Σ P :
  [(XRed0 Γ t u T : [(H : Σ ;;; Γ ⊢ t ~>0 u ▷ T)] -> P Γ t u T ⌈hred1_red0⌋)] ->
  [(XClosure Γ t u T :
      [(Htu : Σ ;;; Γ ⊢ t ~h1 u ▷ T with hred1 Σ)] ->
      [(Xtu : Σ ;;; Γ ⊢ t ~h1 u ▷ T on Htu with P)] ->
      P Γ t u T ⌈hred1_clos1⌋)] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t ~>h u ▷ T)] -> P Γ t u T X.
Proof.
  intros.
  revert Γ t u T X.
  fix Xrec 5.
  intros Γ t u T X; destruct X.
  - apply XRed0; eauto.
  - unshelve eapply XClosure; eauto with fmap.
Defined.
Definition hred1_ind := hred1_rect.

Inductive hred {TC RtP RtS} Σ Γ : forall (t t' T : term), Type :=
  | hred_refl t T :
      [(Xt : Σ ;;; Γ ⊢ t ▹ T)] ->
      Σ ;;; Γ ⊢ t ~>h* t ▷ T

  | hred_step t u v T T' :
      [(Xt : Σ ;;; Γ ⊢ t ~>h u ▷ T)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~>h* v ▷ T')] ->
      Σ ;;; Γ ⊢ t ~>h* v ▷ T
where " Σ ;;; Γ ⊢ t ~>h* t' ▷ T " := (hred Σ Γ t t' T).

Derive Signature for hred.

Definition hred_rect TC RtP RtS Σ P :
  [(XRefl Γ t T :
      [(Xt : Σ ;;; Γ ⊢ t ▹ T)] ->
      P Γ t t T ⌈hred_refl⌋)] ->
  [(XStep Γ t u v T T' :
      [(Xt : Σ ;;; Γ ⊢ t ~>h u ▷ T)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~>h* v ▷ T')] ->
      P Γ u v T' Xu ->
      P Γ t v T ⌈hred_step⌋)] ->
  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t ~>h* u ▷ T)] -> P Γ t u T X.
Proof.
  intros.
  revert Γ t u T X.
  fix Xrec 5.
  intros Γ t u T X; destruct X.
  - apply XRefl; eauto with fmap.
  - eapply XStep; eauto.
Defined.


Inductive pred1 {TC RtP RtS} Σ Γ t u T : Type :=
  | pred1_pred0 :
      [(X : Σ ;;; Γ ⊢ t ≡>0 u ▷ T with pred1 Σ)] ->
      Σ ;;; Γ ⊢ t ≡>1 u ▷ T

  | pred1_clos :
      [(X : Σ ;;; Γ ⊢ t ~ u ▷ T with pred1 Σ, eq, eq)] ->
      Σ ;;; Γ ⊢ t ≡>1 u ▷ T
where " Σ ;;; Γ ⊢ t ≡>1 t' ▷ T " := (pred1 Σ Γ t t' T).
Derive Signature for pred1.

Definition pred1_rect TC RtP RtS Σ P :
  [(XPred0 Γ t u T :
      [(H : Σ ;;; Γ ⊢ t ≡>0 u ▷ T with pred1 Σ)] ->
      [(X : Σ ;;; Γ ⊢ t ≡>0 u ▷ T on H with P)] ->
      P Γ t u T ⌈pred1_pred0⌋)] ->
  [(XClosure Γ t u T :
      [(H : Σ ;;; Γ ⊢ t ~ u ▷ T with pred1 Σ, eq, eq)] ->
      [(X : Σ ;;; Γ ⊢ t ~ u ▷ T on H with P)] ->
      P Γ t u T ⌈pred1_clos⌋)] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t ≡>1 u ▷ T)] -> P Γ t u T X.
Proof.
  intros.
  revert Γ t u T X.
  fix Xrec 5.
  intros Γ t u T X; destruct X.
  - unshelve eapply XPred0; eauto with fmap.
  - unshelve eapply XClosure; tea. now eauto with fmap.
Defined.


Inductive standard_red {TC RtP RtS} Σ Γ t u T :=
  | stredc t' T' :
    [(h : Σ ;;; Γ ⊢ t ~>h* t' ▷ T)] ->
    [(X : Σ ;;; Γ ⊢ t' ~ u ▷ T' with standard_red Σ, eq, eq)] ->
    Σ ;;; Γ ⊢ t =>s u ▷ T
where "Σ  ;;; Γ ⊢ t =>s t' ▷ T" := (standard_red Σ Γ t t' T).
Derive Signature for standard_red.


Inductive standard_redε {TC RtP RtS} Σ (R : forall Γ t t' T, Σ  ;;; Γ ⊢ t =>s t' ▷ T -> Type) Γ t u T : Σ ;;; Γ ⊢ t =>s u ▷ T -> Type :=
  | stredcε t' T' :
    [(h : Σ ;;; Γ ⊢ t ~>h* t' ▷ T)] ->
    [(X : Σ ;;; Γ ⊢ t' ~ u ▷ T' with standard_red Σ, eq, eq)] ->
    [(IX : Σ ;;; Γ ⊢ t' ~ u ▷ T' on X with (fun Γ t t' T H => R Γ t t' T H × standard_redε Σ R Γ t t' T H))] ->
    Σ ;;; Γ ⊢ t =>s u ▷ T on ⌈stredc⌋ with R

where "Σ  ;;; Γ ⊢ t =>s t' ▷ T 'on' H 'with' R" := (standard_redε Σ R Γ t t' T H).
Derive Signature for standard_redε.


Definition standard_red_rect TC RtP RtS Σ P :
  [(X Γ t u T H : [(X : Σ ;;; Γ ⊢ t =>s u ▷ T on H with P)] -> P Γ t u T H)] ->
  forall Γ t u T, [(H : Σ ;;; Γ ⊢ t =>s u ▷ T)] -> P Γ t u T H.
Proof.
  intros ? Γ t u T H.
  apply X.
  revert Γ t u T H.
  fix Xrec 5.
  intros Γ t u T H. destruct H.
  constructor.
  eapply context_closure_toε; intros; split; eauto.
Defined.
Definition standard_red_ind := standard_red_rect.

Class RtP_reflexive RtP Σ := { RtP_refl : forall Γ na A B, Σ ;;; Γ ⊢ tProd na A B ~>Π(na : A), B }.
Class RtS_reflexive RtS Σ := { RtS_refl : forall Γ s, Σ ;;; Γ ⊢ tSort s ~>□ s }.

Section InferClasses.
Context {TC RtP RtS} Σ.

Context {RtPR : RtP_reflexive RtP Σ}.
Context {RtX_inj : BidirUniquePrecondition RtP RtS Σ}.

Instance LeftInfer_red0 : LeftInfer (red0 Σ) Σ.
Proof.
  constructor. induction 1.
  - econstructor; tea.
    econstructor; tea.
    + econstructor; tea.
    + apply RtP_refl.
Qed.

Lemma LeftInfer_headcontext1 P P' Γ t u T :
  [(onP' Γ t u T H : P' Γ t u T H -> Σ ;;; Γ ⊢ t ▹ T)] ->
  [(H : Σ ;;; Γ ⊢ t ~h1 u ▷ T with P)] ->
  Σ ;;; Γ ⊢ t ~h1 u ▷ T on H with P' ->
  Σ ;;; Γ ⊢ t ▹ T.
Proof.
  destruct 2.
  - apply onP' in IXt.
    econstructor; tea. econstructor; tea.
Qed.

Instance LeftInfer_hred1 : LeftInfer (hred1 Σ) Σ.
Proof.
  constructor. induction 1.
  - by eapply infer_left in H.
  - eapply LeftInfer_headcontext1; tea.
    auto.
Qed.

Instance LeftInfer_hred : LeftInfer (hred Σ) Σ.
Proof.
  constructor. induction 1.
  - assumption.
  - by eapply infer_left in Xt.
Qed.

Lemma LeftInfer_pred0 P P' Γ t u T :
  [(onP' Γ t u T H : P' Γ t u T H -> Σ ;;; Γ ⊢ t ▹ T)] ->
  [(H : Σ ;;; Γ ⊢ t ≡>0 u ▷ T with P)] ->
  Σ ;;; Γ ⊢ t ≡>0 u ▷ T on H with P' ->
  Σ ;;; Γ ⊢ t ▹ T.
Proof.
  destruct 2.
  - apply onP' in IXt, IXu.
    econstructor; tea.
    + econstructor; tea.
      * econstructor; tea.
      * apply RtP_refl.
    + econstructor; tea.
Qed.

Lemma LeftInfer_clos P P' Pα Ps Γ t u T :
  [(onP' Γ t u T H : P' Γ t u T H -> Σ ;;; Γ ⊢ t ▹ T)] ->
  [(H : Σ ;;; Γ ⊢ t ~ u ▷ T with P, Pα, Ps)] ->
  Σ ;;; Γ ⊢ t ~ u ▷ T on H with P' ->
  Σ ;;; Γ ⊢ t ▹ T.
Proof.
  destruct 2.
  - by constructor.
  - apply onP' in IXA, IXt.
    econstructor; tea.
    repeat (eexists; cbn; tea).
  - apply onP' in IXt, IXu.
    repeat (econstructor; tea).
  - apply onP' in IXA, IXB.
    repeat (econstructor; tea).
  - constructor; tas.
Qed.

Instance LeftInfer_clos' P Pα Ps : LeftInfer P Σ -> LeftInfer (context_closure Σ P Pα Ps) Σ.
Proof.
  constructor.
  intros; unshelve eapply LeftInfer_clos; revgoals; tea; revgoals.
  - intros; exact True.
  - cbn; intros. by apply infer_left in H.
  - eauto with fmap.
Qed.

Instance LeftInfer_pred1 : LeftInfer (pred1 Σ) Σ.
Proof.
  constructor. induction 1.
  - eapply LeftInfer_pred0; tea. auto.
  - eapply LeftInfer_clos; tea. auto.
Qed.

Instance LeftInfer_standard_red : LeftInfer (standard_red Σ) Σ.
Proof.
  constructor. destruct 1.
  by apply infer_left in h.
Qed.



Definition stred_hred1 Γ t u v T T' : Σ ;;; Γ ⊢ t ~>h u ▷ T -> Σ ;;; Γ ⊢ u =>s v ▷ T' -> Σ ;;; Γ ⊢ t =>s v ▷ T.
Proof.
  intros h [u' T'' h' X].
  exists u' T''; tea.
  now eapply hred_step.
Defined.

Definition stred_hred Γ t u v T T' : Σ ;;; Γ ⊢ t ~>h* u ▷ T -> Σ ;;; Γ ⊢ u =>s v ▷ T' -> Σ ;;; Γ ⊢ t =>s v ▷ T.
Proof.
  induction 1.
  - intro. apply infer_left in X as H'.
    eapply infer_unique with (2 := Xt) in H' as <-. 2: tc.
    assumption.
  - intro. eapply stred_hred1; eauto.
Defined.

Definition stred_clos Γ t u T : Σ ;;; Γ ⊢ t ~ u ▷ T with standard_red Σ, eq, eq -> Σ ;;; Γ ⊢ t =>s u ▷ T.
Proof.
  intro X.
  exists t T; tas. apply hred_refl. by apply infer_left in X.
Defined.



Lemma red0_discriminate Γ t u T :
  Σ ;;; Γ ⊢ t ~>0 u ▷ T ->
  red0_discr t.
Proof.
  induction 1 => //=.
Qed.
Lemma hred1_discriminate Γ t u T :
  Σ ;;; Γ ⊢ t ~>h u ▷ T ->
  hred1_discr t.
Proof.
  induction 1 => //=.
  - induction H => //.
  - induction Xtu => //=.
    now destruct t.
Qed.
Lemma hred_discriminate Γ t u T :
  Σ ;;; Γ ⊢ t ~>h* u ▷ T ->
  ~~ hred1_discr t ->
  t = u.
Proof.
  induction 1 using hred_rect => //=.
  apply hred1_discriminate in Xt as ->.
  intro => //.
Qed.

Lemma head_context1_discriminate Γ t u T :
  Σ ;;; Γ ⊢ t ~h1 u ▷ T with hred1 Σ ->
  head_context1_discr t.
Proof.
  induction 1 => //=.
  now eapply hred1_discriminate.
Qed.

Lemma red0_inj Γ t u T u' T' :
  Σ ;;; Γ ⊢ t ~>0 u ▷ T ->
  Σ ;;; Γ ⊢ t ~>0 u' ▷ T' ->
  u = u'.
Proof.
  induction 1 in u' => //=; eauto.
  intro H.
  depelim H; eauto.
Qed.

Lemma hred1_inj Γ t u T u' T' :
  Σ ;;; Γ ⊢ t ~>h u ▷ T ->
  Σ ;;; Γ ⊢ t ~>h u' ▷ T' ->
  u = u'.
Proof.
  induction 1 in T', u' => //=; eauto.
  - apply red0_discriminate in H as h.
    induction 1 => //=; eauto.
    + now eapply red0_inj.
    + apply head_context1_discriminate in Htu as H'.
      destruct t => //. destruct t1 => //.
  - apply head_context1_discriminate in Htu as H.
    destruct Xtu.
    intro X'.
    depelim X' => //=; eauto.
    + apply red0_discriminate in X as H'.
      destruct t => //.
    + depelim X.
      f_equal. now eapply IXt.
Qed.

Lemma hred_inj Γ t u T u' T' :
  Σ ;;; Γ ⊢ t ~>h* u ▷ T ->
  Σ ;;; Γ ⊢ t ~>h* u' ▷ T' ->
  ~~ hred1_discr u -> ~~ hred1_discr u' ->
  u = u'.
Proof.
  intros X X' H H'.
  induction X in u', T', H, X', H' using hred_rect.
  - by apply hred_discriminate in X'.
  - destruct X'.
    + apply hred1_discriminate in Xt.
      now rewrite Xt in H'.
    + eapply IHX; tas.
      eapply hred1_inj with (1 := Xt0) in Xt as ->; tea.
Qed.

Lemma stred_nhred_inv Γ t u T :
  ~~ hred1_discr t ->
  Σ ;;; Γ ⊢ t =>s u ▷ T ->
  Σ ;;; Γ ⊢ t ~ u ▷ T with standard_red Σ, eq, eq.
Proof.
  intros H [u' T' h X].
  apply infer_left in h as Xt.
  apply hred_discriminate in h as <-; tas.
  apply infer_left in X as Xt'.
  eapply infer_unique with (2 := Xt) in Xt' as <-; tc.
  assumption.
Qed.


Lemma stred_lift Γ n k t u T :
  Σ ;;; Γ ⊢ t =>s u ▷ T -> Σ ;;; Γ ⊢ lift n k t =>s lift n k u ▷ T.
Proof.
  induction 1 in k. destruct X0.
  exists (lift n k t') T'.
  - clear X IX.
    induction h in k.
    + by constructor.
    + eapply hred_step; eauto.
      clear h IHh.
      induction H in k.
      * eapply hred1_red0.
        induction H in k.
        --cbn. relativize (lift _ _ (_ {0 := _})).
          1: constructor.
          rewrite distr_lift_subst //=.
      * eapply hred1_clos.
        destruct Xtu.
        --cbn.
          by constructor.
  - destruct Xtu; repeat match goal with H : _ × _ |- _ => destruct H as [?H ?H] end.
    all: cbn; by constructor.
Qed.


Lemma stred_subst s s' k t u :
  All2 (fun t u => t =>s u) s s' ->
  t =>s u ->
  subst s k t =>s subst s' k u.
Proof.
  intro Hs.
  induction 1 in k. destruct X0.
  eapply stred_hred with (subst s k t').
  - clear Htu Xtu.
    induction h in k.
    + by constructor.
    + eapply hred_step; eauto.
      clear h IHh.
      induction H in k.
      * eapply hred1_red0.
        induction H in k.
        --cbn. relativize (subst _ _ (_ {0 := _})).
          1: constructor.
          rewrite distr_subst //=.
      * eapply hred1_clos.
        destruct Xtu.
        --cbn.
          by constructor.
  - destruct Xtu; repeat match goal with H : _ × _ |- _ => destruct H as [?H ?H] end.
    all: try solve [ eexists (subst s k _); [by apply hred_refl|]; cbn; by constructor ].
    * cbn.
      rewrite -(All2_length Hs).
      destruct (leb_spec_Set k n).
      2: by eexists; [by apply hred_refl|]; cbn; by constructor.
      destruct nth_error eqn:hnth.
      2: { eapply All2_nth_error_None in Hs as ->; tea. by eexists; [by apply hred_refl|]; cbn; by constructor. }
      eapply All2_nth_error_Some in Hs as (t' & -> & Ht); tea.
      by eapply stred_lift.
Qed.


Lemma stred_step t u v : t =>s u -> u ≡>1 v -> t =>s v.
Proof.
  intros Xtu Xuv.
  induction Xtu in v, Xuv. destruct X.
  eapply stred_hred; tea. clear t h; rename t' into t.
  destruct Xuv.
  - destruct X as [na A t' t'' u' u''].
    depelim Xtu.
    specialize (IXu.1 _ ltac:(eassumption)) as Xu'. clear IXu Xu0 Xu.
    apply snd in IXt.
    destruct IXt.
    apply stred_hred with (tApp t'0 u). 1: { clear -h. induction h. - by constructor. - econstructor 2; tea. constructor 2. by constructor. }
    clear t0 h; rename t'0 into t.
    depelim Xtu.
    specialize (IXt.1 _ ltac:(eassumption)) as Xt'. clear IXA IXt Xt0 XA Xt.
    eapply stred_hred1.
    + econstructor. constructor.
    + apply stred_subst; tea. repeat (constructor; tea).
  - destruct Xtu; repeat match goal with H : _ × _ |- _ => destruct H as [?H ?H] end.
    all: depelim X.
    + apply stred_clos; constructor.
    + apply stred_clos; constructor; eauto. congruence.
    + apply stred_clos; constructor; eauto.
    + apply stred_clos; constructor; eauto. congruence.
    + apply stred_clos; constructor. congruence.
Qed.

Lemma stred_init TC Σ Γ t T : Σ ;;; Γ ⊢ t : T -> t =>s t.
Proof.
  induction 1 using typing_rect with (PΓ := fun _ => True) (Pj := fun Γ => lift_wf_term (fun t => t =>s t)) => //.
  - destruct X0 as (? & ? & ? & ?); cbn in *.
    split; tas.
  - apply stred_clos; constructor.
  - apply stred_clos; constructor; eauto.
  - apply stred_clos; constructor; eauto.
    apply IHX.
  - apply stred_clos; constructor; eauto.
    apply IHX.
  - apply stred_clos; constructor; eauto.
Qed.
























































Module UntypedTrial.


Reserved Notation "t ~>0 t'" (at level 50, t' at next level).
Reserved Notation "t ~>h t'" (at level 50, t' at next level).
Reserved Notation "t ~>h* t'" (at level 50, t' at next level).
Reserved Notation "t ~h1 t'" (at level 50, t' at next level).
Reserved Notation "t ~h1 t' 'with' R" (at level 50, t', R at next level).
Reserved Notation "t ~h1 t' 'on' H 'with' R" (at level 50, t', H, R at next level).
Reserved Notation "t ~R t'" (at level 50, t' at next level).
Reserved Notation "t ~R' t' 'on' H" (at level 50, t', H at next level).
Reserved Notation "t =>s t'" (at level 50, t' at next level).
Reserved Notation "t =>s t' 'on' H 'with' P" (at level 50, t', H, P at next level).
Reserved Notation "t ≡>0 t'" (at level 50, t' at next level).
Reserved Notation "t ≡>0 t' 'with' R" (at level 50, t', R at next level).
Reserved Notation "t ≡>0 t' 'on' H 'with' R" (at level 50, t', H, R at next level).
Reserved Notation "t ≡>1 t'" (at level 50, t' at next level).
Reserved Notation "t ~ t'" (at level 50, t' at next level).
Reserved Notation "t ~ t' 'with' R , R' , R''" (at level 50, t', R, R', R'' at next level).
Reserved Notation "t ~ t' 'on' H 'with' R" (at level 50, t', H, R at next level).

Set Elimination Schemes.

Inductive red0 : term -> term -> Type :=
  | red0_beta na A t u : tApp (tLambda na A t) u ~>0 t {0 := u}
where "t ~>0 t'" := (red0 t t').
Derive Signature for red0.

Section Inner.
Variable (R : term -> term -> Type).
Notation "t ~R t'" := (R t t').
Variable (R' : forall t t', t ~R t' -> Type).
Notation "t ~R' t' 'on' H" := (R' t t' H).


Inductive pred0 : forall (t t' : term), Type :=
  | pred0_beta na A t t' u u' :
      [(Xt : t ~R t')] ->
      [(Xu : u ~R u')] ->
      tApp (tLambda na A t) u ≡>0 t' { 0 := u' }
where "t ≡>0 t' " := (pred0 t t') (only parsing).
Derive Signature for pred0.

Inductive pred0ε : forall (t t' : term), t ≡>0 t' -> Type :=
  | pred0ε_beta na A t t' u u' :
      [(Xt : t ~R t')] ->
      [(IXt : t ~R' t' on Xt)] ->
      [(Xu : u ~R u')] ->
      [(IXu : u ~R' u' on Xu)] ->
      tApp (tLambda na A t) u ≡>0 t' { 0 := u' } on (⌈pred0_beta)⌋ with R'
where "t ≡>0 t' 'on' p 'with' R'" := (pred0ε t t' p) (only parsing).
Derive Signature for pred0ε.


Inductive head_context1_closure : forall (t t' : term), Type :=
  | hclos1_appl t t' u :
      [(Xt : t ~R t')] ->
      tApp t u ~h1 tApp t' u
where "t ~h1 t'" := (head_context1_closure t t') (only parsing).
Derive Signature for head_context1_closure.

Inductive head_context1_closureε : forall (t t' : term), t ~h1 t' -> Type :=
  | hclos1ε_appl t t' u :
      [(Xt : t ~R t')] ->
      [(IXt : t ~R' t' on Xt)] ->
      tApp t u ~h1 tApp t' u on ⌈hclos1_appl⌋ with R'
where "t ~h1 t' 'on' p 'with' R'" := (head_context1_closureε t t' p) (only parsing).


Inductive context_closure Rα Rs : forall (t t' : term), Type :=
  | clos_rel n :
      tRel n ~ tRel n

  | clos_lambda na na' A A' t t' :
      [(Xα : Rα na na')] ->
      [(XA : A ~R A')] ->
      [(Xt : t ~R t')] ->
      tLambda na A t ~ tLambda na' A' t'

  | clos_app t t' u u' :
      [(Xt : t ~R t')] ->
      [(Xu : u ~R u')] ->
      tApp t u ~ tApp t' u'

  | clos_prod na na' A A' B B' :
      [(Xα : Rα na na')] ->
      [(XA : A ~R A')] ->
      [(XB : B ~R B')] ->
      tProd na A B ~ tProd na' A' B'

  | clos_sort s s' :
      [(Xs : Rs s s')] ->
      tSort s ~ tSort s'
where "t ~ t' " := (context_closure _ _ t t') (only parsing).
Notation "t ~ t' 'with' R , R' , R'' " := (@context_closure R' R'' t t') (only parsing).
Derive Signature for context_closure.

Inductive context_closureε Rα Rs : forall (t t' : term), t ~ t' with R, Rα, Rs -> Type :=
  | closε_rel n :
      tRel n ~ tRel n on ⌈clos_rel⌋ with R'

  | closε_lambda na na' A A' t t' :
      [(Xα : Rα na na')] ->
      [(XA : A ~R A')] ->
      [(IXA : A ~R' A' on XA)] ->
      [(Xt : t ~R t')] ->
      [(IXt : t ~R' t' on Xt)] ->
      tLambda na A t ~ tLambda na' A' t' on ⌈clos_lambda⌋ with R'

  | closε_app t t' u u' :
      [(Xt : t ~R t')] ->
      [(IXt : t ~R' t' on Xt)] ->
      [(Xu : u ~R u')] ->
      [(IXu : u ~R' u' on Xu)] ->
      tApp t u ~ tApp t' u' on ⌈clos_app⌋ with R'

  | closε_prod na na' A A' B B' :
      [(Xα : Rα na na')] ->
      [(XA : A ~R A')] ->
      [(IXA : A ~R' A' on XA)] ->
      [(XB : B ~R B')] ->
      [(IXB : B ~R' B' on XB)] ->
      tProd na A B ~ tProd na' A' B' on ⌈clos_prod⌋ with R'

  | closε_sort s s' :
      [(Xs : Rs s s')] ->
      tSort s ~ tSort s' on ⌈clos_sort⌋ with R'
where "t ~ t' 'on' p 'with' R'" := (context_closureε _ _ t t' p) (only parsing).
Derive Signature for context_closureε.

End Inner.
Notation "t ≡>0 t' " := (pred0 _ t t').
Notation "t ≡>0 t' 'with' R " := (pred0 R t t').
Notation "t ≡>0 t' 'on' p 'with' R'" := (pred0ε _ R' t t' p).
Notation "t ~h1 t' 'with' R" := (head_context1_closure R t t').
Notation "t ~h1 t' 'on' H 'with' R'" := (head_context1_closureε _ R' t t' H).
Notation "t ~ t' " := (context_closure _ _ _ t t').
Notation "t ~ t' 'with' R , R' , R'' " := (context_closure R R' R'' t t').
Notation "t ~ t' 'on' p 'with' R'" := (context_closureε _ R' _ _ t t' p).

Unset Elimination Schemes.



Lemma pred0_toε R R' t t' :
  [(p : t ≡>0 t' with R)] ->
  [(X t t' : [(H : R t t')] -> R' t t' H)] ->
  t ≡>0 t' on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma pred0ε_fmap R R' R'' t t' :
  [(p : t ≡>0 t' with R)] ->
  [(H : t ≡>0 t' on p with R')] ->
  [(X t t' H : R' t t' H -> R'' t t' H)] ->
  t ≡>0 t' on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.


Lemma context_closure_toε R R' Rα Rs t t' :
  [(p : t ~ t' with R, Rα, Rs)] ->
  [(X t t' : [(H : R t t')] -> R' t t' H)] ->
  t ~ t' on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closure_fmap R R' Rα Rs t t' :
  [(p : t ~ t' with R, Rα, Rs)] ->
  [(X t t' : [(H : R t t')] -> R' t t')] ->
  t ~ t' with R', Rα, Rs.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closureε_fmap R R' R'' Rα Rs t t' :
  [(p : t ~ t' with R, Rα, Rs)] ->
  [(H : t ~ t' on p with R')] ->
  [(X t t' H : R' t t' H -> R'' t t' H)] ->
  t ~ t' on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closure_ofε R R' R'' Rα Rs t t' :
  [(p : t ~ t' with R, Rα, Rs)] ->
  [(H : t ~ t' on p with R')] ->
  [(X t t' H : R' t t' H -> R'' t t')] ->
  t ~ t' with R'', Rα, Rs.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma head_context1_closure_toε R R' t t' :
  [(p : t ~h1 t' with R)] ->
  [(X t t' : [(H : R t t')] -> R' t t' H)] ->
  t ~h1 t' on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma head_context1_closureε_fmap R R' R'' t t' :
  [(p : t ~h1 t' with R)] ->
  [(H : t ~h1 t' on p with R')] ->
  [(X t t' H : R' t t' H -> R'' t t' H)] ->
  t ~h1 t' on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.


Hint Resolve pred0_toε pred0_ofε pred0ε_fmap ext_conv_toε ext_conv_ofε ext_convε_fmap
  ext_eq_toε ext_eq_ofε ext_eqε_fmap
  context_closure_toε context_closure_ofε context_closureε_fmap context_closure_fmap
  context1_closure_toε context1_closure_ofε context1_closureε_fmap
  head_context1_closure_toε head_context1_closure_ofε head_context1_closureε_fmap
  : fmap.







Inductive pred1 t u :=
  | pred1_pred0 :
      [(X : t ≡>0 u with pred1)] ->
      t ≡>1 u

  | pred1_clos :
      [(X : t ~ u with pred1, eq, eq)] ->
      t ≡>1 u
where "t ≡>1 t'" := (pred1 t t').
Derive Signature for pred1.

Definition pred1_rect P :
  [(Xpred0 t u :
      [(H : t ≡>0 u with pred1)] ->
      [(X : t ≡>0 u on H with P)] ->
      P t u (pred1_pred0 _ _ H))] ->
  [(XClosure t u :
      [(H : t ~ u with pred1, eq, eq)] ->
      [(X : t ~ u on H with P)] ->
      P t u (pred1_clos _ _ H))] ->

  forall t u, [(X : t ≡>1 u)] -> P t u X.
Proof.
  intros.
  revert t u X.
  fix Xrec 3.
  intros t_ u_ []; try clear t_; try clear u_; try clear T_.
  - unshelve eapply Xpred0; eauto with fmap.
  - unshelve eapply XClosure; tea. now eauto with fmap.
Defined.

Inductive hred1 t t' :=
  | hred1_red0 :
    [(X : t ~>0 t')] -> t ~>h t'

  | hred1_clos :
    [(X : t ~h1 t' with hred1)] -> t ~>h t'

where "t ~>h t'" := (hred1 t t').
Derive Signature for hred1.

Definition hred1_rect P :
  [(Xred0 t u : [(H : t ~>0 u)] -> P t u (hred1_red0 _ _ H))] ->
  [(XClosure t u :
      [(Htu : t ~h1 u with hred1)] ->
      [(Xtu : t ~h1 u on Htu with P)] ->
      P t u (hred1_clos _ _ Htu))] ->
  forall t u, [(X : t ~>h u)] -> P t u X.
Proof.
  intros.
  revert t u X.
  fix Xrec 3.
  intros t u X; destruct X.
  - apply Xred0; eauto.
  - unshelve eapply XClosure; eauto with fmap.
Defined.
Definition hred1_ind := hred1_rect.

Inductive hred t t' :=
  | hred_refl :
    t = t' -> t ~>h* t'

  | hred_step u :
    t ~>h u -> u ~>h* t' -> t ~>h* t'

where "t ~>h* t'" := (hred t t').
Derive Signature for hred.

Definition hred_rect P :
  [(Xrefl t : P t t (hred_refl t t eq_refl))] ->
  [(Xstep t u v : [(H : t ~>h u)] -> [(X : u ~>h* v)] -> [(IHX : P u v X)] -> P t v (hred_step _ _ _ H X))] ->
  forall t u, [(X : t ~>h* u)] -> P t u X.
Proof.
  intros.
  revert t u X.
  fix Xrec 3.
  intros t u X; destruct X.
  - subst u. apply Xrefl; eauto.
  - unshelve eapply Xstep; eauto with fmap.
Defined.
Definition hred_ind := hred_rect.

Lemma hred_clos t t' :
  t ~h1 t' with hred ->
  t ~>h* t'.
Proof.
  destruct 1.
  - induction Xt.
    + by constructor.
    + eapply hred_step; tea.
      by constructor.
Qed.


Inductive standard_red t u :=
  | stredc t' :
    [(h : t ~>h* t')] ->
    [(X : t' ~ u with standard_red, eq, eq)] ->
    t =>s u

where "t =>s t'" := (standard_red t t').
Derive Signature for standard_red.


Inductive standard_redε R t u : t =>s u -> Type :=
  | stredcε t' :
    [(h : t ~>h* t')] ->
    [(Htu : t' ~ u with standard_red, eq, eq)] ->
    [(Xtu : t' ~ u on Htu with (fun t t' H => R t t' H × standard_redε R t t' H))] ->
    t =>s u on ⌈stredc⌋ with R

where "t =>s t' 'on' H 'with' R" := (standard_redε R t t' H).
Derive Signature for standard_redε.

Definition standard_red_rect P :
  [(X t u H : [(X : t =>s u on H with P)] -> P t u H)] ->
  forall t u, [(H : t =>s u)] -> P t u H.
Proof.
  intros Xr.
  enough (forall t u (X : t =>s u), P t u X × t =>s u on X with P).
  { intros; now apply X. }
  fix Xrec 3.
  intros t v H.
  eenough _ as X.
  { split. 2: exact X. now apply Xr. }
  destruct H; econstructor; tea.
  all: eapply context_closure_toε; intros; by apply Xrec.
Defined.
Definition standard_red_ind := standard_red_rect.


Definition stred_hred1 t u v : t ~>h u -> u =>s v -> t =>s v.
Proof.
  intros h [u' h' X].
  exists u'; tea.
  now eapply hred_step.
Defined.

Definition stred_hred t u v : t ~>h* u -> u =>s v -> t =>s v.
Proof.
  induction 1.
  - intro; assumption.
  - intro. eapply stred_hred1; eauto.
Defined.

Definition stred_clos t u : t ~ u with standard_red, eq, eq -> t =>s u.
Proof.
  intro X.
  exists t; tas. by apply hred_refl.
Defined.



Lemma red0_discriminate t u :
  t ~>0 u ->
  red0_discr t.
Proof.
  induction 1 => //=.
Qed.
Lemma hred1_discriminate t u :
  t ~>h u ->
  hred1_discr t.
Proof.
  induction 1 => //=.
  - induction H => //.
  - induction Xtu => //=.
    now destruct t.
Qed.
Lemma hred_discriminate t u :
  t ~>h* u ->
  ~~ hred1_discr t ->
  t = u.
Proof.
  induction 1 using hred_rect => //=.
  apply hred1_discriminate in H as ->.
  intro => //.
Qed.

Lemma head_context1_discriminate t u :
  t ~h1 u with hred1 ->
  head_context1_discr t.
Proof.
  induction 1 => //=.
  now eapply hred1_discriminate.
Qed.

Lemma red0_inj t u u' :
  t ~>0 u ->
  t ~>0 u' ->
  u = u'.
Proof.
  induction 1 in u' => //=; eauto.
  intro H.
  depelim H; eauto.
Qed.

Lemma hred1_inj t u u' :
  t ~>h u ->
  t ~>h u' ->
  u = u'.
Proof.
  induction 1 in u' => //=; eauto.
  - apply red0_discriminate in H as h.
    induction 1 => //=; eauto.
    + now eapply red0_inj.
    + apply head_context1_discriminate in Htu as H'.
      destruct t => //. destruct t1 => //.
  - apply head_context1_discriminate in Htu as H.
    destruct Xtu.
    intro X'.
    depind X' => //=; eauto.
    + apply red0_discriminate in H as H'.
      destruct t0 => //.
    + depelim Htu.
      f_equal. now eapply IXt.
Qed.

Lemma hred_inj t u u' :
  t ~>h* u ->
  t ~>h* u' ->
  ~~ hred1_discr u -> ~~ hred1_discr u' ->
  u = u'.
Proof.
  intros X X' H H'.
  induction X in u', H, X', H' using hred_rect.
  - by apply hred_discriminate in X'.
  - have {}IHX X := IHX u' X H H'.
    clear X H.
    induction X' in H', H0, IHX using hred_rect; eauto.
    { apply hred1_discriminate in H0. now rewrite H0 in H'. }
    eapply IHX.
    eapply hred1_inj in H as ->; tea.
Qed.

Lemma stred_nhred_inv t u :
  ~~ hred1_discr t ->
  t =>s u ->
  t ~ u with standard_red, eq, eq.
Proof.
  intros H [u' h X].
  by apply hred_discriminate in h as <-.
Qed.


Lemma stred_lift n k t u :
  t =>s u -> lift n k t =>s lift n k u.
Proof.
  induction 1 in k. destruct X0.
  exists (lift n k t').
  - clear Htu Xtu.
    induction h in k.
    + by constructor.
    + eapply hred_step; eauto.
      clear h IHh.
      induction H in k.
      * eapply hred1_red0.
        induction H in k.
        --cbn. relativize (lift _ _ (_ {0 := _})).
          1: constructor.
          rewrite distr_lift_subst //=.
      * eapply hred1_clos.
        destruct Xtu.
        --cbn.
          by constructor.
  - destruct Xtu; repeat match goal with H : _ × _ |- _ => destruct H as [?H ?H] end.
    all: cbn; by constructor.
Qed.


Lemma stred_subst s s' k t u :
  All2 (fun t u => t =>s u) s s' ->
  t =>s u ->
  subst s k t =>s subst s' k u.
Proof.
  intro Hs.
  induction 1 in k. destruct X0.
  eapply stred_hred with (subst s k t').
  - clear Htu Xtu.
    induction h in k.
    + by constructor.
    + eapply hred_step; eauto.
      clear h IHh.
      induction H in k.
      * eapply hred1_red0.
        induction H in k.
        --cbn. relativize (subst _ _ (_ {0 := _})).
          1: constructor.
          rewrite distr_subst //=.
      * eapply hred1_clos.
        destruct Xtu.
        --cbn.
          by constructor.
  - destruct Xtu; repeat match goal with H : _ × _ |- _ => destruct H as [?H ?H] end.
    all: try solve [ eexists (subst s k _); [by apply hred_refl|]; cbn; by constructor ].
    * cbn.
      rewrite -(All2_length Hs).
      destruct (leb_spec_Set k n).
      2: by eexists; [by apply hred_refl|]; cbn; by constructor.
      destruct nth_error eqn:hnth.
      2: { eapply All2_nth_error_None in Hs as ->; tea. by eexists; [by apply hred_refl|]; cbn; by constructor. }
      eapply All2_nth_error_Some in Hs as (t' & -> & Ht); tea.
      by eapply stred_lift.
Qed.


Lemma stred_step t u v : t =>s u -> u ≡>1 v -> t =>s v.
Proof.
  intros Xtu Xuv.
  induction Xtu in v, Xuv. destruct X.
  eapply stred_hred; tea. clear t h; rename t' into t.
  destruct Xuv.
  - destruct X as [na A t' t'' u' u''].
    depelim Xtu.
    specialize (IXu.1 _ ltac:(eassumption)) as Xu'. clear IXu Xu0 Xu.
    apply snd in IXt.
    destruct IXt.
    apply stred_hred with (tApp t'0 u). 1: { clear -h. induction h. - by constructor. - econstructor 2; tea. constructor 2. by constructor. }
    clear t0 h; rename t'0 into t.
    depelim Xtu.
    specialize (IXt.1 _ ltac:(eassumption)) as Xt'. clear IXA IXt Xt0 XA Xt.
    eapply stred_hred1.
    + econstructor. constructor.
    + apply stred_subst; tea. repeat (constructor; tea).
  - destruct Xtu; repeat match goal with H : _ × _ |- _ => destruct H as [?H ?H] end.
    all: depelim X.
    + apply stred_clos; constructor.
    + apply stred_clos; constructor; eauto. congruence.
    + apply stred_clos; constructor; eauto.
    + apply stred_clos; constructor; eauto. congruence.
    + apply stred_clos; constructor. congruence.
Qed.

Lemma stred_init TC Σ Γ t T : Σ ;;; Γ ⊢ t : T -> t =>s t.
Proof.
  induction 1 using typing_rect with (PΓ := fun _ => True) (Pj := fun Γ => lift_wf_term (fun t => t =>s t)) => //.
  - destruct X0 as (? & ? & ? & ?); cbn in *.
    split; tas.
  - apply stred_clos; constructor.
  - apply stred_clos; constructor; eauto.
  - apply stred_clos; constructor; eauto.
    apply IHX.
  - apply stred_clos; constructor; eauto.
    apply IHX.
  - apply stred_clos; constructor; eauto.
Qed.













Reserved Notation "Σ  ;;; Γ ⊢ t ~R t'" (at level 50, Γ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t ~R' t' 'on' H" (at level 50, Γ, t, t', H at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t ~ t'" (at level 50, Γ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' 'with' R , R' , R''" (at level 50, Γ, t, t', R, R', R'' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' 'on' H 'with' R" (at level 50, Γ, t, t', H, R at next level).


Section Closure.
Local Set Elimination Schemes.

Context Σ (R : forall Γ (t t' : term), Type).
Context (R' : forall Γ t t', R Γ t t' -> Type).

Notation " Σ ;;; Γ ⊢ t ~R t' " := (R Γ t t') (only parsing).
Notation " Σ ;;; Γ ⊢ t ~R' t' 'on' H" := (R' Γ t t' H) (only parsing).

Inductive context_closure Rα Rs Γ : forall (t t' : term), Type :=
  | clos_rel n :
      Σ ;;; Γ ⊢ tRel n ~ tRel n

  | clos_lambda na na' A A' t t' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A')] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t')] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t'

  | clos_app t t' u u' :
      [(Xt : Σ ;;; Γ ⊢ t ~R t')] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u')] ->
      Σ ;;; Γ ⊢ tApp t u ~ tApp t' u'

  | clos_prod na na' A A' B B' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A')] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B')] ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B'

  | clos_sort s s' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s'
where "Σ ;;; Γ ⊢ t ~ t'" := (context_closure _ _ Γ t t') (only parsing).
Notation " Σ ;;; Γ ⊢ t ~ t' 'with' R , R' , R'' " := (@context_closure R' R'' Γ t t') (only parsing).
Derive Signature for context_closure.

Inductive context_closureε Rα Rs Γ : forall (t t' : term), Σ ;;; Γ ⊢ t ~ t' with R, Rα, Rs -> Type :=
  | closε_rel n :
      Σ ;;; Γ ⊢ tRel n ~ tRel n on ⌈clos_rel⌋ with R'

  | closε_lambda na na' A A' t t' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A')] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' on XA)] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t')] ->
      [(IXt : Σ ;;; Γ ,, vass na A ⊢ t ~R' t' on Xt)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' on ⌈clos_lambda⌋ with R'

  | closε_app t t' u u' :
      [(Xt : Σ ;;; Γ ⊢ t ~R t')] ->
      [(IXt : Σ ;;; Γ ⊢ t ~R' t' on Xt)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u')] ->
      [(IXu : Σ ;;; Γ ⊢ u ~R' u' on Xu)] ->
      Σ ;;; Γ ⊢ tApp t u ~ tApp t' u' on ⌈clos_app⌋ with R'

  | closε_prod na na' A A' B B' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A')] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' on XA)] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B')] ->
      [(IXB : Σ ;;; Γ ,, vass na A ⊢ B ~R' B' on XB)] ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B' on ⌈clos_prod⌋ with R'

  | closε_sort s s' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' on ⌈clos_sort⌋ with R'
where " Σ ;;; Γ ⊢ t ~ t' 'on' p 'with' R'" := (context_closureε _ _ Γ t t' p) (only parsing).
Derive Signature for context_closureε.
End Closure.

Notation " Σ ;;; Γ ⊢ t ~ t' " := (context_closure Σ _ _ _ Γ t t').
Notation " Σ ;;; Γ ⊢ t ~ t' 'with' R , R' , R'' " := (context_closure Σ R R' R'' Γ t t').
Notation " Σ ;;; Γ ⊢ t ~ t' 'on' p 'with' R'" := (context_closureε Σ _ R' _ _ Γ t t' p).


Lemma context_closure_toε Σ R R' Rα Rs Ξ t t' :
  [(p : Σ ;;; Ξ ⊢ t ~ t' with R, Rα, Rs)] ->
  [(X Ξ t t' : [(H : R Ξ t t')] -> R' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t ~ t' on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closureε_fmap Σ R R' R'' Rα Rs Ξ t t' :
  [(p : Σ ;;; Ξ ⊢ t ~ t' with R, Rα, Rs)] ->
  [(H : Σ ;;; Ξ ⊢ t ~ t' on p with R')] ->
  [(X Ξ t t' : [(H : R Ξ t t')] -> R' Ξ t t' H -> R'' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t ~ t' on p with R''.
Proof.
  intros.
  induction H.
  all: try now econstructor.
Defined.

Hint Resolve context_closure_toε context_closureε_fmap : fmap.

Reserved Notation "t ~>η0 t'" (at level 50, t' at next level).
Reserved Notation "t ~>η t'" (at level 50, t' at next level).

Set Elimination Schemes.
Inductive ηred0 t : term -> Type :=
  | ηred0_prod na A :
    t ~>η0 tLambda na A (tApp (lift0 1 t) (tRel 0))
where "t ~>η0 t'" := (ηred0 t t').
Unset Elimination Schemes.

Inductive ηpred t t' :=
  | ηred1_ηred0 :
    t ~>η0 t' ->
    t ~>η t'

  | ηred1_clos :
    t ~ t' with ηpred, eq, eq ->
    t ~>η t'
where "t ~>η t'" := (ηpred t t').

Definition ηpred_rect P :
  [(Xηred0 t u :
      [(H : t ~>η0 u)] ->
      P t u (ηred1_ηred0 _ _ H))] ->
  [(XClosure t u :
      [(H : t ~ u with ηpred, eq, eq)] ->
      [(X : t ~ u on H with P)] ->
      P t u (ηred1_clos _ _ H))] ->

  forall t u, [(X : t ~>η u)] -> P t u X.
Proof.
  intros.
  revert t u X.
  fix Xrec 3.
  intros ?? X. destruct X.
  - unshelve eapply Xηred0; eauto with fmap.
  - unshelve eapply XClosure; tea. now eauto with fmap.
Defined.


Lemma pred_ηpred_commut t u v :
  t ≡>1 u ->
  t ~>η v ->
  ∑ w, u ~>η w × v ≡>1 w.
Proof.
  intros Xred Xredη.
  induction Xredη in u, Xred.
  - destruct H.
    exists (tLambda na A (tApp (lift0 1 u) (tRel 0))).
    split.
    + constructor. constructor.
    + have {}Xred : lift0 1 t ≡>1 lift0 1 u by admit.
      apply pred1_clos. constructor; trea. 1: admit.
      apply pred1_clos. constructor; trea.
      apply pred1_clos. constructor.
  - destruct Xred.
    + destruct X0.
      depelim X.
    + destruct X; depelim X0.




(*
Instance hRtP : RedtoPi := {| RTPit Σ Γ t na A B := t ~>h* tProd na A B |}.
Instance hRtS : RedtoSort := {| RTSit Σ Γ t s := t ~>h* tSort s |}.


Reserved Notation "Σ ;;; Γ ⊢ t ~>η0 t'" (at level 50, Γ, t, t' at next level).
Reserved Notation "Σ ;;; Γ ⊢ t ~>η t'" (at level 50, Γ, t, t' at next level).

Set Elimination Schemes.
Inductive ηred0 Σ Γ t : term -> Type :=
  | ηred0_prod na A B :
    [(Xt : Σ ;;; Γ ⊢ t ▷Π(na : A), B)] ->
    Σ ;;; Γ ⊢ t ~>η0 tLambda na A (tApp (lift0 1 t) (tRel 0))
where "Σ ;;; Γ ⊢ t ~>η0 t'" := (ηred0 Σ Γ t t').
Unset Elimination Schemes.

Inductive ηpred Σ Γ t t' :=
  | ηred1_ηred0 :
    Σ ;;; Γ ⊢ t ~>η0 t' ->
    Σ ;;; Γ ⊢ t ~>η t'

  | ηred1_clos :
    Σ ;;; Γ ⊢ t ~ t' with ηpred Σ, eq, eq ->
    Σ ;;; Γ ⊢ t ~>η t'
where "Σ ;;; Γ ⊢ t ~>η t'" := (ηpred Σ Γ t t').

Definition ηpred_rect Σ P :
  [(Xηred0 Γ t u :
      [(H : Σ ;;; Γ ⊢ t ~>η0 u)] ->
      P Γ t u (ηred1_ηred0 _ _ _ _ H))] ->
  [(XClosure Γ t u :
      [(H : Σ ;;; Γ ⊢ t ~ u with ηpred Σ, eq, eq)] ->
      [(X : Σ ;;; Γ ⊢ t ~ u on H with P)] ->
      P Γ t u (ηred1_clos _ _ _ _ H))] ->

  forall Γ t u, [(X : Σ ;;; Γ ⊢ t ~>η u)] -> P Γ t u X.
Proof.
  intros.
  revert Γ t u X.
  fix Xrec 4.
  intros ??? X. destruct X.
  - unshelve eapply Xηred0; eauto with fmap.
  - unshelve eapply XClosure; tea. now eauto with fmap.
Defined.


Lemma pred_ηpred_commut Σ Γ t u v :
  t ≡>1 u ->
  Σ ;;; Γ ⊢ t ~>η v ->
  ∑ w, Σ ;;; Γ ⊢ u ~>η w × v ≡>1 w.
Proof.
  intros Xred Xredη.
  induction Xredη in u, Xred.
  - destruct H. *)




End InferTypeTrial.





















Module Untyped.

Reserved Notation "Σ  ;;; Γ ⊢ t ~R t'" (at level 50, Γ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t ~R' t' 'on' H" (at level 50, Γ, t, t', H at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =R t'" (at level 50, Γ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =R' t' 'on' H" (at level 50, Γ, t, t', H at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t ≤R[ pb ] t'" (at level 50, Γ, pb, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t ≤R'[ pb ] t' 'on' H" (at level 50, Γ, pb, t, t', H at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t ~ t'" (at level 50, Γ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' 'with' R , R' , R''" (at level 50, Γ, t, t', R, R', R'' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' 'on' H 'with' R" (at level 50, Γ, t, t', H, R at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =λ t'" (at level 50, Γ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =λ t' 'with' R" (at level 50, Γ, t, t', R at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =λ t' 'on' H 'with' R'" (at level 50, Γ, t, t', H, R' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =ext t'" (at level 50, Γ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' 'with' R" (at level 50, Γ, t, t', R at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' 'on' H 'with' R'" (at level 50, Γ, t, t', H, R' at next level).
Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t'" (at level 50, Γ, pb, t, t' at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'").
Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' 'with' R" (at level 50, Γ, pb, t, t', R at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  'with'  R").
Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' 'on' H 'with' R'" (at level 50, Γ, pb, t, t', H, R' at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  'on'  H  'with'  R'").


Definition prod_spine := list (aname × term).
Fixpoint it_mkProd (Δ : prod_spine) T :=
  match Δ with [] => T | nA :: Δ => tProd nA.1 nA.2 (it_mkProd Δ T) end.
Definition mkvass nA := vass nA.1 nA.2.

Module Export isTermRel.
Definition relevance_context := list relevance.

Implicit Types (Ξ : relevance_context).
Local Set Elimination Schemes.
Inductive isTermRel Σ Ξ : term -> relevance -> Type :=
  | rel_Rel n r :
      nth_error Ξ n = Some r ->
      isTermRel Σ Ξ (tRel n) r

  | rel_Sort s :
      isTermRel Σ Ξ (tSort s) Relevant

  | rel_Prod na A B :
      isTermRel Σ Ξ (tProd na A B) Relevant

  | rel_Lambda na A t r :
      isTermRel Σ (Ξ ,, na.(binder_relevance)) t r ->
      isTermRel Σ Ξ (tLambda na A t) r

  | rel_App t u r :
      isTermRel Σ Ξ t r ->
      isTermRel Σ Ξ (tApp t u) r.
Derive Signature for isTermRel.
Unset Elimination Schemes.

Lemma isTermRel_uniq Σ Ξ t r r' :
  isTermRel Σ Ξ t r -> isTermRel Σ Ξ t r' ->
  r = r'.
Proof.
  induction 1 in r'.
  all: intro X'; depelim X'.
  all: try congruence.
  - by eapply IHX.
  - by eapply IHX.
Qed.

Lemma nth_error_insertion {A} (Γ Γ' Γ'' : list A) n :
  nth_error (Γ ,,, Γ' ,,, Γ'') (if #|Γ''| <=? n then #|Γ'| + n else n) =
  nth_error (Γ ,,, Γ'') n.
Proof.
  destruct (Nat.leb_spec #|Γ''| n).
  - rewrite -app_context_assoc !nth_error_app_ge //.
    1,2: by len.
  - rewrite !nth_error_app_lt //.
Qed.



Lemma isTermRel_lift Σ Ξ Ξ' Ξ'' t r :
  isTermRel Σ (Ξ ,,, Ξ'') t r ->
  isTermRel Σ (Ξ ,,, Ξ' ,,, Ξ'') (lift #|Ξ'| #|Ξ''| t) r.
Proof.
  intro X.
  dependent induction X; rename Ξ0 into Ξ; cbn.
  - constructor.
    rewrite nth_error_insertion //.
  - constructor.
  - constructor.
  - constructor.
    by eapply IHX with (Ξ'' := Ξ'' ,, _).
  - constructor.
    by apply IHX.
Qed.

Lemma isTermRel_unlift Σ Ξ Ξ' Ξ'' t₀ r :
  isTermRel Σ (Ξ ,,, Ξ' ,,, Ξ'') (lift #|Ξ'| #|Ξ''| t₀) r ->
  isTermRel Σ (Ξ ,,, Ξ'') t₀ r.
Proof.
  intro X.
  dependent induction X; destruct t₀; noconf H; rename Ξ0 into Ξ; cbn.
  - constructor.
    rewrite nth_error_insertion // in e.
  - constructor.
  - constructor.
  - constructor.
    by eapply IHX with (Ξ'' := Ξ'' ,, _).
  - constructor.
    by eapply IHX.
Qed.

Lemma isTermRel_subst Σ Ξ Ξ' Ξ'' s t r :
  All2 (isTermRel Σ Ξ) s Ξ' ->
  isTermRel Σ (Ξ ,,, Ξ' ,,, Ξ'') t r ->
  isTermRel Σ (Ξ ,,, Ξ'') (subst s #|Ξ''| t) r.
Proof.
  intros Xs X.
  dependent induction X; rename Ξ0 into Ξ; cbn.
  - destruct (leb_spec_Set #|Ξ''| n).
    1: rewrite nth_error_app_ge // in e.
    1: destruct (nth_error s) eqn:es.
    + eapply All2_nth_error_Some in Xs as (r' & hnth & Xr); tea.
      eapply isTermRel_lift with (Ξ'' := []); cbn.
      relativize r; tea.
      rewrite nth_error_app_lt // in e.
      { by apply nth_error_Some_length in hnth. }
      congruence.
    + apply nth_error_None in es.
      rewrite (All2_length Xs) in es |- *.
      rewrite nth_error_app_ge // in e.
      constructor.
      rewrite nth_error_app_ge //.
      1: by lia.
      relativize (_ - _ - _); tea.
      lia.
    + constructor.
      rewrite !nth_error_app_lt // in e |- *.
  - constructor.
  - constructor.
  - constructor.
    eapply IHX with (Ξ'' := Ξ'' ,, _); trea.
  - constructor.
    by apply IHX.
Qed.

Lemma isTermRel_subst10 Σ Ξ u ur t r :
  isTermRel Σ (Ξ ,, ur) t r ->
  isTermRel Σ Ξ u ur ->
  isTermRel Σ Ξ (t {0 := u}) r.
Proof.
  intros.
  eapply isTermRel_subst with (Ξ' := [_]) (Ξ'' := []); tea.
  repeat constructor; tas.
Qed.

End isTermRel.

Implicit Types (Ξ : relevance_context).

Section Closure.
Local Set Elimination Schemes.

Context Σ (R : forall Ξ (t t' : term), Type).
Context (R' : forall Ξ t t', R Ξ t t' -> Type).

Notation " Σ ;;; Ξ ⊢ t ~R t' " := (R Ξ t t') (only parsing).
Notation " Σ ;;; Ξ ⊢ t ~R' t' 'on' H" := (R' Ξ t t' H) (only parsing).

Inductive eq_lambda_nodomain Σ Ξ : forall (t t' : term), Type :=
  | eqlam_nodom na na' A A' t t' :
      [(Xα : eq_binder_annot na na')] ->
      [(Xt : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t ~R t')] ->
      Σ ;;; Ξ ⊢ tLambda na A t =λ tLambda na' A' t'
where " Σ ;;; Ξ ⊢ t =λ t' " := (eq_lambda_nodomain Σ Ξ t t') (only parsing).
Derive Signature for eq_lambda_nodomain.

Inductive eq_lambda_nodomainε Ξ : forall (t t' : term), Σ ;;; Ξ ⊢ t =λ t' -> Type :=
  | eqlam_nodomε na na' A A' t t' :
      [(Xα : eq_binder_annot na na')] ->
      [(Xt : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t ~R t')] ->
      [(IXt : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t ~R' t' on Xt)] ->
      Σ ;;; Ξ ⊢ tLambda na A t =λ tLambda na' A' t' on ⌈eqlam_nodom⌋ with R'

where " Σ ;;; Ξ ⊢ t =λ t' 'on' p 'with' R'" := (eq_lambda_nodomainε Ξ t t' p) (only parsing).
Derive Signature for eq_lambda_nodomainε.

Inductive ext_eq Ξ : forall (t t' : term), Type :=
  | ext_eta_l na A t u :
      [(XR : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t ~R tApp (lift0 1 u) (tRel 0))] ->
      Σ ;;; Ξ ⊢ tLambda na A t =ext u

  | ext_eta_r na A t u :
      [(XR : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ tApp (lift0 1 t) (tRel 0) ~R u)] ->
      Σ ;;; Ξ ⊢ t =ext tLambda na A u

  | ext_eq_sprop t u :
      [(Xt : isTermRel Σ Ξ t Irrelevant)] ->
      [(Xu : isTermRel Σ Ξ u Irrelevant)] ->
      Σ ;;; Ξ ⊢ t =ext u
where " Σ ;;; Ξ ⊢ t =ext t' " := (ext_eq Ξ t t') (only parsing).
Derive Signature for ext_eq.

Inductive ext_eqε Ξ : forall (t t' : term), Σ ;;; Ξ ⊢ t =ext t' -> Type :=
  | extε_eta_l na A t u :
      [(XR : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t ~R tApp (lift0 1 u) (tRel 0))] ->
      [(IXR : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t ~R' tApp (lift0 1 u) (tRel 0) on XR)] ->
      Σ ;;; Ξ ⊢ tLambda na A t =ext u on ⌈ext_eta_l⌋ with R'

  | extε_eta_r na A t u :
      [(XR : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ tApp (lift0 1 t) (tRel 0) ~R u)] ->
      [(IXR : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ tApp (lift0 1 t) (tRel 0) ~R' u on XR)] ->
      Σ ;;; Ξ ⊢ t =ext tLambda na A u on ⌈ext_eta_r⌋ with R'

  | extε_eq_sprop t u :
      [(Xt : isTermRel Σ Ξ t Irrelevant)] ->
      [(Xu : isTermRel Σ Ξ u Irrelevant)] ->
      Σ ;;; Ξ ⊢ t =ext u on ⌈ext_eq_sprop⌋ with R'
where " Σ ;;; Ξ ⊢ t =ext t' 'on' p 'with' R'" := (ext_eqε Ξ t t' p) (only parsing).
Derive Signature for ext_eqε.


Inductive context_closure Rα Rs Ξ : forall (t t' : term), Type :=
  | clos_rel n :
      Σ ;;; Ξ ⊢ tRel n ~ tRel n

  | clos_lambda na na' A A' t t' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Ξ ⊢ A ~R A')] ->
      [(Xt : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t ~R t')] ->
      Σ ;;; Ξ ⊢ tLambda na A t ~ tLambda na' A' t'

  | clos_app t t' u u' :
      [(Xt : Σ ;;; Ξ ⊢ t ~R t')] ->
      [(Xu : Σ ;;; Ξ ⊢ u ~R u')] ->
      Σ ;;; Ξ ⊢ tApp t u ~ tApp t' u'

  | clos_prod na na' A A' B B' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Ξ ⊢ A ~R A')] ->
      [(XB : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ B ~R B')] ->
      Σ ;;; Ξ ⊢ tProd na A B ~ tProd na' A' B'

  | clos_sort s s' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Ξ ⊢ tSort s ~ tSort s'
where " Σ ;;; Ξ ⊢ t ~ t' " := (context_closure _ _ Ξ t t') (only parsing).
Notation " Σ ;;; Ξ ⊢ t ~ t' 'with' R , R' , R'' " := (@context_closure R' R'' Ξ t t') (only parsing).
Derive Signature for context_closure.

Inductive context_closureε Rα Rs Ξ : forall (t t' : term), Σ ;;; Ξ ⊢ t ~ t' with R, Rα, Rs -> Type :=
  | closε_rel n :
      Σ ;;; Ξ ⊢ tRel n ~ tRel n on ⌈clos_rel⌋ with R'

  | closε_lambda na na' A A' t t' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Ξ ⊢ A ~R A')] ->
      [(IXA : Σ ;;; Ξ ⊢ A ~R' A' on XA)] ->
      [(Xt : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t ~R t')] ->
      [(IXt : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t ~R' t' on Xt)] ->
      Σ ;;; Ξ ⊢ tLambda na A t ~ tLambda na' A' t' on ⌈clos_lambda⌋ with R'

  | closε_app t t' u u' :
      [(Xt : Σ ;;; Ξ ⊢ t ~R t')] ->
      [(IXt : Σ ;;; Ξ ⊢ t ~R' t' on Xt)] ->
      [(Xu : Σ ;;; Ξ ⊢ u ~R u')] ->
      [(IXu : Σ ;;; Ξ ⊢ u ~R' u' on Xu)] ->
      Σ ;;; Ξ ⊢ tApp t u ~ tApp t' u' on ⌈clos_app⌋ with R'

  | closε_prod na na' A A' B B' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Ξ ⊢ A ~R A')] ->
      [(IXA : Σ ;;; Ξ ⊢ A ~R' A' on XA)] ->
      [(XB : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ B ~R B')] ->
      [(IXB : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ B ~R' B' on XB)] ->
      Σ ;;; Ξ ⊢ tProd na A B ~ tProd na' A' B' on ⌈clos_prod⌋ with R'

  | closε_sort s s' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Ξ ⊢ tSort s ~ tSort s' on ⌈clos_sort⌋ with R'
where " Σ ;;; Ξ ⊢ t ~ t' 'on' p 'with' R'" := (context_closureε _ _ Ξ t t' p) (only parsing).
Derive Signature for context_closureε.
End Closure.

Notation " Σ ;;; Ξ ⊢ t ~ t' " := (context_closure Σ _ _ _ Ξ t t').
Notation " Σ ;;; Ξ ⊢ t ~ t' 'with' R , R' , R'' " := (context_closure Σ R R' R'' Ξ t t').
Notation " Σ ;;; Ξ ⊢ t ~ t' 'on' p 'with' R'" := (context_closureε Σ _ R' _ _ Ξ t t' p).
Notation " Σ ;;; Ξ ⊢ t =λ t' " := (eq_lambda_nodomain _ Σ Ξ t t').
Notation " Σ ;;; Ξ ⊢ t =λ t' 'with' R" := (eq_lambda_nodomain R Σ Ξ t t').
Notation " Σ ;;; Ξ ⊢ t =λ t' 'on' p 'with' R'" := (eq_lambda_nodomainε Σ _ R' Ξ t t' p).
Notation " Σ ;;; Ξ ⊢ t =ext t' " := (ext_eq Σ _ Ξ t t').
Notation " Σ ;;; Ξ ⊢ t =ext t' 'with' R" := (ext_eq Σ R Ξ t t').
Notation " Σ ;;; Ξ ⊢ t =ext t' 'on' p 'with' R'" := (ext_eqε Σ _ R' Ξ t t' p).


Section CumulAddon.
Local Set Elimination Schemes.

Context {cf} Σ (R : forall Ξ (pb : conv_pb) (t t' : term), Type).
Context (R' : forall Ξ pb t t', R Ξ pb t t' -> Type).

Notation "Σ ;;; Ξ ⊢ t ≤R[ pb ] t'" := (R Ξ pb t t') (only parsing).
Notation "Σ ;;; Ξ ⊢ t ≤R'[ pb ] t' 'on' H" := (R' Ξ pb t t' H) (only parsing).
Notation "Σ ;;; Ξ ⊢ t =R t'" := (R Ξ Conv t t') (only parsing).
Notation "Σ ;;; Ξ ⊢ t =R' t' 'on' H" := (R' Ξ Conv t t' H) (only parsing).

Inductive cumul_addon Ξ pb : forall (t t' : term), Type :=
  | cumul_prod na na' A A' B B' :
      [(Xα : eq_binder_annot na na')] ->
      [(XA : Σ ;;; Ξ ⊢ A =R A')] ->
      [(XB : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ B ≤R[pb] B')] ->
      Σ ;;; Ξ ⊢ tProd na A B ≤c[pb] tProd na' A' B'

  | cumul_sort s s' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs' : wf_sort Σ s')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      Σ ;;; Ξ ⊢ tSort s ≤c[pb] tSort s'
  (* | (indapp) *)
where "Σ ;;; Ξ ⊢ t ≤c[ pb ] t'" := (@cumul_addon Ξ pb t t') (only parsing).
Derive Signature for cumul_addon.

Inductive cumul_addonε Ξ pb : forall (t t' : term), Σ ;;; Ξ ⊢ t ≤c[ pb ] t' -> Type :=
  | cumulε_prod na na' A A' B B' :
      [(Xα : eq_binder_annot na na')] ->
      [(XA : Σ ;;; Ξ ⊢ A =R A')] ->
      [(IXA : Σ ;;; Ξ ⊢ A =R' A' on XA)] ->
      [(XB : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ B ≤R[pb] B')] ->
      [(IXB : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ B ≤R'[pb] B' on XB)] ->
      Σ ;;; Ξ ⊢ tProd na A B ≤c[pb] tProd na' A' B' on ⌈cumul_prod⌋ with R'

  | cumulε_sort s s' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs' : wf_sort Σ s')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      Σ ;;; Ξ ⊢ tSort s ≤c[pb] tSort s' on ⌈cumul_sort⌋ with R'
  (* | (indapp) *)
where "Σ ;;; Ξ ⊢ t ≤c[ pb ] u 'on' p 'with' R'" := (@cumul_addonε Ξ pb t u p) (only parsing).

End CumulAddon.
Notation "Σ ;;; Ξ ⊢ t ≤c[ pb ] t'" := (cumul_addon Σ _ Ξ pb t t').
Notation "Σ ;;; Ξ ⊢ t ≤c[ pb ] t' 'with' R" := (cumul_addon Σ R Ξ pb t t') (only parsing).
Notation "Σ ;;; Ξ ⊢ t ≤c[ pb ] t' 'on' p 'with' R'" := (cumul_addonε Σ _ R' Ξ pb t t' p).


Lemma context_closure_toε Σ R R' Rα Rs Ξ t t' :
  [(p : Σ ;;; Ξ ⊢ t ~ t' with R, Rα, Rs)] ->
  [(X Ξ t t' : [(H : R Ξ t t')] -> R' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t ~ t' on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closureε_fmap Σ R R' R'' Rα Rs Ξ t t' :
  [(p : Σ ;;; Ξ ⊢ t ~ t' with R, Rα, Rs)] ->
  [(H : Σ ;;; Ξ ⊢ t ~ t' on p with R')] ->
  [(X Ξ t t' : [(H : R Ξ t t')] -> R' Ξ t t' H -> R'' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t ~ t' on p with R''.
Proof.
  intros.
  induction H.
  all: try now econstructor.
Defined.

Lemma eq_lambda_nodomain_toε Σ R R' Ξ t t' :
  [(p : Σ ;;; Ξ ⊢ t =λ t' with R)] ->
  [(X Ξ t t' : [(H : R Ξ t t')] -> R' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t =λ t' on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma eq_lambda_nodomainε_fmap Σ R R' R'' Ξ t t' :
  [(p : Σ ;;; Ξ ⊢ t =λ t' with R)] ->
  [(H : Σ ;;; Ξ ⊢ t =λ t' on p with R')] ->
  [(X Ξ t t' : [(H : R Ξ t t')] -> R' Ξ t t' H -> R'' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t =λ t' on p with R''.
Proof.
  intros.
  induction H.
  all: try now econstructor.
Defined.

Lemma ext_eq_toε Σ R R' Ξ t t' :
  [(p : Σ ;;; Ξ ⊢ t =ext t' with R)] ->
  [(X Ξ t t' : [(H : R Ξ t t')] -> R' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t =ext t' on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma ext_eqε_fmap Σ R R' R'' Ξ t t' :
  [(p : Σ ;;; Ξ ⊢ t =ext t' with R)] ->
  [(H : Σ ;;; Ξ ⊢ t =ext t' on p with R')] ->
  [(X Ξ t t' : [(H : R Ξ t t')] -> R' Ξ t t' H -> R'' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t =ext t' on p with R''.
Proof.
  intros.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_toε {cf} Σ R R' Ξ pb t u :
  [(H : Σ ;;; Ξ ⊢ t ≤c[pb] u with R)] ->
  [(X Ξ pb t u : [(H : R Ξ pb t u)] -> R' Ξ pb t u H)] ->
  Σ ;;; Ξ ⊢ t ≤c[pb] u on H with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addonε_fmap {cf} Σ R R' R'' Ξ pb t u :
  [(p : Σ ;;; Ξ ⊢ t ≤c[pb] u with R)] ->
  [(H : Σ ;;; Ξ ⊢ t ≤c[pb] u on p with R')] ->
  [(X Ξ pb t u H : R' Ξ pb t u H -> R'' Ξ pb t u H)] ->
  Σ ;;; Ξ ⊢ t ≤c[pb] u on p with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_fmap {cf} Σ R R' Ξ pb t u :
  [(H : Σ ;;; Ξ ⊢ t ≤c[pb] u with R)] ->
  [(X Ξ pb t u : R Ξ pb t u -> R' Ξ pb t u)] ->
  Σ ;;; Ξ ⊢ t ≤c[pb] u with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_clos {cf} Σ R Ξ t u :
  Σ ;;; Ξ ⊢ t ≤c[Conv] u with R ->
  Σ ;;; Ξ ⊢ t ~ u with (fun Ξ => R Ξ Conv), eq_binder_annot, eq_sort Σ.
Proof.
  induction 1.
  all: now econstructor.
Defined.

Lemma cumul_addon_clos_fmap {cf} Σ R R' Ξ t u :
  [(H : Σ ;;; Ξ ⊢ t ≤c[Conv] u with R)] ->
  [(X Ξ t u : R Ξ Conv t u -> R' Ξ t u)] ->
  Σ ;;; Ξ ⊢ t ~ u with R', eq_binder_annot, eq_sort Σ.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_clos_on {cf} Σ R R' Ξ t u :
  [(p : Σ ;;; Ξ ⊢ t ≤c[Conv] u with R)] ->
  [(H : Σ ;;; Ξ ⊢ t ≤c[Conv] u on p with R')] ->
  Σ ;;; Ξ ⊢ t ~ u on (ltac:(apply cumul_addon_clos with (1 := p))) with (fun Ξ => R' Ξ Conv).
Proof.
  intros p H.
  induction H.
  all: now econstructor.
Qed.


Lemma cumul_addon_clos_onε {cf} Σ R R' R'' Ξ t u :
  [(p : Σ ;;; Ξ ⊢ t ≤c[Conv] u with R)] ->
  [(H : Σ ;;; Ξ ⊢ t ≤c[Conv] u on p with R')] ->
  [(X Ξ t u H : R' Ξ Conv t u H -> R'' Ξ t u H)] ->
  Σ ;;; Ξ ⊢ t ~ u on (ltac:(apply cumul_addon_clos with (1 := p))) with R''.
Proof.
  intros p H X.
  induction H.
  all: try now econstructor.
Defined.


Hint Resolve context_closure_toε context_closureε_fmap eq_lambda_nodomain_toε eq_lambda_nodomainε_fmap ext_eq_toε ext_eqε_fmap cumul_addon_toε cumul_addonε_fmap : fmap.




Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t'" (at level 50, Γ, t, pb, t' at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]η  t'").
Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' 'on' H 'with' R'" (at level 50, Γ, t, pb, t', H at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]η  t'  'on'  H  'with'  R'").
Reserved Notation "Σ  ;;; Γ ⊢ t =η t'" (at level 50, Γ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =η t' 'on' H 'with' R'" (at level 50, Γ, t, t', H at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =η t' · Δ" (at level 50, Γ, Δ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =η t' · Δ 'on' H 'with' R'" (at level 50, Γ, Δ, t, t', H at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t · Δ =η t'" (at level 50, Γ, Δ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t · Δ =η t' 'on' H 'with' R'" (at level 50, Γ, Δ, t, t', H at next level).


Section Eta.

Variable R : relevance_context -> term -> term -> Type.
Variable R' : forall Ξ t u, R Ξ t u -> Type.
Notation "Σ ;;; Ξ ⊢ t =η t'" := (R Ξ t t') (only parsing).
Notation "Σ ;;; Ξ ⊢ t =η' t' 'on' H" := (R' Ξ t t' H) (only parsing, at level 50, Ξ, t, t' at next level).
Local Set Elimination Schemes.

Inductive eta_left_spine Σ Ξ t' : forall Δ t, Type :=
  | etal_ground t :
      [(X : Σ ;;; Ξ ⊢ t =η t')] ->
      Σ ;;; Ξ ⊢ t =η t' · []

  | etal_push Δ na A t :
      [(X : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t =η lift0 1 t' · map S Δ ,, 0)] ->
      Σ ;;; Ξ ⊢ tLambda na A t =η t' · Δ

  | etal_pop Δ n t z :
      [(X : Σ ;;; Ξ ⊢ t =η t' · Δ)] ->
      [(Xz : Σ ;;; Ξ ⊢ z =η tRel n)] ->
      Σ ;;; Ξ ⊢ tApp t z =η t' · Δ ,, n
where "Σ ;;; Ξ ⊢ t =η t' · Δ" := (eta_left_spine Σ Ξ t' Δ t) (only parsing).
Derive Signature for eta_left_spine.

Inductive eta_left_spineε Σ Ξ t' : forall Δ t, Σ ;;; Ξ ⊢ t =η t' · Δ -> Type :=
  | etalε_ground t :
      [(XR : Σ ;;; Ξ ⊢ t =η t')] ->
      [(IXR : Σ ;;; Ξ ⊢ t =η' t' on XR)] ->
      Σ ;;; Ξ ⊢ t =η t' · [] on ⌈etal_ground⌋ with R'

  | etalε_push Δ na A t :
      [(X : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t =η lift0 1 t' · map S Δ ,, 0)] ->
      [(IX : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t =η lift0 1 t' · map S Δ ,, 0 on X with R')] ->
      Σ ;;; Ξ ⊢ tLambda na A t =η t' · Δ on ⌈etal_push⌋ with R'

  | etalε_pop Δ n t z :
      [(X : Σ ;;; Ξ ⊢ t =η t' · Δ)] ->
      [(IX : Σ ;;; Ξ ⊢ t =η t' · Δ on X with R')] ->
      [(Xz : Σ ;;; Ξ ⊢ z =η tRel n)] ->
      [(IXz : Σ ;;; Ξ ⊢ z =η' tRel n on Xz)] ->
      Σ ;;; Ξ ⊢ tApp t z =η t' · Δ ,, n on ⌈etal_pop⌋ with R'
where "Σ ;;; Ξ ⊢ t =η t' · Δ 'on' H 'with' R'" := (eta_left_spineε Σ Ξ t' Δ t H) (only parsing).
Derive Signature for eta_left_spineε.

Inductive eta_right_spine Σ Ξ t : forall Δ t', Type :=
  | etar_ground t' :
      [(X : Σ ;;; Ξ ⊢ t =η t')] ->
      Σ ;;; Ξ ⊢ t · [] =η t'

  | etar_push Δ na A t' :
      [(X : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ lift0 1 t · map S Δ ,, 0 =η t')] ->
      Σ ;;; Ξ ⊢ t · Δ =η tLambda na A t'

  | etar_pop Δ n t' z :
      [(X : Σ ;;; Ξ ⊢ t · Δ =η t')] ->
      [(Xz : Σ ;;; Ξ ⊢ tRel n =η z)] ->
      Σ ;;; Ξ ⊢ t · Δ ,, n =η tApp t' z
where "Σ ;;; Ξ ⊢ t · Δ =η t'" := (eta_right_spine Σ Ξ t Δ t').
Derive Signature for eta_right_spine.

Inductive eta_right_spineε Σ Ξ t : forall Δ t', Σ ;;; Ξ ⊢ t · Δ =η t' -> Type :=
  | etarε_ground t' :
      [(XR : Σ ;;; Ξ ⊢ t =η t')] ->
      [(IXR : Σ ;;; Ξ ⊢ t =η' t' on XR)] ->
      Σ ;;; Ξ ⊢ t · [] =η t' on ⌈etar_ground⌋ with R'

  | etarε_push Δ na A t' :
      [(X : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ lift0 1 t · map S Δ ,, 0 =η t')] ->
      [(IX : Σ ;;; Ξ ,, na.(binder_relevance) ⊢ lift0 1 t · map S Δ ,, 0 =η t' on X with R')] ->
      Σ ;;; Ξ ⊢ t · Δ =η tLambda na A t' on ⌈etar_push⌋ with R'

  | etarε_pop Δ n t' z :
      [(X : Σ ;;; Ξ ⊢ t · Δ =η t')] ->
      [(IX : Σ ;;; Ξ ⊢ t · Δ =η t' on X with R')] ->
      [(Xz : Σ ;;; Ξ ⊢ tRel n =η z)] ->
      [(IXz : Σ ;;; Ξ ⊢ tRel n =η' z on Xz)] ->
      Σ ;;; Ξ ⊢ t · Δ ,, n =η tApp t' z on ⌈etar_pop⌋ with R'
where "Σ ;;; Ξ ⊢ t · Δ =η t' 'on' H 'with' R'" := (eta_right_spineε Σ Ξ t Δ t' H) (only parsing).
Derive Signature for eta_right_spineε.

Unset Elimination Schemes.
End Eta.

Inductive eta_spine {cf} Σ Ξ t t' : Type :=
  | eta_left :
      [(X : Σ ;;; Ξ ⊢ t =η t' · [])] ->
      Σ ;;; Ξ ⊢ t =η t'

  | eta_right :
      [(X : Σ ;;; Ξ ⊢ t · [] =η t')] ->
      Σ ;;; Ξ ⊢ t =η t'

  | eta_sprop :
      isTermRel Σ Ξ t Irrelevant ->
      isTermRel Σ Ξ t' Irrelevant ->
      Σ ;;; Ξ ⊢ t =η t'

  | eta_lambda_nodomain :
      [(X : Σ ;;; Ξ ⊢ t =λ t' with eta_spine Σ)] ->
      Σ ;;; Ξ ⊢ t =η t'

  | eta_clos :
      [(X : Σ ;;; Ξ ⊢ t ~ t' with eta_spine Σ, eq_binder_annot, eq_sort Σ)] ->
      Σ ;;; Ξ ⊢ t =η t'

where "Σ ;;; Ξ ⊢ t =η t'" := (eta_spine Σ Ξ t t')
and "Σ ;;; Ξ ⊢ t =η t' · Δ" := (eta_left_spine (eta_spine Σ) Σ Ξ t' Δ t)
and "Σ ;;; Ξ ⊢ t · Δ =η t'" := (eta_right_spine (eta_spine Σ) Σ Ξ t Δ t').
Derive Signature for eta_spine.

Inductive eta_spine_pb {cf} Σ Ξ pb t t' : Type :=
  | eta_spine_eta_pb :
    Σ ;;; Ξ ⊢ t =η t' ->
    Σ ;;; Ξ ⊢ t <=[pb]η t'

  | eta_pb_cumul_addon :
    Σ ;;; Ξ ⊢ t ≤c[pb] t' with eta_spine_pb Σ ->
    Σ ;;; Ξ ⊢ t <=[pb]η t'
where "Σ ;;; Ξ ⊢ t <=[ pb ]η t'" := (eta_spine_pb Σ Ξ pb t t').
Derive Signature for eta_spine_pb.

Notation "Σ ;;; Ξ ⊢ t =η t' · Δ 'on' H 'with' R'" := (eta_left_spineε (eta_spine Σ) R' Σ Ξ t' Δ t H).
Notation "Σ ;;; Ξ ⊢ t · Δ =η t' 'on' H 'with' R'" := (eta_right_spineε (eta_spine Σ) R' Σ Ξ t Δ t' H).


Lemma eta_left_spine_toε {cf} Σ R' Ξ Δ t t' :
  [(p : Σ ;;; Ξ ⊢ t =η t' · Δ)] ->
  [(X Ξ t t' : [(H : eta_spine Σ Ξ t t')] -> R' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t =η t' · Δ on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Lemma eta_left_spineε_fmap {cf} Σ R R' Ξ Δ t t' :
  [(p : Σ ;;; Ξ ⊢ t =η t' · Δ)] ->
  [(H : Σ ;;; Ξ ⊢ t =η t' · Δ on p with R)] ->
  [(X Ξ t t' (H : eta_spine Σ Ξ t t') : R Ξ t t' H -> R' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t =η t' · Δ on p with R'.
Proof.
  intros.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Lemma eta_right_spine_toε {cf} Σ R' Ξ Δ t t' :
  [(p : Σ ;;; Ξ ⊢ t · Δ =η t')] ->
  [(X Ξ t t' : [(H : eta_spine Σ Ξ t t')] -> R' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t · Δ =η t' on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Lemma eta_right_spineε_fmap {cf} Σ R R' Ξ Δ t t' :
  [(p : Σ ;;; Ξ ⊢ t · Δ =η t')] ->
  [(H : Σ ;;; Ξ ⊢ t · Δ =η t' on p with R)] ->
  [(X Ξ t t' : [(H : eta_spine Σ Ξ t t')] -> R Ξ t t' H -> R' Ξ t t' H)] ->
  Σ ;;; Ξ ⊢ t · Δ =η t' on p with R'.
Proof.
  intros.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Hint Resolve eta_left_spine_toε eta_left_spineε_fmap eta_right_spine_toε eta_right_spineε_fmap : fmap.

Inductive eta_spineε {cf} Σ R' Ξ t t' : Σ ;;; Ξ ⊢ t =η t' -> Type :=
  | etaε_left :
      [(X : Σ ;;; Ξ ⊢ t =η t' · [])] ->
      [(IX : Σ ;;; Ξ ⊢ t =η t' · [] on X with (fun Ξ t u H => R' Ξ t u × eta_spineε Σ R' Ξ t u H))] ->
      Σ ;;; Ξ ⊢ t =η t' on ⌈eta_left⌋ with R'

  | etaε_right :
      [(X : Σ ;;; Ξ ⊢ t · [] =η t')] ->
      [(IX : Σ ;;; Ξ ⊢ t · [] =η t' on X with (fun Ξ t u H => R' Ξ t u × eta_spineε Σ R' Ξ t u H))] ->
      Σ ;;; Ξ ⊢ t =η t' on ⌈eta_right⌋ with R'

  | etaε_sprop :
      [(Xt : isTermRel Σ Ξ t Irrelevant)] ->
      [(Xt' : isTermRel Σ Ξ t' Irrelevant)] ->
      Σ ;;; Ξ ⊢ t =η t' on ⌈eta_sprop⌋ with R'

  | etaε_lambda_nodomain :
      [(X : Σ ;;; Ξ ⊢ t =λ t' with eta_spine Σ)] ->
      [(IX : Σ ;;; Ξ ⊢ t =λ t' on X with (fun Ξ t u H => R' Ξ t u × eta_spineε Σ R' Ξ t u H))] ->
      Σ ;;; Ξ ⊢ t =η t' on ⌈eta_lambda_nodomain⌋ with R'

  | etaε_clos :
      [(X : Σ ;;; Ξ ⊢ t ~ t' with eta_spine Σ, eq_binder_annot, eq_sort Σ)] ->
      [(IX : Σ ;;; Ξ ⊢ t ~ t' on X with (fun Ξ t u H => R' Ξ t u × eta_spineε Σ R' Ξ t u H))] ->
      Σ ;;; Ξ ⊢ t =η t' on ⌈eta_clos⌋ with R'

where "Σ ;;; Ξ ⊢ t =η t' 'on' H 'with' R'" := (eta_spineε Σ R' Ξ t t' H).
Derive Signature for eta_spineε.

Definition eta_spine_rect cf Σ P :
  [(Xrec Ξ t u : [(H : Σ ;;; Ξ ⊢ t =η u)] -> eta_spineε Σ P Ξ t u H -> P Ξ t u)] ->
  forall Ξ t u, [(H : Σ ;;; Ξ ⊢ t =η u)] -> P Ξ t u.
Proof.
  intros.
  unshelve eapply Xrec; tea.
  revert Ξ t u H. fix rec 4.
  destruct H.
  all: unshelve econstructor; unshelve eauto with fmap; eauto.
Qed.

Definition eta_spine_pb_rect cf Σ P :
  [(Xbase Ξ pb t t' :
    [(X : Σ ;;; Ξ ⊢ t =η t')] ->
    P Ξ pb t t')] ->

  [(XCumulAddon Ξ pb t t' :
    [(X : Σ ;;; Ξ ⊢ t ≤c[pb] t' with eta_spine_pb Σ)] ->
    [(IX : Σ ;;; Ξ ⊢ t ≤c[pb] t' on X with (fun Ξ pb t u _ => P Ξ pb t u))] ->
    P Ξ pb t t')] ->
  forall Ξ pb t u, [(H : Σ ;;; Ξ ⊢ t <=[pb]η u)] -> P Ξ pb t u.
Proof.
  intros.
  revert Ξ pb t u H. fix rec 5.
  destruct 1.
  - unshelve eapply Xbase; tea.
  - unshelve eapply XCumulAddon; tea.
    unshelve eauto with fmap; eauto.
Qed.

Lemma isTermRel_lambda Σ Ξ na A t r :
  isTermRel Σ Ξ (tLambda na A t) r <~> isTermRel Σ (Ξ ,, na.(binder_relevance)) t r.
Proof. split. 2: by constructor. intro H; by depelim H. Qed.

Lemma isTermRel_app Σ Ξ t u r :
  isTermRel Σ Ξ (tApp t u) r <~> isTermRel Σ Ξ t r.
Proof. split. 2: by constructor. intro H; by depelim H. Qed.


Lemma isTermRel_lift' Σ Ξ r₀ t r :
  isTermRel Σ (Ξ ,, r₀) (lift0 1 t) r <~> isTermRel Σ Ξ t r.
Proof.
  split.
  - intro H.
    by eapply isTermRel_unlift with (Ξ' := [_]) (Ξ'' := []) in H.
  - by eapply isTermRel_lift with (Ξ' := [_]) (Ξ'' := []).
Qed.




Lemma eta_spine_relevance {cf} Σ Ξ t u r :
  Σ ;;; Ξ ⊢ t =η u ->
  isTermRel Σ Ξ t r <~> isTermRel Σ Ξ u r.
Proof.
  intro H.
  induction H in r. destruct X.
  - change Ξ with (Ξ ,,, []) at 1.
    move: [] X IX => Ξ' X IX.
    induction IX.
    + eapply IXR.
    + setoid_rewrite isTermRel_lambda.
      setoid_rewrite isTermRel_lift' in IHIX.
      assumption.
    + setoid_rewrite isTermRel_app.
      assumption.
  - change Ξ with (Ξ ,,, []) at 2.
    move: [] X IX => Ξ' X IX.
    induction IX.
    + eapply IXR.
    + setoid_rewrite isTermRel_lambda.
      setoid_rewrite isTermRel_lift' in IHIX.
      assumption.
    + setoid_rewrite isTermRel_app.
      assumption.
  - split; intro H.
    all: now eapply isTermRel_uniq in H as <-.
  - induction IX.
    setoid_rewrite isTermRel_lambda.
    rewrite -Xα.
    eapply IXt.
  - induction IX.
    all: try solve [ split; eauto ].
    + setoid_rewrite isTermRel_lambda.
      rewrite -Xα.
      eapply IXt.
    + setoid_rewrite isTermRel_app.
      apply IXt.
    + split; intro H; depelim H; constructor.
    + split; intro H; depelim H; constructor.
Qed.

Lemma eta_left_spine_relevance {cf} Σ Ξ Δ t u r :
  Σ ;;; Ξ ⊢ t · Δ =η u ->
  isTermRel Σ Ξ t r <~> isTermRel Σ Ξ u r.
Proof.
  intros.
  induction X.
  + by eapply eta_spine_relevance.
  + setoid_rewrite isTermRel_lambda.
    setoid_rewrite isTermRel_lift' in IHX.
    assumption.
  + setoid_rewrite isTermRel_app.
    assumption.
Qed.

Lemma eta_right_spine_relevance {cf} Σ Ξ Δ t u r :
  Σ ;;; Ξ ⊢ t =η u · Δ ->
  isTermRel Σ Ξ t r <~> isTermRel Σ Ξ u r.
Proof.
  intros.
  induction X.
  + by eapply eta_spine_relevance.
  + setoid_rewrite isTermRel_lambda.
    setoid_rewrite isTermRel_lift' in IHX.
    assumption.
  + setoid_rewrite isTermRel_app.
    assumption.
Qed.



(*
Lemma eta_left_invert cf TC Σ
  (rec : forall Ξ t t' T, Σ ;;; Ξ ⊢ t <=[Conv] t' : T -> Σ ;;; Ξ ⊢ t =η t')
  Ξ Δ t u T args :
  #|args| > 0 ->
  Σ ;;; Ξ ,,, Δ ⊢ t <=[Conv] mkApps (lift0 #|Δ| u) (rev_map tRel args) : T ->
  Σ ;;; Ξ ⊢ t =η u · Δ · args.
Proof.
  assert (H10 : forall n, S n > 0) by auto with arith.
  assert (H00 : forall A, 0 > 0 -> A) by lia.

  intros Hlen Xe.
  remember (mkApps _ _) as u₀ eqn:eu.
  remember (Γ ,,, Γ') as ΓΓ' eqn:eΓ.
  induction Xe in Γ', u, args, eu, eΓ, Hlen.
  1: destruct IX; subst.
  + eapply etal_push; trea.
    eapply IXR; trea.
    1: by apply H10.
    rewrite rev_map_cons mkApps_app /=. f_equal.
    rewrite lift_mkApps. f_equal.
    * rewrite simpl_lift //; lia.
    * by rewrite !rev_map_spec map_rev !map_map //=.
  + destruct args => /=. 1: by apply H00.
    rewrite /= rev_map_cons mkApps_app // in eu.
  + todo "untyped sprop".
  + destruct args => /=. 1: by apply H00.
    rewrite /= rev_map_cons mkApps_app /= in eu.
    by destruct X => //.
  + subst Γ0 u0. eauto.
  + destruct args => /=. 1: by apply H00.
    rewrite /= rev_map_cons mkApps_app /= in eu.
    destruct X => //.
    apply rec in Xt as Xt', Xu as Xu'. clear rec.
    injection eu as [= -> ->]. subst Γ0.
    eapply etal_pop; trea.
    destruct args.
    * eapply etal_ground, Xt'.
    * inversion IX; subst.
      eapply IXt; trea.
      apply H10.
Defined.


Lemma eta_right_invert cf TC Σ
  (rec : forall Γ t t' T, Σ ;;; Γ ⊢ t <=[Conv] t' : T -> Σ ;;; Γ ⊢ t =η t')
  Γ Γ' t u T args :
  #|args| > 0 ->
  Σ ;;; Γ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t) (rev_map tRel args) <=[Conv] u : T ->
  Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η u.
Proof.
  assert (H10 : forall n, S n > 0) by auto with arith.
  assert (H00 : forall A, 0 > 0 -> A) by lia.

  remember (mkApps _ _) as t₀ eqn:et.
  remember (Γ ,,, Γ') as ΓΓ' eqn:eΓ.
  intros Hlen Xe.
  induction Xe in Γ', t, args, et, eΓ, Hlen; rename Γ0 into ΓΓ', t0 into t₀.
  1: destruct IX; subst.
  - destruct args => /=. 1: by apply H00.
    by rewrite /= rev_map_cons mkApps_app // in et.
  - eapply etar_push; trea.
    eapply IXR; revgoals; trea.
    + by apply H10.
    + rewrite rev_map_cons mkApps_app /=. f_equal.
      rewrite lift_mkApps. f_equal.
      * rewrite simpl_lift //; lia.
      * by rewrite !rev_map_spec map_rev !map_map //=.
  - todo "untyped sprop".
  - destruct args => /=. 1: by apply H00.
    rewrite /= rev_map_cons mkApps_app /= in et.
    by destruct X.
  - subst ΓΓ' t₀. eauto.
  - destruct args => /=. 1: by apply H00.
    rewrite /= rev_map_cons mkApps_app /= in et.
    destruct X => //.
    apply rec in Xt as Xt', Xu as Xu'. clear rec.
    injection et as [= -> ->]. subst ΓΓ'.
    eapply etar_pop; trea.
    destruct args.
    * eapply etar_ground, Xt'.
    * inversion IX; subst.
      eapply IXt; trea.
      apply H10.
Defined.

Lemma eta_invert cf TC Σ Γ t t' T :
  Σ ;;; Γ ⊢ t <=[Conv] t' : T ->
  Σ ;;; Γ ⊢ t =η t'.
Proof.
  revert Γ t t' T.
  fix rec 5.
  destruct 1.
  1: destruct X.
  - apply eta_left.
    eapply etal_push; trea.
    eapply eta_left_invert; tea.
    1: cbn; auto with arith.

  - apply eta_right.
    eapply etar_push; trea.
    eapply eta_right_invert; tea.
    1: cbn; auto with arith.

  - todo "untyped sprop".
  - eapply eta_clos; trea.
    todo "forget type".
  - eauto.
  - eapply eta_clos; trea.
    todo "forget type".
Qed.

Lemma eta_pb_invert cf TC Σ Γ pb t t' T :
  Σ ;;; Γ ⊢ t <=[pb] t' : T ->
  Σ ;;; Γ ⊢ t <=[pb]η t'.
Proof.
  induction 1.
  - constructor. eapply eta_invert. now constructor.
  - econstructor 2; trea.
    todo "forget type".
  - eauto.
  - constructor. eapply eta_invert. now constructor.
Qed. *)


Section eta_spine_size.
Context {cf Σ}.
Section inner.
Variable (rec : forall Ξ t u, Σ ;;; Ξ ⊢ t =η u -> nat).

Fixpoint eta_left_spine_size {Ξ Δ t u} (H : Σ ;;; Ξ ⊢ t =η u · Δ) : nat.
Proof.
  destruct H.
  all: apply S.
  + eauto.
  + eauto.
  + exact (2 + eta_left_spine_size _ _ _ _ H + rec _ _ _ Xz).
Defined.

Fixpoint eta_right_spine_size {Ξ Δ t u} (H : Σ ;;; Ξ ⊢ t · Δ =η u) : nat.
Proof.
  destruct H.
  all: apply S.
  + eauto.
  + eauto.
  + exact (2 + eta_right_spine_size _ _ _ _ H + rec _ _ _ Xz).
Defined.

Definition context_closure_size {Rα Rs R} {Ξ t u}
  (recR : forall Ξ t u, R Ξ t u -> nat)
  (H : Σ ;;; Ξ ⊢ t ~ u with R, Rα, Rs) : nat.
Proof.
  destruct H.
  all: apply S.
  + exact 0.
  + exact (recR _ _ _ XA + recR _ _ _ Xt).
  + exact (recR _ _ _ Xt + recR _ _ _ Xu).
  + exact (recR _ _ _ XA + recR _ _ _ XB).
  + exact 0.
Defined.

Definition eq_lambda_nodomain_size {R} {Ξ t u}
  (recR : forall Ξ t u, R Ξ t u -> nat)
  (H : Σ ;;; Ξ ⊢ t =λ u with R) : nat.
Proof.
  destruct H.
  apply S.
  exact (recR _ _ _ Xt).
Defined.

End inner.

Fixpoint eta_spine_size {Ξ t u} (H : Σ ;;; Ξ ⊢ t =η u) {struct H} : nat.
Proof.
  destruct H.
  all: apply S.
  - by apply eta_left_spine_size in X.
  - by apply eta_right_spine_size in X.
  - exact 0.
  - by apply eq_lambda_nodomain_size in X.
  - by apply context_closure_size in X.
Defined.

End eta_spine_size.

Definition liftrel n k i := (if k <=? i then (n + i) else i).

Lemma permute_liftrel0 n k args :
  map S (map (liftrel n k) args) = map (liftrel n (S k)) (map S args).
Proof.
  solve_all.
  apply All_refl => x /=.
  rewrite /liftrel /=.
  destruct Nat.leb; lia.
Qed.

Lemma eta_left_spine_lift_size cf Σ (Γ Δ Γ' : relevance_context) t u args :
  [(rec (Γ' : relevance_context) t u (H : Σ ;;; Γ,,, Γ' ⊢ t =η u) :
      ∑ H' : Σ ;;; Γ,,, Δ,,, Γ' ⊢ lift #|Δ| #|Γ'| t =η lift #|Δ| #|Γ'| u,
      eta_spine_size H' = eta_spine_size H)] ->
  [(X : Σ ;;; Γ,,, Γ' ⊢ t =η u · args)] ->
  ∑ H' : Σ ;;; Γ,,, Δ,,, Γ' ⊢ lift #|Δ| #|Γ'| t =η lift #|Δ| #|Γ'| u · map (liftrel #|Δ| #|Γ'|) args,
    eta_left_spine_size (@eta_spine_size cf Σ) H' = eta_left_spine_size (@eta_spine_size cf Σ) X.
Proof.
  intro.
  revert Γ' t u args.
  fix rec' 5. intros Γ' Δ' t u [].
  + epose proof (rec _ _ _ X) as IX.
    unshelve eexists.
    1: constructor; apply IX.π1.
    cbn. repeat f_equal. apply IX.π2.
  + epose proof (rec' (_ ,, _) _ _ _ X) as IX.
    rewrite /= -permute_lift0 -permute_liftrel0 in IX.
    unshelve eexists.
    1: constructor; apply IX.π1.
    cbn. repeat f_equal. apply IX.π2.
  + epose proof (rec' _ _ _ _ X) as IX.
    epose proof (rec _ _ _ Xz) as IXz.
    unshelve eexists.
    1: constructor; tas; [apply IX.π1|apply IXz.π1].
    cbn. repeat f_equal; [apply IX.π2|apply IXz.π2].
Defined.

Lemma eta_right_spine_lift_size cf Σ (Γ Δ Γ' : relevance_context) t u args :
  [(rec (Γ' : relevance_context) t u (H : Σ ;;; Γ,,, Γ' ⊢ t =η u) :
      ∑ H' : Σ ;;; Γ,,, Δ,,, Γ' ⊢ lift #|Δ| #|Γ'| t =η lift #|Δ| #|Γ'| u,
      eta_spine_size H' = eta_spine_size H)] ->
  [(X : Σ ;;; Γ,,, Γ' ⊢ t · args =η u)] ->
  ∑ H' : Σ ;;; Γ,,, Δ,,, Γ' ⊢ lift #|Δ| #|Γ'| t · map (liftrel #|Δ| #|Γ'|) args =η lift #|Δ| #|Γ'| u,
    eta_right_spine_size (@eta_spine_size cf Σ) H' = eta_right_spine_size (@eta_spine_size cf Σ) X.
Proof.
  intro.
  revert Γ' t u args.
  fix rec' 5. intros Γ' Δ' t u [].
  + epose proof (rec _ _ _ X) as IX.
    unshelve eexists.
    1: constructor; apply IX.π1.
    cbn. repeat f_equal. apply IX.π2.
  + epose proof (rec' (_ ,, _) _ _ _ X) as IX.
    rewrite /= -permute_lift0 -permute_liftrel0 in IX.
    unshelve eexists.
    1: constructor; apply IX.π1.
    cbn. repeat f_equal. apply IX.π2.
  + epose proof (rec' _ _ _ _ X) as IX.
    epose proof (rec _ _ _ Xz) as IXz.
    unshelve eexists.
    1: constructor; tas; [apply IX.π1|apply IXz.π1].
    cbn. repeat f_equal; [apply IX.π2|apply IXz.π2].
Defined.


Lemma eta_spine_lift_size cf Σ (Γ Δ Γ' : relevance_context) t u :
  [(H : Σ ;;; Γ ,,, Γ' ⊢ t =η u)] ->
  ∑ H' : Σ ;;; Γ ,,, Δ ,,, Γ' ⊢ lift #|Δ| #|Γ'| t =η lift #|Δ| #|Γ'| u, eta_spine_size H' = eta_spine_size H.
Proof.
  revert Γ' t u.
  fix rec 4.
  destruct H; cbn.
  - epose proof (ltac:(eapply eta_left_spine_lift_size with (X := X))) as [X' e].
    1: unshelve eexists; [now constructor|]; cbn; by f_equal.
    Unshelve. assumption.
  - epose proof (ltac:(eapply eta_right_spine_lift_size with (X := X))) as [X' e].
    1: unshelve eexists; [now constructor|]; cbn; by f_equal.
    Unshelve. assumption.
  - unshelve eexists.
    1: constructor; by apply isTermRel_lift.
    cbnr.
  - destruct X; cbn.
    epose proof (rec (_ ,, _) _ _ Xt) as IXR.
    unshelve eexists.
    1: do 2 econstructor; tas; apply IXR.π1.
    cbn. repeat f_equal. apply IXR.π2.
  - destruct X; cbn.
    + unshelve eexists.
      1: by do 2 econstructor.
      cbnr.
    + epose proof (rec _ _ _ XA) as IXA.
      epose proof (rec (_ ,, _) _ _ Xt) as IXt.
      unshelve eexists.
      1: do 2 econstructor; tas; [apply IXA.π1|apply IXt.π1].
      cbn. repeat f_equal; [apply IXA.π2|apply IXt.π2].
    + epose proof (rec _ _ _ Xt) as IXt.
      epose proof (rec _ _ _ Xu) as IXu.
      unshelve eexists.
      1: do 2 econstructor; tas; [apply IXt.π1|apply IXu.π1].
      cbn. repeat f_equal; [apply IXt.π2|apply IXu.π2].
    + epose proof (rec _ _ _ XA) as IXA.
      epose proof (rec (_ ,, _) _ _ XB) as IXB.
      unshelve eexists.
      1: do 2 econstructor; tas; [apply IXA.π1|apply IXB.π1].
      cbn. repeat f_equal; [apply IXA.π2|apply IXB.π2].
    + unshelve eexists.
      1: by do 2 econstructor.
      cbnr.
Qed.

Lemma eta_spine_lift0_size {cf Σ Ξ t u} r :
  [(H : Σ ;;; Ξ ⊢ t =η u)] ->
  ∑ H' : Σ ;;; Ξ ,, r ⊢ lift0 1 t =η lift0 1 u, eta_spine_size H' = eta_spine_size H.
Proof.
  apply eta_spine_lift_size with (Δ := [_]) (Γ' := []).
Qed.

Lemma eta_left_spine_lift0_size {cf Σ Ξ Δ t u} r :
  [(H : Σ ;;; Ξ ⊢ t =η u · Δ)] ->
  ∑ H' : Σ ;;; Ξ ,, r ⊢ lift0 1 t =η lift0 1 u · map S Δ, eta_left_spine_size (@eta_spine_size cf Σ) H' = eta_left_spine_size (@eta_spine_size cf Σ) H.
Proof.
  intro X.
  apply eta_left_spine_lift_size with (Δ := [_]) (Γ' := []); tas.
  apply eta_spine_lift_size.
Qed.

Lemma eta_right_spine_lift0_size {cf Σ Ξ Δ t u} r :
  [(H : Σ ;;; Ξ ⊢ t · Δ =η u)] ->
  ∑ H' : Σ ;;; Ξ ,, r ⊢ lift0 1 t · map S Δ =η lift0 1 u, eta_right_spine_size (@eta_spine_size cf Σ) H' = eta_right_spine_size (@eta_spine_size cf Σ) H.
Proof.
  apply eta_right_spine_lift_size with (Δ := [_]) (Γ' := []).
  apply eta_spine_lift_size.
Qed.


Lemma eta_left_spine_unlift {cf} Σ P Ξ Ξ' Ξ'' t u args :
  [(onP Ξ'' t u H : P (Ξ ,,, Ξ' ,,, Ξ'') (lift #|Ξ'| #|Ξ''| t) (lift #|Ξ'| #|Ξ''| u) H -> Σ ;;; Ξ ,,, Ξ'' ⊢ t =η u)] ->
  [(X : Σ ;;; Ξ ,,, Ξ' ,,, Ξ'' ⊢ lift #|Ξ'| #|Ξ''| t =η lift #|Ξ'| #|Ξ''| u · map (liftrel #|Ξ'| #|Ξ''|) args)] ->
  [(IX : Σ ;;; Ξ ,,, Ξ' ,,, Ξ'' ⊢ lift #|Ξ'| #|Ξ''| t =η lift #|Ξ'| #|Ξ''| u · map (liftrel #|Ξ'| #|Ξ''|) args on X with P)] ->
  Σ ;;; Ξ ,,, Ξ'' ⊢ t =η u · args.
Proof.
  intros ???.
  remember (Ξ ,,, Ξ' ,,, Ξ'') as Ξ₀ eqn:e1.
  remember (lift #|Ξ'| #|Ξ''| t) as t₀ eqn:e2; remember (lift #|Ξ'| #|Ξ''| u) as u₀ eqn:e3.
  remember (map (liftrel _ _) args) as args₀ eqn:e4.
  induction IX in Ξ'', t, u, args, e1, e2, e3, e4; subst.
  + move: args e4 => [] //= _.
    constructor. eapply onP; trea.
  + move: t e2 => [] //= na' A₀ t₀ [= <- ? ?] {na'}; subst.
    constructor.
    eapply IHIX with (Ξ'' := Ξ'' ,, _); trea.
    * apply permute_lift0.
    * cbn. unfold snoc. f_equal.
      apply permute_liftrel0.
  + move: t e2 => [] //= t₀ arg₀ [= ? ?]; subst.
    move: args e4 => [] //= n₀ args [= ? ?]; subst.
    constructor.
    * eapply IHIX; trea.
    * eapply onP; trea.
Qed.

Lemma eta_right_spine_unlift {cf} Σ P Ξ Ξ' Ξ'' t u args :
  [(onP Ξ'' t u H : P (Ξ ,,, Ξ' ,,, Ξ'') (lift #|Ξ'| #|Ξ''| t) (lift #|Ξ'| #|Ξ''| u) H -> Σ ;;; Ξ ,,, Ξ'' ⊢ t =η u)] ->
  [(X : Σ ;;; Ξ ,,, Ξ' ,,, Ξ'' ⊢ lift #|Ξ'| #|Ξ''| t · map (liftrel #|Ξ'| #|Ξ''|) args =η lift #|Ξ'| #|Ξ''| u)] ->
  [(IX : Σ ;;; Ξ ,,, Ξ' ,,, Ξ'' ⊢ lift #|Ξ'| #|Ξ''| t · map (liftrel #|Ξ'| #|Ξ''|) args =η lift #|Ξ'| #|Ξ''| u on X with P)] ->
  Σ ;;; Ξ ,,, Ξ'' ⊢ t · args =η u.
Proof.
  intros ???.
  remember (Ξ ,,, Ξ' ,,, Ξ'') as Ξ₀ eqn:e1.
  remember (lift #|Ξ'| #|Ξ''| t) as t₀ eqn:e2; remember (lift #|Ξ'| #|Ξ''| u) as u₀ eqn:e3.
  remember (map (liftrel _ _) args) as args₀ eqn:e4.
  induction IX in Ξ'', t, u, args, e1, e2, e3, e4; subst.
  + move: args e4 => [] //= _.
    constructor. eapply onP; trea.
  + move: u e3 => [] //= na' A₀ u₀ [= <- ? ?] {na'}; subst.
    constructor.
    eapply IHIX with (Ξ'' := Ξ'' ,, _); trea.
    * apply permute_lift0.
    * cbn. unfold snoc. f_equal.
      apply permute_liftrel0.
  + move: u e3 => [] //= u₀ arg₀ [= ? ?]; subst.
    move: args e4 => [] //= n₀ args [= ? ?]; subst.
    constructor.
    * eapply IHIX; trea.
    * eapply onP; trea.
Qed.

Lemma eta_spine_unlift {cf} Σ Ξ Ξ' Ξ'' t u :
  Σ ;;; Ξ ,,, Ξ' ,,, Ξ'' ⊢ lift #|Ξ'| #|Ξ''| t =η lift #|Ξ'| #|Ξ''| u ->
  Σ ;;; Ξ ,,, Ξ'' ⊢ t =η u.
Proof.
  intro H.
  remember (Ξ ,,, Ξ' ,,, Ξ'') as Ξ₀ eqn:e1.
  remember (lift #|Ξ'| #|Ξ''| t) as t₀ eqn:e2; remember (lift #|Ξ'| #|Ξ''| u) as u₀ eqn:e3.
  induction H in Ξ'', t, u, e1, e2, e3.
  destruct X.
  - apply eta_left. subst.
    eapply eta_left_spine_unlift; cbn; tea.
    now intros ???? [].
  - apply eta_right. subst.
    eapply eta_right_spine_unlift; cbn; tea.
    now intros ???? [].
  - apply eta_sprop; subst.
    + by apply isTermRel_unlift in Xt.
    + by apply isTermRel_unlift in Xt'.
  - apply eta_lambda_nodomain.
    destruct IX.
    move: t e2 => [] //= na₀ A₀ t₀ [= ? ? ?]; subst.
    move: u e3 => [] //= na₁ A₁ t₁ [= ? ? ?]; subst.
    constructor; tas. apply IXt.1 with (Ξ'' := Ξ'' ,, _); trea.
  - apply eta_clos.
    destruct IX.
    + move: t e2 => [] //= n₀ [= ?]; subst.
      move: u e3 => [] //= n₁ [= ?]; subst.
      suff H : n₀ = n₁ by subst; constructor.
      destruct (Nat.leb_spec #|Ξ''| n₀), (Nat.leb_spec #|Ξ''| n₁).
      all: lia.
    + move: t e2 => [] //= na₀ A₀ t₀ [= ? ? ?]; subst.
      move: u e3 => [] //= na₁ A₁ t₁ [= ? ? ?]; subst.
      constructor; tas.
      * apply IXA.1; trea.
      * apply IXt.1 with (Ξ'' := Ξ'' ,, _); trea.
    + move: t e2 => [] //= t₀ u₀ [= ? ?]; subst.
      move: u e3 => [] //= t₁ u₁ [= ? ?]; subst.
      constructor; tas.
      * apply IXt.1; trea.
      * apply IXu.1; trea.
    + move: t e2 => [] //= na₀ A₀ B₀ [= ? ? ?]; subst.
      move: u e3 => [] //= na₁ A₁ B₁ [= ? ? ?]; subst.
      constructor; tas.
      * apply IXA.1; trea.
      * apply IXB.1 with (Ξ'' := Ξ'' ,, _); trea.
    + move: t e2 => [] //= s₀ [= ?]; subst.
      move: u e3 => [] //= s₁ [= ?]; subst.
      constructor; tas.
Qed.

Lemma eta_spine_unlift0 {cf} {Σ Ξ t u} r :
  Σ ;;; Ξ ,, r ⊢ lift0 1 t =η lift0 1 u ->
  Σ ;;; Ξ ⊢ t =η u.
Proof. apply eta_spine_unlift with (Ξ' := [_]) (Ξ'' := []). Qed.

Lemma eta_left_spine_unlift0 {cf} {Σ Ξ t u args} r :
  Σ ;;; Ξ ,, r ⊢ lift0 1 t =η lift0 1 u · map S args ->
  Σ ;;; Ξ ⊢ t =η u · args.
Proof.
  intro.
  have IX : Σ ;;; Ξ,, r ⊢ lift0 1 t =η lift0 1 u · map S args on X with (fun _ _ _ _ => True)
    by eauto with fmap.
  eapply eta_left_spine_unlift with (Ξ' := [_]) (Ξ'' := []); tea.
  cbn. intros ???? _.
  eapply eta_spine_unlift with (Ξ' := [_]); eassumption.
Qed.

Lemma eta_right_spine_unlift0 {cf} {Σ Ξ t u args} r :
  Σ ;;; Ξ ,, r ⊢ lift0 1 t · map S args =η lift0 1 u ->
  Σ ;;; Ξ ⊢ t · args =η u.
Proof.
  intro.
  have IX : Σ ;;; Ξ,, r ⊢ lift0 1 t · map S args =η lift0 1 u on X with (fun _ _ _ _ => True)
    by eauto with fmap.
  eapply eta_right_spine_unlift with (Ξ' := [_]) (Ξ'' := []); tea.
  cbn. intros ???? _.
  eapply eta_spine_unlift with (Ξ' := [_]); eassumption.
Qed.



Reserved Notation "Σ  ;;; Ξ ⊢ t ~ u ~ v 'with' R" (at level 50, Ξ, t, u, v, R at next level).
Inductive context_closure_trans {cf} Σ R Ξ : forall (t u v : term), Type :=
  | clos_trans_rel n :
      Σ ;;; Ξ ⊢ tRel n ~ tRel n ~ tRel n with R

  | clos_trans_sort s s' s'' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(wfs'': wf_sort Σ s'')] ->
      [(Xs : eq_sort Σ s s')] ->
      [(Xs' : eq_sort Σ s' s'')] ->
      Σ ;;; Ξ ⊢ tSort s ~ tSort s' ~ tSort s'' with R

  | clos_tri_lambda na na' na'' A A' A'' t t' t'' :
      [(Xα : eq_binder_annot na na')] ->
      [(Xα' : eq_binder_annot na' na'')] ->
      (* [(XA : R Ξ A A' A'')] -> *)
      [(Xt : R (Ξ ,, na.(binder_relevance)) t t' t'')] ->
      Σ ;;; Ξ ⊢ tLambda na A t ~ tLambda na' A' t' ~ tLambda na'' A'' t'' with R

  | clos_tri_app f f' f'' a a' a'' :
      [(Xt : R Ξ f f' f'')] ->
      [(Xu : R Ξ a a' a'')] ->
      Σ ;;; Ξ ⊢ tApp f a ~ tApp f' a' ~ tApp f'' a'' with R

  | clos_tri_prod na na' na'' A A' A'' B B' B'' :
      [(Xα : eq_binder_annot na na')] ->
      [(Xα' : eq_binder_annot na' na'')] ->
      [(XA : R Ξ A A' A'')] ->
      [(XT : R (Ξ ,, na.(binder_relevance)) B B' B'')] ->
      Σ ;;; Ξ ⊢ tProd na A B ~ tProd na' A' B' ~ tProd na'' A'' B'' with R
where "Σ ;;; Ξ ⊢ t ~ u ~ v 'with' R" := (context_closure_trans Σ R Ξ t u v).
Derive Signature for context_closure_trans.

Reserved Notation "Σ  ;;; Ξ ⊢ t ≤c[ pb ] u ≤c[ pb' ] v 'with' R" (at level 50, Ξ, pb, pb', t, u, v, R at next level).
Inductive cumul_addon_trans {cf} Σ R Ξ pb pb' : forall (t u v : term), Type :=
  | cumul_trans_sort s s' s'' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(wfs'': wf_sort Σ s'')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      [(Xs' : compare_sort Σ pb' s' s'')] ->
      Σ ;;; Ξ ⊢ tSort s ≤c[pb] tSort s' ≤c[pb'] tSort s'' with R

  | cumul_tri_prod na na' na'' A A' A'' B B' B'' :
      [(Xα : eq_binder_annot na na')] ->
      [(Xα' : eq_binder_annot na' na'')] ->
      [(XA : R Ξ Conv Conv A A' A'')] ->
      [(XT : R (Ξ ,, na.(binder_relevance)) pb pb' B B' B'')] ->
      Σ ;;; Ξ ⊢ tProd na A B ≤c[pb] tProd na' A' B' ≤c[pb'] tProd na'' A'' B'' with R
where "Σ ;;; Ξ ⊢ t ≤c[ pb ] u ≤c[ pb' ] v 'with' R" := (cumul_addon_trans Σ R Ξ pb pb' t u v).
Derive Signature for cumul_addon_trans.



Reserved Notation "Σ ;;; Ξ ⊢ t <=[ pb ]η u <=[ pb' ]η v" (at level 50, Ξ, pb, pb', t, u, v at next level, format "Σ  ;;;  Ξ  ⊢  t  <=[ pb ]η  u  <=[ pb' ]η   v").
Reserved Notation "Σ  ;;; Ξ ⊢ t =η u =η v" (at level 50, Ξ, t, u, v at next level).

Reserved Notation "Σ  ;;; Ξ ⊢ t =η u =η v · Δ" (at level 50, Ξ, t, u, v, Δ at next level).
Reserved Notation "Σ  ;;; Ξ ⊢ t · Δ =η u =η v" (at level 50, Ξ, t, u, v, Δ at next level).
Reserved Notation "Σ  ;;; Ξ ⊢ ( t · Δ =η u ) · Δ' =η v" (at level 50, Ξ, t, u, v, Δ, Δ' at next level).
Reserved Notation "Σ  ;;; Ξ ⊢ t =η ( u =η v · Δ ) · Δ'" (at level 50, Ξ, t, u, v, Δ, Δ' at next level).
Reserved Notation "Σ  ;;; Ξ ⊢ t ·· Δ =η u =η v · Δ'" (at level 50, Ξ, t, u, v, Δ, Δ' at next level).
Reserved Notation "Σ  ;;; Ξ ⊢ t · Δ =η u =η v ·· Δ'" (at level 50, Ξ, t, u, v, Δ, Δ' at next level).

Section EtaSpineSide.
Context {cf} Σ.
Variable R : relevance_context -> term -> term -> term -> Type.
Notation "Σ ;;; Ξ ⊢ t =η t' =η u" := (R Ξ t t' u) (only parsing).

Local Set Elimination Schemes.

Section Inner.
Variable Rl : relevance_context -> term -> term -> term -> list nat -> Type.
Notation "Σ ;;; Ξ ⊢ t =η u =η v · Δ" := (Rl Ξ v t u Δ) (only parsing).
Variable Rr : relevance_context -> term -> term -> term -> list nat -> Type.
Notation "Σ ;;; Ξ ⊢ t · Δ =η u =η v" := (Rl Ξ t u v Δ) (only parsing).

Inductive eta_spine_trans_left Ξ u v Δ : forall t Δ', Type :=
  | eta_spine_trans_left_ground t :
      Σ ;;; Ξ ⊢ t =η u =η v · Δ ->
      Σ ;;; Ξ ⊢ t =η (u =η v · Δ) · []

  | eta_spine_trans_left_push Δ' na A t :
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t =η (lift0 1 u =η lift0 1 v · map S Δ) · map S Δ' ,, 0 ->
      Σ ;;; Ξ ⊢ tLambda na A t =η (u =η v · Δ) · Δ'

  | eta_spine_trans_left_pop Δ' n t z :
      Σ ;;; Ξ ⊢ t =η (u =η v · Δ) · Δ' ->
      Σ ;;; Ξ ⊢ z =η tRel n =η tRel n ->
      Σ ;;; Ξ ⊢ tApp t z =η (u =η v · Δ) · Δ' ,, n
where "Σ ;;; Ξ ⊢ t =η ( u =η v · Δ ) · Δ'" := (eta_spine_trans_left Ξ u v Δ t Δ') (only parsing).

Inductive eta_spine_trans_right Ξ t u Δ : forall v Δ', Type :=
  | eta_spine_trans_right_ground v :
      Σ ;;; Ξ ⊢ t · Δ =η u =η v ->
      Σ ;;; Ξ ⊢ (t · Δ =η u) · [] =η v

  | eta_spine_trans_right_push Δ' na A v :
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ (lift0 1 t · map S Δ =η lift0 1 u) · map S Δ' ,, 0 =η v ->
      Σ ;;; Ξ ⊢ (t · Δ =η u) · Δ' =η tLambda na A v

  | eta_spine_trans_right_pop Δ' n v z :
      Σ ;;; Ξ ⊢ (t · Δ =η u) · Δ' =η v ->
      Σ ;;; Ξ ⊢ tRel n =η tRel n =η z ->
      Σ ;;; Ξ ⊢ (t · Δ =η u) · Δ' ,, n =η tApp v z
where "Σ ;;; Ξ ⊢ ( t · Δ =η u ) · Δ' =η v" := (eta_spine_trans_right Ξ t u Δ v Δ') (only parsing).

Inductive eta_spine_trans_mid_left_right Ξ t v Δ : forall u Δ', Type :=
  | eta_spine_trans_mid_left_right_ground u :
      Σ ;;; Ξ ⊢ t · Δ =η u =η v ->
      Σ ;;; Ξ ⊢ t · Δ =η u =η v ·· []

  | eta_spine_trans_mid_left_right_push na A u Δ' :
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ lift0 1 t · map S Δ =η u =η lift0 1 v ·· map S Δ' ,, 0 ->
      Σ ;;; Ξ ⊢ t · Δ =η tLambda na A u =η v ·· Δ'

  | eta_spine_trans_mid_left_right_pop u n Δ' z :
      Σ ;;; Ξ ⊢ t · Δ =η u =η v ·· Δ' ->
      Σ ;;; Ξ ⊢ tRel n =η z =η tRel n ->
      Σ ;;; Ξ ⊢ t · Δ =η tApp u z =η v ·· Δ' ,, n

where "Σ ;;; Ξ ⊢ t · Δ =η u =η v ·· Δ'" := (eta_spine_trans_mid_left_right Ξ t v Δ u Δ') (only parsing).

Inductive eta_spine_trans_mid_right_left Ξ t v Δ : forall u Δ', Type :=
  | eta_spine_trans_mid_right_left_ground u :
      Σ ;;; Ξ ⊢ t =η u =η v · Δ ->
      Σ ;;; Ξ ⊢ t ·· [] =η u =η v · Δ

  | eta_spine_trans_mid_right_left_push na A u Δ' :
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ lift0 1 t ·· map S Δ' ,, 0 =η u =η lift0 1 v · map S Δ ->
      Σ ;;; Ξ ⊢ t ·· Δ' =η tLambda na A u =η v · Δ

  | eta_spine_trans_mid_right_left_pop u n Δ' z :
      Σ ;;; Ξ ⊢ t ·· Δ' =η u =η v · Δ ->
      Σ ;;; Ξ ⊢ tRel n =η z =η tRel n ->
      Σ ;;; Ξ ⊢ t ·· Δ' ,, n =η tApp u z =η v · Δ

where "Σ ;;; Ξ ⊢ t ·· Δ' =η u =η v · Δ" := (eta_spine_trans_mid_right_left Ξ t v Δ u Δ') (only parsing).

End Inner.

Inductive eta_spine_trans_mid_left Ξ v : forall t u Δ, Type :=
  | eta_spine_trans_mid_left_ground t u :
      Σ ;;; Ξ ⊢ t =η u =η v ->
      Σ ;;; Ξ ⊢ t =η u =η v · []

  | eta_spine_trans_mid_left_both t u Δ :
      Σ ;;; Ξ ⊢ t ·· [] =η u =η v · Δ ->
      Σ ;;; Ξ ⊢ t =η u =η v · Δ

  | eta_spine_trans_mid_left_left t u Δ :
      Σ ;;; Ξ ⊢ t =η (u =η v · Δ) · [] ->
      Σ ;;; Ξ ⊢ t =η u =η v · Δ

  | eta_spine_trans_mid_left_push na na' A A' t u Δ :
      eq_binder_annot na na' ->
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t =η u =η lift0 1 v · map S Δ ,, 0 ->
      Σ ;;; Ξ ⊢ tLambda na A t =η tLambda na' A' u =η v · Δ

  | eta_spine_trans_mid_left_pop t u n Δ z z' :
      Σ ;;; Ξ ⊢ t =η u =η v · Δ ->
      Σ ;;; Ξ ⊢ z =η z' =η tRel n ->
      Σ ;;; Ξ ⊢ tApp t z =η tApp u z' =η v · Δ ,, n

where "Σ ;;; Ξ ⊢ t =η u =η v · Δ" := (eta_spine_trans_mid_left Ξ v t u Δ) (only parsing)
and "Σ ;;; Ξ ⊢ t ·· Δ' =η u =η v · Δ" := (eta_spine_trans_mid_right_left eta_spine_trans_mid_left Ξ t v Δ u Δ') (only parsing)
and "Σ ;;; Ξ ⊢ t =η ( u =η v · Δ ) · Δ'" := (eta_spine_trans_left eta_spine_trans_mid_left Ξ u v Δ t Δ') (only parsing).

Inductive eta_spine_trans_mid_right Ξ t : forall u v Δ, Type :=
  | eta_spine_trans_mid_right_ground u v :
      Σ ;;; Ξ ⊢ t =η u =η v ->
      Σ ;;; Ξ ⊢ t · [] =η u =η v

  | eta_spine_trans_mid_right_both u v Δ :
      Σ ;;; Ξ ⊢ t · Δ =η u =η v ·· [] ->
      Σ ;;; Ξ ⊢ t · Δ =η u =η v

  | eta_spine_trans_mid_right_right u v Δ :
      Σ ;;; Ξ ⊢ (t · Δ =η u) · [] =η v ->
      Σ ;;; Ξ ⊢ t · Δ =η u =η v

  | eta_spine_trans_mid_right_push na na' A A' u v Δ :
      eq_binder_annot na na' ->
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ lift0 1 t · map S Δ ,, 0 =η u =η v ->
      Σ ;;; Ξ ⊢ t · Δ =η tLambda na A u =η tLambda na' A' v

  | eta_spine_trans_mid_right_pop u v n Δ z z' :
      Σ ;;; Ξ ⊢ t · Δ =η u =η v ->
      Σ ;;; Ξ ⊢ tRel n =η z =η z' ->
      Σ ;;; Ξ ⊢ t · Δ ,, n =η tApp u z =η tApp v z'

where "Σ ;;; Ξ ⊢ t · Δ =η u =η v" := (eta_spine_trans_mid_right Ξ t u v Δ) (only parsing)
and "Σ ;;; Ξ ⊢ t · Δ =η u =η v ·· Δ'" := (eta_spine_trans_mid_left_right eta_spine_trans_mid_right Ξ t v Δ u Δ') (only parsing)
and "Σ ;;; Ξ ⊢ ( t · Δ =η u ) · Δ' =η v" := (eta_spine_trans_right eta_spine_trans_mid_right Ξ t u Δ v Δ') (only parsing).

End EtaSpineSide.

Inductive equality_trans {cf} Σ Ξ : forall (t u v : term), Type :=
  (* closure vs closure *)
  | eqtrans_clos t u v :
      Σ ;;; Ξ ⊢ t ~ u ~ v with equality_trans Σ ->
      Σ ;;; Ξ ⊢ t =η u =η v

  (* sprop *)
  | eqtrans_sprop t u v :
      isTermRel Σ Ξ t Irrelevant ->
      isTermRel Σ Ξ u Irrelevant ->
      isTermRel Σ Ξ v Irrelevant ->
      Σ ;;; Ξ ⊢ t =η u =η v

  (* eta on the left *)
  | eqtrans_etal t u v :
      Σ ;;; Ξ ⊢ t =η u =η v · [] ->
      Σ ;;; Ξ ⊢ t =η u =η v

  (* eta on the right *)
  | eqtrans_etar t u v :
      Σ ;;; Ξ ⊢ t · [] =η u =η v ->
      Σ ;;; Ξ ⊢ t =η u =η v

where "Σ ;;; Ξ ⊢ t =η u =η v" := (@equality_trans _ Σ Ξ t u v)
and "Σ ;;; Ξ ⊢ t =η u =η v · Δ" := (eta_spine_trans_mid_left (equality_trans Σ) Ξ v t u Δ)
and "Σ ;;; Ξ ⊢ t · Δ =η u =η v" := (eta_spine_trans_mid_right (equality_trans Σ) Ξ t u v Δ).

Notation "Σ ;;; Ξ ⊢ t ·· Δ' =η u =η v · Δ" := (eta_spine_trans_mid_right_left (equality_trans Σ) (eta_spine_trans_mid_left (equality_trans Σ)) Ξ t v Δ u Δ').
Notation "Σ ;;; Ξ ⊢ t =η ( u =η v · Δ ) · Δ'" := (eta_spine_trans_left (equality_trans Σ) (eta_spine_trans_mid_left (equality_trans Σ)) Ξ u v Δ t Δ').
Notation "Σ ;;; Ξ ⊢ t · Δ =η u =η v ·· Δ'" := (eta_spine_trans_mid_left_right (equality_trans Σ) (eta_spine_trans_mid_right (equality_trans Σ)) Ξ t v Δ u Δ').
Notation "Σ ;;; Ξ ⊢ ( t · Δ =η u ) · Δ' =η v" := (eta_spine_trans_right (equality_trans Σ) (eta_spine_trans_mid_right (equality_trans Σ)) Ξ t u Δ v Δ').


Inductive equality_pb_trans {cf} Σ Ξ pb pb' : forall (t u v : term), Type :=
  (* closure vs closure *)
  | eqpbtrans_eqtrans t u v :
      Σ ;;; Ξ ⊢ t =η u =η v ->
      Σ ;;; Ξ ⊢ t <=[pb]η u <=[pb']η v

  | eqpbtrans_cumul_addon t u v :
      Σ ;;; Ξ ⊢ t ≤c[pb] u ≤c[pb'] v with equality_pb_trans Σ ->
      Σ ;;; Ξ ⊢ t <=[pb]η u <=[pb']η v
where "Σ ;;; Ξ ⊢ t <=[ pb ]η u <=[ pb' ]η v" := (@equality_pb_trans _ Σ Ξ pb pb' t u v).

Derive Signature for equality_trans equality_pb_trans.


Variant eta_spine_pack2 {cf} Σ :=
  | RegularRegular Ξ t u v (Htu : Σ ;;; Ξ ⊢ t =η u) (Huv : Σ ;;; Ξ ⊢ u =η v)
  | RightRegular Ξ Δ t u v (Htu : Σ ;;; Ξ ⊢ t · Δ =η u) (Huv : Σ ;;; Ξ ⊢ u =η v)
  | RegularLeft Ξ Δ t u v (Htu : Σ ;;; Ξ ⊢ t =η u) (Huv : Σ ;;; Ξ ⊢ u =η v · Δ)
  | LeftRegular Ξ Δ t u v (Htu : Σ ;;; Ξ ⊢ t =η u · Δ) (Huv : Σ ;;; Ξ ⊢ u =η v)
  | LeftLeft Ξ Δ Δ' t u v (Htu : Σ ;;; Ξ ⊢ t =η u · Δ') (Huv : Σ ;;; Ξ ⊢ u =η v · Δ)
  | RegularRight Ξ Δ t u v (Htu : Σ ;;; Ξ ⊢ t =η u) (Huv : Σ ;;; Ξ ⊢ u · Δ =η v)
  | RightRight Ξ Δ Δ' t u v (Htu : Σ ;;; Ξ ⊢ t · Δ =η u) (Huv : Σ ;;; Ξ ⊢ u · Δ' =η v)
  | RightLeft1 Ξ Δ Δ' t u v (Htu : Σ ;;; Ξ ⊢ t · Δ' =η u) (Huv : Σ ;;; Ξ ⊢ u =η v · Δ ,,, Δ')
  | RightLeft2 Ξ Δ Δ' t u v (Htu : Σ ;;; Ξ ⊢ t · Δ ,,, Δ' =η u) (Huv : Σ ;;; Ξ ⊢ u =η v · Δ').

Definition eta_spine_pack_size {cf} Σ x :=
  match x with
  | RegularRegular _ _ _ _ H H' => eta_spine_size H + eta_spine_size H'
  | RightRegular _ _ _ _ _ H H' => eta_right_spine_size (@eta_spine_size cf Σ) H + eta_spine_size H'
  | RegularLeft _ _ _ _ _ H H' => eta_spine_size H + eta_left_spine_size (@eta_spine_size cf Σ) H'
  | LeftRegular _ _ _ _ _ H H' => eta_left_spine_size (@eta_spine_size cf Σ) H + eta_spine_size H'
  | LeftLeft _ _ _ _ _ _ H H' => eta_left_spine_size (@eta_spine_size cf Σ) H + eta_left_spine_size (@eta_spine_size cf Σ) H'
  | RegularRight _ _ _ _ _ H H' => eta_spine_size H + eta_right_spine_size (@eta_spine_size cf Σ) H'
  | RightRight _ _ _ _ _ _ H H' => eta_right_spine_size (@eta_spine_size cf Σ) H + eta_right_spine_size (@eta_spine_size cf Σ) H'
  | RightLeft1 _ _ _ _ _ _ H H' => eta_right_spine_size (@eta_spine_size cf Σ) H + eta_left_spine_size (@eta_spine_size cf Σ) H'
  | RightLeft2 _ _ _ _ _ _ H H' => eta_right_spine_size (@eta_spine_size cf Σ) H + eta_left_spine_size (@eta_spine_size cf Σ) H'
  end.

Open Scope type.

Notation Goal Σ x :=
  match x with
  | RegularRegular Ξ t u v _ _ => Σ ;;; Ξ ⊢ t =η u =η v
  | RightRegular Ξ Δ t u v _ _ => Σ ;;; Ξ ⊢ t · Δ =η u =η v + isTermRel Σ Ξ u Irrelevant
  | RegularLeft Ξ Δ t u v _ _ => Σ ;;; Ξ ⊢ t =η u =η v · Δ + isTermRel Σ Ξ u Irrelevant
  | LeftRegular Ξ Δ t u v _ _ => Σ ;;; Ξ ⊢ t =η (u =η v · []) · Δ + isTermRel Σ Ξ u Irrelevant
  | LeftLeft Ξ Δ Δ' t u v _ _ => Σ ;;; Ξ ⊢ t =η (u =η v · Δ) · Δ' + isTermRel Σ Ξ u Irrelevant
  | RegularRight Ξ Δ t u v _ _ => Σ ;;; Ξ ⊢ (t · [] =η u) · Δ =η v + isTermRel Σ Ξ u Irrelevant
  | RightRight Ξ Δ Δ' t u v _ _ => Σ ;;; Ξ ⊢ (t · Δ =η u) · Δ' =η v + isTermRel Σ Ξ u Irrelevant
  | RightLeft1 Ξ Δ Δ' t u v _ _ => Σ ;;; Ξ ⊢ t ·· Δ' =η u =η v · Δ + isTermRel Σ Ξ u Irrelevant
  | RightLeft2 Ξ Δ Δ' t u v _ _ => Σ ;;; Ξ ⊢ t · Δ =η u =η v ·· Δ' + isTermRel Σ Ξ u Irrelevant
  end.


Lemma eta_spine_closure_equality_trans cf Σ Ξ t u v :
  [(X : Σ ;;; Ξ ⊢ t ~ u with eta_spine Σ, eq_binder_annot, eq_sort Σ)] ->
  [(X' : Σ ;;; Ξ ⊢ u ~ v with eta_spine Σ, eq_binder_annot, eq_sort Σ)] ->
  [(IH Ξ t' u' v' (Htu' : Σ ;;; Ξ ⊢ t' =η u') (Huv' : Σ ;;; Ξ ⊢ u' =η v') :
    eta_spine_size Htu' + eta_spine_size Huv' <
    context_closure_size (@eta_spine_size cf Σ) X + context_closure_size (@eta_spine_size cf Σ) X' ->
    Σ ;;; Ξ ⊢ t' =η u' =η v')] ->
  Σ ;;; Ξ ⊢ t ~ u ~ v with equality_trans Σ.
Proof.
  intros Htu Huv IH.
  destruct Htu; depelim Huv.
  - constructor.
  - cbn in IH.
    econstructor; tea.
    destruct Xα.
    unshelve eapply IH; tea.
    all: cbn; lia.
  - econstructor; tea.
    all: unshelve eapply IH; tea.
    all: cbn; lia.
  - cbn in IH.
    econstructor; tea.
    2: destruct Xα.
    all: unshelve eapply IH; tea.
    all: cbn; lia.
  - by constructor.
Qed.


Lemma sum_left_map {A A' B} (f : A -> A') : A + B -> A' + B.
Proof. destruct 1; eauto. Defined.
Lemma sum_right_map {A B B'} (f : B -> B') : A + B -> A + B'.
Proof. destruct 1; eauto. Defined.
Ltac lapply e := eapply sum_left_map; [eapply e|].
Ltac lapply2 e := eapply sum_left_map; [let H := fresh in intro H; eapply e; [> .. | exact H|]|].
Ltac rapply e := eapply sum_right_map; [eapply e|].

Lemma case_regular_regular cf Σ Ξ t u v :
  [(Htu : Σ ;;; Ξ ⊢ t =η u)] ->
  [(Huv : Σ ;;; Ξ ⊢ u =η v)] ->
  [(IH x : eta_spine_pack_size Σ x < eta_spine_size Htu + eta_spine_size Huv -> Goal Σ x)] ->
  Σ ;;; Ξ ⊢ t =η u =η v.
Proof.
  revert Ξ t u v.
  have XIrr Ξ t u v :
    [(Htu : Σ ;;; Ξ ⊢ t =η u)] ->
    [(Huv : Σ ;;; Ξ ⊢ u =η v)] ->
    Σ ;;; Ξ ⊢ t =η u =η v + isTermRel Σ Ξ u Irrelevant ->
    Σ ;;; Ξ ⊢ t =η u =η v.
  { intros ?? []; tas.
    apply eqtrans_sprop; tas.
    - eapply eta_spine_relevance in Htu; by apply Htu.
    - eapply eta_spine_relevance in Huv; by apply Huv. }
  have XLeftReg Ξ t u v :
    [(Htu : Σ ;;; Ξ ⊢ t =η u · [])] ->
    [(Huv : Σ ;;; Ξ ⊢ u =η v)] ->
    [(IH x : eta_spine_pack_size Σ x < eta_spine_size (eta_left _ _ _ _ Htu) + eta_spine_size Huv -> Goal Σ x)] ->
    Σ ;;; Ξ ⊢ t =η u =η v.
  { intros.
    apply XIrr; tas. 1: by constructor.
    lapply eqtrans_etal. lapply eta_spine_trans_mid_left_left.
    unshelve eapply (IH ltac:(eapply LeftRegular)); tea.
    cbn. lia. }
  have XRightReg Ξ t u v :
    [(Htu : Σ ;;; Ξ ⊢ t · [] =η u)] ->
    [(Huv : Σ ;;; Ξ ⊢ u =η v)] ->
    [(IH x : eta_spine_pack_size Σ x < eta_spine_size (eta_right _ _ _ _ Htu) + eta_spine_size Huv -> Goal Σ x)] ->
    Σ ;;; Ξ ⊢ t =η u =η v.
  { intros.
    apply XIrr; tas. 1: by constructor.
    lapply eqtrans_etar.
    unshelve eapply (IH ltac:(eapply RightRegular)); tea.
    cbn. lia. }
  have XRegLeft Ξ t u v :
    [(Htu : Σ ;;; Ξ ⊢ t =η u)] ->
    [(Huv : Σ ;;; Ξ ⊢ u =η v · [])] ->
    [(IH x : eta_spine_pack_size Σ x < eta_spine_size Htu + eta_spine_size (eta_left _ _ _ _ Huv) -> Goal Σ x)] ->
    Σ ;;; Ξ ⊢ t =η u =η v.
  { intros.
    apply XIrr; tas. 1: by constructor.
    lapply eqtrans_etal.
    unshelve eapply (IH ltac:(eapply RegularLeft)); tea.
    cbn. lia. }
  have XRegRight Ξ t u v :
    [(Htu : Σ ;;; Ξ ⊢ t =η u)] ->
    [(Huv : Σ ;;; Ξ ⊢ u · [] =η v)] ->
    [(IH x : eta_spine_pack_size Σ x < eta_spine_size Htu + eta_spine_size (eta_right _ _ _ _ Huv) -> Goal Σ x)] ->
    Σ ;;; Ξ ⊢ t =η u =η v.
  { intros.
    apply XIrr; tas. 1: by constructor.
    lapply eqtrans_etar. lapply eta_spine_trans_mid_right_right.
    unshelve eapply (IH ltac:(eapply RegularRight)); tea.
    cbn. lia. }

  have XLambda Ξ na na' na'' A A' A'' t t' t'' :
    eq_binder_annot na na' ->
    eq_binder_annot na' na'' ->
    [(Xt : Σ ;;; Ξ ,, binder_relevance na ⊢ t =η t')] ->
    [(Xt' : Σ ;;; Ξ ,, binder_relevance na' ⊢ t' =η t'' )] ->
    (forall x : eta_spine_pack2 Σ, eta_spine_pack_size Σ x <= eta_spine_size Xt + eta_spine_size Xt' ->
      Goal Σ x) ->
    Σ ;;; Ξ ⊢ tLambda na A t =η tLambda na' A' t' =η tLambda na'' A'' t''.
  { intros Xα Xα' ?? IH.
    cbn in IH.
    apply eqtrans_clos. econstructor; tea.
    destruct Xα.
    unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
    cbn; lia. }

  refine (
    fun Ξ t u v Htu Huv => match Htu, Huv with
    | eta_left Htu, Huv => XLeftReg Ξ t u v Htu Huv
    | eta_right Htu, Huv => XRightReg Ξ t u v Htu Huv
    | Htu, eta_left Huv => XRegLeft Ξ t u v Htu Huv
    | Htu, eta_right Huv => XRegRight Ξ t u v Htu Huv
    | eta_sprop _ H, _
    | _, eta_sprop H _ => fun _ => XIrr Ξ t u v Htu Huv (inr H)
    | eta_lambda_nodomain Htu, eta_lambda_nodomain Huv => _
    | eta_lambda_nodomain Htu, eta_clos Huv => _
    | eta_clos Htu, eta_lambda_nodomain Huv => _
    | eta_clos Htu, eta_clos Huv => _
    end
  ).
  all: intro IH; clear XLeftReg XRightReg XRegLeft XRegRight XIrr Htu0 Huv0 e.

  - destruct Htu; depelim Huv.
    cbn in IH.
    unshelve eapply XLambda; tea.
    intros; apply IH. lia.
  - destruct Htu; depelim Huv.
    cbn in IH.
    unshelve eapply XLambda; tea.
    intros; apply IH. lia.
  - destruct Htu; depelim Huv.
    cbn in IH.
    unshelve eapply XLambda; tea.
    intros; apply IH. lia.
  - unshelve eapply eqtrans_clos, eta_spine_closure_equality_trans; tea.
    intros; unshelve eapply (IH ltac:(eapply RegularRegular)); tea. cbn. lia.
Qed.

Lemma case_right_regular cf Σ Ξ Δ t u v :
  [(Htu : Σ ;;; Ξ ⊢ t · Δ =η u)] ->
  [(Huv : Σ ;;; Ξ ⊢ u =η v)] ->
  [(IH x : eta_spine_pack_size Σ x < eta_right_spine_size (@eta_spine_size cf Σ) Htu + eta_spine_size Huv -> Goal Σ x)] ->
  Σ ;;; Ξ ⊢ t · Δ =η u =η v + isTermRel Σ Ξ u Irrelevant.
Proof.
  have XRegReg Ξ' t' u' v' :
    [(Htu : Σ ;;; Ξ' ⊢ t' =η u')] ->
    [(Huv : Σ ;;; Ξ' ⊢ u' =η v')] ->
    [(IH x : eta_spine_pack_size Σ x <= eta_spine_size Htu + eta_spine_size Huv -> Goal Σ x)] ->
    Σ ;;; Ξ' ⊢ t' · [] =η u' =η v' + isTermRel Σ Ξ' u' Irrelevant.
  { intros. left.
    apply eta_spine_trans_mid_right_ground.
    unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
    cbn. lia. }
  have XLambda Ξ' Δ' t₀ na na' A A' u' v' :
    eq_binder_annot na na' ->
    [(Xt : Σ ;;; Ξ' ,, binder_relevance na ⊢ lift0 1 t₀ · map S Δ' ,, 0 =η u')] ->
    [(Xt' : Σ ;;; Ξ' ,, binder_relevance na ⊢ u' =η v' )] ->
    (forall x : eta_spine_pack2 Σ, eta_spine_pack_size Σ x <= eta_right_spine_size (@eta_spine_size cf Σ) Xt + eta_spine_size Xt' ->
      Goal Σ x) ->
    Σ ;;; Ξ' ⊢ t₀ · Δ' =η tLambda na A u' =η tLambda na' A' v' + isTermRel Σ Ξ' (tLambda na A u') Irrelevant.
  { intros Xα ?? IH.
    cbn in IH.
    lapply eta_spine_trans_mid_right_push; tas.
    rapply isTermRel_lambda.
    unshelve eapply (IH ltac:(eapply RightRegular)); tea.
    cbn; unfold snoc, app_context in *. lia. }

  intros ?? IH.
  destruct Huv.
  - lapply eta_spine_trans_mid_right_both.
    unshelve eapply (IH ltac:(eapply RightLeft2)); tea.
    cbn. lia.
  - lapply eta_spine_trans_mid_right_right.
    unshelve eapply (IH ltac:(eapply RightRight)); tea.
    cbn. lia.
  - by right.
  - destruct Htu.
    + unshelve eapply XRegReg; tea.
      1: by constructor.
      cbn. intros; apply IH. cbn. lia.
    + depelim X.
      unshelve eapply XLambda; tea.
      cbn. intros; apply IH. cbn. lia.
    + depelim X.
  - destruct Htu.
    + unshelve eapply XRegReg; tea.
      1: by constructor.
      cbn. intros; apply IH. cbn. lia.
    + depelim X.
      unshelve eapply XLambda; tea.
      cbn. intros; apply IH. cbn. lia.
    + depelim X.
      cbn in IH.
      rapply isTermRel_app.
      lapply2 eta_spine_trans_mid_right_pop; tas.
      * unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
        cbn; lia.
      * unshelve eapply (IH ltac:(eapply RightRegular)); tea.
        cbn; lia.
Qed.


Lemma case_regular_left cf Σ Ξ Δ t u v :
  [(Htu : Σ ;;; Ξ ⊢ t =η u)] ->
  [(Huv : Σ ;;; Ξ ⊢ u =η v · Δ)] ->
  [(IH x : eta_spine_pack_size Σ x < eta_spine_size Htu + eta_left_spine_size (@eta_spine_size cf Σ) Huv -> Goal Σ x)] ->
  Σ ;;; Ξ ⊢ t =η u =η v · Δ + isTermRel Σ Ξ u Irrelevant.
Proof.
  have XRegReg Ξ' t' u' v' :
    [(Htu : Σ ;;; Ξ' ⊢ t' =η u')] ->
    [(Huv : Σ ;;; Ξ' ⊢ u' =η v')] ->
    [(IH x : eta_spine_pack_size Σ x <= eta_spine_size Htu + eta_spine_size Huv -> Goal Σ x)] ->
    Σ ;;; Ξ' ⊢ t' =η u' =η v' · [] + isTermRel Σ Ξ u' Irrelevant.
  { intros. left.
    apply eta_spine_trans_mid_left_ground.
    unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
    cbn. lia. }
  have XLambda Ξ' Δ' na na' A A' t' u' v' :
    eq_binder_annot na na' ->
    [(Xt : Σ ;;; Ξ' ,, binder_relevance na ⊢ t' =η u')] ->
    [(Xt' : Σ ;;; Ξ' ,, binder_relevance na' ⊢ u' =η lift0 1 v' · map S Δ' ,, 0 )] ->
    (forall x : eta_spine_pack2 Σ, eta_spine_pack_size Σ x <= eta_spine_size Xt + eta_left_spine_size (@eta_spine_size cf Σ) Xt' ->
      Goal Σ x) ->
    Σ ;;; Ξ' ⊢ tLambda na A t' =η tLambda na' A' u' =η v' · Δ' + isTermRel Σ Ξ' (tLambda na' A' u') Irrelevant.
  { intros Xα ?? IH.
    cbn in IH.
    lapply eta_spine_trans_mid_left_push; tas.
    rapply isTermRel_lambda.
    destruct Xα.
    unshelve eapply (IH ltac:(eapply RegularLeft)); tea.
    cbn; unfold snoc, app_context in *. lia. }

  intros ?? IH.
  destruct Htu.
  - lapply eta_spine_trans_mid_left_left.
    unshelve eapply (IH ltac:(eapply LeftLeft)); tea.
    cbn. lia.
  - lapply eta_spine_trans_mid_left_both.
    unshelve eapply (IH ltac:(eapply RightLeft1)); tea.
    cbn. lia.
  - by right.
  - destruct Huv.
    + unshelve eapply XRegReg; tea.
      1: by constructor.
      cbn. intros; apply IH. cbn. lia.
    + depelim X.
      unshelve eapply XLambda; tea.
      cbn. intros; apply IH. cbn. lia.
    + depelim X.
  - destruct Huv.
    + unshelve eapply XRegReg; tea.
      1: by constructor.
      cbn. intros; apply IH. cbn. lia.
    + depelim X.
      unshelve eapply XLambda; tea.
      cbn. intros; apply IH. cbn. lia.
    + depelim X.
      cbn in IH.
      rapply isTermRel_app.
      lapply2 eta_spine_trans_mid_left_pop; tas.
      * unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
        cbn; lia.
      * unshelve eapply (IH ltac:(eapply RegularLeft)); tea.
        cbn; lia.
Qed.

Lemma case_left_regular cf Σ Ξ Δ t u v :
  [(Htu : Σ ;;; Ξ ⊢ t =η u · Δ)] ->
  [(Huv : Σ ;;; Ξ ⊢ u =η v)] ->
  [(IH x : eta_spine_pack_size Σ x < eta_left_spine_size (@eta_spine_size cf Σ) Htu + eta_spine_size Huv -> Goal Σ x)] ->
  Σ ;;; Ξ ⊢ t =η (u =η v · []) · Δ + isTermRel Σ Ξ u Irrelevant.
Proof.
  intros ?? IH.
  destruct Htu.
  - lapply eta_spine_trans_left_ground. lapply eta_spine_trans_mid_left_ground. left.
    unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
    cbn. lia.
  - lapply eta_spine_trans_left_push. cbn.
    rapply isTermRel_lift'.
    epose proof (eta_spine_lift0_size _ Huv) as [Huv' e].
    unshelve eapply (IH ltac:(eapply LeftRegular)); tea.
    cbn. lia.
  - lapply2 eta_spine_trans_left_pop.
    + unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
      { by do 2 constructor. }
      cbn. lia.
    + unshelve eapply (IH ltac:(eapply LeftRegular)); tea.
      cbn. lia.
Qed.

Lemma case_left_left cf Σ Ξ Δ Δ' t u v :
  [(Htu : Σ ;;; Ξ ⊢ t =η u · Δ')] ->
  [(Huv : Σ ;;; Ξ ⊢ u =η v · Δ)] ->
  [(IH x : eta_spine_pack_size Σ x < eta_left_spine_size (@eta_spine_size cf Σ) Htu + eta_left_spine_size (@eta_spine_size cf Σ) Huv -> Goal Σ x)] ->
  Σ ;;; Ξ ⊢ t =η (u =η v · Δ) · Δ' + isTermRel Σ Ξ u Irrelevant.
Proof.
  intros ?? IH.
  destruct Htu.
  - lapply eta_spine_trans_left_ground.
    unshelve eapply (IH ltac:(eapply RegularLeft)); tea.
    cbn. lia.
  - lapply eta_spine_trans_left_push. cbn.
    rapply isTermRel_lift'.
    epose proof (eta_left_spine_lift0_size _ Huv) as [Huv' e].
    unshelve eapply (IH ltac:(eapply LeftLeft)); tea.
    cbn. lia.
  - lapply2 eta_spine_trans_left_pop.
    + unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
      { by do 2 constructor. }
      cbn. lia.
    + unshelve eapply (IH ltac:(eapply LeftLeft)); tea.
      cbn. lia.
Qed.


Lemma case_regular_right cf Σ Ξ Δ t u v :
  [(Htu : Σ ;;; Ξ ⊢ t =η u)] ->
  [(Huv : Σ ;;; Ξ ⊢ u · Δ =η v)] ->
  [(IH x : eta_spine_pack_size Σ x < eta_spine_size Htu + eta_right_spine_size (@eta_spine_size cf Σ)  Huv -> Goal Σ x)] ->
  Σ ;;; Ξ ⊢ (t · [] =η u) · Δ =η v + isTermRel Σ Ξ u Irrelevant.
Proof.
  intros ?? IH.
  destruct Huv.
  - lapply eta_spine_trans_right_ground. lapply eta_spine_trans_mid_right_ground. left.
    unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
    cbn. lia.
  - lapply eta_spine_trans_right_push. cbn.
    rapply isTermRel_lift'.
    epose proof (eta_spine_lift0_size _ Htu) as [Htu' e].
    unshelve eapply (IH ltac:(eapply RegularRight)); tea.
    cbn. lia.
  - lapply2 eta_spine_trans_right_pop.
    + unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
      { by do 2 constructor. }
      cbn. lia.
    + unshelve eapply (IH ltac:(eapply RegularRight)); tea.
      cbn. lia.
Qed.

Lemma case_right_right cf Σ Ξ Δ Δ' t u v :
  [(Htu : Σ ;;; Ξ ⊢ t · Δ =η u)] ->
  [(Huv : Σ ;;; Ξ ⊢ u · Δ' =η v)] ->
  [(IH x : eta_spine_pack_size Σ x < eta_right_spine_size (@eta_spine_size cf Σ) Htu + eta_right_spine_size (@eta_spine_size cf Σ) Huv -> Goal Σ x)] ->
  Σ ;;; Ξ ⊢ (t · Δ =η u) · Δ' =η v + isTermRel Σ Ξ u Irrelevant.
Proof.
  intros ?? IH.
  destruct Huv.
  - lapply eta_spine_trans_right_ground.
    unshelve eapply (IH ltac:(eapply RightRegular)); tea.
    cbn. lia.
  - lapply eta_spine_trans_right_push. cbn.
    rapply isTermRel_lift'.
    epose proof (eta_right_spine_lift0_size _ Htu) as [Htu' e].
    unshelve eapply (IH ltac:(eapply RightRight)); tea.
    cbn. lia.
  - lapply2 eta_spine_trans_right_pop.
    + unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
      { by do 2 constructor. }
      cbn. lia.
    + unshelve eapply (IH ltac:(eapply RightRight)); tea.
      cbn. lia.
Qed.

Lemma case_right_left1 cf Σ Ξ Δ Δ' t u v :
  [(Htu : Σ ;;; Ξ ⊢ t · Δ' =η u)] ->
  [(Huv : Σ ;;; Ξ ⊢ u =η v · Δ ,,, Δ')] ->
  [(IH x : eta_spine_pack_size Σ x < eta_right_spine_size (@eta_spine_size cf Σ) Htu + eta_left_spine_size (@eta_spine_size cf Σ) Huv -> Goal Σ x)] ->
  Σ ;;; Ξ ⊢ t ·· Δ' =η u =η v · Δ + isTermRel Σ Ξ u Irrelevant.
Proof.
  revert Ξ Δ Δ' t u v.

  have XGround2 Ξ Δ Δ' t u v :
    [(Htu : Σ ;;; Ξ ⊢ t · Δ' =η u)] ->
    [(Huv : Σ ;;; Ξ ⊢ u =η v)] ->
    [] = Δ ,,, Δ' ->
    [(IH x : eta_spine_pack_size Σ x < eta_right_spine_size (@eta_spine_size cf Σ) Htu + (1 + eta_spine_size Huv) -> Goal Σ x)] ->
    Σ ;;; Ξ ⊢ t ·· Δ' =η u =η v · Δ + isTermRel Σ Ξ u Irrelevant.
  { intros.
    destruct Δ, Δ' => //.
    lapply eta_spine_trans_mid_right_left_ground.
    lapply eta_spine_trans_mid_left_ground.
    lapply eqtrans_etar.
    unshelve eapply (IH ltac:(eapply RightRegular)); tea.
    cbn. lia. }

  intros ?????? ?? IH.
  destruct Htu.
  - lapply eta_spine_trans_mid_right_left_ground.
    unshelve eapply (IH ltac:(eapply RegularLeft)); tea.
    cbn. lia.
  - cbn in IH.
    remember (Δ,,, Δ0) as args eqn:e. remember (tLambda na A t') eqn:e'.
    destruct Huv => //.
    + subst.
      unshelve eapply XGround2; trea.
      1: by constructor.
      apply IH.
    + noconf e'. subst.
      lapply eta_spine_trans_mid_right_left_push.
      rapply isTermRel_lambda.
      unshelve eapply (IH ltac:(eapply RightLeft1)); tea.
      * clear IH.
        rewrite map_app //= in Huv.
      * cbn. destruct map_app. cbn. unfold app_context, snoc. lia.
  - depelim Huv.
    rapply isTermRel_app.
    lapply2 eta_spine_trans_mid_right_left_pop.
    + unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
      cbn. lia.
    + unshelve eapply (IH ltac:(eapply RightLeft1)); tea.
      cbn. lia.
Qed.

Lemma case_right_left2 cf Σ Ξ Δ Δ' t u v :
  [(Htu : Σ ;;; Ξ ⊢ t · Δ ,,, Δ' =η u)] ->
  [(Huv : Σ ;;; Ξ ⊢ u =η v · Δ')] ->
  [(IH x : eta_spine_pack_size Σ x < eta_right_spine_size (@eta_spine_size cf Σ) Htu + eta_left_spine_size (@eta_spine_size cf Σ) Huv -> Goal Σ x)] ->
  Σ ;;; Ξ ⊢ t · Δ =η u =η v ·· Δ' + isTermRel Σ Ξ u Irrelevant.
Proof.
  revert Ξ Δ Δ' t u v.

  have XGround2 Ξ Δ Δ' t u v :
    [(Htu : Σ ;;; Ξ ⊢ t =η u)] ->
    [(Huv : Σ ;;; Ξ ⊢ u =η v · Δ')] ->
    [] = Δ ,,, Δ' ->
    [(IH x : eta_spine_pack_size Σ x < 1 + eta_spine_size Htu + eta_left_spine_size (@eta_spine_size cf Σ) Huv -> Goal Σ x)] ->
    Σ ;;; Ξ ⊢ t · Δ =η u =η v ·· Δ' + isTermRel Σ Ξ u Irrelevant.
  { intros.
    destruct Δ, Δ' => //.
    lapply eta_spine_trans_mid_left_right_ground.
    lapply eta_spine_trans_mid_right_ground.
    lapply eqtrans_etal.
    unshelve eapply (IH ltac:(eapply RegularLeft)); tea.
    cbn. lia. }

  intros ?????? ?? IH.
  destruct Huv.
  - lapply eta_spine_trans_mid_left_right_ground.
    unshelve eapply (IH ltac:(eapply RightRegular)); tea.
    cbn. lia.
  - cbn in IH.
    remember (Δ,,, Δ0) as args eqn:e. remember (tLambda na A t0) eqn:e'.
    destruct Htu => //.
    + subst.
      unshelve eapply XGround2; trea.
      1: by constructor.
      apply IH.
    + noconf e'. subst.
      lapply eta_spine_trans_mid_left_right_push.
      rapply isTermRel_lambda.
      unshelve eapply (IH ltac:(eapply RightLeft2)); tea.
      * clear IH.
        rewrite map_app //= in Htu.
      * cbn. destruct map_app. cbn. unfold app_context, snoc. lia.
  - depelim Htu.
    rapply isTermRel_app.
    lapply2 eta_spine_trans_mid_left_right_pop.
    + unshelve eapply (IH ltac:(eapply RegularRegular)); tea.
      cbn. lia.
    + unshelve eapply (IH ltac:(eapply RightLeft2)); tea.
      cbn. lia.
Qed.

Lemma eta_spine_trans_aux cf Σ (x : eta_spine_pack2 Σ) :
  Goal Σ x.
Proof.
  eassert (e : Acc _ x).
  { apply wf_precompose with (m := eta_spine_pack_size Σ), lt_wf. }
  induction e using Fix_F.
  destruct x; cbn in X.
  - eapply case_regular_regular; tea.
  - eapply case_right_regular; tea.
  - eapply case_regular_left; tea.
  - eapply case_left_regular; tea.
  - eapply case_left_left; tea.
  - eapply case_regular_right; tea.
  - eapply case_right_right; tea.
  - eapply case_right_left1; tea.
  - eapply case_right_left2; tea.
Qed.


Theorem eq_trans_equality_trans cf Σ Ξ t u v :
  Σ ;;; Ξ ⊢ t =η u ->
  Σ ;;; Ξ ⊢ u =η v ->
  Σ ;;; Ξ ⊢ t =η u =η v.
Proof.
  intros Htu Huv.
  set (Htuv := RegularRegular _ _ _ _ _ Htu Huv).
  change _ with (Goal Σ Htuv).
  apply eta_spine_trans_aux.
Qed.



Theorem equality_trans_sides cf Σ Ξ t u v :
  Σ ;;; Ξ ⊢ t =η u =η v ->
  Σ ;;; Ξ ⊢ t =η v.
Proof.
  revert Ξ t u v.
  fix rec 5.
  intros ???? X. destruct X.
  - destruct c.
    all: try solve [eapply eta_clos; constructor; eauto].
    + eapply eta_clos.
      constructor; tas. etransitivity; eassumption.
    + eapply eta_lambda_nodomain.
      constructor; tas. 1: etransitivity; eassumption.
      eapply rec; eassumption.
    + eapply eta_clos.
      constructor; tas. 1: etransitivity; eassumption.
      all: eapply rec; eassumption.
  - by apply eta_sprop.
  - apply eta_left.
    move: [] e => Δ X.
    move: Ξ Δ t u v X.
    fix recL 6.
    intros ????? X. destruct X.
    + apply etal_ground. now eapply rec.
    + move: [] e => Δ' X.
      move: Ξ Δ Δ' t u v X.
      fix recLR 7.
      intros ?????? X. destruct X.
      * eapply recL. eassumption.
      * eapply eta_left_spine_unlift0.
        eapply recLR. eassumption.
      * eapply recLR. eassumption.
    + change Δ with (Δ ,,, []).
      move: [] e => Δ' X.
      move: Ξ Δ Δ' t u v X.
      fix recLL 7.
      intros ?????? X. destruct X.
      * eapply recL. eassumption.
      * constructor. rewrite map_app /=.
        eapply recLL with (Δ' := map S Δ' ,, _). eassumption.
      * cbn. constructor.
        --eapply recLL. eassumption.
        --eapply rec. eassumption.
    + constructor.
      eapply recL. eassumption.
    + constructor.
      --eapply recL. eassumption.
      --eapply rec. eassumption.
  - apply eta_right.
    move: [] e => Δ X.
    move: Ξ Δ t u v X.
    fix recR 6.
    intros ????? X. destruct X.
    + apply etar_ground. now eapply rec.
    + move: [] e => Δ' X.
      move: Ξ Δ Δ' t u v X.
      fix recRL 7.
      intros ?????? X. destruct X.
      * eapply recR. eassumption.
      * eapply eta_right_spine_unlift0.
        eapply recRL. eassumption.
      * eapply recRL. eassumption.
    + change Δ with (Δ ,,, []).
      move: [] e => Δ' X.
      move: Ξ Δ Δ' t u v X.
      fix recRR 7.
      intros ?????? X. destruct X.
      * eapply recR. eassumption.
      * constructor. rewrite map_app /=.
        eapply recRR with (Δ' := map S Δ' ,, _). eassumption.
      * cbn. constructor.
        --eapply recRR. eassumption.
        --eapply rec. eassumption.
    + constructor.
      eapply recR. destruct e. eassumption.
    + constructor.
      --eapply recR. eassumption.
      --eapply rec. eassumption.
Qed.



Definition max_pb pb pb' := match pb with Cumul => Cumul | Conv => pb' end.
Lemma max_pb_left R :
  [(X pb t u T : R Conv t u T -> R pb t u T)] ->
  forall pb pb' (t u T : term), R pb t u T -> R (max_pb pb pb') t u T.
Proof. intros X [][] ???; eauto. Qed.
Lemma max_pb_right R :
  [(X pb t u T : R Conv t u T -> R pb t u T)] ->
  forall pb pb' (t u T : term), R pb' t u T -> R (max_pb pb pb') t u T.
Proof. intros X [][] ???; eauto. Qed.
Lemma max_pb_left' R :
  [(X pb t u : R Conv t u -> R pb t u)] ->
  forall pb pb' (t u : sort), R pb t u -> R (max_pb pb pb') t u.
Proof. intros X [][] ???; eauto. Qed.
Lemma max_pb_right' R :
  [(X pb t u : R Conv t u -> R pb t u)] ->
  forall pb pb' (t u : sort), R pb' t u -> R (max_pb pb pb') t u.
Proof. intros X [][] ???; eauto. Qed.



Theorem eta_spine_trans cf Σ Ξ t u v :
  Σ ;;; Ξ ⊢ t =η u ->
  Σ ;;; Ξ ⊢ u =η v ->
  Σ ;;; Ξ ⊢ t =η v.
Proof.
  intros Htu Huv.
  eapply equality_trans_sides.
  now eapply eq_trans_equality_trans.
Qed.

Theorem eta_spine_pb_trans cf Σ Ξ pb pb' t u v :
  Σ ;;; Ξ ⊢ t <=[pb]η u ->
  Σ ;;; Ξ ⊢ u <=[pb']η v ->
  Σ ;;; Ξ ⊢ t <=[max_pb pb pb']η v.
Proof.
  intros Htu Huv.
  induction Htu in pb', v, Huv |- *; rename t' into u.
  - induction Huv; rename t0 into u, t' into v.
    + constructor.
      now eapply eta_spine_trans.
    + admit.
  - constructor. admit.
Abort.

End Untyped.
End UntypedTrial.


















































































































































































































Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]η  t'  :  T").
Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' : T 'on' H 'with' R'" (at level 50, Γ, t, pb, t', T, H at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]η  t'  :  T  'on'  H  'with'  R'").
Reserved Notation "Σ  ;;; Γ ⊢ t =η t' : T" (at level 50, Γ, t, t', T at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =η t' : T 'on' H 'with' R'" (at level 50, Γ, t, t', T, H at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =η ↑^ t' · args : 'Π' Δ , T" (at level 50, Γ, Δ, t, t', args, T at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t =η ↑^ t' · args : 'Π' Δ , T 'on' H 'with' R'" (at level 50, Γ, Δ, t, t', args, T, H at next level).
Reserved Notation "Σ  ;;; Γ ⊢ ↑^ t · args =η t' : 'Π' Δ , T" (at level 50, Γ, Δ, t, t', args, T at next level).
Reserved Notation "Σ  ;;; Γ ⊢ ↑^ t · args =η t' : 'Π' Δ , T 'on' H 'with' R'" (at level 50, Γ, Δ, t, t', args, T, H at next level).


Section Eta.

Definition prod_spine := list (aname × term).
Fixpoint it_mkProd (Δ : prod_spine) T :=
  match Δ with [] => T | nA :: Δ => tProd nA.1 nA.2 (it_mkProd Δ T) end.
Definition mkvass nA := vass nA.1 nA.2.

Context TC.
Variable R : context -> term -> term -> term -> Type.
Variable R' : forall Γ t u T, R Γ t u T -> Type.
Notation "Σ ;;; Γ ⊢ t =η t' : T" := (R Γ t t' T) (only parsing).
Notation "Σ ;;; Γ ⊢ t =η' t' : T 'on' H" := (R' Γ t t' T H) (only parsing, at level 50, Γ, t, t', T at next level).
Local Set Elimination Schemes.

Inductive eta_left_spine Σ Γ Δ t' T : forall t args, Type :=
  (* | etal_sprop t args :
      Σ ;;; Γ ,,, rev_map mkvass (firstn args Δ) ⊢ t : it_mkProd (skipn args Δ) T ->
      Σ ;;; Γ ⊢ t' : it_mkProd Δ T ->
      Σ ;;; Γ ⊢ it_mkProd (skipn args Δ) T : tSort sSProp ->
      Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T *)

  | etal_ground t :
      [(X : Σ ;;; Γ ⊢ t =η t' : it_mkProd Δ T)] ->
      Σ ;;; Γ ⊢ t =η ↑^ t' · 0 : Π Δ, T

  | etal_push nA na A t args :
      [(Hnth : nth_error Δ args = Some nA)] ->
      [(eqna : eq_binder_annot nA.1 na)] ->
      [(HA : Σ ;;; Γ ,,, rev_map mkvass (firstn args Δ) ⊢ nA.2 ≤T A)] ->
      [(X : Σ ;;; Γ ⊢ t =η ↑^ t' · S args : Π Δ, T)] ->
      Σ ;;; Γ ⊢ tLambda na A t =η ↑^ t' · args : Π Δ, T

  | etal_pop nA t args z :
      [(Hnth : nth_error Δ args = Some nA)] ->
      [(Xz : Σ ;;; Γ ,,, rev_map mkvass (firstn (S args) Δ) ⊢ z =η tRel 0 : lift0 1 nA.2)] ->
      [(X : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T)] ->
      Σ ;;; Γ ⊢ tApp (lift0 1 t) z =η ↑^ t' · S args : Π Δ, T

where "Σ ;;; Γ ⊢ t =η ↑^ t' · args : 'Π' Δ , T" := (eta_left_spine Σ Γ Δ t' T t args) (only parsing).
Derive Signature for eta_left_spine.

Inductive eta_left_spineε Σ Γ Δ t' T : forall t args, Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T -> Type :=
  (* | etalε_sprop t args T₀ :
      [(Xt : Σ ;;; Γ ,,, Δ ⊢ t : T₀)] ->
      [(Ht' : Σ ;;; Γ ⊢ t' : T')] ->
      [(Xt' : Σ ;;; Γ ,,, Δ ⊢ mkApps (lift0 #|Δ| t') (rev_map tRel args) : T₀)] ->
      [(XT₀ : Σ ;;; Γ ,,, Δ ⊢ T₀ : tSort sSProp)] ->
      [(XT : Σ ;;; Γ ,,, Δ ⊢ T₀ ≤* T)] ->
      Σ ;;; Γ ;;; Δ ⊢ t =η ↑^ t' · args : T | T' on ⌈etal_sprop⌋ with R' *)

  | etalε_ground t :
      [(XR : Σ ;;; Γ ⊢ t =η t' : it_mkProd Δ T)] ->
      [(IXR : Σ ;;; Γ ⊢ t =η' t' : it_mkProd Δ T on XR)] ->
      Σ ;;; Γ ⊢ t =η ↑^ t' · 0 : Π Δ, T on ⌈etal_ground⌋ with R'

  | etalε_push nA na A t args :
      [(Hnth : nth_error Δ args = Some nA)] ->
      [(eqna : eq_binder_annot nA.1 na)] ->
      [(HA : Σ ;;; Γ ,,, rev_map mkvass (firstn args Δ) ⊢ nA.2 ≤T A)] ->
      [(X : Σ ;;; Γ ⊢ t =η ↑^ t' · S args : Π Δ, T)] ->
      [(IX : Σ ;;; Γ ⊢ t =η ↑^ t' · S args : Π Δ, T on X with R')] ->
      Σ ;;; Γ ⊢ tLambda na A t =η ↑^ t' · args : Π Δ, T on ⌈etal_push⌋ with R'

  | etalε_pop nA t args z :
      [(Hnth : nth_error Δ args = Some nA)] ->
      [(Xz : Σ ;;; Γ ,,, rev_map mkvass (firstn (S args) Δ) ⊢ z =η tRel 0 : lift0 1 nA.2)] ->
      [(IXz : Σ ;;; Γ ,,, rev_map mkvass (firstn (S args) Δ) ⊢ z =η' tRel 0 : lift0 1 nA.2 on Xz)] ->
      [(X : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T)] ->
      [(IX : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T on X with R')] ->
      Σ ;;; Γ ⊢ tApp (lift0 1 t) z =η ↑^ t' · S args : Π Δ, T on ⌈etal_pop⌋ with R'
where "Σ ;;; Γ ⊢ t =η ↑^ t' · args : 'Π' Δ , T 'on' H 'with' R'" := (eta_left_spineε Σ Γ Δ t' T t args H) (only parsing).
Derive Signature for eta_left_spineε.

Inductive eta_right_spine Σ Γ Δ t T : forall t' args, Type :=
  (* | etar_sprop t' args :
      Σ ;;; Γ ,,, map mkvass (firstn args Δ) ⊢ t' : it_mkProd (skipn args Δ) T ->
      Σ ;;; Γ ⊢ t : it_mkProd Δ T ->
      Σ ;;; Γ ⊢ it_mkProd (skipn args Δ) T : tSort sSProp ->
      Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T *)

  | etar_ground t' :
      [(X : Σ ;;; Γ ⊢ t =η t' : it_mkProd Δ T)] ->
      Σ ;;; Γ ⊢ ↑^ t · 0 =η t' : Π Δ, T

  | etar_push nA na A t' args :
      [(Hnth : nth_error Δ args = Some nA)] ->
      [(eqna : eq_binder_annot nA.1 na)] ->
      [(HA : Σ ;;; Γ ,,, rev_map mkvass (firstn args Δ) ⊢ nA.2 ≤T A)] ->
      [(X : Σ ;;; Γ ⊢ ↑^ t · S args =η t' : Π Δ, T)] ->
      Σ ;;; Γ ⊢ ↑^ t · args =η tLambda na A t' : Π Δ, T

  | etar_pop nA t' args z :
      [(Hnth : nth_error Δ args = Some nA)] ->
      [(Xz : Σ ;;; Γ ,,, rev_map mkvass (firstn (S args) Δ) ⊢ tRel 0 =η z : lift0 1 nA.2)] ->
      [(X : Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T)] ->
      Σ ;;; Γ ⊢ ↑^ t · S args =η tApp (lift0 1 t') z : Π Δ, T
where "Σ ;;; Γ ⊢ ↑^ t · args =η t' : 'Π' Δ , T" := (eta_right_spine Σ Γ Δ t T t' args).
Derive Signature for eta_right_spine.

Inductive eta_right_spineε Σ Γ Δ t T : forall t' args, Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T -> Type :=
  (* | etarε_sprop t' args T₀ :
      [(Ht : Σ ;;; Γ ⊢ t : T)] ->
      [(Xt : Σ ;;; Γ ,,, Δ ⊢ mkApps (lift0 #|Δ| t) (rev_map tRel args) : T₀)] ->
      [(Xt' : Σ ;;; Γ ,,, Δ ⊢ t' : T₀)] ->
      [(XT₀ : Σ ;;; Γ ,,, Δ ⊢ T₀ : tSort sSProp)] ->
      [(XT : Σ ;;; Γ ,,, Δ ⊢ T₀ ≤* T')] ->
      Σ ;;; Γ ;;; Δ ⊢ ↑^ t · args =η t' : T | T' on ⌈etar_sprop⌋ with R' *)

  | etarε_ground t' :
      [(XR : Σ ;;; Γ ⊢ t =η t' : it_mkProd Δ T)] ->
      [(IXR : Σ ;;; Γ ⊢ t =η' t' : it_mkProd Δ T on XR)] ->
      Σ ;;; Γ ⊢ ↑^ t · 0 =η t' : Π Δ, T on ⌈etar_ground⌋ with R'

  | etarε_push nA na A t' args :
      [(Hnth : nth_error Δ args = Some nA)] ->
      [(eqna : eq_binder_annot nA.1 na)] ->
      [(HA : Σ ;;; Γ ,,, rev_map mkvass (firstn args Δ) ⊢ nA.2 ≤T A)] ->
      [(X : Σ ;;; Γ ⊢ ↑^ t · S args =η t' : Π Δ, T)] ->
      [(IX : Σ ;;; Γ ⊢ ↑^ t · S args =η t' : Π Δ, T on X with R')] ->
      Σ ;;; Γ ⊢ ↑^ t · args =η tLambda na A t' : Π Δ, T on ⌈etar_push⌋ with R'

  | etarε_pop nA t' args z :
      [(Hnth : nth_error Δ args = Some nA)] ->
      [(Xz : Σ ;;; Γ ,,, rev_map mkvass (firstn (S args) Δ) ⊢ tRel 0 =η z : lift0 1 nA.2)] ->
      [(IXz : Σ ;;; Γ ,,, rev_map mkvass (firstn (S args) Δ) ⊢ tRel 0 =η' z : lift0 1 nA.2 on Xz)] ->
      [(X : Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T)] ->
      [(IX : Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T on X with R')] ->
      Σ ;;; Γ ⊢ ↑^ t · S args =η tApp (lift0 1 t') z : Π Δ, T on ⌈etar_pop⌋ with R'
where "Σ ;;; Γ ⊢ ↑^ t · args =η t' : 'Π' Δ , T 'on' H 'with' R'" := (eta_right_spineε Σ Γ Δ t T t' args H) (only parsing).
Derive Signature for eta_right_spineε.

Unset Elimination Schemes.
End Eta.

Inductive eta_spine {cf TC} Σ Γ t t' T : Type :=
  | eta_left Δ B :
      [(XT : Σ ;;; Γ ⊢ it_mkProd Δ B ≤* T)] ->
      [(X : Σ ;;; Γ ⊢ t =η ↑^ t' · 0 : Π Δ, B)] ->
      Σ ;;; Γ ⊢ t =η t' : T

  | eta_right Δ B :
      [(XT : Σ ;;; Γ ⊢ it_mkProd Δ B ≤* T)] ->
      [(X : Σ ;;; Γ ⊢ ↑^ t · 0 =η t' : Π Δ, B)] ->
      Σ ;;; Γ ⊢ t =η t' : T

  | eta_sprop T₀ :
      [(Ht : Σ ;;; Γ ⊢ t : T₀)] ->
      [(Ht': Σ ;;; Γ ⊢ t': T₀)] ->
      [(HT : Σ ;;; Γ ⊢ T₀ : tSort sSProp)] ->
      [(XT : Σ ;;; Γ ⊢ T₀ ≤* T)] ->
      Σ ;;; Γ ⊢ t =η t' : T

  | eta_clos T₀ :
      [(X : Σ ;;; Γ ⊢ t ~ t' : T₀ with eta_spine Σ, eq_binder_annot, eq_sort Σ)] ->
      [(XT : Σ ;;; Γ ⊢ T₀ ≤* T)] ->
      Σ ;;; Γ ⊢ t =η t' : T

where "Σ ;;; Γ ⊢ t =η t' : T" := (eta_spine Σ Γ t t' T)
and "Σ ;;; Γ ⊢ t =η ↑^ t' · args : 'Π' Δ , T" := (eta_left_spine _ (eta_spine Σ) Σ Γ Δ t' T t args)
and "Σ ;;; Γ ⊢ ↑^ t · args =η t' : 'Π' Δ , T" := (eta_right_spine _ (eta_spine Σ) Σ Γ Δ t T t' args).
Derive Signature for eta_spine.

Inductive eta_spine_pb {cf TC} Σ Γ pb t t' T : Type :=
  | eta_spine_eta_pb :
    Σ ;;; Γ ⊢ t =η t' : T ->
    Σ ;;; Γ ⊢ t <=[pb]η t' : T

  | eta_pb_cumul_addon T₀ :
    Σ ;;; Γ ⊢ t ≤c[pb] t' : T₀ with (eta_spine_pb Σ) ->
    Σ ;;; Γ ⊢ T₀ ≤* T ->
    Σ ;;; Γ ⊢ t <=[pb]η t' : T
where "Σ ;;; Γ ⊢ t <=[ pb ]η t' : T" := (eta_spine_pb Σ Γ pb t t' T).
Derive Signature for eta_spine_pb.

Notation "Σ ;;; Γ ⊢ t =η ↑^ t' · args : 'Π' Δ , T 'on' H 'with' R'" := (eta_left_spineε _ (eta_spine Σ) R' Σ Γ Δ t' T t args H).
Notation "Σ ;;; Γ ⊢ ↑^ t · args =η t' : 'Π' Δ , T 'on' H 'with' R'" := (eta_right_spineε _ (eta_spine Σ) R' Σ Γ Δ t T t' args H).


Lemma eta_left_spine_toε {cf TC} Σ R' Γ Δ t t' args T :
  [(p : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T)] ->
  [(X Γ t t' T : [(H : eta_spine Σ Γ t t' T)] -> R' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Lemma eta_left_spineε_fmap {cf TC} Σ R R' Γ Δ t t' args T :
  [(p : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T)] ->
  [(H : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T on p with R)] ->
  [(X Γ t t' T (H : eta_spine Σ Γ t t' T) : R Γ t t' T H -> R' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T on p with R'.
Proof.
  intros.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Lemma eta_right_spine_toε {cf TC} Σ R' Γ Δ t t' args T :
  [(p : Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T)] ->
  [(X Γ t t' T : [(H : eta_spine Σ Γ t t' T)] -> R' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Lemma eta_right_spineε_fmap {cf TC} Σ R R' Γ Δ t t' args T :
  [(p : Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T)] ->
  [(H : Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T on p with R)] ->
  [(X Γ t t' T : [(H : eta_spine Σ Γ t t' T)] -> R Γ t t' T H -> R' Γ t t' T H)] ->
  Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T on p with R'.
Proof.
  intros.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Hint Resolve eta_left_spine_toε eta_left_spineε_fmap eta_right_spine_toε eta_right_spineε_fmap : fmap.



Inductive eta_spineε {cf TC} Σ R' Γ t t' T : Σ ;;; Γ ⊢ t =η t' : T -> Type :=
  | etaε_left Δ B :
      [(XT : Σ ;;; Γ ⊢ it_mkProd Δ B ≤* T)] ->
      [(X : Σ ;;; Γ ⊢ t =η ↑^ t' · 0 : Π Δ, B)] ->
      [(IX : Σ ;;; Γ ⊢ t =η ↑^ t' · 0 : Π Δ, B on X with (fun Γ t u T H => R' Γ t u T × eta_spineε Σ R' Γ t u T H))] ->
      Σ ;;; Γ ⊢ t =η t' : T on ⌈eta_left⌋ with R'

  | etaε_right Δ B :
      [(XT : Σ ;;; Γ ⊢ it_mkProd Δ B ≤* T)] ->
      [(X : Σ ;;; Γ ⊢ ↑^ t · 0 =η t' : Π Δ, B)] ->
      [(IX : Σ ;;; Γ ⊢ ↑^ t · 0 =η t' : Π Δ, B on X with (fun Γ t u T H => R' Γ t u T × eta_spineε Σ R' Γ t u T H))] ->
      Σ ;;; Γ ⊢ t =η t' : T on ⌈eta_right⌋ with R'

  | etaε_sprop T₀ :
      [(Xt : Σ ;;; Γ ⊢ t : T₀)] ->
      [(Xt' : Σ ;;; Γ ⊢ t': T₀)] ->
      [(XT₀ : Σ ;;; Γ ⊢ T₀ : tSort sSProp)] ->
      [(XT : Σ ;;; Γ ⊢ T₀ ≤* T)] ->
      Σ ;;; Γ ⊢ t =η t' : T on ⌈eta_sprop⌋ with R'

  | etaε_clos T₀ :
      [(X : Σ ;;; Γ ⊢ t ~ t' : T₀ with eta_spine Σ, eq_binder_annot, eq_sort Σ)] ->
      [(IX : Σ ;;; Γ ⊢ t ~ t' : T₀ ondep X with (fun Γ t u T H => R' Γ t u T × eta_spineε Σ R' Γ t u T H))] ->
      [(XT : Σ ;;; Γ ⊢ T₀ ≤* T)] ->
      Σ ;;; Γ ⊢ t =η t' : T on ⌈eta_clos⌋ with R'

where "Σ ;;; Γ ⊢ t =η t' : T 'on' H 'with' R'" := (eta_spineε Σ R' Γ t t' T H).
Derive Signature for eta_spineε.

Definition eta_spine_rect cf TC Σ P :
  [(Xrec Γ t u T : [(H : Σ ;;; Γ ⊢ t =η u : T)] -> [(IH : eta_spineε Σ P Γ t u T H)] -> P Γ t u T)] ->
  forall Γ t u T, [(H : Σ ;;; Γ ⊢ t =η u : T)] -> P Γ t u T.
Proof.
  intros.
  unshelve eapply Xrec; tea.
  revert Γ t u T H. fix rec 5.
  destruct H.
  all: unshelve econstructor; unshelve eauto with fmap; eauto.
Qed.


Definition eta_spine_pb_rect cf TC Σ P :
  [(Xbase Γ pb t t' T :
    [(X : Σ ;;; Γ ⊢ t =η t' : T)] ->
    P Γ pb t t' T)] ->

  [(XCumulAddon Γ pb t t' T T₀ :
    [(X : Σ ;;; Γ ⊢ t ≤c[pb] t' : T₀ with eta_spine_pb Σ)] ->
    [(IX : Σ ;;; Γ ⊢ t ≤c[pb] t' : T₀ on X with P)] ->
    [(XT : Σ ;;; Γ ⊢ T₀ ≤* T)] ->
    P Γ pb t t' T)] ->
  forall Γ pb t u T, [(H : Σ ;;; Γ ⊢ t <=[pb]η u : T)] -> P Γ pb t u T.
Proof.
  intros.
  revert Γ pb t u T H. fix rec 6.
  destruct 1.
  - unshelve eapply Xbase; tea.
  - unshelve eapply XCumulAddon; tea.
    unshelve eauto with fmap; eauto.
Qed.



Lemma eta_spine_cumul cf TC Σ Γ t t' T U :
  Σ ;;; Γ ⊢ t =η t' : T ->
  Σ ;;; Γ ⊢ T ≤T U ->
  Σ ;;; Γ ⊢ t =η t' : U.
Proof.
  intros Xe XT.
  have XT' T' : Σ ;;; Γ ⊢ T' ≤* T -> Σ ;;; Γ ⊢ T' ≤* U
    by now apply TCI_rstep.
  destruct Xe; now econstructor; eauto.
Qed.

Lemma eta_spine_pb_cumul cf TC Σ Γ pb t t' T U :
  Σ ;;; Γ ⊢ t <=[pb]η t' : T ->
  Σ ;;; Γ ⊢ T ≤T U ->
  Σ ;;; Γ ⊢ t <=[pb]η t' : U.
Proof.
  intros Xe XT.
  have XT' T' : Σ ;;; Γ ⊢ T' ≤* T -> Σ ;;; Γ ⊢ T' ≤* U
    by now apply TCI_rstep.
  induction Xe in XT, XT'.
  - constructor 1.
    now eapply eta_spine_cumul.
  - now econstructor 2.
Qed.

Instance TC_compat_eta_spine cf TC Σ Γ t t' : TC_compat TC Σ Γ (eta_spine Σ Γ t t'). intros ????. now eapply eta_spine_cumul. Defined.
Instance TC_compat_eta_spine_pb cf TC Σ Γ pb t t' : TC_compat TC Σ Γ (eta_spine_pb Σ Γ pb t t'). intros ????. now eapply eta_spine_pb_cumul. Defined.



Lemma context_closure_typing_left' {TC} Σ Pα Ps P P' (Pre : TCFromCompareSort Σ Ps) Γ t u T :
  [(onP Γ t u T H : P' Γ t u T H -> Σ ;;; Γ ⊢ t : T)] ->
  [(H : Σ ;;; Γ ⊢ t ~ u : T with P, Pα, Ps)] ->
  [(X : Σ ;;; Γ ⊢ t ~ u : T ondep H with P')] ->
  Σ ;;; Γ ⊢ t : T.
Proof.
  intros.
  induction X.
  - now econstructor.
  - apply onP in IXA, IXt.
    have Xj : lift_typing typing Σ Γ (j_vass na A).
    { repeat eexists; tea. }
    econstructor; tea.
  - econstructor; eauto.
  - apply onP in IXA, IXB.
    have Xj : lift_typing typing Σ Γ (j_vass_s na A s).
    { repeat eexists; tea. }
    econstructor; tea.
  - econstructor.
    1: now constructor.
    eapply TC_from_compare_sort; tas.
    1,2: by apply wf_sort_super.
    now apply TC_super.
Qed.

Lemma context_closure_typing_right' {cf TC CC} Σ P P'
  (CCH : ContextChangeable (typing Σ) Σ)
  (CCR : CCTypedRefl CC TC Σ)
  (ITC : RevImpliesTC Σ P)
  (TCCC : TCIsCmpType Σ)
  (TCP : TCFromCompareProd Σ P)
  (TCS : TCFromCompareSubst10 Σ P)
  Γ t u T :
  [(onP' Γ t u T H : P' Γ t u T H -> Σ ;;; Γ ⊢ u : T)] ->
  [(X : Σ ;;; Γ ⊢ t ~ u : T with P, eq_binder_annot, eq_sort Σ)] ->
  [(IX : Σ ;;; Γ ⊢ t ~ u : T ondep X with P')] ->
  Σ ;;; Γ ⊢ u : T.
Proof.
  intros.
  induction IX.
  - now econstructor.
  - apply onP' in IXA, IXt.
    have Xj' : lift_typing typing Σ Γ (j_vass na' A').
    { repeat eexists; tea. rewrite /= -Xα //. }
    econstructor; tea.
    + econstructor; tea.
      eapply change_context; tea.
      eapply convertible_contexts_snoc_vass; tea.
      now eapply typing_wf_local.
    + now eapply TC_from_compare_prod.
  - econstructor; eauto.
    1: econstructor; eauto.
    * now eapply TC_from_compare_subst10.
  - apply onP' in IXA, IXB.
    have Xj' : lift_typing typing Σ Γ (j_vass_s na' A' s).
    { repeat eexists; tea. rewrite /= -Xα //. }
    constructor; tas.
    eapply change_context; tea.
    eapply convertible_contexts_snoc_vass; tea.
    now eapply typing_wf_local.
  - now constructor.
Qed.




Lemma lambda_change_domain TC Σ Γ na na' A A' t B :
  Σ ;;; Γ ,, vass na A ⊢ t : B ->
  eq_binder_annot na na' ->
  Σ ;;; Γ ⊢ A ≤T A' ->
  Σ ;;; Γ ⊢ tLambda na' A' t : tProd na A B.
Proof.
  intros Xt e XA.
  econstructor.
  1: econstructor.
  todo "".
Qed.

Lemma lambda_inv_change_domain TC Σ Γ na na' A A' t B :
  Σ ;;; Γ ⊢ tLambda na' A' t : tProd na A B ->
  Σ ;;; Γ ,, vass na A ⊢ t : B.
Proof.
  intro X.
  dependent destruction X using typing_elim. subst ty.

  todo "".
Qed.


Lemma typing_lift0 TC Σ Γ Δ t T :
  Σ ;;; Γ ⊢ t : T ->
  All_local_rel (lift_typing typing Σ) Γ Δ ->
  Σ ;;; Γ ,,, Δ ⊢ lift0 #|Δ| t : lift0 #|Δ| T.
Proof.
  todo "".
Qed.


Lemma eta_left_spine_left_typing cf TC Σ P Γ Δ t t' args T :
  [(XP Γ t t' T H : P Γ t t' T H -> Σ ;;; Γ ⊢ t : T)] ->
  [(H : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T)] ->
  [(X : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T on H with P)] ->
  Σ ;;; Γ ,,, rev_map mkvass (firstn args Δ) ⊢ t : it_mkProd (skipn args Δ) T.
Proof.
  induction 2.
  - cbn. now eapply XP.
  - move: (skipn_nth_error Δ args).
    rewrite Hnth /= => e.
    have e' : firstn (S args) Δ = firstn args Δ ++ [nA].
    { rewrite -Nat.add_1_r firstn_add e //=. }
    rewrite e /=.
    eapply lambda_change_domain; tea.
    rewrite e' rev_map_app //= in IHX.
  - move: (skipn_nth_error Δ args).
    rewrite Hnth /= => e.
    have e' : firstn (S args) Δ = firstn args Δ ++ [nA].
    { rewrite -Nat.add_1_r firstn_add e //=. }
    rewrite e /= in IHX.
    rewrite e' rev_map_app /= {1}/mkvass -/(snoc _ _) in Xz, IXz |- *.
    eapply typing_lift0 with (Δ := [mkvass nA]) in IHX.
    2: { apply XP, typing_wf_local in IXz. apply All_local_env_tip in IXz as []. constructor; tas. constructor. }
    cbn in IHX.
    rewrite -[it_mkProd _ _]subst_rel0_lift.
    have HT : Σ ;;; (Γ,,, rev_map mkvass (firstn args Δ)),, vass nA.1 nA.2 ⊢ (lift 1 1 (it_mkProd (skipn (S args) Δ) T)) {0 := z} ≤T (lift 1 1 (it_mkProd (skipn (S args) Δ) T)) {0 := tRel 0} by todo "".
    econstructor; tea.
    econstructor; tea.
    now eapply XP.
Qed.

Lemma eta_left_spine_right_typing cf TC Σ P Γ Δ t t' args T :
  [(XP Γ t t' T H : P Γ t t' T H -> Σ ;;; Γ ⊢ t' : T)] ->
  [(H : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T)] ->
  [(X : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T on H with P)] ->
  Σ ;;; Γ ⊢ t' : it_mkProd Δ T.
Proof.
  induction 2 => //.
  now eapply XP.
Qed.

Lemma eta_right_spine_left_typing cf TC Σ P Γ Δ t t' args T :
  [(XP Γ t t' T H : P Γ t t' T H -> Σ ;;; Γ ⊢ t : T)] ->
  [(H : Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T)] ->
  [(X : Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T on H with P)] ->
  Σ ;;; Γ ⊢ t : it_mkProd Δ T.
Proof.
  induction 2 => //.
  now eapply XP.
Qed.

Lemma eta_right_spine_right_typing cf TC Σ P Γ Δ t t' args T :
  [(XP Γ t t' T H : P Γ t t' T H -> Σ ;;; Γ ⊢ t' : T)] ->
  [(H : Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T)] ->
  [(X : Σ ;;; Γ ⊢ ↑^ t · args =η t' : Π Δ, T on H with P)] ->
  Σ ;;; Γ ,,, rev_map mkvass (firstn args Δ) ⊢ t' : it_mkProd (skipn args Δ) T.
Proof.
  induction 2.
  - now eapply XP.
  - move: (skipn_nth_error Δ args).
    rewrite Hnth /= => e.
    have e' : firstn (S args) Δ = firstn args Δ ++ [nA].
    { rewrite -Nat.add_1_r firstn_add e //=. }
    rewrite e /=.
    eapply lambda_change_domain; tea.
    rewrite e' rev_map_app //= in IHX.
  - move: (skipn_nth_error Δ args).
    rewrite Hnth /= => e.
    have e' : firstn (S args) Δ = firstn args Δ ++ [nA].
    { rewrite -Nat.add_1_r firstn_add e //=. }
    rewrite e /= in IHX.
    rewrite e' rev_map_app /= {1}/mkvass -/(snoc _ _) in Xz, IXz |- *.
    eapply typing_lift0 with (Δ := [mkvass nA]) in IHX.
    2: { apply XP, typing_wf_local in IXz. apply All_local_env_tip in IXz as []. constructor; tas. constructor. }
    cbn in IHX.
    rewrite -[it_mkProd _ _]subst_rel0_lift.
    have HT : Σ ;;; (Γ,,, rev_map mkvass (firstn args Δ)),, vass nA.1 nA.2 ⊢ (lift 1 1 (it_mkProd (skipn (S args) Δ) T)) {0 := z} ≤T (lift 1 1 (it_mkProd (skipn (S args) Δ) T)) {0 := tRel 0} by todo "".
    econstructor; tea.
    econstructor; tea.
    now eapply XP.
Qed.

Lemma eta_spine_left_typing cf TC Σ {Pre : TCFromCompareSort Σ (eq_sort Σ)} Γ t t' T :
  [(H : Σ ;;; Γ ⊢ t =η t' : T)] ->
  Σ ;;; Γ ⊢ t : T.
Proof.
  induction 1. destruct IH.
  - eapply TCI_elim; tea; tc.
    eapply eta_left_spine_left_typing with (args := 0); tea.
    now intros ????? [].
  - eapply TCI_elim; tea; tc.
    eapply eta_right_spine_left_typing with (args := 0); tea.
    now intros ????? [].
  - eapply TCI_elim; tea; tc.
  - eapply TCI_elim; tea; tc.
    eapply context_closure_typing_left' in IX; tea.
    now intros ????? [].
Qed.

Lemma eta_spine_right_typing cf TC Σ
  {CC : ContextChangeable (typing Σ) (eta_spine Σ)}
  {TR : TypedReflexivity (eta_spine Σ) Σ}
  {TCP : TCFromCompareProd Σ (eta_spine Σ)}
  {TCS : TCFromCompareSubst10 Σ (eta_spine Σ)}
  Γ t t' T :
  [(H : Σ ;;; Γ ⊢ t =η t' : T)] ->
  Σ ;;; Γ ⊢ t' : T.
Proof.
  induction 1. destruct IH.
  - eapply TCI_elim; tea; tc.
    eapply eta_left_spine_right_typing with (args := 0); tea.
    now intros ????? [].
  - eapply TCI_elim; tea; tc.
    eapply eta_right_spine_right_typing with (args := 0); tea.
    now intros ????? [].
  - eapply TCI_elim; tea; tc.
  - eapply TCI_elim; tea; tc.
    eapply context_closure_typing_right' in IX; tea.
    now intros ????? [].
Qed.


Class EtaRetyping cf TC Σ := {
  ER_TC_Sort ::> TCFromCompareSort Σ (eq_sort Σ);
  ER_shared_pi_type Γ t Δ T U :
    Σ ;;; Γ ⊢ t : it_mkProd Δ T -> Σ ;;; Γ ⊢ t : U ->
    ∑ Δ₀ T₀, Σ ;;; Γ ⊢ t : it_mkProd Δ₀ T₀ × Σ ;;; Γ ⊢ it_mkProd Δ₀ T₀ ≤T U × Σ ;;; Γ ⊢ it_mkProd Δ₀ T₀ ≤T it_mkProd Δ T
}.

Lemma skipn_Sn_nth_error {A} Δ args (nA : A) :
  nth_error Δ args = Some nA ->
  skipn args Δ = nA :: skipn (S args) Δ.
Proof. intro e. move: (skipn_nth_error Δ args). rewrite e //. Qed.

Lemma rev_map_firstn_nth_error {A B} (f : A -> B) Δ args nA :
  nth_error Δ args = Some nA ->
  rev_map f (firstn (S args) Δ) = rev_map f (firstn args Δ) ,, f nA.
Proof.
  intro.
  rewrite -Nat.add_1_r firstn_add rev_map_app //=.
  rewrite (skipn_Sn_nth_error _ _ nA) //=.
Qed.

Lemma eta_spine_left_retyping_left cf TC Σ P (Pre : EtaRetyping cf TC Σ) Γ Δ t t' args T Γ' U :
  [(H : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T)] ->
  [(X : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T on H with P)] ->
  [(onP Γ t t' T H : P Γ t t' T H -> forall Γ' U, Σ ;;; Γ' ⊢ t : U -> Σ ;;; Γ' ⊢ t =η t' : U)] ->
  Σ ;;; Γ' ,,, rev_map mkvass (firstn args Δ) ⊢ t : U ->
  ∑ Δ' T',
  Σ ;;; Γ' ,,, rev_map mkvass (firstn args Δ) ⊢ it_mkProd (skipn args Δ') T' ≤* U ×
  All2 (fun nA nA' => eq_binder_annot nA.1 nA'.1) Δ' Δ ×
  Σ ;;; Γ' ⊢ t =η ↑^ t' · args : Π Δ', T'.
Proof.
  intros H X onP XT.
  induction X in Γ', U, XT.
  - cbn in XT.
    todo "".
  - dependent destruction XT using typing_elim.
    have {}XT : Σ ;;; Γ',,, rev_map mkvass (firstn args Δ),, mkvass nA ⊢ t : B
      by todo "".
    rewrite <- rev_map_firstn_nth_error in XT; tas.

    edestruct IHX as (Δ' & T' & XU & XΔ & Xr); cbn; tea.
    exists Δ', T'. repeat split; tea.

    { etransitivity; tea.
      subst ty.
      todo "". }

    eapply All2_nth_error_Some_r with (1 := XΔ) in Hnth as (nA' & Hnth' & h).
    econstructor; tea.
    + etransitivity; tea.
    + todo "".

  - dependent destruction XT using typing_elim.
    erewrite rev_map_firstn_nth_error in XT1, XT2; tea.
    have {na XT1}[na [A₀ [B₀ [XA [XB XT]]]]] :
      ∑ na A₀ B₀, Σ ;;; Γ' ,,, rev_map mkvass (firstn args Δ),, mkvass nA ⊢ A ≤* lift0 1 A₀ ×
      Σ ;;; Γ' ,,, rev_map mkvass (firstn args Δ),, mkvass nA ,, vass na (lift0 1 A₀) ⊢ lift 1 1 B₀ ≤* B ×
      Σ ;;; Γ' ,,, rev_map mkvass (firstn args Δ) ⊢ t : tProd na A₀ B₀.
    1: by todo "".

    edestruct IHX as (Δ' & T' & XU & XΔ & Xr); cbn; tea.
    exists Δ', T'. repeat split; tea.

    { etransitivity; tea.
      subst ty.
      todo "". }

    eapply All2_nth_error_Some_r with (1 := XΔ) in Hnth as (nA' & Hnth' & h).
    econstructor; tea.
    eapply onP in IXz; tea.
    eapply TCI_elim in XT2; tea; tc.
    todo "".
Qed.


Lemma eta_spine_left_retyping_right cf TC Σ P (Pre : EtaRetyping cf TC Σ) Γ Δ t t' args T Γ' Δ' T' :
  [(H : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T)] ->
  [(X : Σ ;;; Γ ⊢ t =η ↑^ t' · args : Π Δ, T on H with P)] ->
  [(onP Γ t t' T H : P Γ t t' T H -> forall Γ' U, Σ ;;; Γ' ⊢ t' : U -> Σ ;;; Γ' ⊢ t =η t' : U)] ->
  Σ ;;; Γ' ⊢ t' : it_mkProd Δ' T' ->
  All2 (fun nA nA' => eq_binder_annot nA.1 nA'.1) Δ' Δ ->
  Σ ;;; Γ' ⊢ t =η ↑^ t' · args : Π Δ', T'.
Proof.
  intros H X onP XT XΔ.
  induction X.
  - cbn in XT.
    constructor.
    eapply onP; tea.
  - eapply All2_nth_error_Some_r with (1 := XΔ) in Hnth as (nA' & Hnth' & h).
    econstructor; tea.
    + etransitivity; tea.
    + todo "".

  - eapply All2_nth_error_Some_r with (1 := XΔ) in Hnth as (nA' & Hnth' & h).
    econstructor; tea.
    eapply onP in IXz; tea.
    todo "".
Qed.








Lemma eta_spine_retyping_left cf TC Σ Γ t t' T U :
  Σ ;;; Γ ⊢ t =η t' : T ->
  Σ ;;; Γ ⊢ t : U ->
  Σ ;;; Γ ⊢ t =η t' : U.
Proof.
  intros X XT.
  induction X in U, XT.
  destruct IH.
  -
  -
  - eapply eta_sprop; revgoals; tea. admit.
  - eapply context_closureεε_fmap in IX. 2: exact (fun _ _ _ _ _ => fst).
    eapply context_closure_ofεε in IX.
    eapply context_closure_retyping in IX as (U₀ & H & H'); tea.
    + now econstructor.
    + auto.
    + intros.
      admit.
Qed.





























Reserved Notation "Σ  ;;; Γ ⊢ t ~ u ~ v : T 'with' R" (at level 50, Γ, t, u, v, T, R at next level).
Inductive context_closure_trans {cf TC} Σ R Γ : forall (t u v T : term), Type :=
  | clos_trans_rel n decl :
      [(wfΓ : wf_local Σ Γ)] ->
      [(hnth : nth_error Γ n = Some decl)] ->
      Σ ;;; Γ ⊢ tRel n ~ tRel n ~ tRel n : lift0 (S n) decl.(decl_type) with R

  | clos_trans_sort s s' s'' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : eq_sort Σ s s')] ->
      [(Xs' : eq_sort Σ s' s'')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' ~ tSort s'' : tSort (Sort.super s'') with R

  | clos_trans_lambda na na' na'' A A' A'' s t t' t'' B :
      [(Xα : eq_binder_annot na na')] ->
      [(Xα' : eq_binder_annot na' na'')] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XA : R Γ A A' A'' (tSort s))] ->
      [(Xt : R (Γ ,, vass na A) t t' t'' B)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' ~ tLambda na'' A'' t'' : tProd na A B with R

  | clos_trans_app na A B f f' f'' a a' a'' :
      [(Xt : R Γ f f' f'' (tProd na A B))] ->
      [(Xu : R Γ a a' a'' A)] ->
      Σ ;;; Γ ⊢ tApp f a ~ tApp f' a' ~ tApp f'' a'' : B {0 := a} with R

  | clos_trans_prod na na' na'' A A' A'' s B B' B'' s' :
      [(Xα : eq_binder_annot na na')] ->
      [(Xα' : eq_binder_annot na' na'')] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XA : R Γ A A' A'' (tSort s))] ->
      [(XT : R (Γ ,, vass na A) B B' B'' (tSort s'))] ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B' ~ tProd na'' A'' B'' : tSort (Sort.sort_of_product s s') with R
where "Σ ;;; Γ ⊢ t ~ u ~ v : T 'with' R" := (context_closure_trans Σ R Γ t u v T).
Derive Signature for context_closure_trans.

Reserved Notation "Σ  ;;; Γ ⊢ t ≤c[ pb ] u ≤c[ pb' ] v : T 'with' R" (at level 50, Γ, pb, pb', t, u, v, R at next level).
Inductive cumul_addon_trans {cf} Σ R Γ pb pb' : forall (t u v T : term), Type :=
  | cumul_trans_sort s s' s'' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(wfs'': wf_sort Σ s'')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      [(Xs' : compare_sort Σ pb' s' s'')] ->
      Σ ;;; Γ ⊢ tSort s ≤c[pb] tSort s' ≤c[pb'] tSort s'' : tSort (Sort.super s'') with R

  | cumul_trans_prod na na' na'' A A' A'' s B B' B'' s' :
      [(Xα : eq_binder_annot na na')] ->
      [(Xα' : eq_binder_annot na' na'')] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XA : R Γ Conv Conv A A' A'' (tSort s))] ->
      [(XT : R (Γ ,, vass na A) pb pb' B B' B'' (tSort s'))] ->
      Σ ;;; Γ ⊢ tProd na A B ≤c[pb] tProd na' A' B' ≤c[pb'] tProd na'' A'' B'' : tSort (Sort.sort_of_product s s') with R
where "Σ ;;; Γ ⊢ t ≤c[ pb ] u ≤c[ pb' ] v : T 'with' R" := (cumul_addon_trans Σ R Γ pb pb' t u v T).
Derive Signature for cumul_addon_trans.



Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ]η u <=[ pb' ]η v : T" (at level 50, Γ, pb, pb', t, u, v, T at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]η  u  <=[ pb' ]η   v  :  T").
Reserved Notation "Σ  ;;; Γ ⊢ t =η u =η v : T" (at level 50, Γ, t, u, v, T at next level).

Reserved Notation "Σ  ;;; Γ ⊢ t =η ↑^ ( u =η v ) · args : 'Π' Δ , T" (at level 50, Γ, Δ, t, u, v, T, args at next level).
Reserved Notation "Σ  ;;; Γ ⊢ ↑^ ( t =η u ) · args =η v : 'Π' Δ , T" (at level 50, Γ, Δ, t, u, v, T, args at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t · args =η u =η v · args' : 'Π' Δ , T" (at level 50, Γ, Δ, t, u, v, T, args, args' at next level).

Section EtaSpineSide.
Context {cf TC} Σ.
Variable R : context -> term -> term -> term -> term -> Type.
Notation "Σ ;;; Γ ⊢ t =η t' =η u : T" := (R Γ t t' u T) (only parsing).

Local Set Elimination Schemes.

Inductive eta_spine_trans_left Γ Δ u v T : forall t args, Type :=
  (* | pred1etar_sprop t' args T₀ :
      P ->
      Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t) (rev_map tRel args) : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ t' : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ _ · args =η t' : T with t, P, P' *)

  | eta_spine_trans_left_ground t :
      Σ ;;; Γ ⊢ t =η u =η v : it_mkProd Δ T ->
      Σ ;;; Γ ⊢ t =η ↑^ (u =η v) · 0 : Π Δ, T

  | eta_spine_trans_left_push na A t args :
      args < #|Δ| ->
      Σ ;;; Γ ⊢ t =η ↑^ (u =η v) · S args : Π Δ, T ->
      Σ ;;; Γ ⊢ tLambda na A t =η ↑^ (u =η v) · args : Π Δ, T

  | eta_spine_trans_left_pop nA t args z :
      nth_error Δ args = Some nA ->
      Σ ;;; Γ ⊢ t =η ↑^ (u =η v) · args : Π Δ, T ->
      Σ ;;; Γ ,,, map mkvass (firstn args Δ) ⊢ z =η tRel 0 : nA.2 ->
      Σ ;;; Γ ⊢ tApp t z =η ↑^ (u =η v) · S args : Π Δ, T
where "Σ ;;; Γ ⊢ t =η ↑^ ( u =η v ) · args : 'Π' Δ , T" := (eta_spine_trans_left Γ Δ u v T t args) (only parsing).

Inductive eta_spine_trans_right Γ Δ t u T : forall v args, Type :=
  (* | pred1etar_sprop t' args T₀ :
      P ->
      Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t) (rev_map tRel args) : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ t' : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ _ · args =η t' : T with t, P, P' *)

  | eta_spine_trans_right_ground v :
      Σ ;;; Γ ⊢ t =η u =η v : it_mkProd Δ T ->
      Σ ;;; Γ ⊢ ↑^ (t =η u) · 0 =η v : Π Δ, T

  | eta_spine_trans_right_push na A v args :
      args < #|Δ| ->
      Σ ;;; Γ ⊢ ↑^ (t =η u) · S args =η v : Π Δ, T ->
      Σ ;;; Γ ⊢ ↑^ (t =η u) · args =η tLambda na A v : Π Δ, T

  | eta_spine_trans_right_pop nA v args z :
      nth_error Δ args = Some nA ->
      Σ ;;; Γ ⊢ ↑^ (t =η u) · args =η v : Π Δ, T ->
      Σ ;;; Γ ,,, map mkvass (firstn args Δ) ⊢ tRel 0 =η z : nA.2 ->
      Σ ;;; Γ ⊢ ↑^ (t =η u) · S args =η tApp v z : Π Δ, T
where "Σ ;;; Γ ⊢ ↑^ ( t =η u ) · args =η v : 'Π' Δ , T" := (eta_spine_trans_right Γ Δ t u T v args) (only parsing).

Inductive eta_spine_trans_mid Γ Δ T : forall t u v args args', Type :=
  (* | pred1etar_sprop t' args T₀ :
      P ->
      Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t) (rev_map tRel args) : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ t' : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ _ · args =η t' : T with t, P, P' *)

  | eta_spine_trans_mid_ground t u v :
      Σ ;;; Γ ⊢ t =η u =η v : it_mkProd Δ T ->
      Σ ;;; Γ ⊢ t · 0 =η u =η v · 0 : Π Δ, T

  | eta_spine_trans_mid_push_both na A t u v args args' :
      args < #|Δ| -> args' < #|Δ| ->
      Σ ;;; Γ ⊢ t · S args =η u =η v · S args' : Π Δ, T ->
      Σ ;;; Γ ⊢ t · args =η tLambda na A u =η v · args' : Π Δ, T

  | eta_spine_trans_mid_push_left na na' A A' s t u v args :
      eq_binder_annot na na' ->
      isSortRel s na.(binder_relevance) ->
      args < #|Δ| ->
      Σ ;;; Γ ,,, map mkvass (firstn args Δ) ⊢ A =η A' : tSort s ->
      Σ ;;; Γ ⊢ t · S args =η u =η v · 0 : Π Δ, T ->
      Σ ;;; Γ ⊢ t · args =η tLambda na A u =η tLambda na' A' v · 0 : Π Δ, T

  | eta_spine_trans_mid_push_right na na' A A' s t u v args :
      eq_binder_annot na na' ->
      isSortRel s na.(binder_relevance) ->
      args < #|Δ| ->
      Σ ;;; Γ ,,, map mkvass (firstn args Δ) ⊢ A =η A' : tSort s ->
      Σ ;;; Γ ⊢ t · 0 =η u =η v · S args : Π Δ, T ->
      Σ ;;; Γ ⊢ tLambda na A t · 0 =η tLambda na' A' u =η v · args : Π Δ, T

  | eta_spine_trans_mid_pop_both nA t u v args args' z :
      nth_error Δ (max args args') = Some nA ->
      Σ ;;; Γ ,,, map mkvass (firstn (max args args') Δ) ⊢ tRel 0 =η z =η tRel 0 : nA.2 ->
      Σ ;;; Γ ⊢ t · args =η u =η v · args' : Π Δ, T ->
      Σ ;;; Γ ⊢ t · S args =η tApp u z =η v · S args' : Π Δ, T

  | eta_spine_trans_mid_pop_left nA t u v args z z' :
      nth_error Δ args = Some nA ->
      Σ ;;; Γ ⊢ t · args =η u =η v · 0 : Π Δ, T ->
      Σ ;;; Γ ,,, map mkvass (firstn args Δ) ⊢ tRel 0 =η z =η z' : nA.2 ->
      Σ ;;; Γ ⊢ t · S args =η tApp u z =η tApp v z' · 0 : Π Δ, T

  | eta_spine_trans_mid_pop_right nA t u v args z z' :
      nth_error Δ args = Some nA ->
      Σ ;;; Γ ,,, map mkvass (firstn args Δ) ⊢ z =η z' =η tRel 0 : nA.2 ->
      Σ ;;; Γ ⊢ t · 0 =η u =η v · args : Π Δ, T ->
      Σ ;;; Γ ⊢ tApp t z · 0 =η tApp u z' =η v · S args : Π Δ, T

where "Σ ;;; Γ ⊢ t · args =η u =η v · args' : 'Π' Δ , T" := (eta_spine_trans_mid Γ Δ T t u v args args') (only parsing).

End EtaSpineSide.

Inductive equality_trans {cf TC} Σ Γ t u v T :=
  (* closure vs closure *)
  | eqtrans_clos T₀ :
      Σ ;;; Γ ⊢ t ~ u ~ v : T₀ with equality_trans Σ ->
      Σ ;;; Γ ⊢ T₀ ≤* T ->
      Σ ;;; Γ ⊢ t =η u =η v : T

  (* sprop *)
  (* | eqtrans_sprop t t' u T₀ T :
      Σ ;;; Γ ⊢ t ≡>1 u : T₀ ->
      Σ ;;; Γ ⊢ t : T ->
      Σ ;;; Γ ⊢ t' : T ->
      Σ ;;; Γ ⊢ T : tSort sSProp ->
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T *)

  (* eta on the left *)
  | eqtrans_etal Δ B :
      Σ ;;; Γ ⊢ t =η ↑^ (u =η v) · 0 : Π Δ, B ->
      Σ ;;; Γ ⊢ it_mkProd Δ B ≤* T ->
      Σ ;;; Γ ⊢ t =η u =η v : T

  (* eta on the right *)
  | eqtrans_etar Δ B :
      Σ ;;; Γ ⊢ ↑^ (t =η u) · 0 =η v : Π Δ, B ->
      Σ ;;; Γ ⊢ it_mkProd Δ B ≤* T ->
      Σ ;;; Γ ⊢ t =η u =η v : T

  (* eta in the middle *)
  | eqtrans_eta_mid Δ B :
      Σ ;;; Γ ⊢ t · 0 =η u =η v · 0 : Π Δ, B ->
      Σ ;;; Γ ⊢ it_mkProd Δ B ≤* T ->
      Σ ;;; Γ ⊢ t =η u =η v : T


where "Σ ;;; Γ ⊢ t =η u =η v : T" := (@equality_trans _ _ Σ Γ t u v T)
and "Σ ;;; Γ ⊢ t =η ↑^ ( u =η v ) · args : 'Π' Δ , T" := (eta_spine_trans_left Σ (equality_trans Σ) Γ Δ u v T t args)
and "Σ ;;; Γ ⊢ ↑^ ( t =η u ) · args =η v : 'Π' Δ , T" := (eta_spine_trans_right Σ (equality_trans Σ) Γ Δ t u T v args)
and "Σ ;;; Γ ⊢ t · args =η u =η v · args' : 'Π' Δ , T" := (eta_spine_trans_mid Σ (equality_trans Σ) Γ Δ T t u v args args').

Inductive equality_pb_trans {cf TC} Σ Γ pb pb' t u v T :=
  (* closure vs closure *)
  | eqpbtrans_eqtrans :
      Σ ;;; Γ ⊢ t =η u =η v : T ->
      Σ ;;; Γ ⊢ t <=[pb]η u <=[pb']η v : T

  | eqpbtrans_cumul_addon T₀ :
      Σ ;;; Γ ⊢ t ≤c[pb] u ≤c[pb'] v : T₀ with equality_pb_trans Σ ->
      Σ ;;; Γ ⊢ T₀ ≤* T ->
      Σ ;;; Γ ⊢ t <=[pb]η u <=[pb']η v : T
where "Σ ;;; Γ ⊢ t <=[ pb ]η u <=[ pb' ]η v : T" := (@equality_pb_trans _ _ Σ Γ pb pb' t u v T).

Derive Signature for equality_trans equality_pb_trans.








Section eta_spine_size.
Context {cf TC Σ}.
Section inner.
Variable (rec : forall Γ t u T, Σ ;;; Γ ⊢ t =η u : T -> nat).
Context {Γ}.


Fixpoint eta_left_spine_size {Δ T t u args} (H : Σ ;;; Γ ⊢ t =η ↑^ u · args : Π Δ, T) : nat.
Proof.
  destruct H.
  all: apply S.
  + by apply rec in X.
  + by apply eta_left_spine_size in H.
  + exact (rec _ _ _ _ Xz + eta_left_spine_size _ _ _ _ _ H).
Defined.

Fixpoint eta_right_spine_size {Δ T t u args} (H : Σ ;;; Γ ⊢ ↑^ t · args =η u : Π Δ, T) : nat.
Proof.
  destruct H.
  all: apply S.
  + by apply rec in X.
  + by apply eta_right_spine_size in H.
  + exact (rec _ _ _ _ Xz + eta_right_spine_size _ _ _ _ _ H).
Defined.

Definition context_closure_size {Rα Rs R} {T t u}
  (recR : forall Γ t u T, R Γ t u T -> nat)
  (H : Σ ;;; Γ ⊢ t ~ u : T with R, Rα, Rs) : nat.
Proof.
  destruct H.
  all: apply S.
  + exact 0.
  + exact (recR _ _ _ _ XA + recR _ _ _ _ Xt).
  + exact (recR _ _ _ _ Xt + recR _ _ _ _ Xu).
  + exact (recR _ _ _ _ XA + recR _ _ _ _ XB).
  + exact 0.
Defined.

(* Definition eq_lambda_nodomain_size {R} {t u}
  (recR : forall Γ t u, R Γ t u -> nat)
  (H : Σ ;;; Γ ⊢ t =λ u with R) : nat.
Proof.
  destruct H.
  apply S.
  exact (recR _ _ _ Xt).
Defined. *)

End inner.

Fixpoint eta_spine_size {Γ t u T} (H : Σ ;;; Γ ⊢ t =η u : T) {struct H} : nat.
Proof.
  destruct H.
  all: apply S.
  - by apply eta_left_spine_size in X.
  - by apply eta_right_spine_size in X.
  (* - by apply eq_lambda_nodomain_size in X. *)
  - exact 0.
  - by apply context_closure_size in X.
Defined.

End eta_spine_size.


Variant eta_spine_pack2 {cf TC} Σ :=
  | RegularRegular Γ t u v T T' (Htu : Σ ;;; Γ ⊢ t =η u : T) (Huv : Σ ;;; Γ ⊢ u =η v : T')
  | LeftRegular Γ Δ B T t u v args (Htu : Σ ;;; Γ ⊢ t =η ↑^ u · args : Π Δ, B) (Huv : Σ ;;; Γ ⊢ u =η v : T)
  | RegularRight Γ Δ T t u v args (Htu : Σ ;;; Γ ⊢ t =η u : it_mkProd Δ T) (Huv : Σ ;;; Γ ⊢ ↑^ u · args =η v : Π Δ, T)
  | RightRegular Γ Δ T t u v args (Htu : Σ ;;; Γ ⊢ ↑^ t · args =η u : Π Δ, T) (Huv : Σ ;;; Γ ,,, map mkvass (firstn args Δ) ⊢ u =η v : it_mkProd (skipn args Δ) T)
  | RegularLeft Γ Δ T t u v args (Htu : Σ ;;; Γ ,,, map mkvass (firstn args Δ) ⊢ t =η u : it_mkProd (skipn args Δ) T) (Huv : Σ ;;; Γ ⊢ u =η ↑^ v · args : Π Δ, T)
  | RightLeft Γ Δ T t u v args args'
    (Htu : Σ ;;; Γ ,,, map mkvass (firstn (max args args' - args) Δ) ⊢ ↑^ t · args =η u : Π skipn (max args args' - args) Δ, T)
    (Huv : Σ ;;; Γ ,,, map mkvass (firstn (max args args' - args') Δ) ⊢ u =η ↑^ v · args' : Π skipn (max args args' - args') Δ, T).

Definition eta_spine_pack_size {cf TC} Σ x :=
  match x with
  | RegularRegular _ _ _ _ _ _ H H' => eta_spine_size H + eta_spine_size H'
  | LeftRegular _ _ _ _ _ _ _ _ H H' => eta_left_spine_size (@eta_spine_size _ _ Σ) H + eta_spine_size H'
  | RegularRight _ _ _ _ _ _ _ H H' => eta_spine_size H + eta_right_spine_size (@eta_spine_size _ _ Σ) H'
  | RightRegular _ _ _ _ _ _ _ H H' => eta_right_spine_size (@eta_spine_size _ _ Σ) H + eta_spine_size H'
  | RegularLeft _ _ _ _ _ _ _ H H' => eta_spine_size H + eta_left_spine_size (@eta_spine_size _ _ Σ) H'
  | RightLeft _ _ _ _ _ _ _ _ H H' => eta_right_spine_size (@eta_spine_size _ _ Σ) H + eta_left_spine_size (@eta_spine_size _ _ Σ) H'
  end.

Notation Goal Σ x :=
  match x return Type with
  | RegularRegular Γ t u v T₀ T₁ _ _ => forall T, Σ ;;; Γ ⊢ T₀ ≤* T -> Σ ;;; Γ ⊢ T₁ ≤* T -> Σ ;;; Γ ⊢ t =η u =η v : T
  | LeftRegular Γ Δ B T t u v args _ _ => Σ ;;; Γ ⊢ it_mkProd Δ B ≤* T -> Σ ;;; Γ ⊢ t =η ↑^ (u =η v) · args : Π Δ, T
  | RegularRight Γ Δ T t u v args _ _ => Σ ;;; Γ ⊢ ↑^ (t =η u) · args =η v : Π Δ, T
  | RightRegular Γ Δ T t u v args _ _ => Σ ;;; Γ ⊢ t · args =η u =η v · 0 : Π Δ, T
  | RegularLeft Γ Δ T t u v args _ _ => Σ ;;; Γ ⊢ t · 0 =η u =η v · args : Π Δ, T
  | RightLeft Γ Δ T t u v args args' _ _ => Σ ;;; Γ ⊢ t · args =η u =η v · args : Π Δ, T
  end.


Lemma eta_spine_left_equality_trans cf TC Σ Γ Δ t u v T args :
  [(X : Σ ;;; Γ ⊢ t =η ↑^ u · args : Π Δ, T)] ->
  [(X' : Σ ;;; Γ ⊢ u =η v : it_mkProd Δ T)] ->
  [(IH Γ t' u' v' T' (Htu' : Σ ;;; Γ ⊢ t' =η u' : T') (Huv' : Σ ;;; Γ ⊢ u' =η v' : T') :
    eta_spine_size Htu' + eta_spine_size Huv' < eta_left_spine_size (@eta_spine_size _ _ Σ) X + eta_spine_size X' ->
    Σ ;;; Γ ⊢ t' =η u' =η v' : T')] ->
  Σ ;;; Γ ⊢ t =η ↑^ (u =η v) · args : Π Δ, T.
Proof.
  intros Htu Huv IH.
  induction Htu.
  (* - eapply eta_spine_trans_left_sprop; tea. *)
  - eapply eta_spine_trans_left_ground; trea.
    unshelve eapply IH; tea. cbn. lia.

  - eapply eta_spine_trans_left_push; trea.
    unshelve eapply IHHtu; tea.
    intros; unshelve eapply IH; tea. cbn. lia.

  - eapply eta_spine_trans_left_pop; trea.
    unshelve eapply IHHtu; tea.
    intros; unshelve eapply IH; tea. cbn. lia.
Qed.

Lemma eta_spine_right_equality_trans cf TC Σ Γ Δ t u v T args :
  [(X : Σ ;;; Γ ⊢ t =η u : it_mkProd Δ T)] ->
  [(X' : Σ ;;; Γ ⊢ ↑^ u · args =η v : Π Δ, T)] ->
  [(IH Γ t' u' v' T' (Htu' : Σ ;;; Γ ⊢ t' =η u' : T') (Huv' : Σ ;;; Γ ⊢ u' =η v' : T') :
    eta_spine_size Htu' + eta_spine_size Huv' < eta_spine_size X + eta_right_spine_size (@eta_spine_size _ _ Σ) X' ->
    Σ ;;; Γ ⊢ t' =η u' =η v' : T')] ->
  Σ ;;; Γ ⊢ ↑^ (t =η u) · args =η v : Π Δ, T.
Proof.
  intros Htu Huv IH.
  induction Huv.
  (* - eapply eta_spine_trans_left_sprop; tea. *)
  - eapply eta_spine_trans_right_ground; trea.
    unshelve eapply IH; tea. cbn. lia.

  - eapply eta_spine_trans_right_push; trea.
    unshelve eapply IHHuv; tea.
    intros; unshelve eapply IH; tea. cbn. lia.

  - eapply eta_spine_trans_right_pop; trea.
    unshelve eapply IHHuv; tea.
    intros; unshelve eapply IH; tea. cbn. lia.
Qed.


Lemma eta_spine_closure_equality_trans cf TC Σ Γ t u v T₀ T :
  [(X : Σ ;;; Γ ⊢ t ~ u : T₀ with eta_spine Σ, eq_binder_annot, eq_sort Σ)] ->
  [(X' : Σ ;;; Γ ⊢ u ~ v : T with eta_spine Σ, eq_binder_annot, eq_sort Σ)] ->
  [(IH Γ t' u' v' T' (Htu' : Σ ;;; Γ ⊢ t' =η u' : T') (Huv' : Σ ;;; Γ ⊢ u' =η v' : T') :
    eta_spine_size Htu' + eta_spine_size Huv' <
    context_closure_size (@eta_spine_size _ _ Σ) X + context_closure_size (@eta_spine_size _ _ Σ) X' ->
    Σ ;;; Γ ⊢ t' =η u' =η v' : T')] ->
  Σ ;;; Γ ⊢ t ~ u ~ v : T with equality_trans Σ.
Proof.
  (* intros Htu Huv IH.
  destruct Htu; depelim Huv.
  - by constructor.
  - epose proof (eta_spine_change_context_size (Γ ,, vass na A) Xt0) as (Xt0' & e).
    econstructor; tea.
    all: unshelve eapply IH; tea.
    all: cbn; lia.
  - econstructor; tea.
    all: unshelve eapply IH; tea.
    all: cbn; lia.
  - epose proof (eta_spine_change_context_size (Γ ,, vass na A) XB0) as (XB0' & e).
    econstructor; tea.
    all: unshelve eapply IH; tea.
    all: cbn; lia.
  - by constructor. *)
Qed.


Lemma case_regular_regular cf TC Σ Γ t u v T₀ T₁ T :
  [(Htu : Σ ;;; Γ ⊢ t =η u : T₀)] ->
  [(Huv : Σ ;;; Γ ⊢ u =η v : T₁)] ->
  [(XT₀ : Σ ;;; Γ ⊢ T₀ ≤* T)] ->
  [(XT₁ : Σ ;;; Γ ⊢ T₁ ≤* T)] ->
  [(IH x : eta_spine_pack_size Σ x < eta_spine_size Htu + eta_spine_size Huv -> Goal Σ x)] ->
  Σ ;;; Γ ⊢ t =η u =η v : T.
Proof.
  intros.
  destruct Htu.
  - eapply TCI_trans in XT₀; tea.
    eapply eqtrans_etal; tea.
    unshelve eapply (IH ltac:(eapply LeftRegular)).
    cbn. lia.

  - destruct Huv.
    + apply eqtrans_eta_mid.
      unshelve epose (x := RightLeft Σ Γ [] [] [] [] t u v [] [] eq_refl _ _); tea.
      specialize (IH x).
      cbn in IH.
      forward IH by lia.
      rewrite !lift0_id // in IH.

    + apply eqtrans_etar.
      unshelve eapply (IH ltac:(eapply RegularRight)); tea.
      1: now econstructor.
      cbn. lia.

    + apply eqtrans_eta_mid.
      unshelve epose (x := RightRegular Σ Γ [] t u v [] _ _); tea.
      1: now econstructor.
      specialize (IH x).
      cbn in IH.
      forward IH by lia.
      rewrite !lift0_id // in IH.

    + apply eqtrans_eta_mid.
      unshelve epose (x := RightRegular Σ Γ [] t u v [] _ _); tea.
      1: now econstructor.
      specialize (IH x).
      cbn in IH.
      forward IH by lia.
      rewrite !lift0_id // in IH.

  - destruct Huv.
    + apply eqtrans_eta_mid.
      unshelve epose (x := RegularLeft Σ Γ [] t u v [] _ _); tea.
      1: now econstructor.
      specialize (IH x).
      cbn in IH.
      forward IH by lia.
      rewrite !lift0_id // in IH.

    + apply eqtrans_etar.
      unshelve eapply (IH ltac:(eapply RegularRight)); tea.
      1: now econstructor.
      cbn. lia.

    + destruct X. depelim X0.
      epose proof (eta_spine_change_context_size (Γ ,, vass na A) Xt0) as (Xt0' & e).
      apply eqtrans_clos, clos_tri_lambda; tea.
      unshelve epose (x := RegularRegular Σ (Γ ,, vass na A) t t' t'0 _ _); tea.
      specialize (IH x).
      cbn in IH.
      by forward IH by lia.

    + destruct X. depelim X0.
      epose proof (eta_spine_change_context_size (Γ ,, vass na A) Xt0) as (Xt0' & e).
      apply eqtrans_clos, clos_tri_lambda; tea.
      unshelve epose (x := RegularRegular Σ (Γ ,, vass na A) t t' t'0 _ _); tea.
      specialize (IH x).
      cbn in IH.
      by forward IH by lia.

  - destruct Huv.
    + apply eqtrans_eta_mid.
      unshelve epose (x := RegularLeft Σ Γ [] t u v [] _ _); tea.
      1: now econstructor.
      specialize (IH x).
      cbn in IH.
      forward IH by lia.
      rewrite !lift0_id // in IH.

    + apply eqtrans_etar.
      unshelve eapply (IH ltac:(eapply RegularRight)); tea.
      1: now econstructor.
      cbn. lia.

    + destruct X0. depelim X.
      epose proof (eta_spine_change_context_size (Γ ,, vass na0 A0) Xt0) as (Xt0' & e).
      apply eqtrans_clos, clos_tri_lambda; tea.
      unshelve epose (x := RegularRegular Σ (Γ ,, vass na0 A0) t1 t0 t' _ _); tea.
      specialize (IH x).
      cbn in IH.
      by forward IH by lia.

    + apply eqtrans_clos.
      unshelve eapply eta_spine_closure_equality_trans; tea.
      intros ???? Htu' Huv' ?.
      unshelve epose (x := RegularRegular Σ _ _ _ _ Htu' Huv'); tea.
      specialize (IH x).
      cbn in IH.
      by forward IH by lia.
Qed.

Lemma case_right_regular cf Σ Γ Γ' t u v args :
  [(Htu : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η u)] ->
  [(Huv : Σ ;;; Γ ,,, Γ' ⊢ u =η v)] ->
  [(IH x : eta_spine_pack_size Σ x < eta_right_spine_size (@eta_spine_size cf Σ) Htu + eta_spine_size Huv -> Goal Σ x)] ->
  Σ ;;; Γ ;;; Γ' ⊢ lift0 #|Γ'| t · args =η u =η v · [].
Proof.
  intros.
  destruct Htu.
  - apply eta_spine_trans_mid_ground.
    unshelve epose (x := RegularRegular Σ _ _ t' v _ _); revgoals; tea.
    specialize (IH x).
    cbn in IH.
    by forward IH by lia.
  - apply eta_spine_trans_mid_push_left.
    unshelve epose (x := RegularRegular Σ _ _ t' v _ _); revgoals; tea.
    specialize (IH x).
    cbn in IH.
    by forward IH by lia.
  -


Theorem eq_trans_equality_trans cf Σ Γ t u v :
  Σ ;;; Γ ⊢ t =η u ->
  Σ ;;; Γ ⊢ u =η v ->
  Σ ;;; Γ ⊢ t =η u =η v.
Proof.
  intros Htu Huv.
  set (Htuv := RegularRegular _ _ _ _ _ Htu Huv).
  change _ with (Goal Σ Htuv). clearbody Htuv.
  clear Γ t u v Htu Huv.
  eassert (e : Acc _ Htuv).
  { apply wf_precompose with (m := eta_spine_pack_size Σ), lt_wf. }
  induction e using Fix_F. rename X into IH.
  destruct x; cbn in IH.
  - by unshelve eapply case_regular_regular.
  - unshelve eapply eta_spine_left_equality_trans; tea.
    intros ???? Htu' Huv' ?.
    unshelve epose (x := RegularRegular Σ _ _ _ _ Htu' Huv'); tea.
    specialize (IH x).
    cbn in IH.
    by forward IH by lia.
  - unshelve eapply eta_spine_right_equality_trans; tea.
    intros ???? Htu' Huv' ?.
    unshelve epose (x := RegularRegular Σ _ _ _ _ Htu' Huv'); tea.
    specialize (IH x).
    cbn in IH.
    by forward IH by lia.
  - by unshelve eapply case_right_regular.
  - by unshelve eapply case_regular_left.
  - by unshelve eapply case_right_left.
Qed.











































































Definition lift1_app_rel0 t := tApp (lift0 1 t) (tRel 0).

Lemma eta_left_invert cf TC Σ
  (rec : forall Γ t t' T, Σ ;;; Γ ⊢ t <=[Conv] t' : T -> Σ ;;; Γ ⊢ t =η t' : T)
  Γ Δ Δ' t u T args B :
  Σ ;;; Γ ,,, map mkvass Δ ⊢ t <=[Conv] iter_nat args _ lift1_app_rel0 u : T ->
  Σ ;;; Γ ,,, map mkvass Δ ⊢ T ≤* it_mkProd Δ' B ->
  Σ ;;; Γ ⊢ t =η ↑^ u · args : Π (Δ ++ Δ'), B.
Proof.
  intros Xe XT.
  remember (iter_nat args _ lift1_app_rel0 u) as u₀ eqn:eu. cbn in u₀.
  remember (Γ ,,, map mkvass Δ) as ΓΔ eqn:eΓ.
  induction Xe in Δ, Δ', u, args, B, eu, eΓ, XT.
  1: destruct IX; subst.
  + eapply etal_push; trea.

    eapply IXR; trea.
    1: by apply H10.
    rewrite rev_map_cons mkApps_app /=. f_equal.
    rewrite lift_mkApps. f_equal.
    * rewrite simpl_lift //; lia.
    * by rewrite !rev_map_spec map_rev !map_map //=.
  + destruct args => /=. 1: by apply H00.
    rewrite /= rev_map_cons mkApps_app // in eu.
  + eapply etal_sprop; trea.
  + destruct args => /=. 1: by apply H00.
    rewrite /= rev_map_cons mkApps_app /= in eu.
    by destruct X => //.
  + subst Γ0 u0. eapply eta_left_spine_cumul; eauto.
  + destruct args => /=. 1: by apply H00.
    rewrite /= rev_map_cons mkApps_app /= in eu.
    destruct X => //.
    apply rec in Xt as Xt', Xu as Xu'. clear rec.
    injection eu as [= -> ->]. subst Γ0.
    eapply etal_pop with (na := na); trea.
    destruct args.
    * eapply etal_ground, Xt'.
    * inversion IX; subst.
      eapply IXt; trea.
      apply H10.
Defined.


Lemma eta_right_invert cf TC Σ
  (rec : forall Γ t t' T, Σ ;;; Γ ⊢ t <=[Conv] t' : T -> Σ ;;; Γ ⊢ t =η t' : T)
  Γ Γ' t u T args :
  #|args| > 0 ->
  Σ ;;; Γ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t) (rev_map tRel args) <=[Conv] u : T ->
  Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η u : T.
Proof.
  assert (H10 : forall n, S n > 0) by auto with arith.
  assert (H00 : forall A, 0 > 0 -> A) by lia.

  remember (mkApps _ _) as t₀ eqn:et.
  remember (Γ ,,, Γ') as ΓΓ' eqn:eΓ.
  intros Hlen Xe.
  induction Xe in Γ', t, args, et, eΓ, Hlen; rename Γ0 into ΓΓ', t0 into t₀.
  1: destruct IX; subst.
  - destruct args => /=. 1: by apply H00.
    by rewrite /= rev_map_cons mkApps_app // in et.
  - eapply etar_push; trea.
    eapply IXR; revgoals; trea.
    + by apply H10.
    + rewrite rev_map_cons mkApps_app /=. f_equal.
      rewrite lift_mkApps. f_equal.
      * rewrite simpl_lift //; lia.
      * by rewrite !rev_map_spec map_rev !map_map //=.
  - eapply etar_sprop; trea.
  - destruct args => /=. 1: by apply H00.
    rewrite /= rev_map_cons mkApps_app /= in et.
    by destruct X.
  - subst ΓΓ' t₀.
    eapply eta_right_spine_cumul; eauto.
  - destruct args => /=. 1: by apply H00.
    rewrite /= rev_map_cons mkApps_app /= in et.
    destruct X => //.
    apply rec in Xt as Xt', Xu as Xu'. clear rec.
    injection et as [= -> ->]. subst ΓΓ'.
    eapply etar_pop with (na := na); trea.
    destruct args.
    * eapply etar_ground, Xt'.
    * inversion IX; subst.
      eapply IXt; trea.
      apply H10.
Defined.

Lemma eta_invert cf TC Σ Γ t t' T :
  Σ ;;; Γ ⊢ t <=[Conv] t' : T ->
  Σ ;;; Γ ⊢ t =η t' : T.
Proof.
  revert Γ t t' T.
  fix rec 5.
  destruct 1.
  1: destruct X.
  - eapply eta_left.
    eapply etal_push; trea.
    apply eta_left_invert; tas.
    1: cbn; auto with arith.

  - apply eta_right.
    eapply etar_push; trea.
    apply eta_right_invert; tas.
    1: cbn; auto with arith.

  - eapply eta_sprop; trea.
  - eapply eta_clos; trea.
    now eapply cumul_addon_clos_fmap in X.
  - now eapply eta_spine_cumul.
  - eapply eta_clos; trea.
    eapply context_closure_fmap; eauto.
Qed.

Lemma eta_pb_invert cf TC Σ Γ pb t t' T :
  Σ ;;; Γ ⊢ t <=[pb] t' : T ->
  Σ ;;; Γ ⊢ t <=[pb]η t' : T.
Proof.
  induction 1.
  - constructor. apply eta_invert. now constructor.
  - econstructor 2; trea.
    eauto with fmap.
  - now eapply tc_compat.
  - constructor. apply eta_invert. now constructor.
Qed.


Definition max_pb pb pb' := match pb with Cumul => Cumul | Conv => pb' end.
Lemma max_pb_left R :
  [(X pb t u T : R Conv t u T -> R pb t u T)] ->
  forall pb pb' (t u T : term), R pb t u T -> R (max_pb pb pb') t u T.
Proof. intros X [][] ???; eauto. Qed.
Lemma max_pb_right R :
  [(X pb t u T : R Conv t u T -> R pb t u T)] ->
  forall pb pb' (t u T : term), R pb' t u T -> R (max_pb pb pb') t u T.
Proof. intros X [][] ???; eauto. Qed.
Lemma max_pb_left' R :
  [(X pb t u : R Conv t u -> R pb t u)] ->
  forall pb pb' (t u : sort), R pb t u -> R (max_pb pb pb') t u.
Proof. intros X [][] ???; eauto. Qed.
Lemma max_pb_right' R :
  [(X pb t u : R Conv t u -> R pb t u)] ->
  forall pb pb' (t u : sort), R pb' t u -> R (max_pb pb pb') t u.
Proof. intros X [][] ???; eauto. Qed.



Theorem eta_spine_trans cf TC Σ Γ t u v T :
  Σ ;;; Γ ⊢ t =η u : T ->
  Σ ;;; Γ ⊢ u =η v : T ->
  Σ ;;; Γ ⊢ t =η v : T.
Proof.
  intros Htu Huv.
  induction Htu in v, Huv |- *.
  destruct X.
  -
  -
  - admit.
  -
Qed.



Theorem eta_spine_pb_trans cf TC Σ Γ pb pb' t u v TA TB T :
  Σ ;;; Γ ⊢ TA ≤* T ->
  Σ ;;; Γ ⊢ TB ≤* T ->
  Σ ;;; Γ ⊢ t <=[pb]η u : TA ->
  Σ ;;; Γ ⊢ u <=[pb']η v : TB ->
  Σ ;;; Γ ⊢ t <=[max_pb pb pb']η v : T.
Proof.
  intros HTA HTB Htu Huv.
  induction Htu in pb', v, Huv, T, HTA, HTB |- *; rename t' into u, T0 into TA.
  1: induction Huv; rename t0 into u, t' into v, T0 into TB.
  3: destruct Huv.
  - constructor.
    now eapply eta_spine_trans.
  - admit.
  - admit.
  - admit.
Qed.


Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' | ≡>1 u : T" (at level 50, Γ, t, pb, t', u, T at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]η  t'  |  ≡>1  u  :  T").
Reserved Notation "Σ  ;;; Γ ⊢ t =η t' | ≡>1 u : T" (at level 50, Γ, t, t', u, T at next level).
Reserved Notation "Σ ;;; Γ ⊢ 'λ(' na : A ) , t =η t' | ≡>1 u : T" (at level 50, Γ, na, A, t, t', u, T at next level, format "Σ  ;;;  Γ  ⊢  'λ(' na  :  A ) ,  t  =η  t'  |  ≡>1  u  :  T").
Reserved Notation "Σ  ;;; Γ  ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T | T'" (at level 50, Γ, Γ', t, t', args, u, T at next level).
Reserved Notation "Σ ;;; Γ ;;; Γ' ⊢ 'λ(' na : A ) , t =η ↑^ t' · args | ≡>1 u : T | T'" (at level 50, Γ, Γ', na, A, t, t', args, u, T, T' at next level, format "Σ  ;;;  Γ  ;;;  Γ'  ⊢  'λ(' na  :  A ) ,  t  =η  ↑^  t'  ·  args  |  ≡>1  u  :  T  |  T'").
Reserved Notation "Σ  ;;; Γ  ;;; Γ' ⊢ ↑^ t · args =η t' | ≡>1 u : T" (at level 50, Γ, Γ', t, t', args, u, T at next level).
Reserved Notation "Σ ;;; Γ ;;; Γ' ⊢ '↑^(' 'λ(' na : A ) , t ) · args =η t' | ≡>1 u : T" (at level 50, Γ, Γ', na, A, t, t', u, T at next level, format "Σ  ;;;  Γ  ;;;  Γ'  ⊢  '↑^(' 'λ(' na  :  A ) ,  t )  ·  args  =η  t'  |  ≡>1  u  :  T").

Section Pred1EtaL.
Context {cf TC} Σ.
Variable R : context -> term -> term -> term -> term -> Type.
Variable Ru : context -> aname -> term -> term -> term -> term -> term -> Type.
Notation "Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T" := (R Γ t t' u T) (only parsing).
Notation "Σ ;;; Γ ⊢ 'λ(' na : A ) , t =η t' | ≡>1 u : T" := (Ru Γ na A t u T t') (only parsing).
Local Set Elimination Schemes.

Section Under.
Variable rec : context -> term -> context -> term -> term -> term -> list nat -> term -> Type.
Notation "Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T | T'" := (rec Γ T' Γ' t' T t args u) (only parsing).
Inductive pred1_etal_spine_under Γ T' Γ' na A t t' u T : forall args, Type :=
  | pred1etal_under_sprop args T₀ T₀' :
      Σ ;;; Γ ,,, Γ' ,, vass na A ⊢ t ≡>1 u : T₀' ->
      Σ ;;; Γ ⊢ t' : T' ->
      Σ ;;; Γ ,,, Γ' ⊢ tLambda na A t : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t') (rev_map tRel args) : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T | T'

  | pred1etal_under_push args B :
      Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ t =η ↑^ t' · map S args ,, 0 | ≡>1 u : B | T' ->
      Σ ;;; Γ ,,, Γ' ⊢ tProd na A B ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T | T'

  | pred1etal_under_ground T₀ :
      Σ ;;; Γ ,,, Γ' ⊢ λ(na : A), t =η lift0 #|Γ'| t' | ≡>1 u : T₀ ->
      Σ ;;; Γ ⊢ t' : T' ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · [] | ≡>1 u : T | T'

where "Σ ;;; Γ ;;; Γ' ⊢ 'λ(' na : A ) , t =η ↑^ t' · args | ≡>1 u : T | T'" := (pred1_etal_spine_under Γ T' Γ' na A t t' u T args) (only parsing).
End Under.

Inductive pred1_etal_spine Γ T' Γ' t' T : forall t args u, Type :=
  | pred1etal_sprop t args u T₀ T₀' :
      Σ ;;; Γ ,,, Γ' ⊢ t ≡>1 u : T₀' ->
      Σ ;;; Γ ⊢ t' : T' ->
      Σ ;;; Γ ,,, Γ' ⊢ t : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t') (rev_map tRel args) : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T | T'

  | pred1etal_ground t u :
      Σ ;;; Γ ,,, Γ' ⊢ t =η lift0 #|Γ'| t' | ≡>1 u : T ->
      Σ ;;; Γ ⊢ t' : T' ->
      Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · [] | ≡>1 u : T | T'

  | pred1etal_push na A B s T₀ t u args :
      Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ t =η ↑^ t' · map S args ,, 0 | ≡>1 u : T₀ | T' ->
      Σ ;;; Γ ,,, Γ' ⊢ A ≡>1 B : tSort s ->
      Σ ;;; Γ ,,, Γ' ⊢ tProd na A T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ tLambda na A t =η ↑^ t' · args | ≡>1 tLambda na B u : T | T'

  | pred1etal_pop_clos na A B t u args n n' n'' :
      Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : tProd na A B | T' ->
      Σ ;;; Γ ,,, Γ' ⊢ n' =η tRel n | ≡>1 n'' : A ->
      Σ ;;; Γ ,,, Γ' ⊢ B {0 := n'} ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ tApp t n' =η ↑^ t' · args ,, n | ≡>1 tApp u n'' : T | T'

  | pred1etal_pop_beta na A B t u args n n' n'' :
      Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : tProd na A B | T' ->
      Σ ;;; Γ ,,, Γ' ⊢ n' =η tRel n | ≡>1 n'' : A ->
      Σ ;;; Γ ,,, Γ' ⊢ B {0 := n'} ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ tApp (tLambda na A t) n' =η ↑^ t' · args ,, n | ≡>1 u {0 := n''} : T | T'

where "Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T | T'" := (pred1_etal_spine Γ T' Γ' t' T t args u) (only parsing)
and "Σ ;;; Γ ;;; Γ' ⊢ 'λ(' na : A ) , t =η ↑^ t' · args | ≡>1 u : T | T'" := (pred1_etal_spine_under pred1_etal_spine Γ T' Γ' na A t t' u T args) (only parsing).

End Pred1EtaL.



Section Pred1EtaR.
Context {cf TC} Σ.
Variable R : context -> term -> term -> term -> term -> Type.
Variable Ru : context -> aname -> term -> term -> term -> term -> term -> Type.
Notation "Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T" := (R Γ t t' u T) (only parsing).
Notation "Σ ;;; Γ ⊢ 'λ(' na : A ) , t =η t' | ≡>1 u : T" := (Ru Γ na A t u T t') (only parsing).
Local Set Elimination Schemes.

Reserved Notation "Σ  ;;; Γ  ;;; Γ' ⊢ ↑^ '_' · args =η t' : T 'with' t , P , P'" (at level 50, Γ, Γ', args, t', T, t, P, P' at next level).

Inductive modular_etar_spine P P' t Γ Γ' T : forall t' args, Type :=
  | pred1etar_sprop t' args T₀ :
      P ->
      Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t) (rev_map tRel args) : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ t' : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ _ · args =η t' : T with t, P, P'

  | pred1etar_ground t' T₀ :
      P' Γ' t' T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ _ · [] =η t' : T with t, P, P'

  | pred1etar_push t' args na A T₀ :
      Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ ↑^ _ · map S args ,, 0 =η t' : T₀ with t, P, P' ->
      lift_typing typing Σ (Γ ,,, Γ') (j_vass na A) ->
      Σ ;;; Γ ,,, Γ' ⊢ tProd na A T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ _ · args =η tLambda na A t' : T with t, P, P'

  | pred1etar_pop t' args na A B n n' :
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ _ · args =η t' : tProd na A B with t, P, P' ->
      Σ ;;; Γ ,,, Γ' ⊢ tRel n =η n' : A ->
      Σ ;;; Γ ,,, Γ' ⊢ B {0 := tRel n} ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ _ · args ,, n =η tApp t' n' : T with t, P, P'
where "Σ ;;; Γ ;;; Γ' ⊢ ↑^ '_' · args =η t' : T 'with' t , P , P'" := (modular_etar_spine P P' t Γ Γ' T t' args) (only parsing).

Definition pred1_etar_spine Γ Γ' t t' u args T :=
  modular_etar_spine
    (∑ T₀, Σ ;;; Γ ⊢ t ≡>1 u : T₀)
    (fun Γ' t' T₀ => Σ ;;; Γ ,,, Γ' ⊢ lift0 #|Γ'| t =η t' | ≡>1 lift0 #|Γ'| u : T₀)
    t Γ Γ' T t' args.

Definition pred1_etar_spine_under Γ Γ' na A t t' u args T :=
  modular_etar_spine
    (∑ T₀, Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀)
    (fun Γ' t' T₀ => Σ ;;; Γ ,,, Γ' ⊢ λ(na : lift0 #|Γ'| A), lift #|Γ'| 1 t =η t' | ≡>1 lift #|Γ'| 1 u : T₀)
    (tLambda na A t)
    Γ Γ' T t' args.

Notation "Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' | ≡>1 u : T" := (pred1_etar_spine Γ Γ' t t' u args T) (only parsing).
Notation "Σ ;;; Γ ;;; Γ' ⊢ '↑^(' 'λ(' na : A ) , t ) · args =η t' | ≡>1 u : T" := (pred1_etar_spine_under Γ Γ' na A t t' u args T) (only parsing).

End Pred1EtaR.

Section Pred1EqLam.
Context {cf TC} Σ.
Variable R : context -> term -> term -> term -> term -> Type.
Notation "Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T" := (R Γ t t' u T) (only parsing).

Local Set Elimination Schemes.

Inductive pred1_eq_spine_under Γ na A t u T : forall t', Type :=
  | pred1eq_lam_etar t' :
      Σ ;;; Γ ;;; [] ⊢ ↑^(λ(na : A), t) · [] =η t' | ≡>1 u : T ->
      Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T

  | pred1eq_lam_etal t' T' :
      Σ ;;; Γ ;;; [] ⊢ λ(na : A), t =η ↑^ t' · [] | ≡>1 u : T | T' ->
      Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T

  | pred1eq_lam_ground s na' A' t' B :
      eq_binder_annot na na' ->
      isSortRel s (binder_relevance na) ->
      Σ ;;; Γ ⊢ A =η A' : tSort s ->
      Σ ;;; Γ ,, vass na A ⊢ t =η t' | ≡>1 u : B ->
      Σ ;;; Γ ⊢ tProd na A B ≤* T ->
      Σ ;;; Γ ⊢ λ(na : A), t =η tLambda na' A' t' | ≡>1 u : T

where "Σ ;;; Γ ⊢ 'λ(' na : A ) , t =η t' | ≡>1 u : T" := (pred1_eq_spine_under Γ na A t u T t') (only parsing)
and "Σ ;;; Γ ;;; Γ' ⊢ 'λ(' na : A ) , t =η ↑^ t' · args | ≡>1 u : T | T'" := (pred1_etal_spine_under Σ pred1_eq_spine_under (pred1_etal_spine Σ R pred1_eq_spine_under) Γ T' Γ' na A t t' u T args) (only parsing)
and "Σ ;;; Γ ;;; Γ' ⊢ '↑^(' 'λ(' na : A ) , t ) · args =η t' | ≡>1 u : T" := (pred1_etar_spine_under Σ pred1_eq_spine_under Γ Γ' na A t t' u args T) (only parsing).

End Pred1EqLam.

Inductive pred1_equality {cf TC} Σ Γ : forall (t t' u T : term), Type :=
  (* Inconsequent *)
  | pred1eq_cumul t t' u T T' :
      Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T ->
      Σ ;;; Γ ⊢ T ≤T T' ->
      Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T'

  (* closure vs closure *)
  | pred1eq_clos t t' u T :
      context_closure_tri Σ (fun Γ => pred1_equality Σ Γ) Γ t t' u T ->
      Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T
  (* sprop *)
  | pred1eq_sprop t t' u T₀ T :
      Σ ;;; Γ ⊢ t ≡>1 u : T₀ ->
      Σ ;;; Γ ⊢ t : T ->
      Σ ;;; Γ ⊢ t' : T ->
      Σ ;;; Γ ⊢ T : tSort sSProp ->
      Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T

  (* eta on the right *)
  | pred1eq_etar t t' u T :
      Σ ;;; Γ ;;; [] ⊢ ↑^ t · [] =η t' | ≡>1 u : T ->
      Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T

  (* eta on the left *)
  | pred1eq_etal t t' u T :
      Σ ;;; Γ ;;; [] ⊢ t =η ↑^t' · [] | ≡>1 u : T | T ->
      Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T

  (* beta vs clos for app *)
  | pred1eq_beta_clos na A t t' u a a' b B :
      Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : tProd na A B ->
      Σ ;;; Γ ⊢ a =η a' | ≡>1 b : A ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) a =η tApp t' a' | ≡>1 u {0 := b} : B {0 := a}

where "Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T" := (@pred1_equality _ _ Σ Γ t t' u T)
and "Σ ;;; Γ ⊢ 'λ(' na : A ) , t =η t' | ≡>1 u : T" := (pred1_eq_spine_under Σ (pred1_equality Σ) Γ na A t u T t')
and "Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T | T'" := (pred1_etal_spine Σ (pred1_equality Σ) (pred1_eq_spine_under Σ (pred1_equality Σ)) Γ T' Γ' t' T t args u)
and "Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' | ≡>1 u : T" := (pred1_etar_spine Σ (pred1_equality Σ) Γ Γ' t t' u args T).

Inductive pred1_equality_pb {cf TC} Σ Γ (pb : conv_pb) (t t' u : term) : forall (T : term), Type :=
  (* Inconsequent *)
  | pred1eqpb_cumul T T' :
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T ->
      Σ ;;; Γ ⊢ T ≤T T' ->
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T'

  | pred1eqpb_pred1eq T :
      Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T

  | pred1eqpb_cumul_addon T :
      cumul_addon_tri Σ (pred1_equality_pb Σ) Γ pb t t' u T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T
where "Σ ;;; Γ ⊢ t <=[ pb ]η t' | ≡>1 u : T" := (@pred1_equality_pb _ _ Σ Γ pb t t' u T).

Notation "Σ ;;; Γ ;;; Γ' ⊢ 'λ(' na : A ) , t =η ↑^ t' · args | ≡>1 u : T | T'" := (pred1_etal_spine_under Σ (pred1_eq_spine_under Σ (pred1_equality Σ)) (pred1_etal_spine Σ (pred1_equality Σ) (pred1_eq_spine_under Σ (pred1_equality Σ))) Γ T' Γ' na A t t' u T args).
Notation "Σ ;;; Γ ;;; Γ' ⊢ '↑^(' 'λ(' na : A ) , t ) · args =η t' | ≡>1 u : T" := (pred1_etar_spine_under Σ (pred1_eq_spine_under Σ (pred1_equality Σ)) Γ Γ' na A t t' u args T).

Derive Signature for pred1_equality.

Instance TC_compat_pred1_equality cf TC Σ Γ t t' u : TC_compat TC Σ Γ (pred1_equality Σ Γ t t' u). by now econstructor. Defined.
Instance TC_compat_pred1_equality_pb cf TC Σ Γ pb t t' u : TC_compat TC Σ Γ (pred1_equality_pb Σ Γ pb t t' u). by now econstructor. Defined.
Instance TC_compat_pred1_etal_spine_under cf TC Σ Γ T' Γ' na A t t' args u : TC_compat TC Σ (Γ ,,, Γ') (fun T => Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T | T').
Proof.
  intros ???[]; now econstructor; tea; eapply TCI_rstep; tea.
Defined.
Instance TC_compat_pred1_etar_spine_under cf TC Σ Γ Γ' na A t t' args u : TC_compat TC Σ (Γ ,,, Γ') (fun T => Σ ;;; Γ ;;; Γ' ⊢ ↑^(λ(na : A), t) · args =η t' | ≡>1 u : T).
Proof.
  intros ???[]; now econstructor; tea; eapply TCI_rstep; tea.
Defined.
Instance TC_compat_pred1_eq_spine_under cf TC Σ Γ na A t t' u : TC_compat TC Σ Γ (fun T => Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T).
Proof.
  intros ??? [].
  - constructor; now eapply TC_compat_pred1_etar_spine_under.
  - econstructor; now eapply TC_compat_pred1_etal_spine_under.
  - econstructor; eauto; now eapply TCI_rstep.
Defined.


Lemma etal_left_typing cf TC Σ Γ Γ' t t' args T : Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^t' · args : T -> Σ ;;; Γ ,,, Γ' ⊢ t : T.
Proof.
  induction 1.
  - eapply TCI_elim; tc; tea.
  -
  - eapply TCI_elim; tc; tea.
    constructor; tas.
  - eapply TCI_elim; tc; tea.
    econstructor; tea.
Abort.

Lemma eta_spine_left_pred1_equality cf TC Σ Γ Γ' t t' u args T T' T₀ :
  let P Γ t t' T :=
    match t with tLambda na A t =>
      forall u T₀, Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T
    | _ => True
    end ×
    forall u T₀, Σ ;;; Γ ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T
  in
  [(Xt' : Σ ;;; Γ ⊢ t' : T')] ->
  [(X : Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args : T)] ->
  [(IX : Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args : T on X with
    fun Γ t t' T H => P Γ t t' T × eta_spineε Σ P Γ t t' T H)] ->
  match t with tLambda na A t =>
  [(Xp : Σ ;;; Γ ,,, Γ' ,, vass na A ⊢ t ≡>1 u : T₀)] ->
    Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T | T'
  | _ => True
  end ×
  ([(Xp : Σ ;;; Γ ,,, Γ' ⊢ t ≡>1 u : T₀)] ->
    Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T | T').
Proof.
  intros * ? * IX.
  induction IX in u, T₀, Xt', T'.
  3,4: split => //; intro Xp.
  1,2: split; [destruct t => //|]; intro Xp.
  - eapply pred1etal_under_sprop; tea.
  - eapply pred1etal_sprop; tea.
  - eapply pred1etal_under_ground; trea.
    now eapply IXR.
  - apply pred1etal_ground; tas.
    eapply IXR; tea.
  - eapply pred1etal_under_push; trea.
    1: now eapply IHIX.
  - destruct Xp using pred1_elim.
    1: by depelim X0.
    depelim X0. subst na'.
    eapply pred1etal_push; tea.
    now eapply IHIX.
  - destruct Xp using pred1_elim.
    + depelim X0.
      eapply fst in IHIX; tea.
      forward IHIX by tea.
      apply fst, snd in IXn.
      specialize (IXn _ _ p0).
      have XA : Σ ;;; Γ ,,, Γ' ⊢ A ≤* A0 by admit.
      eapply TCI_elim in IXn; tc; tea.
      have XB : Σ ;;; Γ ,,, Γ' ⊢ tProd na A B ≤* tProd na0 A0 B by admit.
      eapply pred1etal_pop_beta; tea.
      eapply TCI_elim with (1 := ltac:(apply TC_compat_pred1_etal_spine_under)); tea.
    + depelim X0.
      eapply pred1etal_pop_clos; tea.
      * now eapply IHIX.
      * now eapply IXn.
Admitted.



Lemma eta_spine_right_pred1_equality cf TC Σ Q Γ Γ' t t' u args T T₀ :
  let P Γ t t' T :=
    Q Γ t t' T ×
    forall u T₀, Σ ;;; Γ ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T
  in
  [(X : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' : T)] ->
  [(IX : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' : T on X with
    fun Γ t t' T H => P Γ t t' T × eta_spineε Σ P Γ t t' T H)] ->
  [(Xp : Σ ;;; Γ ⊢ t ≡>1 u : T₀)] ->
    Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' | ≡>1 u : T.
Proof.
  intros * IX.
  induction IX in u, T₀ => Xp.
  - eapply pred1etar_sprop; tea.
    now eexists.
  - eapply pred1etar_ground; trea.
    eapply IXR; tea.
    have {} Xp : Σ ;;; Γ ,,, Γ' ⊢ lift0 #|Γ'| t ≡>1 lift0 #|Γ'| u : lift0 #|Γ'| T₀ by admit.
    eassumption.
  - eapply pred1etar_push; tea.
    now eapply IHIX.
  - eapply pred1etar_pop; trea.
    now eapply IHIX.
Admitted.


Lemma eta_spine_right_pred1_equality_under cf TC Σ Q Γ Γ' na A t t' u args T T₀ :
  let P Γ t t' T :=
    match t return Type with tLambda na A t =>
      forall u T₀, Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T
    | _ => True
    end × Q Γ t t' T
  in
  [(X : Σ ;;; Γ ;;; Γ' ⊢ ↑^ tLambda na A t · args =η t' : T)] ->
  [(IX : Σ ;;; Γ ;;; Γ' ⊢ ↑^ tLambda na A t · args =η t' : T on X with
    fun Γ t t' T H => P Γ t t' T × eta_spineε Σ P Γ t t' T H)] ->
  [(Xp : Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀)] ->
    Σ ;;; Γ ;;; Γ' ⊢ ↑^(λ(na : A), t) · args =η t' | ≡>1 u : T.
Proof.
  intros * IX.
  dependent induction IX => Xp.
  - eapply pred1etar_sprop; tea.
    now eexists.
  - eapply pred1etar_ground; trea.
    cbn in IXR.
    eapply IXR; tea.
    have {} Xp : Σ ;;; Γ ,,, Γ' ,, vass na (lift0 #|Γ'| A) ⊢ lift #|Γ'| 1 t0 ≡>1 lift #|Γ'| 1 u : lift #|Γ'| 1 T₀ by admit.
    eassumption.
  - eapply pred1etar_push; tea.
    now eapply IHIX.
  - eapply pred1etar_pop; trea.
    now eapply IHIX.
Admitted.




Theorem pred1_equality_pred1_equality cf TC Σ (Pre : PredEqPrecondition cf TC Σ) Γ t t' u T T₀ :
  Σ ;;; Γ ⊢ t =η t' : T ->
  Σ ;;; Γ ⊢ t ≡>1 u : T₀ ->
  Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T.
Proof.
  intro Xe.
  revert u T₀.
  set P := fun Γ t t' T =>
    match t with tLambda na A t =>
      forall u T₀, Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T
    | _ => True
    end × forall u T₀, Σ ;;; Γ ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T.
  eenough (XGoal : P Γ t t' T) by exact (snd XGoal).
  induction Xe.
  destruct X.
  all: split; [destruct t => //|]; try rename u into t'; intros u T₀' Xp.

  - eapply pred1eq_lam_etal.
    have Xt' : Σ ;;; Γ ⊢ t' : T by admit. (* right typing *)
    now eapply eta_spine_left_pred1_equality in IX.
  - eapply pred1eq_etal.
    have Xt' : Σ ;;; Γ ⊢ t' : T by admit. (* right typing *)
    now eapply eta_spine_left_pred1_equality in IX.

  - eapply pred1eq_lam_etar.
    now eapply eta_spine_right_pred1_equality_under in IX.
  - eapply pred1eq_etar.
    now eapply eta_spine_right_pred1_equality in IX.

  - eapply pred1eq_lam_etar, pred1etar_sprop; tea.
    1: now eexists.
    rewrite /= !lift0_id //.
  - eapply TCI_elim; tc; tea.
    now eapply pred1eq_sprop.

  - depelim IX.
    eapply pred1eq_lam_ground; eauto.
    now eapply IXt.

  - eapply TCI_elim; tc; tea.
    clear XT T. rename T₀ into T.
    destruct Xp using pred1_elim; revgoals.
    all: clear XT U.

    + apply pred1eq_clos.
      destruct IX; depelim X0.
      * rewrite hnth in hnth0. injection hnth0 as [= <-].
        now constructor.
      * subst na'0.
        econstructor.
        -- eauto.
        -- now eapply IXA.
        -- eauto.
        -- now eapply IXt.
      * econstructor.
        -- now eapply IXt.
        -- now eapply IXu.
      * subst na'0.
        econstructor; eauto.
        -- now eapply IXA.
        -- now eapply IXB.
      * subst s'0.
        econstructor; eauto.

    + destruct IX; depelim X0.
      rename t0 into t₀, t' into t'₀, u0 into a, u' into a', u'0 into b, t'0 into u, A0 into A₀, na0 into na₀.
      have XA : Σ ;;; Γ ⊢ A ≤* A₀ by admit.
      have XB : Σ ;;; Γ ⊢ tProd na A B ≤* tProd na₀ A₀ B by admit.
      eapply pred1eq_beta_clos.
      * eapply TCI_elim with (1 := ltac:(apply TC_compat_pred1_eq_spine_under)); tea.
        now eapply IXt.
      * eapply TCI_elim; tc; tea.
        now eapply IXu.
Admitted.

Definition pred1_commut_on_lambda {cf TC} Σ Γ Γ' na A (t : term) t' args u B T : Type :=
  (
    args = [] ×
    ∑ na' A' t'' s u',
      t' = tLambda na' A' t'' × eq_binder_annot na na' × Σ ;;; Γ ⊢ A <=[Conv]η A' : tSort s ×
      Σ ;;; Γ ,, vass na A ⊢ t'' ≡>1 u' : T × Σ ;;; Γ ,,, Γ',, vass na (lift0 #|Γ'| A) ⊢ u <=[Conv]η lift #|Γ'| 1 u' : B
  ) + (
    ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ;;; Γ',, vass na (lift0 #|Γ'| A) ⊢ u =η ↑^ u' · map S args,, 0 : B
  ).

Lemma pred1_equality_commut_base cf TC Σ (Pre : PredEqPrecondition cf TC Σ) :
  [(Xrec Γ t t' u T : Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T -> ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u =η u' : T)] ->
  [(XetaL Γ Γ' t t' u args T T' : Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T | T' ->
    ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T' × Σ ;;; Γ ;;; Γ' ⊢ u =η ↑^ u' · args : T)] ->
  [(XetaR Γ Γ' t t' u args T : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' | ≡>1 u : T ->
    ∑ u' : term, Σ ;;; Γ ,,, Γ' ⊢ t' ≡>1 u' : T × Σ ;;; Γ ;;; Γ' ⊢ ↑^ u · args =η u' : T)] ->
  [(Xlam Γ na A t t' u T : Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T ->
    ∑ B,
    Σ ;;; Γ ⊢ tProd na A B ≤* T ×
    pred1_commut_on_lambda Σ Γ [] na A t t' [] u B T)] ->
  forall Γ t t' u T,
  Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T ->
  ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u =η u' : T.
Proof.
  intros.
  destruct X.

  - apply Xrec in X as (u' & Xpu & Xeu).
    eexists; split.
    + now eapply pred1_cumul.
    + now eapply eta_spine_cumul.
  - enough (∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u =η u' : T).
    { destruct X as (u' & Xpu & Xeu); eexists; split; tea. }
    destruct c.
    + exists (tRel n); split.
      * now do 2 econstructor.
      * now do 2 econstructor.
    + exists (tSort s'); split.
      * now do 2 econstructor.
      * now do 2 econstructor.
    + apply Xrec in XA as (B' & XpB & XeB), Xt as (u' & Xpu & Xeu).
      exists (tLambda na' B' u'); split.
      * eapply TCI_elim; tc; tea.
        1: do 2 econstructor; trea.
        all: admit.
      * eapply eta_clos.
        1: econstructor; tea.
        all: admit.
    + apply Xrec in Xt as (g' & Xpg & Xeg), Xu as (b' & Xpb & Xeb).
      exists (tApp g' b'); split.
      * eapply TCI_elim; tc; tea.
        1: do 2 econstructor; trea.
        all: admit.
      * eapply eta_clos.
        1: econstructor; tea.
        all: admit.
    + apply Xrec in XA as (B' & XpB & XeB), XT as (U' & XpU & XeU).
      exists (tProd na' B' U'); split.
      * do 2 econstructor; trea.
        -- rewrite -Xα //.
        -- admit.
      * eapply eta_clos; trea.
        1: econstructor; tea.
        all: admit.

  - exists t'; split.
    + now apply pred1_trefl.
    + eapply eta_sprop; trea.
      admit.

  - eapply XetaR in p as (u' & Xpu & Xeu).
    exists u'; split.
    + assumption.
    + now eapply eta_right.

  - eapply XetaL in p as (u' & Xpu & Xeu).
    exists u'; split.
    + assumption.
    + now eapply eta_left.

  - eapply Xrec in X as (b' & Xpb & Xeb).
    eapply Xlam in p as (B' & XT & [ (_ & na' & A' & t'' & s & u' & -> & eqna & XA & Xpu & Xeu)|(u' & Xpu & Xeu) ]).
    + exists (u' {0 := b'}); split.
      * eapply TCI_elim; tc.
        1: eapply pred1_pred0, pred0_beta.
        all: admit.
      * rewrite /= !lift0_id -/(snoc Γ (vass _ _)) in Xeu.
        admit.

    + exists (tApp u' b'); split.
      * eapply TCI_elim; tc.
        1: eapply pred1_clos, clos_app; tea.
        admit.
      * rewrite /= lift0_id /snoc in Xeu.
        admit.
Qed.


Lemma pred1_equality_commut_etaL cf TC Σ (Pre : PredEqPrecondition cf TC Σ) :
  [(Xrec Γ t t' u T : Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T -> ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u =η u' : T)] ->
  [(XetaL Γ Γ' t t' u args T T' : Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T | T' ->
    ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T' × Σ ;;; Γ ;;; Γ' ⊢ u =η ↑^ u' · args : T)] ->
  [(XetaLlam Γ Γ' na A t args t' u T T' : Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T | T' ->
    ∑ B,
    Σ ;;; Γ ⊢ tProd na A B ≤* T ×
    pred1_commut_on_lambda Σ Γ Γ' na A t t' args u B T')] ->
  forall Γ Γ' t t' u args T T', Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T | T' ->
    ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T' × Σ ;;; Γ ;;; Γ' ⊢ u =η ↑^ u' · args : T.
Proof.
  intros.
  destruct X.

  - exists t'; split.
    * apply pred1_trefl. now eapply TCI_elim; tc; tea.
    * eapply etal_sprop; tea.
      admit.

  - apply Xrec in p as (u' & Xpu & Xeu).
    have {Xpu} [u'' [eu Xpu]] : ∑ u'', u' = lift0 #|Γ'| u'' × Σ ;;; Γ ⊢ t' ≡>1 u'' : T' by admit. subst u'.
    exists u''; split.
    * assumption.
    * by eapply etal_ground.

  - eapply XetaL in X as (u' & Xpu & Xeu).
    exists u'; split.
    * assumption.
    * eapply etal_push; tea.
      all: admit.

  - apply Xrec in p as (n4 & Xpn & Xen).
    assert (n4 = tRel n) as -> by admit.
    eapply XetaL in X as (u' & Xpu & Xeu).
    exists u'; split.
    * assumption.
    * eapply etal_pop; tea.
      admit.

  - apply Xrec in p0 as (n4 & Xpn & Xen).
    assert (n4 = tRel n) as -> by admit.
    apply XetaLlam in p as (B' & XT & [ (-> & na' & A' & t'' & s & u' & -> & eqna & XA & Xpu & Xeu)|(u' & Xpu & Xeu) ]).
    + admit.

    + exists u'.
      split.
      * assumption.
      * eapply TCI_elim with (1 := ltac:(apply TC_compat_eta_left_spine)); tea.
        admit.




    enough (∑ u' : term,
        Σ ;;; Γ ⊢ t' ≡>1 u' : T'
      × Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ u =η ↑^ u' · map S args,, 0 : B) by admit. (* eq substitutivity *)

    enough (∑ u' : term,
      Σ ;;; Γ ⊢ t' ≡>1 u' : T'
      × Σ ;;; Γ ;;; Γ' ⊢ tLambda na A u =η ↑^ u' · args : tProd na A B) by admit. (* eta is invertible *)

    enough (forall Γ Γ' na A t t' u args T T', Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T | T' ->
      ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T' × Σ ;;; Γ ;;; Γ' ⊢ tLambda na A u =η ↑^ u' · args : T).
    { now eapply X. }

    all: admit.



Theorem pred1_equality_commut cf TC Σ (Pre : PredEqPrecondition cf TC Σ) Γ t t' u T :
  Σ ;;; Γ ⊢ t =η t' | ≡>1 u : T ->
  ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u =η u' : T.
Proof.
  revert Γ t t' u T.
  fix rec 6.
  intros * X.
  destruct X.
  - apply rec in X as (u' & Xpu & Xeu).
    eexists; split.
    + now eapply pred1_cumul.
    + now eapply eta_spine_cumul.
  - enough (∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u =η u' : T).
    { destruct X as (u' & Xpu & Xeu); eexists; split; tea. }
    destruct c.
    + exists (tRel n); split.
      * now do 2 econstructor.
      * now do 2 econstructor.
    + exists (tSort s'); split.
      * now do 2 econstructor.
      * now do 2 econstructor.
    + apply rec in XA as (B' & XpB & XeB), Xt as (u' & Xpu & Xeu).
      exists (tLambda na' B' u'); split.
      * eapply TCI_elim; tc; tea.
        1: do 2 econstructor; trea.
        all: admit.
      * eapply eta_clos.
        1: econstructor; tea.
        all: admit.
    + apply rec in Xt as (g' & Xpg & Xeg), Xu as (b' & Xpb & Xeb).
      exists (tApp g' b'); split.
      * eapply TCI_elim; tc; tea.
        1: do 2 econstructor; trea.
        all: admit.
      * eapply eta_clos.
        1: econstructor; tea.
        all: admit.
    + apply rec in XA as (B' & XpB & XeB), XT as (U' & XpU & XeU).
      exists (tProd na' B' U'); split.
      * do 2 econstructor; trea.
        -- rewrite -Xα //.
        -- admit.
      * eapply eta_clos; trea.
        1: econstructor; tea.
        all: admit.

  - destruct c.
    + exists (tSort s'); split.
      * now do 2 econstructor.
      * now do 2 econstructor.
    + apply rec in XA as (B' & XpB & XeB), XT as (U' & XpU & XeU).
      exists (tProd na' B' U'); split.
      * do 2 econstructor; trea.
        -- rewrite -Xα //.
        -- admit.
      * eapply eta_clos; trea.
        1: econstructor; tea.
        all: admit.

  - exists t'; split.
    + now apply pred1_trefl.
    + eapply eta_sprop; trea.
      admit.

  - enough (forall Γ Γ' t t' u args T, Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' | ≡>1 u : T ->
      ∑ u' : term, Σ ;;; Γ ,,, Γ' ⊢ t' ≡>1 u' : T × Σ ;;; Γ ;;; Γ' ⊢ ↑^ u · args =η u' : T).
    { edestruct X as (u' & Xpu & Xeu); tea. eexists; split; tea. now eapply eta_right. }
    clear Γ pb t t' u T p.
    induction 1.
    + exists t'; split.
      * apply pred1_trefl. now eapply TCI_elim; tc; tea.
      * eapply etar_sprop; tea.
        admit.

    + apply rec in p as (u' & Xpu & Xeu).
      exists u'; split.
      * eapply TCI_elim; tc; tea.
      * eapply etar_ground.
        eapply TCI_elim; tc; tea.

    + destruct IHX as (u' & Xpu & Xeu).
      exists (tLambda na A u'); split.
      * eapply TCI_elim; tc; tea.
        destruct l as (_ & s & XA & _ & Xs); cbn in XA, Xs.
        eapply pred1_clos, clos_lambda; trea.
        now apply pred1_trefl.
      * eapply etar_push; tea.

    + destruct IHX as (u' & Xpu & Xeu).
      exists (tApp u' n'); split.
      * eapply TCI_elim; tc.
        1: eapply pred1_clos, clos_app; trea.
        1: apply pred1_trefl.
        all: admit.
      * eapply etar_pop; tea.

  - enough (forall Γ Γ' t t' u args T T', Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T | T' ->
      ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T' × Σ ;;; Γ ;;; Γ' ⊢ u =η ↑^ u' · args : T).
    { edestruct X as (u' & Xpu & Xeu); tea. eexists; split; tea. now eapply eta_left. }
    clear Γ pb t t' u T p.
    induction 1.
    + exists t'; split.
      * apply pred1_trefl. now eapply TCI_elim; tc; tea.
      * eapply etal_sprop; tea.
        admit.

    + apply rec in r as (u' & Xpu & Xeu).
      have {Xpu} [u'' [eu Xpu]] : ∑ u'', u' = lift0 #|Γ'| u'' × Σ ;;; Γ ⊢ t' ≡>1 u'' : T' by admit. subst u'.
      exists u''; split.
      * assumption.
      * by eapply etal_ground.

    + destruct IHX as (u' & Xpu & Xeu).
      exists u'; split.
      * assumption.
      * eapply etal_push; tea.
        all: admit.

    + apply rec in r as (n4 & Xpn & Xen).
      assert (n4 = tRel n) as -> by admit.
      destruct IHX as (u' & Xpu & Xeu).
      exists u'; split.
      * assumption.
      * eapply etal_pop; tea.
        admit.

    + apply rec in r as (n4 & Xpn & Xen).
      assert (n4 = tRel n) as -> by admit.

      enough (∑ u' : term,
          Σ ;;; Γ ⊢ t' ≡>1 u' : T'
        × Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ u =η ↑^ u' · map S args,, 0 : B) by admit. (* eq substitutivity *)

      enough (∑ u' : term,
        Σ ;;; Γ ⊢ t' ≡>1 u' : T'
        × Σ ;;; Γ ;;; Γ' ⊢ tLambda na A u =η ↑^ u' · args : tProd na A B) by admit. (* eta is invertible *)

      enough (forall Γ Γ' na A t t' u args T T', Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T | T' ->
        ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T' × Σ ;;; Γ ;;; Γ' ⊢ tLambda na A u =η ↑^ u' · args : T).
      { now eapply X. }

      all: admit.

  - apply rec in X as (b' & Xpb & Xeb).
    enough (forall Γ na A t t' u T, Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T ->
      ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ,, vass na A ⊢ u <=[Conv]η u' : T).
    { edestruct X as (u' & Xpu & Xeu); tea. eexists; split; tea. }

Abort.







Lemma red0_pred0 TC Σ R (Pre : TypedReflexivity R Σ) Γ t u T :
  Σ ;;; Γ ⊢ t ~>0 u : T ->
  Σ ;;; Γ ⊢ t ≡>0 u : T with R.
Proof.
  induction 1.
  - constructor; tas.
    all: now apply trefl.
Qed.


Lemma hred_pred1 TC Σ (Pre : TypedReflexivity (pred1 Σ) Σ) Γ t u T :
  Σ ;;; Γ ⊢ t ~>h u : T ->
  Σ ;;; Γ ⊢ t ≡>1 u : T.
Proof.
  induction 1.
  - now apply pred1_pred0, red0_pred0.
  - now econstructor.
  - eapply head_context1_closure_ofε, head_context1_closure_context1_closure, context1_closure_context_closure in Xtu; tas.
    apply pred1_clos. eauto with fmap.
Qed.

(* Lemma conv'_inv cf TC Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t <===[pb] u : T ->
  ∑ t' u', Σ ;;; Γ ⊢ t ≡>* t' : T × Σ ;;; Γ ⊢ u ≡>* u' : T × Σ ;;; Γ ⊢ t' <=[pb] u'.
Proof.
 *)

(* Lemma cumul_addon_conv' cf TC Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t ≤c[pb] u : T with (conv' Σ) ->
  Σ ;;; Γ ⊢ t <===[pb] u : T.
Proof.
  induction 1.
  - induction XB.
    + eapply conv'_pred1_l; tea.
      eapply pred1_clos, clos_prod; trea.
      all: admit.
    + eapply conv'_pred1_r; tea.
      eapply pred1_clos, clos_prod; trea.
      all: admit.
    +  *)

Lemma conv_conv' cf TC Σ (Pre : TypedReflexivity (pred1 Σ) Σ) Γ pb t u T :
  Σ ;;; Γ ⊢ t <==[pb] u : T ->
  Σ ;;; Γ ⊢ t <===[pb] u : T.
Proof.
  induction 1.
  - eapply conv'_pred1_l; tea.
    now apply hred_pred1.
  - eapply conv'_pred1_r; tea.
    now apply hred_pred1.
  - apply conv'_eq, eq_ext.
    admit.
  -
















Class ConvTransPrecondition {cf TC} Σ := {
  CTP_context_change :: ContextChangeable (typing Σ) (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T);
  CTP_context_change2 :: ContextChangeable2Pb (conv Σ) (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T);
  CTP_right_typing_red0 :: RightTyping (red0 Σ) Σ;
  CTP_left_typing_conv pb :: LeftConvTyping (conv Σ) Σ pb;
  CTP_right_typing_conv pb :: RightConvTyping (conv Σ) Σ pb;
(*   CTP_conv_inst : forall Γ pb t u T σ Δ,
    Σ ;;; Γ ⊢ t <==[pb] u : T ->
    Σ ;;; Δ ⊢ σ : Γ wellsubst with typing ->
    Σ ;;; Δ ⊢ t.[σ] <==[pb] u.[σ] : T.[σ]; *)
  CTP_cmp_sort pb :: TCFromCompareSort Σ (compare_sort Σ pb);
  CTP_cmp_prod :: TCFromCompareProd Σ (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T);
  CTP_cmp_inst :: TCFromCompareSubst10 Σ (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T);

  CTP_conv_sym Γ t u T : Σ ;;; Γ ⊢ t === u : T -> Σ ;;; Γ ⊢ u === t : T;

  CTP_sort_relevance Γ s s' : Σ ;;; Γ ⊢ tSort s ≤* tSort s' -> relevance_of_sort s = relevance_of_sort s';

  CTP_cmp_inst' Γ na (A B B' u : term) :
    Σ ;;; Γ ,, vass na A ⊢ B ≤* B' ->
    Σ ;;; Γ ⊢ B {0 := u} ≤* B' {0 := u};

  CTP_shared_max_prod_type Γ t na na' A A' B B' :
    Σ ;;; Γ ⊢ t : tProd na A B ->
    Σ ;;; Γ ⊢ t : tProd na' A' B' ->
    ∑ na'' A0 B0, Σ ;;; Γ ⊢ tProd na A B ≤* tProd na'' A0 B0 × Σ ;;; Γ ⊢ tProd na' A' B' ≤* tProd na'' A0 B0;

  CTP_shared_max_sort_type Γ t s s' :
    Σ ;;; Γ ⊢ t : tSort s ->
    Σ ;;; Γ ⊢ t : tSort s' ->
    ∑ s0, Σ ;;; Γ ⊢ tSort s ≤* tSort s0 × Σ ;;; Γ ⊢ tSort s' ≤* tSort s0;

  CTP_shared_max_prod_type' Γ t na na' u u' A A' B B' T :
    Σ ;;; Γ ⊢ t : tProd na A B ->
    Σ ;;; Γ ⊢ t : tProd na' A' B' ->
    Σ ;;; Γ ⊢ B {0 := u} ≤* T ->
    Σ ;;; Γ ⊢ B'{0 := u'} ≤* T ->
    Σ ;;; Γ ⊢ u === u' : A ->
    ∑ na'' A0 B0, Σ ;;; Γ ⊢ tProd na A B ≤* tProd na'' A0 B0 × Σ ;;; Γ ⊢ tProd na' A' B' ≤* tProd na'' A0 B0 ×
      Σ ;;; Γ ⊢ B {0 := u} ≤* B0 {0 := u} × Σ ;;; Γ ⊢ B' {0 := u'} ≤* B0 {0 := u} × Σ ;;; Γ ⊢ B0 {0 := u} ≤* T;

  CTP_shared_max_prod Γ na na' A A' B B' T :
    Σ ;;; Γ ⊢ tProd na A B ≤* T ->
    Σ ;;; Γ ⊢ tProd na' A' B' ≤* T ->
    lift_typing typing Σ Γ (j_vass na A) ->
    ∑ B0, Σ ;;; Γ ,, vass na A ⊢ B ≤* B0 × Σ ;;; Γ ,, vass na A ⊢ B' ≤* B0 × Σ ;;; Γ ⊢ tProd na A B0 ≤* T;

  CTP_shared_max_sort Γ na A sA sA' sB sB' T :
    Σ ;;; Γ ⊢ tSort (Sort.sort_of_product sA sB) ≤* T ->
    Σ ;;; Γ ⊢ tSort (Sort.sort_of_product sA' sB') ≤* T ->
    lift_typing typing Σ Γ (j_vass na A) ->
    ∑ sA0 sB0, Σ ;;; Γ ⊢ tSort sA ≤* tSort sA0 × Σ ;;; Γ ⊢ tSort sA' ≤* tSort sA0 × Σ ;;; Γ ,, vass na A ⊢ tSort sB ≤* tSort sB0 × Σ ;;; Γ ,, vass na A ⊢ tSort sB' ≤* tSort sB0 ×
      Σ ;;; Γ ⊢ tSort (Sort.sort_of_product sA0 sB0) ≤* T;

  CTP_Prod_invert Γ na na' A A' B B' : Σ ;;; Γ ⊢ tProd na A B ≤* tProd na' A' B' -> eq_binder_annot na na' × Σ ;;; Γ ⊢ A' ≤* A × Σ ;;; Γ ⊢ A ≤* A' × Σ ;;; Γ ,, vass na A ⊢ B ≤* B';

  (* CTP_sym_conv Γ pb t u T : Σ ;;; Γ ⊢ t === u : T -> Σ ;;; Γ ⊢ u <==[pb] t : T; *)
  CTP_incl_conv Γ pb A B s : Σ ;;; Γ ⊢ A <==[pb] B : tSort s -> Σ ;;; Γ ⊢ A ≤T B;

  CTP_conv_subst10 Γ na (A B t t' u u' : term) :
    Σ ;;; Γ ,, vass na A ⊢ t === t' : B ->
    Σ ;;; Γ ⊢ u === u' : A ->
    Σ ;;; Γ ⊢ t {0 := u} === t' {0 := u'} : B {0 := u};

  (* CTP_insert_red0_left Γ pb t t' u A B T : Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T -> Σ ;;; Γ ⊢ t <==[pb] u : T -> Σ ;;; Γ ⊢ t ~>0 t' : T -> Σ ;;; Γ ⊢ t' <==[pb] u : T; *)
  (* CTP_lift_red0_left Γ pb na A B t t' u T : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t') (tRel 0) <==[pb] u : T -> Σ ;;; Γ ⊢ t ~>0 t' : B -> Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) <==[pb] u : T; *)
  }.
Arguments ConvTransPrecondition : clear implicits.






Lemma case_hredL_context_closure {cf} {TC} Σ (PC : ConvTransPrecondition cf TC Σ) Γ redex reduct u A T B :
  Σ ;;; Γ ⊢ A ≤* T ->
  Σ ;;; Γ ⊢ B ≤* T ->
  Σ ;;; Γ ⊢ redex ~>0 reduct : A ->
  Σ ;;; Γ ⊢ redex ~ u : B with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ ->
  Σ ;;; Γ ⊢ reduct === u : B.
Proof.
  intros XT XT' Ht Xtu.
  apply red0_discriminate in Ht as ht.
  induction Xtu in reduct, A, T, XT, XT', Ht, ht => //=; try rename T0 into B.

  - (* beta *)
    set AP := tProd _ _ _ in Xt.
    have XAP : Σ ;;; Γ ⊢ AP ≤* tProd na A0 B by apply TCI_refl. clearbody AP.
    remember Conv as pb in *.
    induction Xt in reduct, A, T, XT, B, u, XT', Ht, na, A0, u', Heqpb, Xu, ht, XAP; subst pb.
    + apply hred1_discriminate in X.
      destruct t => //.
    + eapply conv_hred_r.
      { eapply hred1_cumul.
        - eapply hred1_clos1, hclos1_appl.
          + eapply TCI_elim; eauto.
            now econstructor.
          + now eapply typing_rightpb.
        - now eapply TC_from_compare_subst10. }
      eapply IHXt; revgoals; trea.
    + depelim X.
      * clear IXR.
        admit.
      * {
        apply conv_ext, ext_sprop.
        - depelim Ht.
          admit.
        - econstructor.
          2: now eapply TC_from_compare_subst10.
          econstructor.
          + todo "Additional argument for tApp".
          + eapply TCI_elim; tea.
            1: now econstructor.
          + now eapply typing_rightpb.
        - admit. }
    + exfalso.
      clear -H ht.
      depelim H => //.
    + eapply IHXt; revgoals; trea.
      eapply TCI_step; tea.
    + clear X.
      depelim H => //.
      depelim Ht.
      apply CTP_Prod_invert in XAP as (eqna & XA' & _ & XB).
      eapply conv_hred_r.
      * eapply TCI_elim; eauto.
        1: intros; now econstructor.
        { eapply hred1_red0, red0_beta.
          - repeat eexists; cbn; tea.
            1: now eapply typing_rightpb.
            rewrite -Xα //.
          - eapply change_context.
            1: now eapply typing_rightpb.
            apply convertible_contexts_snoc.
            1: eapply convertible_contexts_refl; tea.
            * apply treflpb.
            * now eapply typing_wf_local.
            * repeat eexists; cbn; tea. constructor.
          - eapply type_cumul.
            2: now eapply CTP_incl_conv with (pb := Conv) in XA.
            eapply TCI_elim; eauto.
            * intros; now eapply type_cumul.
            * now eapply typing_rightpb. }
        eapply TCI_step.
        1: eapply TC_from_compare_subst10; tea.
        now eapply CTP_cmp_inst'.
      * eapply TCI_elim in Xu; revgoals; tea.
        1: now econstructor.
        eapply TCI_elim in Xt; revgoals; tea.
        1: now econstructor.
        eapply CTP_conv_subst10; tea.
Qed.




Lemma case_hredL_conv {cf} {TC} Σ (PC : ConvTransPrecondition cf TC Σ) Γ pb t t' u A T B :
  Σ ;;; Γ ⊢ A ≤* T ->
  Σ ;;; Γ ⊢ B ≤* T ->
  Σ ;;; Γ ⊢ t ~>h t' : A ->
  Σ ;;; Γ ⊢ t <==[pb] u : B ->
  Σ ;;; Γ ⊢ t' <==[pb] u : B.
Proof.
  intros XT XT' Xt Xtu.
  induction Xt in pb, u, B, T, XT, XT', Xtu.
  - rename T0 into A, u0 into t', X into Xt.
    induction Xtu in t', A, T, XT, XT', Xt; try rename T0 into B.
    + clear IHXtu.
      eapply hred1_inj in X.
      2: { constructor; tea. }
      now rewrite X.
    + eapply conv_hred_r; tea.
      eapply IHXtu; revgoals; eassumption.
    + admit.
    + exfalso.
      now eapply red0_cumul_addon.
    + eapply conv_cumul; tea.
      eapply IHXtu; revgoals; tea.
      eapply TCI_step; tea.
    + clear X.
      apply conv_eq_pb. clear pb.
      now apply case_hredL_context_closure.
  - eapply IHXt; tea.
    now eapply TCI_step.
  - destruct Xtu0.
    depind Xtu.
    + clear IHXtu.
      eapply hred1_inj in X as e.
      2: { eapply hred1_clos1, hclos1_appl; tea.  }
      now rewrite e.
    + eapply conv_hred_r; tea.
      eapply IHXtu; tea.
    + admit.
    + exfalso.
      clear -H Xt.
      depelim H.
    + eapply conv_cumul; tea.
      eapply IHXtu; revgoals; tea.
      eapply TCI_step; tea.
    + clear X.
      apply conv_eq_pb. clear pb.
      depelim H.
      eapply conv_clos, clos_app; tea.
      have XP : ∑ na'' A' B', Σ ;;; Γ ⊢ tProd na A B ≤* tProd na'' A' B' × Σ ;;; Γ ⊢ tProd na0 A0 B0 ≤* tProd na'' A' B'.
      { eapply CTP_shared_max_prod_type.
        1: now eapply typing_leftpb.
        now eapply typing_left. }
      destruct XP as (na'' & A' & B' & XP & XP').
      eapply IXt; tea.
Qed.

Lemma case_ext_conv {cf} {TC} Σ (PC : ConvTransPrecondition cf TC Σ) Γ pb t t' u A T B :
  Σ ;;; Γ ⊢ A ≤* T ->
  Σ ;;; Γ ⊢ B ≤* T ->
  Σ ;;; Γ ⊢ t ~ext t' : A with (fun Γ t u A => forall pb v T B,
      Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T -> Σ ;;; Γ ⊢ u <==[pb] v : B -> Σ ;;; Γ ⊢ t <==[pb] v : T) ->
  Σ ;;; Γ ⊢ t' <==[pb] u : B ->
  Σ ;;; Γ ⊢ t <==[pb] u : B.
Proof.
  intros XT XT' Xt Xtu.
  induction Xt in pb, u, B, T, XT, XT', Xtu.
  - rename u0 into t'.
    (* + apply IHXuv; tas.
      eapply eta_ext_red0_trans in X; tea.
    + eapply conv_hred_r; eauto.
    + apply conv_ext.
      eapply eta_ext_trans; tea.
      eapply ext_conv_fmap; tea; cbn; auto.
    + eapply eta_ext_cumul_addon_trans; tea.
      eapply typing_rightpb, H.
    + eapply conv_cumul; tea.
      apply IHXuv. *)
Abort.

Lemma case_cumul_addon_conv {cf} {TC} Σ (PC : ConvTransPrecondition cf TC Σ) Γ pb pb' t t' u A T B :
  Σ ;;; Γ ⊢ A ≤* T ->
  Σ ;;; Γ ⊢ B ≤* T ->
  [(Ht : Σ ;;; Γ ⊢ t ≤c[pb] t' : A with (conv Σ))] ->
  Σ ;;; Γ ⊢ t ≤c[pb] t' : A on Ht with (fun Γ pb t u A => forall pb' v T B,
      Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T -> Σ ;;; Γ ⊢ u <==[pb'] v : B -> Σ ;;; Γ ⊢ t <==[max_pb pb pb'] v : T) ->
  Σ ;;; Γ ⊢ t' <==[pb'] u : B ->
  Σ ;;; Γ ⊢ t <==[max_pb pb pb'] u : T.
Proof.
  intros XT XT' Ht Xt Xtu.
  apply cumul_addon_discriminate_r in Ht as ht.
  induction Xtu; try rename T0 into B; try rename pb0 into pb'.
  - exfalso.
    now eapply hred1_cumul_addon_r.
  - eapply conv_hred_r; tea.
    + eapply TCI_elim; tea.
      now econstructor.
    + eauto.
  - admit.
  - clear X.
    induction Xt; depelim H.
    + eapply CTP_shared_max_sort with (1 := XT) in XT' as XT0; tea; revgoals.
      { eapply typing_leftpb in XA.
        repeat eexists; cbn; tea. }
      destruct XT0 as (s_ & s'_ & Xss_ & Xs0s_ & Xs's'_ & Xs'0s'_ & Xs_T).
      eapply TCI_elim.
      1: intros; now econstructor.
      1: eapply conv_cumul_addon, cumul_prod.
      * congruence.
      * eapply IXA; eauto.
      * erewrite <-CTP_sort_relevance; tea.
      * eapply IXB.
        3: eapply change_context2pb; tea.
        1,2: eassumption.
        {
        eapply convertible_contexts_snoc.
        1: eapply convertible_contexts_refl.
        - apply treflpb.
        - now eapply conv_wf_local.
        - repeat eexists; cbn.
          + constructor.
          + now symmetry.
          + now apply CTP_conv_sym.
          + rewrite -Xα //. }
      * assumption.
    + eapply TCI_elim.
      1: intros; now econstructor.
      1: eapply conv_cumul_addon, cumul_sort; tas.
      * transitivity s'.
        1: eapply max_pb_left'; tea.
        2: eapply max_pb_right'; tea.
        all: apply compare_sort_subrel.
      * assumption.
  - eapply IHXtu; tea.
    now eapply TCI_step.
  - clear X.
    induction Xt; depelim H.
    + eapply CTP_shared_max_sort with (1 := XT) in XT' as XT0; tea; revgoals.
      { eapply typing_leftpb in XA.
        repeat eexists; cbn; tea. }
      destruct XT0 as (s_ & s'_ & Xss_ & Xs0s_ & Xs's'_ & Xs'0s'_ & Xs_T).
      eapply TCI_elim.
      1: intros; now econstructor.
      1: eapply conv_cumul_addon, cumul_prod.
      * congruence.
      * eapply IXA; eauto.
      * erewrite <-CTP_sort_relevance; tea.
      * eapply IXB.
        3: eapply conv_eq_pb, change_context2pb; tea.
        1,2: eassumption.
        {
        eapply convertible_contexts_snoc.
        1: eapply convertible_contexts_refl.
        - apply treflpb.
        - now eapply conv_wf_local.
        - repeat eexists; cbn.
          + constructor.
          + now symmetry.
          + now apply CTP_conv_sym.
          + rewrite -Xα //. }
      * assumption.
    + eapply TCI_elim.
      1: intros; now econstructor.
      1: eapply conv_cumul_addon, cumul_sort; tas.
      * transitivity s'.
        1: eapply max_pb_left'; tea.
        2: eapply compare_sort_subrel; tea.
        all: apply compare_sort_subrel.
      * assumption.
Qed.

Lemma case_context_closure_conv {cf} {TC} Σ (PC : ConvTransPrecondition cf TC Σ) Γ pb t t' u A T B :
  Σ ;;; Γ ⊢ A ≤* T ->
  Σ ;;; Γ ⊢ B ≤* T ->
  [(Ht : Σ ;;; Γ ⊢ t ~ t' : A with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
  Σ ;;; Γ ⊢ t ~ t' : A on Ht with (fun Γ t u A => forall pb v T B,
      Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T -> Σ ;;; Γ ⊢ u <==[pb] v : B -> Σ ;;; Γ ⊢ t <==[pb] v : T) ->
  Σ ;;; Γ ⊢ t' <==[pb] u : B ->
  Σ ;;; Γ ⊢ t <==[pb] u : T.
Proof.
  intros XT XT' Ht Xt Xtu.
  induction Xtu; try rename T0 into B; try rename pb0 into pb'.
  - eapply IHXtu; tas.

    admit.
  - eapply conv_hred_r; tea.
    + eapply TCI_elim; tea.
      now econstructor.
    + eauto.
  - admit.
  - clear X.
    induction Xt; depelim H.
    + eapply CTP_shared_max_sort with (1 := XT) in XT' as XT0; tea; revgoals.
      { eapply typing_leftpb in XA.
        repeat eexists; cbn; tea. }
      destruct XT0 as (s_ & s'_ & Xss_ & Xs0s_ & Xs's'_ & Xs'0s'_ & Xs_T).
      eapply TCI_elim.
      1: intros; now econstructor.
      1: eapply conv_cumul_addon, cumul_prod.
      * congruence.
      * eapply IXA; eauto.
      * erewrite <-CTP_sort_relevance; tea.
      * eapply IXB.
        3: eapply change_context2pb; tea.
        1,2: eassumption.
        {
        eapply convertible_contexts_snoc.
        1: eapply convertible_contexts_refl.
        - apply treflpb.
        - now eapply conv_wf_local.
        - repeat eexists; cbn.
          + constructor.
          + now symmetry.
          + now apply CTP_conv_sym.
          + rewrite -Xα //. }
      * assumption.
    + eapply TCI_elim.
      1: intros; now econstructor.
      1: eapply conv_cumul_addon, cumul_sort; tas.
      * transitivity s'; tas.
        eapply compare_sort_subrel; tea.
      * assumption.
  - eapply IHXtu; tea.
    now eapply TCI_step.
  - clear X.
    apply conv_eq_pb.
    induction Xt; depelim H.
    + eapply TCI_elim.
      * now econstructor.
      * now apply conv_clos, clos_rel.
      * assumption.
    + have [s' [Xs' Xs0']] : ∑ s', Σ ;;; Γ ⊢ tSort s ≤* tSort s' × Σ ;;; Γ ⊢ tSort s0 ≤* tSort s'.
      { eapply CTP_shared_max_sort_type.
        1: now eapply typing_rightpb.
        now eapply typing_leftpb. }
      eapply CTP_shared_max_prod with (1 := XT) in XT' as XT0; tea; revgoals.
      { eapply typing_leftpb in XA.
        repeat eexists; cbn; tea. }
      destruct XT0 as (T00 & XT0 & XT0' & XTT).
      eapply TCI_elim.
      1: now econstructor.
      1: eapply conv_clos, clos_lambda.
      * congruence.
      * eapply IXA; eauto.
      * erewrite <-CTP_sort_relevance; tea.
      * eapply IXt; eauto.
        eapply conv_eq_pb, change_context2pb; tea.
        {
        eapply convertible_contexts_snoc.
        1: eapply convertible_contexts_refl.
        - apply treflpb.
        - now eapply conv_wf_local.
        - repeat eexists; cbn.
          + constructor.
          + now symmetry.
          + now apply CTP_conv_sym.
          + rewrite -Xα //. }
      * assumption.
    + eapply CTP_shared_max_prod_type' with (3 := XT) in XT' as XP; revgoals.
      { eassumption. }
      { by now eapply typing_leftpb. }
      { by now eapply typing_rightpb. }
      destruct XP as (na'' & A' & B' & XP & XP' & XB0 & XB1 & XB').
      apply CTP_Prod_invert in XP as XP_, XP' as XP'_.
      destruct XP_ as (eqna'' & XA'A & XAA' & XBB').
      destruct XP'_ as (eqna0'' & XA'A0 & XA0A' & XB0B').
      eapply TCI_elim.
      1: intros; now econstructor.
      1: eapply conv_clos, clos_app; tas.
      * eapply IXt; eauto.
      * eapply IXu; eauto.
      * assumption.
    + eapply CTP_shared_max_sort with (1 := XT) in XT' as XT0; tea; revgoals.
      { eapply typing_leftpb in XA.
        repeat eexists; cbn; tea. }
      destruct XT0 as (s_ & s'_ & Xss_ & Xs0s_ & Xs's'_ & Xs'0s'_ & Xs_T).
      eapply TCI_elim.
      1: intros; now econstructor.
      1: eapply conv_cumul_addon, cumul_prod.
      * congruence.
      * eapply IXA; eauto.
      * erewrite <-CTP_sort_relevance; tea.
      * eapply IXB.
        3: eapply conv_eq_pb, change_context2pb; tea.
        1,2: eassumption.
        {
        eapply convertible_contexts_snoc.
        1: eapply convertible_contexts_refl.
        - apply treflpb.
        - now eapply conv_wf_local.
        - repeat eexists; cbn.
          + constructor.
          + now symmetry.
          + now apply CTP_conv_sym.
          + rewrite -Xα //. }
      * assumption.
    + eapply TCI_elim.
      1: intros; now econstructor.
      1: eapply conv_cumul_addon, cumul_sort; tas.
      * now transitivity s'.
      * assumption.
Qed.

Lemma conv_trans {cf} {TC} Σ (PC : ConvTransPrecondition cf TC Σ) Γ pb pb' t u v T :
  Σ ;;; Γ ⊢ t <==[pb] u : T ->
  Σ ;;; Γ ⊢ u <==[pb'] v : T ->
  Σ ;;; Γ ⊢ t <==[max_pb pb pb'] v : T.
Proof.
  set (A := T) at 1. set (B := T) at 1.
  have XT : Σ ;;; Γ ⊢ A ≤* T by constructor.
  have XT' : Σ ;;; Γ ⊢ B ≤* T by constructor.
  clearbody A B.
  intros Xtu Xuv.
  remember u as u' eqn:e in Xuv.
  pose proof (conv2_conv2 _ _ _ _ _ _ _ _ _ _ _ _ _ XT XT' Xtu Xuv) as X.
  clear XT XT' Xtu Xuv.
  symmetry in e.
  induction X.
  induction 1 in T, B, XT, XT', v, pb' |- * => Xuv; try rename T0 into A.
  - eapply IHX in Xuv; tea.
    eapply conv_hred_l; tea.
    eapply TCI_elim; tea.
    now econstructor.
  - eapply IHX; tea. clear IHX X0 t pb.
    rename u into t, u' into t', v into u, pb' into pb.
    now eapply case_hredL_conv.
  - cbn in X. eapply max_pb_right. 1: apply conv_eq_pb.
    eapply ext_conv_ofε in X; tea. clear H.
    now eapply case_ext_conv.
  - now eapply case_cumul_addon_conv.
  - eapply IHX; tea.
    now eapply TCI_step.
  - cbn in X. apply max_pb_right. 1: apply conv_eq_pb.
    now eapply case_context_closure_conv.
Qed.


Lemma eta_ext_trans {TC} Σ R Γ t u v A B T :
  Σ ;;; Γ ⊢ A ≤[T]≥ B ->
  Σ ;;; Γ ⊢ t ~ext u : A with (fun Γ t u T => forall v, R Γ u v T -> R Γ t v T) ->
  Σ ;;; Γ ⊢ u ~ext v : B with R ->
  Σ ;;; Γ ⊢ t ~ext v : T with R.
Proof.
  intro HT.
  induction 1.
  all: intro X; depelim X.
  - constructor; tas.
    now apply r.
    all: admit.
  - apply ext_sprop; tas.
  - apply ext_sprop; tas.
  - apply ext_sprop; tas.
Qed.

Lemma eta_ext_red0_trans {cf TC} Σ (PC : ConvTransPrecondition cf TC Σ) (R := conv Σ) Γ t u u' T :
  Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ t u T => forall pb v, R Γ pb u v T -> R Γ pb t v T) ->
  Σ ;;; Γ ⊢ u ~>0 u' : T ->
  Σ ;;; Γ ⊢ t ~ext u' : T with (fun Γ t u T => forall pb v, R Γ pb u v T -> R Γ pb t v T).
Proof.
  destruct 1 => Xuu'.
  all: apply typing_right in Xuu' as Xu'.
  2: now constructor.
  have wfΓ : wf_local Σ Γ by now eapply typing_wf_local.
  have wfΓ' : wf_local Σ (Γ ,, vass na A) by now constructor.
  constructor; tas.
  intros pb v Xv.
  eapply r.
  eapply CTP_lift_red0_left; tea.
Qed.

Lemma eta_ext_cumul_addon_trans {cf TC} Σ R R' Γ pb t u v T :
  Σ ;;; Γ ⊢ t ~ext u : T with R ->
  Σ ;;; Γ ⊢ u ≤c[pb] v : T with R' ->
  Σ ;;; Γ ⊢ v : T ->
  Σ ;;; Γ ⊢ t <==[pb] v : T.
Proof.
  destruct 1 => Xuv Xv.
  - by depelim Xuv.
  - by do 2 constructor.
Qed.

Lemma eta_ext_context_closure_trans {cf TC} Σ R R' Γ pb t u v T :
  Σ ;;; Γ ⊢ t ~ext u : T with R ->
  Σ ;;; Γ ⊢ u ~ v : T with R', eq_binder_annot, eq_sort Σ ->
  Σ ;;; Γ ⊢ v : T ->
  Σ ;;; Γ ⊢ t <==[pb] v : T.
Proof.
  destruct 1 => Xuv Xv.
  2: by do 2 constructor.
  depelim Xuv.
  - cbn in *.
Qed.

Lemma context_closure_conv_trans {cf} {TC} Σ (PC : ConvTransPrecondition cf TC Σ) Γ t u v T :
  [(X : Σ ;;; Γ ⊢ t ~ u : T with (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T), eq_binder_annot, eq_sort Σ)] ->
  [(IX : Σ ;;; Γ ⊢ t ~ u : T on X with (fun Γ t u T => forall v, Σ ;;; Γ ⊢ u === v : T -> Σ ;;; Γ ⊢ t === v : T))] ->
  Σ ;;; Γ ⊢ u ~ v : T with (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T), eq_binder_annot, eq_sort Σ ->
  Σ ;;; Γ ⊢ t === v : T.
Proof.
  (* intros X IX.
  induction IX in v |- *.
  all: intro X; depelim X.
  - now apply conv_clos, clos_rel.
  - eapply conv_clos, clos_lambda; tea.
    + now apply IXt.
    + now symmetry.
    + rewrite -Xα //.
    + eapply change_context2pb; tea.
      apply convertible_contexts_snoc.
      1: eapply convertible_contexts_refl.
      * apply treflpb.
      * now eapply conv_wf_local.
      * repeat eexists; cbn; tea.
        constructor.
    + eapply TC_from_compare_prod; tea.
  - eapply conv_cumul.
    1: eapply conv_clos, clos_app; tea.
    + now eapply TC_from_compare_subst10.
  - eapply conv_clos, clos_prod; tea.
    + now symmetry.
    + rewrite -Xα //.
    + eapply change_context2pb; tea.
      apply convertible_contexts_snoc.
      1: eapply convertible_contexts_refl.
      * apply treflpb.
      * now eapply conv_wf_local.
      * repeat eexists; cbn; tea.
        constructor.
  - eapply conv_cumul.
    1: eapply conv_clos, clos_sort; tea.
    + now symmetry in Xs.
    + eapply TC_from_compare_sort with (pb := Conv); tea.
      1,2: by apply wf_sort_super.
      now apply compare_sort_super. *)
Abort.





(*



Remaining goals:
  + algo transitivity: Γ |- t <== u : T -> Γ |- u <== v : T -> Γ |- t <== v : T
  + decidable ~>Prod, decidable ~>Sort, decidable <==

Assumptions on ≤T:
  + ≤T reflexivity on types
  + ≤T context conversion (<==)
  + (<==) incl ≤T


Step 2: algo transitivity

- context closure transitivity: Γ |- t ~R u : T0 -> Γ |- u ~R v : T1 -> T0 ≤T T -> T1 ≤T T -> Γ |- t ~R v : T
  needs: context conversion (for ~R), ~R transitive mod ≤T

- algo transitivity: Γ |- t <== u : T0 -> Γ |- u <== v : T1 -> T0 ≤T T -> T1 ≤T T -> Γ |- t <== v : T
  by induction over 1
  case 1: nothing
  case 2: add_beta_algo: Γ |- u ~>β u' : T0 -> Γ |- u <== v : T1 -> T0 ≤T T -> T1 ≤T T -> Γ |- u' <== v : T
  case 3: typed algorithmic conv -> (right) typing + ≤T_SProp (Γ |- T0 : SProp & Γ |- t : T0 -> Γ |- u : T0 -> T0 ≤T T -> T1 ≤T T -> Γ |- u <== v : T1 -> Γ |- t <== v : T)
  case 4: add_eta_algo
  case 5: nothing
  case 6: cumul_addon / context closure -> induction 2
    subcase 1: add_beta_algo_r: Γ |- v ~>β v' : T1 -> Γ |- u <== v : T0 -> T0 ≤T T -> T1 ≤T T -> Γ |- u <== v' : T
    subcase 2: nothing
    subcase 3: typed algorithmic conv -> (left) typing + ≤T_SProp (Γ |- T1 : SProp & Γ |- u : T1 -> Γ |- v : T1 -> Γ |- u <== v : T0 -> T0 ≤T T -> T1 ≤T T -> Γ |- t <== v : T)
    subcase 4: nothing (congruences)
    subcase 5: nothing
    subcase 6: cumul_addon / context closure vs cumul_addon / context closure: context closure transitivity

- ≤T_SProp: Γ |- T : SProp -> T ≤T T' -> Γ |- T' : SProp

- add_eta_algo: Γ |- tApp (↑ u) (tRel 0) <== v : T1 -> T0 ≤T T -> T1 ≤T T -> Γ |- u <== v : T
  [inversion] Γ |- (tLam) <== v : T1

- add_beta_algo: Γ |- t ~>β t' : T0 -> Γ |- t' : T0 -> Γ |- t <== u : T1 -> T0 ≤T T -> T1 ≤T T -> Γ |- t' <== u : T
  inversion: t = (fun na : A => f : B) arg; t' = f {0 := arg}; T0 = B {0 := arg};
    case 0: nothing
    case 1: T1 : SProp
    case 1' (η): comm_beta_eta0
    case 2: u = f' arg', f' : tProd na' A' B', arg' : A', B' {0 := arg'} ≤T T1, tProd na' A' B' : SProp, so by typing substitutivity B' {0 := arg'} : SProp
    case 2': comm_beta_eta1
    case 3: u = (fun na' : A'' => f' : B') arg', arg' : A', f === f', B === B', arg === arg' -> substitutivity for f {0 := arg} <== f' {0 := arg'} (then βr)
            ≤T product injectivity

- comm_beta_eta0: Γ ,, (na, A) |- tApp (↑ (tApp (tLambda na A' f) arg)) (tRel 0) <== tApp (↑ u) (tRel 0) : tProd na A B -> Γ |- f {0 := arg} <== u : T
  needs: ≤T product injectivity, <== context conversion

- comm_beta_eta1: Γ ,, (na, A) |- tApp (↑ (tLambda na A' f)) (tRel 0) <== tApp (↑ f') (tRel 0) : tProd na A B -> Γ |- f {0 := arg} <== f' arg : T
  needs: ≤T product injectivity, (tApp congr), <== context conversion



- algo substitutivity: Γ, Δ, Γ' |- t <== u : T -> Γ |- s <== s' : Δ -> Γ, Γ'{s} |- t{s} <== t'{s'} : T{s}
  needs: typing substitutivity, ≤T substitutivity, (β substitutivity), algo weakening

- algo weakening: Γ, Γ' |- t <== u : T -> Γ, Δ, Γ'{↑Δ} |- t{↑Δ} <== t'{↑Δ} : T{↑Δ}
  needs: typing weakening, ≤T weakening, (β weakening)

- typing substitutivity: Γ, Δ, Γ' |- t : T -> Γ |- s : Δ -> Γ, Γ'{s} |- t{s} : T{s}
  needs: ≤T substitutivity, typing weakening

- typing weakening: Γ, Γ' |- t : T -> Γ, Δ, Γ'{↑Δ} |- t{↑Δ} : T{↑Δ}
  needs: ≤T weakening


Assumptions on ≤T:
  + ≤T reflexivity on types
  + ≤T context conversion (<==)
  + (<==) incl ≤T
  + ≤T weakening, substitutivity
  + ≤T_SProp
  + ≤T product injectivity


Part 3: Instantiating ≤T
Step 1: with <==

[1] reflexivity on types: by induction
[2] context conversion with <==: needs [2,3,4]
[3] (<==) incl ≤T: by definition
[4] ≤T substitutivity, weakening: needs [4]
[5] ≤T_SProp:
[6] product injectivity: nothing



[5] Γ |- T : SProp -> Γ |- T <== T' : tSort s -> Γ |- T' : SProp
  needs: typed algorithmic conv -> (left+right) typing, uniqueness of type (thanks to bidir) mod (===), (===) sort injectivity

Step 2: with ≤
Just use the now established equivalence between ≤ and <==


Part 4: Ditching the types

Remaining goals:
  + decidable ~>Prod, decidable ~>Sort, decidable <==

Inductive untyped context closure ~ :=
  | Γ |- tRel n ~ tRel n
  | Rα na na' -> Γ |- A ~R A' -> rel_of_sort s = na -> Γ ,, (na, A) |- t ~R t' -> Γ |- tLambda na A t ~ tLambda na' A' t'
  | Γ |- t ~R t' -> Γ |- u ~R u' -> Γ |- tApp t u ~ tApp t' u'
  | Rα na na' -> Γ |- A ~R A' -> rel_of_sort s = na -> Γ ,, (na, A) |- B ~<=R B' -> Γ |- tProd na A B ~<= tProd na' A' B'
  | Rs s s' -> Γ |- tSort s ~<= tSort s'
  | ... (incl. cases where Γ is useful? is it only useful for lets in contexts)

Inductive untyped algorithmic conversion :=
  | t ~>β t' -> Γ |- t' <== u -> Γ |- t <== u
  | u ~>β u' -> Γ |- t <== u' -> Γ |- t <== u
  | Γ |- t IRREL -> Γ |- u IRREL -> Γ |- t <== u
  | Γ ,, (na, A) |- t === tApp (↑ t') (tRel 0) -> Γ |- tLambda na A t <== t'
  | Γ ,, (na, A) |- tApp (↑ t) (tRel 0) === t' -> Γ |- t <== tLambda na A t' : tProd na A B
  | Γ |- t ~ u : T (R := untyped algorithmic conversion) (Rα, ≤s) -> Γ |- t <== u


Inductive untyped head reduction :=
  | whnf t -> t ~>h t
  | t ~>β t' -> t' ~> u -> t ~>h u


Theorem:
- typed -> untyped beta: Γ |- t ~>β u : T -> Γ |- t ~>β u
  needs: nothing

- untyped -> typed beta: Γ |- t : T -> Γ |- t ~>β u -> Γ |- t ~>β u : T
  needs: ≤T product injectivity


- typed -> untyped eta: Γ |- t ~η t' : tProd na A B -> Γ |- t ==> u
  needs: nothing

- untyped -> typed beta: Γ |- t : T -> Γ |- t ~>β u -> Γ |- t ~>β u : T
  needs: ≤T product injectivity


- typed -> untyped SProp Irrel: Γ |- t : T -> Γ |- T : SProp -> Γ |- t IRREL
  needs: ≤T sort injectivity

- untyped -> typed SProp Irrel: Γ |- t : T -> Γ |- t IRREL -> Γ |- T : SProp
  needs: ≤T sort injectivity


- typed -> untyped conversion: Γ |- t ==> u : T -> Γ |- t ==> u
  needs: lemmas above

- untyped -> typed conversion: Γ |- t : T -> Γ |- t ==> u -> Γ |- t ==> u : T
  needs: lemmas above


- typed -> untyped head reduction: Γ |- t ~>h u : T -> Γ |- t ~>h u
  needs: typed -> untyped beta

- untyped -> typed head reduction: Γ |- t : T -> Γ |- t ~>h u -> Γ |- t ~>h u : T
  needs: untyped -> typed beta


- decidable ~>Prod / ~>Sort
  needs: SN

- decidable ==>
  needs: SN, add_beta_algo{,_r}, decidable =α, decidable =s, decidable ≤s



*)






Definition ext_conv_length {R} (R_length : forall {Γ t u T}, R Γ t u T -> nat) {TC Σ Γ t u T} : ext_conv Σ R Γ t u T -> nat :=
  fun H => match H with
  | ext_eta _ _ _ _ _ _ _ _ H => R_length H
  | ext_sprop _ _ _ _ _ _ => 0
  end.

Lemma ext_convε_length {cf} {TC} Σ R R_length R' Γ t u T :
  [(H : Σ ;;; Γ ⊢ t ~ext u : T with R)] ->
  [(X0 Γ t u T : [(H' : R Γ t u T)] -> R_length _ _ _ _ H' <= ext_conv_length R_length H -> R' Γ t u T)] ->
  Σ ;;; Γ ⊢ t ~ext u : T on H with R'.
Proof.
  intros H X.
  induction H in X |- *.
  - econstructor; tea.
    unshelve eapply X; tea.
    reflexivity.
  - now econstructor.
Defined.

Definition cumul_addon_length {R} (R_length : forall {Γ pb t u T}, R Γ pb t u T -> nat) {cf TC Σ Γ pb t u T} : cumul_addon Σ R Γ pb t u T -> nat :=
  fun H => match H with
  | cumul_prod _ _ _ _ _ _ _ _ _ H _ H0 => R_length H + R_length H0
  | cumul_sort _ _ _ _ _ _ => 0
  end.

Lemma cumul_addonε_length {cf} {TC} Σ R R_length R' Γ pb t u T :
  [(H : Σ ;;; Γ ⊢ t ≤c[pb] u : T with R)] ->
  [(X Γ pb t u T : [(H' : R Γ pb t u T)] -> R_length _ _ _ _ _ H' <= cumul_addon_length R_length H -> R' Γ pb t u T)] ->
  Σ ;;; Γ ⊢ t ≤c[pb] u : T on H with R'.
Proof.
  intros H X.
  induction H in X |- *.
  - econstructor; tea.
    all: unshelve eapply X; tea.
    all: cbn; lia.
  - now econstructor.
Defined.

Definition context_closure_length {R Rα Rs} (R_length : forall {Γ t u T}, R Γ t u T -> nat) {TC Σ Γ t u T} : context_closure Σ R Rα Rs Γ t u T -> nat :=
  fun H => match H with
  | clos_rel _ _ _ _ => 0
  | clos_sort _ _ _ _ _ _ => 0
  | clos_lambda _ _ _ _ _ _ _ _ _ H _ H0 => R_length H + R_length H0
  | clos_app _ _ _ _ _ _ _ H H0 => R_length H + R_length H0
  | clos_prod _ _ _ _ _ _ _ _ _ H _ H0 => R_length H + R_length H0
  end.

Lemma context_closureε_length {cf} {TC} Σ R Rα Rs R_length R' Γ t u T :
  [(H : Σ ;;; Γ ⊢ t ~ u : T with R, Rα, Rs)] ->
  [(X Γ t u T : [(H' : R Γ t u T)] -> R_length _ _ _ _ H' <= context_closure_length R_length H -> R' Γ t u T)] ->
  Σ ;;; Γ ⊢ t ~ u : T on H with R'.
Proof.
  intros H X.
  induction H in X |- *.
  all: try now econstructor.
  - econstructor; tea.
    all: unshelve eapply X; tea.
    all: cbn; lia.
  - econstructor; tea.
    all: unshelve eapply X; tea.
    all: cbn; lia.
  - econstructor; tea.
    all: unshelve eapply X; tea.
    all: cbn; lia.
Defined.

Fixpoint conv_length {cf TC Σ Γ pb t u T} (H : Σ ;;; Γ ⊢ t <==[pb] u : T) : nat :=
  match H with
  | conv_hred_l _ _ _ _ _ H => 1 + conv_length H
  | conv_hred_r _ _ _ _ _ H => 1 + conv_length H
  | conv_ext _ _ _ H => 1 + ext_conv_length (fun Γ => @conv_length _ _ _ Γ _) H
  | conv_cumul_addon _ _ _ H => 1 + cumul_addon_length (@conv_length _ _ _) H
  | conv_cumul _ _ _ _ H _ => 1 + conv_length H
  | conv_clos _ _ _ H => 1 + context_closure_length (fun Γ => @conv_length _ _ _ Γ _) H
  end.



  Reserved Notation "Σ ;;; Γ ⊢ t <==[ pb ] u | v <==[ pb' ] w : A ≤ T ≥ B" (at level 50, Γ, t, pb, u, v, pb', w, A, T, B at next level, format "Σ  ;;;  Γ  ⊢  t  <==[ pb ]  u  |  v  <==[ pb' ]  w  :  A  ≤  T  ≥  B").
  Inductive conv2ε {cf} {TC} Σ Γ (pb pb' : conv_pb) (t u v w A B T : term) : Type :=
    | conv2_hred_l t' :
        Σ ;;; Γ ⊢ t ~>h t' : A ->
        Σ ;;; Γ ⊢ t' <==[pb] u | v <==[pb'] w : A ≤ T ≥ B ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_hred_r w' :
        Σ ;;; Γ ⊢ w ~>h w' : B ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w' : A ≤ T ≥ B ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_hred_m1 u' :
        Σ ;;; Γ ⊢ u ~>h u' : A ->
        Σ ;;; Γ ⊢ t <==[pb] u' | v <==[pb'] w : A ≤ T ≥ B ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_hred_m2 v' :
        Σ ;;; Γ ⊢ v ~>h v' : B ->
        Σ ;;; Γ ⊢ t <==[pb] u | v' <==[pb'] w : A ≤ T ≥ B ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_cumul_l A' :
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A' ≤ T ≥ B ->
        Σ ;;; Γ ⊢ A' ≤T A ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_cumul_r B' :
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B' ->
        Σ ;;; Γ ⊢ B' ≤T B ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_clos_clos :
        [(Xtu : Σ ;;; Γ ⊢ t ~ u : A with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
        [(IXtu : Σ ;;; Γ ⊢ t ~ u : A on Xtu with (fun Γ t u A => forall v w pb' B T, Σ ;;; Γ ⊢ v <==[pb'] w : B -> Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->  Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B))] ->
        [(Xuv : Σ ;;; Γ ⊢ v ~ w : B with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
        [(XA : Σ ;;; Γ ⊢ A ≤* T)] ->
        [(XB : Σ ;;; Γ ⊢ B ≤* T)] ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_cumul_addon_cumul_addon :
        [(Xtu : Σ ;;; Γ ⊢ t ≤c[pb] u : A with (conv Σ))] ->
        [(IXtu : Σ ;;; Γ ⊢ t ≤c[pb] u : A on Xtu with (fun Γ pb t u A => forall v w pb' B T, Σ ;;; Γ ⊢ v <==[pb'] w : B -> Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->  Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B))] ->
        [(Xuv : Σ ;;; Γ ⊢ v ≤c[pb'] w : B with (conv Σ))] ->
        [(XA : Σ ;;; Γ ⊢ A ≤* T)] ->
        [(XB : Σ ;;; Γ ⊢ B ≤* T)] ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_clos_ext :
        [(Xtu : Σ ;;; Γ ⊢ t ~ u : A with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
        [(IXtu : Σ ;;; Γ ⊢ t ~ u : A on Xtu with (fun Γ t u A => forall v w pb' B T, Σ ;;; Γ ⊢ v <==[pb'] w : B -> Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->  Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B))] ->
        [(Xvw : Σ ;;; Γ ⊢ v ~ext w : B with (fun Γ => conv Σ Γ Conv))] ->
        [(XA : Σ ;;; Γ ⊢ A ≤* T)] ->
        [(XB : Σ ;;; Γ ⊢ B ≤* T)] ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_ext_clos :
        [(Xtu : Σ ;;; Γ ⊢ t ~ext u : A with (fun Γ => conv Σ Γ Conv))] ->
        [(IXtu : Σ ;;; Γ ⊢ t ~ext u : A on Xtu with (fun Γ t u A => forall v w pb' B T, Σ ;;; Γ ⊢ v <==[pb'] w : B -> Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->  Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B))] ->
        [(Xvw : Σ ;;; Γ ⊢ v ~ w : B with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
        [(XA : Σ ;;; Γ ⊢ A ≤* T)] ->
        [(XB : Σ ;;; Γ ⊢ B ≤* T)] ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_clos_cumul_addon :
        [(Xtu : Σ ;;; Γ ⊢ t ~ u : A with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
        [(IXtu : Σ ;;; Γ ⊢ t ~ u : A on Xtu with (fun Γ t u A => forall v w pb' B T, Σ ;;; Γ ⊢ v <==[pb'] w : B -> Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->  Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B))] ->
        [(Xvw : Σ ;;; Γ ⊢ v ≤c[pb'] w : B with (conv Σ))] ->
        [(XA : Σ ;;; Γ ⊢ A ≤* T)] ->
        [(XB : Σ ;;; Γ ⊢ B ≤* T)] ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_cumul_addon_clos :
        [(Xtu : Σ ;;; Γ ⊢ t ≤c[pb] u : A with (conv Σ))] ->
        [(IXtu : Σ ;;; Γ ⊢ t ≤c[pb] u : A on Xtu with (fun Γ pb t u A => forall v w pb' B T, Σ ;;; Γ ⊢ v <==[pb'] w : B -> Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->  Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B))] ->
        [(Xvw : Σ ;;; Γ ⊢ v ~ w : B with (fun Γ => conv Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
        [(XA : Σ ;;; Γ ⊢ A ≤* T)] ->
        [(XB : Σ ;;; Γ ⊢ B ≤* T)] ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B


    | conv2_cumul_addon_ext :
        [(Xtu : Σ ;;; Γ ⊢ t ≤c[pb] u : A with (conv Σ))] ->
        [(IXtu : Σ ;;; Γ ⊢ t ≤c[pb] u : A on Xtu with (fun Γ pb t u A => forall v w pb' B T, Σ ;;; Γ ⊢ v <==[pb'] w : B -> Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->  Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B))] ->
        [(Xvw : Σ ;;; Γ ⊢ v ~ext w : B with (fun Γ => conv Σ Γ Conv))] ->
        [(XA : Σ ;;; Γ ⊢ A ≤* T)] ->
        [(XB : Σ ;;; Γ ⊢ B ≤* T)] ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_ext_cumul_addon :
        [(Xtu : Σ ;;; Γ ⊢ t ~ext u : A with (fun Γ => conv Σ Γ Conv))] ->
        [(IXtu : Σ ;;; Γ ⊢ t ~ext u : A on Xtu with (fun Γ t u A => forall v w pb' B T, Σ ;;; Γ ⊢ v <==[pb'] w : B -> Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->  Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B))] ->
        [(Xvw : Σ ;;; Γ ⊢ v ≤c[pb'] w : B with (conv Σ))] ->
        [(XA : Σ ;;; Γ ⊢ A ≤* T)] ->
        [(XB : Σ ;;; Γ ⊢ B ≤* T)] ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B

    | conv2_ext_ext :
        [(Xtu : Σ ;;; Γ ⊢ t ~ext u : A with (fun Γ => conv Σ Γ Conv))] ->
        [(IXtu : Σ ;;; Γ ⊢ t ~ext u : A on Xtu with (fun Γ t u A => forall v w pb' B T, Σ ;;; Γ ⊢ v <==[pb'] w : B -> Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->  Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B))] ->
        [(Xvw : Σ ;;; Γ ⊢ v ~ext w : B with (fun Γ => conv Σ Γ Conv))] ->
        [(XA : Σ ;;; Γ ⊢ A ≤* T)] ->
        [(XB : Σ ;;; Γ ⊢ B ≤* T)] ->
        Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B
  where "Σ ;;; Γ ⊢ t <==[ pb ] u | v <==[ pb' ] w : A ≤ T ≥ B" := (@conv2ε _ _ Σ Γ pb pb' t u v w A B T).
  Derive Signature for conv2ε.


Lemma conv2_eq_pb {cf} {TC} Σ Γ (pb pb' : conv_pb) (t u v w A B T : term) :
Σ ;;; Γ ⊢ t <==[Conv] u | v <==[pb'] w : A ≤ T ≥ B ->
Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B.
Proof.
revert Γ pb pb' t u v w A B T.
fix rec 11. intros * H.
assert (forall Γ t u A,
  (forall v w pb' B T, Σ ;;; Γ ⊢ v <==[pb'] w : B -> Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->
      Σ ;;; Γ ⊢ t <==[Conv] u | v <==[pb'] w : A ≤ T ≥ B) ->
  forall v w pb' B T,
    Σ ;;; Γ ⊢ v <==[pb'] w : B ->
    Σ ;;; Γ ⊢ A ≤* T ->
    Σ ;;; Γ ⊢ B ≤* T ->
    Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B).
{ intros ???? X **; apply rec, X; assumption. }
destruct H.
all: try solve [ econstructor; eauto ]; clear rec.
all: try solve [ econstructor; unshelve eauto with fmap ].
all: try solve [ econstructor; unshelve eauto using cumul_addon_clos_onε ].
Qed.



Lemma conv2_conv2 cf TC Σ Γ (pb pb' : conv_pb) (t u v w A B T : term) :
Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->
Σ ;;; Γ ⊢ t <==[pb] u : A ->
Σ ;;; Γ ⊢ v <==[pb'] w : B ->
Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B.
Proof.
intros XA XB Xuv Xvw.
have Xl : Acc (lexprod lt lt) (conv_length Xuv, conv_length Xvw).
{ apply acc_A_B_lexprod. all: try apply lt_wf. }
revert Γ pb pb' t u v w A B T XA XB Xuv Xvw Xl.
fix rec 15.
intros Γ pb pb' t u v w A B T XA XB Xuv Xvw Xl.

have {rec} IH : forall Γ pb pb' t u v w A B T,
  Σ ;;; Γ ⊢ A ≤* T -> Σ ;;; Γ ⊢ B ≤* T ->
  forall (Xuv' : Σ ;;; Γ ⊢ t <==[pb] u : A) (Xvw' : Σ ;;; Γ ⊢ v <==[pb'] w : B),
  lexprod lt lt (conv_length Xuv', conv_length Xvw') (conv_length Xuv, conv_length Xvw) ->
  Σ ;;; Γ ⊢ t <==[pb] u | v <==[pb'] w : A ≤ T ≥ B.
{ intros; eapply rec; tas. eapply Acc_inv; tea. }


destruct Xuv in pb', v, w, B, T, XA, XB, Xvw, IH; rename T0 into A.
5: { eapply conv2_cumul_l; tea. cbn in IH; unshelve eapply IH; eauto. 1: now eapply TCI_step. apply left_lex; unfold lt; reflexivity. }
- eapply conv2_hred_l; tea.
  cbn in IH; unshelve eapply IH; eauto.  apply left_lex; unfold lt; reflexivity.
- eapply conv2_hred_m1; tea.
  cbn in IH; unshelve eapply IH; eauto.  apply left_lex; unfold lt; reflexivity.
- set (Xuv0 := (ltac:(now econstructor) : Σ ;;; Γ ⊢ t <==[pb] u : A) ) in IH.
  rename t into a, u into b, pb into pb_.
  destruct Xvw; rename T0 into B; cbn -[Xuv0] in IH.
  5: { eapply conv2_cumul_r; tea. eapply IH; eauto. 1: now eapply TCI_step.  apply right_lex; unfold lt; reflexivity. }
  + eapply conv2_hred_m2; tea.
    eapply IH; eauto.  apply right_lex; unfold lt; reflexivity.
  + eapply conv2_hred_r; tea.
    eapply IH; eauto.  apply right_lex; unfold lt; reflexivity.
  + unshelve eapply conv2_ext_ext; tea.
    eapply ext_convε_length with (R_length := fun Γ => @conv_length _ _ _ Γ _) (H := e); tea.
    clear -IH.
    intros.
    apply conv2_eq_pb.
    unshelve eapply IH; tea.
    apply left_lex. cbn. lia.
  + unshelve eapply conv2_ext_cumul_addon; tea.
    eapply ext_convε_length with (R_length := fun Γ => @conv_length _ _ _ Γ _) (H := e); tea.
    clear -IH.
    intros.
    apply conv2_eq_pb.
    unshelve eapply IH; tea.
    apply left_lex. cbn. lia.
  + unshelve eapply conv2_ext_clos; tea.
    eapply ext_convε_length with (R_length := fun Γ => @conv_length _ _ _ Γ _) (H := e); tea.
    clear -IH.
    intros.
    apply conv2_eq_pb.
    unshelve eapply IH; tea.
    apply left_lex. cbn. lia.
- set (Xuv0 := (ltac:(now econstructor) : Σ ;;; Γ ⊢ t <==[pb] u : A) ) in IH.
  rename t into a, u into b, pb into pb_.
  destruct Xvw; rename T0 into B; cbn -[Xuv0] in IH.
  5: { eapply conv2_cumul_r; tea. eapply IH; eauto. 1: now eapply TCI_step.  apply right_lex; unfold lt; reflexivity. }
  + eapply conv2_hred_m2; tea.
    eapply IH; eauto.  apply right_lex; unfold lt; reflexivity.
  + eapply conv2_hred_r; tea.
    eapply IH; eauto.    apply right_lex; unfold lt; reflexivity.
  + unshelve eapply conv2_cumul_addon_ext; tea.
    eapply cumul_addonε_length with (R_length := @conv_length _ _ _) (H := c); tea.
    clear -IH.
    intros.
    unshelve eapply IH; tea.
    apply left_lex. cbn. lia.
  + unshelve eapply conv2_cumul_addon_cumul_addon; tea.
    eapply cumul_addonε_length with (R_length := @conv_length _ _ _) (H := c); tea.
    clear -IH.
    intros.
    unshelve eapply IH; tea.
    apply left_lex. cbn. lia.
  + unshelve eapply conv2_cumul_addon_clos; tea.
    eapply cumul_addonε_length with (R_length := @conv_length _ _ _) (H := c); tea.
    clear -IH.
    intros.
    unshelve eapply IH; tea.
    apply left_lex. cbn. lia.
- set (Xuv0 := (ltac:(now econstructor) : Σ ;;; Γ ⊢ t <==[pb] u : A) ) in IH.
  rename t into a, u into b, pb into pb_.
  destruct Xvw; rename T0 into B; cbn -[Xuv0] in IH.
  5: { eapply conv2_cumul_r; tea. eapply IH; eauto. 1: now eapply TCI_step.  apply right_lex; unfold lt; reflexivity. }
  + eapply conv2_hred_m2; tea.
    eapply IH; eauto.  apply right_lex; unfold lt; reflexivity.
  + eapply conv2_hred_r; tea.
    eapply IH; eauto.    apply right_lex; unfold lt; reflexivity.
  + unshelve eapply conv2_clos_ext; tea.
    eapply context_closureε_length with (R_length := fun Γ => @conv_length _ _ _ Γ _) (H := c); tea.
    clear -IH.
    intros.
    apply conv2_eq_pb.
    unshelve eapply IH; tea.
    apply left_lex. cbn. lia.
  + unshelve eapply conv2_clos_cumul_addon; tea.
    eapply context_closureε_length with (R_length := fun Γ => @conv_length _ _ _ Γ _) (H := c); tea.
    clear -IH.
    intros.
    apply conv2_eq_pb.
    unshelve eapply IH; tea.
    apply left_lex. cbn. lia.
  + unshelve eapply conv2_clos_clos; tea.
    eapply context_closureε_length with (R_length := fun Γ => @conv_length _ _ _ Γ _) (H := c); tea.
    clear -IH.
    intros.
    apply conv2_eq_pb.
    unshelve eapply IH; tea.
    apply left_lex. cbn. lia.
Qed.





Definition typing_inverted {TC} Σ Γ t T :=
  match t with
  | tRel n => ∑ decl, wf_local Σ Γ × nth_error Γ n = Some decl × Σ ;;; Γ ⊢ lift0 (S n) decl.(decl_type) ≤* T
  | tLambda na A t => ∑ B, lift_typing typing Σ Γ (j_vass na A) × Σ ;;; Γ ,, vass na A ⊢ t : B × Σ ;;; Γ ⊢ tProd na A B ≤* T
  | tApp t u => ∑ na A B, Σ ;;; Γ ⊢ t : tProd na A B × Σ ;;; Γ ⊢ u : A × Σ ;;; Γ ⊢ B {0 := u} ≤* T
  | tProd na A B => ∑ s s', lift_typing typing Σ Γ (j_vass_s na A s) × Σ ;;; Γ ,, vass na A ⊢ B : tSort s' × Σ ;;; Γ ⊢ tSort (Sort.sort_of_product s s') ≤* T
  | tSort s => wf_local Σ Γ × wf_sort Σ s × Σ ;;; Γ ⊢ tSort (Sort.super s) ≤* T
  | _ => False
  end.

Definition context_closure_inverted_l {TC} Σ R Rα Rs Γ t u T :=
  match t with
  | tRel n => u = tRel n × ∑ decl, wf_local Σ Γ × nth_error Γ n = Some decl × Σ ;;; Γ ⊢ lift0 (S n) decl.(decl_type) ≤* T
  | tLambda na A t => ∑ na' A' t', u = tLambda na' A' t' × ∑ s B, Rα na na' × R Γ A A' (tSort s) × isSortRel s na.(binder_relevance) × R (Γ ,, vass na A) t t' B × Σ ;;; Γ ⊢ tProd na A B ≤* T
  | tApp f a => ∑ f' a', u = tApp f' a' × ∑ na A B, R Γ f f' (tProd na A B) × R Γ a a' A × Σ ;;; Γ ⊢ B {0 := a} ≤* T
  | tProd na A B => ∑ na' A' B', u = tProd na' A' B' × ∑ s s', Rα na na' × R Γ A A' (tSort s) × isSortRel s na.(binder_relevance) × R (Γ ,, vass na A) B B' (tSort s') × Σ ;;; Γ ⊢ tSort (Sort.sort_of_product s s') ≤* T
  | tSort s => ∑ s', u = tSort s' × wf_local Σ Γ × wf_sort Σ s × wf_sort Σ s' × Rs s s' × Σ ;;; Γ ⊢ tSort (Sort.super s') ≤* T
  | _ => False
  end.

Definition equality_inverted_l {cf TC} Σ Γ pb t u T : Type :=
  (∑ T0, Σ ;;; Γ ⊢ T0 ≤* T × Σ ;;; Γ ⊢ t ~ext u : T0 with (fun Γ => equality Σ Γ Conv)) +
  match t with
  | tRel n => u = tRel n × ∑ decl, wf_local Σ Γ × nth_error Γ n = Some decl × Σ ;;; Γ ⊢ lift0 (S n) decl.(decl_type) ≤* T
  | tLambda na A t => ∑ na' A' t', u = tLambda na' A' t' × ∑ s B, eq_binder_annot na na' × equality Σ Γ Conv A A' (tSort s) × isSortRel s na.(binder_relevance) × equality Σ (Γ ,, vass na A) Conv t t' B × Σ ;;; Γ ⊢ tProd na A B ≤* T
  | tApp f a => ∑ f' a', u = tApp f' a' × ∑ na A B, equality Σ Γ Conv f f' (tProd na A B) × equality Σ Γ Conv a a' A × Σ ;;; Γ ⊢ B {0 := a} ≤* T
  | tProd na A B => ∑ na' A' B', u = tProd na' A' B' × ∑ s s', eq_binder_annot na na' × equality Σ Γ Conv A A' (tSort s) × isSortRel s na.(binder_relevance) × equality Σ (Γ ,, vass na A) pb B B' (tSort s') × Σ ;;; Γ ⊢ tSort (Sort.sort_of_product s s') ≤* T
  | tSort s => ∑ s', u = tSort s' × wf_local Σ Γ × wf_sort Σ s × wf_sort Σ s' × compare_sort Σ pb s s' × Σ ;;; Γ ⊢ tSort (Sort.super s') ≤* T
  | _ => False
  end.

Lemma typing_inverted_cumul TC Σ Γ t T U :
  typing_inverted Σ Γ t T ->
  Σ ;;; Γ ⊢ T ≤T U ->
  typing_inverted Σ Γ t U.
Proof.
  intros X XT.
  destruct t; tas.
  all: repeat destruct X as (? & X); repeat (eexists; tea).
  all: now eapply TCI_rstep.
Qed.

Lemma context_closure_inverted_l_cumul TC Σ R Rα Rs Γ t u T U :
  context_closure_inverted_l Σ R Rα Rs Γ t u T ->
  Σ ;;; Γ ⊢ T ≤T U ->
  context_closure_inverted_l Σ R Rα Rs Γ t u U.
Proof.
  intros X XT.
  destruct t; tas.
  all: repeat destruct X as (? & X); repeat (eexists; tea).
  all: now eapply TCI_rstep.
Qed.

Lemma equality_inverted_l_cumul cf TC Σ Γ pb t u T U :
  equality_inverted_l Σ Γ pb t u T ->
  Σ ;;; Γ ⊢ T ≤T U ->
  equality_inverted_l Σ Γ pb t u U.
Proof.
  intros [ (T0 & XT0 & X)|X] XT.
  { left; repeat eexists; tea. now eapply TCI_rstep. }
  right.
  destruct t; tas.
  all: repeat destruct X as (? & X); repeat (eexists; tea).
  all: now eapply TCI_rstep.
Qed.

Lemma typing_invert TC Σ Γ t T :
  Σ ;;; Γ ⊢ t : T -> typing_inverted Σ Γ t T.
Proof.
  induction 1 using typing_rect with (Pj := fun _ _ => True) (PΓ := fun _ => True) => //.
  - repeat (eexists; tea). constructor.
  - repeat (eexists; tea). constructor.
  - repeat (eexists; tea). constructor.
  - repeat (eexists; tea). constructor.
  - repeat (eexists; tea). constructor.
  - now eapply typing_inverted_cumul.
Qed.

Lemma context_closure_invert_l TC Σ R Rα Rs Γ t u T :
  Σ ;;; Γ ⊢ t ~ u : T with R, Rα, Rs ->
  context_closure_inverted_l Σ R Rα Rs Γ t u T.
Proof.
  induction 1 => //.
  - repeat (eexists; tea). constructor.
  - repeat (eexists; tea). constructor.
  - repeat (eexists; tea). constructor.
  - repeat (eexists; tea). constructor.
  - repeat (eexists; tea). constructor.
Qed.

Lemma pred1_invert_l TC Σ Γ t u T :
  Σ ;;; Γ ⊢ t ≡>1 u : T ->
  match t with tApp _ _ => false | _ => true end ->
  context_closure_inverted_l Σ (pred1 Σ) eq eq Γ t u T.
Proof.
  induction 1.
  - induction X => //.
  - intro.
    eapply context_closure_inverted_l_cumul; auto.
  - intro.
    now eapply context_closure_invert_l.
Qed.

Lemma equality_invert_l cf TC Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t <=[pb] u : T ->
  equality_inverted_l Σ Γ pb t u T.
Proof.
  induction 1.
  - left. repeat eexists; tea. constructor.
  - clear IX. right.
    induction X.
    all: repeat (eexists; tea); [constructor].
  - now eapply equality_inverted_l_cumul.
  - clear IX. right.
    induction X.
    all: try solve [repeat (eexists; tea); [constructor]].
    + repeat (eexists; tea); try apply TCI_refl.
      now apply equality_eq_pb.
    + repeat (eexists; tea); try apply TCI_refl.
      now apply compare_sort_subrel.
Qed.










Lemma pred1_rel_inv TC Σ Γ n u T : Σ ;;; Γ ⊢ tRel n ≡>1 u : T -> u = tRel n.
Proof.
  intro X.
  dependent induction X using pred1_elim.
  - depelim X.
  - by depelim X.
Qed.


Lemma pred0_eta_redex cf TC Σ (Pre : PredEqPrecondition cf TC Σ) Γ na A B t t' T' T :
  Σ ;;; Γ ⊢ t : tProd na A B -> Σ ;;; Γ ,, vass na A ⊢ B ≤* T -> Σ ;;; Γ ,, vass na A ⊢ T' ≤* T ->
  Σ ;;; Γ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ≡>0 t' : T' with (pred1 Σ) ->
  ∑ na₀ A₀ t₀, t = tLambda na₀ A₀ t₀ × Σ ;;; Γ,, vass na₀ A₀ ⊢ t₀ ≡>1 t' : T.
Proof.
  intros Ht HB HT' H.
  depelim H. rename T0 into T', na0 into na₀.
  assert (∑ A u, t = tLambda na₀ A u × A0 = lift0 1 A × t0 = lift 1 1 u) as (A₀ & u₀ & -> & -> & ->).
  { destruct t; noconf H. now eexists _, _. } clear H.
  repeat eexists.

  dependent induction Ht using typing_elim. clear IHHt.
  apply Prod_invert in X0 as (eqna & XA0A & XAA0 & XB).

  apply pred1_rel_inv in p0 as ->.
  eapply PE_strengthening_pred with (Γ' := [vass _ _]) in p as (u & T'' & -> & Hu & HT).
  eapply PE_cmp_inst' with (u := tRel 0) in HT.
  eapply TCI_trans in HT'; tea.
  eapply PE_change_context_self in HT'; tea. 2: symmetry; eassumption.
  eapply TCI_elim; tc; tea.
  rewrite !subst_rel0_lift; eassumption.
Qed.




Lemma pred1_eta cf TC Σ (Pre : PredEqPrecondition cf TC Σ) Γ pb t t' u TA TB T :
  Σ ;;; Γ ⊢ TA ≤* T ->
  Σ ;;; Γ ⊢ TB ≤* T ->
  Σ ;;; Γ ⊢ t ≡>1 u : TA ->
  [(Htt : Σ ;;; Γ ⊢ t =ext t' : TB with (fun Γ => equality Σ Γ Conv))] ->
  [(Xtt : Σ ;;; Γ ⊢ t =ext t' : TB on Htt with (fun Γ t t' A => forall pb u B T,
    Σ ;;; Γ ⊢ A ≤* T ->
    Σ ;;; Γ ⊢ B ≤* T ->
    Σ ;;; Γ ⊢ t ≡>1 u : B ->
    ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u <=[pb] u' : T))] ->
  ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u <=[pb] u' : T.
Proof.
  intros XA XB Xtu Htt Xtt.
  destruct Xtt.
  - dependent induction Xtu using pred1_elim.
    1: by depelim X.
    eapply TCI_trans in XA; tea. clear U XT.
    depelim X. subst na'.
    rename T1 into T, T0 into B', t0 into t, u0 into u.
    apply PE_shared_max_prod with (1 := XB) in XA0 as (T' & XBT' & XB'T' & XT'T); tea.
    specialize (IXR Conv _ _ _ XBT' XB'T' Xt) as (u' & Xuu' & Xt'u').
    dependent destruction Xt using pred1_elim.
    + depelim X. dependent induction XR using equality_elim; try by depelim X.
      1: admit.

      eapply pred0_eta_redex in X as (na₀ & A₀ & u₀ & -> & Xu₀); tea.
      depelim X. rename na0 into na₀.
      assert (∑ A t, u = tLambda na₀ A t × A0 = lift0 1 A × t0 = lift 1 1 t) as (A₀ & u₀ & -> & -> & ->).
      { destruct u; noconf H. now eexists _, _. }
      clear H.

    have [Hu'|Hu'] : {isLambda u} + {~~ isLambda u} by destruct (isLambda u); eauto.
    + assert (∑ na A t, u = tLambda na A t) as (na' & A₀ & u₀ & ->).
      { destruct u => //. now eexists _, _, _. }
      have {} Xuu' : Σ ;;; Γ ⊢ u₀ ≡>1 u' : T'.
      { clear -Xuu'.
        dependent induction Xuu' using pred1_elim.
        - depelim X.




       }
      eexists; split.
      * eapply TCI_elim; tc; eassumption.
      * eapply PE_change_proddom_pred in XA as XP.
        destruct XP as (XP & XP').
        eapply TCI_trans in XT'T; tea.
        eapply TCI_elim in
        eapply TCI_elim; tc; tea.
        eapply eq_ext, ext_eta_l.
        { apply typing_right in XA. repeat eexists; cbn; tea. }

    + apply PE_inv_eta_lift in Xuu' as (u'' & -> & Xuu'); tas. rename u'' into u'.
    eexists; split.
    + eapply TCI_elim; tc; eassumption.
    + eapply PE_change_proddom_pred in XA as XP.
      destruct XP as (XP & XP').
      eapply TCI_trans in XT'T; tea.
      eapply TCI_elim in
      eapply TCI_elim; tc; tea.
      eapply eq_ext, ext_eta_l.
      { apply typing_right in XA. repeat eexists; cbn; tea. }


    todo "".
  - rename u0 into t'.

    todo "".
  - exists u0; split.
    + apply trefl. eapply TCI_elim; tea; tc.
    + apply eq_ext, ext_eq_sprop.
      1,2: eapply TCI_elim; tc.
      * eapply typing_right; tc; tea. * assumption.
      * eassumption. * assumption.
      * apply PE_type_relevance with (r := Irrelevant) in XB.
        apply fst in XB.
        destruct XB as (_ & s & HT & _ & Hs).
        { repeat eexists; cbn; tea. reflexivity. }
        destruct s => //.
Qed.

Lemma pred0_eq cf TC Σ (Pre : PredEqPrecondition cf TC Σ) Γ pb t t' u A B T :
  Σ ;;; Γ ⊢ A ≤* T ->
  Σ ;;; Γ ⊢ B ≤* T ->
  [(Htu : Σ ;;; Γ ⊢ t ≡>0 u : A with pred1 Σ)] ->
  Σ ;;; Γ ⊢ t ≡>0 u : A on Htu with (fun Γ t u A => forall pb t' B T,
      Σ ;;; Γ ⊢ A ≤* T ->
      Σ ;;; Γ ⊢ B ≤* T ->
      Σ ;;; Γ ⊢ t <=[pb] t' : B ->
      ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u <=[pb] u' : T) ->
  Σ ;;; Γ ⊢ t <=[pb] t' : B ->
  ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u <=[pb] u' : T.
Proof.
  intros XA XB Htu Xtu Xtt.
  induction Xtu in B, T, XA, XB, t', Xtt; try rename T0 into A.
  -
    dependent induction Xtt using equality_elim; try now depelim X.
    { eapply pred1_eta in X; tc; revgoals; tas.
    - now apply pred1_pred0, pred0_beta.
    - eapply TCI_trans; eassumption.
    - assumption.
    - eassumption. }
    depelim X.
    eapply TCI_trans in XB; tea. clear U X0. move XB before XA.
    have XA0 : Σ ;;; Γ ⊢ A0 ≤* A.
    { apply typing_leftpb in Xt.
      dependent induction Xt using typing_elim. clear IHXt.
      now apply Prod_invert in X0 as (Xα & XA1A & XAA1 & XB1). }
    eapply TCI_elim in Xu; tc; tea.
    edestruct IXu as (u'' & IXu'' & IXu'''); trea. clear Xu0 Xu IXu.
    dependent induction Xt using equality_elim; try now depelim X.
    { eapply pred1_eta in X; tc; revgoals; tas.
    - eapply pred1_clos, clos_lambda; trea. 1: apply trefl, Xj.2.π2.1. apply Xj.2.π2.2.
    - eapply TCI_trans; eassumption.
    - assumption.
    - eassumption. }
    depelim X.
    apply Prod_invert in X0 as (Xα0 & XAA0 & XA0A & XB0).
    eapply TCI_elim in Xt; tc; tea. clear T0 XB0.
    apply typing_rightpb in XA as XA', Xt as Xt', Xu as Xu'.
    have [TT0 [XTT0 [XTT0' XTTs]]] : ∑ TT0, Σ ;;; Γ,, vass na A ⊢ T2 ≤* TT0 × Σ ;;; Γ,, vass na A ⊢ B ≤* TT0 × Σ ;;; Γ ⊢ TT0 {0 := u0} ≤* T1.
    { eapply PE_shared_max_type_subst.
    - now apply typing_left in Xt0.
    - now eapply typing_leftpb in Xt.
    - eassumption.
    - assumption. }
    eapply PE_change_subst_eq in XTTs as XTTs'; tea.
    eapply PE_change_subst_pred in XTTs as XTTs''; tea.
    edestruct IXt as (t'' & IXt'' & IXt'''); tea.
    apply PE_incl_conv in XA as XTA; destruct XTA as (XTA & XTA').
    edestruct IXu with (T := A') as (u'' & IXu'' & IXu'''); revgoals; tea; revgoals.
    { etransitivity; tea. }
    eexists; split.
    all: eapply TCI_elim; tc.
    + apply pred1_pred0, pred0_beta; tea.
      * repeat eexists; cbn; tea.
        now rewrite -Xα.
      * apply pred1_wf_local in Xu0.
        eapply change_context2; tea.
        apply convertible_contexts_snoc.
        1: repeat eexists; cbn; tea.
        1: eapply convertible_contexts_refl; tea.
        1: by apply treflpb.
        repeat eexists; cbn; tea. constructor.
    + assumption.
    + eapply TCI_elim in IXu'''; tc; tea.
      eapply PE_eq_subst; tea.
      now apply equality_eq_pb.
    + assumption.
Qed.

Lemma pred1_eq cf TC Σ Γ pb t t' u A B T :
  Σ ;;; Γ ⊢ A ≤* T ->
  Σ ;;; Γ ⊢ B ≤* T ->
  Σ ;;; Γ ⊢ t ≡>1 u : A ->
  Σ ;;; Γ ⊢ t <=[pb] t' : B ->
  ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u <=[pb] u' : T.
Proof.
  intros XA XB Xtu Xtt.
  induction Xtu in B, T, XA, XB, pb, t', Xtt; try rename T0 into A.
  -
  - admit.
  - destruct IX; dependent induction Xtu using pred1_elim; try now depelim X.
    + depelim X. subst na'.
      all: admit.
    + depelim X. subst s'.
      eexists; split.
      all: eapply TCI_elim; tea.
      1: now econstructor.
      * eapply pred1_clos, clos_sort; trea.
      * now econstructor.
      * eapply eq_cumul_addon, cumul_sort; trea.
  - eapply IHXtt; revgoals; tea.
    + now eapply TCI_step.
  - destruct IX; dependent induction Xtu using pred1_elim; try now depelim X.
    + depelim X.

    + depelim X. subst na'.

    + dependent induction Xtt using equality_elim.
      1: admit.
      1: by depelim X.
      depelim X.
      dependent induction Xt using equality_elim.
      1: admit.
      1: by depelim X.
      depelim X.

    induction Xtt.
    +
    + clear IX.

    + eapply IHXtt; tea. now econstructor.
    +
  - eapply IHXtu; tea.
    now econstructor.
  -

Inductive Acc2 {A B : Type} (R : A -> B -> A -> B -> Prop) x y : Prop :=
  Acc2_intro : (forall x' y', R x' y' x y -> Acc2 R x' y') -> Acc2 R x y.
Arguments Acc2_intro {_ _ _ _ _ _}.
Definition Acc2_inv {A B} {R} {x : A} {y : B} (a : Acc2 R x y) [x' y'] := let '(Acc2_intro f) := a in f x' y'.
Definition well_founded2 {A B} R := forall (x : A) (y : B), Acc2 R x y.

Notation "'precompose2'" := (fun R f x y x' y' => R (f x y) (f x' y')) (only parsing).

Lemma wf_precompose2 {A B M} (R : M -> M -> Prop) (m : A -> B -> M) :
  well_founded R -> well_founded2 (precompose2 R m).
Proof.
  intros X x y.
  remember (m x y) as a eqn:e.
  induction (X a) as [a _ IH] in e, x, y.
  constructor.
  rewrite -e => x' y' H.
  now eapply IH.
Defined.

Definition Fix_F2 [A B : Type] [R : A -> B -> A -> B -> Prop] [P : A -> B -> Type]
  (F : forall x y, (forall x' y', R x' y' x y -> P x' y') -> P x y) :=
  fix Fix_F2 x y (a : Acc2 R x y) {struct a} : P x y :=
    F x y (fun x' y' h => Fix_F2 x' y' (Acc2_inv a h)).

Inductive Acc3 {A B C : Type} (R : A -> B -> C -> A -> B -> C -> Prop) x y z : Prop :=
Acc3_intro : (forall x' y' z', R x' y' z' x y z -> Acc3 R x' y' z') -> Acc3 R x y z.
Arguments Acc3_intro {_ _ _ _ _ _ _ _}.
Definition Acc3_inv {A B C} {R} {x : A} {y : B} {z : C} (a : Acc3 R x y z) [x' y' z'] := let '(Acc3_intro f) := a in f x' y' z'.
Definition well_founded3 {A B C} R := forall (x : A) (y : B) (z : C), Acc3 R x y z.

Notation "'precompose3'" := (fun R f x y z x' y' z' => R (f x y z) (f x' y' z')) (only parsing).
About Acc_inv.
Lemma wf_precompose3 {A B C M} (R : M -> M -> Prop) (m : A -> B -> C -> M) :
well_founded R -> well_founded3 (precompose3 R m).
Proof.
intros X x y z.
remember (m x y z) as a eqn:e.
induction (X a) as [a _ IH] in e, x, y, z.
constructor.
rewrite -e => x' y' z' H.
now eapply IH.
Defined.

About Fix_F.

Definition Fix_F3 [A B C : Type] [R : A -> B -> C -> A -> B -> C -> Prop] [P : A -> B -> C -> Type]
(F : forall x y z, (forall x' y' z', R x' y' z' x y z -> P x' y' z') -> P x y z) :=
fix Fix_F3 x y z (a : Acc3 R x y z) {struct a} : P x y z :=
  F x y z (fun x' y' z' h => Fix_F3 x' y' z' (Acc3_inv a h)).


Fixpoint size_lambda t : nat :=
match t with
| tRel _ => 1
| tEvar ev args => S (list_size size_lambda args)
| tLambda na A t => 5 + (size_lambda A + size_lambda t)
| tApp u v => S (size_lambda u + size_lambda v)
| tProd na A B => S (size_lambda A + size_lambda B)
| tLetIn na b t b' => S (size_lambda b + size_lambda t + size_lambda b')
(* | tCase ind p c brs => S (predicate_size size_lambda p +
  size_lambda c + list_size (branch_size size_lambda) brs)
| tProj p c => S (size_lambda c)
| tFix mfix idx => S (mfixpoint_size size_lambda mfix)
| tCoFix mfix idx => S (mfixpoint_size size_lambda mfix) *)
| _ => 1
end.


Lemma eta_spine_left_equality_trans cf Σ Γ Γ' t u v args :
[(IH : forall Γ t' u' v',
  size_lambda t' + size_lambda u' + size_lambda v' <
  size_lambda t + size_lambda u + size_lambda v ->
  Σ ;;; Γ ⊢ t' =η u' -> Σ ;;; Γ ⊢ u' =η v' -> Σ ;;; Γ ⊢ t' =η u' =η v')] ->
[(X : Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ u · args)] ->
[(X' : Σ ;;; Γ ⊢ u =η v)] ->
Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ (u =η v) · args.
Proof.
intros IH X X'.
destruct X.
(* - eapply eta_spine_trans_left_sprop; tea. *)
- eapply eta_spine_trans_left_ground; trea.
  eapply IH; tea.
- eapply eta_spine_trans_left_push; trea.
  now eapply IHIX.
- eapply eta_spine_trans_left_pop; trea.
  now eapply IHIX.
Qed.

Lemma eta_spine_right_equality_trans cf Σ Γ Γ' t u v args :
let P Γ t u :=
(* match t with tLambda na A t =>
  forall u T₀, Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T
| _ => True
end × *)
  forall v, Σ ;;; Γ ⊢ t =η u -> Σ ;;; Γ ⊢ t =η u =η v
in
[(X : Σ ;;; Γ ⊢ t =η u)] ->
[(IX : Σ ;;; Γ ⊢ t =η u on X with P)] ->
[(X' : Σ ;;; Γ ;;; Γ' ⊢ ↑^ u · args =η v)] ->
Σ ;;; Γ ;;; Γ' ⊢ ↑^ (t =η u) · args =η v.
Proof.
intros * ? * ?.
induction X' in t, X, IX.
(* - eapply eta_spine_trans_right_sprop; tea. *)
- eapply eta_spine_trans_right_ground; trea.
  now eapply IXR.
- eapply eta_spine_trans_left_push; trea.
  now eapply IHIX.
- eapply eta_spine_trans_left_pop; trea.
  now eapply IHIX.
Qed.

(* Lemma eta_spine_right_pred1_equality cf TC Σ Q Γ Γ' t t' u args T T₀ :
let P Γ pb t t' T :=
  Q Γ pb t t' T ×
  forall u T₀, Σ ;;; Γ ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T
in
[(X : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' : T)] ->
[(IX : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' : T on X with
  fun Γ pb t t' T H => P Γ pb t t' T × eta_spineε Σ P Γ pb t t' T H)] ->
[(Xp : Σ ;;; Γ ⊢ t ≡>1 u : T₀)] ->
  Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' | ≡>1 u : T.
Proof.
intros * IX.
induction IX in u, T₀ => Xp.
- eapply pred1etar_sprop; tea.
  now eexists.
- eapply pred1etar_ground; trea.
  eapply IXR; tea.
  have {} Xp : Σ ;;; Γ ,,, Γ' ⊢ lift0 #|Γ'| t ≡>1 lift0 #|Γ'| u : lift0 #|Γ'| T₀ by admit.
  eassumption.
- eapply pred1etar_push; tea.
  now eapply IHIX.
- eapply pred1etar_pop; trea.
  now eapply IHIX.
Admitted. *)


(* Lemma eta_spine_right_pred1_equality_under cf TC Σ Q Γ Γ' na A t t' u args T T₀ :
let P Γ pb t t' T :=
  match t return Type with tLambda na A t =>
    forall u T₀, Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T
  | _ => True
  end × Q Γ pb t t' T
in
[(X : Σ ;;; Γ ;;; Γ' ⊢ ↑^ tLambda na A t · args =η t' : T)] ->
[(IX : Σ ;;; Γ ;;; Γ' ⊢ ↑^ tLambda na A t · args =η t' : T on X with
  fun Γ pb t t' T H => P Γ pb t t' T × eta_spineε Σ P Γ pb t t' T H)] ->
[(Xp : Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀)] ->
  Σ ;;; Γ ;;; Γ' ⊢ ↑^(λ(na : A), t) · args =η t' | ≡>1 u : T.
Proof.
intros * IX.
dependent induction IX => Xp.
- eapply pred1etar_sprop; tea.
  now eexists.
- eapply pred1etar_ground; trea.
  cbn in IXR.
  eapply IXR; tea.
  have {} Xp : Σ ;;; Γ ,,, Γ' ,, vass na (lift0 #|Γ'| A) ⊢ lift #|Γ'| 1 t0 ≡>1 lift #|Γ'| 1 u : lift #|Γ'| 1 T₀ by admit.
  eassumption.
- eapply pred1etar_push; tea.
  now eapply IHIX.
- eapply pred1etar_pop; trea.
  now eapply IHIX.
Admitted. *)




Theorem eq_trans_equality_trans cf Σ Γ t u v :
Σ ;;; Γ ⊢ t =η u ->
Σ ;;; Γ ⊢ u =η v ->
Σ ;;; Γ ⊢ t =η u =η v.
Proof.
assert (e : Acc3 (precompose3 lt (fun x y z => size_lambda x + size_lambda y + size_lambda z)) t u v)
  by apply wf_precompose3, lt_wf.
induction e using Fix_F3.
rename x into t, y into u, z into v, X into IH.
intros Htu Huv.
destruct Htu.
- apply eqtrans_etal.

- apply eqtrans_eta_mid.
- destruct IX.
  destruct IXt as (IXt & _).
-




Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ] t'" (at level 50, Γ, t, pb, t' at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]  t'").
Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ] t' 'on' H 'with' R'" (at level 50, Γ, t, pb, t', H at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]  t'  'on'  H  'with'  R'").
Reserved Notation "Σ  ;;; Γ ⊢ t = t'" (at level 50, Γ, t, t' at next level).
Reserved Notation "Σ  ;;; Γ ⊢ t = t' 'on' H 'with' R'" (at level 50, Γ, t, t', H at next level).


Inductive equality {cf} Σ Ξ t t' : Type :=
  | eq_eta :
      [(X : Σ ;;; Ξ ⊢ t =ext t' with equality Σ)] ->
      Σ ;;; Ξ ⊢ t = t'

  | eq_lambda :
      [(X : Σ ;;; Ξ ⊢ t =λ t' with equality Σ)] ->
      Σ ;;; Ξ ⊢ t = t'

  | eq_clos :
      [(X : Σ ;;; Ξ ⊢ t ~ t' with equality Σ, eq_binder_annot, eq_sort Σ)] ->
      Σ ;;; Ξ ⊢ t = t'

where "Σ ;;; Ξ ⊢ t = t'" := (equality Σ Ξ t t').
Derive Signature for equality.

Inductive equality_pb {cf} Σ Ξ pb t t' : Type :=
  | equality_to_pb :
    Σ ;;; Ξ ⊢ t = t' ->
    Σ ;;; Ξ ⊢ t <=[pb] t'

  | eq_pb_cumul_addon :
    Σ ;;; Ξ ⊢ t ≤c[pb] t' with equality_pb Σ ->
    Σ ;;; Ξ ⊢ t <=[pb] t'
where "Σ ;;; Ξ ⊢ t <=[ pb ] t'" := (equality_pb Σ Ξ pb t t').
Derive Signature for equality_pb.


Inductive equalityε {cf} Σ R' Ξ t t' : Σ ;;; Ξ ⊢ t = t' -> Type :=
  | eq_etaε :
      [(X : Σ ;;; Ξ ⊢ t =ext t' with equality Σ)] ->
      [(IX : Σ ;;; Ξ ⊢ t =ext t' on X with (fun Ξ t u H => R' Ξ t u × equalityε Σ R' Ξ t u H))] ->
      Σ ;;; Ξ ⊢ t = t' on ⌈eq_eta⌋ with R'

  | eqε_lambda :
      [(X : Σ ;;; Ξ ⊢ t =λ t' with equality Σ)] ->
      [(IX : Σ ;;; Ξ ⊢ t =λ t' on X with (fun Ξ t u H => R' Ξ t u × equalityε Σ R' Ξ t u H))] ->
      Σ ;;; Ξ ⊢ t = t' on ⌈eq_lambda⌋ with R'

  | eqε_clos :
      [(X : Σ ;;; Ξ ⊢ t ~ t' with equality Σ, eq_binder_annot, eq_sort Σ)] ->
      [(IX : Σ ;;; Ξ ⊢ t ~ t' on X with (fun Ξ t u H => R' Ξ t u × equalityε Σ R' Ξ t u H))] ->
      Σ ;;; Ξ ⊢ t = t' on ⌈eq_clos⌋ with R'

where "Σ ;;; Ξ ⊢ t = t' 'on' H 'with' R'" := (equalityε Σ R' Ξ t t' H).
Derive Signature for equalityε.

Definition equality_rect cf Σ P :
  [(Xrec Ξ t u H : Σ ;;; Ξ ⊢ t = u on H with P -> P Ξ t u)] ->
  forall Ξ t u, [(H : Σ ;;; Ξ ⊢ t = u)] -> P Ξ t u.
Proof.
  intros.
  unshelve eapply Xrec; tea.
  revert Ξ t u H. fix rec 4.
  destruct H.
  all: unshelve econstructor; unshelve eauto with fmap; eauto.
Defined.

Definition equality_pb_rect cf Σ P :
  [(Xbase Ξ pb t t' :
    [(X : Σ ;;; Ξ ⊢ t = t')] ->
    P Ξ pb t t')] ->

  [(XCumulAddon Ξ pb t t' :
    [(X : Σ ;;; Ξ ⊢ t ≤c[pb] t' with equality_pb Σ)] ->
    [(IX : Σ ;;; Ξ ⊢ t ≤c[pb] t' on X with (fun Ξ pb t u _ => P Ξ pb t u))] ->
    P Ξ pb t t')] ->
  forall Ξ pb t u, [(H : Σ ;;; Ξ ⊢ t <=[pb] u)] -> P Ξ pb t u.
Proof.
  intros.
  revert Ξ pb t u H. fix rec 5.
  destruct 1.
  - unshelve eapply Xbase; tea.
  - unshelve eapply XCumulAddon; tea.
    unshelve eauto with fmap; eauto.
Defined.


Lemma eta_spine_relevance {cf} Σ Ξ t u r :
  Σ ;;; Ξ ⊢ t = u ->
  isTermRel Σ Ξ t r <~> isTermRel Σ Ξ u r.
Proof.
  have XLam Ξ' na A t' r' : isTermRel Σ Ξ' (tLambda na A t') r' <~> isTermRel Σ (Ξ' ,, na.(binder_relevance)) t' r'.
  { split. 2: by constructor. intro H; by depelim H. }
  have XApp Ξ' t' u' r' : isTermRel Σ Ξ' (tApp t' u') r' <~> isTermRel Σ Ξ' t' r'.
  { split. 2: by constructor. intro H; by depelim H. }
  have XLift Ξ' r₀ t' r' : isTermRel Σ (Ξ' ,, r₀) (lift0 1 t') r' <~> isTermRel Σ Ξ' t' r'.
  { split. - intro H. by eapply isTermRel_unlift with (Ξ' := [_]) (Ξ'' := []) in H. - by eapply isTermRel_lift with (Ξ' := [_]) (Ξ'' := []). }

  intro H.
  induction H in r. destruct X.
  - destruct IX.
    + setoid_rewrite XLam.
      setoid_rewrite IXR.1.
      setoid_rewrite XApp.
      setoid_rewrite XLift.
      reflexivity.
    + setoid_rewrite XLam.
      setoid_rewrite <- IXR.1.
      setoid_rewrite XApp.
      setoid_rewrite XLift.
      reflexivity.
    + split; intro H.
      all: now eapply isTermRel_uniq in H as <-.
  - induction IX.
    setoid_rewrite XLam.
    rewrite -Xα.
    eapply IXt.
  - induction IX.
    all: try solve [ split; eauto ].
    + setoid_rewrite XLam.
      rewrite -Xα.
      eapply IXt.
    + setoid_rewrite XApp.
      apply IXt.
    + split; intro H; depelim H; constructor.
    + split; intro H; depelim H; constructor.
Qed.

(*
Lemma eta_invert cf TC Σ Γ t t' T :
  Σ ;;; Γ ⊢ t <=[Conv] t' : T ->
  Σ ;;; map (fun decl => decl.(decl_name).(binder_relevance)) Γ ⊢ t = t'.
Proof.
  revert Γ t t' T.
  fix rec 5.
  destruct 1.
  1: destruct X.
  - apply eta_left.
    eapply etal_push; trea.
    eapply eta_left_invert; tea.
    1: cbn; auto with arith.

  - apply eta_right.
    eapply etar_push; trea.
    eapply eta_right_invert; tea.
    1: cbn; auto with arith.

  - todo "untyped sprop".
  - eapply eta_clos; trea.
    todo "forget type".
  - eauto.
  - eapply eta_clos; trea.
    todo "forget type".
Qed.

Lemma eta_pb_invert cf TC Σ Γ pb t t' T :
  Σ ;;; Γ ⊢ t <=[pb] t' : T ->
  Σ ;;; Γ ⊢ t <=[pb]η t'.
Proof.
  induction 1.
  - constructor. eapply eta_invert. now constructor.
  - econstructor 2; trea.
    todo "forget type".
  - eauto.
  - constructor. eapply eta_invert. now constructor.
Qed. *)


Section equality_size.
Context {cf Σ}.
Section inner.
Variable (rec : forall Ξ t u, Σ ;;; Ξ ⊢ t = u -> nat).

Definition context_closure_size {Rα Rs R} {Ξ t u}
  (recR : forall Ξ t u, R Ξ t u -> nat)
  (H : Σ ;;; Ξ ⊢ t ~ u with R, Rα, Rs) : nat.
Proof.
  destruct H.
  all: apply S.
  + exact 0.
  + exact (recR _ _ _ XA + recR _ _ _ Xt).
  + exact (recR _ _ _ Xt + recR _ _ _ Xu).
  + exact (recR _ _ _ XA + recR _ _ _ XB).
  + exact 0.
Defined.

Definition eq_lambda_nodomain_size {R} {Ξ t u}
  (recR : forall Ξ t u, R Ξ t u -> nat)
  (H : Σ ;;; Ξ ⊢ t =λ u with R) : nat.
Proof.
  destruct H.
  apply S.
  exact (recR _ _ _ Xt).
Defined.

Definition ext_eq_size {R} {Ξ t u}
  (recR : forall Ξ t u, R Ξ t u -> nat)
  (H : Σ ;;; Ξ ⊢ t =ext u with R) : nat.
Proof.
  destruct H.
  all: apply S, S, S, S.
  1,2: exact (recR _ _ _ XR).
  exact 0.
Defined.

End inner.

Fixpoint equality_size {Ξ t u} (H : Σ ;;; Ξ ⊢ t = u) {struct H} : nat.
Proof.
  destruct H.
  all: apply S.
  - by apply ext_eq_size in X.
  - by apply eq_lambda_nodomain_size in X.
  - by apply context_closure_size in X.
Defined.

End equality_size.


(* Lemma equality_lift {cf Σ} (Γ Δ Γ' : relevance_context) t u :
  Σ ;;; Γ ,,, Γ' ⊢ t = u ->
  Σ ;;; Γ ,,, Δ ,,, Γ' ⊢ lift #|Δ| #|Γ'| t = lift #|Δ| #|Γ'| u.
Proof.
  intro H.
  set (Ξ := Γ ,,, Γ') in H.
  pose proof eq_refl : Ξ = Γ ,,, Γ' as e. clearbody Ξ.
  induction H in Γ', e; destruct X.
  - apply eq_eta.
    destruct IX.
    + cbn. constructor.
      rewrite permute_lift0.
      eapply IXR.1 with (Γ' := Γ' ,, _).
      by apply (f_equal2 snoc).
    + cbn. constructor.
      rewrite permute_lift0.
      eapply IXR.1 with (Γ' := Γ' ,, _).
      by apply (f_equal2 snoc).
    + constructor; subst Ξ.
      all: by apply isTermRel_lift.
  - apply eq_lambda.
    destruct IX.
    + cbn. constructor; tas.
      eapply IXt.1 with (Γ' := Γ' ,, _).
      by apply (f_equal2 snoc).
  - apply eq_clos.
    destruct IX.
    + cbn. constructor.
    + cbn. constructor; tas.
      * by eapply IXA.1.
      * eapply IXt.1 with (Γ' := Γ' ,, _).
        by apply (f_equal2 snoc).
    + cbn. constructor; tas.
      * by eapply IXt.1.
      * by eapply IXu.1.
    + cbn. constructor; tas.
      * by eapply IXA.1.
      * eapply IXB.1 with (Γ' := Γ' ,, _).
        by apply (f_equal2 snoc).
    + cbn. constructor; tas.
Defined. *)

Lemma equality_lift_size cf Σ (Γ Δ Γ' : relevance_context) t u :
  [(H : Σ ;;; Γ ,,, Γ' ⊢ t = u)] ->
  ∑ H' : Σ ;;; Γ ,,, Δ ,,, Γ' ⊢ lift #|Δ| #|Γ'| t = lift #|Δ| #|Γ'| u,
    equality_size H' = equality_size H.
Proof.
  revert Γ' t u.
  fix rec 4.
  destruct H; cbn.
  - destruct X; cbn.
    + epose proof (rec (_ ,, _) _ _ XR) as IXR.
      rewrite /= -permute_lift0 in IXR.
      unshelve eexists.
      1: do 2 constructor; apply IXR.π1.
      cbn. repeat f_equal. apply IXR.π2.
    + epose proof (rec (_ ,, _) _ _ XR) as IXR.
      rewrite /= -permute_lift0 in IXR.
      unshelve eexists.
      1: do 2 constructor; apply IXR.π1.
      cbn. repeat f_equal. apply IXR.π2.
    + unshelve eexists.
      1: do 2 constructor; by apply isTermRel_lift.
      cbnr.
  - destruct X; cbn.
    epose proof (rec (_ ,, _) _ _ Xt) as IXR.
    unshelve eexists.
    1: do 2 econstructor; tas; apply IXR.π1.
    cbn. repeat f_equal. apply IXR.π2.
  - destruct X; cbn.
    + unshelve eexists.
      1: by do 2 econstructor.
      cbnr.
    + epose proof (rec _ _ _ XA) as IXA.
      epose proof (rec (_ ,, _) _ _ Xt) as IXt.
      unshelve eexists.
      1: do 2 econstructor; tas; [apply IXA.π1|apply IXt.π1].
      cbn. repeat f_equal; [apply IXA.π2|apply IXt.π2].
    + epose proof (rec _ _ _ Xt) as IXt.
      epose proof (rec _ _ _ Xu) as IXu.
      unshelve eexists.
      1: do 2 econstructor; tas; [apply IXt.π1|apply IXu.π1].
      cbn. repeat f_equal; [apply IXt.π2|apply IXu.π2].
    + epose proof (rec _ _ _ XA) as IXA.
      epose proof (rec (_ ,, _) _ _ XB) as IXB.
      unshelve eexists.
      1: do 2 econstructor; tas; [apply IXA.π1|apply IXB.π1].
      cbn. repeat f_equal; [apply IXA.π2|apply IXB.π2].
    + unshelve eexists.
      1: by do 2 econstructor.
      cbnr.
Qed.




Reserved Notation "Σ  ;;; Ξ ⊢ t ~ u ~ v 'with' R" (at level 50, Ξ, t, u, v, R at next level).
Inductive context_closure_trans {cf} Σ R Ξ : forall (t u v : term), Type :=
  | clos_trans_rel n :
      Σ ;;; Ξ ⊢ tRel n ~ tRel n ~ tRel n with R

  | clos_trans_sort s s' s'' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : eq_sort Σ s s')] ->
      [(Xs' : eq_sort Σ s' s'')] ->
      Σ ;;; Ξ ⊢ tSort s ~ tSort s' ~ tSort s'' with R

  | clos_tri_lambda na na' na'' A A' A'' t t' t'' :
      [(Xα : eq_binder_annot na na')] ->
      [(Xα' : eq_binder_annot na' na'')] ->
      (* [(XA : R Ξ A A' A'')] -> *)
      [(Xt : R (Ξ ,, na.(binder_relevance)) t t' t'')] ->
      Σ ;;; Ξ ⊢ tLambda na A t ~ tLambda na' A' t' ~ tLambda na'' A'' t'' with R

  | clos_tri_app f f' f'' a a' a'' :
      [(Xt : R Ξ f f' f'')] ->
      [(Xu : R Ξ a a' a'')] ->
      Σ ;;; Ξ ⊢ tApp f a ~ tApp f' a' ~ tApp f'' a'' with R

  | clos_tri_prod na na' na'' A A' A'' B B' B'' :
      [(Xα : eq_binder_annot na na')] ->
      [(Xα' : eq_binder_annot na' na'')] ->
      [(XA : R Ξ A A' A'')] ->
      [(XT : R (Ξ ,, na.(binder_relevance)) B B' B'')] ->
      Σ ;;; Ξ ⊢ tProd na A B ~ tProd na' A' B' ~ tProd na'' A'' B'' with R
where "Σ ;;; Ξ ⊢ t ~ u ~ v 'with' R" := (context_closure_trans Σ R Ξ t u v).
Derive Signature for context_closure_trans.

Reserved Notation "Σ  ;;; Ξ ⊢ t ≤c[ pb ] u ≤c[ pb' ] v 'with' R" (at level 50, Ξ, pb, pb', t, u, v, R at next level).
Inductive cumul_addon_trans {cf} Σ R Ξ pb pb' : forall (t u v : term), Type :=
  | cumul_trans_sort s s' s'' :
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(wfs'': wf_sort Σ s'')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      [(Xs' : compare_sort Σ pb' s' s'')] ->
      Σ ;;; Ξ ⊢ tSort s ≤c[pb] tSort s' ≤c[pb'] tSort s'' with R

  | cumul_tri_prod na na' na'' A A' A'' B B' B'' :
      [(Xα : eq_binder_annot na na')] ->
      [(Xα' : eq_binder_annot na' na'')] ->
      [(XA : R Ξ Conv Conv A A' A'')] ->
      [(XT : R (Ξ ,, na.(binder_relevance)) pb pb' B B' B'')] ->
      Σ ;;; Ξ ⊢ tProd na A B ≤c[pb] tProd na' A' B' ≤c[pb'] tProd na'' A'' B'' with R
where "Σ ;;; Ξ ⊢ t ≤c[ pb ] u ≤c[ pb' ] v 'with' R" := (cumul_addon_trans Σ R Ξ pb pb' t u v).
Derive Signature for cumul_addon_trans.


Reserved Notation "Σ ;;; Ξ ⊢ t <=[ pb ] u <=[ pb' ] v" (at level 50, Ξ, pb, pb', t, u, v at next level, format "Σ  ;;;  Ξ  ⊢  t  <=[ pb ]  u  <=[ pb' ]   v").
Reserved Notation "Σ  ;;; Ξ ⊢ t = u = v" (at level 50, Ξ, t, u, v at next level).

Inductive equality_trans {cf} Σ Ξ : forall (t u v : term), Type :=
  (* closure vs closure *)
  | eqtrans_clos t u v :
      Σ ;;; Ξ ⊢ t ~ u ~ v with equality_trans Σ ->
      Σ ;;; Ξ ⊢ t = u = v

  (* sprop *)
  | eqtrans_sprop t u v :
      isTermRel Σ Ξ t Irrelevant ->
      isTermRel Σ Ξ u Irrelevant ->
      isTermRel Σ Ξ v Irrelevant ->
      Σ ;;; Ξ ⊢ t = u = v

  (* eta on the left *)
  | eqtrans_etal na A t u v :
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t = tApp (lift0 1 u) (tRel 0) = tApp (lift0 1 v) (tRel 0) ->
      Σ ;;; Ξ ⊢ tLambda na A t = u = v

  (* eta on the right *)
  | eqtrans_etar na A t u v :
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ tApp (lift0 1 t) (tRel 0) = tApp (lift0 1 u) (tRel 0) = v ->
      Σ ;;; Ξ ⊢ t = u = tLambda na A v

  | eqtrans_eta_mid_left na na' A A' t u v :
      eq_binder_annot na na' ->
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ tApp (lift0 1 t) (tRel 0) = u = v ->
      Σ ;;; Ξ ⊢ t = tLambda na A u = tLambda na' A' v

  | eqtrans_eta_mid_right na na' A A' t u v :
      eq_binder_annot na na' ->
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ t = u = tApp (lift0 1 v) (tRel 0) ->
      Σ ;;; Ξ ⊢ tLambda na A t = tLambda na' A' u = v

  | eqtrans_eta_mid_both na A t u v :
      Σ ;;; Ξ ,, na.(binder_relevance) ⊢ tApp (lift0 1 t) (tRel 0) = u = tApp (lift0 1 v) (tRel 0) ->
      Σ ;;; Ξ ⊢ t = tLambda na A u = v

where "Σ ;;; Ξ ⊢ t = u = v" := (@equality_trans _ Σ Ξ t u v).

Inductive equality_pb_trans {cf} Σ Ξ pb pb' : forall (t u v : term), Type :=
  (* closure vs closure *)
  | eqpbtrans_eqtrans t u v :
      Σ ;;; Ξ ⊢ t = u = v ->
      Σ ;;; Ξ ⊢ t <=[pb] u <=[pb'] v

  | eqpbtrans_cumul_addon t u v :
      Σ ;;; Ξ ⊢ t ≤c[pb] u ≤c[pb'] v with equality_pb_trans Σ ->
      Σ ;;; Ξ ⊢ t <=[pb] u <=[pb'] v
where "Σ ;;; Ξ ⊢ t <=[ pb ] u <=[ pb' ] v" := (@equality_pb_trans _ Σ Ξ pb pb' t u v).

Derive Signature for equality_trans equality_pb_trans.

