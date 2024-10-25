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
  Reserved Notation "Σ  ;;; Γ ⊢ t ≤[ pb ] t' : T " (at level 50, Γ, pb, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t = t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≤ t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≤[ pb ] t' : T 'with' TC" (at level 50, Γ, t, pb, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▹ T" (at level 50, Γ, t, T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▹□ u" (at level 50, Γ, t, u at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▹Π ( na , A , B )" (at level 50, Γ, t, na, A, B at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ▹{ ind } ( u , args )" (at level 50, Γ, t, ind, u, args at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ◃ T" (at level 50, Γ, t, T at next level).
  Reserved Notation "'wf_local_bd' Σ Γ" (at level 9, Σ, Γ at next level).
  Reserved Notation "'wf_local_bd_rel' Σ Γ Γ'" (at level 9, Σ, Γ, Γ' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>0 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>0 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>0 t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>0 t' : T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ext t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ext t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ext t' : T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =ext t' : T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~R' t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =R t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t =R' t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ ;;; Γ ⊢ t ≤R[ pb ] t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤R[ pb ]  t'  :  T").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤R'[ pb ] t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤R'[ pb ]  t'  :  T").
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~ t' : T 'with' R , R' , R'' " (at level 50, Γ, t, t', T, R, R', R'' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~1 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~1 t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~1 t' : T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~h1 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~h1 t' : T 'on' p 'with' R'" (at level 50, Γ, t, t', T, p, R' at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~h1 t' : T 'with' R " (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>1 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡>1 t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~> t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ≡> t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>h t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t ~>h* t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ  ;;; Γ ⊢ t h~> t' : T" (at level 50, Γ, t, t', T at next level).
  Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  :  T").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'on' p 'with' R'" (at level 50, Γ, t, pb, t', T, p, R' at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  :  T  'on'  p  'with'  R'").
  Reserved Notation "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'with' R " (at level 50, Γ, t, pb, t', T, R at next level, format "Σ  ;;;  Γ  ⊢  t  ≤c[ pb ]  t'  :  T  'with'  R").
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


Module typing_utils.
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

End typing_utils. Include typing_utils.

Module Substs.
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

End Substs. Include Substs.

Module ContextConversion.

  Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
  | rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
  | rel_none : rel_option R None None.

  Derive Signature NoConfusion for rel_option.

  Definition convertible_decls R R' (decl decl' : context_decl) :=
    rel_option (fun t u => R t u decl.(decl_type)) decl.(decl_body) decl'.(decl_body) ×
    eq_binder_annot decl.(decl_name) decl'.(decl_name) ×
    ∑ s, R' decl.(decl_type) decl'.(decl_type) (tSort s) ×
    isSortRel s decl.(decl_name).(binder_relevance).

  Definition convertible_contexts R : crelation context := All2_fold (fun Γ _ => convertible_decls (R Γ) (R Γ)).

  Notation "Σ ⊢ Γ = Δ 'with' R" := (convertible_contexts (R Σ) Γ Δ) (at level 80, Γ, Δ, R at next level).

  Lemma convertible_contexts_snoc R Γ Δ d d' :
    convertible_contexts R Γ Δ ->
    convertible_decls (R Γ) (R Γ) d d' ->
    convertible_contexts R (Γ ,, d) (Δ ,, d').
  Proof.
    intros.
    constructor; tas.
  Qed.

  Lemma convertible_contexts_refl P R Γ :
    [(typed_refl Γ t T : P Γ t T -> R Γ t t T)] ->
    All_local_env (lift_typing1 P) Γ -> convertible_contexts R Γ Γ.
  Proof.
    intro.
    induction 1; try apply convertible_contexts_snoc; auto.
    1: constructor.
    all: destruct t0 as (Hb & s & HT & Hs).
    all: repeat split; cbn; eauto.
    all: try now constructor.
    all: eexists; split; eauto.
    all: apply Hs.
  Qed.

  Definition cumulative_contexts R pb := All2_fold (fun Γ _ => convertible_decls (R Γ Conv) (R Γ pb)).

  Notation "Σ ⊢ Γ ≤[ pb ] Δ 'with' R" := (cumulative_contexts (R Σ) pb Γ Δ) (at level 80, pb, Γ, Δ, R at next level).

  Lemma cumulative_contexts_snoc R pb Γ Δ d d' :
    cumulative_contexts R pb Γ Δ ->
    convertible_decls (R Γ Conv) (R Γ pb) d d' ->
    cumulative_contexts R pb (Γ ,, d) (Δ ,, d').
  Proof.
    intros.
    constructor; tas.
  Qed.

  Lemma cumulative_contexts_refl P R pb Γ :
    [(typed_refl Γ pb t T : P Γ t T -> R Γ pb t t T)] ->
    All_local_env (lift_typing1 P) Γ -> cumulative_contexts R pb Γ Γ.
  Proof.
    intro.
    induction 1; try apply cumulative_contexts_snoc; auto.
    1: constructor.
    all: destruct t0 as (Hb & s & HT & Hs).
    all: repeat split; cbn; eauto.
    all: try now constructor.
    all: eexists; split; eauto.
    all: apply Hs.
  Qed.

  Definition convertible_decls_no_lets R (decl decl' : context_decl) :=
    eq_binder_annot decl.(decl_name) decl'.(decl_name) ×
    eq decl.(decl_body) decl'.(decl_body) ×
    R decl.(decl_type) decl'.(decl_type).

  Definition convertible_contexts_no_lets R : crelation context :=
    All2_fold (fun Γ _ => convertible_decls_no_lets (R Γ)).

  Lemma convertible_cumulable_contexts R Γ Δ :
    convertible_contexts (fun Γ => R Γ Conv) Γ Δ <~> cumulative_contexts R Conv Γ Δ.
  Proof.
    split; induction 1; constructor; eauto.
  Qed.

  Class ContextChangeable P R := {
    change_context : forall Γ Δ (t T : term),
      P Γ t T ->
      convertible_contexts R Γ Δ ->
      P Δ t T
  }.

  Class ContextChangeable2 P R := {
    change_context2 : forall Γ Δ (t u T : term),
      P Γ t u T ->
      convertible_contexts R Γ Δ ->
      P Δ t u T
  }.

  Class ContextChangeable2Pb P R := {
    change_context2pb : forall Γ Δ (pb : conv_pb) (t u T : term),
      P Γ pb t u T ->
      convertible_contexts R Γ Δ ->
      P Δ pb t u T
  }.

  Class ContextCumulable P R pb := {
    change_context_cumul : forall Γ Δ (t T : term),
      P Γ t T ->
      cumulative_contexts R pb Γ Δ ->
      P Δ t T
  }.

  Class ContextChangeableNoLets P R := {
    change_context_no_lets : forall Γ Δ (t T : term),
      P Γ t T ->
      convertible_contexts_no_lets R Γ Δ ->
      P Δ t T
  }.

  Instance ContextCumulable_to_Changeable P R :
    ContextCumulable P R Conv -> ContextChangeable P (fun Γ => R Γ Conv).
  Proof.
    constructor. intros ???? h H.
    rewrite -> convertible_cumulable_contexts in H.
    now eapply change_context_cumul.
  Qed.

End ContextConversion. Include ContextConversion.




(* Abstract relation to compare types, to reduce to products and to sorts *)


Class TypeComparator := { TCit : forall (Σ : global_env_ext) (Γ : context) (T T' : term), Type }.
Class RedtoPi := { RTPit : forall (Σ : global_env_ext) (Γ : context) (T : term) (na : aname) (A B : term), Type }.
Class RedtoSort := { RTSit : forall (Σ : global_env_ext) (Γ : context) (T : term) (s : sort), Type }.
Coercion TCit : TypeComparator >-> Funclass.
Coercion RTPit : RedtoPi >-> Funclass.
Coercion RTSit : RedtoSort >-> Funclass.

Implicit Types (TC : TypeComparator) (RtP : RedtoPi) (RtS : RedtoSort).

Notation " Σ  ;;; Γ ⊢ T ≤T T' " := (@TCit _ Σ Γ T T') (at level 50, Γ, T, T' at next level).
Notation " Σ  ;;; Γ ⊢ T ≤T T' 'with' TC" := (@TCit TC Σ Γ T T') (at level 50, Γ, T, T', TC at next level, only parsing).


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

  | type_App t na A B s u :
      (* Paranoid assumption, allows to show equivalence with template-coq,
        but eventually unnecessary thanks to validity. *)
      Σ ;;; Γ ⊢ tProd na A B : tSort s ->
      Σ ;;; Γ ⊢ t : tProd na A B ->
      Σ ;;; Γ ⊢ u : A ->
      Σ ;;; Γ ⊢ tApp t u : B {0 := u}

  | type_cumul t A B :
      Σ ;;; Γ ⊢ t : A ->
      Σ ;;; Γ ⊢ A ≤T B ->
      Σ ;;; Γ ⊢ t : B

where " Σ ;;; Γ ⊢ t : T " := (typing Σ Γ t T)
and "'wf_local' Σ Γ " := (All_local_env (lift_typing typing Σ) Γ).
Derive Signature for typing.

Notation " Σ  ;;; Γ ⊢ t : T 'with' TC" := (@typing TC Σ Γ t T) (at level 50, Γ, t, T at next level, only parsing).
Notation "'wf_local' Σ Γ 'with' TC" := (All_local_env (lift_typing1 (@typing TC Σ)) Γ) (at level 9, Σ, Γ, TC at next level, only parsing).

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

  [(XApp Γ t na A B s u :
      (* Paranoid assumption, allows to show equivalence with template-coq,
        but eventually unnecessary thanks to validity. *)
      Σ ;;; Γ ⊢ tProd na A B : tSort s ->
      P Γ (tProd na A B) (tSort s) ->
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
  intros Γ t_ T_ []; try clear t_; try clear T_.
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

  [(XApp Γ t na A B s u T :
      (* Paranoid assumption, allows to show equivalence with template-coq,
        but eventually unnecessary thanks to validity. *)
      Σ ;;; Γ ⊢ tProd na A B : tSort s ->
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
Context {TC} {RtP} {RtS}.

Inductive infering (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
  | infer_Rel n decl :
    nth_error Γ n = Some decl ->
    Σ ;;; Γ ⊢ tRel n ▹ lift0 (S n) (decl_type decl)

  | infer_Sort s :
    wf_sort Σ s ->
    Σ ;;; Γ ⊢ tSort s ▹ tSort (Sort.super s)

  | infer_Prod na A B s1 s2 :
    lift_sorting (checking Σ Γ) (infering_sort Σ Γ) (j_vass_s na A s1) ->
    Σ ;;; Γ ,, vass na A ⊢ B ▹□ s2 ->
    Σ ;;; Γ ⊢ tProd na A B ▹ tSort (Sort.sort_of_product s1 s2)

  | infer_Lambda na A t B :
    lift_sorting (checking Σ Γ) (infering_sort Σ Γ) (j_vass na A) ->
    Σ ;;; Γ ,, vass na A ⊢ t ▹ B ->
    Σ ;;; Γ ⊢ tLambda na A t ▹ tProd na A B

  | infer_App t na A B u :
    Σ ;;; Γ ⊢ t ▹Π (na,A,B) ->
    Σ ;;; Γ ⊢ u ◃ A ->
    Σ ;;; Γ ⊢ tApp t u ▹ B{0 := u}

with infering_sort (Σ : global_env_ext) (Γ : context) : term -> sort -> Type :=
  | infer_sort_Sort t T u:
    Σ ;;; Γ ⊢ t ▹ T ->
    RtS Σ Γ T u ->
    Σ ;;; Γ ⊢ t ▹□ u

with infering_prod (Σ : global_env_ext) (Γ : context) : term -> aname -> term -> term -> Type :=
  | infer_prod_Prod t T na A B:
    Σ ;;; Γ ⊢ t ▹ T ->
    RtP Σ Γ T na A B ->
    Σ ;;; Γ ⊢ t ▹Π (na,A,B)

with checking (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
  | check_Cumul t T T':
    Σ ;;; Γ ⊢ t ▹ T ->
    Σ ;;; Γ ⊢ T ≤T T' ->
    Σ ;;; Γ ⊢ t ◃ T'

where " Σ ;;; Γ ⊢ t ▹ T " := (@infering Σ Γ t T) : type_scope
and " Σ ;;; Γ ⊢ t ▹□ u " := (@infering_sort Σ Γ t u) : type_scope
and " Σ ;;; Γ ⊢ t ▹Π ( na , A , B ) " := (@infering_prod Σ Γ t na A B) : type_scope
and " Σ ;;; Γ ⊢ t ◃ T " := (@checking Σ Γ t T) : type_scope
and "'wf_local_bd' Σ Γ" := (All_local_env (lift_sorting1 (checking Σ) (infering_sort Σ)) Γ)
and "'wf_local_bd_rel' Σ Γ Γ'" := (All_local_rel (lift_sorting1 (checking Σ) (infering_sort Σ)) Γ Γ').
End BD.
Derive Signature for infering checking infering_prod infering_sort.

(* BD Renotations *)
  Notation " Σ ;;; Γ ⊢ t ▹ T " := (@infering _ _ _ Σ Γ t T) : type_scope.
  Notation " Σ ;;; Γ ⊢ t ▹□ u " := (@infering_sort _ _ _ Σ Γ t u) : type_scope.
  Notation " Σ ;;; Γ ⊢ t ▹Π ( na , A , B ) " := (@infering_prod _ _ _ Σ Γ t na A B) : type_scope.
  Notation " Σ ;;; Γ ⊢ t ◃ T " := (@checking _ _ _ Σ Γ t T) : type_scope.
  Notation "'wf_local_bd' Σ Γ" := (All_local_env (lift_sorting1 (checking Σ) (infering_sort Σ)) Γ).
  Notation "'wf_local_bd_rel' Σ Γ Γ'" := (All_local_rel (lift_sorting1 (checking Σ) (infering_sort Σ)) Γ Γ').
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
  BDXinferprod : forall Γ T na A B, Σ ;;; Γ ⊢ T ▹Π ( na , A , B ) -> Pinferprod Γ T na A B;
  BDXinfersort : forall Γ T s, Σ ;;; Γ ⊢ T ▹□ s -> Pinfersort Γ T s;
  BDXΓ : forall Γ, wf_local_bd Σ Γ -> PΓ Γ;
  BDXΓrel : forall Γ Δ, wf_local_bd_rel Σ Γ Δ -> PΓrel Γ Δ;
}.

Definition bidir_ind TC RtP RtS Σ (P : BidirTypingElimType) :
  [(Xj Γ j : lift_sorting (checking Σ Γ) (infering_sort Σ Γ) j -> lift_sorting (Pcheck Γ) (Pinfersort Γ) j -> Pj Γ j)] ->
  [(XΓ Γ   : wf_local_bd Σ Γ -> All_local_env Pj Γ -> PΓ Γ)] ->
  [(XΓrel Γ Δ : wf_local_bd_rel Σ Γ Δ -> All_local_rel Pj Γ Δ -> PΓrel Γ Δ)] ->
  [(XRel Γ n decl :
      nth_error Γ n = Some decl ->
      Pinfer Γ (tRel n) (lift0 (S n) decl.(decl_type)))] ->
  [(XSort Γ s :
      wf_sort Σ s ->
      Pinfer Γ (tSort s) (tSort (Sort.super s)))] ->

  [(XProd Γ na A B s1 s2 :
      lift_sorting (checking Σ Γ) (infering_sort Σ Γ) (j_vass_s na A s1) ->
      Pj Γ (j_vass_s na A s1) ->
      Σ ;;; Γ ,, vass na A ⊢ B ▹□ s2 ->
      Pinfersort (Γ ,, vass na A) B s2 ->
      Pinfer Γ (tProd na A B) (tSort (Sort.sort_of_product s1 s2)))] ->

  [(XLambda Γ na A t B :
      lift_sorting (checking Σ Γ) (infering_sort Σ Γ) (j_vass na A) ->
      Pj Γ (j_vass na A) ->
      Σ ;;; Γ ,, vass na A ⊢ t ▹ B ->
      Pinfer (Γ ,, vass na A) t B ->
      Pinfer Γ (tLambda na A t) (tProd na A B))] ->

  [(XApp Γ t na A B u :
      Σ ;;; Γ ⊢ t ▹Π(na, A, B) ->
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
  assert (XInferProd' : XrecT -> forall Γ t na A B, Σ ;;; Γ ⊢ t ▹Π (na, A, B) -> Pinferprod Γ t na A B).
  { intros Xrec Γ t na A B []. eauto. }
  assert (XInferSort' : XrecT -> forall Γ T s, Σ ;;; Γ ⊢ T ▹□ s -> Pinfersort Γ T s).
  { intros Xrec Γ t s []. eauto. }
  assert (XCumul' : XrecT -> forall Γ t T, Σ ;;; Γ ⊢ t ◃ T -> Pcheck Γ t T).
  { intros Xrec Γ t T []. eauto. }
  assert (Xj' : XrecT -> forall Γ j, lift_sorting (checking Σ Γ) (infering_sort Σ Γ) j -> Pj Γ j).
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

Theorem infer_to_typing {cf} {TC} {RtP} {RtS} Σ (X : BidirToTypingPrecondition TC RtP RtS Σ) :
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
  - econstructor; eauto.
    Unshelve. all: todo "decide whether we keep additional hypothesis in tApp".
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
    TC_prod_construct Γ na A B B' : Σ ;;; Γ ,, vass na A ⊢ B ≤T B' -> Σ ;;; Γ ⊢ tProd na A B ≤T tProd na A B';
    TC_prod_invert Γ T na' A' B' : Σ ;;; Γ ⊢ T ≤T tProd na' A' B' -> ∑ na A B, RtP Σ Γ T na A B × Σ ;;; Γ ⊢ A' ≤T A × Σ ;;; Γ ,, vass na A ⊢ B ≤T B';
    TC_sort_invert Γ T s' : Σ ;;; Γ ⊢ T ≤T tSort s' -> ∑ s, RtS Σ Γ T s × Σ ;;; Γ ⊢ tSort s ≤T tSort s'
  }.
Arguments TypingBidirPrecondition : clear implicits.

Theorem typing_to_check {cf} {TC} {RtP} {RtS} Σ (X : TypingBidirPrecondition TC RtP RtS Σ) :
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
  - destruct IHtyping as (_ & s & Hs1 & <- & Hrel); cbn in *.
    depelim IHtyping0.
    destruct (TC_sort_invert _ _ _ t0) as (s20 & HRtS & HT).
    depelim Hs1.
    destruct (TC_sort_invert _ _ _ t0) as (s10 & HRtS0 & HT0).
    econstructor. 1: econstructor.
    + repeat (eexists; cbn; tea).
      rewrite -Hrel.
      now eapply TC_sort_relevance.
    + econstructor; tea.
    + now eapply TC_sort_of_product.
  - destruct IHtyping as (_ & s & Hs1 & _ & Hrel); cbn in *.
    depelim IHtyping0.
    depelim Hs1.
    destruct (TC_sort_invert _ _ _ t1) as (s10 & HRtS0 & HT0).
    econstructor. 1: econstructor.
    + repeat (eexists; cbn; tea).
      rewrite -Hrel.
      now eapply TC_sort_relevance.
    + eassumption.
    + now eapply TC_prod_construct.
  - depelim IHtyping2.
    destruct (TC_prod_invert _ _ _ _ _ t1) as (na0 & A0' & B0 & HRtS & HTA & HTB).
    depelim IHtyping3.
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
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ≡>0 t' { 0 := u' } : T { 0 := u } on (ltac:(now eapply pred0_beta)) with R'
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
      Σ ;;; Γ ⊢ t ~ext u : tProd na A B on ltac:(now eapply ext_eta) with R'

  | extε_sprop t u T :
      [(Xt : Σ ;;; Γ ⊢ t : T)] ->
      [(Xu : Σ ;;; Γ ⊢ u : T)] ->
      [(XT : Σ ;;; Γ ⊢ T : tSort sSProp)] ->
      Σ ;;; Γ ⊢ t ~ext u : T on ltac:(now eapply ext_sprop) with R'
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
      Σ ;;; Γ ⊢ tLambda na A t =ext u : tProd na A B on ltac:(now eapply ext_eta_l) with R'

  | extε_eta_r t u na A B :
      [(Xj : lift_typing typing Σ Γ (j_vass na A))] ->
      [(Xt : Σ ;;; Γ ⊢ t : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ,, vass na A ⊢ u : B)] ->
      [(XR : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ~R u : B)] ->
      [(IXR : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ~R' u : B)] ->
      Σ ;;; Γ ⊢ t =ext tLambda na A u : tProd na A B on ltac:(now eapply ext_eta_r) with R'

  | extε_eq_sprop t u T :
      [(Xt : Σ ;;; Γ ⊢ t : T)] ->
      [(Xu : Σ ;;; Γ ⊢ u : T)] ->
      [(XT : Σ ;;; Γ ⊢ T : tSort sSProp)] ->
      Σ ;;; Γ ⊢ t =ext u : T on ltac:(now eapply ext_eq_sprop) with R'
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
      Σ ;;; Γ ⊢ tRel n ~ tRel n : lift0 (S n) decl.(decl_type) on ltac:(now eapply clos_rel) with R'

  | closε_lambda na na' A A' t t' T s :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T)] ->
      [(IXt : Σ ;;; Γ ,, vass na A ⊢ t ~R' t' : T)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' : tProd na A T on ltac:(now eapply clos_lambda) with R'

  | closε_app na A B t t' u u' :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' : tProd na A B)] ->
      [(IXt : Σ ;;; Γ ⊢ t ~R' t' : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' : A)] ->
      [(IXu : Σ ;;; Γ ⊢ u ~R' u' : A)] ->
      Σ ;;; Γ ⊢ tApp t u ~ tApp t' u' : B { 0 := u } on ltac:(now eapply clos_app) with R'

  | closε_prod na na' A A' B B' s s' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B' : tSort s')] ->
      [(IXB : Σ ;;; Γ ,, vass na A ⊢ B ~R' B' : tSort s')] ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B' : tSort (Sort.sort_of_product s s') on ltac:(now eapply clos_prod) with R'

  | closε_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' : tSort (Sort.super s') on ltac:(eapply clos_sort; eassumption) with R'
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
      Σ ;;; Γ ⊢ tLambda na A t ~1 tLambda na A' t : tProd na A T on ltac:(now eapply clos1_lamty) with R'

  | clos1ε_lamtm na A t t' T :
      [(Xj : lift_typing typing Σ Γ (j_vass na A))] ->
      [(XA : Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T)] ->
      [(IXA : Σ ;;; Γ ,, vass na A ⊢ t ~R' t' : T)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~1 tLambda na A t' : tProd na A T on ltac:(now eapply clos1_lamtm) with R'

  | clos1ε_appl na A B t t' u :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' : tProd na A B)] ->
      [(IXt : Σ ;;; Γ ⊢ t ~R' t' : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ⊢ u : A)] ->
      Σ ;;; Γ ⊢ tApp t u ~1 tApp t' u : B { 0 := u } on ltac:(now eapply clos1_appl) with R'

  | clos1ε_appr na A B t u u' :
      [(Xt : Σ ;;; Γ ⊢ t : tProd na A B)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' : A)] ->
      [(IXu : Σ ;;; Γ ⊢ u ~R' u' : A)] ->
      Σ ;;; Γ ⊢ tApp t u ~1 tApp t u' : B { 0 := u } on ltac:(now eapply clos1_appr) with R'

  | clos1ε_proddom na A A' B s s' :
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B : tSort s')] ->
      Σ ;;; Γ ⊢ tProd na A B ~1 tProd na A' B : tSort (Sort.sort_of_product s s') on ltac:(now eapply clos1_proddom) with R'

  | clos1ε_prodcodom na A B B' s s' :
      [(Xj : lift_typing typing Σ Γ (j_vass_s na A s))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B' : tSort s')] ->
      [(IXB : Σ ;;; Γ ,, vass na A ⊢ B ~R' B' : tSort s')] ->
      Σ ;;; Γ ⊢ tProd na A B ~1 tProd na A B' : tSort (Sort.sort_of_product s s') on ltac:(now eapply clos1_prodcodom) with R'
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
      Σ ;;; Γ ⊢ tApp t u ~h1 tApp t' u : B { 0 := u } on ltac:(now eapply hclos1_appl) with R'
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

Instance TC_compat_hred TC Σ Γ t u : TC_compat TC Σ Γ (hred Σ Γ t u). by now econstructor. Defined.

Definition hred_rect cf TC Σ P :
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
      Σ ;;; Γ ⊢ tProd na A B ≤c[pb] tProd na' A' B' : tSort (Sort.sort_of_product s s') on ltac:(now eapply cumul_prod) with R'

  | cumulε_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs' : wf_sort Σ s')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      Σ ;;; Γ ⊢ tSort s ≤c[pb] tSort s' : tSort (Sort.super s') on ltac:(now eapply cumul_sort) with R'
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
  remember Conv as pb eqn:e in X. revert e.
  induction X => e; subst pb.
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
    CTT_change_context :: ContextChangeable (typing Σ) (fun Γ t u T => Σ ;;; Γ ⊢ t ≡ u : T);
    CTT_typed_reflexivity :: TypedReflexivity (fun Γ t u T => Σ ;;; Γ ⊢ t ≡ u : T) Σ;
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
    1: by todo "Additional hypothesis for tApp".
    econstructor; tea.
    Unshelve. by todo "Additional hypothesis for tApp".
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
    Unshelve. all: by todo "Additional hypothesis for tApp".
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
    Unshelve. all: by todo "Additional hypothesis for tApp".
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

Lemma cumul_addon_typing_right {cf TC} Σ P P'
  (CC : ContextChangeable (typing Σ) (fun Γ t u T => P Γ Conv t u T))
  (TR : TypedReflexivity (fun Γ t u T => P Γ Conv t u T) Σ)
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
    apply convertible_contexts_snoc.
    1: eapply convertible_contexts_refl.
    + intros.
      now apply treflpb.
    + now eapply typing_wf_local.
    + repeat eexists; cbn; tea.
      constructor.
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
    * todo "Additional hypothesis for tApp".
      Unshelve. all: todo "Additional hypothesis for tApp".
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

Lemma context_closure_typing_right {cf TC} Σ P P'
  (CC : ContextChangeable (typing Σ) P)
  (TR : TypedReflexivity P Σ)
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
      apply convertible_contexts_snoc.
      1: eapply convertible_contexts_refl.
      * now apply trefl.
      * now eapply typing_wf_local.
      * repeat eexists; cbn; tea.
        constructor.
    + now eapply TC_from_compare_prod.
  - econstructor; eauto.
    1: econstructor; eauto.
    * todo "Additional hypothesis for tApp".
      Unshelve. all: todo "Additional hypothesis for tApp".
    * now eapply TC_from_compare_subst10.
  - apply onP' in IXA, IXB.
    have Xj' : lift_typing typing Σ Γ (j_vass_s na' A' s).
    { repeat eexists; tea. rewrite /= -Xα //. }
    constructor; tas.
    eapply change_context; tea.
    apply convertible_contexts_snoc.
    1: eapply convertible_contexts_refl.
    + intros.
      now apply trefl.
    + now eapply typing_wf_local.
    + repeat eexists; cbn; tea.
      constructor.
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
  have [s' XProd] : ∑ s', Σ ;;; Γ ⊢ tProd na A B : tSort s'.
  { todo "Additional hypothesis for app". }
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
    - eapply XL in X2. eassumption.
    - now apply XL in XProd. }

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
  CSP_context_change :: ContextChangeable2Pb (conv Σ) (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T);
  CSP_typed_refl :: TypedConvReflexivity (conv Σ) Σ Conv;
  CSP_cmp_sort pb :: TCFromCompareSort Σ (compare_sort Σ pb);
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

Lemma eta_ext_sym {TC} Σ R Γ t u T :
  Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ t u T => R Γ u t T) ->
  Σ ;;; Γ ⊢ u ~ext t : T with R.
Proof.
  induction 1.
  all: try now econstructor.
Qed.

Lemma context_closure_conv_sym {cf} {TC} Σ (PC : ConvSymPrecondition cf TC Σ) Γ t u T :
  [(X : Σ ;;; Γ ⊢ t ~ u : T with (fun Γ t u T => Σ ;;; Γ ⊢ t === u : T), eq_binder_annot, eq_sort Σ)] ->
  [(IX : Σ ;;; Γ ⊢ t ~ u : T on X with (fun Γ t u T => Σ ;;; Γ ⊢ u === t : T))] ->
  Σ ;;; Γ ⊢ u === t : T.
Proof.
  intros X IX.
  induction IX.
  - now apply conv_clos, clos_rel.
  - eapply conv_cumul.
    1: eapply conv_clos, clos_lambda; tea.
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
    + eapply TC_from_compare_sort; tea.
      1,2: by apply wf_sort_super.
      instantiate (1 := Conv).
      now apply TC_super.
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
  - now eapply context_closure_conv_sym.
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
  PC_TypedRefl :: TypedReflexivity (pred1 Σ) Σ;
  PC_LeftTyping :: LeftTyping (pred1 Σ) Σ;
  PC_cmp_subst10 :: TCFromCompareSubst10 Σ (pred1 Σ);
  PC_context_change :: ContextChangeable2 (pred1 Σ) (pred1 Σ);
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
      1: todo "Additional argument to tApp".
      constructor; tas.
      Unshelve. 1: todo "Additional argument to tApp".
  - now econstructor.
  - apply context_closure_ofε in X; clear H.
    eapply context_closure_typing_left; tea.
    auto.
Qed.

Lemma context_closure_retyping {TC} Σ Pα P P' Γ t u T T' :
  [(onP Γ t u T T' : P Γ t u T -> Σ ;;; Γ ⊢ t : T' -> P' Γ t u T')] ->
  [(X : Σ ;;; Γ ⊢ t ~ u : T with P, Pα, eq)] ->
  Σ ;;; Γ ⊢ t : T' ->
  ∑ T0, Σ ;;; Γ ⊢ T0 ≤* T' ×
  Σ ;;; Γ ⊢ t ~ u : T0 with P', Pα, eq.
Proof.
  intros onP X X'.
  induction X in X', T'.
  all: dependent induction X' using typing_elim.
  all: eexists; split; [eassumption|].
  - now econstructor.
  - destruct X as (_ & s' & XA' & _ & Xs').
    econstructor; now eauto.
  - econstructor; eauto.
  - destruct X as (_ & s1' & XA' & <- & Xs').
    econstructor; now eauto.
  - econstructor; eauto.
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
      dependent induction X'2 using typing_elim.
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
  - induction X.
    + apply pred1_clos; now econstructor.
    + eapply pred1_cumul.
      * apply pred1_clos.
        subst na'; cbn.
        eapply clos_lambda; trea.
        eapply change_context2; tea.
        eapply convertible_contexts_snoc.
        1: eapply convertible_contexts_refl.
        1: eapply trefl.
        1: now eapply pred1_wf_local.
        repeat eexists; tea. constructor.
      * subst na'.
        eapply PC_TCFromCompareProd; trea.

    + eapply pred1_cumul.
      2: by eapply TC_from_compare_subst10; eassumption.
      have Xdef : Σ ;;; Γ ⊢ tApp t' u' ≡>1 tApp (ρ t) (ρ u) : B {0 := u'}
        by now eapply pred1_clos, clos_app.
      destruct t => //.
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
      apply pred1_pred0, pred0_beta; tas.
      * by repeat (eexists; cbn; tea).
      * eapply TCI_elim; tea.
        1: now econstructor.
      * eapply TCI_elim; tea.
        1: now econstructor.

    + apply pred1_clos.
      subst na'; cbn.
      eapply clos_prod; trea.
      eapply change_context2; tea.
      eapply convertible_contexts_snoc.
      1: eapply convertible_contexts_refl.
      1: eapply trefl.
      1: now eapply pred1_wf_local.
      repeat eexists; tea. constructor.

    + subst s'.
      apply pred1_clos, clos_sort; trea.
Qed.









Class PredEqPrecondition {cf TC} Σ := {
  PE_pred1_trefl :: TypedReflexivity (pred1 Σ) Σ;
  PE_pred1_typing_left :: LeftTyping (pred1 Σ) Σ;
  PE_pred1_typing_right :: RightTyping (pred1 Σ) Σ;
  PE_eq_treflpb pb :: TypedConvReflexivity (equality Σ) Σ pb;
  PE_eq_typing_left pb :: LeftConvTyping (equality Σ) Σ pb;
  PE_eq_typing_right pb :: RightConvTyping (equality Σ) Σ pb;

  PE_context_change_eq :: ContextChangeable (typing Σ) (fun Γ t u T => Σ ;;; Γ ⊢ t <=[Conv] u : T);
  PE_context_change_pred_eq :: ContextChangeable2 (pred1 Σ) (fun Γ t u T => Σ ;;; Γ ⊢ t <=[Conv] u : T);

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
      Σ ;;; Γ ⊢ tRel n ~ tRel n : lift0 (S n) decl.(decl_type) ondep ltac:(now eapply clos_rel) with R'

  | closεε_lambda na na' A A' t t' T s :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s on XA)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(Xt : Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T)] ->
      [(IXt : Σ ;;; Γ ,, vass na A ⊢ t ~R' t' : T on Xt)] ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' : tProd na A T ondep ltac:(now eapply clos_lambda) with R'

  | closεε_app na A B t t' u u' :
      [(Xt : Σ ;;; Γ ⊢ t ~R t' : tProd na A B)] ->
      [(IXt : Σ ;;; Γ ⊢ t ~R' t' : tProd na A B on Xt)] ->
      [(Xu : Σ ;;; Γ ⊢ u ~R u' : A)] ->
      [(IXu : Σ ;;; Γ ⊢ u ~R' u' : A on Xu)] ->
      Σ ;;; Γ ⊢ tApp t u ~ tApp t' u' : B { 0 := u } ondep ltac:(now eapply clos_app) with R'

  | closεε_prod na na' A A' B B' s s' :
      [(Xα : Rα na na')] ->
      [(XA : Σ ;;; Γ ⊢ A ~R A' : tSort s)] ->
      [(IXA : Σ ;;; Γ ⊢ A ~R' A' : tSort s on XA)] ->
      [(Xs : isSortRel s na.(binder_relevance))] ->
      [(XB : Σ ;;; Γ ,, vass na A ⊢ B ~R B' : tSort s')] ->
      [(IXB : Σ ;;; Γ ,, vass na A ⊢ B ~R' B' : tSort s' on XB)] ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B' : tSort (Sort.sort_of_product s s') ondep ltac:(now eapply clos_prod) with R'

  | closεε_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs': wf_sort Σ s')] ->
      [(Xs : Rs s s')] ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' : tSort (Sort.super s') ondep ltac:(eapply clos_sort; eassumption) with R'
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
      Σ ;;; Γ ⊢ tProd na A B ≤c[pb] tProd na' A' B' : tSort (Sort.sort_of_product s s') ondep ltac:(now eapply cumul_prod) with R'

  | cumulεε_sort s s' :
      [(wfΓ : wf_local Σ Γ)] ->
      [(wfs : wf_sort Σ s)] ->
      [(wfs' : wf_sort Σ s')] ->
      [(Xs : compare_sort Σ pb s s')] ->
      Σ ;;; Γ ⊢ tSort s ≤c[pb] tSort s' : tSort (Sort.super s') ondep ltac:(now eapply cumul_sort) with R'
  (* | (indapp) *)
where "Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'ondep' p 'with' R'" := (cumul_addonεε Γ pb t t' T p) (only parsing).

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






Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' : T" (at level 50, Γ, t, pb, t', T at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]η  t'  :  T").
Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' : T 'on' H 'with' R'" (at level 50, Γ, t, pb, t', T, H at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]η  t'  :  T  'on'  H  'with'  R'").
Reserved Notation "Σ  ;;; Γ  ;;; Γ' ⊢ t ==η ↑^ t' · args : T" (at level 50, Γ, Γ', t, t', args, T at next level).
Reserved Notation "Σ  ;;; Γ  ;;; Γ' ⊢ t ==η ↑^ t' · args : T 'on' H 'with' R'" (at level 50, Γ, Γ', t, t', args, T, H at next level).
Reserved Notation "Σ  ;;; Γ  ;;; Γ' ⊢ ↑^ t · args ==η t' : T" (at level 50, Γ, Γ', t, t', args, T at next level).
Reserved Notation "Σ  ;;; Γ  ;;; Γ' ⊢ ↑^ t · args ==η t' : T 'on' H 'with' R'" (at level 50, Γ, Γ', t, t', args, T, H at next level).


Section Eta.

Context TC.
Variable R : context -> conv_pb -> term -> term -> term -> Type.
Variable R' : forall Γ pb t u T, R Γ pb t u T -> Type.
Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' : T" := (R Γ pb t t' T) (only parsing).
Notation "Σ ;;; Γ ⊢ t <=[ pb ]η' t' : T 'on' H" := (R' Γ pb t t' T H) (only parsing, at level 50, Γ, t, pb, t', T at next level).
Local Set Elimination Schemes.

Inductive eta_left_spine Σ Γ Γ' t' T : forall t args, Type :=
  | etal_sprop t args T₀ :
      Σ ;;; Γ ,,, Γ' ⊢ t : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t') (rev_map tRel args) : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T

  | etal_ground t :
      Σ ;;; Γ ,,, Γ' ⊢ t <=[Conv]η lift0 #|Γ'| t' : T ->
      Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · [] : T

  | etal_push na A B t args :
      Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ t ==η ↑^ t' · map S args ,, 0 : B ->
      lift_typing typing Σ (Γ ,,, Γ') (j_vass na A) ->
      Σ ;;; Γ ,,, Γ' ⊢ tProd na A B ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ tLambda na A t ==η ↑^ t' · args : T

  | etal_pop na A B t args n' n :
      Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : tProd na A B ->
      Σ ;;; Γ ,,, Γ' ⊢ n' <=[Conv]η tRel n : A ->
      Σ ;;; Γ ,,, Γ' ⊢ B {0 := n'} ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ tApp t n' ==η ↑^ t' · args ,, n : T
where "Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T" := (eta_left_spine Σ Γ Γ' t' T t args) (only parsing).

Inductive eta_left_spineε Σ Γ Γ' t' T : forall t args, Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T -> Type :=
  | etalε_sprop t args T₀ :
      [(Xt : Σ ;;; Γ ,,, Γ' ⊢ t : T₀)] ->
      [(Xt' : Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t') (rev_map tRel args) : T₀)] ->
      [(XT₀ : Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp)] ->
      [(XT : Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T)] ->
      Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T on ltac:(eapply etal_sprop; eassumption) with R'

  | etalε_ground t :
      [(XR : Σ ;;; Γ ,,, Γ' ⊢ t <=[Conv]η lift0 #|Γ'| t' : T)] ->
      [(IXR : Σ ;;; Γ ,,, Γ' ⊢ t <=[Conv]η' lift0 #|Γ'| t' : T on XR)] ->
      Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · [] : T on ltac:(eapply etal_ground; eassumption) with R'

  | etalε_push na A B t args :
      [(X : Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ t ==η ↑^ t' · map S args ,, 0 : B)] ->
      [(IX : Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ t ==η ↑^ t' · map S args ,, 0 : B on X with R')] ->
      [(Xj : lift_typing typing Σ (Γ ,,, Γ') (j_vass na A))] ->
      [(XT : Σ ;;; Γ ,,, Γ' ⊢ tProd na A B ≤* T)] ->
      Σ ;;; Γ ;;; Γ' ⊢ tLambda na A t ==η ↑^ t' · args : T on ltac:(eapply etal_push; eassumption) with R'

  | etalε_pop na A B t args n' n :
      [(X : Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : tProd na A B)] ->
      [(IX : Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : tProd na A B on X with R')] ->
      [(Xn : Σ ;;; Γ ,,, Γ' ⊢ n' <=[Conv]η tRel n : A)] ->
      [(IXn : Σ ;;; Γ ,,, Γ' ⊢ n' <=[Conv]η' tRel n : A on Xn)] ->
      [(XT : Σ ;;; Γ ,,, Γ' ⊢ B {0 := n'} ≤* T)] ->
      Σ ;;; Γ ;;; Γ' ⊢ tApp t n' ==η ↑^ t' · args ,, n : T on ltac:(eapply etal_pop; eassumption) with R'
where "Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T 'on' H 'with' R'" := (eta_left_spineε Σ Γ Γ' t' T t args H) (only parsing).
Derive Signature for eta_left_spineε.

Inductive eta_right_spine Σ Γ Γ' t T : forall t' args, Type :=
  | etar_sprop t' args T₀ :
      Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t) (rev_map tRel args) : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ t' : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T

  | etar_ground t' :
      Σ ;;; Γ ,,, Γ' ⊢ lift0 #|Γ'| t <=[Conv]η t' : T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · [] ==η t' : T

  | etar_push na A B t' args :
      Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ ↑^ t · map S args ,, 0 ==η t' : B ->
      lift_typing typing Σ (Γ ,,, Γ') (j_vass na A) ->
      Σ ;;; Γ ,,, Γ' ⊢ tProd na A B ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η tLambda na A t' : T

  | etar_pop na A B t' args n n' :
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : tProd na A B ->
      Σ ;;; Γ ,,, Γ' ⊢ tRel n <=[Conv]η n' : A ->
      Σ ;;; Γ ,,, Γ' ⊢ B {0 := tRel n} ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ,, n ==η tApp t' n' : T
where "Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T" := (eta_right_spine Σ Γ Γ' t T t' args).


Inductive eta_right_spineε Σ Γ Γ' t T : forall t' args, Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T -> Type :=
  | etarε_sprop t' args T₀ :
      [(Xt : Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t) (rev_map tRel args) : T₀)] ->
      [(Xt' : Σ ;;; Γ ,,, Γ' ⊢ t' : T₀)] ->
      [(XT₀ : Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp)] ->
      [(XT : Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T)] ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T on ltac:(eapply etar_sprop; eassumption) with R'

  | etarε_ground t' :
      [(XR : Σ ;;; Γ ,,, Γ' ⊢ lift0 #|Γ'| t <=[Conv]η t' : T)] ->
      [(IXR : Σ ;;; Γ ,,, Γ' ⊢ lift0 #|Γ'| t <=[Conv]η' t' : T on XR)] ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · [] ==η t' : T on ltac:(eapply etar_ground; eassumption) with R'

  | etarε_push na A B t' args :
      [(X : Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ ↑^ t · map S args ,, 0 ==η t' : B)] ->
      [(IX : Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ ↑^ t · map S args ,, 0 ==η t' : B on X with R')] ->
      [(Xj : lift_typing typing Σ (Γ ,,, Γ') (j_vass na A))] ->
      [(XT : Σ ;;; Γ ,,, Γ' ⊢ tProd na A B ≤* T)] ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η tLambda na A t' : T on ltac:(eapply etar_push; eassumption) with R'

  | etarε_pop na A B t' args n n' :
      [(X : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : tProd na A B)] ->
      [(IX : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : tProd na A B on X with R')] ->
      [(XR : Σ ;;; Γ ,,, Γ' ⊢ tRel n <=[Conv]η n' : A)] ->
      [(IXR : Σ ;;; Γ ,,, Γ' ⊢ tRel n <=[Conv]η' n' : A on XR)] ->
      [(XT : Σ ;;; Γ ,,, Γ' ⊢ B {0 := tRel n} ≤* T)] ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ,, n ==η tApp t' n' : T on ltac:(eapply etar_pop; eassumption) with R'
where "Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T 'on' H 'with' R'" := (eta_right_spineε Σ Γ Γ' t T t' args H) (only parsing).
Derive Signature for eta_right_spineε.

Unset Elimination Schemes.
End Eta.

Inductive eta_spine {cf TC} Σ Γ pb t t' T : Type :=
  | eta_left :
      Σ ;;; Γ ;;; [] ⊢ t ==η ↑^ t' · [] : T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' : T

  | eta_right :
      Σ ;;; Γ ;;; [] ⊢ ↑^ t · [] ==η t' : T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' : T

  | eta_sprop T₀ :
      Σ ;;; Γ ⊢ t : T₀ ->
      Σ ;;; Γ ⊢ t': T₀ ->
      Σ ;;; Γ ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ⊢ T₀ ≤* T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' : T

  | eta_cumul_addon T₀ :
      Σ ;;; Γ ⊢ t ≤c[pb] t' : T₀ with (eta_spine Σ) ->
      Σ ;;; Γ ⊢ T₀ ≤* T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' : T

  | eta_clos T₀ :
      Σ ;;; Γ ⊢ t ~ t' : T₀ with (fun Γ => eta_spine Σ Γ Conv), eq_binder_annot, eq_sort Σ ->
      Σ ;;; Γ ⊢ T₀ ≤* T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' : T

where "Σ ;;; Γ ⊢ t <=[ pb ]η t' : T" := (eta_spine Σ Γ pb t t' T)
and "Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T" := (eta_left_spine _ (eta_spine Σ) Σ Γ Γ' t' T t args)
and "Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T" := (eta_right_spine _ (eta_spine Σ) Σ Γ Γ' t T t' args).

Notation "Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T 'on' H 'with' R'" := (eta_left_spineε _ (eta_spine Σ) R' Σ Γ Γ' t' T t args H).
Notation "Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T 'on' H 'with' R'" := (eta_right_spineε _ (eta_spine Σ) R' Σ Γ Γ' t T t' args H).


Lemma eta_left_spine_toε {cf TC} Σ R' Γ Γ' t t' args T :
  [(p : Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T)] ->
  [(X Γ pb t t' T : [(H : eta_spine Σ Γ pb t t' T)] -> R' Γ pb t t' T H)] ->
  Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Lemma eta_left_spineε_fmap {cf TC} Σ R R' Γ Γ' t t' args T :
  [(p : Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T)] ->
  [(H : Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T on p with R)] ->
  [(X Γ pb t t' T (H : eta_spine Σ Γ pb t t' T) : R Γ pb t t' T H -> R' Γ pb t t' T H)] ->
  Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T on p with R'.
Proof.
  intros.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Lemma eta_right_spine_toε {cf TC} Σ R' Γ Γ' t t' args T :
  [(p : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t ·args ==η t' : T)] ->
  [(X Γ pb t t' T : [(H : eta_spine Σ Γ pb t t' T)] -> R' Γ pb t t' T H)] ->
  Σ ;;; Γ ;;; Γ' ⊢ ↑^ t ·args ==η t' : T on p with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Lemma eta_right_spineε_fmap {cf TC} Σ R R' Γ Γ' t t' args T :
  [(p : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t ·args ==η t' : T)] ->
  [(H : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t ·args ==η t' : T on p with R)] ->
  [(X Γ pb t t' T : [(H : eta_spine Σ Γ pb t t' T)] -> R Γ pb t t' T H -> R' Γ pb t t' T H)] ->
  Σ ;;; Γ ;;; Γ' ⊢ ↑^ t ·args ==η t' : T on p with R'.
Proof.
  intros.
  induction H.
  all: try now econstructor; eauto with fmap.
Defined.

Hint Resolve eta_left_spine_toε eta_left_spineε_fmap eta_right_spine_toε eta_right_spineε_fmap : fmap.



Inductive eta_spineε {cf TC} Σ R' Γ pb t t' T : Σ ;;; Γ ⊢ t <=[pb]η t' : T -> Type :=
  | etaε_left :
      [(X : Σ ;;; Γ ;;; [] ⊢ t ==η ↑^ t' · [] : T)] ->
      [(IX : Σ ;;; Γ ;;; [] ⊢ t ==η ↑^ t' · [] : T on X with (fun Γ pb t u T H => R' Γ pb t u T × eta_spineε Σ R' Γ pb t u T H))] ->
      Σ ;;; Γ ⊢ t <=[pb]η t' : T on ltac:(eapply eta_left; eassumption) with R'

  | etaε_right :
      [(X : Σ ;;; Γ ;;; [] ⊢ ↑^ t · [] ==η t' : T)] ->
      [(IX : Σ ;;; Γ ;;; [] ⊢ ↑^ t · [] ==η t' : T on X with (fun Γ pb t u T H => R' Γ pb t u T × eta_spineε Σ R' Γ pb t u T H))] ->
      Σ ;;; Γ ⊢ t <=[pb]η t' : T on ltac:(eapply eta_right; eassumption) with R'

  | etaε_sprop T₀ :
      [(Xt : Σ ;;; Γ ⊢ t : T₀)] ->
      [(Xt' : Σ ;;; Γ ⊢ t': T₀)] ->
      [(XT₀ : Σ ;;; Γ ⊢ T₀ : tSort sSProp)] ->
      [(XT : Σ ;;; Γ ⊢ T₀ ≤* T)] ->
      Σ ;;; Γ ⊢ t <=[pb]η t' : T on ltac:(eapply eta_sprop; eassumption) with R'

  | etaε_cumul_addon T₀ :
      [(X : Σ ;;; Γ ⊢ t ≤c[pb] t' : T₀ with (eta_spine Σ))] ->
      [(IX : Σ ;;; Γ ⊢ t ≤c[pb] t' : T₀ ondep X with (fun Γ pb t u T H => R' Γ pb t u T × eta_spineε Σ R' Γ pb t u T H))] ->
      [(XT : Σ ;;; Γ ⊢ T₀ ≤* T)] ->
      Σ ;;; Γ ⊢ t <=[pb]η t' : T on ltac:(eapply eta_cumul_addon; eassumption) with R'

  | etaε_clos T₀ :
      [(X : Σ ;;; Γ ⊢ t ~ t' : T₀ with (fun Γ => eta_spine Σ Γ Conv), eq_binder_annot, eq_sort Σ)] ->
      [(IX : Σ ;;; Γ ⊢ t ~ t' : T₀ ondep X with (fun Γ t u T H => R' Γ Conv t u T × eta_spineε Σ R' Γ Conv t u T H))] ->
      [(XT : Σ ;;; Γ ⊢ T₀ ≤* T)] ->
      Σ ;;; Γ ⊢ t <=[pb]η t' : T on ltac:(eapply eta_clos; eassumption) with R'

where "Σ ;;; Γ ⊢ t <=[ pb ]η t' : T 'on' H 'with' R'" := (eta_spineε Σ R' Γ pb t t' T H).
Derive Signature for eta_spineε.

Definition eta_spine_rect cf TC Σ P :
  [(Xrec Γ pb t u T : [(H : Σ ;;; Γ ⊢ t <=[pb]η u : T)] -> eta_spineε Σ P Γ pb t u T H -> P Γ pb t u T)] ->
  forall Γ pb t u T, [(H : Σ ;;; Γ ⊢ t <=[pb]η u : T)] -> P Γ pb t u T.
Proof.
  intros.
  unshelve eapply Xrec; tea.
  revert Γ pb t u T H. fix rec 6.
  destruct H.
  all: unshelve econstructor; unshelve eauto with fmap; eauto.
Qed.




Lemma eta_spine_cumul cf TC Σ Γ pb t t' T U :
  Σ ;;; Γ ⊢ t <=[pb]η t' : T ->
  Σ ;;; Γ ⊢ T ≤T U ->
  Σ ;;; Γ ⊢ t <=[pb]η t' : U.
Proof.
  intros Xe XT.
  have {} XT T' : Σ ;;; Γ ⊢ T' ≤* T -> Σ ;;; Γ ⊢ T' ≤* U
    by now apply TCI_rstep.
  induction Xe in XT.
  destruct X; [econstructor 1|econstructor 2|..].
  1,2: destruct IX; econstructor; now eauto.
  - now econstructor 3.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
Qed.

Lemma eta_left_spine_cumul cf TC Σ Γ Γ' t t' args T U :
  Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T ->
  Σ ;;; Γ ,,, Γ' ⊢ T ≤T U ->
  Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : U.
Proof.
  intros Xe XT.
  have XT' T' : Σ ;;; Γ ,,, Γ' ⊢ T' ≤* T -> Σ ;;; Γ ,,, Γ' ⊢ T' ≤* U
    by now apply TCI_rstep.
  destruct Xe; try now econstructor; eauto.
  eapply eta_spine_cumul in e; tea.
  now econstructor.
Qed.

Lemma eta_right_spine_cumul cf TC Σ Γ Γ' t t' args T U :
  Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T ->
  Σ ;;; Γ ,,, Γ' ⊢ T ≤T U ->
  Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : U.
Proof.
  intros Xe XT.
  have XT' T' : Σ ;;; Γ ,,, Γ' ⊢ T' ≤* T -> Σ ;;; Γ ,,, Γ' ⊢ T' ≤* U
    by now apply TCI_rstep.
  destruct Xe; try now econstructor; eauto.
  eapply eta_spine_cumul in e; tea.
  now econstructor.
Qed.

Instance TC_compat_eta_spine cf TC Σ Γ pb t t' : TC_compat TC Σ Γ (eta_spine Σ Γ pb t t'). intros ????. now eapply eta_spine_cumul. Defined.
Instance TC_compat_eta_left_spine cf TC Σ Γ Γ' t t' args : TC_compat TC Σ (Γ ,,, Γ') (fun T => Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T). intros ????. now eapply eta_left_spine_cumul. Defined.
Instance TC_compat_eta_right_spine cf TC Σ Γ Γ' t t' args : TC_compat TC Σ (Γ ,,, Γ') (fun T => Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T). intros ????. now eapply eta_right_spine_cumul. Defined.

Lemma eta_left_invert cf TC Σ
  (rec : forall Γ pb t t' T, Σ ;;; Γ ⊢ t <=[pb] t' : T -> Σ ;;; Γ ⊢ t <=[pb]η t' : T)
  Γ Γ' t u T args :
  #|args| > 0 ->
  Σ ;;; Γ,,, Γ' ⊢ t <=[Conv] mkApps (lift0 #|Γ'| u) (rev_map tRel args) : T ->
  Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ u · args : T.
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
  (rec : forall Γ pb t t' T, Σ ;;; Γ ⊢ t <=[pb] t' : T -> Σ ;;; Γ ⊢ t <=[pb]η t' : T)
  Γ Γ' t u T args :
  #|args| > 0 ->
  Σ ;;; Γ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t) (rev_map tRel args) <=[Conv] u : T ->
  Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η u : T.
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

Lemma eta_invert cf TC Σ Γ pb t t' T :
  Σ ;;; Γ ⊢ t <=[pb] t' : T ->
  Σ ;;; Γ ⊢ t <=[pb]η t' : T.
Proof.
  revert Γ pb t t' T.
  fix rec 6.
  destruct 1.
  1: destruct X.
  - apply eta_left.
    eapply etal_push; trea.
    apply eta_left_invert; tas.
    1: cbn; auto with arith.

  - apply eta_right.
    eapply etar_push; trea.
    apply eta_right_invert; tas.
    1: cbn; auto with arith.

  - eapply eta_sprop; trea.
  - eapply eta_cumul_addon; trea.
    eapply cumul_addon_fmap; tea.
  - now eapply eta_spine_cumul.
  - eapply eta_clos; trea.
    eapply context_closure_fmap; eauto.
Qed.


Reserved Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' | ≡>1 u : T" (at level 50, Γ, t, pb, t', u, T at next level, format "Σ  ;;;  Γ  ⊢  t  <=[ pb ]η  t'  |  ≡>1  u  :  T").
Reserved Notation "Σ ;;; Γ ⊢ 'λ(' na : A ) , t =η t' | ≡>1 u : T" (at level 50, Γ, na, A, t, t', u, T at next level, format "Σ  ;;;  Γ  ⊢  'λ(' na  :  A ) ,  t  =η  t'  |  ≡>1  u  :  T").
Reserved Notation "Σ  ;;; Γ  ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T" (at level 50, Γ, Γ', t, t', args, u, T at next level).
Reserved Notation "Σ ;;; Γ ;;; Γ' ⊢ 'λ(' na : A ) , t =η ↑^ t' · args | ≡>1 u : T" (at level 50, Γ, Γ', na, A, t, t', args, u, T at next level, format "Σ  ;;;  Γ  ;;;  Γ'  ⊢  'λ(' na  :  A ) ,  t  =η  ↑^  t'  ·  args  |  ≡>1  u  :  T").
Reserved Notation "Σ  ;;; Γ  ;;; Γ' ⊢ ↑^ t · args =η t' | ≡>1 u : T" (at level 50, Γ, Γ', t, t', args, u, T at next level).
Reserved Notation "Σ ;;; Γ ;;; Γ' ⊢ '↑^(' 'λ(' na : A ) , t ) · args =η t' | ≡>1 u : T" (at level 50, Γ, Γ', na, A, t, t', u, T at next level, format "Σ  ;;;  Γ  ;;;  Γ'  ⊢  '↑^(' 'λ(' na  :  A ) ,  t )  ·  args  =η  t'  |  ≡>1  u  :  T").

Section Pred1EtaL.
Context {cf TC} Σ.
Variable R : context -> conv_pb -> term -> term -> term -> term -> Type.
Variable Ru : context -> aname -> term -> term -> term -> term -> term -> Type.
Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' | ≡>1 u : T" := (R Γ pb t t' u T) (only parsing).
Notation "Σ ;;; Γ ⊢ 'λ(' na : A ) , t =η t' | ≡>1 u : T" := (Ru Γ na A t u T t') (only parsing).
Local Set Elimination Schemes.

Section Under.
Variable rec : context -> context -> term -> term -> term -> list nat -> term -> Type.
Notation "Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T" := (rec Γ Γ' t' T t args u) (only parsing).
Inductive pred1_etal_spine_under Γ Γ' na A t t' u T : forall args, Type :=
  | pred1etal_under_sprop args T₀ T₀' :
      Σ ;;; Γ ,,, Γ' ,, vass na A ⊢ t ≡>1 u : T₀' ->
      Σ ;;; Γ ,,, Γ' ⊢ tLambda na A t : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t') (rev_map tRel args) : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T

  | pred1etal_under_push args B :
      Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ t =η ↑^ t' · map S args ,, 0 | ≡>1 u : B ->
      Σ ;;; Γ ,,, Γ' ⊢ tProd na A B ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T

  | pred1etal_under_ground T₀ :
      Σ ;;; Γ ,,, Γ' ⊢ λ(na : A), t =η lift0 #|Γ'| t' | ≡>1 u : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · [] | ≡>1 u : T

where "Σ ;;; Γ ;;; Γ' ⊢ 'λ(' na : A ) , t =η ↑^ t' · args | ≡>1 u : T" := (pred1_etal_spine_under Γ Γ' na A t t' u T args) (only parsing).
End Under.

Inductive pred1_etal_spine Γ Γ' t' T : forall t args u, Type :=
  | pred1etal_sprop t args u T₀ T₀' :
      Σ ;;; Γ ,,, Γ' ⊢ t ≡>1 u : T₀' ->
      Σ ;;; Γ ,,, Γ' ⊢ t : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ mkApps (lift0 #|Γ'| t') (rev_map tRel args) : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ : tSort sSProp ->
      Σ ;;; Γ ,,, Γ' ⊢ T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T

  | pred1etal_ground t u :
      Σ ;;; Γ ,,, Γ' ⊢ t <=[Conv]η lift0 #|Γ'| t' | ≡>1 u : T ->
      Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · [] | ≡>1 u : T

  | pred1etal_push na A B s T₀ t u args :
      Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ t =η ↑^ t' · map S args ,, 0 | ≡>1 u : T₀ ->
      Σ ;;; Γ ,,, Γ' ⊢ A ≡>1 B : tSort s ->
      Σ ;;; Γ ,,, Γ' ⊢ tProd na A T₀ ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ tLambda na A t =η ↑^ t' · args | ≡>1 tLambda na B u : T

  | pred1etal_pop_clos na A B t u args n n' n'' :
      Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : tProd na A B ->
      Σ ;;; Γ ,,, Γ' ⊢ n' <=[Conv]η tRel n | ≡>1 n'' : A ->
      Σ ;;; Γ ,,, Γ' ⊢ B {0 := n'} ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ tApp t n' =η ↑^ t' · args ,, n | ≡>1 tApp u n'' : T

  | pred1etal_pop_beta na A B t u args n n' n'' :
      Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : tProd na A B ->
      Σ ;;; Γ ,,, Γ' ⊢ n' <=[Conv]η tRel n | ≡>1 n'' : A ->
      Σ ;;; Γ ,,, Γ' ⊢ B {0 := n'} ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ tApp (tLambda na A t) n' =η ↑^ t' · args ,, n | ≡>1 u {0 := n''} : T

where "Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T" := (pred1_etal_spine Γ Γ' t' T t args u) (only parsing)
and "Σ ;;; Γ ;;; Γ' ⊢ 'λ(' na : A ) , t =η ↑^ t' · args | ≡>1 u : T" := (pred1_etal_spine_under pred1_etal_spine Γ Γ' na A t t' u T args) (only parsing).

End Pred1EtaL.



Section Pred1EtaR.
Context {cf TC} Σ.
Variable R : context -> conv_pb -> term -> term -> term -> term -> Type.
Variable Ru : context -> aname -> term -> term -> term -> term -> term -> Type.
Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' | ≡>1 u : T" := (R Γ pb t t' u T) (only parsing).
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
      Σ ;;; Γ ,,, Γ' ⊢ tRel n <=[Conv]η n' : A ->
      Σ ;;; Γ ,,, Γ' ⊢ B {0 := tRel n} ≤* T ->
      Σ ;;; Γ ;;; Γ' ⊢ ↑^ _ · args ,, n =η tApp t' n' : T with t, P, P'
where "Σ ;;; Γ ;;; Γ' ⊢ ↑^ '_' · args =η t' : T 'with' t , P , P'" := (modular_etar_spine P P' t Γ Γ' T t' args) (only parsing).

Definition pred1_etar_spine Γ Γ' t t' u args T :=
  modular_etar_spine
    (∑ T₀, Σ ;;; Γ ⊢ t ≡>1 u : T₀)
    (fun Γ' t' T₀ => Σ ;;; Γ ,,, Γ' ⊢ lift0 #|Γ'| t <=[Conv]η t' | ≡>1 lift0 #|Γ'| u : T₀)
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
Variable R : context -> conv_pb -> term -> term -> term -> term -> Type.
Notation "Σ ;;; Γ ⊢ t <=[ pb ]η t' | ≡>1 u : T" := (R Γ pb t t' u T) (only parsing).

Local Set Elimination Schemes.

Inductive pred1_eq_spine_under Γ na A t u T : forall t', Type :=
  | pred1eq_lam_etar t' :
      Σ ;;; Γ ;;; [] ⊢ ↑^(λ(na : A), t) · [] =η t' | ≡>1 u : T ->
      Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T

  | pred1eq_lam_etal t' :
      Σ ;;; Γ ;;; [] ⊢ λ(na : A), t =η ↑^ t' · [] | ≡>1 u : T ->
      Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T

  | pred1eq_lam_ground s na' A' t' B :
      eq_binder_annot na na' ->
      isSortRel s (binder_relevance na) ->
      Σ ;;; Γ ⊢ A <=[Conv]η A' : tSort s ->
      Σ ;;; Γ ,, vass na A ⊢ t <=[Conv]η t' | ≡>1 u : B ->
      Σ ;;; Γ ⊢ tProd na A B ≤* T ->
      Σ ;;; Γ ⊢ λ(na : A), t =η tLambda na' A' t' | ≡>1 u : T

where "Σ ;;; Γ ⊢ 'λ(' na : A ) , t =η t' | ≡>1 u : T" := (pred1_eq_spine_under Γ na A t u T t') (only parsing)
and "Σ ;;; Γ ;;; Γ' ⊢ 'λ(' na : A ) , t =η ↑^ t' · args | ≡>1 u : T" := (pred1_etal_spine_under Σ pred1_eq_spine_under (pred1_etal_spine Σ R pred1_eq_spine_under) Γ Γ' na A t t' u T args) (only parsing)
and "Σ ;;; Γ ;;; Γ' ⊢ '↑^(' 'λ(' na : A ) , t ) · args =η t' | ≡>1 u : T" := (pred1_etar_spine_under Σ pred1_eq_spine_under Γ Γ' na A t t' u args T) (only parsing)
and "Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T" := (pred1_etal_spine Σ R pred1_eq_spine_under Γ Γ' t' T t args u) (only parsing).

End Pred1EqLam.

Inductive pred1_equality {cf TC} Σ Γ (pb : conv_pb) : forall (t t' u T : term), Type :=
  (* Inconsequent *)
  | pred1eq_cumul t t' u T T' :
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T ->
      Σ ;;; Γ ⊢ T ≤T T' ->
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T'

  (* closure vs closure *)
  | pred1eq_clos t t' u T :
      context_closure_tri Σ (fun Γ => pred1_equality Σ Γ Conv) Γ t t' u T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T

  | pred1eq_cumul_addon t t' u T :
      cumul_addon_tri Σ (pred1_equality Σ) Γ pb t t' u T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T

  (* sprop *)
  | pred1eq_sprop t t' u T₀ T :
      Σ ;;; Γ ⊢ t ≡>1 u : T₀ ->
      Σ ;;; Γ ⊢ t : T ->
      Σ ;;; Γ ⊢ t' : T ->
      Σ ;;; Γ ⊢ T : tSort sSProp ->
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T

  (* eta on the right *)
  | pred1eq_etar t t' u T :
      Σ ;;; Γ ;;; [] ⊢ ↑^ t · [] =η t' | ≡>1 u : T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T

  (* eta on the left *)
  | pred1eq_etal t t' u T :
      Σ ;;; Γ ;;; [] ⊢ t =η ↑^t' · [] | ≡>1 u : T ->
      Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T

  (* beta vs clos for app *)
  | pred1eq_beta_clos na A t t' u a a' b B :
      Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : tProd na A B ->
      Σ ;;; Γ ⊢ a <=[Conv]η a' | ≡>1 b : A ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) a <=[pb]η tApp t' a' | ≡>1 u {0 := b} : B {0 := a}

where "Σ ;;; Γ ⊢ t <=[ pb ]η t' | ≡>1 u : T" := (@pred1_equality _ _ Σ Γ pb t t' u T)
and "Σ ;;; Γ ⊢ 'λ(' na : A ) , t =η t' | ≡>1 u : T" := (pred1_eq_spine_under Σ (pred1_equality Σ) Γ na A t u T t')
and "Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T" := (pred1_etal_spine Σ (pred1_equality Σ) (pred1_eq_spine_under Σ (pred1_equality Σ)) Γ Γ' t' T t args u)
and "Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args =η t' | ≡>1 u : T" := (pred1_etar_spine Σ (pred1_equality Σ) Γ Γ' t t' u args T).
Notation "Σ ;;; Γ ;;; Γ' ⊢ 'λ(' na : A ) , t =η ↑^ t' · args | ≡>1 u : T" := (pred1_etal_spine_under Σ (pred1_eq_spine_under Σ (pred1_equality Σ)) (pred1_etal_spine Σ (pred1_equality Σ) (pred1_eq_spine_under Σ (pred1_equality Σ))) Γ Γ' na A t t' u T args).
Notation "Σ ;;; Γ ;;; Γ' ⊢ '↑^(' 'λ(' na : A ) , t ) · args =η t' | ≡>1 u : T" := (pred1_etar_spine_under Σ (pred1_eq_spine_under Σ (pred1_equality Σ)) Γ Γ' na A t t' u args T).

Derive Signature for pred1_equality.

Instance TC_compat_pred1_equality cf TC Σ Γ pb t t' u : TC_compat TC Σ Γ (pred1_equality Σ Γ pb t t' u). by now econstructor. Defined.
Instance TC_compat_pred1_etal_spine_under cf TC Σ Γ Γ' na A t t' args u : TC_compat TC Σ (Γ ,,, Γ') (fun T => Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T).
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
  - constructor; now eapply TC_compat_pred1_etal_spine_under.
  - econstructor; eauto; now eapply TCI_rstep.
Defined.


Lemma etal_left_typing cf TC Σ Γ Γ' t t' args T : Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^t' · args : T -> Σ ;;; Γ ,,, Γ' ⊢ t : T.
Proof.
  induction 1.
  - eapply TCI_elim; tc; tea.
  -
  - eapply TCI_elim; tc; tea.
    constructor; tas.
  - eapply TCI_elim; tc; tea.
    econstructor; tea.
Abort.

Lemma eta_spine_left_pred1_equality cf TC Σ Γ Γ' t t' u args T T₀ :
  let P Γ pb t t' T :=
    match t with tLambda na A t =>
      forall u T₀, Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T
    | _ => True
    end ×
    forall u T₀, Σ ;;; Γ ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T
  in
  [(X : Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T)] ->
  [(IX : Σ ;;; Γ ;;; Γ' ⊢ t ==η ↑^ t' · args : T on X with
    fun Γ pb t t' T H => P Γ pb t t' T × eta_spineε Σ P Γ pb t t' T H)] ->
  match t with tLambda na A t =>
  [(Xp : Σ ;;; Γ ,,, Γ' ,, vass na A ⊢ t ≡>1 u : T₀)] ->
    Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T
  | _ => True
  end ×
  ([(Xp : Σ ;;; Γ ,,, Γ' ⊢ t ≡>1 u : T₀)] ->
    Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T).
Proof.
  intros * IX.
  induction IX in u, T₀.
  3,4: split => //; intro Xp.
  1,2: split; [destruct t => //|]; intro Xp.
  - eapply pred1etal_under_sprop; tea.
  - eapply pred1etal_sprop; tea.
  - eapply pred1etal_under_ground; trea.
    now eapply IXR.
  - apply pred1etal_ground.
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
  let P Γ pb t t' T :=
    Q Γ pb t t' T ×
    forall u T₀, Σ ;;; Γ ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T
  in
  [(X : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T)] ->
  [(IX : Σ ;;; Γ ;;; Γ' ⊢ ↑^ t · args ==η t' : T on X with
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
Admitted.


Lemma eta_spine_right_pred1_equality_under cf TC Σ Q Γ Γ' na A t t' u args T T₀ :
  let P Γ pb t t' T :=
    match t return Type with tLambda na A t =>
      forall u T₀, Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T
    | _ => True
    end × Q Γ pb t t' T
  in
  [(X : Σ ;;; Γ ;;; Γ' ⊢ ↑^ tLambda na A t · args ==η t' : T)] ->
  [(IX : Σ ;;; Γ ;;; Γ' ⊢ ↑^ tLambda na A t · args ==η t' : T on X with
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
Admitted.




Theorem pred1_equality_pred1_equality cf TC Σ (Pre : PredEqPrecondition cf TC Σ) Γ pb t t' u T T₀ :
  Σ ;;; Γ ⊢ t <=[pb]η t' : T ->
  Σ ;;; Γ ⊢ t ≡>1 u : T₀ ->
  Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T.
Proof.
  intro Xe.
  revert u T₀.
  set P := fun Γ pb t t' T =>
    match t with tLambda na A t =>
      forall u T₀, Σ ;;; Γ ,, vass na A ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ λ(na : A), t =η t' | ≡>1 u : T
    | _ => True
    end × forall u T₀, Σ ;;; Γ ⊢ t ≡>1 u : T₀ -> Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T.
  eenough (XGoal : P Γ pb t t' T) by exact (snd XGoal).
  induction Xe.
  destruct X.
  all: split; [destruct t => //|]; try rename u into t'; intros u T₀' Xp.

  - eapply pred1eq_lam_etal.
    now eapply eta_spine_left_pred1_equality in IX.
  - eapply pred1eq_etal.
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
  - by depelim X.
  - eapply TCI_elim; tc; tea.
    clear XT T. rename T₀ into T.

    destruct Xp using pred1_elim.
    1: by destruct X0; depelim X.
    clear XT U.

    eapply pred1eq_cumul_addon.
    destruct IX; depelim X0.
    + subst na'0.
      constructor; eauto.
      * now eapply IXA.
      * now eapply IXB.
    + subst s'0.
      constructor; auto.

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

Theorem pred1_equality_commut cf TC Σ (Pre : PredEqPrecondition cf TC Σ) Γ pb t t' u T :
  Σ ;;; Γ ⊢ t <=[pb]η t' | ≡>1 u : T ->
  ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u <=[pb]η u' : T.
Proof.
  revert Γ pb t t' u T.
  fix rec 7.
  intros * X.
  destruct X.
  - apply rec in X as (u' & Xpu & Xeu).
    eexists; split.
    + now eapply pred1_cumul.
    + now eapply eta_spine_cumul.
  - enough (∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ⊢ u <=[Conv]η u' : T).
    { destruct X as (u' & Xpu & Xeu); eexists; split; tea. admit; eapply eta_spine_eq_pb. }
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
      ∑ u' : term, Σ ;;; Γ ,,, Γ' ⊢ t' ≡>1 u' : T × Σ ;;; Γ ;;; Γ' ⊢ ↑^ u · args ==η u' : T).
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

  - enough (forall Γ Γ' t t' u args T, Σ ;;; Γ ;;; Γ' ⊢ t =η ↑^ t' · args | ≡>1 u : T ->
      ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ;;; Γ' ⊢ u ==η ↑^ u' · args : T).
    { edestruct X as (u' & Xpu & Xeu); tea. eexists; split; tea. now eapply eta_left. }
    clear Γ pb t t' u T p.
    induction 1.
    + exists t'; split.
      * apply pred1_trefl. now eapply TCI_elim; tc; tea.
      * eapply etal_sprop; tea.
        admit.

    + apply rec in r as (u' & Xpu & Xeu).
      have {Xpu} [u'' [eu Xpu]] : ∑ u'', u' = lift0 #|Γ'| u'' × Σ ;;; Γ ⊢ t' ≡>1 u'' : T by admit. subst u'.
      exists u''; split.
      * assumption.
      * by eapply etal_ground.

    + destruct IHX as (u' & Xpu & Xeu).
      exists u'; split.
      * eapply TCI_elim; tc; tea.
        destruct l as (_ & s & XA & _ & Xs); cbn in XA, Xs.
        eapply pred1_clos, clos_lambda; trea.
        now apply pred1_trefl.
      * eapply etal_push; tea.
        all: admit.

    + apply rec in r as (n4 & Xpn & Xen).
      assert (n4 = tRel n) as -> by admit.
      destruct IHX as (u' & Xpu & Xeu).
      exists u'; split.
      * all: admit.
      * eapply etal_pop; tea.
        admit.

    + apply rec in r as (n4 & Xpn & Xen).
      assert (n4 = tRel n) as -> by admit.

      enough (forall Γ Γ' na A t t' u args T, Σ ;;; Γ ;;; Γ' ⊢ λ(na : A), t =η ↑^ t' · args | ≡>1 u : T ->
        ∑ u', Σ ;;; Γ ⊢ t' ≡>1 u' : T × Σ ;;; Γ ;;; Γ' ,, vass na A ⊢ u ==η ↑^ u' · args ,, 0 : T).
      { edestruct X as (u' & Xpu & Xeu); tea. eexists; split; tea. 1: admit. eapply etal_pop. }
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
