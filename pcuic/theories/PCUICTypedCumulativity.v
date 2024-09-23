(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses CMorphisms.
From Equations.Type Require Import Relation Relation_Properties.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config BasicAst Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
  PCUICLiftSubst PCUICSigmaCalculus PCUICUnivSubst PCUICCases PCUICOnFreeVars.

Require Import ssreflect.
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
  Reserved Notation " Σ  ;;; Γ ⊢ T ≤T T' " (at level 50, Γ, T, T' at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ T ≤T T' 'with' TC" (at level 50, Γ, T, T', TC at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t : T 'subst'" (at level 50, Γ, t, T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t : T 'subst' 'with' R" (at level 50, Γ, t, T, R at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t = t' : T 'subst'" (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t = t' : T 'subst' 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t : T " (at level 50, Γ, t, T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t : T 'with' TC" (at level 50, Γ, t, T at next level).
  Reserved Notation "'wf_local' Σ Γ " (at level 9, Σ, Γ at next level).
  Reserved Notation "'wf_local' Σ Γ 'with' TC" (at level 9, Σ, Γ, TC at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≤[ pb ] t' : T " (at level 50, Γ, pb, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t = t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≤ t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≤[ pb ] t' : T 'with' TC" (at level 50, Γ, t, pb, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ▹ T " (at level 50, Γ, t, T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ▹□ u " (at level 50, Γ, t, u at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ▹Π ( na , A , B ) " (at level 50, Γ, t, na, A, B at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ▹{ ind } ( u , args )" (at level 50, Γ, t, ind, u, args at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ◃ T " (at level 50, Γ, t, T at next level).
  Reserved Notation "'wf_local_bd' Σ Γ " (at level 9, Σ, Γ at next level).
  Reserved Notation "'wf_local_bd_rel' Σ Γ Γ'" (at level 9, Σ, Γ, Γ' at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~>0 t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≡>0 t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≡>0 t' : T 'with' R " (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~ext t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~ext t' : T 'with' R" (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~R t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t =R t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≤R[ pb ] t' : T " (at level 50, Γ, t, pb, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~ t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~ t' : T 'with' R , R' , R'' " (at level 50, Γ, t, t', T, R, R', R'' at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~1 t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~1 t' : T 'with' R " (at level 50, Γ, t, t', T, R at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~>1 t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≡>1 t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~> t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≡> t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ~>h t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t h~> t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≤c[ pb ] t' : T " (at level 50, Γ, t, pb, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≤c[ pb ] t' : T 'with' R " (at level 50, Γ, t, pb, t', T, R at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t == t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t <= t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t <=[ pb ] t' : T " (at level 50, Γ, t, pb, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t === t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t <== t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t <==[ pb ] t' : T " (at level 50, Γ, t, pb, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≡ t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≦ t' : T " (at level 50, Γ, t, t', T at next level).
  Reserved Notation " Σ  ;;; Γ ⊢ t ≦[ pb ] t' : T " (at level 50, Γ, t, pb, t', T at next level).
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
    (lift 1 1 t) { 0 := tRel 0 }= t.
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
    forall x decl,
      nth_error Γ x = Some decl ->
    forall b,
      decl.(decl_body) = Some b ->
      (∑ x' decl', σ x = tRel x' ×
        nth_error Δ x' = Some decl' ×
        (** This is let-preservation *)
        option_map (rename (rshiftk (S x'))) decl'.(decl_body) =
          Some (b.[↑^(S x) ∘s σ])) +
      (* This allows to expand a let-binding everywhere *)
      (σ x = b.[↑^(S x) ∘s σ]).

  Definition welltyped_inst typing (Γ : context) σ (Δ : context) :=
    (forall n decl,
      [(Hnth : nth_error Γ n = Some decl)] ->
      typing Δ (σ n) (lift0 (S n) (decl_type decl)).[ σ ]) ×
    usubst Γ σ Δ.

  Notation "Σ ;;; Δ ⊢ σ : Γ 'subst'" := (welltyped_inst (_ Σ) Γ σ Δ).
  Notation "Σ ;;; Δ ⊢ σ : Γ 'subst' 'with' R" := (welltyped_inst (R Σ) Γ σ Δ) (only parsing).

  Definition wellconv_inst conv (Γ : context) (σ σ' : substitutionT) (Δ : context) :=
    (forall n decl,
      [(Hnth : nth_error Γ n = Some decl)] ->
      conv Δ (σ n) (σ' n) (lift0 (S n) (decl_type decl)).[ σ ]) ×
    usubst Γ σ Δ.

  Notation "Σ ;;; Δ ⊢ σ = σ' : Γ 'subst'" := (wellconv_inst (_ Σ) Γ σ σ' Δ).
  Notation "Σ ;;; Δ ⊢ σ = σ' : Γ 'subst' 'with' R" := (wellconv_inst (R Σ) Γ σ σ' Δ) (only parsing).

  Instance usubst_proper : Proper (Logic.eq ==> `=1` ==> Logic.eq ==> iffT) usubst.
  Proof.
    intros Γ Γ' <- σ σ' eq Δ ? <-.
    split; intros X n decl hnth' b hb; specialize (X n decl hnth' b hb).
    all: [> rewrite <-eq| rewrite -> eq]; relativize (b.[_]); tea.
    all: apply inst_ext.
    all: now [> rewrite <-eq| rewrite -> eq].
  Qed.


  Lemma lift_rename_usubst {Γ Δ Γ'} :
    usubst (Γ,,, Γ') (⇑^#|Γ'| (↑^#|Δ|)) (Γ,,, Δ,,, lift_context #|Δ| 0 Γ').
  Proof.
    intros n decl.
    case: (nth_error_app_context Γ Γ' n) => // x hnth hlt [=] hx; subst x => b hb.
    - left; eexists n, _.
      split. 2: split.
      + rewrite /Upn /subst_consn idsn_lt //.
      + rewrite nth_error_app_lt; len => //.
        rewrite nth_error_lift_context_eq hnth /= //.
      + cbn -[rshiftk]. rewrite hb. cbn -[rshiftk]. f_equal.
        rewrite lift_rename !rename_inst inst_assoc ren_lift_renaming ren_rshiftk Nat.add_0_r.
        apply inst_ext.
        rewrite -shiftn_Upn -Upn_Upn.
        now replace (S n + _) with #|Γ'| by lia.
    - left; exists (n + #|Δ|), decl.
      repeat split.
      + rewrite Upn_eq /shiftk /subst_consn nth_error_idsn_None //; try lia.
        cbn. f_equal. len. lia.
      + rewrite nth_error_app_ge; len; try lia.
        rewrite nth_error_app_ge; len; try lia.
        rewrite -hnth. lia_f_equal.
      + cbn -[rshiftk]. rewrite hb. cbn -[rshiftk]. f_equal.
        rewrite rename_inst ren_rshiftk.
        apply inst_ext.
        replace (S n) with (S n - #|Γ'| + #|Γ'|) by lia.
        rewrite -shiftk_compose subst_compose_assoc shiftn_Upn.
        rewrite !shiftk_compose.
        now replace (S n - _ + _) with (S (n + #|Δ|)) by lia.
  Qed.

  Lemma welltyped_lift_rename_inst {typing Γ Γ' Δ} :
    [(onrel n decl : nth_error (Γ,,, Δ,,, lift_context #|Δ| 0 Γ') n = Some decl -> typing (Γ,,, Δ,,, lift_context #|Δ| 0 Γ') (tRel n) (lift0 (S n) (decl_type decl)))] ->
    welltyped_inst typing (Γ,,, Γ') (⇑^#|Γ'| (↑^#|Δ|)) (Γ,,, Δ,,, lift_context #|Δ| 0 Γ').
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

  Lemma wellconv_lift_rename_inst {conv Γ Γ' Δ} :
    [(onrel n decl : nth_error (Γ,,, Δ,,, lift_context #|Δ| 0 Γ') n = Some decl -> conv (Γ,,, Δ,,, lift_context #|Δ| 0 Γ') (tRel n) (tRel n) (lift0 (S n) (decl_type decl)))] ->
    wellconv_inst conv (Γ,,, Γ') (⇑^#|Γ'| (↑^#|Δ|)) (⇑^#|Γ'| (↑^#|Δ|)) (Γ,,, Δ,,, lift_context #|Δ| 0 Γ').
  Proof.
    split.
    2: now apply lift_rename_usubst.
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
  Lemma wellformed_usubst {Γ Δ Γ' s} :
    wellformed_subst s Δ ->
    usubst (Γ,,, Δ,,, Γ') (⇑^#|Γ'| (s ⋅n ids)) (Γ,,, subst_context s 0 Γ').
  Proof.
    intros subs n decl.
    apply wellformed_subst_length in subs as Hlen.
    case: (nth_error_app_context (Γ ,,, Δ) Γ' n) => // x hnth hlt [=] hx; subst x => b hb.
    2: move: hnth.
    2: case: (nth_error_app_context Γ Δ _) => // x' hnth hn' [=] eq; subst x'.
    - left; eexists n, _.
      split. 2: split.
      + rewrite /Upn /subst_consn idsn_lt //.
      + rewrite nth_error_app_lt; len => //.
        rewrite nth_error_subst_context hnth /= //.
      + rewrite /= hb /= Nat.add_0_r. f_equal.
        rewrite rename_inst subst_inst inst_assoc.
        apply inst_ext.
        replace #|Γ'| with (S n + (#|Γ'| - S n)) at 2 by lia.
        rewrite Upn_Upn shiftn_Upn //.
    - right.
      eapply wellformed_subst_def in hb; tea.
      rewrite /Upn {1}/subst_consn nth_error_idsn_None ?idsn_length; try lia.
      rewrite {1}/subst_consn {1}/subst_compose hb.
      rewrite subst_inst Upn_0 inst_assoc. apply inst_ext.
      (rewrite skipn_subst; try by lia); [].
      rewrite !subst_compose_assoc.
      rewrite subst_consn_compose. sigma.
      rewrite -subst_compose_assoc -shiftk_shift -subst_compose_assoc.
      rewrite -shiftk_shift.
      (rewrite (shift_subst_consn_ge (S n)); try by len; lia); [].
      now len.
    - left; exists (n - #|s|), decl.
      len in hlt.
      repeat split.
      + rewrite Upn_eq /subst_consn nth_error_idsn_None //; try lia.
        cbn.
        rewrite (proj2 (nth_error_None _ _)); try (len; lia).
        simpl. len. unfold shiftk. lia_f_equal.
      + rewrite nth_error_app_ge; len; try lia.
        rewrite -hnth. lia_f_equal.
      + rewrite /= hb /=. f_equal.
        rewrite rename_inst.
        apply inst_ext.
        replace (S n) with ((S n - #|Γ'| - #|s|) + #|s| + #|Γ'|) by lia.
        rewrite -shiftk_compose subst_compose_assoc shiftn_Upn -subst_compose_assoc.
        rewrite -shiftk_compose [_ ∘s (s ⋅n ids) ]subst_compose_assoc subst_consn_shiftn // compose_ids_r.
        rewrite shiftk_compose -ren_rshiftk /rshiftk /ren. intro. lia_f_equal.
  Qed.

  Lemma welltyped_subst_inst {typing Γ Γ' s Δ} :
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


  Lemma wellconv_subst_inst {conv Γ Γ' s s' Δ} :
    wellconv_subst (conv Γ) s s' Δ ->
    [(onrel n decl : nth_error (Γ ,,, subst_context s 0 Γ') n = Some decl -> conv (Γ ,,, subst_context s 0 Γ') (tRel n) (tRel n) (lift0 (S n) (decl_type decl)))] ->
    [(shift_conv t t' T : conv Γ t t' T -> conv (Γ ,,, subst_context s 0 Γ') t.[↑^#|Γ'|] t'.[↑^#|Γ'|] T.[↑^#|Γ'|])] ->
    wellconv_inst conv (Γ ,,, Δ ,,, Γ') (⇑^#|Γ'| (s ⋅n ids)) (⇑^#|Γ'| (s' ⋅n ids)) (Γ ,,, subst_context s 0 Γ').
  Proof.
    intros hs onrel shift_conv.
    apply wellconv_subst_well_formed in hs as hus.
    destruct hus as [hus hus'].
    apply wellformed_subst_length in hus as hlen, hus' as hlen'.
    split.
    2: now eapply wellformed_usubst in hus.
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
      lia_f_equal.
  Qed.

End Substs. Include Substs.






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

Notation " Σ  ;;; Γ ⊢ t : T 'with' TC" := (@typing TC Σ Γ t T) (at level 50, Γ, t, T at next level, only parsing).
Notation "'wf_local' Σ Γ 'with' TC" := (All_local_env (lift_typing1 (@typing TC Σ)) Γ) (at level 9, Σ, Γ, TC at next level, only parsing).



Definition typing_rect TC Σ P Pj PΓ :
  [(Xj Γ j : lift_typing typing Σ Γ j -> lift_typing1 P Γ j -> Pj Γ j)] ->
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
  have {} XΓ Γ : wf_local Σ Γ -> PΓ Γ.
  { eauto 8 with fmap. }
  have {} Xj Γ j : lift_typing typing Σ Γ j -> Pj Γ j.
  { eauto with fmap. }
  intros Γ t_ T_ []; try clear t_; try clear T_.
  all: try solve [ match goal with h : _ |- _ => eapply h; eauto end ].
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


Inductive typed_conversion_spec {cf : checker_flags} {TC} (Σ : global_env_ext) (Γ : context) pb : forall (t t' T : term), Type :=
  | tc_sym t u T :
      Σ ;;; Γ ⊢ t = u : T ->
      Σ ;;; Γ ⊢ u ≤[pb] t : T

  | tc_trans t u v T :
      Σ ;;; Γ ⊢ t ≤[pb] u : T ->
      Σ ;;; Γ ⊢ u ≤[pb] v : T ->
      Σ ;;; Γ ⊢ t ≤[pb] v : T

  | tc_beta na A s t t' u u' T :
      Σ ;;; Γ ⊢ A = A : tSort s ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ t = t' : T ->
      Σ ;;; Γ ⊢ u = u' : A ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ≤[pb] t' { 0 := u' } : T { 0 := u }

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
  [(XBeta Γ pb na A s t t' u u' T :
      Σ ;;; Γ ⊢ A = A : tSort s ->
      P Γ Conv A A (tSort s) ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ t = t' : T ->
      P (Γ ,, vass na A) Conv t t' T ->
      Σ ;;; Γ ⊢ u = u' : A ->
      P Γ Conv u u' A ->
      P Γ pb (tApp (tLambda na A t) u) (t' { 0 := u' }) (T { 0 := u }) )] ->
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

Lemma typing_to_typed_conv {cf} {TC} Σ Γ t T :
  Σ ;;; Γ ⊢ t : T -> Σ ;;; Γ ⊢ t = t : T.
Proof.
  induction 1 using typing_rect with (Pj := lift_typing1 (fun Γ t T => Σ ;;; Γ ⊢ t = t : T)) (PΓ := fun Γ => True) => //=.
  all: try now econstructor; eauto.
  - destruct IHX as (_ & s & HT & e & ?); cbn in *.
    subst s.
    eapply tc_prod; eauto.
  - destruct IHX as (_ & s & HT & _ & ?); cbn in *.
    eapply tc_lambda; eauto.
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
    TC_refl : forall Γ t T, Σ ;;; Γ ⊢ t : T -> Σ ;;; Γ ⊢ T ≤T T;
    TC_trans : forall Γ T T' T'', Σ ;;; Γ ⊢ T ≤T T' -> Σ ;;; Γ ⊢ T' ≤T T'' -> Σ ;;; Γ ⊢ T ≤T T'';
    TC_subst : forall Γ na A u T T', Σ ;;; Γ ,, vass na A ⊢ T ≤T T' -> Σ ;;; Γ ⊢ u : A -> Σ ;;; Γ ⊢ T {0 := u} ≤T T' {0 := u};
    TC_sort_of_product : forall Γ Γ' s1 s2 s1' s2', Σ ;;; Γ ⊢ tSort s1 ≤T tSort s1' -> Σ ;;; Γ' ⊢ tSort s2 ≤T tSort s2' -> Σ ;;; Γ ⊢ tSort (Sort.sort_of_product s1 s2) ≤T tSort (Sort.sort_of_product s1' s2');
    TC_sort_relevance : forall Γ s s', Σ ;;; Γ ⊢ tSort s ≤T tSort s' -> relevance_of_sort s = relevance_of_sort s';
    TC_prod_construct : forall Γ na A B B', Σ ;;; Γ ,, vass na A ⊢ B ≤T B' -> Σ ;;; Γ ⊢ tProd na A B ≤T tProd na A B';
    TC_prod_invert : forall Γ T na' A' B', Σ ;;; Γ ⊢ T ≤T tProd na' A' B' -> ∑ na A B, RtP Σ Γ T na A B × Σ ;;; Γ ⊢ A' ≤T A × Σ ;;; Γ ,, vass na A ⊢ B ≤T B';
    TC_sort_invert : forall Γ T s', Σ ;;; Γ ⊢ T ≤T tSort s' -> ∑ s, RtS Σ Γ T s × Σ ;;; Γ ⊢ tSort s ≤T tSort s'
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

Context {TC} Σ (R : forall (Γ : context) (t t' T : term), Type).

Notation " Σ ;;; Γ ⊢ t ~R t' : T " := (R Γ t t' T) (only parsing).

Inductive red0 Γ : forall (t t' T : term), Type :=
  | red0_beta na A t T u :
      lift_typing typing Σ Γ (j_vass na A) ->
      Σ ;;; Γ ,, vass na A ⊢ t : T ->
      Σ ;;; Γ ⊢ u : A ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ~>0 t { 0 := u } : T { 0 := u }

  | red0_cumul t u T U :
      Σ ;;; Γ ⊢ t ~>0 u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t ~>0 u : U
where " Σ ;;; Γ ⊢ t ~>0 t' : T " := (@red0 Γ t t' T) (only parsing).

Inductive pred0 Γ : forall (t t' T : term), Type :=
  | pred0_beta na A t t' T u u' :
      lift_typing typing Σ Γ (j_vass na A) ->
      Σ ;;; Γ ⊢ t ~R t' : T ->
      Σ ;;; Γ ⊢ u ~R u' : A ->
      Σ ;;; Γ ⊢ tApp (tLambda na A t) u ≡>0 t' { 0 := u' } : T { 0 := u }

  | pred0_cumul t u T U :
      Σ ;;; Γ ⊢ t ≡>0 u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t ≡>0 u : U
where " Σ ;;; Γ ⊢ t ≡>0 t' : T " := (@pred0 Γ t t' T) (only parsing).

Inductive ext_eq Γ : forall (t t' T : term), Type :=
  | ext_eta t t' na A B :
      lift_typing typing Σ Γ (j_vass na A) ->
      Σ ;;; Γ ⊢ t : tProd na A B ->
      Σ ;;; Γ ⊢ t' : tProd na A B ->
      Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) ~R tApp (lift0 1 t') (tRel 0) : B ->
      Σ ;;; Γ ⊢ t ~ext t' : tProd na A B

  | ext_sprop t u T :
      Σ ;;; Γ ⊢ t : T ->
      Σ ;;; Γ ⊢ u : T ->
      Σ ;;; Γ ⊢ T : tSort sSProp ->
      Σ ;;; Γ ⊢ t ~ext u : T
where " Σ ;;; Γ ⊢ t ~ext t' : T " := (@ext_eq Γ t t' T) (only parsing).

Inductive context_closure Rα Rs Γ : forall (t t' T : term), Type :=
  | clos_rel n decl :
      wf_local Σ Γ ->
      nth_error Γ n = Some decl ->
      Σ ;;; Γ ⊢ tRel n ~ tRel n : lift0 (S n) decl.(decl_type)

  | clos_lambda na na' A A' t t' T s :
      Rα na na' ->
      Σ ;;; Γ ⊢ A ~R A' : tSort s ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ t ~R t' : T ->
      Σ ;;; Γ ⊢ tLambda na A t ~ tLambda na' A' t' : tProd na A T

  | clos_app na A B t t' u u' :
      Σ ;;; Γ ⊢ t ~R t' : tProd na A B ->
      Σ ;;; Γ ⊢ u ~R u' : A ->
      Σ ;;; Γ ⊢ tApp t u ~ tApp t' u' : B { 0 := u }

  | clos_prod na na' A A' B B' s s' :
      Rα na na' ->
      Σ ;;; Γ ⊢ A ~R A' : tSort s ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ B ~R B' : tSort s' ->
      Σ ;;; Γ ⊢ tProd na A B ~ tProd na' A' B' : tSort (Sort.sort_of_product s s')

  | clos_sort s s' :
      wf_local Σ Γ ->
      wf_sort Σ s ->
      wf_sort Σ s' ->
      Rs s s' ->
      Σ ;;; Γ ⊢ tSort s ~ tSort s' : tSort (Sort.super s')
where " Σ ;;; Γ ⊢ t ~ t' : T " := (context_closure _ _ Γ t t' T) (only parsing).

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

End Closure.

Check context1_closure.

(* Begin Closure renotations *)
  Notation " Σ ;;; Γ ⊢ t ~>0 t' : T " := (@red0 _ Σ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ≡>0 t' : T " := (@pred0 _ Σ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ≡>0 t' : T 'with' R " := (@pred0 _ Σ R Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t ~ext t' : T " := (@ext_eq _ Σ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ~ext t' : T 'with' R " := (@ext_eq _ Σ R Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t ~ t' : T " := (@context_closure _ Σ _ _ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ~ t' : T 'with' R , R' , R'' " := (@context_closure _ Σ R R' R'' Γ t t' T) (only parsing).
  Notation " Σ ;;; Γ ⊢ t ~1 t' : T " := (@context1_closure _ Σ _ Γ t t' T).
  Notation " Σ ;;; Γ ⊢ t ~1 t' : T 'with' R " := (@context1_closure _ Σ R Γ t t' T) (only parsing).
(* End Closure notations *)

Lemma pred0ε {cf} {TC} Σ R R' Γ t t' T :
  Σ ;;; Γ ⊢ t ≡>0 t' : T with R ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ≡>0 t' : T with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma ext_eqε {cf} {TC} Σ R R' Γ t t' T :
  Σ ;;; Γ ⊢ t ~ext t' : T with R ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~ext t' : T with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context_closureε {cf} {TC} Σ R R' Rα Rα' Rs Rs' Γ t t' T :
  Σ ;;; Γ ⊢ t ~ t' : T with R, Rα, Rs ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  [(Xα na na' : Rα na na' -> Rα' na na')] ->
  [(Xs s s' : Rs s s' -> Rs' s s')] ->
  Σ ;;; Γ ⊢ t ~ t' : T with R', Rα', Rs'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma context1_closureε {cf} {TC} Σ R R' Γ t t' T :
  Σ ;;; Γ ⊢ t ~1 t' : T with R ->
  [(X Γ t t' T : R Γ t t' T -> R' Γ t t' T)] ->
  Σ ;;; Γ ⊢ t ~1 t' : T with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Hint Resolve pred0ε ext_eqε context_closureε context1_closureε : fmap.



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
  - eapply XClosure. eauto with fmap.
Defined.

Inductive pred1 {TC} Σ Γ : forall (t t' T : term), Type :=
  | pred1_pred0 t u T :
      Σ ;;; Γ ⊢ t ≡>0 u : T with pred1 Σ ->
      Σ ;;; Γ ⊢ t ≡>1 u : T

  | pred1_cumul t u T U :
      Σ ;;; Γ ⊢ t ≡>1 u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t ≡>1 u : U

  | pred1_clos t u T :
      Σ ;;; Γ ⊢ t ~ u : T with pred1 Σ, eq, eq ->
      Σ ;;; Γ ⊢ t ≡>1 u : T
where " Σ ;;; Γ ⊢ t ≡>1 t' : T " := (@pred1 _ Σ Γ t t' T).

Definition pred1_rect cf TC Σ P :
  [(Xpred0 Γ t u T :
      Σ ;;; Γ ⊢ t ≡>0 u : T with P ->
      P Γ t u T)] ->
  [(XCumul Γ t u A B :
      Σ ;;; Γ ⊢ t ≡>1 u : A ->
      P Γ t u A ->
      Σ ;;; Γ ⊢ A ≤T B with TC ->
      P Γ t u B )] ->
  [(XClosure Γ t u T :
      Σ ;;; Γ ⊢ t ~ u : T with P, eq, eq ->
      P Γ t u T )] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t ≡>1 u : T)] -> P Γ t u T.
Proof.
  intros.
  revert Γ t u T X.
  fix Xrec 5.
  intros Γ t_ u_ T_ []; try clear t_; try clear u_; try clear T_.
  - apply Xpred0; eauto with fmap.
  - eapply XCumul; eauto.
  - eapply XClosure. eauto with fmap.
Defined.

Inductive hred {TC} Σ Γ : forall (t t' T : term), Type :=
  | hred_refl t T :
      Σ ;;; Γ ⊢ t : T ->
      Σ ;;; Γ ⊢ t ~>h t : T

  | hred_step t u v T :
      Σ ;;; Γ ⊢ t ~>0 u : T ->
      Σ ;;; Γ ⊢ u ~>h v : T ->
      Σ ;;; Γ ⊢ t ~>h v : T

  | hred_cumul t u T U :
      Σ ;;; Γ ⊢ t ~>h u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t ~>h u : U
where " Σ ;;; Γ ⊢ t ~>h t' : T " := (@hred _ Σ Γ t t' T).

Definition hred_rect cf TC Σ P :
  [(Xrefl Γ t T :
      Σ ;;; Γ ⊢ t : T ->
      P Γ t t T)] ->
  [(Xstep Γ t u v T :
      Σ ;;; Γ ⊢ t ~>0 u : T ->
      Σ ;;; Γ ⊢ u ~>h v : T ->
      P Γ u v T ->
      P Γ t v T)] ->
  [(XCumul Γ t u A B :
      Σ ;;; Γ ⊢ t ~>h u : A ->
      P Γ t u A ->
      Σ ;;; Γ ⊢ A ≤T B with TC ->
      P Γ t u B )] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t ~>h u : T)] -> P Γ t u T.
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
      Σ ;;; Γ ⊢ t ~ u : T with P, eq, eq ->
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
  - eapply XClosure. eauto with fmap.
Defined.

Section CumulAddon.
Local Set Elimination Schemes.

Context {cf} {TC} Σ (R : forall (Γ : context) (pb : conv_pb) (t t' T : term), Type).

Notation " Σ ;;; Γ ⊢ t ≤R[ pb ] t' : T " := (R Γ pb t t' T) (only parsing).
Notation " Σ ;;; Γ ⊢ t =R t' : T " := (R Γ Conv t t' T) (only parsing).

Inductive cumul_addon Γ pb : forall (t t' T : term), Type :=
  | cumul_prod na na' A A' B B' s s' :
      eq_binder_annot na na' ->
      Σ ;;; Γ ⊢ A =R A' : tSort s ->
      isSortRel s na.(binder_relevance) ->
      Σ ;;; Γ ,, vass na A ⊢ B ≤R[pb] B' : tSort s' ->
      Σ ;;; Γ ⊢ tProd na A B ≤c[pb] tProd na' A' B' : tSort (Sort.sort_of_product s s')

  | cumul_sort s s' :
      wf_local Σ Γ ->
      wf_sort Σ s ->
      wf_sort Σ s' ->
      compare_sort Σ pb s s' ->
      Σ ;;; Γ ⊢ tSort s ≤c[pb] tSort s' : tSort (Sort.super s')
  (* | (indapp) *)
where " Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T " := (@cumul_addon Γ pb t t' T) (only parsing).

End CumulAddon.
Notation " Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T " := (@cumul_addon _ _ Σ _ Γ pb t t' T).
Notation " Σ ;;; Γ ⊢ t ≤c[ pb ] t' : T 'with' R" := (@cumul_addon _ _ Σ R Γ pb t t' T) (only parsing).

Lemma cumul_addonε {cf} {TC} Σ R R' Γ pb t u T :
  Σ ;;; Γ ⊢ t ≤c[pb] u : T with R ->
  [(X Γ pb t u T : R Γ pb t u T -> R' Γ pb t u T)] ->
  Σ ;;; Γ ⊢ t ≤c[pb] u : T with R'.
Proof.
  intros H X.
  induction H.
  all: try now econstructor.
Defined.

Lemma cumul_addon_clos {cf} {TC} Σ R R' Γ t u T :
  Σ ;;; Γ ⊢ t ≤c[Conv] u : T with R ->
  [(X Γ pb t u T : pb = Conv -> R Γ pb t u T -> R' Γ t u T)] ->
  Σ ;;; Γ ⊢ t ~ u : T with R', eq_binder_annot, eq_sort Σ.
Proof.
  intros H X.
  induction H.
  all: now econstructor.
Qed.

Hint Resolve cumul_addonε : fmap.

Inductive equality {cf} {TC} Σ Γ pb : forall (t t' T : term), Type :=
  | eq_ext t u T :
      Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ => equality Σ Γ Conv) ->
      Σ ;;; Γ ⊢ t <=[pb] u : T
  | eq_cumul_addon t u T :
      Σ ;;; Γ ⊢ t ≤c[pb] u : T with equality Σ ->
      Σ ;;; Γ ⊢ t <=[pb] u : T
  | eq_cumul t u T U :
      Σ ;;; Γ ⊢ t <=[pb] u : T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      Σ ;;; Γ ⊢ t <=[pb] u : U
  | eq_clos t u T :
      Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => equality Σ Γ Conv), eq_binder_annot, eq_sort Σ ->
      Σ ;;; Γ ⊢ t <=[pb] u : T
where " Σ ;;; Γ ⊢ t <=[ pb ] t' : T " := (@equality _ _ Σ Γ pb t t' T).

Definition equality_rect cf TC Σ P :
  [(Xext Γ pb t u T :
      Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ => P Γ Conv) ->
      P Γ pb t u T)] ->
  [(XCumulAddon Γ pb t u T :
      Σ ;;; Γ ⊢ t ≤c[pb] u : T with P ->
      P Γ pb t u T)] ->
  [(XCumul Γ pb t u T U :
      Σ ;;; Γ ⊢ t <=[pb] u : T ->
      P Γ pb t u T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      P Γ pb t u U )] ->
  [(XClosure Γ pb t u T :
      Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => P Γ Conv), eq_binder_annot, eq_sort Σ ->
      P Γ pb t u T )] ->

  forall Γ pb t u T, [(X : Σ ;;; Γ ⊢ t <=[pb] u : T)] -> P Γ pb t u T.
Proof.
  intros.
  revert Γ pb t u T X.
  fix Xrec 6.
  intros Γ pb_ t_ u_ T_ []; try clear pb_; try clear t_; try clear u_; try clear T_.
  - apply Xext; eauto with fmap.
  - eapply XCumulAddon; eauto with fmap.
  - eapply XCumul; eauto.
  - eapply XClosure. eauto with fmap.
Defined.

Inductive conv {cf} {TC} Σ Γ (pb : conv_pb) : forall (t t' T : term), Type :=
  | conv_red0_l t t' u T :
      Σ ;;; Γ ⊢ t ~>0 t' : T ->
      Σ ;;; Γ ⊢ t' <==[pb] u : T ->
      Σ ;;; Γ ⊢ t <==[pb] u : T
  | conv_red0_r t u u' T :
      Σ ;;; Γ ⊢ u ~>0 u' : T ->
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

Definition conv_rect cf TC Σ P :
  [(XRed0L Γ pb t t' u T :
      Σ ;;; Γ ⊢ t ~>0 t' : T ->
      Σ ;;; Γ ⊢ t' <==[pb] u : T ->
      P Γ pb t' u T ->
      P Γ pb t u T)] ->
  [(XRed0R Γ pb t u u' T :
      Σ ;;; Γ ⊢ u ~>0 u' : T ->
      Σ ;;; Γ ⊢ t <==[pb] u' : T ->
      P Γ pb t u' T ->
      P Γ pb t u T)] ->
  [(Xext Γ pb t u T :
      Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ => P Γ Conv) ->
      P Γ pb t u T)] ->
  [(XCumulAddon Γ pb t u T :
      Σ ;;; Γ ⊢ t ≤c[pb] u : T with P ->
      P Γ pb t u T)] ->
  [(XCumul Γ pb t u T U :
      Σ ;;; Γ ⊢ t <==[pb] u : T ->
      P Γ pb t u T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      P Γ pb t u U )] ->
  [(XClosure Γ pb t u T :
      Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => P Γ Conv), eq_binder_annot, eq_sort Σ ->
      P Γ pb t u T )] ->

  forall Γ pb t u T, [(X : Σ ;;; Γ ⊢ t <==[pb] u : T)] -> P Γ pb t u T.
Proof.
  intros.
  revert Γ pb t u T X.
  fix Xrec 6.
  intros Γ pb_ t_ u_ T_ []; try clear pb_; try clear t_; try clear u_; try clear T_.
  - eapply XRed0L; eauto.
  - eapply XRed0R; eauto.
  - apply Xext; eauto with fmap.
  - eapply XCumulAddon; eauto with fmap.
  - eapply XCumul; eauto.
  - eapply XClosure. eauto with fmap.
Defined.

Definition conv_Conv_rect cf TC Σ P :
  [(XRed0L Γ t t' u T :
      Σ ;;; Γ ⊢ t ~>0 t' : T ->
      Σ ;;; Γ ⊢ t' === u : T ->
      P Γ t' u T ->
      P Γ t u T)] ->
  [(XRed0R Γ t u u' T :
      Σ ;;; Γ ⊢ u ~>0 u' : T ->
      Σ ;;; Γ ⊢ t === u' : T ->
      P Γ t u' T ->
      P Γ t u T)] ->
  [(Xext Γ t u T :
      Σ ;;; Γ ⊢ t ~ext u : T with P ->
      P Γ t u T)] ->
  [(XCumul Γ t u T U :
      Σ ;;; Γ ⊢ t === u : T ->
      P Γ t u T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      P Γ t u U )] ->
  [(XClosure Γ t u T :
      Σ ;;; Γ ⊢ t ~ u : T with P, eq_binder_annot, eq_sort Σ ->
      P Γ t u T )] ->

  forall Γ t u T, [(X : Σ ;;; Γ ⊢ t === u : T)] -> P Γ t u T.
Proof.
  intros.
  remember Conv as pb eqn:e in X. revert e.
  induction X => e; subst pb.
  - eapply XRed0L; eauto.
  - eapply XRed0R; eauto.
  - apply Xext; eauto with fmap.
  - apply XClosure.
    eapply cumul_addon_clos; eauto.
  - eapply XCumul; eauto.
  - eapply XClosure. eauto with fmap.
Defined.


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

Notation "`≡`" := (fun Σ Γ t t' T => Σ ;;; Γ ⊢ t ≡ t' : T).

Lemma conv_alt_eq_pb {cf} {TC} Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t ≡ u : T ->
  Σ ;;; Γ ⊢ t ≦[ pb ] u : T.
Proof. intro; now do 2 apply conv_alt_sym. Defined.

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
      Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ => P Γ Conv) ->
      P Γ pb t u T)] ->
  [(XCumulAddon Γ pb t u T :
      Σ ;;; Γ ⊢ t ≤c[pb] u : T with P ->
      P Γ pb t u T)] ->
  [(XCumul Γ pb t u T U :
      Σ ;;; Γ ⊢ t ≦[pb] u : T ->
      P Γ pb t u T ->
      Σ ;;; Γ ⊢ T ≤T U ->
      P Γ pb t u U )] ->
  [(XClosure Γ pb t u T :
      Σ ;;; Γ ⊢ t ~ u : T with (fun Γ => P Γ Conv), eq_binder_annot, eq_sort Σ ->
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
  - apply Xext; eauto with fmap.
  - eapply XCumulAddon; eauto with fmap.
  - eapply XCumul; eauto.
  - eapply XClosure. eauto with fmap.
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


(* Spec Alt to regular spec *)

Class AltToSpecPrecondition {cf TC} Σ := {
    ATS_tying_spec : forall Γ t T, Σ ;;; Γ ⊢ t : T -> Σ ;;; Γ ⊢ t = t : T;
  }.
Arguments AltToSpecPrecondition : clear implicits.

Lemma red0_to_spec {cf TC} Σ (PC : AltToSpecPrecondition cf TC Σ) Γ t u T :
  Σ ;;; Γ ⊢ t ~>0 u : T -> Σ ;;; Γ ⊢ t = u : T.
Proof.
  induction 1.
  + destruct l as (_ & s & HA & _ & Hs); cbn in *.
    econstructor 3; eauto.
    all: try eapply ATS_tying_spec => //=.
  + now eapply tc_cumul.
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
      all: now eapply ATS_tying_spec.
    + eapply tc_sym, tc_eta; tea.
      all: now eapply ATS_tying_spec.
    + eapply tc_lambda; trea.
      { now eapply ATS_tying_spec. }
      now eapply XP.
    all: try eapply ATS_tying_spec => //=.
  - eapply tc_sprop.
    all: try eapply ATS_tying_spec => //=.
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
    eapply ext_to_spec; eauto.
  - eapply cumul_addon_to_spec; eauto.
  - eapply tc_cumul; eauto.
  - apply tc_eq_pb.
    eapply closure_to_spec; eauto.
Qed.


Instance AltSoundPreconditionI {cf TC} Σ : AltToSpecPrecondition cf TC Σ := {| ATS_tying_spec := typing_to_typed_conv _ |}.

(* Regular Spec to alt *)

Class SpecToAltPrecondition {cf TC} Σ := {
    STA_spec_typing : forall Γ t t' T, Σ ;;; Γ ⊢ t ≡ t' : T -> Σ ;;; Γ ⊢ t : T;
    STA_alt_inst : forall Γ pb t u T σ σ' Δ,
      Σ ;;; Γ ⊢ t ≦[pb] u : T ->
      Σ ;;; Δ ⊢ σ = σ' : Γ subst with `≡` ->
      Σ ;;; Δ ⊢ t.[σ] ≦[pb] u.[σ'] : T.[σ];
    STA_typing_inst : forall Γ t T σ Δ,
      Σ ;;; Γ ⊢ t : T ->
      Σ ;;; Δ ⊢ σ : Γ subst with typing ->
      Σ ;;; Δ ⊢ t.[σ] : T.[σ];
  }.
Arguments SpecToAltPrecondition : clear implicits.

Lemma beta_alt_complete {cf} {TC} Σ (PC : SpecToAltPrecondition cf TC Σ) Γ t t' na A T u u' s :
  isSortRel s (binder_relevance na) ->
  Σ ;;; Γ ⊢ A ≡ A : tSort s ->
  Σ ;;; Γ,, vass na A ⊢ t ≡ t' : T ->
  Σ ;;; Γ ⊢ u ≡ u' : A ->
  Σ ;;; Γ ⊢ tApp (tLambda na A t) u ≡ t' {0 := u'} : T {0 := u}.
Proof.
  intros Hs XA Xt Xu.
  eapply conv_alt_trans.
  - apply conv_alt_red0.
    econstructor.
    all: try now eapply STA_spec_typing.
    repeat (eexists; cbn; tea).
    now eapply STA_spec_typing.
  - unfold subst1. sigma.
    eapply STA_alt_inst; tea.
    eapply @wellconv_subst_inst with (Γ' := []) (s := [u]) (s' := [u']) (Δ := [_]).
    + constructor. 1: constructor.
      rewrite subst_empty //.
    + intros.
      eapply conv_alt_clos, clos_rel; tas.
      now eapply conv_spec_alt_wf_local.
    + intros. cbn. rewrite -> (inst_ext _ _ (shiftk_0)), subst_ids,
        (inst_ext _ _ (shiftk_0)), subst_ids, (inst_ext _ _ (shiftk_0)), subst_ids.
      apply X.
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
  have /= X2a : Σ ;;; Γ ,, vass na A ⊢ lift0 1 t : lift0 1 (tProd na A B).
  { rewrite lift_rename rename_inst lift_rename rename_inst.
    eapply STA_typing_inst; tea.
    rewrite ren_lift_renaming.
    eapply @welltyped_lift_rename_inst. with (Γ' := []) (s := [u]) (s' := [u']) (Δ := [_]).

    eassumption. }
  have /= X2b : Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 t) (tRel 0) : B.
  { replace B with ((lift 1 1 B) {0 := tRel 0}) by rewrite subst_rel0_lift //.
    econstructor; revgoals.
    - constructor; cbnr; eauto.
    - eassumption.
    - change (tProd _ _ _) with (lift0 1 (tProd na A B)).
      change (tSort ?s) with (lift0 1 (tSort s)).
      rewrite lift_rename rename_inst lift_rename rename_inst.
      eapply STA_typing_inst. eassumption. }

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
    rewrite lift_rename rename_inst lift_rename rename_inst.
    eapply STA_typing_inst.
    eassumption.
  + rewrite lift_rename rename_inst lift_rename rename_inst lift_rename rename_inst.
    eapply STA_typing_inst. eassumption.
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
    all: now eapply STA_spec_typing.
  - apply conv_alt_clos. eapply clos_rel; tas.
  - apply conv_alt_clos. eapply clos_lambda; tea.
  - apply conv_alt_clos. eapply clos_app; tea.
  - apply conv_alt_cumul_addon. eapply cumul_prod; tea.
  - apply conv_alt_cumul_addon. eapply cumul_sort; tea.
  - apply conv_alt_ext. apply ext_sprop.
    all: now eapply STA_spec_typing.
  - now eapply conv_alt_cumul.
Qed.



Lemma conv_sound {cf} {TC} Σ Γ pb t u T :
  Σ ;;; Γ ⊢ t <==[pb] u : T ->
  Σ ;;; Γ ⊢ t ≦[pb] u : T.
Proof.
  induction 1.
  - eapply conv_alt_trans; tea.
    apply conv_alt_red0. assumption.
  - eapply conv_alt_trans; tea.
    apply conv_alt_sym.
    apply conv_alt_red0. assumption.
  - now apply conv_alt_ext.
  - now apply conv_alt_cumul_addon.
  - now eapply conv_alt_cumul.
  - now apply conv_alt_clos.
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
  - eapply conv_red0_l; tea.
    now eapply STC_SR_diag.
  - now apply conv_ext.
  - now apply conv_cumul_addon.
  - now eapply conv_cumul.
  - now apply conv_clos.
Qed.




Lemma conv_eq_pb {cf} {TC} Σ Γ (pb : conv_pb) (t u T : term) :
  Σ ;;; Γ ⊢ t === u : T ->
  Σ ;;; Γ ⊢ t <==[pb] u : T.
Proof.
  intro H. revert Γ t u T H pb.
  apply (conv_Conv_rect _ _ Σ (fun Γ t u T => forall pb, Σ ;;; Γ ⊢ t <==[pb] u : T)).
  all: intros.
  all: try now econstructor.
  - apply conv_ext.
    eauto with fmap.
  - apply conv_clos.
    eauto with fmap.
Qed.

Class ConvSymPrecondition {cf TC} Σ := {
  }.
Arguments ConvSymPrecondition : clear implicits.


Lemma eta_ext_sym {TC} Σ R Γ t u T :
  Σ ;;; Γ ⊢ t ~ext u : T with (fun Γ t u T => R Γ u t T) ->
  Σ ;;; Γ ⊢ u ~ext t : T with R.
Proof.
  induction 1.
  all: try now econstructor.
Qed.

Lemma context_closure_conv_sym {cf} {TC} Σ (PC : ConvSymPrecondition cf TC Σ) Γ t u T :
  Σ ;;; Γ ⊢ t ~ u : T with (fun Γ t u T => conv Σ Γ Conv u t T), eq_binder_annot, eq_sort Σ ->
  Σ ;;; Γ ⊢ u === t : T.
Proof.
  induction 1.
  - now apply conv_clos, clos_rel.
  - eapply conv_cumul.
    1: eapply conv_clos, clos_lambda; tea.
    + now symmetry.
    + rewrite -r //.
    + admit.
    + admit.
  - eapply conv_cumul.
    1: eapply conv_clos, clos_app; tea.
    +
  - eapply conv_cumul.
    1: eapply conv_clos, clos_prod; tea.
    + now symmetry.
    + rewrite -r //.
    +
    +
  - eapply conv_cumul.
    1: eapply conv_clos, clos_sort; tea.
    + now symmetry in r.
    +
Admitted.

Lemma conv_sym {cf} {TC} Σ (PC : ConvSymPrecondition cf TC Σ) Γ t u T :
  Σ ;;; Γ ⊢ t === u : T ->
  Σ ;;; Γ ⊢ u === t : T.
Proof.
  intro H. revert Γ t u T H.
  apply (conv_Conv_rect _ _ Σ (fun Γ t u T => Σ ;;; Γ ⊢ u === t : T)).
  all: intros.
  all: try now econstructor.
  - apply conv_ext.
    now apply eta_ext_sym.
  - apply conv_clos.
    now apply context_closure_sym.
Qed.





(*


- algo context conversion: Γ, Δ |- t <== u : T -> All_local_rel (<==) Δ Δ' -> Γ, Δ' |- t <== u : T
  needs: beta context conversion (<==), typing context conversion (<==), cumul_addon context conversion (<==), ≤T context conversion (<==), context closure context conversion (<==)

- beta context conversion: Γ, Δ |- t ~>β u : T -> All_local_rel R Δ Δ' -> Γ, Δ' |- t ~>β u : T
  needs: typing context conversion (R)

- cumul_addon context conversion: Γ, Δ |- t ≤c u : T -> All_local_rel R Δ Δ' -> Γ, Δ' |- t ≤c u : T
  needs: typing context conversion (R), R context conversion

- context closure context conversion: Γ, Δ |- t ~ u : T -> All_local_rel R Δ Δ' -> Γ, Δ' |- t ~ u : T
  needs: typing context conversion (R), R context conversion


- typing context conversion: Γ, Δ |- t : T -> All_local_rel R Δ Δ' -> Γ, Δ' |- t : T
  needs: R typed reflexivity, R weakening, R incl ≤T, ≤T context conversion


- typed alternate conv -> typing: Γ |- t ≤ u : T -> Γ |- t : T & Γ |- u : T
  needs: algorithmic complete, algorithmic conv -> typing

- typed algorithmic conv -> typing: Γ |- t <== u : T -> Γ |- t : T & Γ |- u : T
  needs: algorithmic complete, algorithmic conv -> typing

- beta -> typing: Γ |- t ~>β u : T -> Γ |- t : T
  needs: nothing

- cumul_addon -> typing: Γ |- t ≤c u : T -> Γ |- t : T & Γ |- u : T
  needs: (<==) incl ≤T

- context closure -> typing: Γ |- t ~ u : T -> Γ |- t : T & Γ |- u : T
  needs: typing context conversion (R)


- "right-strong injectivity" of products and sorts: T ≤ tProd na A' B' -> T ~>h tProd na A B & A ≅ A' & B ≤ B'
  needs:
    + algorithmic complete (Γ |- T <== tProd na A' B' : tSort s)
    + [inversion] Γ |- T h~> T' : tSort s, Γ |- T' ≤c tProd na A' B' : tSort s / ~
    + [inversion] T' = tProd na A B, Γ |- A === A' : tSort sa, Γ ,, (na, A) |- B <== B' : tSort sb (thus Γ |- T ~>h T' : tSort s)
    + === incl <== to account for case ~
    + algorithmic sound: Γ |- T ~>h tProd na A B : tSort s, Γ |- A ≡ A' : tSort sa, Γ ,, (na, A) |- B ≤ B' : tSort sb

- === incl <==: needs nothing


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
