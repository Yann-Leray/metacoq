(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms. 
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICSigmaCalculus PCUICClosed 
     PCUICOnFreeVars PCUICTyping PCUICReduction PCUICGlobalEnv PCUICWeakeningEnvConv
     PCUICEquality.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma type_local_ctx_All_local_env {cf} P Σ Γ Δ s : 
  All_local_env (lift_typing P Σ) Γ ->
  type_local_ctx (lift_typing P) Σ Γ Δ s ->
  All_local_env (lift_typing P Σ) (Γ ,,, Δ).
Proof.
  induction Δ; simpl; auto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition auto.
   exists s; auto.
Qed.

Lemma sorts_local_ctx_All_local_env {cf} P Σ Γ Δ s : 
  All_local_env (lift_typing P Σ) Γ ->
  sorts_local_ctx (lift_typing P) Σ Γ Δ s ->
  All_local_env (lift_typing P Σ) (Γ ,,, Δ).
Proof.
  induction Δ in s |- *; simpl; eauto.
  destruct a as [na [b|] ty];
  intros wfΓ wfctx; constructor; intuition eauto.
  destruct s => //. destruct wfctx; eauto.
  destruct s => //. destruct wfctx. exists t; auto.
Qed.

Lemma type_local_ctx_Pclosed {cf} Σ Γ Δ s :
  type_local_ctx (lift_typing Pclosed) Σ Γ Δ s ->
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev Δ).
Proof.
  induction Δ; simpl; auto; try constructor.  
  destruct a as [? [] ?]; intuition auto.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in b0. simpl.
    rewrite app_context_length in b0. now rewrite Nat.add_comm.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in b0. simpl.
    rewrite app_context_length in b0. rewrite Nat.add_comm.
    now rewrite andb_true_r in b0.
Qed.

Lemma sorts_local_ctx_Pclosed {cf} Σ Γ Δ s :
  sorts_local_ctx (lift_typing Pclosed) Σ Γ Δ s ->
  Alli (fun i d => closed_decl (#|Γ| + i) d) 0 (List.rev Δ).
Proof.
  induction Δ in s |- *; simpl; auto; try constructor.  
  destruct a as [? [] ?]; intuition auto.
  - apply Alli_app_inv; eauto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in b0. simpl.
    rewrite app_context_length in b0. now rewrite Nat.add_comm.
  - destruct s as [|u us]; auto. destruct X as [X b].
    apply Alli_app_inv; eauto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in b. simpl.
    rewrite app_context_length in b. rewrite Nat.add_comm.
    now rewrite andb_true_r in b.
Qed.

Lemma All_local_env_Pclosed {cf} Σ Γ :
  All_local_env (lift_typing Pclosed Σ) Γ ->
  Alli (fun i d => closed_decl i d) 0 (List.rev Γ).
Proof.
  induction Γ; simpl; auto; try constructor.  
  intros all; depelim all; intuition auto.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed in l. simpl. red in l.
    destruct l as [s H].
    now rewrite andb_true_r in H.
  - apply Alli_app_inv; auto. constructor. simpl.
    rewrite List.rev_length. 2:constructor.
    unfold closed_decl. unfold Pclosed, lift_typing in *. now simpl.
Qed.

Lemma weaken_env_prop_closed {cf} : 
  weaken_env_prop (lift_typing (fun (_ : global_env_ext) (Γ : context) (t T : term) =>
  closedn #|Γ| t && closedn #|Γ| T)).
Proof. repeat red. intros. destruct t; red in X0; eauto. Qed.


Lemma closedn_ctx_alpha {k ctx ctx'} : 
  eq_context_upto_names ctx ctx' ->
  closedn_ctx k ctx = closedn_ctx k ctx'.
Proof.
  induction 1 in k |- *; simpl; auto.
  rewrite IHX. f_equal.
  rewrite (All2_length X).
  destruct r; cbn; now subst.
Qed.

Lemma on_global_env_impl `{checker_flags} Σ P Q :
  (forall Σ Γ t T, on_global_env P Σ.1 ->
    on_global_env Q Σ.1 -> P Σ Γ t T -> Q Σ Γ t T) ->
  on_global_env P Σ -> on_global_env Q Σ.
Proof.
  intros X X0.
  simpl in *. destruct X0 as [ongu ond]; constructor; auto.
  destruct Σ as [univs Σ]; cbn in *.
  induction ond; constructor; auto.
  destruct d; simpl.
  - destruct c; simpl. destruct cst_body0; simpl in *; now eapply X.
  - red in o. simpl in *.
    destruct o0 as [onI onP onNP].
    constructor; auto.
    -- eapply Alli_impl. exact onI. eauto. intros.
       refine {| ind_arity_eq := X0.(ind_arity_eq);
                 ind_cunivs := X0.(ind_cunivs) |}.
       --- apply onArity in X0. unfold on_type in *; simpl in *.
           now eapply X.
       --- pose proof X0.(onConstructors) as X11. red in X11.
          eapply All2_impl; eauto.
          simpl. intros. destruct X1 as [? ? ? ?]; unshelve econstructor; eauto.
          * apply X; cbn; eauto. split; eauto. split; eauto.
          * clear -X0 ond ongu IHond X on_cargs. revert on_cargs.
            generalize (cstr_args x0).
            induction c in y |- *; destruct y; simpl; auto;
              destruct a as [na [b|] ty]; simpl in *; auto;
          split; intuition eauto.
          all: apply X; try split; cbn; eauto.
          * clear -X0 ond ongu IHond X on_cindices.
            revert on_cindices.
            generalize (List.rev (lift_context #|cstr_args x0| 0 (ind_indices x))).
            generalize (cstr_indices x0).
            induction 1; simpl; constructor; auto. apply X; try split; cbn; eauto.
       --- simpl; intros. pose (onProjections X0 H0). simpl in *; auto.
       --- destruct X0. simpl. unfold check_ind_sorts in *.
           destruct Universe.is_prop => //.
           destruct Universe.is_sprop; auto.
           split.
           * apply ind_sorts.
           * destruct indices_matter; auto.
             eapply type_local_ctx_impl. eapply ind_sorts.
             intros. apply X; eauto; split; eauto.
      --- eapply X0.(ind_relevance_compat).
      --- eapply X0.(onIndices).
    -- red in onP. red.
       eapply All_local_env_impl. eauto.
       intros. now apply X.
Qed.

Lemma closedn_All_local_env (ctx : list context_decl) :
  All_local_env 
    (fun (Γ : context) (b : term) (t : typ_or_rel_or_none) =>
      closedn #|Γ| b && typ_or_rel_or_none_default (closedn #|Γ|) t true) ctx ->
    closedn_ctx 0 ctx.
Proof.
  induction 1; auto; rewrite closedn_ctx_cons IHX /=; now move/andP: t0 => [].
Qed.

Lemma declared_minductive_closed_inds {cf} {Σ ind mdecl u} {wfΣ : wf Σ} :
  declared_minductive Σ (inductive_mind ind) mdecl ->
  forallb (closedn 0) (inds (inductive_mind ind) u (ind_bodies mdecl)).
Proof.
  intros h.
  red in h.
  eapply lookup_on_global_env in h. 2: eauto.
  destruct h as [Σ' [ext wfΣ' decl']].
  red in decl'. destruct decl' as [h ? ? ?].
  rewrite inds_spec. rewrite forallb_rev.
  unfold mapi.
  generalize 0 at 1. generalize 0. intros n m.
  induction h in n, m |- *.
  - reflexivity.
  - simpl. eauto.
Qed.

Lemma closed_cstr_branch_context_gen {cf : checker_flags} {Σ} {wfΣ : wf Σ} {c mdecl cdecl} : 
  closed_inductive_decl mdecl ->
  closed_constructor_body mdecl cdecl ->
  closedn_ctx (context_assumptions mdecl.(ind_params)) (cstr_branch_context c mdecl cdecl).
Proof.
  intros cl clc.
  move/andP: cl => [] clpars _.
  move/andP: clc => [] /andP [] clargs clinds cltype.
  rewrite /cstr_branch_context /=.
  eapply (closedn_ctx_expand_lets 0) => // /=.
  eapply (closedn_ctx_subst 0). len. now rewrite Nat.add_comm.
  eapply closed_inds.
Qed.

Lemma closedn_All_local_closed:
  forall (cf : checker_flags) (Σ : global_env_ext) (Γ : context) (ctx : list context_decl)
         (wfΓ' : wf_local Σ (Γ ,,, ctx)),
    All_local_env_over typing
    (fun (Σ0 : global_env_ext) (Γ0 : context) (_ : wf_local Σ0 Γ0) (t T : term) (_ : Σ0;;; Γ0 |- t : T) =>
       closedn #|Γ0| t && closedn #|Γ0| T) Σ (Γ ,,, ctx) wfΓ' ->
    closedn_ctx 0 Γ && closedn_ctx #|Γ| ctx.
Proof.
  intros cf Σ Γ ctx wfΓ' al.
  remember (Γ ,,, ctx) as Γ'. revert Γ' wfΓ' ctx HeqΓ' al.
  induction Γ. simpl. intros. subst. unfold app_context in *. rewrite app_nil_r in wfΓ' al.
  induction al; try constructor;
  rewrite closedn_ctx_cons /=; cbn.
  move/andP: p => [] /= -> _. now rewrite IHal.
  now rewrite IHal /= /test_decl /=.
  intros.
  unfold app_context in *. subst Γ'.
  specialize (IHΓ (ctx ++ a :: Γ) wfΓ' (ctx ++ [a])).
  rewrite -app_assoc in IHΓ. specialize (IHΓ eq_refl al).
  rewrite closedn_ctx_app /= Nat.add_1_r andb_assoc in IHΓ.
  now rewrite closedn_ctx_cons /=.
Qed.

