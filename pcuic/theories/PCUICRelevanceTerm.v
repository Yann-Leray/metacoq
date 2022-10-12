From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICRelevance PCUICInduction PCUICCases PCUICSigmaCalculus PCUICLiftSubst PCUICWeakeningEnv PCUICOnFreeVars.

Require Import ssreflect.
From Equations Require Import Equations.


Lemma extends_isTermRel {cf : checker_flags} {Pcmp P} Σ Σ' Γ t rel :
  on_global_env Pcmp P Σ' ->
  extends Σ Σ' ->
  isTermRel Σ Γ t rel ->
  isTermRel Σ' Γ t rel.
Proof.
  induction t in Γ, rel |- * using term_forall_list_ind;
    intros wfΣ' ext Hirr; depelim Hirr; try solve [econstructor; eauto with extends].
  - destruct X as (X & X' & X'').
    destruct w as (H & H' & H'').
    econstructor; eauto with extends.
    1: repeat split; eauto with extends.
    + solve_all. destruct b; eauto.
    + clear -wfΣ' ext X' H'.
      induction H'.
      1: constructor.
      all: depelim X'; apply IHH' in X'; constructor; auto.
      all: destruct o; destruct t0; split; cbn in *; eauto.
      destruct o0; eauto.
    + solve_all.
      destruct b as (Hc & Hb); split.
      * induction Hc.
        1: constructor.
        all: depelim a0; apply IHHc in a0; constructor; auto.
        all: destruct o; destruct t1; split; cbn in *; eauto.
        destruct o0; eauto.
      * destruct Hb; eauto.
  - constructor; unfold wfTermRel_mfix in *; solve_all.
  - constructor; unfold wfTermRel_mfix in *; solve_all.
Qed.

#[global] Hint Resolve extends_isTermRel : extends.


Lemma extends_isTermRelOpt {cf : checker_flags} {Pcmp P} Σ Σ' Γ t relopt :
  on_global_env Pcmp P Σ' ->
  extends Σ Σ' ->
  isTermRelOpt Σ Γ t relopt ->
  isTermRelOpt Σ' Γ t relopt.
Proof.
  destruct relopt => //=; eauto with extends.
Qed.

#[global] Hint Resolve extends_isTermRelOpt : extends.

Lemma isTermRel_is_open_term Σ Γ t rel : isTermRel Σ Γ t rel -> is_open_term Γ t.
Proof.
  intro wft.
  induction t in Γ, rel, wft |- * using term_forall_list_ind; cbn.
  all: try solve [ eauto ].
  all: depelim wft.
  all: try solve [ rtoProp; repeat split; auto; rewrite -?shiftnP_S; eauto ].
  - apply nth_error_Some_length, Nat.ltb_lt in e.
    unfold is_open_term, shiftnP. now rewrite e.
  - rtoProp; repeat split; eauto. rewrite -shiftnP_S. eapply (IHt2 (Γ ,, _)); tea.
  - rtoProp; repeat split; eauto. rewrite -shiftnP_S. eapply (IHt2 (Γ ,, _)); tea.
  - rtoProp; repeat split; eauto. rewrite -shiftnP_S. eapply (IHt3 (Γ ,, _)); tea.
  - destruct X as (X & X' & X''), w as (H & H' & H'').
    rtoProp; repeat split; eauto.
    + solve_all. now destruct b.
    + apply X'' in H''.
      rewrite app_length -shiftnP_add map_length inst_case_predicate_context_length in H'' => //.
    + induction (pcontext p) using ctx_ind.
      1: constructor.
      all: inv X'; inv H'; cbn; rtoProp; split; auto.
      all: destruct X1; destruct X4; cbn in *; eauto.
      1: apply i in i0; rewrite app_length map_length repeat_length -closedP_shiftnP in i0 => //.
      unfold test_decl; cbn; rtoProp; split.
      1: destruct o0; apply o in i1; rewrite app_length map_length repeat_length -closedP_shiftnP in i1 => //.
      1: apply i in i0; rewrite app_length map_length repeat_length -closedP_shiftnP in i0 => //.
    + solve_all; destruct b as (Hc & Hb).
      2: destruct Hb; apply b0 in i; rewrite app_length !map_length -shiftnP_add inst_case_branch_context_length in i => //.
      clear -a0 Hc.
      induction (bcontext x) using ctx_ind.
      1: constructor.
      all: inv a0; inv Hc; cbn; rtoProp; split; auto.
      all: destruct X; destruct X2; cbn in *; eauto.
      1: apply i in i0; rewrite app_length map_length repeat_length -closedP_shiftnP in i0 => //.
      unfold test_decl; cbn; rtoProp; split.
      1: destruct o0; apply o in i1; rewrite app_length map_length repeat_length -closedP_shiftnP in i1 => //.
      1: apply i in i0; rewrite app_length map_length repeat_length -closedP_shiftnP in i0 => //.
  - unfold wfTermRel_mfix in *; solve_all. rtoProp. unfold test_def; rtoProp; split; eauto.
    apply b0 in a; rewrite app_length map_length fix_context_length -shiftnP_add in a => //.
  - unfold wfTermRel_mfix in *; solve_all. rtoProp. unfold test_def; rtoProp; split; eauto.
    apply b0 in a; rewrite app_length map_length fix_context_length -shiftnP_add in a => //.
Qed.

Lemma wfTermRel_is_open_term Σ Γ t : wfTermRel Σ Γ t -> is_open_term Γ t.
Proof. intros []; now eapply isTermRel_is_open_term. Qed.

Lemma is_open_term_on_free_vars {A} P (Γ: list A) t : is_open_term Γ t -> on_free_vars (shiftnP #|Γ| P) t.
Proof. apply on_free_vars_impl => i. rewrite /shiftnP orb_false_r => -> //. Qed.
