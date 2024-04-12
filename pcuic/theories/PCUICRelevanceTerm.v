From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICRelevance PCUICInduction PCUICCases PCUICSigmaCalculus PCUICLiftSubst PCUICWeakeningEnv PCUICOnFreeVars.

Require Import ssreflect.
From Equations Require Import Equations.


Lemma extends_isTermRel {cf : checker_flags} {Pcmp P} Σ Σ' Γ t r :
  on_global_env Pcmp P Σ' ->
  extends Σ Σ' ->
  isTermRel Σ Γ t r ->
  isTermRel Σ' Γ t r.
Proof using Type.
  intros wf ext.
  revert Γ t r.
  fix rec 4.
  intros ???[].
  all: try solve [ econstructor; eauto ].
  - econstructor.
    now eapply weakening_env_declared_constant.
  - econstructor.
    now eapply weakening_env_declared_constructor.
  - econstructor; eauto.
    1: now eapply weakening_env_declared_inductive.
    + destruct w as (? & ? & ?). repeat (split; tea); eauto.
      induction c0; econstructor; eauto.
    + induction a; constructor; eauto. destruct r0; split; eauto.
  - econstructor; eauto.
    now eapply weakening_env_declared_projection.
  - econstructor; eauto.
    set (Ξ := fix_context mfix) in *. clearbody Ξ. clear -w rec.
    induction w; constructor; eauto.
    destruct p; split; auto.
  - econstructor; eauto.
    set (Ξ := fix_context mfix) in *. clearbody Ξ. clear -w rec.
    induction w; constructor; eauto.
    destruct p; split; auto.
  - destruct p as (? & []); inv p0; do 2 econstructor.
    all: eauto.
    solve_all.
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

From MetaCoq.PCUIC Require Import PCUICGlobalEnv PCUICTyping PCUICClosed PCUICClosedConv PCUICClosedTyp.

Lemma isTermRel_closedn {cf : checker_flags} Σ Γ t rel : wf Σ -> isTermRel Σ Γ t rel -> closedn #|Γ| t.
Proof.
  intros wfΣ wft.
  induction t in Γ, rel, wft |- * using term_forall_list_ind; cbn.
  all: try solve [ eauto ].
  all: depelim wft.
  all: try solve [ rtoProp; repeat split; auto; rewrite -?shiftnP_S; eauto ].
  - apply nth_error_Some_length, Nat.ltb_lt in e.
    unfold is_open_term, shiftnP. now rewrite e.
  - rtoProp; repeat split; eauto. eapply (IHt2 (Γ ,, _)); tea.
  - rtoProp; repeat split; eauto. eapply (IHt2 (Γ ,, _)); tea.
  - rtoProp; repeat split; eauto. eapply (IHt3 (Γ ,, _)); tea.
  - eapply wfTermRel_pred_wf_predicate in w as Hp; tea. 2: apply d.
    eapply @declared_minductive_closed in wfΣ as Xcl. 2: apply d.
    destruct X as (X & X' & X''), w as (H & H' & H'').
    unfold test_predicate_k; rtoProp; repeat split; eauto.
    + induction H in X |- *; [|depelim X|]; cbn; eauto. erewrite i; eauto.
    + rewrite (closedn_ctx_alpha H').
      eapply closed_ind_predicate_context in Xcl; tea.
      rewrite (wf_predicate_length_pars Hp).
      now rewrite (declared_minductive_ind_npars d).
    + apply X'' in H''.
      rewrite app_length map_length case_predicate_context_length in H'' => //.
    + pose proof (closed_ind_closed_cstrs Xcl d).
      unfold test_branch_k. solve_all; destruct b0 as (Hc & Hb).
      2: {
        assert (wf_branch x y) as wfb by (eapply wfTermRel_pred_wf_branch; now split).
        apply b1 in Hb; rewrite app_length !map_length case_branch_context_length in Hb => //. }

      rewrite (closedn_ctx_alpha Hc).
      eapply closed_cstr_branch_context_gen in Xcl; tea.
      rewrite (wf_predicate_length_pars Hp).
      now rewrite (declared_minductive_ind_npars d).

  - unfold wfTermRel_mfix in *; solve_all. rtoProp. unfold test_def; rtoProp; split; eauto.
    apply b0 in a; rewrite app_length map_length fix_context_length in a => //.
  - unfold wfTermRel_mfix in *; solve_all. rtoProp. unfold test_def; rtoProp; split; eauto.
    apply b0 in a; rewrite app_length map_length fix_context_length in a => //.
  - destruct p as [[] pv]; depelim pv; cbnr.
    destruct X as (? & ? & ?). depelim p1. rtoProp; repeat split => //.
    all: eauto.
    solve_all.
Qed.
