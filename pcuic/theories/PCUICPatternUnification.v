(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Lia ssreflect ssrbool.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config (* BasicAst *).
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPattern PCUICPosition PCUICReduction.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Require Import CRelationClasses CMorphisms.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.


Variant pattern_unif_mode := Super | Compat.

Section unifiable.
Context (mode : pattern_unif_mode).
Inductive unifiable_rigid_patterns : rigid_arg_pattern -> rigid_arg_pattern -> Type :=
  | unif_Constr ind n : unifiable_rigid_patterns (pConstr ind n) (pConstr ind n)
  | unif_argApp pf pf' parg parg' :
    unifiable_rigid_patterns pf pf' -> unifiable_arg_patterns parg parg' -> unifiable_rigid_patterns (pargApp pf parg) (pargApp pf' parg')

with unifiable_arg_patterns : arg_pattern -> arg_pattern -> Type :=
  | unif_Hole p : unifiable_arg_patterns p pHole
  | unif_Hole_rev p : mode = Compat -> unifiable_arg_patterns pHole p
  | unif_Rigid p p' : unifiable_rigid_patterns p p' -> unifiable_arg_patterns (pRigid p) (pRigid p').

Inductive unifiable_patterns : pattern -> pattern -> Type :=
  | unif_Head k n : unifiable_patterns (pSymb k n) (pSymb k n)
  | unif_App pf pf' parg parg' :
    unifiable_patterns pf pf' -> unifiable_arg_patterns parg parg' -> unifiable_patterns (pApp pf parg) (pApp pf' parg')
  | unif_Case pc pc' nbrs :
    unifiable_patterns pc pc' -> unifiable_patterns (pCase pc nbrs) (pCase pc' nbrs)
  | unif_Proj pc pc' : unifiable_patterns pc pc' -> unifiable_patterns (pProj pc) (pProj pc').

Scheme unifiable_arg_patterns_mutual_ind := Elimination for unifiable_arg_patterns Sort Type
  with unifiable_rigid_patterns_mutual_ind := Elimination for unifiable_rigid_patterns Sort Type.

Derive Signature for unifiable_rigid_patterns unifiable_arg_patterns unifiable_patterns.
End unifiable.

Fixpoint rigid_super_compat p p' (H : unifiable_rigid_patterns Super p p') : unifiable_rigid_patterns Compat p p'
with arg_super_compat p p' (H : unifiable_arg_patterns Super p p') : unifiable_arg_patterns Compat p p'.
Proof.
  - induction H; constructor => //. apply arg_super_compat => //.
  - induction H; constructor => //. apply rigid_super_compat => //.
Qed.

Lemma pattern_super_compat p p' (H : unifiable_patterns Super p p') : unifiable_patterns Compat p p'.
Proof. induction H => //; constructor => //. apply arg_super_compat => //. Qed.

Fixpoint rigid_unifiable_refl mode p : unifiable_rigid_patterns mode p p
with arg_unifiable_refl mode p : unifiable_arg_patterns mode p p.
Proof.
  - destruct p; constructor => //.
  - destruct p; constructor => //.
Qed.
#[global] Instance rigid_unifiable_refl' mode : Reflexive (unifiable_rigid_patterns mode) := rigid_unifiable_refl mode.
#[global] Instance arg_unifiable_refl' mode : Reflexive (unifiable_arg_patterns mode) := arg_unifiable_refl mode.
#[global] Instance pattern_unifiable_refl mode : Reflexive (unifiable_patterns mode).
Proof. intro p. induction p => //; constructor => //. apply arg_unifiable_refl => //. Qed.

Fixpoint rigid_unifiable_trans p p' p'' (H1 : unifiable_rigid_patterns Super p p') : unifiable_rigid_patterns Super p' p'' -> unifiable_rigid_patterns Super p p''
with arg_unifiable_trans p p' p'' (H1 : unifiable_arg_patterns Super p p') : unifiable_arg_patterns Super p' p'' -> unifiable_arg_patterns Super p p''.
Proof.
  - depelim H1 => //.
    intro H2. depelim H2.
    constructor.
    all: eauto.
  - depelim H1 => //.
    all: intro H2; depelim H2 => //.
    + constructor.
    + constructor.
    + constructor. eauto.
Qed.
#[global] Instance rigid_unifiable_trans' : Transitive (unifiable_rigid_patterns Super) := rigid_unifiable_trans.
#[global] Instance arg_unifiable_trans' : Transitive (unifiable_arg_patterns Super) := arg_unifiable_trans.
#[global] Instance pattern_unifiable_trans : Transitive (unifiable_patterns Super).
Proof. intros p p' p'' H1 H2. induction H1 in p'', H2 |- * => //; depelim H2 => //; constructor => //. all: eauto. etransitivity. all: eassumption. Qed.


Fixpoint unify_arg_patterns_same_root (p p' : arg_pattern) (H : unifiable_arg_patterns Compat p p') : arg_pattern :=
  match H with
  | unif_Hole p | unif_Hole_rev p _ => p
  | unif_Rigid p p' r => pRigid (unify_rigid_patterns_same_root p p' r)
  end
with unify_rigid_patterns_same_root (p p' : rigid_arg_pattern) (H : unifiable_rigid_patterns Compat p p') : rigid_arg_pattern :=
  match H with
  | unif_Constr ind n => pConstr ind n
  | unif_argApp pf pf' parg parg' r r' => pargApp (unify_rigid_patterns_same_root pf pf' r) (unify_arg_patterns_same_root parg parg' r')
  end.

Fixpoint unify_patterns_same_root (p p' : pattern) (H : unifiable_patterns Compat p p') : pattern :=
  match H with
  | unif_Head k n => pSymb k n
  | unif_App pf pf' parg parg' r r' => pApp (unify_patterns_same_root pf pf' r) (unify_arg_patterns_same_root parg parg' r')
  | unif_Case pc pc' nbrs r => pCase (unify_patterns_same_root pc pc' r) nbrs
  | unif_Proj pc pc' r => pProj (unify_patterns_same_root pc pc' r)
  end.

Lemma unifiable_arg_patterns_sound p p' :
  (exists t s s', arg_pattern_matches p t s × arg_pattern_matches p' t s') -> unifiable_arg_patterns Compat p p'.
Proof.
  revert p'.
  induction p using arg_pattern_ind
    with (P0 := fun p => forall p', (exists t s s', rigid_arg_pattern_matches p t s × rigid_arg_pattern_matches p' t s') -> unifiable_rigid_patterns Compat p p'); intros.
  - constructor => //.
  - destruct p'.
    1: constructor.
    constructor.
    apply IHp.
    exact H.
  - destruct p'.
    2: { exfalso. destruct H as (? & ? & ? & r & ?). apply rigid_pattern_matches_app_inv_l in r as (? & ? & ? & ? & -> & -> & ? & ?) => //. }
    constructor.
    + eapply IHp.
      destruct H as (? & ? & ? & r & r').
      apply rigid_pattern_matches_app_inv_l in r as (tf & targ & ? & ? & -> & -> & ? & ?).
      apply rigid_pattern_matches_app_inv in r' as (? & ? & ? & ? & [= <- <-] & [= ->] & ? & ?).
      eexists tf, _, _; now split.
    + eapply IHp0.
      destruct H as (? & ? & ? & r & r').
      apply rigid_pattern_matches_app_inv_l in r as (tf & targ & ? & ? & -> & -> & ? & ?).
      apply rigid_pattern_matches_app_inv in r' as (? & ? & ? & ? & [= <- <-] & [= ->] & ? & ?).
      eexists targ, _, _; now split.
  - destruct p'.
    { exfalso. destruct H as (? & ? & ? & ? & r). apply rigid_pattern_matches_app_inv_l in r as (? & ? & ? & ? & -> & -> & ? & ?) => //. }
    relativize (pConstr ind0 n0).
    1: constructor.
    destruct H as (t & ? & ? & r & r'). revert r r'.
    unfold rigid_arg_pattern_matches.
    destruct t => //=.
    repeat match goal with |- context[eqb ?a ?b] => destruct (eqb_specT a b); subst => // end.
Qed.

Lemma super_arg_patterns_sound p p' :
  unifiable_arg_patterns Super p p' ->
  forall t s, arg_pattern_matches p t s -> ∑ s, arg_pattern_matches p' t s.
Proof.
  intro H.
  induction H using unifiable_arg_patterns_mutual_ind with
    (P0 := fun p p' _ => forall t s, rigid_arg_pattern_matches p t s -> ∑ s, rigid_arg_pattern_matches p' t s); intros.
  - eexists; cbnr.
  - discriminate e.
  - eauto.
  - eauto.
  - apply rigid_pattern_matches_app_inv_l in H0 as (f & arg & s1 & s2 & -> & -> & X1 & X2).
    apply IHunifiable_arg_patterns in X1 as (s1' & X1').
    apply IHunifiable_arg_patterns0 in X2 as (s2' & X2').
    unfold rigid_arg_pattern_matches. cbn.
    rewrite X1' X2'. now eexists.
Qed.


Lemma unify_arg_patterns_same_root_super p p' H :
  let pp := unify_arg_patterns_same_root p p' H in
  unifiable_arg_patterns Super pp p × unifiable_arg_patterns Super pp p'.
Proof.
  induction H using unifiable_arg_patterns_mutual_ind
    with (P0 := fun p p' H => let pp := unify_rigid_patterns_same_root p p' H in
    unifiable_rigid_patterns Super pp p × unifiable_rigid_patterns Super pp p') => //=.
  all: try solve [split; try constructor; eauto using arg_unifiable_refl].
  - destruct IHunifiable_arg_patterns.
    split; constructor => //.
  - destruct IHunifiable_arg_patterns, IHunifiable_arg_patterns0.
    split; constructor => //.
Qed.

Lemma super_unify_arg_patterns_same_root p p' H :
  unifiable_arg_patterns Super p p' ->
  unify_arg_patterns_same_root p p' H = p.
Proof.
  induction H using unifiable_arg_patterns_mutual_ind
    with (P0 := fun p p' H => unifiable_rigid_patterns Super p p' -> unify_rigid_patterns_same_root p p' H = p) => //=.
  all: intro H'; depelim H' => //.
  all: f_equal; auto.
Qed.

Lemma unify_arg_patterns_same_root_sound1 p p' H t s :
  arg_pattern_matches (unify_arg_patterns_same_root p p' H) t s ->
  (∑ s s', arg_pattern_matches p t s × arg_pattern_matches p' t s').
Proof.
  pose proof (unify_arg_patterns_same_root_super _ _ H) as (X1 & X2).
  intro Hp.
  eapply super_arg_patterns_sound in X1 as [], X2 as []; tea.
  now do 2 eexists.
Qed.

Lemma unify_arg_patterns_same_root_sound2 p p' H t s s' :
  arg_pattern_matches p t s -> arg_pattern_matches p' t s' ->
  ∑ s, arg_pattern_matches (unify_arg_patterns_same_root p p' H) t s.
Proof.
  revert t s s'.
  induction H using unifiable_arg_patterns_mutual_ind with
    (P0 := fun p p' H => forall t s s', rigid_arg_pattern_matches p t s -> rigid_arg_pattern_matches p' t s' ->
    ∑ s, rigid_arg_pattern_matches (unify_rigid_patterns_same_root p p' H) t s); intros.
  1,2: now eexists _.
  - cbn. eauto.
  - destruct t => //.
    revert H; unfold rigid_arg_pattern_matches; cbn.
    repeat match goal with |- context[eqb ?a ?b] => destruct (eqb_specT a b); subst => //= end.
    eauto.
  - apply rigid_pattern_matches_app_inv_l in H0 as (f & arg & s1' & s2' & -> & -> & X1' & X2').
    apply rigid_pattern_matches_app_inv_l in H1 as (f' & arg' & s1'' & s2'' & [= <- <-] & -> & X1'' & X2'').
    eapply IHunifiable_arg_patterns in X1' as (s1 & X1); tea.
    eapply IHunifiable_arg_patterns0 in X2' as (s2 & X2); tea.
    unfold rigid_arg_pattern_matches. cbn.
    rewrite X1 X2. now eexists.
Qed.


Lemma unifiable_patterns_sound p p' :
  (exists t s s', pattern_matches p t s × pattern_matches p' t s') -> unifiable_patterns Compat p p'.
Proof.
  induction p in p' |- *; intro H.
  - relativize p'.
    1: constructor.
    destruct H as ([] & ? & ? & r & r') => //.
    now apply pattern_matches_symb_inv in r as ([= <- <-] & _), r' as (-> & _).
  - destruct p'.
    all: try solve [exfalso; destruct H as ([] & ? & ? & r & ?) => //].
    constructor.
    + eapply IHp.
      destruct H as (? & ? & ? & r & r').
      apply pattern_matches_app_inv_l in r as (tf & targ & ? & ? & -> & -> & ? & ?).
      apply pattern_matches_app_inv in r' as (? & ? & ? & ? & [= <- <-] & [= ->] & ? & ?).
      eexists tf, _, _; now split.
    + eapply unifiable_arg_patterns_sound.
      destruct H as (? & ? & ? & r & r').
      apply pattern_matches_app_inv_l in r as (tf & targ & ? & ? & -> & -> & ? & ?).
      apply pattern_matches_app_inv in r' as (? & ? & ? & ? & [= <- <-] & [= ->] & ? & ?).
      eexists targ, _, _; now split.
  - destruct p'.
    all: try solve [exfalso; destruct H as ([] & ? & ? & r & ?) => //].
    relativize nbrs0.
    1: constructor.
    + eapply IHp.
      destruct H as ([] & ? & ? & r & r') => //.
      apply pattern_matches_case_inv in r as (? & ? & [= <- ->] & -> & ? & ?).
      apply pattern_matches_case_inv in r' as (? & ? & [= <- ->] & -> & ? & ?).
      eexists _, _, _; now split.
    + destruct H as ([] & ? & ? & r & r') => //.
      apply pattern_matches_case_inv in r as (? & ? & [= <- ->] & -> & ? & ?).
      apply pattern_matches_case_inv in r' as (? & ? & [= <- ->] & -> & ? & ?).
      reflexivity.
  - destruct p'.
    all: try solve [exfalso; destruct H as ([] & ? & ? & r & ?) => //].
    constructor.
    eapply IHp.
    destruct H as ([] & ? & ? & r & r') => //.
    eexists _, _, _; now split.
Qed.

Lemma super_patterns_sound p p' :
  unifiable_patterns Super p p' ->
  forall t s, pattern_matches p t s -> ∑ s, pattern_matches p' t s.
Proof.
  intro H.
  induction H => //; intros.
  - now eexists.
  - apply pattern_matches_app_inv_l in H0 as (f & arg & s1 & s2 & -> & -> & X1 & X2).
    apply IHunifiable_patterns in X1 as (s1' & X1').
    apply super_arg_patterns_sound with (p' := parg') in X2 as (s2' & X2') => //.
    unfold pattern_matches. cbn.
    rewrite X1' X2'. now eexists.
  - apply pattern_matches_case_inv_l in H0 as (? & ? & ? & ? & ? & -> & -> & -> & flagCase & X).
    apply IHunifiable_patterns in X as (sc' & X').
    unfold pattern_matches. cbn.
    rewrite X' eqb_refl flagCase. now eexists.
  - destruct t => //.
    apply IHunifiable_patterns in H0 as (sc' & X').
    unfold pattern_matches. cbn.
    rewrite X'. now eexists.
Qed.


Lemma unify_patterns_same_root_super p p' H :
  let pp := unify_patterns_same_root p p' H in
  unifiable_patterns Super pp p × unifiable_patterns Super pp p'.
Proof.
  induction H => //=.
  - split; constructor.
  - destruct IHunifiable_patterns.
    destruct (unify_arg_patterns_same_root_super _ _ u).
    split; constructor => //.
  - destruct IHunifiable_patterns.
    split; constructor => //.
  - destruct IHunifiable_patterns.
    split; constructor => //.
Qed.

Lemma super_unify_patterns_same_root p p' H :
  unifiable_patterns Super p p' ->
  unify_patterns_same_root p p' H = p.
Proof.
  induction H => //=.
  all: intro H'; depelim H' => //.
  all: f_equal; auto.
  now apply super_unify_arg_patterns_same_root.
Qed.

Lemma unify_patterns_same_root_sound1 p p' H t s :
  pattern_matches (unify_patterns_same_root p p' H) t s ->
  (∑ s s', pattern_matches p t s × pattern_matches p' t s').
Proof.
  pose proof (unify_patterns_same_root_super _ _ H) as (X1 & X2).
  intro Hp.
  eapply super_patterns_sound in X1 as [], X2 as []; tea.
  now do 2 eexists.
Qed.

Lemma unify_patterns_same_root_sound2 p p' H t s s' :
  pattern_matches p t s -> pattern_matches p' t s' ->
  ∑ s, pattern_matches (unify_patterns_same_root p p' H) t s.
Proof.
  induction H in t, s, s' |- *; cbn; intros.
  1: now eexists _.
  - apply pattern_matches_app_inv_l in H0 as (f & arg & s1' & s2' & -> & -> & X1' & X2').
    apply pattern_matches_app_inv_l in H1 as (f' & arg' & s1'' & s2'' & [= <- <-] & -> & X1'' & X2'').
    eapply IHunifiable_patterns in X1' as (s1 & X1); tea.
    eapply unify_arg_patterns_same_root_sound2 with (H := u) in X2' as (s2 & X2); tea.
    unfold pattern_matches. cbn.
    rewrite X1 X2. now eexists.
  - destruct t => //.
    apply pattern_matches_case_inv in H0 as (? & ? & [= <- ->] & -> & flagCase & X).
    apply pattern_matches_case_inv in H1 as (? & ? & [= <-] & -> & _ & X').
    eapply IHunifiable_patterns in X as (sc' & Xc); tea.
    unfold pattern_matches. cbn.
    rewrite Xc eqb_refl flagCase. now eexists.
  - destruct t => //.
    eapply IHunifiable_patterns in H0 as (sc' & X); tea.
    unfold pattern_matches. cbn.
    rewrite X. now eexists.
Qed.



Section Position.

  Variant anypattern :=
    | Rigid of rigid_arg_pattern
    | Pattern of pattern.

  Fixpoint atpos_arg_pattern t (p : position) {struct t} :=
    match t with
    | pRigid t' => atpos_rigid_pattern t' p
    | pHole => None
    end
  with atpos_rigid_pattern t (p : position) {struct t} :=
    match p with
    | [] => Some (Rigid t)
    | c :: p =>
      match c, t with
      | app_l, pargApp u v => atpos_rigid_pattern u p
      | app_r, pargApp u v => atpos_arg_pattern v p
      | _, _ => None
      end
    end.

  Fixpoint atpos_pattern t (p : position) {struct p} :=
    match p with
    | [] => Some (Pattern t)
    | c :: p =>
      match c, t with
      | app_l, pApp u v => atpos_pattern u p
      | app_r, pApp u v => atpos_arg_pattern v p
      (* | case_preturn, pCase pc nbrs => validpos pr.(preturn) p *)
      | case_c, pCase c nbrs => atpos_pattern c p
      (* | case_brsbody n, tCase ci pr c brs =>
          match nth_error brs n with
          | Some br => validpos br.(bbody) p
          | None => false
          end *)
      | proj_c, pProj c => atpos_pattern c p
      | _, _ => None
      end
    end.

  Definition validpos_arg_pattern p pos : bool := isSome (atpos_arg_pattern p pos).
  Definition validpos_rigid_pattern p pos : bool := isSome (atpos_rigid_pattern p pos).
  Definition validpos_pattern p pos : bool := isSome (atpos_pattern p pos).

  Definition validpos_subpattern_arg_pattern p pos : bool := match atpos_arg_pattern p pos with Some (Pattern _) => true | _ => false end.
  Definition validpos_subpattern_rigid_pattern p pos : bool := match atpos_rigid_pattern p pos with Some (Pattern _) => true | _ => false end.
  Definition validpos_subpattern_pattern p pos : bool := match atpos_pattern p pos with Some (Pattern _) => true | _ => false end.

  Fixpoint term_context_position ctx :=
    match ctx with
    | tCtxHole => []
    | tCtxEvar n l => let res := list_context_position l in evar_arg res.1 :: res.2
    | tCtxProd_l _ ctx _ => prod_l :: term_context_position ctx
    | tCtxProd_r _ _ ctx => prod_r :: term_context_position ctx
    | tCtxLambda_l _ ctx _ => lam_ty :: term_context_position ctx
    | tCtxLambda_r _ _ ctx => lam_tm :: term_context_position ctx
    | tCtxLetIn_l _ ctx _ _ => let_bd :: term_context_position ctx
    | tCtxLetIn_b _ _ ctx _ => let_ty :: term_context_position ctx
    | tCtxLetIn_r _ _ _ ctx => let_in :: term_context_position ctx
    | tCtxApp_l ctx _ => app_l :: term_context_position ctx
    | tCtxApp_r _ ctx => app_r :: term_context_position ctx
    | tCtxCase_pars _ lctx _ _ _ _ _ => let res := list_context_position lctx in case_par res.1 :: res.2
    | tCtxCase_pred _ _ _ _ ctx _ _ => case_preturn :: term_context_position ctx
    | tCtxCase_discr _ _ ctx _ => case_c :: term_context_position ctx
    | tCtxCase_branch _ _ _ bctx => let res := branch_context_position bctx in case_brsbody res.1 :: res.2
    | tCtxProj _ ctx => proj_c :: term_context_position ctx
    | tCtxFix mctx _ => let res := mfixpoint_context_position mctx in (if res.1.1 then fix_mfix_ty else fix_mfix_bd) res.1.2 :: res.2
    | tCtxCoFix mctx _ => let res := mfixpoint_context_position mctx in (if res.1.1 then cofix_mfix_ty else cofix_mfix_bd) res.1.2 :: res.2
    end
  with list_context_position lctx : nat * position :=
    match lctx with
    | tCtxHead ctx _ => (0, term_context_position ctx)
    | tCtxTail _ lctx => let res := list_context_position lctx in (S res.1, res.2)
    end
  with branch_context_position lctx : nat * position :=
    match lctx with
    | tCtxHead_nat (_, ctx) _ => (0, term_context_position ctx)
    | tCtxTail_nat _ bctx => let res := branch_context_position bctx in (S res.1, res.2)
    end
  with mfixpoint_context_position mctx : bool * nat * position :=
    match mctx with
    | tCtxHead_mfix_Def _ _ ctx _ _ => (false, 0, term_context_position ctx)
    | tCtxHead_mfix_Type _ ctx _ _ _ => (true, 0, term_context_position ctx)
    | tCtxTail_mfix _ lctx => let res := mfixpoint_context_position lctx in (res.1.1, S res.1.2, res.2)
    end.

  Lemma atpos_fill_context st ctx :
    atpos (fill_context st ctx) (term_context_position ctx) = st.
  Proof.
    revert ctx.
    fix aux 1.
    assert (forall ctx : list_context,
    match nth_error (fill_list_context st ctx) (list_context_position ctx).1 with
    | Some arg => atpos arg (list_context_position ctx).2
    | None => tRel 0
    end = st).
    { intro ctx; induction ctx => //=. }
    assert (forall ctx : branch_context,
    match nth_error (fill_branch_context st ctx) (branch_context_position ctx).1 with
    | Some br => atpos br.(bbody) (branch_context_position ctx).2
    | None => tRel 0
    end = st).
    { intro ctx; induction ctx => //=. destruct p => //=. }
    assert (Hmfix : forall ctx : mfixpoint_context,
    let bnpos := mfixpoint_context_position ctx in
    match nth_error (fill_mfix_context st ctx) bnpos.1.2 with
    | Some d => atpos (if bnpos.1.1 then dtype d else dbody d) bnpos.2
    | None => tRel 0
    end = st).
    { intro ctx; induction ctx => //=. }
    intros [] => //=.
    all: specialize (Hmfix m); destruct mfixpoint_context_position as [[[] n'] pos]; cbn in *; assumption.
  Qed.

  Lemma validpos_fill_context st ctx :
    validpos (fill_context st ctx) (term_context_position ctx).
  Proof.
    revert ctx.
    fix aux 1.
    assert (forall ctx : list_context,
    match nth_error (fill_list_context st ctx) (list_context_position ctx).1 with
    | Some arg => validpos arg (list_context_position ctx).2
    | None => false
    end).
    { intro ctx; induction ctx => //=. }
    assert (forall ctx : branch_context,
    match nth_error (fill_branch_context st ctx) (branch_context_position ctx).1 with
    | Some br => validpos br.(bbody) (branch_context_position ctx).2
    | None => false
    end).
    { intro ctx; induction ctx => //=. destruct p => //=. }
    assert (Hmfix : forall ctx : mfixpoint_context,
    let bnpos := mfixpoint_context_position ctx in
    match nth_error (fill_mfix_context st ctx) bnpos.1.2 with
    | Some d => validpos (if bnpos.1.1 then dtype d else dbody d) bnpos.2
    | None => false
    end).
    { intro ctx; induction ctx => //=. }
    intros [] => //=.
    all: specialize (Hmfix m); destruct mfixpoint_context_position as [[[] n'] pos]; cbn in *; assumption.
  Qed.

  Lemma validpos_arg_pattern_matches pos p t s :
    validpos_arg_pattern p pos ->
    arg_pattern_matches p t s ->
    validpos t pos.
  Proof.
    intros H H0.
    induction H0 using arg_pattern_matches_ind in pos, H |- *.
    all: destruct pos as [|pos0 pos] => //.
    all: destruct pos0 => //=.
    all: eauto.
  Qed.

  Lemma validpos_rigid_pattern_matches pos p t s :
    validpos_rigid_pattern p pos ->
    rigid_arg_pattern_matches p t s ->
    validpos t pos.
  Proof.
    apply validpos_arg_pattern_matches with (p := pRigid p).
  Qed.

  Lemma validpos_pattern_matches pos p t s :
    validpos_pattern p pos ->
    pattern_matches p t s ->
    validpos t pos.
  Proof.
    intros H H0.
    induction H0 using pattern_matches_ind in pos, H |- *.
    all: destruct pos as [|pos0 pos] => //.
    all: destruct pos0 => //=.
    all: eauto.
    now eapply validpos_arg_pattern_matches.
  Qed.

  Lemma valid_atpos pos t :
    validpos t pos ->
    ∑ ctx, t = fill_context (atpos t pos) ctx × term_context_position ctx = pos.
  Proof.
    induction pos in t |- *; cbn.
    { exists tCtxHole. split; reflexivity. }
    destruct a => /=.
    all: destruct t => //=.
    all: intro H; try destruct nth_error eqn:enth => //; specialize (IHpos _ H) as (ctx & e & Hpos).
    - eexists (tCtxApp_l _ _); split; cbn; f_equal; eassumption.
    - eexists (tCtxApp_r _ _); split; cbn; f_equal; eassumption.
    - destruct p as [pars puinst pctx pret]; cbn in enth.
      assert (∑ ctx0, pars = fill_list_context (atpos t0 pos) ctx0 × let res := list_context_position ctx0 in res.1 = n × res.2 = pos) as (ctx' & e' & Hpos'1 & Hpos'2).
      2: { eexists (tCtxCase_pars _ _ _ _ _ _ _); split; cbn; repeat f_equal; eassumption. }
      induction pars in n, enth |- *; destruct n => //.
      + injection enth as [= ->].
        eexists (tCtxHead _ _); repeat split; cbn; f_equal; eassumption.
      + specialize (IHpars _ enth) as (ctx' & e' & Hpos'1 & Hpos'2).
        eexists (tCtxTail _ _); repeat split; cbn; f_equal; eassumption.
    - destruct p as [pars puinst pctx pret]; cbn in *.
      eexists (tCtxCase_pred _ _ _ _ _ _ _); split; cbn; repeat f_equal; eassumption.
    - eexists (tCtxCase_discr _ _ _ _); split; cbn; repeat f_equal; eassumption.
    - assert (∑ ctx0, brs = fill_branch_context (atpos (bbody b) pos) ctx0 × let res := branch_context_position ctx0 in res.1 = n × res.2 = pos) as (ctx' & e' & Hpos'1 & Hpos'2).
      2: { eexists (tCtxCase_branch _ _ _ _); split; cbn; repeat f_equal; eassumption. }
      destruct b as [bctx bbod]; cbn in *.
      induction brs in n, enth |- *; destruct n => //.
      + injection enth as [= ->].
        eexists (tCtxHead_nat (_, _) _); repeat split; cbn; repeat f_equal; eassumption.
      + specialize (IHbrs _ enth) as (ctx' & e' & Hpos'1 & Hpos'2).
        eexists (tCtxTail_nat _ _); repeat split; cbn; f_equal; eassumption.
    - eexists (tCtxProj _ _); split; cbn; f_equal; eassumption.
    - destruct d as [dname dtype dbody rarg]; cbn in *.
      assert (∑ ctx0, mfix = fill_mfix_context (atpos dtype pos) ctx0 × let res := mfixpoint_context_position ctx0 in res.1.1 = true × res.1.2 = n × res.2 = pos) as (ctx' & e' & Hpos'1 & Hpos'2 & Hpos'3).
      2: { eexists (tCtxFix _ _); split; cbn; repeat f_equal; tea. rewrite Hpos'1 //. apply f_equal. }
      induction mfix in n, enth |- *; destruct n => //.
      + injection enth as [= ->].
        eexists (tCtxHead_mfix_Type _ _ _ _ _); repeat split; cbn; repeat f_equal; eassumption.
      + specialize (IHmfix _ enth) as (ctx' & e' & Hpos'1 & Hpos'2 & Hpos'3).
        eexists (tCtxTail_mfix _ _); repeat split; cbn; f_equal; eassumption.
    - destruct d as [dname dtype dbody rarg]; cbn in *.
      assert (∑ ctx0, mfix = fill_mfix_context (atpos dbody pos) ctx0 × let res := mfixpoint_context_position ctx0 in res.1.1 = false × res.1.2 = n × res.2 = pos) as (ctx' & e' & Hpos'1 & Hpos'2 & Hpos'3).
      2: { eexists (tCtxFix _ _); split; cbn; repeat f_equal; tea. rewrite Hpos'1 //. apply f_equal. }
      induction mfix in n, enth |- *; destruct n => //.
      + injection enth as [= ->].
        eexists (tCtxHead_mfix_Def _ _ _ _ _); repeat split; cbn; repeat f_equal; eassumption.
      + specialize (IHmfix _ enth) as (ctx' & e' & Hpos'1 & Hpos'2 & Hpos'3).
        eexists (tCtxTail_mfix _ _); repeat split; cbn; f_equal; eassumption.
    - destruct d as [dname dtype dbody rarg]; cbn in *.
      assert (∑ ctx0, mfix = fill_mfix_context (atpos dtype pos) ctx0 × let res := mfixpoint_context_position ctx0 in res.1.1 = true × res.1.2 = n × res.2 = pos) as (ctx' & e' & Hpos'1 & Hpos'2 & Hpos'3).
      2: { eexists (tCtxCoFix _ _); split; cbn; repeat f_equal; tea. rewrite Hpos'1 //. apply f_equal. }
      induction mfix in n, enth |- *; destruct n => //.
      + injection enth as [= ->].
        eexists (tCtxHead_mfix_Type _ _ _ _ _); repeat split; cbn; repeat f_equal; eassumption.
      + specialize (IHmfix _ enth) as (ctx' & e' & Hpos'1 & Hpos'2 & Hpos'3).
        eexists (tCtxTail_mfix _ _); repeat split; cbn; f_equal; eassumption.
    - destruct d as [dname dtype dbody rarg]; cbn in *.
      assert (∑ ctx0, mfix = fill_mfix_context (atpos dbody pos) ctx0 × let res := mfixpoint_context_position ctx0 in res.1.1 = false × res.1.2 = n × res.2 = pos) as (ctx' & e' & Hpos'1 & Hpos'2 & Hpos'3).
      2: { eexists (tCtxCoFix _ _); split; cbn; repeat f_equal; tea. rewrite Hpos'1 //. apply f_equal. }
      induction mfix in n, enth |- *; destruct n => //.
      + injection enth as [= ->].
        eexists (tCtxHead_mfix_Def _ _ _ _ _); repeat split; cbn; repeat f_equal; eassumption.
      + specialize (IHmfix _ enth) as (ctx' & e' & Hpos'1 & Hpos'2 & Hpos'3).
        eexists (tCtxTail_mfix _ _); repeat split; cbn; f_equal; eassumption.
    - eexists (tCtxLambda_l _ _ _); split; cbn; f_equal; eassumption.
    - eexists (tCtxLambda_r _ _ _); split; cbn; f_equal; eassumption.
    - eexists (tCtxProd_l _ _ _); split; cbn; f_equal; eassumption.
    - eexists (tCtxProd_r _ _ _); split; cbn; f_equal; eassumption.
    - eexists (tCtxLetIn_l _ _ _ _); split; cbn; f_equal; eassumption.
    - eexists (tCtxLetIn_b _ _ _ _); split; cbn; f_equal; eassumption.
    - eexists (tCtxLetIn_r _ _ _ _); split; cbn; f_equal; eassumption.
    - assert (∑ ctx0, l = fill_list_context (atpos t pos) ctx0 × let res := list_context_position ctx0 in res.1 = n × res.2 = pos) as (ctx' & e' & Hpos'1 & Hpos'2).
      2: { eexists (tCtxEvar _ _); split; cbn; repeat f_equal; eassumption. }
      induction l in n, enth |- *; destruct n => //.
      + injection enth as [= ->].
        eexists (tCtxHead _ _); repeat split; cbn; f_equal; eassumption.
      + specialize (IHl _ enth) as (ctx' & e' & Hpos'1 & Hpos'2).
        eexists (tCtxTail _ _); repeat split; cbn; f_equal; eassumption.
  Qed.

End Position.

Section unifiable.
Context (mode : pattern_unif_mode).

Inductive unifiable_rigid_patterns_off (mode : pattern_unif_mode) | : rigid_arg_pattern -> position -> pattern -> Type :=
  | unifoff_argApp_L pf pos p parg :
    unifiable_rigid_patterns_off pf pos p ->
    unifiable_rigid_patterns_off (pargApp pf parg) (app_l :: pos) p
  | unifoff_argApp_R pf parg pos p :
    unifiable_arg_patterns_off parg pos p ->
    unifiable_rigid_patterns_off (pargApp pf parg) (app_r :: pos) p

with unifiable_arg_patterns_off (mode : pattern_unif_mode) | : arg_pattern -> position -> pattern -> Type :=
  | unifoff_Rigid p pos p' : unifiable_rigid_patterns_off p pos p' -> unifiable_arg_patterns_off (pRigid p) pos p'.

Inductive unifiable_patterns_off : pattern -> position -> pattern -> Type :=
  | unifoff_Here p p' : unifiable_patterns mode p p' -> unifiable_patterns_off p [] p'
  | unifoff_App_L pf pos p parg :
    unifiable_patterns_off pf pos p ->
    unifiable_patterns_off (pApp pf parg) (app_l :: pos) p
  | unifoff_App_R pf parg pos p :
    unifiable_arg_patterns_off mode parg pos p ->
    unifiable_patterns_off (pApp pf parg) (app_r :: pos) p
  | unifoff_Case_discr pc pos p' nbrs :
    unifiable_patterns_off pc pos p' -> unifiable_patterns_off (pCase pc nbrs) (case_c :: pos) p'
  | unifoff_Proj_discr pc pos p' :
    unifiable_patterns_off pc pos p' -> unifiable_patterns_off (pProj pc) (proj_c :: pos) p'.

Scheme unifiable_arg_patterns_off_mutual_ind := Elimination for unifiable_arg_patterns_off Sort Type
  with unifiable_rigid_patterns_off_mutual_ind := Elimination for unifiable_rigid_patterns_off Sort Type.

Derive Signature for unifiable_rigid_patterns_off unifiable_arg_patterns_off unifiable_patterns_off.

End unifiable.

Fixpoint rigidoff_super_compat p pos p' (H : unifiable_rigid_patterns_off Super p pos p') : unifiable_rigid_patterns_off Compat p pos p'
with argoff_super_compat p pos p' (H : unifiable_arg_patterns_off Super p pos p') : unifiable_arg_patterns_off Compat p pos p'.
Proof.
  - destruct H; constructor => //. 1: apply rigidoff_super_compat => //. apply argoff_super_compat => //.
  - destruct H; constructor => //. apply rigidoff_super_compat => //.
Qed.

Lemma patternoff_super_compat p pos p' (H : unifiable_patterns_off Super p pos p') : unifiable_patterns_off Compat p pos p'.
Proof. induction H => //; constructor => //. 1: apply pattern_super_compat => //. apply argoff_super_compat => //. Qed.

Fixpoint rigid_unifiable_off_trans p p' pos p'' {struct p'} : unifiable_rigid_patterns Super p p' -> unifiable_rigid_patterns_off Super p' pos p'' -> unifiable_rigid_patterns_off Super p pos p''
with arg_unifiable_off_trans p p' pos p'' {struct p'} : unifiable_arg_patterns Super p p' -> unifiable_arg_patterns_off Super p' pos p'' -> unifiable_arg_patterns_off Super p pos p''.
Proof.
  all: destruct p'; intros H1 H2; depelim H1 => //; depelim H2 => //.
  - constructor. eauto.
  - constructor. eauto.
  - constructor. eauto.
Qed.
Lemma pattern_unifiable_off_trans p p' pos p'' : unifiable_patterns Super p p' -> unifiable_patterns_off Super p' pos p'' -> unifiable_patterns_off Super p pos p''.
Proof.
  intros H1 H2.
  induction H2 in p, H1 |- *; depelim H1 => //.
  all: constructor; eauto.
  4: eapply arg_unifiable_off_trans; eassumption.
  all: etransitivity; eauto.
  all: constructor => //.
Qed.


Fixpoint unify_arg_patterns_off p pos p' (H : unifiable_arg_patterns_off Compat p pos p') : arg_pattern :=
  match H with
  | unifoff_Rigid p pos p' r => pRigid (unify_rigid_patterns_off p pos p' r)
  end
with unify_rigid_patterns_off p pos p' (H : unifiable_rigid_patterns_off Compat p pos p') : rigid_arg_pattern :=
  match H with
  | unifoff_argApp_L pf pos p parg r => pargApp (unify_rigid_patterns_off pf pos p r) parg
  | unifoff_argApp_R pf parg pos p r => pargApp pf (unify_arg_patterns_off parg pos p r)
  end.

Fixpoint unify_patterns_off p pos p' (H : unifiable_patterns_off Compat p pos p') : pattern :=
  match H with
  | unifoff_Here p p' H => unify_patterns_same_root p p' H
  | unifoff_App_L pf pos p parg r => pApp (unify_patterns_off pf pos p r) parg
  | unifoff_App_R pf parg pos p r => pApp pf (unify_arg_patterns_off parg pos p r)
  | unifoff_Case_discr pc pos p' nbrs r => pCase (unify_patterns_off pc pos p' r) nbrs
  | unifoff_Proj_discr pc pos p' r => pProj (unify_patterns_off pc pos p' r)
  end.

Lemma unifiable_arg_patterns_off_sound p pos p' :
  validpos_arg_pattern p pos ->
  (exists t s ss, arg_pattern_matches p t s × pattern_matches p' (atpos t pos) ss) -> unifiable_arg_patterns_off Compat p pos p'.
Proof.
  revert pos p'.
  induction p using arg_pattern_ind
    with (P0 := fun p => forall pos p', validpos_rigid_pattern p pos -> (exists t s ss, rigid_arg_pattern_matches p t s × pattern_matches p' (atpos t pos) ss) -> unifiable_rigid_patterns_off Compat p pos p'); intros.
  - exfalso.
    destruct pos => //.
  - constructor.
    apply IHp; tas.
  - destruct pos as [|[]] => //.
    + exfalso.
      destruct H0 as (t & s & ss & r & Hp).
      cbn in Hp.
      eapply symb_hd_rigid_shape.
      1: now apply pattern_to_symb_hd in Hp.
      now apply rigid_to_shape in r.
    + constructor.
      eapply IHp; tas.
      destruct H0 as (t & s & ss & r & Hp).
      cbn in Hp.
      apply rigid_pattern_matches_app_inv_l in r as (tf & targ & s1 & s2 & -> & -> & r1 & r2).
      repeat eexists; tea.
    + constructor.
      eapply IHp0; tas.
      destruct H0 as (t & s & ss & r & Hp).
      cbn in Hp.
      apply rigid_pattern_matches_app_inv_l in r as (tf & targ & s1 & s2 & -> & -> & r1 & r2).
      repeat eexists; tea.
  - destruct pos as [|[]] => //.
    + exfalso.
      destruct H0 as (t & s & ss & r & Hp).
      cbn in Hp.
      eapply symb_hd_rigid_shape.
      1: now apply pattern_to_symb_hd in Hp.
      now apply rigid_to_shape in r.
Qed.

Lemma unifiable_arg_patterns_off_valid_pos p pos p' :
  unifiable_arg_patterns_off Compat p pos p' -> validpos_subpattern_arg_pattern p pos.
Proof.
  induction 1 using unifiable_arg_patterns_off_mutual_ind with (P0 := fun p pos p' (H : unifiable_rigid_patterns_off Compat p pos p') => validpos_subpattern_rigid_pattern p pos) => //=.
Qed.


Lemma super_arg_patterns_off_sound p pos p' :
  unifiable_arg_patterns_off Super p pos p' ->
  forall t s, arg_pattern_matches p t s -> ∑ s, pattern_matches p' (atpos t pos) s.
Proof.
  intro H.
  induction H using unifiable_arg_patterns_off_mutual_ind with
    (P0 := fun p pos p' _ => forall t s, rigid_arg_pattern_matches p t s -> ∑ s, pattern_matches p' (atpos t pos) s); intros.
  - apply IHunifiable_arg_patterns_off in H as (s' & X').
    eexists; eauto.
  - apply rigid_pattern_matches_app_inv_l in H as (f & arg & s1 & s2 & -> & -> & X1 & X2).
    apply IHunifiable_arg_patterns_off in X1 as (s' & X').
    eexists; eauto.
  - apply rigid_pattern_matches_app_inv_l in H0 as (f & arg & s1 & s2 & -> & -> & X1 & X2).
    apply IHunifiable_arg_patterns_off in X2 as (s' & X').
    eexists; eauto.
Qed.


Lemma unify_arg_patterns_off_super p pos p' H :
  let pp := unify_arg_patterns_off p pos p' H in
  unifiable_arg_patterns Super pp p × unifiable_arg_patterns_off Super pp pos p'.
Proof.
  induction H using unifiable_arg_patterns_off_mutual_ind
    with (P0 := fun p pos p' H => let pp := unify_rigid_patterns_off p pos p' H in
    unifiable_rigid_patterns Super pp p × unifiable_rigid_patterns_off Super pp pos p') => //=.
  - destruct IHunifiable_arg_patterns_off.
    split; constructor => //.
  - destruct IHunifiable_arg_patterns_off.
    split; constructor => //.
    apply arg_unifiable_refl.
  - destruct IHunifiable_arg_patterns_off.
    split; constructor => //.
    apply rigid_unifiable_refl.
Qed.

Lemma super_unify_arg_patterns_off p pos p' H :
  unifiable_arg_patterns_off Super p pos p' ->
  unify_arg_patterns_off p pos p' H = p.
Proof.
  induction H using unifiable_arg_patterns_off_mutual_ind
    with (P0 := fun p pos p' H => unifiable_rigid_patterns_off Super p pos p' -> unify_rigid_patterns_off p pos p' H = p) => //=.
  all: intro H'; depelim H' => //.
  all: f_equal; auto.
Qed.

Lemma unify_arg_patterns_off_sound1 p pos p' H t s :
  arg_pattern_matches (unify_arg_patterns_off p pos p' H) t s ->
  (∑ s ss, arg_pattern_matches p t s × pattern_matches p' (atpos t pos) ss).
Proof.
  pose proof (unify_arg_patterns_off_super _ _ _ H) as (X1 & X2).
  intro Hp.
  eapply super_arg_patterns_sound in X1 as []; tea.
  eapply super_arg_patterns_off_sound in X2 as []; tea.
  now do 2 eexists.
Qed.

Lemma unify_arg_patterns_off_sound2 p pos p' H t s ss :
  arg_pattern_matches p t s -> pattern_matches p' (atpos t pos) ss ->
  ∑ s, arg_pattern_matches (unify_arg_patterns_off p pos p' H) t s.
Proof.
  revert t s ss.
  induction H using unifiable_arg_patterns_off_mutual_ind with
    (P0 := fun p pos p' H => forall t s ss, rigid_arg_pattern_matches p t s -> pattern_matches p' (atpos t pos) ss ->
    ∑ s, rigid_arg_pattern_matches (unify_rigid_patterns_off p pos p' H) t s); intros.
  - cbn. eauto.
  - apply rigid_pattern_matches_app_inv_l in H as (f & arg & s1' & s2' & -> & -> & X1' & X2).
    cbn in H0.
    eapply IHunifiable_arg_patterns_off in X1' as (s1 & X1); tea.
    unfold rigid_arg_pattern_matches. cbn.
    rewrite X1 X2. now eexists.
  - apply rigid_pattern_matches_app_inv_l in H0 as (f & arg & s1' & s2' & -> & -> & X1 & X2').
    cbn in H1.
    eapply IHunifiable_arg_patterns_off in X2' as (s2 & X2); tea.
    unfold rigid_arg_pattern_matches. cbn.
    rewrite X1 X2. now eexists.
Qed.

Lemma unifiable_patterns_off_sound p pos p' :
  validpos_pattern p pos ->
  (exists t s ss, pattern_matches p t s × pattern_matches p' (atpos t pos) ss) -> unifiable_patterns_off Compat p pos p'.
Proof.
  induction p in pos, p' |- *; intros H X.
  - destruct pos as [|[]] => //.
    constructor.
    now apply unifiable_patterns_sound.
  - destruct pos as [|[]] => //.
    + constructor. now apply unifiable_patterns_sound.
    + constructor.
      eapply IHp; tas.
      destruct X as (t & s & ss & r & Hp).
      cbn in Hp.
      apply pattern_matches_app_inv_l in r as (tf & targ & s1 & s2 & -> & -> & r1 & r2).
      now repeat eexists.
    + constructor.
      eapply unifiable_arg_patterns_off_sound; tas.
      destruct X as (t & s & ss & r & Hp).
      cbn in Hp.
      apply pattern_matches_app_inv_l in r as (tf & targ & s1 & s2 & -> & -> & r1 & r2).
      now repeat eexists.
  - destruct pos as [|[]] => //.
    + constructor. now apply unifiable_patterns_sound.
    + constructor.
      eapply IHp; tas.
      destruct X as (t & s & ss & r & Hp).
      cbn in Hp.
      apply pattern_matches_case_inv_l in r as (? & ? & ? & ? & ? & -> & -> & ? & ? & ?).
      now repeat eexists.
  - destruct pos as [|[]] => //.
    + constructor. now apply unifiable_patterns_sound.
    + constructor.
      eapply IHp; tas.
      destruct X as (t & s & ss & r & Hp).
      cbn in Hp.
      destruct t => //.
      now repeat eexists.
Qed.

Lemma unifiable_patterns_off_valid_pos p pos p' :
  unifiable_patterns_off Compat p pos p' -> validpos_subpattern_pattern p pos.
Proof.
  induction 1 => //=.
  now eapply unifiable_arg_patterns_off_valid_pos.
Qed.


Lemma super_patterns_off_sound p pos p' :
  unifiable_patterns_off Super p pos p' ->
  forall t s, pattern_matches p t s -> ∑ s, pattern_matches p' (atpos t pos) s.
Proof.
  intro H.
  induction H; intros.
  - eapply super_patterns_sound; eassumption.
  - apply pattern_matches_app_inv_l in H0 as (f & arg & s1 & s2 & -> & -> & X1 & X2).
    apply IHunifiable_patterns_off in X1 as (s' & X').
    eexists; eauto.
  - apply pattern_matches_app_inv_l in H as (f & arg & s1 & s2 & -> & -> & X1 & X2).
    eapply super_arg_patterns_off_sound in X2 as (s' & X'); tea.
    eexists; eauto.
  - apply pattern_matches_case_inv_l in H0 as (? & ? & ? & ? & ? & -> & -> & enbrs & flagCase & X).
    apply IHunifiable_patterns_off in X as (sc' & X).
    unfold pattern_matches. cbn.
    now eexists.
  - destruct t => //.
    now eapply IHunifiable_patterns_off.
Qed.


Lemma unify_patterns_off_super p pos p' H :
  let pp := unify_patterns_off p pos p' H in
  unifiable_patterns Super pp p × unifiable_patterns_off Super pp pos p'.
Proof.
  induction H => //=.
  - destruct (unify_patterns_same_root_super _ _ u).
    split => //. constructor => //.
  - destruct IHunifiable_patterns_off.
    split; constructor => //.
    apply arg_unifiable_refl.
  - destruct (unify_arg_patterns_off_super _ _ _ u).
    split; constructor => //.
    apply pattern_unifiable_refl.
  - destruct IHunifiable_patterns_off.
    split; constructor => //.
  - destruct IHunifiable_patterns_off.
    split; constructor => //.
Qed.

Lemma super_unify_patterns_off p pos p' H :
  unifiable_patterns_off Super p pos p' ->
  unify_patterns_off p pos p' H = p.
Proof.
  induction H => //=.
  all: intro H'; depelim H' => //.
  1: now apply super_unify_patterns_same_root.
  all: f_equal; auto.
  now apply super_unify_arg_patterns_off.
Qed.


Lemma unify_patterns_off_sound1 p pos p' H t s :
  pattern_matches (unify_patterns_off p pos p' H) t s ->
  (∑ s ss, pattern_matches p t s × pattern_matches p' (atpos t pos) ss).
Proof.
  pose proof (unify_patterns_off_super _ _ _ H) as (X1 & X2).
  intro Hp.
  eapply super_patterns_sound in X1 as []; tea.
  eapply super_patterns_off_sound in X2 as []; tea.
  now do 2 eexists.
Qed.

Lemma unify_patterns_off_sound2 p pos p' H t s ss :
  pattern_matches p t s -> pattern_matches p' (atpos t pos) ss ->
  ∑ s, pattern_matches (unify_patterns_off p pos p' H) t s.
Proof.
  induction H in t, s, ss |- *; cbn; intros.
  - now eapply unify_patterns_same_root_sound2.
  - apply pattern_matches_app_inv_l in H0 as (f & arg & s1' & s2' & -> & -> & X1' & X2).
    eapply IHunifiable_patterns_off in X1' as (s1 & X1); tea.
    unfold pattern_matches. cbn.
    rewrite X1 X2. now eexists.
  - apply pattern_matches_app_inv_l in H as (f & arg & s1' & s2' & -> & -> & X1 & X2').
    unshelve eapply unify_arg_patterns_off_sound2 in X2' as (s2 & X2); revgoals; tea.
    unfold pattern_matches. cbn.
    rewrite X1 X2. now eexists.
  - apply pattern_matches_case_inv_l in H0 as (? & ? & ? & ? & ? & -> & -> & enbrs & flagCase & X).
    eapply IHunifiable_patterns_off in X as (sc' & Xc); tea.
    unfold pattern_matches. cbn.
    rewrite Xc enbrs eqb_refl flagCase. now eexists.
  - destruct t => //.
    eapply IHunifiable_patterns_off in H0 as (sc' & X); tea.
    unfold pattern_matches. cbn.
    now eexists.
Qed.


Inductive unify_patterns_n pp p0 : list (position * pattern) -> Type :=
  | unify_1 : pp = p0 -> unify_patterns_n pp p0 []
  | unify_S pos p1 H ps : let p01 := unify_patterns_off p0 pos p1 H in unify_patterns_n pp p01 ps -> unify_patterns_n pp p0 ((pos, p1) :: ps).

Lemma unify_pattern_n_unifiable_super pp p0 ps :
  unify_patterns_n pp p0 ps -> unifiable_patterns Super pp p0 × All (fun '(pos, p') => unifiable_patterns_off Super pp pos p') ps.
Proof.
  induction 1.
  - split => //.
    rewrite e. apply pattern_unifiable_refl.
  - destruct IHunify_patterns_n as (H1 & H2).
    pose proof (unify_patterns_off_super p0 pos p1 H) as (? & ?).
    split => //.
    1: etransitivity; eassumption.
    constructor => //.
    eapply pattern_unifiable_off_trans; eassumption.
Qed.

Definition pattern_unification_closed Σ :=
  forall k rd r r' pos t s,
  lookup_rules Σ k = Some rd ->
  first_match (rd.(prules) ++ rd.(rules)) t = Some (r, s) ->
  In r' (rd.(prules) ++ rd.(rules)) ->
  unifiable_patterns_off Compat r.(pat_lhs) pos r'.(pat_lhs) ->
  unifiable_patterns_off Super r.(pat_lhs) pos r'.(pat_lhs).

Lemma unify_pattern_n_unification_closed Σ k rd p0 ps pp :
  pattern_unification_closed Σ ->
  lookup_rules Σ k = Some rd ->
  (exists r t s,
    first_match (rd.(prules) ++ rd.(rules)) t = Some (r, s) ×
    r.(pat_lhs) = p0) ->
  All (fun posp => ∑ r', In r' (rd.(prules) ++ rd.(rules)) × r'.(pat_lhs) = posp.2) ps ->
  unify_patterns_n pp p0 ps -> pp = p0.
Proof.
  intros X H H0 H1.
  destruct H0 as (r & t & s & e & e').
  pose proof (fun r' pos Hr' => X _ _ _ r' pos _ _ H e Hr').
  induction 1 in H1, e' |- * => //.
  depelim H1. cbn in s0. destruct s0 as (r' & Hin & <-).
  specialize (X0 r' pos Hin).
  rewrite e' in X0. specialize (X0 H0).
  apply super_unify_patterns_off with (H := H0) in X0.
  subst p01; rewrite X0 in IHunify_patterns_n.
  eapply IHunify_patterns_n => //.
Qed.
