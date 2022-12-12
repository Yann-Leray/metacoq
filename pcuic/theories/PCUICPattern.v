(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Lia ssreflect.
From MetaCoq.Utils Require Import utils monad_utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases
  PCUICUnivSubst.

Import MCMonadNotation.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Lemma symbols_subst_length kn i u n : #|symbols_subst kn i u n| = n - i.
Proof.
  rewrite /symbols_subst list_make_length //.
Qed.
#[global]
Hint Rewrite symbols_subst_length : len.

Global Instance subst_instance_found_substitution : UnivSubst found_substitution :=
  fun u => found_substitution_map (subst_instance u) (subst_instance u).

Fixpoint pattern_head (p: pattern) : kername × nat :=
  match p with
  | pSymb k n => (k, n)
  | pApp f arg => pattern_head f
  | pCase c nbrs => pattern_head c
  | pProj c => pattern_head c
  end.

Fixpoint arg_pattern_holes (p: arg_pattern) : nat :=
  match p with
  | pHole => 1
  | pRigid p => rigid_arg_pattern_holes p
  end
with rigid_arg_pattern_holes p :=
  match p with
  | pargApp f arg => rigid_arg_pattern_holes f + arg_pattern_holes arg
  | pConstr ind n => 0
  (* | pSymb k n => 0 *)
  end.

Fixpoint pattern_holes (p: pattern) : nat :=
  match p with
  | pSymb k n => 0
  | pApp f arg => pattern_holes f + arg_pattern_holes arg
  | pCase c nbrs => pattern_holes c + (1 + nbrs)
  | pProj c => pattern_holes c
  end.

Fixpoint arg_pattern_match (p: arg_pattern) (t: term) : option (list term) :=
  match p, t with
  | pHole, t => Some [t]
  | pRigid p, t => rigid_arg_pattern_match p t
  end
with rigid_arg_pattern_match p t :=
  match p, t with
  | pargApp pf parg, tApp f arg =>
      s <- rigid_arg_pattern_match pf f;;
      s' <- arg_pattern_match parg arg;;
      ret (s ++ s')
  | pConstr ind n, tConstruct ind' n' ui' =>
      if eqb ind ind' && eqb n n' then ret [] else None
  | _, _ => None
  end.

Module Type CaseInPatternSIG.
  Parameter Inline case_in_pattern : bool.
  Parameter Inline no_case_in_pattern : case_in_pattern = false.
End CaseInPatternSIG.

Module CaseInPattern : CaseInPatternSIG.
  Definition case_in_pattern : bool := false.
  Definition no_case_in_pattern : case_in_pattern = false := eq_refl.
End CaseInPattern.
Include CaseInPattern.

Fixpoint pattern_match (p: pattern) (t: term) : option (found_substitution) :=
  match p, t with
  | pSymb k n, tSymb k' n' ui' =>
      if eqb k k' && (n == n') then
        ret {| found_usubst := ui'; found_subst := [] |}
      else None
  | pApp pf parg, tApp f arg =>
      s <- pattern_match pf f;;
      s' <- arg_pattern_match parg arg;;
      ret (s ++f s')
  | pCase pc nbrs, tCase ci p c brs =>
      s <- pattern_match pc c;;
      s' <- (
        if eqb nbrs #|brs| then
          ret (List.map (fun br => it_mkLambda_or_LetIn (inst_case_branch_context p br) br.(bbody)) brs)
        else None
      );;
      sc <- (
        ret [it_mkProd_or_LetIn (inst_case_predicate_context p) p.(preturn)]
      );;
      (if case_in_pattern then ret tt else None);;
      ret (s ++f sc ++f s')
  | pProj pc, tProj p c => pattern_match pc c
  | _, _ => None
  end.

Definition rigid_arg_pattern_matches p t s := rigid_arg_pattern_match p t = Some s.
Definition arg_pattern_matches p t s := arg_pattern_match p t = Some s.
Definition pattern_matches p t s := pattern_match p t = Some s.

Lemma rigid_pattern_matches_app_inv_l pf parg t s :
  rigid_arg_pattern_matches (pargApp pf parg) t s ->
  ∑ f arg s1 s2, t = tApp f arg × s = s1 ++ s2 × rigid_arg_pattern_matches pf f s1 × arg_pattern_matches parg arg s2.
Proof.
  destruct t => //.
  unfold rigid_arg_pattern_matches, arg_pattern_matches.
  cbn.
  destruct rigid_arg_pattern_match as [s1|] eqn:e1 => //.
  destruct arg_pattern_match as [s2|] eqn:e2 => //.
  intros [= <-].
  repeat eexists.
  all: assumption.
Qed.

Lemma rigid_pattern_matches_app_inv p f arg s :
  rigid_arg_pattern_matches p (tApp f arg) s ->
  ∑ pf parg s1 s2, p = pargApp pf parg × s = s1 ++ s2 × rigid_arg_pattern_matches pf f s1 × arg_pattern_matches parg arg s2.
Proof.
  destruct p => //.
  unfold rigid_arg_pattern_matches, arg_pattern_matches.
  cbn.
  destruct rigid_arg_pattern_match as [s1|] eqn:e1 => //.
  destruct arg_pattern_match as [s2|] eqn:e2 => //.
  intros [= <-].
  repeat eexists.
  all: assumption.
Qed.

Lemma pattern_matches_symb_inv_l k n t s :
  pattern_matches (pSymb k n) t s ->
  ∑ u, t = tSymb k n u × s = {| found_subst := []; found_usubst := u |}.
Proof.
  unfold pattern_matches.
  destruct t => //=.
  destruct (eqb_specT k k0), (eqb_specT n n0) => //=.
  intros [= <-].
  subst; eexists; now split.
Qed.

Lemma pattern_matches_symb_inv p s k n u :
  pattern_matches p (tSymb k n u) s ->
  p = pSymb k n × s = {| found_subst := []; found_usubst := u |}.
Proof.
  unfold pattern_matches.
  destruct p => //=.
  destruct (eqb_specT k0 k), (eqb_specT n0 n) => //=.
  intros [= <-].
  subst; now split.
Qed.

Lemma pattern_matches_app_inv_l pf parg t s :
  pattern_matches (pApp pf parg) t s ->
  ∑ f arg s1 s2, t = tApp f arg × s = s1 ++f s2 × pattern_matches pf f s1 × arg_pattern_matches parg arg s2.
Proof.
  destruct t => //.
  unfold pattern_matches, arg_pattern_matches.
  cbn.
  destruct pattern_match as [s1|] eqn:e1 => //.
  destruct arg_pattern_match as [s2|] eqn:e2 => //.
  intros [= <-].
  repeat eexists.
  all: assumption.
Qed.

Lemma pattern_matches_app_inv p f arg s :
  pattern_matches p (tApp f arg) s ->
  ∑ pf parg s1 s2, p = pApp pf parg × s = s1 ++f s2 × pattern_matches pf f s1 × arg_pattern_matches parg arg s2.
Proof.
  destruct p => //.
  unfold pattern_matches, arg_pattern_matches.
  cbn.
  destruct pattern_match as [s1|] eqn:e1 => //.
  destruct arg_pattern_match as [s2|] eqn:e2 => //.
  intros [= <-].
  repeat eexists.
  all: assumption.
Qed.

Lemma pattern_matches_case_inv_l pc nbrs t s :
  pattern_matches (pCase pc nbrs) t s ->
  ∑ ci p c sc brs, t = tCase ci p c brs ×
  (let sret := [it_mkProd_or_LetIn (inst_case_predicate_context p) p.(preturn)] in
  let sbrs := List.map (fun br => it_mkLambda_or_LetIn (inst_case_branch_context p br) br.(bbody)) brs in
  s = sc ++f sret ++f sbrs) × nbrs = #|brs| ×
  case_in_pattern × pattern_matches pc c sc.
Proof.
  destruct t => //.
  unfold pattern_matches, arg_pattern_matches.
  cbn.
  destruct pattern_match as [sc|] eqn:e1 => //.
  destruct eqb eqn:eb => //.
  destruct case_in_pattern eqn:flagCase => //.
  intros [= <-].
  repeat eexists.
  2: eassumption.
  destruct (eqb_spec nbrs #|brs|) => //.
Qed.

Lemma pattern_matches_case_inv p ci pr c brs s :
  pattern_matches p (tCase ci pr c brs) s ->
  ∑ pc sc, p = pCase pc #|brs| ×
  (let sret := [it_mkProd_or_LetIn (inst_case_predicate_context pr) pr.(preturn)] in
  let sbrs := List.map (fun br => it_mkLambda_or_LetIn (inst_case_branch_context pr br) br.(bbody)) brs in
  s = sc ++f sret ++f sbrs) ×
  case_in_pattern × pattern_matches pc c sc.
Proof.
  destruct p => //.
  unfold pattern_matches, arg_pattern_matches.
  cbn.
  destruct pattern_match as [sc|] eqn:e1 => //.
  destruct eqb eqn:eb => //.
  destruct case_in_pattern eqn:flagCase => //.
  intros [= <-].
  repeat eexists.
  2: eassumption.
  destruct (eqb_spec nbrs #|brs|) => //. auto.
Qed.

Lemma arg_pattern_matches_mutual_ind (P : _ -> _ -> _ -> Type) (P' : _ -> _ -> _ -> Type) :
  (forall t, P pHole t [t]) ->
  (forall p t s, rigid_arg_pattern_matches p t s -> P' p t s -> P (pRigid p) t s) ->
  (forall pf parg f arg s1 s2,
    rigid_arg_pattern_matches pf f s1 -> arg_pattern_matches parg arg s2 ->
    P' pf f s1 -> P parg arg s2 ->
    P' (pargApp pf parg) (tApp f arg) (s1 ++ s2)) ->
  (forall ind n ui, P' (pConstr ind n) (tConstruct ind n ui) []) ->
  (forall p t s, arg_pattern_matches p t s -> P p t s) × (forall p t s, rigid_arg_pattern_matches p t s -> P' p t s).
Proof.
  intros fHole fRigid fApp fConstr.
  assert (forall p t s, rigid_arg_pattern_matches p t s -> P' p t s). {
  intros p t s.
  unfold rigid_arg_pattern_matches.
  induction p using rigid_arg_pattern_ind
    with (P := fun p => forall t s, arg_pattern_match p t = Some s -> P p t s) in t, s |- * => /=.
  { intros [= <-] => //. }
  { easy. }
  all: destruct t => //=.
  - destruct (rigid_arg_pattern_match p t1) as [s1|] eqn:e1 => //.
    destruct (arg_pattern_match arg t2) as [s2|] eqn:e2 => //.
    intros [= <-].
    eauto.
  - intro H.
    destruct (eqb_specT ind ind0), (eqb_specT n n0) => //.
    injection H as [= <-]. subst ind0 n0. easy.
  }
  split => //.
  intros p t s.
  destruct p.
  { intros [= <-] => //. }
  { easy. }
Qed.

Lemma arg_pattern_matches_ind (P : _ -> _ -> _ -> Type) :
  (forall t, P pHole t [t]) ->
  (forall pf parg f arg s1 s2,
    arg_pattern_matches (pRigid pf) f s1 -> arg_pattern_matches parg arg s2 ->
    P (pRigid pf) f s1 -> P parg arg s2 ->
    P (pRigid (pargApp pf parg)) (tApp f arg) (s1 ++ s2)) ->
  (forall ind n ui, P (pRigid (pConstr ind n)) (tConstruct ind n ui) []) ->
  forall p t s, arg_pattern_matches p t s -> P p t s.
Proof.
  intros fHole fApp fConstr.
  eapply arg_pattern_matches_mutual_ind with (P' := fun p => P (pRigid p)).
  all: auto.
Qed.

Lemma pattern_matches_ind (P : _ -> _ -> _ -> Type) :
  (forall k n ui, P (pSymb k n) (tSymb k n ui) {|found_usubst := ui; found_subst := []|}) ->
  (forall pf parg f arg s1 s2,
    pattern_matches pf f s1 ->
    P pf f s1 -> arg_pattern_matches parg arg s2 ->
    P (pApp pf parg) (tApp f arg) (s1 ++f s2)) ->
  (forall pc indn p c brs s,
    pattern_matches pc c s ->
    P pc c s ->
    forall (flagCase : case_in_pattern = true),
    let sc := [it_mkProd_or_LetIn (inst_case_predicate_context p) p.(preturn)] in
    let s' := List.map (fun br => it_mkLambda_or_LetIn (inst_case_branch_context p br) br.(bbody)) brs in
    P (pCase pc #|brs|) (tCase indn p c brs) (s ++f sc ++f s')) ->
  (forall pc p c s,
    pattern_matches pc c s -> P pc c s -> P (pProj pc) (tProj p c) s) ->
  forall p t s, pattern_matches p t s -> P p t s.
Proof.
  intros fSymb fApp fCase fProj.
  intros p t s.
  unfold pattern_matches.
  assert (Hf: forall p t s, None = Some s -> P p t s) by easy.
  induction p in t, s |- *; destruct t; try apply Hf; cbn.
  - destruct (eqb_specT k k0) as [<-|] => //; destruct (eqb_specT n n0) as [<-|] => //=.
    intros [= <-] => //.
  - destruct (pattern_match p t1) as [s1|] eqn:e1 => //.
    destruct (arg_pattern_match arg t2) as [s2|] eqn:e2 => //.
    intros [= <-]. destruct s1 as [s1 ui1].
    eapply fApp; eauto.
  - destruct (pattern_match p t) as [s1|] eqn:e => //.
    intro H; assert (nbrs = #|brs|) as -> by destruct (eqb_spec nbrs #|brs|) as [->|] => //; revert H.
    rewrite eqb_refl /=.
    destruct case_in_pattern eqn:e' => //=.
    intros [= <-]. destruct s1 as [s1 ui1] => /=.
    eapply fCase; eauto.
  - intro.
    eapply fProj; eauto.
Qed.


Lemma rigid_pattern_matches_length p t s :
  rigid_arg_pattern_matches p t s ->
  #|s| = rigid_arg_pattern_holes p.
Proof.
  intro H.
  eapply arg_pattern_matches_mutual_ind with (P := fun p t s => #|s| = arg_pattern_holes p) (P' := fun p t s => #|s| = rigid_arg_pattern_holes p) => //=; tea.
  intros. len. lia.
Qed.

Lemma arg_pattern_matches_length p t s :
  arg_pattern_matches p t s ->
  #|s| = arg_pattern_holes p.
Proof.
  unfold arg_pattern_matches.
  destruct p => //=.
  1: now intros [= <-].
  apply rigid_pattern_matches_length.
Qed.

Lemma pattern_matches_length p t s :
  pattern_matches p t s ->
  #|found_subst s| = pattern_holes p.
Proof.
  induction 1 using pattern_matches_ind => //=.
  2: { rewrite !app_length map_length /=. lia. }
  len; f_equal; tas.
  induction H0 using arg_pattern_matches_ind => //=.
  cbn in IHarg_pattern_matches1.
  len. lia.
Qed.

Lemma patterns_match_head p p' t s s' :
  pattern_matches p t s ->
  pattern_matches p' t s' ->
  pattern_head p = pattern_head p'.
Proof.
  induction 1 using pattern_matches_ind in p', s' |- *; destruct p' => //=; intro H'.
  all: unfold pattern_matches in H'; cbn in H'.
  1: destruct (eqb_specT n0 n) => //; destruct (eqb_specT k0 k) => //; congruence.
  all: destruct pattern_match eqn:? => //.
  all: now eapply IHpattern_matches.
Qed.

Lemma patterns_match_usubst p p' t s s' :
  pattern_matches p t s ->
  pattern_matches p' t s' ->
  found_usubst s = found_usubst s'.
Proof.
  induction 1 using pattern_matches_ind in p', s' |- *; destruct p' => //=; intro H'.
  all: unfold pattern_matches in H'; cbn in H'.
  1: destruct (eqb_specT n0 n) => //; destruct (eqb_specT k0 k) => //; injection H' as [= <-] => //.
  all: destruct pattern_match eqn:? => //.
  - destruct arg_pattern_match => //. injection H' as [= <-]. unfold found_substitution_app, found_substitution_map; cbn. eauto.
  - destruct eqb, case_in_pattern => //. injection H' as [= <-]. unfold found_substitution_app, found_substitution_map; cbn. eauto.
  - injection H' as [= <-]. eauto.
Qed.

Fixpoint symb_hd (t: term) : option (kername × nat) :=
  match t with
  | tSymb k n u => Some (k, n)
  | tApp f arg => symb_hd f
  | tCase ci p c brs => symb_hd c
  | tProj p c => symb_hd c
  | _ => None
  end.

Lemma symb_hd_mkApps_inv t args :
  symb_hd (mkApps t args) = symb_hd t.
Proof.
  induction args using rev_ind; cbn; auto.
  rewrite mkApps_app //.
Qed.

Lemma pattern_to_symb_hd p t s :
  pattern_matches p t s -> symb_hd t = Some (pattern_head p).
Proof.
  induction 1 using pattern_matches_ind => //.
Qed.

Fixpoint rigid_shape (t: term) :=
  match t with
  | tConstruct ind n ui => true
  | tSymb k n u => false
  | tApp t u => rigid_shape t
  | _ => false
  end.

Lemma rigid_shape_subst s n t :
  rigid_shape t ->
  rigid_shape (subst s n t).
Proof.
  induction t => //=.
Qed.

Lemma rigid_shape_mkApps_inv t args :
  rigid_shape (mkApps t args) = rigid_shape t.
Proof.
  induction args using rev_ind; cbn; auto.
  rewrite mkApps_app //.
Qed.

Lemma rigid_to_shape p t s :
  rigid_arg_pattern_matches p t s ->
  rigid_shape t.
Proof.
  change (rigid_arg_pattern_matches _ _ _) with (arg_pattern_matches (pRigid p) t s).
  remember (pRigid p) as p'.
  induction 1 using arg_pattern_matches_ind in p, Heqp' |- *=> //.
  injection Heqp' as <-.
  eapply IHarg_pattern_matches1 => //.
Qed.

Lemma symb_hd_rigid_shape t k : symb_hd t = Some k -> rigid_shape t -> False.
Proof.
  induction t => //.
Qed.


(* First lhs matching in a list of rules *)
Fixpoint first_match (l : list rewrite_rule) (t : term) :=
  match l with
  | [] => None
  | r :: l =>
    match pattern_match r.(pat_lhs) t with
    | Some s => Some (r, s)
    | None => first_match l t
    end
  end.

Lemma first_match_rule_list :
  forall l t r s,
    first_match l t = Some (r, s) ->
    ∑ n, nth_error l n = Some r × pattern_matches r.(pat_lhs) t s.
Proof.
  intros l t r s h.
  induction l in r, s, h |- *; cbn in h => //.
  destruct pattern_match eqn:e.
  - noconf h. exists 0. now split.
  - apply IHl in h as [n h]. exists (S n). auto.
Qed.

Lemma first_match_to_symb_hd l t r s :
  first_match l t = Some (r, s) ->
  symb_hd t = Some (pattern_head (pat_lhs r)).
Proof.
  induction l => //.
  unfold first_match.
  destruct pattern_match eqn:e => //.
  intros [= -> ->].
  eapply pattern_to_symb_hd, e.
Qed.

Lemma first_match_subst_length :
  forall l t r s,
  first_match l t = Some (r, s) ->
  #|s.(found_subst)| = pattern_holes r.(pat_lhs).
Proof.
  intros l t r s h.
  induction l in r, s, h |- *; cbn in h => //.
  destruct pattern_match eqn:e.
  - noconf h. eapply pattern_matches_length; eassumption.
  - now apply IHl in h.
Qed.

Lemma first_match_impl l t t' r s s' f :
  first_match l t = Some (r, s) ->
  pattern_matches (pat_lhs r) t' s' ->
  (forall p s, pattern_matches p t' s -> pattern_matches p t (f s)) ->
  first_match l t' = Some (r, s').
Proof.
  intros H H0 IH.
  induction l as [|r' l] in H, H0 |- * => //=.
  cbn in H.
  destruct pattern_match eqn:e => //=.
  + injection H as [= -> ->].
    rewrite H0 //.
  + apply IHl in H; tas.
    destruct (pattern_match _ t') eqn:e' => //.
    apply IH in e'.
    rewrite e' // in e.
Qed.


From MetaCoq.PCUIC Require Import PCUICDepth.

Lemma arg_pattern_matches_depth p t s :
  arg_pattern_matches p t s ->
  list_depth s <= depth t.
Proof.
  induction 1 using arg_pattern_matches_ind => //=.
  2: rewrite list_depth_app.
  all: lia.
Qed.

Lemma pattern_matches_depth p t s :
  pattern_matches p t s ->
  list_depth (found_subst s) < depth t.
Proof.
  induction 1 using pattern_matches_ind => //=.
  - rewrite list_depth_app.
    apply arg_pattern_matches_depth in H0.
    lia.
  - rewrite !list_depth_app /=.
    rewrite no_case_in_pattern // in flagCase.
  - lia.
Qed.

Lemma first_match_subst_depth l t r s :
  first_match l t = Some (r, s) ->
  list_depth s.(found_subst) < depth t.
Proof.
  intro h.
  apply first_match_rule_list in h as (n & e & h).
  eapply pattern_matches_depth; eassumption.
Qed.

Inductive pattern_stack_entry :=
  | psApp (arg : arg_pattern)
  | psCase (* Hole for return predicate *) (nbrs : nat) (* Number of branches *)
  | psProj.

Fixpoint pattern_of_stack k n s :=
  match s with
  | [] => pSymb k n
  | psApp arg :: s => pApp (pattern_of_stack k n s) arg
  | psCase nbrs :: s => pCase (pattern_of_stack k n s) nbrs
  | psProj :: s => pProj (pattern_of_stack k n s)
  end.

Fixpoint stack_of_pattern p :=
  match p with
  | pSymb _ _ => []
  | pApp f arg => psApp arg :: stack_of_pattern f
  | pCase c nbrs => psCase nbrs :: stack_of_pattern c
  | pProj c => psProj :: stack_of_pattern c
  end.
