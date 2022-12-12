(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Lia ssreflect ssrbool.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICCases
  PCUICPattern PCUICPosition PCUICReduction PCUICGlobalMaps PCUICPatternUnification.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.


Inductive minimal_arg_pattern_term (n : nat) : arg_pattern -> term -> Type :=
| min_Hole : minimal_arg_pattern_term n pHole (tRel n)
| min_Rigid p t : minimal_rigid_arg_pattern_term n p t -> minimal_arg_pattern_term n (pRigid p) t
with minimal_rigid_arg_pattern_term (n : nat) : rigid_arg_pattern -> term -> Type :=
| min_argApp pf parg f arg :
  minimal_rigid_arg_pattern_term n pf f ->
  minimal_arg_pattern_term (n + rigid_arg_pattern_holes pf) parg arg ->
  minimal_rigid_arg_pattern_term n (pargApp pf parg) (tApp f arg)
| min_Constr ind k ui : minimal_rigid_arg_pattern_term n (pConstr ind k) (tConstruct ind k ui).

Scheme minimal_arg_pattern_ind := Minimality for minimal_arg_pattern_term Sort Type
  with minimal_rigid_arg_pattern_ind := Minimality for minimal_rigid_arg_pattern_term Sort Type.

Inductive minimal_subst n : nat -> list term -> Type :=
| min_subst_empty : minimal_subst n n []
| min_subst_single p t : minimal_arg_pattern_term n p t -> minimal_subst n (n + arg_pattern_holes p) [t]
| min_subst_app m p s1 s2 : minimal_subst n m s1 -> minimal_subst m p s2 -> minimal_subst n p (s1 ++ s2).

Inductive minimal_pattern_term (n : nat) : pattern -> term -> Type :=
| min_Head k m u : minimal_pattern_term n (pSymb k m) (tSymb k m u)
| min_App pf parg f arg :
  minimal_pattern_term n pf f ->
  minimal_arg_pattern_term (n + pattern_holes pf) parg arg ->
  minimal_pattern_term n (pApp pf parg) (tApp f arg)
| min_Case indn p pc c brs (flagCase : case_in_pattern = true) :
  minimal_pattern_term n pc c ->
  let m := n + pattern_holes pc in
  p.(preturn) = tRel m ->
  map bbody brs = list_make tRel (S m) #|brs| ->
  minimal_pattern_term n (pCase pc #|brs|) (tCase indn p c brs)
| min_Proj pr pc c : minimal_pattern_term n pc c -> minimal_pattern_term n (pProj pc) (tProj pr c).

Inductive minimal_term : term -> Type :=
| min_Arg n p t : minimal_arg_pattern_term n p t -> minimal_term t
| min_Rig n p t : minimal_rigid_arg_pattern_term n p t -> minimal_term t
| min_Pat n p t : minimal_pattern_term n p t -> minimal_term t.

Derive Signature for minimal_arg_pattern_term minimal_rigid_arg_pattern_term minimal_pattern_term minimal_subst minimal_term.

Lemma minimal_atpos_arg_pattern n p t pos :
  minimal_arg_pattern_term n p t ->
  validpos_arg_pattern p pos ->
  minimal_term (atpos t pos).
Proof.
  induction pos in n, p, t |- * => //.
  1: now econstructor.
  destruct p => //=.
  destruct a, p => //=.
  all: intro H; inv H; inv X.
  all: unfold validpos_arg_pattern; cbn.
  all: intro H; eapply IHpos; tea.
  1: instantiate (1 := pRigid _).
  1: now constructor.
  assumption.
Qed.

Lemma minimal_atpos_pattern n p t pos :
  minimal_pattern_term n p t ->
  validpos_pattern p pos ->
  minimal_term (atpos t pos).
Proof.
  induction pos in n, p, t |- * => //.
  1: now econstructor.
  destruct a, p => //=.
  all: intro H; inv H.
  all: unfold validpos_pattern; cbn.
  all: try eapply IHpos; tea.
  now eapply minimal_atpos_arg_pattern.
Qed.

Lemma minimal_arg_pattern_matches n p t :
  minimal_arg_pattern_term n p t ->
  arg_pattern_matches p t (list_make tRel n (arg_pattern_holes p)) ×
  forall p' s,
  arg_pattern_matches p' t s ->
  (forall σ, arg_pattern_matches p' (subst0 σ t) (map (subst0 σ) s)) ×
  minimal_subst n (n + arg_pattern_holes p) s.
Proof.
  set (P0 := fun n p t =>
    rigid_arg_pattern_matches p t (list_make tRel n (rigid_arg_pattern_holes p)) ×
    forall p' s,
    rigid_arg_pattern_matches p' t s ->
    (forall σ, rigid_arg_pattern_matches p' (subst0 σ t) (map (subst0 σ) s)) ×
    minimal_subst n (n + rigid_arg_pattern_holes p) s
    ).
  induction 1 using minimal_arg_pattern_ind with (P0 := P0).
  all: subst P0; unfold arg_pattern_matches, rigid_arg_pattern_matches in *; cbn in *; intros.
  - split. 1: reflexivity.
    destruct p' => //=. 2: destruct p => //.
    intros ? [= <-]. cbn.
    split. 1: reflexivity.
    eapply min_subst_single with (p := pHole).
    constructor.
  - destruct IHX as (? & IHX2).
    split; tas.
    destruct p' => //=. 2: now eapply IHX2.
    intros ? [= <-].
    split. 1: reflexivity.
    eapply min_subst_single with (p := pRigid _).
    constructor. eassumption.
  - destruct IHX as (IHX & IHX1), IHX0 as (IHX' & IHX1').
    split.
    1: rewrite IHX IHX' list_make_app //.
    intros.
    apply rigid_pattern_matches_app_inv in H as (pf' & parg' & s1 & s2 & -> & -> & H1 & H2).
    specialize (IHX1 _ _ H1) as [IHX1 IHX2].
    specialize (IHX1' _ _ H2) as [IHX1' IHX2'].
    split.
    + intro σ. rewrite /= IHX1 IHX1' map_app //.
    + rewrite Nat.add_assoc. econstructor; eassumption.
  - split.
    1: rewrite !eqb_refl //.
    intros.
    destruct p' => //=.
    revert H.
    cbn.
    destruct (eqb_specT ind0 ind) => //.
    destruct (eqb_specT n0 k) => //=.
    intros [= <-]; split; auto.
    rewrite Nat.add_0_r; constructor.
Qed.

Lemma minimal_arg_pattern_subst n p t :
  minimal_arg_pattern_term n p t ->
  forall s s1 s2 s1' s2' n0,
  n0 + #|s1| = n -> n0 + #|s1'| = n ->
  #|s| = arg_pattern_holes p ->
  subst (s1 ++ s ++ s2) n0 t = subst (s1' ++ s ++ s2') n0 t.
Proof.
  set (P0 := fun n p t =>
    forall s s1 s2 s1' s2' n0,
    n0 + #|s1| = n -> n0 + #|s1'| = n ->
    #|s| = rigid_arg_pattern_holes p ->
    subst (s1 ++ s ++ s2) n0 t = subst (s1' ++ s ++ s2') n0 t
  ).
  induction 1 using minimal_arg_pattern_ind with (P0 := P0); subst P0; cbn in *; intros; auto.
  2: {
  rewrite -(firstn_skipn (rigid_arg_pattern_holes pf) s).
  f_equal.
  - rewrite -!app_assoc. eapply IHX; tas.
    rewrite firstn_length_le //. lia.
  - rewrite !app_assoc -app_assoc -app_assoc -app_assoc app_assoc. eapply IHX0; tas.
    all: len.
    1,2: rewrite firstn_length_le; try lia.
    rewrite skipn_length. lia.
  }
  destruct s as [|t[]] => //.
  destruct (Nat.leb_spec n0 n) => //=.
  rewrite -{1}H -{2}H0.
  rewrite nth_error_app2. 1: lia. replace (_ + _ - _ - _) with 0 by lia.
  rewrite nth_error_app2. 1: lia. replace (_ + _ - _ - _) with 0 by lia.
  cbnr.
Qed.

Lemma minimal_subst_leq n m a :
  minimal_subst n m a ->
  n <= m.
Proof.
  induction 1; cbn; intros; auto.
  all: lia.
Qed.

Lemma minimal_subst_subst n m a :
  minimal_subst n m a ->
  forall s s1 s2 s1' s2' n0,
  n0 + #|s1| = n -> n0 + #|s1'| = n ->
  #|s| = m - n ->
  map (subst (s1 ++ s ++ s2) n0) a = map (subst (s1' ++ s ++ s2') n0) a.
Proof.
  induction 1; cbn; intros; auto.
  - f_equal.
    eapply minimal_arg_pattern_subst; tea.
    lia.
  - rewrite -(firstn_skipn (m - n) s).
    rewrite !map_app.
    apply minimal_subst_leq in X1, X2.
    f_equal.
    + rewrite -!app_assoc. eapply IHX1; tas.
      rewrite firstn_length_le //. lia.
    + rewrite !app_assoc -app_assoc -app_assoc -app_assoc app_assoc. eapply IHX2; tas.
      all: len.
      1,2: rewrite firstn_length_le; try lia.
      rewrite skipn_length. lia.
Qed.

Lemma minimal_subst_closed n m a :
  minimal_subst n m a ->
  All (closedn m) a.
Proof.
  induction 1; cbn; intros; auto.
  2: { apply All_app_inv => //. apply All_impl with (1 := IHX1). intros. eapply closed_upwards; tea. eapply minimal_subst_leq. eassumption. }
  repeat constructor.
  set (P0 := fun n p t => closedn (n + rigid_arg_pattern_holes p) t).
  induction m using minimal_arg_pattern_ind with (P0 := P0); subst P0; cbn in *; intros; auto.
  - apply Nat.ltb_lt; lia.
  - rewrite !Nat.add_assoc.
    toProp => //.
    eapply closed_upwards; tea. lia.
Qed.

Lemma subst_map_subst_closed s ms p n M :
  closedn (p + #|ms| + n) M ->
  subst s (p + n) (subst ms p M) = subst (map (subst s n) ms) p M.
Proof.
  intro H.
  rewrite distr_subst_rec.
  rewrite (subst_closed _ _ M) //.
Qed.

Lemma subst_id m p M :
  closedn (p + m) M ->
  subst (list_make tRel 0 m) p M = M.
Proof.
  induction M in m, p |- * using PCUICInduction.term_forall_list_ind; simpl;
  intros; unfold test_predicate_k, test_branch_k, test_def in *; rtoProp; simpl; autorewrite with map;
    try solve [f_equal; eauto; solve_all]; repeat nth_leb_simpl.
  - rewrite list_make_length in l.
    rewrite nth_error_list_make // in e. injection e as [= <-].
    cbn.
    replace _ with n by lia.
    reflexivity.
  - cbn in H. rewrite list_make_length in l. exfalso. destruct (Nat.ltb_spec n (p + m)) => //. lia.
  - f_equal; eauto.
    + solve_all. eapply e. rewrite -Nat.add_assoc //.
    + solve_all. eapply b0. rewrite -Nat.add_assoc //.
Qed.

Lemma id_subst s :
  s = map (subst0 s) (list_make tRel 0 #|s|).
Proof.
  eapply All2_eq, All2_from_nth_error.
  1: rewrite map_length list_make_length //.
  intros n t1 t2 H Hnth Hnth'.
  rewrite nth_error_map nth_error_list_make //= in Hnth'.
  injection Hnth' as [= <-].
  rewrite Nat.sub_0_r Hnth lift0_id //.
Qed.

Lemma minimal_pattern_matches n p t :
  minimal_pattern_term n p t ->
  (∑ ui, pattern_matches p t {| found_subst := list_make tRel n (pattern_holes p); found_usubst := ui |}) ×
  forall p' s,
  pattern_matches p' t s ->
  (forall σ, pattern_matches p' (subst0 σ t) (found_substitution_map (map (subst0 σ)) id s)) ×
  minimal_subst n (n + pattern_holes p) (found_subst s).
Proof.
  induction 1.
  all: unfold pattern_matches in *; cbn in *; intros.
  - split.
    { rewrite !eqb_refl; now eexists. }
    destruct p' => //=.
    destruct (eqb_specT k0 k) => //.
    destruct (eqb_specT n0 m) => //=.
    intros ? [= <-]. split; cbn; auto.
    rewrite Nat.add_0_r. constructor.
  - destruct IHX as ((ui & IHX) & IHX1).
    apply minimal_arg_pattern_matches in m as (IHX' & IHX1').
    split.
    { rewrite IHX IHX' /found_substitution_app /found_substitution_map /= list_make_app //. now eexists. }
    intros.
    apply pattern_matches_app_inv in H as (pf' & parg' & s1 & s2 & -> & -> & H1 & H2).
    specialize (IHX1 _ _ H1) as [IHX1 IHX2].
    specialize (IHX1' _ _ H2) as [IHX1' IHX2'].
    split.
    + intro σ. rewrite /found_substitution_app /found_substitution_map /= IHX1 IHX1' map_app //.
    + rewrite Nat.add_assoc. econstructor; eassumption.
  - destruct IHX as ((ui & IHX) & IHX1).
    split.
    { rewrite !eqb_refl flagCase IHX e /found_substitution_app /found_substitution_map //=.
      eexists. do 2 f_equal.
      rewrite no_case_in_pattern // in flagCase. }
    intros.
    apply pattern_matches_case_inv in H as (pc' & sc & -> & -> & _ & H1).
    specialize (IHX1 _ _ H1) as [IHX1 IHX2].
    split.
    1: intro σ; rewrite /found_substitution_app /found_substitution_map /= map_length eqb_refl flagCase IHX1 map_app //.
    all: now rewrite no_case_in_pattern // in flagCase.
  - destruct IHX as ((ui & IHX) & IHX1).
    split.
    1: now eexists.
    intros.
    destruct p' => //.
    now specialize (IHX1 _ _ H).
Qed.

Lemma minimal_term_subst t p s :
  minimal_term t ->
  pattern_matches p t s ->
  ∑ n m, minimal_subst n m (found_subst s).
Proof.
  destruct 1.
  3: intro H; repeat eexists; eapply minimal_pattern_matches; tea; exact [].
  all: intro H; exfalso.
  - apply minimal_arg_pattern_matches in m as X; destruct X as (X & _).
    destruct p0 => //=.
    + depelim m. solve_discr.
    + eapply symb_hd_rigid_shape. 1: now eapply pattern_to_symb_hd. now eapply rigid_to_shape.
  - apply min_Rigid, minimal_arg_pattern_matches in m as X; destruct X as (X & _).
    eapply symb_hd_rigid_shape. 1: now eapply pattern_to_symb_hd. now eapply rigid_to_shape.
Qed.

Lemma exists_none_some {A} : (exists (s: A), None = Some s) -> False. intros []; by easy. Qed.

Lemma rigid_pattern_matches_app_inv_Prop {pf parg f arg} :
  (exists s, rigid_arg_pattern_matches (pargApp pf parg) (tApp f arg) s) ->
  (exists s, rigid_arg_pattern_matches pf f s) ×
  (exists s, arg_pattern_matches parg arg s).
Proof.
  intro H.
  split; destruct H as (s & H).
  all: apply rigid_pattern_matches_app_inv in H as (? & ? & ? & ? & [= <- <-] & ? & ? & ?).
  all: eexists; eassumption.
Qed.

Lemma pattern_matches_app_inv_Prop {pf parg f arg} :
  (exists s, pattern_matches (pApp pf parg) (tApp f arg) s) ->
  (exists s, pattern_matches pf f s) ×
  (exists s, arg_pattern_matches parg arg s).
Proof.
  intro H.
  split; destruct H as (s & H).
  all: apply pattern_matches_app_inv in H as (? & ? & ? & ? & [= <- <-] & ? & ? & ?).
  all: eexists; eassumption.
Qed.

Lemma pattern_matches_case_inv_Prop {p nbrs ci pr c brs} :
  (exists s, pattern_matches (pCase p nbrs) (tCase ci pr c brs) s) ->
  (exists s, pattern_matches p c s).
Proof.
  intros (s & H).
  apply pattern_matches_case_inv in H as (? & ? & [= <- ->] & ? & ? & ?).
  eexists; eassumption.
Qed.

Fixpoint arg_pattern_minimize p t (n: nat) {struct p} : (exists s, arg_pattern_matches p t s) -> term :=
  match p with
  | pHole => fun _ => tRel n
  | pRigid p => fun H => rigid_arg_pattern_minimize p t n H
  end
with rigid_arg_pattern_minimize p t (n: nat) {struct p} : (exists s, rigid_arg_pattern_matches p t s) -> term :=
  match p with
  | pConstr _ _ => fun _ => t
  | pargApp pf parg =>
    match t with
    | tApp t1 t2 => fun H =>
      let t1 := rigid_arg_pattern_minimize pf t1 n (fst (rigid_pattern_matches_app_inv_Prop H)) in
      let t2 := arg_pattern_minimize parg t2 (n + rigid_arg_pattern_holes pf) (snd (rigid_pattern_matches_app_inv_Prop H)) in
      tApp t1 t2
    | _ => fun H => False_rect term (exists_none_some H)
    end
  end.

Lemma rigid_pattern_minimize_erase_proof p t n H H' :
  rigid_arg_pattern_minimize p t n H = rigid_arg_pattern_minimize p t n H'.
Proof.
  induction p in t, n, H, H' |- * using rigid_arg_pattern_ind
    with (P := fun p => forall t n H H', arg_pattern_minimize p t n H = arg_pattern_minimize p t n H'); intros; auto.
  - cbn. apply IHp.
  - cbn. destruct t => //.
    all: try solve [destruct H => //].
    f_equal; eauto.
Qed.

Lemma arg_pattern_minimize_erase_proof p t n H H' :
  arg_pattern_minimize p t n H = arg_pattern_minimize p t n H'.
Proof.
  destruct p => //=.
  apply rigid_pattern_minimize_erase_proof.
Qed.

Lemma rigid_pattern_minimize_sound p t s n H :
  rigid_arg_pattern_matches p t s ->
  let t' := rigid_arg_pattern_minimize p t n H in
  minimal_rigid_arg_pattern_term n p t' ×
  forall s1 s2 n0, n0 + #|s1| = n ->
  subst (s1 ++ s ++ s2) n0 t' = lift0 n0 t.
Proof.
  set P : forall _ _ _, Type := fun p t s =>
  forall n H,
  let t' := arg_pattern_minimize p t n H in
  minimal_arg_pattern_term n p t' ×
  forall s1 s2 n0, n0 + #|s1| = n ->
  subst (s1 ++ s ++ s2) n0 t' = lift0 n0 t.
  set P' : forall _ _ _, Type := fun p t s =>
  forall n H,
  let t' := rigid_arg_pattern_minimize p t n H in
  minimal_rigid_arg_pattern_term n p t' ×
  forall s1 s2 n0, n0 + #|s1| = n ->
  subst (s1 ++ s ++ s2) n0 t' = lift0 n0 t.
  intro X.
  revert n H.
  eapply arg_pattern_matches_mutual_ind with (P := P) (P' := P'); subst P P'; cbn; intros; cbn; auto.
  - repeat split. 1: constructor.
    intros.
    destruct (Nat.leb_spec n0 n). 2: lia.
    rewrite nth_error_app_ge. 1: lia.
    replace (_ - _ - _) with 0 by lia. cbnr.
  - specialize (X0 n H0).
    destruct X0 as (? & ?); repeat (split; tas).
    now constructor.
  - specialize (X0 n (rigid_pattern_matches_app_inv_Prop H1).1).
    destruct X0.
    specialize (X1 (n + rigid_arg_pattern_holes pf) (rigid_pattern_matches_app_inv_Prop H1).2).
    destruct X1.
    split. 1: now econstructor. intros. cbn. f_equal.
    + rewrite -app_assoc.
      eapply e => //.
    + rewrite -app_assoc {1}app_assoc.
      eapply e0 => //.
      apply rigid_pattern_matches_length in H as Hl.
      len; lia.
  - split; tas.
    1: constructor.
    now intros.
Qed.

Lemma arg_pattern_minimize_sound p t s n H :
  arg_pattern_matches p t s ->
  let t' := arg_pattern_minimize p t n H in
  minimal_arg_pattern_term n p t' ×
  forall s1 s2 n0, n0 + #|s1| = n ->
  subst (s1 ++ s ++ s2) n0 t' = lift0 n0 t.
Proof.
  destruct p => //=.
  - intros [= <-].
    repeat split. 1: constructor.
    intros.
    destruct (Nat.leb_spec n0 n). 2: lia.
    rewrite nth_error_app_ge. 1: lia.
    replace (_ - _ - _) with 0 by lia. cbnr.
  - intro.
    eapply rigid_pattern_minimize_sound with (n := n)(H := H) in H0 as [].
    split => //.
    now constructor.
Qed.

From MetaCoq.PCUIC Require Import PCUICOnFreeVars.

Lemma rigid_arg_pattern_minimize_on_free_vars p t n H :
  on_free_vars xpredT t ->
  on_free_vars xpredT (rigid_arg_pattern_minimize p t n H).
Proof.
  induction p in t, n, H |- * using rigid_arg_pattern_ind
    with (P := fun p => forall t n H, on_free_vars xpredT t -> on_free_vars xpredT (arg_pattern_minimize p t n H)); intros; auto.
  - cbn. now apply IHp.
  - cbn. destruct t => //.
    all: try solve [destruct H => //].
    inv_on_free_vars.
    cbn. rtoProp. split; auto.
Qed.

Lemma arg_pattern_minimize_on_free_vars p t n H :
  on_free_vars xpredT t ->
  on_free_vars xpredT (arg_pattern_minimize p t n H).
Proof.
  destruct p => //=.
  eapply rigid_arg_pattern_minimize_on_free_vars.
Qed.

Fixpoint pattern_minimize p t (n nt : nat) {struct p} : (exists s, pattern_matches p t s) -> term :=
  match p with
  | pSymb _ _ => fun _ => t
  | pApp pf parg =>
    match t with
    | tApp t1 t2 => fun H =>
    let t1 := pattern_minimize pf t1 n nt (fst (pattern_matches_app_inv_Prop H)) in
    let t2 := arg_pattern_minimize parg t2 (n + pattern_holes pf) (snd (pattern_matches_app_inv_Prop H)) in
    tApp t1 t2
    | _ => fun H => False_rect term (exists_none_some H)
    end
  | pCase p nbrs =>
    match t with
    | tCase indn p' c brs => fun H =>
    let c := pattern_minimize p c n nt (pattern_matches_case_inv_Prop H) in
    let n := n + pattern_holes p in
    let p' := {| pparams := map (lift0 nt) (pparams p'); puinst := puinst p'; pcontext := pcontext p';
      preturn := mkApps (tRel (n + #|pcontext p'|)) (List.rev (list_make tRel 0 #|pcontext p'|)) |} in
    let brs := mapi (fun k br => let k := k + (S n) in {| bcontext := bcontext br; bbody := mkApps (tRel (k + #|bcontext br|)) (List.rev (list_make tRel 0 #|bcontext br|)) |}) brs in
    tCase indn p' c brs
    | _ => fun H => False_rect term (exists_none_some H)
    end
  | pProj p =>
    match t with
    | tProj p' c => fun H =>
    let c := pattern_minimize p c n nt H in
    tProj p' c
    | _ => fun H => False_rect term (exists_none_some H)
    end
  end.

Lemma pattern_minimize_erase_proof p t n nt H H' :
  pattern_minimize p t n nt H = pattern_minimize p t n nt H'.
Proof.
  induction p in t, n, nt, H, H' |- * => //=; destruct t => //.
  all: try solve [destruct H => //].
  all: try solve [f_equal => //].
  - f_equal => //.
    apply arg_pattern_minimize_erase_proof.
Qed.

Lemma pattern_minimize_sound p t s n nt H :
  pattern_matches p t s ->
  forall n0,
  let t' := pattern_minimize p t n (n0 + nt) H in
  minimal_pattern_term n p t' ×
  forall s1 s2, n0 + #|s1| = n -> #|s1| + #|found_subst s| + #|s2| = nt ->
  subst (s1 ++ found_subst s ++ s2) n0 t' = lift0 n0 t.
Proof.
  intro X.
  revert n nt.
  induction X using pattern_matches_ind => //=; intros.
  - split; intros; auto. constructor.
  - specialize (IHX (pattern_matches_app_inv_Prop H).1 n nt n0).
    destruct IHX.
    pose proof (arg_pattern_minimize_sound _ _ _ (n + pattern_holes pf) (pattern_matches_app_inv_Prop H).2 H0) as H2.
    destruct H2; subst.
    split. 1: now econstructor. intros. cbn. f_equal.
    + rewrite -app_assoc.
      eapply e => //. revert H2. len.
    + rewrite -app_assoc {1}app_assoc.
      eapply e0 => //.
      apply pattern_matches_length in X as Hl.
      revert H2.
      len.
  - specialize (IHX (pattern_matches_case_inv_Prop H) n nt n0).
    destruct IHX; subst.
    apply pattern_matches_length in X as Hl.
    split.
    { relativize (pCase pc #|brs|). 1: eapply min_Case. 5: len. all: tas. all: cbn. all: rewrite no_case_in_pattern // in flagCase. }
    intros. cbn. f_equal.
    + unfold map_predicate_k. f_equal => //=.
      * rewrite map_map. apply All2_eq, All2_map, All2_refl => t.
        epose proof (simpl_subst _ t n0 n0) as Hlen.
        relativize (n0 + nt). 1: eapply Hlen.
        1: lia.
        rewrite -H1. len.
      * rewrite subst_mkApps -Hl /=.
        destruct (Nat.leb_spec (#|pcontext p| + n0) (n + #|found_subst s| + #|pcontext p|)). 2: lia.
        rewrite -!app_assoc nth_error_app_ge. 1: lia.
        rewrite nth_error_app_ge. 1: lia.
        replace _ with 0. 2: lia. rewrite {1}/sc. cbn -[sc].
        rewrite map_rev list_make_map.
        assert (forall p s n k, list_make (fun i => subst s (k + p + n) (tRel i)) k p = list_make tRel k p).
        { induction p0 => //. intros; cbn [list_make]. f_equal. 1: cbn; destruct (Nat.leb_spec (k + S p0 + n1) k) => //. 1: lia. relativize (k + S p0). 1: eapply IHp0. lia. }
        rewrite (H3 _ _ _ 0). clear H3.
        rewrite no_case_in_pattern // in flagCase.
    + rewrite -!app_assoc.
      eapply e => //.
      revert H1. len.
    + rewrite no_case_in_pattern // in flagCase.
  - specialize (IHX H n nt n0).
    destruct IHX.
    split => //. 1: now constructor.
    intros. cbn. f_equal. now apply e.
Qed.

Lemma pattern_minimize_on_free_vars p t n nt H :
  on_free_vars xpredT t ->
  on_free_vars xpredT (pattern_minimize p t n nt H).
Proof.
  induction p in t, n, nt, H |- * => //=; destruct t => //.
  all: try solve [destruct H => //].
  - intros; inv_on_free_vars; cbn; rtoProp; split.
    1: auto.
    now apply arg_pattern_minimize_on_free_vars.
  - intros; inv_on_free_vars.
    cbn. rewrite !map_length. rtoProp; repeat split.
    + solve_all.
      eapply on_free_vars_lift0.
      eapply on_free_vars_impl; tea. unfold addnP; auto.
    + rewrite shiftnP_xpredT on_free_vars_mkApps.
      rtoProp; split; cbnr.
      rewrite forallb_rev.
      clear. generalize 0 as m; induction #|pcontext p0| => //=.
    + rewrite test_context_k_closed_on_free_vars_ctx //.
    + auto.
    + clear -p1 p5. unfold mapi. generalize 0 at 2 as m.
      induction brs => m //=.
      cbn in p5.
      rtoProp; repeat split; auto.
      rewrite shiftnP_xpredT on_free_vars_mkApps.
      rtoProp; split; cbnr.
      rewrite forallb_rev.
      clear. generalize 0 as m; induction #|bcontext a| => //=.
  - cbn. auto.
Qed.
