(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Lia ssreflect ssrbool.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config (* BasicAst *).
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICCases PCUICOnFreeVars
  PCUICPattern PCUICPosition PCUICReduction PCUICPatternUnification PCUICPatternMinimization
  PCUICParallelReduction PCUICTyping PCUICUnivSubst PCUICTactics.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.


Lemma firstn_skipn_split {A} a b c (τ : list A) :
 firstn (b + c) (skipn a τ) = firstn b (skipn a τ) ++ firstn c (skipn (a + b) τ).
Proof.
  intros.
  rewrite -{1}(firstn_skipn b (firstn _ (skipn _ _))).
  f_equal.
  - rewrite firstn_firstn. f_equal. lia.
  - rewrite -firstn_skipn_comm skipn_skipn //.
Qed.

Lemma subst_factorisation1 Σ P Γ Γ' τ α α' p n :
  (forall t t', pred1 Σ Γ Γ' t t' -> on_free_vars xpredT t -> on_free_vars xpredT t') ->
  All (on_free_vars xpredT) τ ->
  forall H: pred1 Σ Γ Γ' (subst0 τ α) α',
  All_ctx P Γ Γ' (pred1_pred_context Σ H) ->
  minimal_arg_pattern_term n p α ->
  n + arg_pattern_holes p <= #|τ| ->
  ∑ τ',
    (forall τ'0 τ'1, #|τ'0| = n -> α' = subst0 (τ'0 ++ τ' ++ τ'1) α) ×
    All (on_free_vars xpredT) τ' ×
    All2 (fun t t' : term => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) (firstn (arg_pattern_holes p) (skipn n τ)) τ'.
Proof.
  intros pred1_on_free_vars Hτ **.
  revert α' H X H0.
  set (P0 := fun n p α =>
  forall α' (H : pred1 Σ Γ Γ' (subst0 τ α) α'),
  All_ctx P Γ Γ' (pred1_pred_context Σ H) ->
  n + rigid_arg_pattern_holes p <= #|τ| ->
  ∑ τ', (forall τ'0 τ'1, #|τ'0| = n -> α' = subst0 (τ'0 ++ τ' ++ τ'1) α) × All (on_free_vars xpredT) τ' × All2 (fun t t' : term => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) (firstn (rigid_arg_pattern_holes p) (skipn n τ)) τ'
  ).
  induction X0 using minimal_arg_pattern_ind with (P0 := P0); subst P0; cbn -[subst] in *; intros; eauto.
  - exists [α']; repeat split.
    + intros ?? <-. cbn. rewrite Nat.sub_0_r nth_error_app2 // Nat.sub_diag /= lift0_id //.
    + repeat constructor.
      eapply pred1_on_free_vars; tea.
      cbn.
      destruct nth_error eqn:e => //.
      eapply All_nth_error in e; tea.
      rewrite lift0_id //.
    + revert H X.
      cbn.
      rewrite Nat.sub_0_r.
      destruct (nth_error τ n) as [α|] eqn: e=> //.
      2: { apply nth_error_None in e. lia. }
      assert (firstn 1 (skipn n τ) = [α]) as ->. { pose proof (skipn_nth_error τ n). rewrite e in H. rewrite H /= //. }
      rewrite lift0_id.
      repeat constructor.
      exists H; assumption.
  - revert H X1.
    rewrite firstn_skipn_split.
    cbn.
    pose proof (minimal_arg_pattern_matches _ (pRigid pf) _ ltac:(now econstructor)) as (X' & _). apply rigid_to_shape in X'.
    apply rigid_shape_subst with (n := 0) (s := τ) in X'. remember (subst0 τ f) as f' in *.
    intro H. depelim H => //; solve_discr.
    { apply symb_hd_rigid_shape in X1 => //. }
    subst f'.
    rename M1 into αf, N1 into αarg.
    intro X1.
    inv X1. inv X2.
    specialize (IHX0 _ _ X1 ltac:(lia)) as (τ'1 & e1 & c1 & a1).
    specialize (IHX1 _ _ X4 ltac:(lia)) as (τ'2 & e2 & c2 & a2).
    exists (τ'1 ++ τ'2); repeat split.
    { apply All2_length in a1 as e.
      rewrite firstn_length skipn_length in e.
      intros. cbn. f_equal.
      - rewrite (e1 τ'0 (τ'2 ++ τ'3)) //.
        rewrite -app_assoc //.
      - rewrite (e2 (τ'0 ++ τ'1) τ'3).
        len; lia.
        rewrite -!app_assoc //. }
    1: now apply All_app_inv.
    now apply All2_app.
  - cbn in H.
    eexists; split => //.
    cbn. intros _ _ _.
    clear X.
    depelim H => //.
    1: solve_discr.
    1: solve_discr.
Qed.


Lemma subst_factorisation_rec Σ P Γ Γ' τ α σ n l :
  (forall t t', pred1 Σ Γ Γ' t t' -> on_free_vars xpredT t -> on_free_vars xpredT t') ->
  All (on_free_vars xpredT) τ ->
  minimal_subst n l α ->
  All2 (fun t t' : term => ∑ H : pred1 Σ Γ Γ' (subst0 τ t) t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) α σ ->
  l <= #|τ| ->
  ∑ τ',
    (forall τ'0 τ'1, #|τ'0| = n -> σ = map (subst0 (τ'0 ++ τ' ++ τ'1)) α) ×
    All (on_free_vars xpredT) τ' ×
    All2 (fun t t' : term => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) (firstn (l - n) (skipn n τ)) τ'.
Proof.
  intros pred1_on_free_vars Hτ.
  induction 1 in σ |- *.
  { depelim X. rewrite Nat.sub_diag firstn_0 //. eexists; split => //. }
  2: {
    intros.
    apply minimal_subst_leq in X1 as Hlen1, X2 as Hlen2.
    apply All2_length in X as Hlen.
    rewrite -(firstn_skipn #|s1| σ) in X |- *.
    apply All2_app_inv in X as (H1 & H2).
    2: { len in Hlen. rewrite firstn_length_le; lia. }
    specialize (IHX1 _ H1) as (τ'1 & e1 & c1 & a1). 1: lia.
    specialize (IHX2 _ H2) as (τ'2 & e2 & c2 & a2); tas.
    assert (#|τ'1| = m - n). { apply All2_length in a1 as <-. apply firstn_length_le. rewrite skipn_length. lia. }
    exists (τ'1 ++ τ'2); split.
    { intros. rewrite map_app. f_equal.
      - rewrite (e1 τ'0 (τ'2 ++ τ'3)) //.
        rewrite -app_assoc //.
      - rewrite (e2 (τ'0 ++ τ'1) τ'3).
        len; lia.
        rewrite -!app_assoc //. }
    assert (firstn (p - n) (skipn n τ) = firstn (m - n) (skipn n τ) ++ firstn (p - m) (skipn m τ)) as ->.
    { replace m with (n + (m - n)) at 3 by lia. relativize (p - n). 1:eapply firstn_skipn_split. lia. }
    split. 1: apply All_app_inv; assumption.
    apply All2_app; assumption.
  }
  intros.
  depelim X. depelim X.
  destruct s as (r & IHr).
  replace (n + _ - n) with (arg_pattern_holes p) by lia.
  cbn.
  eapply subst_factorisation1 in IHr as (τ' & H1 & H2); tea.
  exists τ'. split => //.
  intros. f_equal. auto.
Qed.


Lemma subst_factorisation Σ P Γ Γ' τ α σ :
  (forall t t', pred1 Σ Γ Γ' t t' -> on_free_vars xpredT t -> on_free_vars xpredT t') ->
  All (on_free_vars xpredT) τ ->
  All2 (fun t t' : term => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) (map (subst0 τ) α) σ ->
  minimal_subst 0 #|τ| α ->
  ∑ τ',
    σ = map (subst0 τ') α ×
    All (on_free_vars xpredT) τ' ×
    All2 (fun t t' : term => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) τ τ'.
Proof.
  intros pred1_on_free_vars Hτ **.
  cut (∑ τ' : list term, (forall τ'0 τ'1, #|τ'0| = 0 -> σ = map (subst0 (τ'0 ++ τ' ++ τ'1)) α) × All (on_free_vars xpredT) τ' × All2 (fun t t' : term => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) τ τ').
  { intros (τ' & H & H'). exists τ'; repeat split => //. rewrite -(app_nil_r τ'). apply H with (τ'0 := []) (τ'1 := []) => //. }
  apply All2_map_left_inv in X. cbn in X.
  assert (H : #|τ| <= #|τ|) by lia; revert H.
  revert X0 X.
  assert (firstn (#|τ| - 0) (skipn 0 τ) = τ).
  { cbn. apply firstn_ge. lia. }
  rewrite -{7}H. clear H.
  now eapply subst_factorisation_rec.
Qed.


Section pred1_match.
Context (Σ : global_env).
Context (pred1_on_free_vars : forall Γ Γ' t t', pred1 Σ Γ Γ' t t' -> on_ctx_free_vars xpredT Γ -> on_free_vars xpredT t -> on_free_vars xpredT t').

Lemma pred1_arg_pattern_matches0 P Γ Γ' t t' Δ Δ' p s :
  pred1_ctx Σ Δ Δ' -> on_free_vars xpredT t' ->
  forall (H : pred1 Σ Γ Γ' t t') (ctx := pred1_pred_context Σ H), All_ctx P Γ Γ' ctx ->
  (forall p s, rigid_arg_pattern_matches p t s ->
    ∑ Hi s,
      rigid_arg_pattern_matches p t s ×
      forall n,
      let t0 := rigid_arg_pattern_minimize p t n Hi in
      ∑ t0' s',
        pred1 Σ Δ Δ' t0 t0' ×
        All (on_free_vars xpredT) s' ×
        (forall s'1 s'2, #|s'1| = n -> t' = subst0 (s'1 ++ s' ++ s'2) t0') ×
        All2 (fun t t' => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) s s') ->
  (arg_pattern_matches p t s ->
    ∑ Hi s,
      arg_pattern_matches p t s ×
      forall n,
      let t0 := arg_pattern_minimize p t n Hi in
      ∑ t0' s',
        pred1 Σ Δ Δ' t0 t0' ×
        All (on_free_vars xpredT) s' ×
        (forall s'1 s'2, #|s'1| = n -> t' = subst0 (s'1 ++ s' ++ s'2) t0') ×
        All2 (fun t t' => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) s s').
Proof.
  intros HΔ Ht' h ctx H IH.
  destruct p.
  - intros [= <-].
    unshelve eexists. { eexists; reflexivity. }
    eexists; repeat split.
    intros n t0.
    cbn in t0.
    eexists t0, [t']. repeat split.
    + now eapply pred1_refl_gen.
    + repeat constructor. apply Ht'.
    + intros ?? <-. cbn.
      rewrite nth_error_app2. { lia. }
      rewrite Nat.sub_0_r Nat.sub_diag /= lift0_id //.
    + repeat constructor; tas.
      now eexists.
  - intros. specialize (IH p s H0) as (Hi & s0 & Hu & HH).
    exists Hi, s0.
    split => //.
Defined.

Context {cf : checker_flags} {wfΣ : wf Σ}.

Lemma pred1_pattern_matches_arg P Γ Γ' t t' Δ Δ' :
  pred1_ctx Σ Γ Γ' -> pred1_ctx Σ Δ Δ' -> on_ctx_free_vars xpredT Γ -> on_free_vars xpredT t ->
  forall (H : pred1 Σ Γ Γ' t t') (ctx := pred1_pred_context Σ H), All_ctx_strict P Γ Γ' ctx ->
  (forall p s,
    rigid_arg_pattern_matches p t s ->
    ∑ Hi s,
    rigid_arg_pattern_matches p t s ×
    forall n,
    let t0 := rigid_arg_pattern_minimize p t n Hi in
    ∑ t0' s',
      pred1 Σ Δ Δ' t0 t0' ×
      All (on_free_vars xpredT) s' ×
      (forall s'1 s'2, #|s'1| = n -> t' = subst0 (s'1 ++ s' ++ s'2) t0') ×
      All2 (fun t t' => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) s s') ×
  (forall p s,
    pattern_matches p t s ->
    forall k rd n, lookup_rules Σ k = Some rd -> symb_hd t = Some (k, n) ->
    ∑ p0 ps Hi s,
    unify_patterns_n p0 p ps ×
    All (fun posp => ∑ r', In r' (rd.(prules) ++ rd.(rules)) × r'.(pat_lhs) = posp.2) ps ×
    pattern_matches p0 t s ×
    forall n1 n2,
    let t0 := pattern_minimize p0 t n1 (pattern_holes p0 + n1 + n2) Hi in
    ∑ t0' s',
      pred1 Σ Δ Δ' t0 t0' ×
      All (on_free_vars xpredT) s' ×
      (forall s'1 s'2, #|s'1| = n1 -> #|s'2| = n2 -> t' = subst0 (s'1 ++ s' ++ s'2) t0') ×
      All2 (fun t t' => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) (found_subst s) s').
Proof using cf pred1_on_free_vars wfΣ.
  revert Γ Γ' t t' Δ Δ'.
  fix aux 11.
  intros Γ Γ' t t' Δ Δ' HΓ HΔ onΓ ont H ctx X.
  pose proof (ont' := pred1_on_free_vars _ _ _ _ H onΓ ont).
  destruct H.
  all: try solve [clear aux; split; intros; solve_discr].
  - split; intros ???.
    { apply pattern_to_symb_hd in p as e0. apply symb_hd_rigid_shape in e0 as e0' => //. now apply rigid_to_shape in H. }
    intros k0 rd0 n0 Hlookup Hsymbhd. assert (k0 = k) as ->.
    { apply lookup_rules_declared_gen, declared_rules_from_gen in Hlookup. clear ctx X. eapply PCUICWeakeningEnvTyp.on_declared_rule_prule in e as []; tea. apply pattern_to_symb_hd in p. rewrite lhsHead Hsymbhd in p. now noconf p. }
    assert (rd0 = rdecl) as ->.
    { clear ctx X. apply @declared_rules_to_gen with (1 := wfΣ) in d. eapply lookup_rules_declared_gen in Hlookup. eapply PCUICGlobalEnv.declared_rules_inj; eassumption. }
    destruct s as [s ui]; cbn in * |-.
    destruct s0 as [s0 ui0]; cbn in *|-.
    assert (ui = ui0) as <-. { eapply patterns_match_usubst with (1 := p) (2 := H). }
    assert (unifiable_patterns Compat p0 (pat_lhs decl)). { apply unifiable_patterns_sound. now repeat eexists. }
    pose (unify_patterns_same_root _ _ H0) as pp.
    exists pp.
    pose proof (unify_patterns_same_root_super _ _ H0) as (H1' & H1'').
    epose proof unify_patterns_same_root_sound2 _ _ H0 _ _ _. do 2 forward X0 by tea. fold pp in X0. destruct X0 as ((s00 & ui0) & Hp0).
    apply pattern_matches_length in Hp0 as Hp0len; cbn in Hp0len.
    assert (ui = ui0) as <-. { eapply patterns_match_usubst with (1 := p) (2 := Hp0). }
    eapply on_free_vars_pattern_inv in Hp0 as ons00; tea. cbn in ons00. apply forallb_All in ons00.
    eexists [_], (ex_intro _ _ Hp0), _.
    split. { econstructor. constructor. instantiate (1 := unifoff_Here _ _ _ _). cbn. reflexivity. }
    split. { repeat constructor. eexists. split => //=. now eapply nth_error_In. }
    split; [eassumption|].
    intros n1 n2 t0.
    set s00p := (list_make tRel 0 n1 ++ s00 ++ list_make tRel (pattern_holes pp) n2).
    assert (ons00p : All (on_free_vars xpredT) s00p).
    { repeat apply All_app_inv => //. 1: generalize 0 as m; rename n1 into n. 2: generalize (pattern_holes pp) as m; rename n2 into n. all: induction n; intro; cbn; constructor; auto. }
    pose proof (pattern_minimize_sound _ _ _ n1 (pattern_holes pp + n1 + n2) (ex_intro _ _ Hp0) Hp0 0). cbn in X0. fold t0 in X0. destruct X0 as (Hmppt0 & eqsubstt0).
    specialize (eqsubstt0 (list_make tRel 0 n1) (list_make tRel (pattern_holes pp) n2)).
    rewrite !list_make_length lift0_id in eqsubstt0.
    forward eqsubstt0 by lia. forward eqsubstt0 by lia.
    apply minimal_pattern_matches in Hmppt0 as ((ui0 & Hp00) & IHp00). cbn in IHp00.
    assert (ui0 = ui) as ->.
    { apply IHp00 in Hp00 as (Hp00 & _). pose proof Hp0 as Hp0'.
      rewrite -eqsubstt0 in Hp0'.
      specialize (Hp00 s00p).
      now eapply patterns_match_usubst with (1 := Hp00) (2 := Hp0'). }
    eapply unify_patterns_same_root_sound1 in Hp00 as Hp01. destruct Hp01 as ((s01 & ui0) & (s02 & ui1) & Hp01 & Hp02).
    assert (ui = ui0) as <-. { eapply patterns_match_usubst with (1 := Hp00) (2 := Hp01). }
    assert (ui = ui1) as <-. { eapply patterns_match_usubst with (1 := Hp00) (2 := Hp02). }
    eapply IHp00 in Hp01 as Hpmin01. destruct Hpmin01 as (IHp01 & Hpmin01). specialize (IHp01 s00p); rewrite /pattern_matches eqsubstt0 H in IHp01. injection IHp01 as [= IHp01].
    eapply IHp00 in Hp02 as Hpmin02. destruct Hpmin02 as (IHp02 & Hpmin02). specialize (IHp02 s00p); rewrite /pattern_matches eqsubstt0 p in IHp02. injection IHp02 as [= IHp02].
    cbn in *.
    assert (All2 (fun t t' => ∑ H : pred1 Σ Γ Γ' t t', All_ctx P Γ Γ' (pred1_pred_context Σ H)) s s').
    { inv X. clear -a0 X0. induction a0 => //=. depelim X0. constructor; auto. exists r. assumption. }
    rewrite IHp02 in X0.
    apply All2_map_left_inv in X0. cbn in X0.
    eapply subst_factorisation_rec in X0 as (s00' & IHp02' & ons00' & X0); tea.
    2: intros; now eapply pred1_on_free_vars.
    2: len; rewrite !list_make_length; lia.
    replace (n1 + pattern_holes pp - n1) with (pattern_holes pp) in X0 by lia.
    rewrite skipn_app skipn_all2 in X0. { rewrite list_make_length; lia. }
    rewrite list_make_length Nat.sub_diag /= firstn_app -Hp0len Nat.sub_diag firstn_all firstn_0 // app_nil_r in X0.
    assert (closedn #|s02| (subst ss #|s02| (rhs decl))).
    { eapply PCUICWeakeningEnvTyp.on_declared_rule_prule in e as H'; tea.
      destruct H'.
      eapply PCUICClosed.closedn_subst with (k := 0).
      1: { unfold ss, symbols_subst. clear. generalize 0 at 2. induction (_ - _) => //=. }
      relativize (_ + _ + _); tea.
      rewrite -(map_length (subst0 s00p) s02) -IHp02 (pattern_matches_length _ lhs _ p) // /ss symbols_subst_length map_length lhsHoles. lia.
    }
    eexists (subst0 (s02 ++ _) (rhs decl)), s00'.
    repeat split; tea.
    2: {
      intros s'1 s'2 elen elen2.
      rewrite /rhs0 {1}subst_app_simpl [subst0 (s02 ++ _) _]subst_app_simpl (IHp02' s'1 s'2) // map_length //=. change 0 with (0 + 0) at 3.
      rewrite subst_map_subst_closed. 2: f_equal. 1: rewrite Nat.add_0_r //.
    }
    eapply pred_rewrite with (s := {| found_subst := _; found_usubst := _ |}) => //; tea.
    apply All2_refl; intro. now apply pred1_refl_gen.

  - set (H := pred_symb _ _ _ k n u a) in ctx.
    split; intros ???.
    { solve_discr. }
    intros k0 rd0 n0 Hlookup Hsymbhd.
    apply pattern_matches_symb_inv in H0 as H'.
    destruct H' as (e & H').
    exists p, [], (ex_intro _ _ H0), s; repeat split; tas.
    1: { constructor => //. }
    { constructor. }
    intros n' t0.
    exists (tSymb k n u), [].
    subst.
    repeat split; tas.
    1: now constructor.
    all: constructor.

  - split; intros ???.
    { apply rigid_pattern_matches_app_inv in H1 as (pf & parg & s1 & s2 & -> & -> & e1 & e2).
      repeat inv_on_free_vars.
      unfold ctx in X. inv X. inv X0.
      eapply (fst (aux _ _ M0 _ _ _ HΓ HΔ onΓ a0 _ X)) in e1 as (Hif & s1' & Hp1 & HH1).
      eapply pred1_arg_pattern_matches0 with (1 := HΔ) (2 := b) (3 := X1) in e2 as (Hiarg & s2' & Hp2 & HH2); tas.
      2: inv X1; eapply (fst (aux _ _ _ _ _ _ HΓ HΔ onΓ b0 _ X0)).
      assert (Hi : rigid_arg_pattern_matches (pargApp pf parg) (tApp M0 N0) (s1' ++ s2')).
      { rewrite /rigid_arg_pattern_matches /= Hp1 Hp2 //. }
      exists (ex_intro _ _ Hi), (s1' ++ s2').
      split => //.
      cbn. intros n.
      rewrite (rigid_pattern_minimize_erase_proof _ _ _ _ Hif) (arg_pattern_minimize_erase_proof _ _ _ _ Hiarg).
      specialize (HH1 n) as (tf' & s1'' & hr1 & Hsc1 & Hs1 & hs1).
      specialize (HH2 (n + rigid_arg_pattern_holes pf)) as (targ' & s2'' & hr2 & Hsc2 & Hs2 & hs2).
      set (tf := rigid_arg_pattern_minimize _ _ _ Hif) in *.
      set (targ := arg_pattern_minimize _ _ _ Hiarg) in *.
      exists (tApp tf' targ'), (s1'' ++ s2''). repeat split.
      + constructor => //.
      + apply All_app_inv => //.
      + intros ?? <-. cbn. f_equal.
        * rewrite (Hs1 s'1 (s2'' ++ s'2)) -?app_assoc //.
        * rewrite (Hs2 (s'1 ++ s1'') s'2) -?app_assoc //.
          rewrite app_length -(All2_length hs1) (rigid_pattern_matches_length _ _ _ Hp1) //.
      + apply All2_app => //.
    }
    intros k0 rd0 n0 Hlookup Hsymbhd.
    repeat inv_on_free_vars.
    apply pattern_matches_app_inv in H1 as H1'; destruct H1' as (pf & parg & s1 & s2 & -> & -> & e1 & e2).
    unfold ctx in X. inv X. inv X0.
    eapply pred1_arg_pattern_matches0 with (1 := HΔ) (3 := X1) in e2 as (Hiarg & s2' & Hp2 & HH2); tas.
    2: inv X1; eapply (fst (aux _ _ _ _ _ _ HΓ HΔ onΓ b0 _ X0)).
    destruct (snd (aux _ _ _ _ _ _ HΓ HΔ onΓ a0 H X) pf s1 e1 _ _ _ Hlookup Hsymbhd) as (ppf & psf & Hif & s1' & Hu1 & Hus1 & Hp1 & HH1).
    exists (pApp ppf parg).
    eassert (Huu : pattern_matches (pApp ppf parg) (tApp M0 N0) _).
    { rewrite /pattern_matches /= Hp1 Hp2 //. }
    eexists (map (fun '(pos, p') => (app_l :: pos, p')) psf), (ex_intro _ _ Huu), _.
    split. { clear -Hu1. induction Hu1 => //=. 1: constructor; congruence. unshelve econstructor. 1: constructor => //. cbn. assumption. }
    split. { solve_all. destruct x => //. }
    split; tea.
    intros n1 n2 t0.
    subst t0. cbn.
    rewrite (pattern_minimize_erase_proof _ _ _ _ _ Hif) (arg_pattern_minimize_erase_proof _ _ _ _ Hiarg).
    specialize (HH1 n1 (n2 + arg_pattern_holes parg)).
    replace (_ + _ + _) with (pattern_holes ppf + arg_pattern_holes parg + n1 + n2) in HH1 by lia.
    destruct HH1 as (tf' & s1'' & hr1 & Hsc1 & Hs1 & hs1).
    set (tf := pattern_minimize ppf M0 n1 (pattern_holes ppf + arg_pattern_holes parg + n1 + n2) Hif) in *.
    specialize (HH2 (n1 + pattern_holes ppf)) as (targ' & s2'' & hr2 & Hsc2 & Hs2 & hs2).
    set (targ := arg_pattern_minimize parg N0 (n1 + pattern_holes ppf) Hiarg) in *.
    exists (tApp tf' targ'), (s1'' ++ s2''). repeat split.
    + constructor => //.
    + apply All_app_inv => //.
    + intros ?? <- <-. cbn. f_equal.
      * rewrite (Hs1 s'1 (s2'' ++ s'2)) -?app_assoc //.
        rewrite app_length -(All2_length hs2) (arg_pattern_matches_length _ _ _ Hp2) Nat.add_comm //.
      * rewrite (Hs2 (s'1 ++ s1'') s'2) -?app_assoc //.
        rewrite app_length -(All2_length hs1) (pattern_matches_length _ _ _ Hp1) //.
    + apply All2_app => //.

  - split; intros ???.
    { solve_discr. }
    intros k0 rd0 n0 Hlookup Hsymbhd.
    repeat inv_on_free_vars.
    apply pattern_matches_case_inv in H1 as (pc & sc & -> & -> & flagCase & ec).
    unfold ctx in X. inv X. inv X2.
    destruct (snd (aux _ _ _ _ _ _ HΓ HΔ onΓ p10 H0 X) pc sc ec _ _ _ Hlookup Hsymbhd) as (ppc & psc & Hic & sc' & Huc & Husc & Hpc & HHc).
    exists (pCase ppc #|brs0|).
    eassert (Huu : pattern_matches (pCase ppc #|brs0|) (tCase ci p0 c0 brs0) _).
    { rewrite /pattern_matches /= Hpc eqb_refl flagCase //. }
    eexists (map (fun '(pos, p') => (case_c :: pos, p')) psc), (ex_intro _ _ Huu), _.
    split. { clear -Huc. induction Huc => //=. 1: constructor; congruence. unshelve econstructor. 1: constructor => //. cbn. assumption. }
    split. { solve_all. destruct x => //. }
    split; tea.
    intros n1 n2 t0.
    subst t0. cbn.
    rewrite (pattern_minimize_erase_proof _ _ _ _ _ Hic).
    specialize (HHc n1 (n2 + S #|brs0|)).
    replace (_ + _ + _) with (pattern_holes ppc + S #|brs0| + n1 + n2) in HHc by lia.
    destruct HHc as (tc' & sc'' & hrc & Hscc & Hsc & hsc).
    set (tc := pattern_minimize ppc c0 n1 (pattern_holes ppc + S #|brs0| + n1 + n2) Hic) in *.
    destruct p1 as [pars1 puinst1 pctx1 pret1]. cbn in *.
    set stot' := sc'' ++ [it_mkProd_or_LetIn (inst_case_context pars1 puinst1 pctx1) pret1] ++ map (fun br => it_mkLambda_or_LetIn (inst_case_context pars1 puinst1 br.(bcontext)) (bbody br)) brs1.
    eexists (tCase ci (mk_predicate _ _ _ _) tc' _), stot'.
    repeat split.
    3: {
    intros ?? e1 e2. cbn. unfold map_predicate_k, map_branch_k. cbn. f_equal. 1: f_equal; cbnr.
    - instantiate (1 := map (lift0 (n1 + #|stot'| + n2 + 0)) pars1).
      apply All2_eq, All2_map_right, All2_map_right, All2_refl. intro t.
      eassert (n1 + #|stot'| + n2 = #|s'1 ++ stot' ++ s'2|) as -> by (len; lia).
      rewrite simpl_subst // lift0_id //.
    - rewrite no_case_in_pattern // in flagCase.
    - erewrite (Hsc s'1 (_ ++ s'2)) => //. 1: { rewrite /stot' -app_assoc. f_equal. }
      len. rewrite (All2_length a2). lia.
    - apply All2_eq, All2_map_right.
      rewrite no_case_in_pattern // in flagCase.
    }
    + constructor => //=.
      * apply All2_map, All2_impl with (1 := a0). intros.
        rewrite no_case_in_pattern // in flagCase.
        (* eapply weakening_pred1_0.
        relativize (n1 + _ + _ + _). *)
      * unfold inst_case_predicate_context; cbn.
        rewrite no_case_in_pattern // in flagCase.
      * apply pred1_refl_gen.
        apply on_contexts_app => //.
        rewrite no_case_in_pattern // in flagCase.
      * unfold inst_case_branch_context; cbn.
        instantiate (1 := mapi (fun k br => {| bcontext := bcontext br; bbody :=
             mkApps (tRel (k + S (n1 + pattern_holes ppc) + #|bcontext br|)) (List.rev (list_make tRel 0 #|bcontext br|)) |}) brs1).
        rewrite no_case_in_pattern // in flagCase.
    + repeat apply All_app_inv => //.
      * repeat constructor.
        rewrite on_free_vars_it_mkProd_or_LetIn inst_case_context_length p3 andb_true_r.
        eapply on_free_vars_ctx_inst_case_context; tea; cbnr.
      * solve_all.
        rewrite on_free_vars_it_mkLambda_or_LetIn inst_case_context_length H2 andb_true_r.
        eapply on_free_vars_ctx_inst_case_context; tea; cbnr. now toAll.
    + rewrite -app_assoc. repeat apply All2_app => //.
      * repeat constructor.
        rewrite no_case_in_pattern // in flagCase.
      * apply All2_map.
        rewrite no_case_in_pattern // in flagCase.


  - split; intros ???.
    { solve_discr. }
    intros k0 rd0 n0 Hlookup Hsymbhd.
    unfold ctx in X; inv X. inv X0.
    destruct p0 => //.
    cbn in ont, ont'.
    destruct (snd (aux _ _ _ _ _ _ HΓ HΔ onΓ ont H X) p0 s H0 _ _ _ Hlookup Hsymbhd) as (ppc & psc & Hic & sc' & Huc & Husc & Hpc & HHc).
    exists (pProj ppc).
    eassert (Huu : pattern_matches (pProj ppc) (tProj p c) _).
    { rewrite /pattern_matches /= Hpc //. }
    eexists (map (fun '(pos, p') => (proj_c :: pos, p')) psc), (ex_intro _ _ Huu), _.
    split. { clear -Huc. induction Huc => //=. 1: constructor; congruence. unshelve econstructor. 1: constructor => //. cbn. assumption. }
    split. { solve_all. destruct x => //. }
    split; tea.
    intros n1 n2 t0.
    subst t0. cbn.
    rewrite (pattern_minimize_erase_proof _ _ _ _ _ Hic).
    specialize (HHc n1 n2).
    destruct HHc as (tc' & sc'' & hrc & Hscc & Hsc & hsc).
    set (tc := pattern_minimize ppc c n1 (pattern_holes ppc + n1 + n2) Hic) in *.
    eexists (tProj p tc'), sc''.
    repeat split.
    + constructor => //.
    + apply Hscc.
    + intros ?? <- <-. cbn. f_equal.
      apply Hsc => //.
    + assumption.

  - split; intros.
    2: { solve_discr. destruct t => //. }
    exists (ex_intro _ _ H), s; repeat split; tas.
    intros n t0.
    eapply rigid_pattern_minimize_sound with (n := n) (H := ex_intro _ _ H) in H as HH.
    fold t0 in HH. destruct HH as (Hmint0 & eqsubstt0).
    assert (s = []) as ->.
    { clear -i H. destruct t => //; solve_discr.  destruct p => //=. rewrite /rigid_arg_pattern_matches /= in H. destruct (eqb_specT ind0 ind), (eqb_specT n0 n) => //=. now injection H as [=]. }
    exists t0, []. repeat split; tas; auto.
    + now apply pred1_refl_gen.
    + intros.
      rewrite eqsubstt0.
      1: lia.
      rewrite lift0_id //.
Qed.

Definition pred1_pattern_matches P Γ Γ' t t' Δ Δ' := fun HΓ HΔ onΓ ont H X => snd (pred1_pattern_matches_arg P Γ Γ' t t' Δ Δ' HΓ HΔ onΓ ont H X).

Definition pred1_arg_pattern_matches P Γ Γ' t t' Δ Δ' p s := fun HΓ HΔ onΓ ont H X =>
  let ont' := pred1_on_free_vars _ _ _ _ H onΓ ont in
  pred1_arg_pattern_matches0 P Γ Γ' t t' Δ Δ' p s HΔ ont' H X (fst (pred1_pattern_matches_arg P _ _ _ _ _ _ HΓ HΔ onΓ ont H (All_ctx_to_strict X))).

End pred1_match.






Definition triangle_criterion Σ :=
  forall k rd r,
  lookup_rules Σ k = Some rd ->
  forall t s,
  first_match (rd.(prules) ++ rd.(rules)) t = Some (r, s) ->
  minimal_pattern_term 0 r.(pat_lhs) t ->
  forall Γ Γ' Γ'' Δ u,
  assumption_context Δ ->
  #|Δ| = pattern_holes (r.(pat_lhs)) ->
  on_ctx_free_vars xpredT Δ ->
  pred1_ctx Σ Γ Γ' ->
  pred1_ctx Σ Γ' Γ'' ->
  on_ctx_free_vars xpredT Γ ->
  on_free_vars xpredT t ->
  pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ) t u ->
  let ss := symbols_subst k 0 s.(found_usubst) #|rd.(symbols)| in
  pred1 Σ (Γ' ,,, Δ) (Γ'' ,,, Δ) u (subst0 (s.(found_subst) ++ ss) r.(rhs)).

Lemma wf_pattern_unification_closed {cf : checker_flags} Σ (wfΣ : wf Σ) : pattern_unification_closed Σ.
Proof.
  intros ? **.
  admit.
Admitted.

Lemma first_match_best_match {cf : checker_flags} Σ (wfΣ : wf Σ) : triangle_criterion Σ.
Proof.
  intros ? **.
  apply first_match_rule_list in H0 as Hp.
  destruct Hp as (n' & e & Hp).
  admit.
Admitted.




Definition triangle_criterion' Σ :=
  forall k rd r r',
  lookup_rules Σ k = Some rd ->
  forall t s,
  minimal_pattern_term 0 r.(pat_lhs) t ->
  first_match (rd.(prules) ++ rd.(rules)) t = Some (r, s) ->
  In r' (rd.(prules) ++ rd.(rules)) ->
  forall Γ Γ' st s0 ctx,
  pred1_ctx Σ Γ Γ' ->
  on_ctx_free_vars xpredT Γ ->
  on_free_vars xpredT t ->
  t = fill_context st ctx ->
  pattern_matches r'.(pat_lhs) st s0 ->
  let ss := symbols_subst k 0 s.(found_usubst) #|rd.(symbols)| in
  let ss0 := symbols_subst k 0 s0.(found_usubst) #|rd.(symbols)| in
  pred1 Σ Γ Γ'
    (fill_context (subst0 (found_subst s0 ++ ss0) r'.(rhs)) ctx)
    (subst0 (s.(found_subst) ++ ss) r.(rhs)).


Lemma old_impl_new_no_symb_argpattern {cf : checker_flags} Σ (wfΣ : wf Σ):
  (forall Γ Γ', pred1_ctx Σ Γ Γ' -> on_ctx_free_vars xpredT Γ -> on_ctx_free_vars xpredT Γ') ->
  triangle_criterion' Σ ->
  triangle_criterion Σ.
Proof.
  intros pred1_on_ctx_free_vars X.
  intros ? **.
  assert (#|Δ| >= pattern_holes (pat_lhs r)) by lia.
  eapply pred1_ctx_app_refl_gen with (Δ := Δ) in X1 as X1', X2 as X2'.
  eapply lookup_rules_declared_gen in H as HH.
  eapply declared_rules_from_gen in HH.
  eapply first_match_rule_list in H0 as H0'; destruct H0' as (? & ? & ?).
  cut (((pattern_matches (pat_lhs r) u s) + ∑ r' st s0 ctx,
    In r' (rd.(prules) ++ rd.(rules)) ×
    t = fill_context st ctx ×
    unifiable_patterns_off Compat r.(pat_lhs) (term_context_position ctx) r'.(pat_lhs) ×
    pattern_matches r'.(pat_lhs) st s0 ×
    u = fill_context (subst0 (found_subst s0 ++ (symbols_subst k 0 s0.(found_usubst) #|rd.(symbols)|)) r'.(rhs)) ctx)%type).
  { intros [Hp | (r' & st & s0 & ctx & ? & -> & ? & ? & ->)].
    1: { econstructor. all: tea. apply All2_refl; intros; now apply pred1_refl_gen. }
    unshelve eapply X => //; tea.
    eapply pred1_on_ctx_free_vars; tea.
    rewrite PCUICInstConv.on_ctx_free_vars_app PCUICInstConv.addnP_xpredT H3 H4 //.
  }
  assert (Xarg : forall p n t u Γ Γ' Δ, assumption_context Δ -> #|Δ| >= n + arg_pattern_holes p -> minimal_arg_pattern_term n p t -> pred1 Σ (Γ,,, Δ) (Γ',,, Δ) t u -> t = u) by shelve.
  assert (Xrew : forall Γ Γ' Δ k rd n pr t k1 rdecl decl s0 s s' r0 (ss := symbols_subst k1 0 (found_usubst s) #|symbols rdecl|),
    declared_rules Σ k rd ->
    pattern_head pr = (k, n) ->
    declared_rules Σ k1 rdecl ->
    nth_error (prules rdecl ++ rules rdecl) r0 = Some decl ->
    minimal_pattern_term 0 pr t ->
    pattern_matches pr t s0 ->
    pattern_matches (pat_lhs decl) t s ->
    All2 (pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ)) (found_subst s) s' ->
    assumption_context Δ -> #|Δ| >= pattern_holes pr ->
    ∑ (r' : rewrite_rule) (st : term) (s0 : found_substitution) (ctx : term_context),
    In r' (prules rd ++ rules rd)
    × t = fill_context st ctx
      × unifiable_patterns_off Compat pr (term_context_position ctx) (pat_lhs r')
        × pattern_matches (pat_lhs r') st s0 × subst0 (s' ++ ss) (rhs decl) = fill_context (subst0 (found_subst s0 ++ symbols_subst k 0 (found_usubst s0) #|symbols rd|) (rhs r')) ctx
  ).
  { clear -wfΣ Xarg.
    intros.
    apply pattern_to_symb_hd in H3 as p, H4 as p'.
    eapply PCUICWeakeningEnvTyp.on_declared_rule_prule with (1 := wfΣ) in H1 as H'; tea. destruct H'.
    rewrite p lhsHead H0 /= in p'. noconf p'.
    eapply @declared_rules_to_gen with (1 := wfΣ), PCUICGlobalEnv.declared_rules_inj in H as e.
    2: now eapply @declared_rules_to_gen with (1 := wfΣ).
    subst rdecl.
    repeat eexists; tea.
    2: instantiate (1 := tCtxHole).
    all: eauto.
    * now eapply nth_error_In.
    * constructor. apply unifiable_patterns_sound; repeat eexists; tea.
    * cbn. do 2 f_equal.
      apply minimal_pattern_matches in X as (? & IHX0).
      specialize (IHX0 _ _ H4) as (? & X4).
      clear -X0 X4 Xarg H5 H6. cbn in X4.
      induction X4 in s', X0, H6 |- *.
      1: now depelim X0.
      { depelim X0. inv X0. f_equal. eapply Xarg in p => //; tea. }
      apply All2_length in X0 as Xlen.
      rewrite -(firstn_skipn #|s1| s') in X0 |- *.
      apply All2_app_inv in X0 as [].
      2: len in Xlen; rewrite firstn_length; lia.
      f_equal; eauto.
      eapply IHX4_1; tea. apply minimal_subst_leq in X4_2. lia.
  }
  eapply PCUICWeakeningEnvTyp.on_declared_rule_prule with (1 := wfΣ) in e as H'; tea. destruct H'.
  clear -wfΣ H X0 X3 Xrew Xarg p lhsHead HH H1 H6.
  { induction X0 in u, s, p, X3, lhsHead, H6 |- *; cbn in H6.
  - depelim X3; unfold pred_atom in * => //; solve_discr.
    2: now left.
    right.
    unfold ss.
    eapply Xrew => //; tea. constructor.
  - depelim X3; unfold pred_atom in * => //; solve_discr.
    1: right; eapply Xrew => //; tea. 1: now constructor.
    apply pattern_matches_app_inv in p as (? & ? & s1 & s2 & [= -> ->] & -> & p1 & p2).
    assert (arg = N1) as <- by now eapply Xarg.
    specialize (IHX0 _ _ X3_1 ltac:(lia) p1 lhsHead) as [Hp | (? & ? & ? & ? & ? & ? & ? & ? & ?)].
    { left. rewrite /pattern_matches /= Hp p2 //. }
    right.
    eexists _, _, _, (tCtxApp_l x4 arg); repeat split; tea; cbnr.
    1,3: congruence.
    now constructor.
  - depelim X3; unfold pred_atom in * => //; solve_discr.
    1: right; eapply Xrew => //; tea. 1: now constructor.
    apply pattern_matches_case_inv in p as (? & sc & [= ->] & -> & pflagCase & p).
    assert (p0 = p2) by rewrite no_case_in_pattern // in flagCase.
    assert (brs = brs1) by rewrite no_case_in_pattern // in flagCase.
    specialize (IHX0 _ _ X3_2 ltac:(lia) p lhsHead) as [Hp | (? & ? & ? & ? & ? & ? & ? & ? & ?)].
    + left. rewrite /pattern_matches /= Hp (All2_length a2) eqb_refl flagCase H0 H2 //.
    + right.
      eexists _, _, _, (tCtxCase_discr _ _ _ _); repeat split; tea; cbnr.
      1: rewrite e3; reflexivity.
      2: congruence.
      now constructor.
  - depelim X3; unfold pred_atom in * => //; solve_discr.
    1: right; eapply Xrew => //; tea. 1: now constructor.
    specialize (IHX0 _ _ X3 ltac:(lia) p lhsHead) as [Hp | (? & ? & ? & ? & ? & ? & ? & ? & ?)].
    { left. rewrite /pattern_matches /= Hp //. }
    right.
    eexists _, _, _, (tCtxProj pr x2); repeat split; tea; cbnr.
    1,3: congruence.
    now constructor.
  }
  Unshelve.
  clear -wfΣ.
  intros.
  induction X using minimal_arg_pattern_ind with (P0 := fun n p t => forall u, #|Δ| >= n + rigid_arg_pattern_holes p -> pred1 Σ (Γ,,, Δ) (Γ',,, Δ) t u -> t = u) in u, H0, X0 |- *.
  - depelim X0; unfold pred_atom in * => //; solve_discr.
    destruct nth_error eqn:e' => //.
    rewrite nth_error_app_lt in e'. 1: cbn in H0; lia.
    exfalso.
    injection e.
    revert e'.
    clear -H.
    induction Δ in n, H |- * => //=; destruct n => //=.
    + inv H. intros [= <-] => //.
    + inv H. now apply IHΔ.
  - eapply IHX => //.
  - apply minimal_arg_pattern_matches in X1 as X1'; destruct X1' as (X1' & _).
    apply min_Rigid in X as X'. apply minimal_arg_pattern_matches in X' as (X' & _). change (arg_pattern_matches (pRigid ?p)) with (rigid_arg_pattern_matches p) in X'.
    depelim X0; unfold pred_atom in * => //; solve_discr.
    + exfalso. eapply symb_hd_rigid_shape; tea. now eapply rigid_to_shape.
    + cbn in H0.
      erewrite IHX, IHX0; auto.
      all: lia.
  - depelim X0; unfold pred_atom in * => //; solve_discr.
Qed.

