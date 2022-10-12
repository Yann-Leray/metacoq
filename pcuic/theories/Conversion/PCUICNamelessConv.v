(* Distributed under the terms of the MIT license. *)
From Coq Require Import RelationClasses.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICInduction PCUICCases PCUICRelevance
     PCUICLiftSubst PCUICEquality PCUICReduction PCUICCumulativitySpec PCUICCumulativity PCUICPosition PCUICUnivSubst
     PCUICNamelessDef PCUICGuardCondition PCUICClosedConv PCUICClosedTyp PCUICUnivSubstitutionConv
     PCUICClosed PCUICSigmaCalculus (* for context manipulations *).
Require Import Equations.Prop.DepElim.
Require Import ssreflect.

Implicit Types cf : checker_flags.

(** Conversion does not rely on name annotations of binders.

  We prove this by constructing a type-preserving translation to 
  terms where all binders are anonymous. An alternative would be to 
  be parametrically polymorphic everywhere on the binder name type.
  This would allow to add implicit information too. *)

Local Set Keyed Unification.

Set Default Goal Selector "!".


Lemma banon_spec na : banon na -> na = {| binder_name := nAnon; binder_relevance := na.(binder_relevance) |}.
Proof.
  destruct na, binder_name; cbnr; discriminate.
Qed.

Lemma banon_eq_binder_annot na na' : banon na -> banon na' -> eq_binder_annot na na' -> na = na'.
Proof.
  intros ->%banon_spec ->%banon_spec.
  now unfold eq_binder_annot; simpl; intros ->.
Qed.

Lemma nl_marks_of_context Γ : marks_of_context (nlctx Γ) = marks_of_context Γ.
Proof.
  rewrite /marks_of_context /nlctx map_map //.
Qed. 

Lemma banon_list l : forallb (banon ∘ anonymize) l.
Proof.
  induction l; simpl; auto.
Qed.

Lemma nl_spec :
  forall u, nameless (nl u).
Proof.
  intros u. induction u using term_forall_list_ind.
  all: try reflexivity.
  all: try (simpl ; repeat (eapply andb_true_intro ; split) ; assumption).
  - cbn. solve_all.
  - destruct X as [? [? ?]].
    cbn; rtoProp; repeat split; tas.
    * solve_all.
    * solve_all.
      destruct X.
      rewrite /nameless_decl /=. rtoProp; split; tas.
      destruct (decl_body x); simpl in *; auto.
    * solve_all.
      destruct X.
      rewrite /nameless_decl /=. rtoProp; split; tas.
      destruct (decl_body x0); simpl in *; auto.
  - cbn. solve_all.
    unfold test_def; rtoProp; split; tas.
  - cbn. solve_all.
    unfold test_def; rtoProp; split; tas.
Qed.

Lemma nl_lookup_env :
  forall Σ c,
    lookup_env (nl_global_env Σ) c
    = option_map nl_global_decl (lookup_env Σ c).
Proof.
  intros [univs Σ] c.
  rewrite /lookup_env /=.
  induction Σ. 1: reflexivity.
  simpl.
  case: eqb_spec; intros e; subst.
  - reflexivity.
  - assumption.
Qed.


Lemma nlctx_spec :
  forall Γ, nameless_ctx (nlctx Γ).
Proof.
  intros Γ. induction Γ as [| [na [b|] B] Γ ih].
  - reflexivity.
  - simpl. rewrite /nameless_decl /= 2!nl_spec ih. reflexivity.
  - simpl. rewrite /nameless_decl /= nl_spec ih. reflexivity.
Qed.

Lemma binder_anonymize n : eq_binder_annot n (anonymize n).
Proof. destruct n; reflexivity. Qed.
#[global]
Hint Resolve binder_anonymize : core.
#[global] Hint Constructors compare_decls : core.
Local Hint Unfold map_decl_anon : core.

Lemma nl_decompose_prod_assum :
  forall Γ t,
    decompose_prod_assum (nlctx Γ) (nl t)
    = let '(Γ, t) := decompose_prod_assum Γ t in (nlctx Γ, nl t).
Proof.
  intros Γ t.
  induction t in Γ |- *. all: try reflexivity.
  - apply (IHt2 (Γ ,, vass na t1)).
  - apply (IHt3 (Γ ,, vdef na t1 t2)).
Qed.

Lemma nl_it_mkLambda_or_LetIn :
  forall Γ t,
    nl (it_mkLambda_or_LetIn Γ t) =
    it_mkLambda_or_LetIn (nlctx Γ) (nl t).
Proof.
  intros Γ t.
  induction Γ as [| [na [b|] B] Γ ih] in t |- *.
  - reflexivity.
  - simpl. cbn. rewrite ih. reflexivity.
  - simpl. cbn. rewrite ih. reflexivity.
Qed.

Lemma nl_mkApps :
  forall t l,
    nl (mkApps t l) = mkApps (nl t) (map nl l).
Proof.
  intros t l.
  induction l in t |- *.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma nlctx_app_context :
  forall Γ Δ,
    nlctx (Γ ,,, Δ) = nlctx Γ ,,, nlctx Δ.
Proof.
  intros Γ Δ.
  induction Δ as [| [na [b|] B] Δ ih] in Γ |- *.
  - reflexivity.
  - simpl. f_equal. apply ih.
  - simpl. f_equal. apply ih.
Qed.

Lemma nl_subst_instance :
  forall u b,
    nl (subst_instance u b) = subst_instance u (nl b).
Proof.
  intros u b.
  rewrite /subst_instance /=.
  induction b using term_forall_list_ind.
  all: try (simpl ; rewrite ?IHb ?IHb1 ?IHb2 ?IHb3 ; reflexivity).
  - simpl. f_equal. rename X into H; induction H.
    + reflexivity.
    + simpl. rewrite p IHAll. reflexivity.
  - simpl. rewrite IHb. f_equal.
    * unfold nl_predicate, map_predicate. simpl. f_equal; solve_all.
    * induction X0.
      + reflexivity.
      + simpl. f_equal.
        ++ destruct x. simpl in *. unfold nl_branch, map_branch.
          simpl. f_equal; solve_all.
        ++ apply IHX0.
  - simpl. f_equal. induction X ; try reflexivity.
    simpl. rewrite IHX. f_equal.
    destruct p as [h1 h2].
    destruct x. simpl in *.
    unfold map_def, map_def_anon. cbn.
    rewrite h1 h2. reflexivity.
  - simpl. f_equal. induction X ; try reflexivity.
    simpl. rewrite IHX. f_equal.
    destruct p as [h1 h2].
    destruct x. simpl in *.
    unfold map_def, map_def_anon. cbn.
    rewrite h1 h2. reflexivity.
Qed.

Lemma context_position_nlctx :
  forall Γ,
    context_position (nlctx Γ) = context_position Γ.
Proof.
  intros Γ. induction Γ as [| [na [b|] A] Γ ih ].
  - reflexivity.
  - simpl. rewrite ih. reflexivity.
  - simpl. rewrite ih. reflexivity.
Qed.

Lemma global_ext_levels_nlg :
  forall Σ, global_ext_levels (nlg Σ) = global_ext_levels Σ.
Proof.
  intros [[univs g] ?].
  cbn. unfold global_ext_levels. f_equal.
Qed.

Lemma global_ext_constraints_nlg :
  forall Σ,
    global_ext_constraints (nlg Σ) = global_ext_constraints Σ.
Proof. 
  intros [[univs g] ?]. reflexivity.
Qed.

Lemma lookup_env_nlg :
  forall Σ c decl,
    lookup_env Σ.1 c = Some decl ->
    lookup_env (nlg Σ) c = Some (nl_global_decl decl).
Proof.
  intros [[univs g] ?] c decl h.
  rewrite nl_lookup_env. cbn in *.
  rewrite h. reflexivity.
Qed.

Lemma All_mapi_spec {A B} {P : A -> Type} {l} {f g : nat -> A -> B} {n} :
  All P l -> (forall n x, P x -> f n x = g n x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  induction 1 in n |- *; simpl; trivial.
  intros Heq. rewrite Heq; f_equal; auto.
Qed.
#[global] Hint Resolve All_mapi_spec : all.

Lemma nl_lift :
  forall n k t,
    nl (lift n k t) = lift n k (nl t).
Proof.
  intros n k t.
  induction t in n, k |- * using term_forall_list_ind.
  all: simpl.
  all: try congruence.
  - f_equal. rename X into H; induction H.
    + reflexivity.
    + simpl. f_equal.
      * eapply p.
      * eapply IHAll.
  - rewrite /map_predicate_k /= map_length.
    f_equal; auto.
    * unfold nl_predicate, map_predicate; simpl; f_equal; solve_all.
    * induction X0. 1: reflexivity.
      simpl. f_equal. 2: assumption.
      unfold nl_branch, map_branch_k. cbn. f_equal; auto; solve_all.
  - f_equal. rewrite map_length.
    generalize (#|m| + k). intro l.
    induction X.
    + reflexivity.
    + simpl. f_equal.
      * unfold map_def_anon, map_def. simpl.
        f_equal. all: eapply p.
      * assumption.
  - f_equal. rewrite map_length.
    generalize (#|m| + k). intro l.
    induction X.
    + reflexivity.
    + simpl. f_equal.
      * unfold map_def_anon, map_def. simpl.
        f_equal. all: eapply p.
      * assumption.
Qed.

Lemma nlctx_fix_context_alt :
  forall l,
    nlctx (fix_context_alt l) =
    fix_context_alt (map (fun d => (anonymize d.1, nl d.2)) l).
Proof.
  intro l.
  unfold fix_context_alt. unfold nlctx.
  rewrite map_rev. f_equal.
  rewrite map_mapi. rewrite mapi_map.
  eapply mapi_ext.
  intros n [na t]. simpl.
  unfold map_decl_anon. unfold vass.
  simpl.
  rewrite nl_lift. reflexivity.
Qed.

Lemma map_def_sig_nl :
  forall m,
    map (fun d : aname × term => (anonymize d.1, nl d.2)) (map def_sig m) =
    map def_sig (map (map_def_anon nl nl) m).
Proof.
  intro m.
  rewrite 2!map_map. eapply map_ext.
  intros [na ty bo ra]. simpl.
  unfold def_sig, map_def_anon. simpl.
  reflexivity.
Qed.

(*
Lemma nlctx_stack_context :
  forall ρ,
    nlctx (stack_context ρ) = stack_context (nlstack ρ).
Proof.
  intro ρ. induction ρ.
  all: try (simpl ; rewrite ?IHρ ; reflexivity).
  - simpl. rewrite nlctx_app_context. rewrite IHρ.
    rewrite nlctx_fix_context_alt.
    rewrite map_app. simpl.
    rewrite 2!map_def_sig_nl.
    reflexivity.
  - simpl. rewrite nlctx_app_context. rewrite IHρ.
    rewrite nlctx_fix_context_alt.
    rewrite map_app. simpl.
    rewrite 2!map_def_sig_nl.
    reflexivity.
  - simpl. rewrite nlctx_app_context. now rewrite IHρ.
  - simpl. rewrite nlctx_app_context. now rewrite IHρ.
Qed.
*)

Lemma nl_subst :
  forall s k u,
    nl (subst s k u) = subst (map nl s) k (nl u).
Proof.
  intros s k u.
  induction u in s, k |- * using term_forall_list_ind.
  all: simpl.
  all: try congruence.
  - destruct (_ <=? _). 2: reflexivity.
    rewrite nth_error_map. destruct (nth_error _ _).
    + simpl. apply nl_lift.
    + rewrite map_length. reflexivity.
  - f_equal. rename X into H; induction H.
    + reflexivity.
    + simpl. f_equal.
      * eapply p.
      * eapply IHAll.
  - f_equal; auto.
    * unfold nl_predicate, map_predicate_k; simpl; f_equal;
      rewrite ?map_map_compose ?map_length; solve_all.
    * induction X0. 1: reflexivity.
      simpl. f_equal. 2: assumption.
      unfold nl_branch, map_branch_k. cbn.
      rewrite map_length. f_equal; solve_all.
  - f_equal. rewrite map_length.
    generalize (#|m| + k). intro l.
    induction X.
    + reflexivity.
    + simpl. f_equal.
      * unfold map_def_anon, map_def. simpl.
        f_equal. all: eapply p.
      * assumption.
  - f_equal. rewrite map_length.
    generalize (#|m| + k). intro l.
    induction X.
    + reflexivity.
    + simpl. f_equal.
      * unfold map_def_anon, map_def. simpl.
        f_equal. all: eapply p.
      * assumption.
Qed.

Lemma nl_decompose_app :
  forall t,
    decompose_app (nl t)
    = let '(u, vs) := decompose_app t in (nl u, map nl vs).
Proof.
  intro t.
  unfold decompose_app.
  change [] with (map nl []) at 1. generalize (@nil term).
  induction t. all: try reflexivity.
  intro l. cbn. change (nl t2 :: map nl l) with (map nl (t2 :: l)).
  apply IHt1.
Qed.

Lemma nl_pred_set_preturn p pret : nl_predicate nl (set_preturn p pret) = 
  set_preturn (nl_predicate nl p) (nl pret).
Proof. reflexivity. Qed.

Lemma nl_pred_set_pparams p pret : nl_predicate nl (set_pparams p pret) = 
  set_pparams (nl_predicate nl p) (map nl pret).
Proof. reflexivity. Qed.

Lemma nl_fix_context :
  forall mfix,
    nlctx (fix_context mfix) = fix_context (map (map_def_anon nl nl) mfix).
Proof.
  intro mfix.
  unfold nlctx, fix_context, mapi.
  generalize 0 at 2 4.
  induction mfix.
  - reflexivity.
  - intro n. simpl. rewrite map_app. cbn. f_equal.
    + apply IHmfix.
    + unfold map_decl_anon. cbn. rewrite nl_lift. reflexivity.
Qed.

Lemma nl_declared_constant Σ kn cst :
  declared_constant Σ kn cst ->
  declared_constant (nl_global_env Σ) kn (nl_constant_body cst).
Proof.
  intro H.
  rewrite /declared_constant nl_lookup_env H //.
Qed.

Lemma nl_declared_inductive Σ ind mdecl idecl :
  declared_inductive Σ ind mdecl idecl ->
  declared_inductive (nl_global_env Σ) ind
    (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl).
Proof.
  intros []. split.
  - unfold declared_minductive.
    rewrite nl_lookup_env H.
    simpl. reflexivity.
  - simpl. now rewrite nth_error_map H0.
Qed.

Lemma nl_declared_constructor Σ c mdecl idecl cdecl :
  declared_constructor Σ c mdecl idecl cdecl ->
  declared_constructor (nl_global_env Σ) c
    (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl)
    (nl_constructor_body cdecl).
Proof.
  intros []. split.
  - now eapply nl_declared_inductive.
  - simpl. now rewrite nth_error_map H0.
Qed.

Lemma nl_declared_projection Σ c mdecl idecl cdecl pdecl :
  declared_projection Σ c mdecl idecl cdecl pdecl ->
  declared_projection (nl_global_env Σ) c
    (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl)
    (nl_constructor_body cdecl) (nl_projection_body pdecl).
Proof.
  intros (? & ? & ?). split; [|split]; tas.
  - now eapply nl_declared_constructor.
  - simpl. now rewrite nth_error_map H0.
Qed.

Lemma nl_to_extended_list:
  forall indctx : list context_decl,
    map nl (to_extended_list indctx) = to_extended_list (nlctx indctx).
Proof.
  intros indctx. unfold to_extended_list, to_extended_list_k.
  change [] with (map nl []) at 2.
  unf_term. generalize (@nil term), 0.
  induction indctx.
  - reflexivity.
  - simpl. intros l n.
    destruct a as [? [?|] ?].
    all: cbn.
    all: apply IHindctx.
Qed.

Lemma nlctx_subst_instance :
  forall u Γ,
    nlctx (subst_instance u Γ) = subst_instance u (nlctx Γ).
Proof.
  intros u Γ.
  rewrite /subst_instance /=.
  induction Γ as [| [na [b|] B] Δ ih] in Γ |- *; rewrite /= ?subst_context_snoc /snoc /=
    /map_decl.
  - reflexivity.
  - f_equal; auto.
    rewrite /subst_decl /map_decl /= /map_decl_anon /=; repeat f_equal;
    now rewrite nl_subst_instance.
  - f_equal; [|apply ih].
    rewrite /subst_decl /map_decl /= /map_decl_anon /=; repeat f_equal;
    now rewrite nl_subst_instance.
Qed.

Lemma nlctx_subst_context :
  forall s k Γ,
    nlctx (subst_context s k Γ) = subst_context (map nl s) k (nlctx Γ).
Proof.
  intros s k Γ.
  induction Γ as [| [na [b|] B] Δ ih] in Γ |- *; rewrite /= ?subst_context_snoc /snoc /=
    /map_decl.
  - reflexivity.
  - simpl. f_equal; auto.
    rewrite /subst_decl /map_decl /= /map_decl_anon /=; repeat f_equal.
    * now rewrite nl_subst; len.
    * now rewrite nl_subst; len. 
  - simpl. f_equal; [|apply ih].
    rewrite /subst_decl /map_decl /= /map_decl_anon /=; repeat f_equal.
    now rewrite nl_subst; len.
Qed.


Lemma nlctx_lift_context :
  forall n k Γ,
    nlctx (lift_context n k Γ) = lift_context n k (nlctx Γ).
Proof.
  intros s k Γ.
  induction Γ as [| [na [b|] B] Δ ih] in Γ |- *; rewrite /= ?lift_context_snoc /snoc /=
    /map_decl.
  - reflexivity.
  - simpl. f_equal; auto.
    rewrite /lift_decl /map_decl /= /map_decl_anon /=; repeat f_equal.
    * now rewrite nl_lift; len.
    * now rewrite nl_lift; len. 
  - simpl. f_equal; [|apply ih].
    rewrite /subst_decl /map_decl /= /map_decl_anon /=; repeat f_equal.
    now rewrite nl_lift; len.
Qed.

Lemma nl_it_mkProd_or_LetIn :
  forall Γ A,
    nl (it_mkProd_or_LetIn Γ A) = it_mkProd_or_LetIn (nlctx Γ) (nl A).
Proof.
  intros Γ A.
  induction Γ in A |- *.
  - reflexivity.
  - simpl. rewrite IHΓ. f_equal.
    destruct a as [? [?|] ?].
    all: reflexivity.
Qed.

Lemma nl_context_assumptions ctx : context_assumptions (nlctx ctx) = context_assumptions ctx.
Proof.
  induction ctx; simpl; auto.
  destruct a as [na [b|] ty] => /= //.
  f_equal; auto.
Qed.

Lemma nl_extended_subst Γ k :
  map nl (extended_subst Γ k) = extended_subst (nlctx Γ) k.
Proof.
  revert k; induction Γ as [|[? [] ?] ?]; intros k; simpl; f_equal; auto;
     rewrite ?nl_subst ?nl_lift ?nl_context_assumptions ?IHΓ; len => //.
Qed.

#[global]
Hint Rewrite nl_context_assumptions : len.

Lemma nl_expand_lets_k Γ k t : 
  nl (expand_lets_k Γ k t) = 
  expand_lets_k (nlctx Γ) k (nl t).
Proof.
  rewrite /expand_lets_k.
  now rewrite nl_subst nl_extended_subst nl_lift; len; autorewrite with len.
Qed.

Lemma nl_expand_lets Γ t : 
  nl (expand_lets Γ t) = 
  expand_lets (nlctx Γ) (nl t).
Proof.
  now rewrite /expand_lets nl_expand_lets_k.
Qed.

Lemma subst_instance_nlctx u ctx :
  subst_instance u (nlctx ctx) = nlctx (subst_instance u ctx).
Proof.
  induction ctx; cbnr.
  f_equal. 2: apply IHctx.
  clear. destruct a as [? [] ?]; unfold map_decl, map_decl_anon; cbn; f_equal.
  all: now rewrite nl_subst_instance.
Qed.

Lemma map_anon_fold_context_k g g' ctx : 
  (forall i, nl ∘ g i =1 g' i ∘ nl) ->
  map (map_decl_anon nl) (fold_context_k g ctx) = 
  fold_context_k g' (map (map_decl_anon nl) ctx).
Proof.
  intros hg.
  rewrite !fold_context_k_alt map_mapi mapi_map. 
  apply mapi_ext => i d.
  rewrite /map_decl /map_decl_anon. len.
  f_equal.
  - destruct (decl_body d) => /= //.
    f_equal. apply hg.
  - apply hg.
Qed.

Lemma nl_subst_context s k ctx :
  nlctx (subst_context s k ctx) = 
  subst_context (map nl s) k (nlctx ctx).
Proof.
  rewrite /nlctx /subst_context.
  apply map_anon_fold_context_k. 
  intros i x. now rewrite nl_subst.
Qed.

Lemma nl_subst_telescope s k ctx :
  nlctx (subst_telescope s k ctx) = 
  subst_telescope (map nl s) k (nlctx ctx).
Proof.
  rewrite /nlctx /subst_telescope.
  rewrite map_mapi mapi_map. apply mapi_ext => i d.
  rewrite /map_decl_anon /map_decl; destruct d as [na [b|] ty]; cbn; f_equal;
    now rewrite nl_subst.
Qed.

Lemma nl_lift_context n k ctx :
  nlctx (lift_context n k ctx) = 
  lift_context n k (nlctx ctx).
Proof.
  rewrite /nlctx /subst_context.
  apply map_anon_fold_context_k. 
  intros i x. now rewrite nl_lift.
Qed.

Lemma nl_expand_lets_ctx Γ Δ : 
  nlctx (expand_lets_ctx Γ Δ) = 
  expand_lets_ctx (nlctx Γ) (nlctx Δ).
Proof.
  rewrite /expand_lets_ctx /expand_lets_k_ctx.
  now rewrite nl_subst_context nl_extended_subst nl_lift_context nl_context_assumptions; len.
Qed.

Lemma nl_inds ind puinst bodies :
 map nl (inds ind puinst bodies) =
  inds ind puinst (map nl_one_inductive_body bodies).
Proof.
  rewrite /inds; len.
  induction #|bodies|; simpl; f_equal; auto.
Qed.


Lemma map_map2 {A B C D} (f : A -> B) (g : C -> D -> A) l l' : 
  map f (map2 g l l') = map2 (fun x y => f (g x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto. f_equal.
  apply IHl.
Qed.

Lemma map2_map {A A' B B' C} (f : A -> B) (f' : A' -> B') (g : B -> B' -> C) l l' : 
  map2 g (map f l) (map f' l') = map2 (fun x y => g (f x) (f' y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto. f_equal.
  apply IHl.
Qed.

Lemma nlctx_length Γ : #|nlctx Γ| = #|Γ|.
Proof. now rewrite map_length. Qed.
#[global]
Hint Rewrite nlctx_length : len.

Lemma map2_map_left {A B C D} (f : A -> B) (g : B -> C -> D) (l : list A) (l' : list C) :
  map2 g (map f l) l' = map2 (fun x y => g (f x) y) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto. f_equal; eauto.
Qed.

Lemma map2_ext {A B C} (f g : A -> B -> C) (l : list A) (l' : list B) :
  (forall x y, f x y = g x y) ->  
  map2 f l l' = map2 g l l'.
Proof.
  intros H.
  induction l in l' |- *; destruct l'; simpl; auto. f_equal; eauto.
Qed.

Lemma nl_inst_case_context pars puinst ctx :
  nlctx (inst_case_context pars puinst ctx) =
  inst_case_context (map nl pars) puinst (nlctx ctx).
Proof.
  rewrite /inst_case_context.
  now rewrite nlctx_subst_context map_rev nlctx_subst_instance.
Qed.

Definition nlctx_binders := map (map_decl_anon id).

(*Lemma nl_ind_predicate_context ind mdecl idecl :
  nlctx_binders (ind_predicate_context ind mdecl idecl) =
  nlctx_binders (ind_predicate_context ind (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl)).
Proof.
  rewrite /ind_predicate_context /= /map_decl_anon /=. simpl. f_equal.

 *)

Lemma nlctx_smash_context Γ Δ : 
  nlctx (smash_context Γ Δ) = smash_context (nlctx Γ) (nlctx Δ).
Proof.
  induction Δ as [|[na [b|] ty] Δ] in Γ |- *; simpl; auto.
  - now rewrite IHΔ nlctx_subst_context.
  - now rewrite /= IHΔ nlctx_app_context /=.
Qed.

Lemma nl_case_predicate_context ind mdecl idecl p :
  nlctx (case_predicate_context ind mdecl idecl p) =
  case_predicate_context ind (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl) 
    (nl_predicate nl p).
Proof.
  unfold case_predicate_context, case_predicate_context_gen.
  simpl.
  rewrite /nlctx /=.
  simpl. rewrite /forget_types map_map_compose.
  rewrite /pre_case_predicate_context_gen.
  rewrite map_map2. cbn.
  rewrite /ind_predicate_context /=.
  rewrite /inst_case_context !subst_instance_cons !subst_context_snoc /=.
  destruct (pcontext p); simpl; auto.
  f_equal.
  - rewrite /map_decl_anon /= /set_binder_name /=; f_equal. len.
    rewrite nl_subst map_rev. f_equal.
    rewrite nl_subst_instance. f_equal.
    rewrite nl_mkApps /=. f_equal.
    now rewrite nl_to_extended_list nlctx_app_context nlctx_smash_context -nl_expand_lets_ctx.
  - rewrite -map_rev.
    rewrite -nl_expand_lets_ctx -nlctx_subst_instance -nlctx_subst_context.
    rewrite map2_map.
    rewrite map2_map_left.
    apply map2_ext. intros [] []; reflexivity.
Qed.

Lemma nl_cstr_branch_context ind mdecl cdecl :
  nlctx (cstr_branch_context ind mdecl cdecl) =
  cstr_branch_context ind (nl_mutual_inductive_body mdecl) (nl_constructor_body cdecl).
Proof.
  rewrite /cstr_branch_context.
  rewrite nl_expand_lets_ctx. f_equal.
  rewrite nlctx_subst_context /= // nl_inds //. now len.
Qed.

Lemma nl_case_branch_context ind mdecl p br cdecl :
  nlctx (case_branch_context ind mdecl p br cdecl) =
  case_branch_context ind (nl_mutual_inductive_body mdecl)
    (nl_predicate nl p) (map anonymize br) 
    (nl_constructor_body cdecl).
Proof.
  unfold case_branch_context, case_branch_context_gen. simpl.
  rewrite /pre_case_branch_context_gen. 
  rewrite /nlctx -nl_cstr_branch_context -nl_inst_case_context. cbn.
  now rewrite map_map2 map2_map.
Qed.

Lemma nl_case_branch_type ci mdecl idecl p br i cdecl : 
  let ptm := it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p) in
  case_branch_type ci (nl_mutual_inductive_body mdecl)
    (nl_one_inductive_body idecl) (nl_predicate nl p) 
    (nl_branch nl br)
    (nl ptm) i (nl_constructor_body cdecl) = 
  map_pair nlctx nl (case_branch_type ci mdecl idecl p br ptm i cdecl).
Proof.
  intros ptm.
  unfold case_branch_type, case_branch_type_gen.
  simpl. unfold map_pair. simpl. f_equal.
  - rewrite nl_case_branch_context.
    now rewrite /forget_types !map_map_compose.
  - rewrite nl_mkApps nl_lift; len. f_equal.
    rewrite !map_map_compose map_app /= !map_map_compose nl_mkApps.
    f_equal.
    * apply map_ext => idx. rewrite nl_subst nl_expand_lets_k map_rev.
      now rewrite nlctx_subst_instance nl_subst nl_inds nl_subst_instance.
    * f_equal.
      simpl. f_equal.
      rewrite map_app !map_map_compose.
      setoid_rewrite nl_lift.
      now rewrite nl_to_extended_list.
Qed.

Lemma nl_forget_types ctx : 
  forget_types (map (map_decl_anon nl) ctx) = 
  map anonymize (forget_types ctx).
Proof.
  now rewrite /forget_types !map_map_compose.
Qed.

Lemma nl_wf_predicate mdecl idecl p : 
  wf_predicate mdecl idecl p ->
  wf_predicate (nl_mutual_inductive_body mdecl) (nl_one_inductive_body idecl) (nl_predicate nl p).
Proof.
  intros []; split. 
  { len => //. }
  depelim H0.
  simpl. rewrite nl_forget_types H2 /=. constructor; auto.
  eapply Forall2_map. solve_all.
Qed.

Lemma nl_wf_branch cdecl br :
  wf_branch cdecl br ->
  wf_branch (nl_constructor_body cdecl) (nl_branch nl br).  
Proof.
  unfold wf_branch, wf_branch_gen.
  simpl.
  rewrite nl_forget_types /=.
  intros H; apply Forall2_map; solve_all.
Qed.

Lemma nl_wf_branches idecl brs :
  wf_branches idecl brs ->
  wf_branches (nl_one_inductive_body idecl) (map (nl_branch nl) brs).  
Proof.
  unfold wf_branches, wf_branches_gen.
  simpl. intros H; apply Forall2_map.
  eapply (Forall2_impl H).
  apply nl_wf_branch.
Qed.

Lemma closed_ctx_IH :
  forall (l : list context_decl) (n : nat),
  onctx_k (fun (k : nat) (t : term) => closedn k (nl t)) n l ->
  closedn_ctx n (map (map_decl_anon nl) l).
Proof.   
  unfold onctx_k. intros l n.
  solve_all.
  induction l; simpl; auto. len.
  intros. depelim X.
  rewrite IHl.
  * eapply (Alli_shiftn_inv 0 _ 1) in X.
    eapply (Alli_impl _ X). intros ? [na [b|] ty]; rewrite /ondecl;
    now replace (#|l| - (1 + n0) + n) with (Nat.pred #|l| - n0 + n) by lia.
  * rewrite Nat.sub_0_r in o.
    rewrite /ondecl in o. rewrite /test_decl.
    destruct o. cbn.
    rewrite i. destruct (decl_body a) => //. simpl in o.
    simpl. now rewrite o.
Qed.

Lemma closed_nl n t : closedn n t -> closedn n (nl t).
Proof.
  revert n t.
  eapply term_closedn_list_ind; simpl; intros; auto; solve_all.
  - now nat_compare_specs.
  - destruct X as [? [? ?]].
    rewrite /test_predicate_k. solve_all.
    simpl. now apply closed_ctx_IH.
  - red in X0. solve_all. rewrite /test_branch_k. solve_all.
    now apply closed_ctx_IH.
  - rewrite /test_def; solve_all. simpl. now len in b.
  - rewrite /test_def; solve_all. simpl. now len in b.
Qed.

Lemma closed_nlctx n t : closedn_ctx n t -> closedn_ctx n (nlctx t).
Proof.
  induction t in n |- *; simpl; auto.
  move/andb_and=> [] clt cldd.
  rewrite IHt //. len.
  move/andb_and: cldd => [] clb clt'.
  destruct a as [na [b|] ty]; cbn in *.
  - rewrite /map_decl_anon /= // /test_decl /=.
    rewrite !closed_nl //.
  - rewrite closed_nl //.
Qed.


Local Ltac ih :=
  lazymatch goal with
  | ih : forall (v : term) (napp : nat), _ -> _ -> compare_term_upto_univ_napp_rel _ _ _ _ _ _ _ _ -> ?u = _
    |- ?u = ?v =>
    eapply ih ; try eapply compare_term_upto_univ_NoTermIrrel_ctx ; eassumption
  end.

Lemma nameless_eqctx_IH ctx ctx' :
  forallb (nameless_decl nameless) ctx ->
  forallb (nameless_decl nameless) ctx' ->
  eq_context_upto_names_gen ctx ctx' ->
  ctx = ctx'.
Proof.
  solve_all.
  induction X; auto.
  all:destruct p; depelim H; depelim H0; auto; f_equal; subst; auto.
  - unfold nameless_decl in i, i0; rtoProp.
    f_equal => //.
    eapply banon_eq_binder_annot; eauto.
  - unfold nameless_decl in i, i0; rtoProp.
    f_equal => //.
    eapply banon_eq_binder_annot; eauto.
Qed.

Lemma nameless_eq_term_spec :
  forall u v napp,
    nameless u ->
    nameless v ->
    compare_term_upto_univ_napp_rel empty_global_env StrictUnivEq NoTermIrrel Conv napp [] u v ->
    u = v.
Proof.
  intros u v napp hu hv e.
  induction u in v, napp, hu, hv, e |- * using term_forall_list_ind.
  all: depelim e => //.
  all: cbn in hu, hv ; rtoProp .
  all: try solve [ f_equal ; try ih ; try assumption; try now apply banon_eq_binder_annot].
  - f_equal.
    apply All2_eq.
    solve_all.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    eapply eq_univ_make. assumption.
  - f_equal ; try solve [ ih ].
    * destruct e as [eqpar [eqinst [eqctx eqret]]].
      destruct X as [? [? ?]]. 
      destruct p, p'; simpl in *. f_equal.
      + apply All2_eq; solve_all.
      + red in eqinst. apply Forall2_eq. eapply Forall2_map_inv in eqinst.
        solve_all.
        now apply Universe.make_inj in H.
      + eapply nameless_eqctx_IH; eauto.
      + ih.
    * apply All2_eq. unfold eq_branches in e1.
      solve_all.
      destruct b0.
      destruct x, y; simpl in *; f_equal.
      + eapply nameless_eqctx_IH => //.
        -- apply All_forallb, All_impl with (1 := a0) => ? [??] //.
        -- apply All_forallb => //.
      + ih.
  - f_equal. apply All2_eq. unfold eq_mfix in e.
    solve_all.
    unfold test_def in b1, b3. rtoProp.
    destruct x, y; simpl in *; f_equal => //.
    + now apply banon_eq_binder_annot.
    + ih.
    + ih.
  - f_equal. apply All2_eq. unfold eq_mfix in e.
    solve_all.
    unfold test_def in b1, b3. rtoProp.
    destruct x, y; simpl in *; f_equal => //.
    + now apply banon_eq_binder_annot.
    + ih.
    + ih.
Qed.


Lemma nl_destArity :
  forall Γ A,
    destArity (nlctx Γ) (nl A) =
    option_map (fun '(ctx, s) => (nlctx ctx, s)) (destArity Γ A).
Proof.
  intros Γ A.
  induction A in Γ |- *.
  all: simpl in *. all:auto.
  - apply (IHA2 (Γ ,, vass na A1)).
  - apply (IHA3 (Γ ,, vdef na A1 A2)).
Qed.


Lemma global_variance_nl_sigma_mon {Σ gr napp} :
  global_variance (nl_global_env Σ) gr napp =
  global_variance Σ gr napp.
Proof.
  rewrite /global_variance /lookup_constructor /lookup_inductive /lookup_minductive.
  destruct gr as [|ind|[ind i]|] => //=.
  all: rewrite nl_lookup_env.
  all: destruct lookup_env => //=.
  all: destruct g => //=.
  all: rewrite nth_error_map.
  all: destruct nth_error => //=.
  - rewrite (nl_destArity []).
    destruct (destArity [] (ind_type o)) as [[ctx s]|] eqn:da => //=.
    now rewrite nl_context_assumptions.
  - rewrite nth_error_map.
    destruct nth_error => /= //.
Qed.

Lemma R_global_instance_nl Σ Re Rle gr napp :
  CRelationClasses.subrelation (R_global_instance Σ Re Rle gr napp)
       (R_global_instance (nl_global_env Σ) Re Rle gr napp).
Proof.
  intros t t'.
  unfold R_global_instance.
  now rewrite global_variance_nl_sigma_mon.
Qed.

Lemma eq_context_nl_IH Σ R isTermIrrel ctx ctx' :
  (forall (napp : nat) (t t' : term) (pb : conv_pb) (Γ : mark_context),
      compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ t t' ->
      compare_term_upto_univ_napp_rel (nl_global_env Σ) R isTermIrrel pb napp Γ
        (nl t) (nl t')) ->
  eq_context_upto_names_gen ctx ctx' ->
  eq_context_upto_names_gen
    (map (map_decl_anon nl) ctx)
    (map (map_decl_anon nl) ctx').
Proof.
  intros aux H.
  induction H; simpl; constructor; simpl; destruct p; simpl; 
  intuition (constructor; auto); subst; reflexivity.
Defined.

Lemma nl_eq_term_upto_univ :
  forall Σ R isTermIrrel pb napp Γ t t',
    (forall Γ t, isTermIrrel Σ Γ t -> isTermIrrel (nl_global_env Σ) Γ (nl t)) ->
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ t t' ->
    compare_term_upto_univ_napp_rel (nl_global_env Σ) R isTermIrrel pb napp Γ (nl t) (nl t').
Proof.
  intros Σ R isTermIrrel pb napp Γ t t' Hirrel h.
  induction t in t', h, napp, Γ, pb |- * using term_forall_list_ind.
  all: depelim h.
  all: try solve [ econstructor ; eauto ].
  - cbn. econstructor.
    solve_all.
  - econstructor.
    eapply R_global_instance_nl; eauto.
  - econstructor.
    eapply R_global_instance_nl; eauto.
  - cbn. econstructor; eauto.
    + red. destruct e, X; intuition auto; simpl.
      * solve_all.
      * apply eq_context_upto_names_upto_names_gen in a3.
        apply eq_context_upto_names_upto_names_gen.
        solve_all.
        destruct a0, b0. all: now constructor => //=.
      * rewrite mark_inst_case_predicate_context.
        rewrite mark_inst_case_predicate_context in b1.
        apply b => //. rewrite /= /marks_of_context map_map //.
    + unfold eq_branches in *; solve_all.
      destruct b; split; cbn.
      * apply eq_context_upto_names_upto_names_gen in e0.
        apply eq_context_upto_names_upto_names_gen.
        solve_all.
        destruct a1, b. all: now constructor => //=.
      * rewrite mark_inst_case_branch_context.
        rewrite mark_inst_case_branch_context in c0.
        apply b0 => //. rewrite /= /marks_of_context map_map //.
  - cbn. econstructor; eauto.
    unfold eq_mfix in *; solve_all.
    apply b0. rewrite /= /marks_of_context /fix_context mapi_map map_rev map_mapi /=.
    rewrite /marks_of_context /fix_context map_rev map_mapi /= // in b1.
  - cbn. econstructor; eauto.
    unfold eq_mfix in *; solve_all.
    apply b0. rewrite /= /marks_of_context /fix_context mapi_map map_rev map_mapi /=.
    rewrite /marks_of_context /fix_context map_rev map_mapi /= // in b1.
Qed.

Lemma eq_context_nl Σ R isTermIrrel pb Γ0 ctx ctx' :
  (forall Γ t, isTermIrrel Σ Γ t -> isTermIrrel (nl_global_env Σ) Γ (nl t)) ->
  eq_context_upto Σ R isTermIrrel pb Γ0 ctx ctx' ->
  eq_context_upto (nl_global_env Σ) R isTermIrrel pb Γ0
    (nlctx ctx) (nlctx ctx').
Proof.
  intros Hirr H.
  induction H; constructor; simpl; destruct p; intuition 
    (constructor; auto using nl_eq_term_upto_univ).
  all: rewrite nl_marks_of_context; auto using nl_eq_term_upto_univ.
Qed.

Lemma map_anon_dname {A B} (f : A -> B) (g : A -> B) (d : def A) :
  binder_relevance (dname d) = binder_relevance (dname (map_def_anon f g d)).
Proof. destruct d; reflexivity. Qed.

Lemma nl_isTermRel Σ Γ t rel :
  isTermRel Σ Γ t rel -> isTermRel (nl_global_env Σ) Γ (nl t) rel.
Proof.
  induction t in Γ, rel |- * using term_forall_list_ind.
  all: intro _H; depelim _H.
  all: try (rewrite H; clear H).
  all: try solve [ econstructor; eauto ].
  - apply nl_declared_constant in d.
    change (cst_relevance decl) with (cst_relevance (nl_constant_body decl)).
    constructor; tea.
  - apply nl_declared_constructor in d.
    change (ind_relevance idecl) with (ind_relevance (nl_one_inductive_body idecl)).
    econstructor; tea.
  - cbn. econstructor; eauto.
    + destruct X as (X & X' & X''), w as (H & H' & H''); unfold nl_predicate; repeat split; cbn.
      * solve_all. destruct b; eexists; eauto.
      * len. induction H'; cbn.
        1: constructor.
        all: inv X'; constructor; [eapply IHH'|]; eauto.
        all: destruct t1 as (Hb & Ht), X1 as (Xb & Xt); split; auto.
        all: rewrite /marks_of_context map_map /=; eauto.
        destruct Hb; eexists; eauto.
      * rewrite !mark_inst_case_predicate_context /marks_of_context map_map /= in H'' |- *. auto.
    + solve_all. destruct b as (Hc & rel & H).
      split.
      * rewrite /nl_predicate map_length /nl_branch /=.
        induction Hc; cbn.
        1: constructor.
        all: inv a2; constructor; [eapply IHHc|]; eauto.
        all: destruct t1 as (Hb & Ht), X as (Xb & Xt); split; auto.
        all: rewrite /marks_of_context map_map /=; eauto.
        destruct Hb; eexists; eauto.
      * eexists; rewrite !mark_inst_case_branch_context /marks_of_context map_map /= in H |- *. eauto.
  - apply nl_declared_projection in d.
    change (proj_relevance pdecl) with (proj_relevance (nl_projection_body pdecl)).
    econstructor; eauto.
  - cbn. erewrite map_anon_dname. econstructor. 1: rewrite nth_error_map e //.
    unfold wfTermRel_mfix in *; solve_all. rewrite /marks_of_context /fix_context !map_rev !map_mapi mapi_map /= in a |- *. auto.
  - cbn. erewrite map_anon_dname. econstructor. 1: rewrite nth_error_map e //.
    unfold wfTermRel_mfix in *; solve_all. rewrite /marks_of_context /fix_context !map_rev !map_mapi mapi_map /= in a |- *. auto.
Qed.

Lemma nl_compare_term {cf:checker_flags} pb Σ φ Γ t t' :
  compare_term pb Σ φ Γ t t' ->
  compare_term pb (nl_global_env Σ) φ Γ (nl t) (nl t').
Proof.
  apply nl_eq_term_upto_univ.
  intros; now apply nl_isTermRel.
Qed.

Lemma nl_leq_term {cf:checker_flags} Σ:
  forall φ Γ t t',
    leq_term Σ φ Γ t t' ->
    leq_term (nl_global_env Σ) φ Γ (nl t) (nl t').
Proof. apply nl_compare_term. Qed.

Lemma nl_eq_term {cf:checker_flags} Σ:
  forall φ Γ t t',
    eq_term Σ φ Γ t t' ->
    eq_term (nl_global_env Σ) φ Γ (nl t) (nl t').
Proof. apply nl_compare_term. Qed.

Corollary eq_term_nl_eq :
  forall u v,
    u ≡α v ->
    nl u = nl v.
Proof.
  intros u v h.
  eapply nameless_eq_term_spec.
  - eapply nl_spec.
  - eapply nl_spec.
  - instantiate (1:=0). now eapply (nl_eq_term_upto_univ empty_global_env).
Qed.

Local Ltac ih3 :=
  lazymatch goal with
  | ih : forall Rle napp v, compare_term_upto_univ_napp_rel _ _ _ _ _ _ (nl ?u) _ -> _
    |- compare_term_upto_univ_napp_rel _ _ _ _ _ _ ?u _ =>
    eapply ih ; assumption
  end.

(* Lemma eq_context_nl_inv_IH Σ R isTermIrrel ctx ctx' :
  onctx (fun u : term => forall (napp : nat) (v : term) (pb : conv_pb) (Γ : mark_context),
      compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ (nl u) (nl v) ->
      compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ u v) ctx ->
  eq_context_upto_names_gen (map (map_decl_anon nl) ctx) (map (map_decl_anon nl) ctx') ->
  eq_context_upto_names_gen ctx ctx'.
Proof.
  intros Hctx. unfold ondecl in *.
  induction ctx as [|[na [b|] ty] Γ] in ctx', Hctx |- *; 
  destruct ctx' as [|[na' [b'|] ty'] Δ]; simpl; intros H;
  depelim H; constructor; simpl in *; depelim Hctx; intuition eauto.
  * depelim c; constructor; auto. 
    + cbn in *.
  * depelim c.
  * depelim c.
  * depelim c; constructor; auto.
Qed. *)

(* Lemma eq_term_upto_univ_nl_inv :
  forall Σ R isTermIrrel pb napp Γ u v,
    (forall Γ t, isTermIrrel Σ Γ (nl t) -> isTermIrrel (nl_global_env Σ) Γ t) ->
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ (nl u) (nl v) ->
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ u v.
Proof.
  intros Σ R isTermIrrel pb napp Γ u v hirr h.
  induction u in napp, Γ, v, h, pb |- * using term_forall_list_ind.
  all: dependent destruction h.
  all: destruct v ; try discriminate.
  all: try solve [
    try lazymatch goal with
    | h : nl _ = _ |- _ =>
      simpl in h ; inversion h ; subst
    end ;
    constructor ;
    try ih3 ;
    assumption
  ].
  - cbn in H. inversion H. subst. constructor.
    apply All2_map_inv in a. solve_all.
  - cbn in H. inversion H. subst. constructor ; try ih3.
    + red. destruct e; solve_all.
      * simpl in a0. eapply All2_map_inv in a0. solve_all.
      * simpl in a4. noconf H.
        eapply eq_context_nl_IH; tea.
    + apply All2_map_inv in a. solve_all.
      eapply eq_context_nl_IH; tea.
  - cbn in H. inversion H. subst. constructor ; try ih3.
    apply All2_map_inv in a. solve_all.
  - cbn in H. inversion H. subst. constructor ; try ih3.
    apply All2_map_inv in a. solve_all.
Qed. *)

Lemma nl_isTermIrrel_inv Σ Γ t rel :
  isTermRel Σ Γ (nl t) rel -> isTermRel (nl_global_env Σ) Γ t rel.
Proof.
  induction t in Γ, rel |- * using term_forall_list_ind.
  all: intro _H; depelim _H.
  all: try (rewrite H; clear H).
  all: try solve [ econstructor; eauto ].
  - apply nl_declared_constant in d.
    change (cst_relevance decl) with (cst_relevance (nl_constant_body decl)).
    constructor; tea.
  - apply nl_declared_constructor in d.
    change (ind_relevance idecl) with (ind_relevance (nl_one_inductive_body idecl)).
    econstructor; tea.
  - cbn. econstructor; eauto.
    + destruct X as (X & X' & X''), w as (H & H' & H''); unfold nl_predicate in *; repeat split; cbn in *.
      * solve_all. destruct b; eexists; eauto.
      * len in H'. clear -H' X'.
        induction (pcontext p) as [|[na [b|] T] ctx IH] in H', X' |- *; cbn.
        1: constructor.
        all: inv X'; inv H'; constructor; [eapply IH|]; eauto.
        all: destruct X2 as (Hb & Ht), X as (Xb & Xt); split; auto.
        all: rewrite /marks_of_context map_map /= in Hb, Ht; eauto.
        destruct Hb; eexists; eauto.
      * rewrite !mark_inst_case_predicate_context /marks_of_context map_map /= in H'' |- *. auto.
    + solve_all. destruct b as (Hc & rel & H).
      split.
      * rewrite /nl_predicate map_length /nl_branch /= in Hc.
        clear -Hc a2.
        induction (bcontext x) as [|[na [b|] T] ctx IH] in Hc, a2 |- *; cbn.
        1: constructor.
        all: inv a2; inv Hc; constructor; [eapply IH|]; eauto.
        all: destruct X2 as (Hb & Ht), X as (Xb & Xt); split; auto.
        all: rewrite /marks_of_context map_map /= in Hb, Ht; eauto.
        destruct Hb; eexists; eauto.
      * eexists; rewrite !mark_inst_case_branch_context /marks_of_context map_map /= in H |- *. eauto.
  - apply nl_declared_projection in d.
    change (proj_relevance pdecl) with (proj_relevance (nl_projection_body pdecl)).
    econstructor; eauto.
  - cbn. rewrite nth_error_map in e.
    destruct nth_error eqn:H => //.
    simpl in e. inv e. simpl. econstructor; tea.
    rewrite /marks_of_context /fix_context !map_rev !map_mapi mapi_map /= in w |- *.
    unfold wfTermRel_mfix in *; solve_all.
  - cbn. rewrite nth_error_map in e.
    destruct nth_error eqn:H => //.
    simpl in e. inv e. simpl. econstructor; tea.
    rewrite /marks_of_context /fix_context !map_rev !map_mapi mapi_map /= in w |- *.
    unfold wfTermRel_mfix in *; solve_all.
Qed.


(* Lemma eq_term_upto_univ_tm_nl :
  forall Σ R isTermIrrel pb napp Γ u,
    Reflexive (R Conv) ->
    Reflexive (R pb) ->
    compare_term_upto_univ_napp_rel Σ R isTermIrrel pb napp Γ u (nl u).
Proof.
  intros Σ R isTermIrrel pb napp Γ u hRe hRle.
  induction u in napp, Γ, pb, hRle |- * using term_forall_list_ind.
  all: try solve [
    cbnr ; auto ; constructor ; eauto
  ].
  - simpl. constructor.
    solve_all.
  - simpl. destruct p. constructor ; eauto.
    * destruct X; red; simpl in *; intuition auto.
      + solve_all.
      + reflexivity.
      + clear -a0 hRe hRle. induction a0.
        { constructor; auto. }
        destruct x as [na [b|] ty]; simpl; constructor; auto; 
          destruct p; simpl in *; intuition (simpl; auto);
          constructor; auto.
    * induction l.
      + constructor.
      + simpl. depelim X0. destruct p.
        simpl in *. repeat constructor.
        ++ simpl.
          clear -hRe hRle a0.
          induction a0; [constructor; auto|].
          destruct x as [na [b|] ty]; simpl; constructor; auto; 
          destruct p; simpl in *; intuition auto; constructor; auto.
        ++ auto.
        ++ eapply IHl. assumption.
  - simpl. constructor. induction m.
    + constructor.
    + simpl. inversion X. subst. constructor ; auto.
      repeat split ; auto.
      all: apply X0 ; eauto.
  - simpl. constructor. induction m.
    + constructor.
    + simpl. inversion X. subst. constructor ; auto.
      repeat split ; auto.
      all: apply X0 ; eauto.
Qed. *)

(* Corollary eq_term_tm_nl :
  forall `{checker_flags} Σ G u, eq_term Σ G u (nl u).
Proof.
  intros flags Σ G u.
  eapply eq_term_upto_univ_tm_nl.
  - intro. eapply eq_universe_refl.
  - intro. eapply eq_universe_refl.
Qed. *)


Lemma nl_eq_decl {cf:checker_flags} :
  forall pb Σ φ Γ d d',
    compare_decl pb Σ φ Γ d d' ->
    compare_decl pb (nl_global_env Σ) φ Γ (map_decl nl d) (map_decl nl d').
Proof.
  intros pb Σ φ Γ d d' []; constructor;
  intuition auto using nl_compare_term.
Qed.

Lemma nl_eq_decl' {cf:checker_flags} :
  forall pb Σ φ Γ d d',
    compare_decl pb Σ φ Γ d d' ->
    compare_decl pb (nl_global_env Σ) φ Γ (map_decl_anon nl d) (map_decl_anon nl d').
Proof.
  intros pb Σ φ Γ d d' []; constructor;
  intuition auto using nl_compare_term.
Qed.

Lemma nl_eq_context {cf:checker_flags} :
  forall pb Σ φ Γ0 Γ Γ',
    compare_context pb Σ φ Γ0 Γ Γ' ->
    compare_context pb (nl_global_env Σ) φ Γ0 (nlctx Γ) (nlctx Γ').
Proof.
  intros pb Σ φ Γ0 Γ Γ' h.
  unfold eq_context, nlctx.
  eapply eq_context_nl; tea.
  intros; now apply nl_isTermRel.
Qed.

Lemma nl_red1 :
  forall Σ Γ M N,
    red1 Σ Γ M N ->
    red1 (nl_global_env Σ) (nlctx Γ) (nl M) (nl N).
Proof.
  intros Σ Γ M N h.
  induction h using red1_ind_all.
  all: simpl.
  all: rewrite ?nl_lift ?nl_subst ?nl_subst_instance.
  all: try solve [ econstructor ; eauto ].
  - constructor; eauto. apply nl_isTermRel; rewrite nl_marks_of_context //.
  - constructor. unfold nlctx. rewrite nth_error_map.
    destruct (nth_error Γ i). 2: discriminate.
    cbn in *. apply some_inj in H. rewrite H. reflexivity.
  - rewrite nl_mkApps. cbn.
    rewrite map_rev map_skipn nl_extended_subst nl_lift.
    rewrite -(nl_context_assumptions (inst_case_branch_context p br)).
    change (nl (bbody br)) with (bbody (nl_branch nl br)).
    rewrite -(nlctx_length (inst_case_branch_context p br)).
    change (subst0 (extended_subst (nlctx (inst_case_branch_context p br)) 0)
    (lift (context_assumptions (nlctx (inst_case_branch_context p br))) #|
       nlctx (inst_case_branch_context p br)| (bbody (nl_branch nl br)))) with
     (expand_lets (nlctx (inst_case_branch_context p br)) (bbody (nl_branch nl br))).
    epose proof (nth_error_map (nl_branch nl) c brs).
    rewrite /inst_case_branch_context.
    rewrite nl_inst_case_context.
    change (map nl (pparams p)) with (pparams (nl_predicate nl p)).
    change (nlctx (bcontext br)) with (bcontext (nl_branch nl br)).
    rewrite -/(inst_case_branch_context _ _).
    eapply red_iota => //.
    * apply nl_isTermRel in X; rewrite nl_marks_of_context //.
    * rewrite H1 H //.
    * rewrite nl_context_assumptions; len; eauto.
  - rewrite !nl_mkApps. cbn. eapply red_fix with (narg:=narg).
    + unfold unfold_fix in *. rewrite nth_error_map.
      destruct (nth_error mfix idx). 2: discriminate.
      cbn.
      replace (isLambda (nl (dbody d))) with (isLambda (dbody d))
        by (destruct (dbody d) ; reflexivity).
      inversion H. subst. rewrite nl_subst.
      repeat f_equal. clear.
      unfold fix_subst. rewrite map_length.
      induction #|mfix|.
      * reflexivity.
      * cbn. rewrite IHn. reflexivity.
    + unfold is_constructor in *.
      rewrite nth_error_map. destruct (nth_error args narg) ; [| discriminate ].
      cbn. unfold isConstruct_app in *. rewrite nl_decompose_app.
      destruct (decompose_app t) as [u ?].
      destruct u. all: try discriminate.
      reflexivity.
  - rewrite !nl_mkApps. simpl. eapply red_cofix_case with (narg := narg).
    unfold unfold_cofix in *. rewrite nth_error_map.
    destruct (nth_error mfix idx). 2: discriminate.
    cbn.
    inversion H. subst. rewrite nl_subst.
    repeat f_equal. clear.
    unfold cofix_subst. rewrite map_length.
    induction #|mfix|.
    * reflexivity.
    * cbn. rewrite IHn. reflexivity.
  - rewrite !nl_mkApps. simpl. eapply red_cofix_proj with (narg := narg).
    unfold unfold_cofix in *. rewrite nth_error_map.
    destruct (nth_error mfix idx). 2: discriminate.
    cbn.
    inversion H. subst. rewrite nl_subst.
    repeat f_equal. clear.
    unfold cofix_subst. rewrite map_length.
    induction #|mfix|.
    * reflexivity.
    * cbn. rewrite IHn. reflexivity.
  - econstructor.
    + unfold declared_constant in *.
      rewrite nl_lookup_env H. reflexivity.
    + destruct decl as [? [?|] ?].
      all: cbn in *.
      * f_equal. f_equal. congruence.
      * discriminate.
  - rewrite nl_mkApps. cbn. constructor.
    rewrite nth_error_map H. reflexivity.
  - rewrite nl_pred_set_pparams.
    econstructor; tea.
    eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    solve_all.
  - rewrite nl_pred_set_preturn. econstructor.
    rewrite /inst_case_predicate_context -nl_inst_case_context.
    rewrite -nlctx_app_context. apply IHh.
  - econstructor; tea.
    simpl.
    eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [? ?]; cbn; solve_all.
    red; simpl. solve_all.
    rewrite /inst_case_branch_context /= -nl_inst_case_context.
    now rewrite -nlctx_app_context.
  - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [? ?]; auto.
  - constructor. apply OnOne2_map. eapply OnOne2_impl; [eassumption|].
    cbn. intros x y [? ?]; auto. red; simpl; intuition auto. congruence.
  - apply fix_red_body. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split.
    + rewrite nlctx_app_context nl_fix_context in r0. assumption.
    + cbn. congruence.
  - constructor. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split. 1: assumption.
    cbn. congruence.
  - apply cofix_red_body. eapply OnOne2_map, OnOne2_impl. 1: eassumption.
    cbn. intros x y [[? ?] ?]. split.
    + rewrite nlctx_app_context nl_fix_context in r0. assumption.
    + cbn. congruence.
Qed.

Lemma nl_cumul_pb {cf:checker_flags} :
  forall pb Σ Γ A B,
    Σ ;;; Γ |- A <=[pb] B ->
    nlg Σ ;;; nlctx Γ |- nl A <=[pb] nl B.
Proof.
  intros pb [Σ univs] Γ A B h => /=.
  induction h.
  - constructor.
    apply nl_compare_term.
    rewrite nl_marks_of_context.
    assumption.
  - eapply cumul_red_l. 2: eassumption.
    apply nl_red1. assumption.
  - eapply cumul_red_r. 1: eassumption.
    apply nl_red1. assumption.
Qed.

Lemma nl_conv {cf:checker_flags} :
  forall Σ Γ A B,
    Σ ;;; Γ |- A = B ->
    nlg Σ ;;; nlctx Γ |- nl A = nl B.
Proof. apply nl_cumul_pb. Qed.

Lemma nl_cumul {cf:checker_flags} :
  forall Σ Γ A B,
    Σ ;;; Γ |- A <= B ->
    nlg Σ ;;; nlctx Γ |- nl A <= nl B.
Proof. apply nl_cumul_pb. Qed.


Notation nldecl := (map_decl_anon nl).

Lemma nl_cumul_pb_decls {cf} {pb Σ Γ Γ'} {d d'} :
  cumul_pb_decls cumulAlgo_gen pb Σ Γ Γ' d d' ->
  cumul_pb_decls cumulAlgo_gen pb (nlg Σ) (nlctx Γ) (nlctx Γ') (nldecl d) (nldecl d').
Proof.
  intros Hd; depelim Hd; constructor; tas;
    eapply nl_cumul_pb; tea.
Qed.

Lemma nl_conv_decls {cf} {Σ Γ Γ'} {d d'} :
  conv_decls cumulAlgo_gen Σ Γ Γ' d d' ->
  conv_decls cumulAlgo_gen (nlg Σ) (nlctx Γ) (nlctx Γ') (nldecl d) (nldecl d').
Proof. apply nl_cumul_pb_decls. Qed.

Lemma nl_cumul_decls {cf} {Σ Γ Γ' d d'} :
   cumul_decls cumulAlgo_gen Σ Γ Γ' d d' ->
   cumul_decls cumulAlgo_gen (nlg Σ) (nlctx Γ) (nlctx Γ') (nldecl d) (nldecl d').
Proof. apply nl_cumul_pb_decls. Qed.

Lemma nl_cumul_pb_ctx {cf} {pb Σ Γ Δ} :
  cumul_pb_context cumulAlgo_gen pb Σ Γ Δ ->
  cumul_pb_context cumulAlgo_gen pb (nlg Σ) (nlctx Γ) (nlctx Δ).
Proof.
  intros.
  induction X; simpl; constructor; eauto; simpl; now eapply nl_cumul_pb_decls in p.
Qed.
#[global] Hint Resolve nl_cumul_pb_ctx : nl.

Lemma nl_conv_ctx {cf} {Σ Γ Δ} :
  conv_context cumulAlgo_gen Σ Γ Δ ->
  conv_context cumulAlgo_gen (nlg Σ) (nlctx Γ) (nlctx Δ).
Proof. apply nl_cumul_pb_ctx. Qed.

Lemma nl_cumul_ctx {cf} {Σ Γ Δ} :
  cumul_context cumulAlgo_gen Σ Γ Δ ->
  cumul_context cumulAlgo_gen (nlg Σ) (nlctx Γ) (nlctx Δ).
Proof. apply nl_cumul_pb_ctx. Qed.

Lemma nl_global_levels Σ : global_levels (nl_global_env Σ) = global_levels Σ.
Proof.
  induction Σ; simpl; auto.
Qed.

Lemma nl_global_ext_levels Σ :
  LevelSet.Equal (global_ext_levels (nlg Σ)) (global_ext_levels Σ).
Proof.
  destruct Σ as [Σ univ].
  unfold global_ext_levels; simpl.
  intros x; reflexivity.
Qed.


Lemma All2i_map {A B C D} (f : A -> B) (g : C -> D) P n l l' : 
  All2i (fun i x y => P i (f x) (g y)) n l l' <~>
  All2i P n (map f l) (map g l').
Proof.
  split.
  - induction 1; constructor; auto.
  - induction l in n, l' |- *; destruct l'; intros H; depelim H; constructor; auto.
Qed.

Lemma nl_is_allowed_elimination {cf:checker_flags} (Σ : global_env_ext) ps kelim :
  is_allowed_elimination Σ kelim ps ->
  is_allowed_elimination (nlg Σ) kelim ps.
Proof.
  now rewrite global_ext_constraints_nlg.
Qed.


(* Corollary reflect_nleq_term : *)
(*   forall t t', *)
(*     reflect (nl t = nl t') (nleq_term t t'). *)
(* Proof. *)
(*   intros t t'. *)
(*   destruct (reflect_upto_names t t'). *)
(*   - constructor. eapply eq_term_nl_eq. assumption. *)
(*   - constructor. intro bot. apply f. *)
(*     apply eq_term_upto_univ_nl_inv. *)
(*     rewrite bot. *)
(*     apply eq_term_upto_univ_refl. *)
(*     all: auto. *)
(* Qed. *)

(* Lemma nleq_term_it_mkLambda_or_LetIn : *)
(*   forall Γ u v, *)
(*     nleq_term u v -> *)
(*     nleq_term (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v). *)
(* Proof. *)
(*   intros Γ u v h. *)
(*   induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *. *)
(*   - assumption. *)
(*   - simpl. cbn. apply ih. *)
(*     eapply ssrbool.introT. *)
(*     + eapply reflect_nleq_term. *)
(*     + cbn. f_equal. *)
(*       eapply ssrbool.elimT. *)
(*       * eapply reflect_nleq_term. *)
(*       * assumption. *)
(*   - simpl. cbn. apply ih. *)
(*     eapply ssrbool.introT. *)
(*     + eapply reflect_nleq_term. *)
(*     + cbn. f_equal. *)
(*       eapply ssrbool.elimT. *)
(*       * eapply reflect_nleq_term. *)
(*       * assumption. *)
(* Qed. *)

Lemma anonymize_two na : anonymize (anonymize na) = anonymize na.
Proof.
  destruct na; simpl; reflexivity.
Qed.

Lemma nl_two M :
  nl (nl M) = nl M.
Proof.
  induction M using term_forall_list_ind; cbnr.
  all: rewrite ?IHM1 ?IHM2 ?IHM3 ?IHM; cbnr.
  - f_equal. induction X; cbnr. congruence.
  - destruct X; cbnr.
    f_equal; solve_all.
    * unfold nl_predicate; cbn; f_equal; solve_all.
      unfold ondecl in *; solve_all.
      unfold nldecl; destruct x as [na [bod|] ty]; simpl in *; f_equal; auto.
      f_equal; eauto.
    * unfold nl_branch; destruct x; cbn. f_equal; auto.
      unfold ondecl in *; solve_all.
      unfold nldecl; destruct x as [na [bod|] ty]; simpl; f_equal; auto.
      f_equal; eauto.
  - f_equal. induction X; cbnr. f_equal; tas.
    destruct p, x; unfold map_def_anon; simpl in *.
    rewrite anonymize_two; congruence.
  - f_equal. induction X; cbnr. f_equal; tas.
    destruct p, x; unfold map_def_anon; simpl in *. 
    rewrite anonymize_two; congruence.
Qed.


Local Ltac aa :=
  match goal with
  | |- ∑ _ : _, _ × ?t = _ => exists t
  end; split; [|symmetry; apply nl_two]; simpl;
  rewrite ?nl_lift ?nl_subst ?nl_subst_instance.

Local Ltac bb :=
  repeat match goal with
  | H : ∑ _ : _, _ × ?t = _ |- _ => destruct H as [? [? ?]]
  end;
  eexists; split.

Local Ltac bb' := bb; [econstructor|]; tea; cbn.

Arguments on_snd {_ _ _} _ _/.
Arguments map_def_anon {_ _} _ _ _/.
