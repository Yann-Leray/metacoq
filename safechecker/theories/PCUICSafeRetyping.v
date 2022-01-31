(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool Utf8.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

From Coq Require Import Bool String List Program.
From MetaCoq.Template Require Import config monad_utils utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICArities PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv
     PCUICWeakeningEnvConv PCUICWeakeningEnvTyp 
     PCUICReduction
     PCUICWeakeningConv PCUICWeakeningTyp 
     PCUICClosed PCUICClosedTyp
     PCUICSafeLemmata PCUICSubstitution PCUICValidity
     PCUICGeneration PCUICInversion PCUICValidity PCUICInductives PCUICInductiveInversion PCUICReduction
     PCUICSpine PCUICSR PCUICCumulativity PCUICConversion PCUICConfluence PCUICArities
     PCUICContexts PCUICContextConversion PCUICContextConversionTyp PCUICOnFreeVars
     PCUICWellScopedCumulativity PCUICSafeLemmata PCUICSN PCUICConvCumInversion.

From MetaCoq.PCUIC Require Import BDTyping BDToPCUIC BDFromPCUIC BDUnique.

From MetaCoq.SafeChecker Require Import PCUICErrors PCUICSafeReduce PCUICWfEnv.

(** Allow reduction to run inside Coq *)
Transparent Acc_intro_generator.

Local Open Scope string_scope.
Set Asymmetric Patterns.
Import monad_utils.MCMonadNotation.

#[global]
Hint Constructors assumption_context : pcuic.

Derive NoConfusion for type_error.

Set Equations With UIP.
Set Equations Transparent.

Add Search Blacklist "_graph_mut".
Add Search Blacklist "obligation".

Require Import ssreflect.

Lemma into_equality_terms_Algo {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ l l'} : 
  All2 (convAlgo Σ Γ) l l' ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) l ->
  forallb (is_open_term Γ) l' ->
  equality_terms Σ Γ l l'.
Proof.
  solve_all.
  now eapply into_equality.
Qed.

Lemma on_free_vars_ind_predicate_context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {ind mdecl idecl} :
  declared_inductive Σ ind mdecl idecl → 
  on_free_vars_ctx (closedP (context_assumptions (ind_params mdecl)) xpredT) 
    (ind_predicate_context ind mdecl idecl).
Proof.
  intros decli.
  rewrite <- closedn_ctx_on_free_vars.
  eapply closed_ind_predicate_context; tea.
  eapply (declared_minductive_closed decli).
Qed.

Inductive wellinferred {cf: checker_flags} Σ Γ t : Prop :=
  | iswellinferred T : Σ ;;; Γ |- t ▹ T -> wellinferred Σ Γ t.

Definition well_sorted {cf:checker_flags} Σ Γ T := 
  ∥ ∑ u, Σ ;;; Γ |- T ▹□ u ∥.

Lemma well_sorted_wellinferred {cf:checker_flags} {Σ Γ T} :
  well_sorted Σ Γ T -> wellinferred Σ Γ T.
Proof.
  intros [[s []]].
  now econstructor.
Qed.

Coercion well_sorted_wellinferred : well_sorted >-> wellinferred.

Lemma spine_subst_smash_inv {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} 
  {Γ inst Δ s} :
  wf_local Σ (Γ ,,, Δ) ->
  spine_subst Σ Γ inst s (smash_context [] Δ) ->
  ∑ s', spine_subst Σ Γ inst s' Δ.
Proof.
  intros wf.
  move/spine_subst_ctx_inst.
  intros c. eapply ctx_inst_smash in c.
  unshelve epose proof (ctx_inst_spine_subst _ c); auto.
  now eexists.
Qed.

(** Smashed variant that is easier to use *)
Lemma inductive_cumulative_indices_smash {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} :
  forall {ind mdecl idecl u u' napp},
  declared_inductive Σ ind mdecl idecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  PCUICEquality.R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) napp u u' ->
  forall Γ pars pars',
  spine_subst Σ Γ pars (List.rev pars) (smash_context [] (subst_instance u (ind_params mdecl))) ->
  spine_subst Σ Γ pars' (List.rev pars') (smash_context [] (subst_instance u' (ind_params mdecl))) ->  
  equality_terms Σ Γ pars pars' ->
  let indctx := idecl.(ind_indices)@[u] in
  let indctx' := idecl.(ind_indices)@[u'] in
  let pindctx := subst_context_let_expand (List.rev pars) (ind_params mdecl)@[u] (smash_context [] indctx) in
  let pindctx' := subst_context_let_expand (List.rev pars') (ind_params mdecl)@[u'] (smash_context [] indctx') in
  context_equality_rel true Σ Γ pindctx pindctx'.
Proof.
  intros ind mdecl idecl u u' napp isdecl up cu cu' hR Γ pars pars' sppars sppars' eq.
  unshelve epose proof (spine_subst_smash_inv _ sppars) as [parsubst sppars2].
  eapply weaken_wf_local; tea. apply sppars.
  eapply (on_minductive_wf_params isdecl cu).
  unshelve epose proof (spine_subst_smash_inv _ sppars') as [parsubst' sppars3].
  eapply weaken_wf_local; tea. apply sppars.
  eapply (on_minductive_wf_params isdecl cu').
  epose proof (inductive_cumulative_indices isdecl cu cu' hR Γ pars pars' _ _ sppars2 sppars3 eq).
  intros.
  cbn in X.
  rewrite (spine_subst_inst_subst sppars2) in X.
  rewrite (spine_subst_inst_subst sppars3) in X.
  rewrite /pindctx /pindctx'.
  rewrite - !smash_context_subst_context_let_expand.
  apply X.
Qed.

(** * Retyping

  The [infer] function provides a fast (and loose) type inference
  function which assumes that the provided term is already well-typed in
  the given context and recomputes its type. Only reduction (for
  head-reducing types to uncover dependent products or inductives) and
  substitution are costly here. No universe checking or conversion is done
  in particular. *)

Section TypeOf.
  Context {cf : checker_flags} {nor : normalizing_flags}.

  Context {Σ_type : wf_env_impl} {Σ : Σ_type.π1}.

  Local Definition gΣ := wf_env_env Σ. 
  Local Definition heΣ : ∥ wf_ext gΣ ∥ := wf_env_wf Σ.

  Local Definition G : universes_graph := wf_env_graph Σ.
  Local Definition HG : is_graph_of_uctx G (global_ext_uctx gΣ) := wf_env_graph_wf Σ.

  Local Definition hΣ : ∥ wf gΣ ∥ := map_squash (wf_ext_wf _) heΣ.

  Definition on_subterm P Pty Γ t : Type := 
  match t with
  | tProd na t b => Pty Γ t * Pty (Γ ,, vass na t) b
  | tLetIn na d t t' => 
    Pty Γ t * P Γ d * P (Γ ,, vdef na d t) t'
  | tLambda na t b => Pty Γ t * P (Γ ,, vass na t) b
  | _ => True
  end.

Lemma welltyped_subterm {Γ t} :
  wellinferred gΣ Γ t -> on_subterm (wellinferred gΣ) (well_sorted gΣ) Γ t.
Proof.
  destruct t; simpl; auto; intros [T HT]; sq.
  now inversion HT ; auto; split; do 2 econstructor.
  now inversion HT ; auto; split; econstructor ; [econstructor|..].
  now inversion HT ; inversion X0 ; auto;
    split; [split|]; econstructor ; [econstructor|..].
Qed.

  #[local] Notation ret t := (t; _).

  #[local] Definition principal_type Γ t := 
    ∑ T : term, ∥ gΣ ;;; Γ |- t ▹ T ∥.
  #[local] Definition principal_sort Γ T := 
    ∑ u, ∥ gΣ ;;; Γ |- T ▹□ u ∥.
  #[local] Definition principal_type_type {Γ t} (wt : principal_type Γ t) : term
    := projT1 wt.
  #[local] Definition principal_sort_sort {Γ T} (ps : principal_sort Γ T) : Universe.t
    := projT1 ps.
  #[local] Coercion principal_type_type : principal_type >-> term.
  #[local] Coercion principal_sort_sort : principal_sort >-> Universe.t.

  Program Definition infer_as_sort {Γ T}
    (wfΓ : ∥ wf_local gΣ Γ ∥)
    (wf : well_sorted gΣ Γ T)
    (tx : principal_type Γ T) : principal_sort Γ T :=
    match @reduce_to_sort cf nor _ Σ Γ tx _ with
    | Checked_comp (u;_) => (u;_)
    | TypeError_comp e _ => !
    end.
  Next Obligation.
    destruct tx ; cbn in *.
    destruct wf as [[]], hΣ as [wΣ].
    sq.
    eapply infering_typing, validity in s as []; eauto.
    now eexists.
  Defined.
  Next Obligation.
    clear Heq_anonymous.
    destruct tx.
    cbn in *.
    sq.
    econstructor ; tea.
    now apply closed_red_red.
  Qed.
  Next Obligation.
    clear Heq_anonymous.
    destruct tx.
    cbn in *.
    sq.
    destruct wf as [[? i]], hΣ as [wΣ].
    eapply infering_sort_infering in i ; eauto.
  Qed.

  Program Definition infer_as_prod Γ T
    (wfΓ : ∥ wf_local gΣ Γ ∥)
    (wf : welltyped gΣ Γ T)
    (isprod : ∥ ∑ na A B, red gΣ Γ T (tProd na A B) ∥) : 
    ∑ na' A' B', ∥ gΣ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥ :=
    match @reduce_to_prod cf nor _ Σ Γ T wf with
    | Checked_comp p => p
    | TypeError_comp e _ => !
    end.
    Next Obligation.
      clear Heq_anonymous. pose hΣ.
      sq.
      destruct isprod as (?&?&?&?).
      apply wildcard'.
      do 3 eexists.
      sq.
      eapply into_closed_red ; tea.
      1: fvs.
      destruct wf.
      now eapply subject_is_open_term.
    Qed.
    
  Equations lookup_ind_decl ind : typing_result
        (∑ decl body, declared_inductive (fst gΣ) ind decl body) :=
  lookup_ind_decl ind with inspect (lookup_env (fst gΣ) ind.(inductive_mind)) :=
    { | exist (Some (InductiveDecl decl)) look with inspect (nth_error decl.(ind_bodies) ind.(inductive_ind)) :=
      { | exist (Some body) eqnth => Checked (decl; body; _);
        | exist None _ => raise (UndeclaredInductive ind) };
      | _ => raise (UndeclaredInductive ind) }.
  Next Obligation.
    split.
    - symmetry in look.
      etransitivity. eassumption. reflexivity.
    - now symmetry.
  Defined.

  Lemma lookup_ind_decl_complete ind e : lookup_ind_decl ind = TypeError e -> 
    ((∑ mdecl idecl, declared_inductive gΣ ind mdecl idecl) -> False).
  Proof.
    apply_funelim (lookup_ind_decl ind).
    1-2:intros * _ her [mdecl [idecl [declm decli]]];
    red in declm; rewrite declm in e0; congruence.
    1-2:intros * _ _ => // => _ [mdecl [idecl [declm /= decli]]].
    red in declm. rewrite declm in look. noconf look.
    congruence.
  Qed.
  
  Obligation Tactic := intros ;
    try match goal with
      | infer : context [wellinferred _ _ _ -> principal_type _ _ ],
        wt : wellinferred _ _ _ |- _ =>
        try clear infer ; destruct wt as [T HT]
    end.


  Equations infer (Γ : context) (wfΓ : ∥ wf_local gΣ Γ ∥) (t : term) (wt : wellinferred gΣ Γ t) :
    principal_type Γ t
    by struct t :=
   infer Γ wfΓ (tRel n) wt with 
    inspect (option_map (lift0 (S n) ∘ decl_type) (nth_error Γ n)) := 
    { | exist None _ => !;
      | exist (Some t) _ => ret t };
    
    infer Γ wfΓ (tVar n) wt := !;
    infer Γ wfΓ (tEvar ev args) wt := !;

    infer Γ wfΓ (tSort s) wt := ret (tSort (Universe.super s));

    infer Γ wfΓ (tProd n ty b) wt :=
      let wfΓ' : ∥ wf_local gΣ (Γ ,, vass n ty) ∥ := _ in
      let ty1 := infer Γ wfΓ ty (welltyped_subterm wt).1 in
      let s1 := infer_as_sort wfΓ (welltyped_subterm wt).1 ty1 in
      let ty2 := infer (Γ ,, vass n ty) wfΓ' b (welltyped_subterm wt).2 in
      let s2 := infer_as_sort wfΓ' (welltyped_subterm wt).2 ty2 in
      ret (tSort (Universe.sort_of_product s1 s2));

    infer Γ wfΓ (tLambda n t b) wt :=
      let t2 := infer (Γ ,, vass n t) _ b (welltyped_subterm wt).2 in
      ret (tProd n t t2);

    infer Γ wfΓ (tLetIn n b b_ty b') wt :=
      let b'_ty := infer (Γ ,, vdef n b b_ty) _ b' (welltyped_subterm wt).2 in
      ret (tLetIn n b b_ty b'_ty);

    infer Γ wfΓ (tApp t a) wt :=
      let ty := infer Γ wfΓ t _ in
      let pi := infer_as_prod Γ ty wfΓ _ _ in
      ret (subst10 a pi.π2.π2.π1);

    infer Γ wfΓ (tConst cst u) wt with inspect (wf_env_lookup Σ cst) :=
      { | exist (Some (ConstantDecl d)) _ := ret (subst_instance u d.(cst_type));
        |  _ := ! };

    infer Γ wfΓ (tInd ind u) wt with inspect (lookup_ind_decl ind) :=
      { | exist (Checked decl) _ := ret (subst_instance u decl.π2.π1.(ind_type));
        | exist (TypeError e) _ := ! };
    
    infer Γ wfΓ (tConstruct ind k u) wt with inspect (lookup_ind_decl ind) :=
      { | exist (Checked decl) _ with inspect (nth_error decl.π2.π1.(ind_ctors) k) := 
        { | exist (Some cdecl) _ => ret (type_of_constructor decl.π1 cdecl (ind, k) u);
          | exist None _ => ! };
      | exist (TypeError e) _ => ! };

    infer Γ wfΓ (tCase ci p c brs) wt
      with inspect (reduce_to_ind Γ (infer Γ wfΓ c _) _) :=
      { | exist (Checked_comp indargs) _ =>
          let ptm := it_mkLambda_or_LetIn (inst_case_predicate_context p) p.(preturn) in
          ret (mkApps ptm (List.skipn ci.(ci_npar) indargs.π2.π2.π1 ++ [c]));
        | exist (TypeError_comp _ _) _ => ! };

    infer Γ wfΓ (tProj (ind, n, k) c) wt with inspect (@lookup_ind_decl ind) :=
      { | exist (Checked d) _ with inspect (nth_error d.π2.π1.(ind_projs) k) :=
        { | exist (Some pdecl) _ with inspect (reduce_to_ind Γ (infer Γ wfΓ c _) _) :=
          { | exist (Checked_comp indargs) _ => 
              let ty := snd pdecl in
              ret (subst0 (c :: List.rev (indargs.π2.π2.π1)) (subst_instance indargs.π2.π1 ty));
            | exist (TypeError_comp _ _) _ => ! };
         | exist None _ => ! };
        | exist (TypeError e) _ => ! };

    infer Γ wfΓ (tFix mfix n) wt with inspect (nth_error mfix n) :=
      { | exist (Some f) _ => ret f.(dtype);
        | exist None _ => ! };

    infer Γ wfΓ (tCoFix mfix n) wt with inspect (nth_error mfix n) :=
      { | exist (Some f) _ => ret f.(dtype);
        | exist None _ => ! };

    infer Γ wfΓ (tPrim p) wt := !.

  Next Obligation.
    sq.
    destruct (nth_error Γ n) eqn:hnth => //.
    noconf e.
    now constructor.
  Qed.
  Next Obligation.
    inversion HT ; subst.
    rewrite H0 in e => //.
  Qed.

  Next Obligation.
    now inversion HT.
  Qed.

  Next Obligation.
    now inversion HT.
  Qed.

  Next Obligation.
    now inversion HT.
  Qed.

  Next Obligation.
    pose hΣ. sq.
    constructor ; tea.
    inversion HT ; subst.
    now eapply infering_sort_isType.
  Qed.
  Next Obligation.
    case s1, s2.
    sq.
    now constructor.
  Defined.

  Next Obligation.
    pose hΣ. sq.
    inversion HT ; subst.
    constructor ; tea.
    now eapply infering_sort_isType.
  Qed.
  Next Obligation.
    case t2 as [].
    sq.
    inversion HT ; subst.
    now econstructor.
  Defined.

  Next Obligation.
    pose hΣ. sq.
    inversion HT ; subst.
    constructor ; tea.
    1: now eapply infering_sort_isType.
    apply checking_typing ; eauto.
    now eapply infering_sort_isType.
  Qed.
  Next Obligation.
   case b'_ty as [].
    sq.
    inversion HT ; subst.
    now econstructor.
  Defined.

  Next Obligation.
    sq.
    inversion HT ; subst.
    inversion X.
    now econstructor.
  Qed.
  Next Obligation.
    case ty as [].
    apply wat_welltyped ; tea.
    pose hΣ. sq.
    eapply validity, infering_typing ; eauto.
  Defined.
  Next Obligation.
    case ty as [].
    pose hΣ. sq.
    inversion HT ; subst.
    eapply infering_prod_infering in X as (?&?&[]); eauto.
    do 3 eexists.
    now apply closed_red_red.
  Defined.
  Next Obligation.
    case pi as (?&?&[]).
    case ty as [].
    cbn in *.
    pose hΣ. sq.
    inversion HT ; subst.
    inversion X0 ; subst.
    move: (X) => tyt.
    apply infering_prod_typing, validity, isType_tProd in tyt as [] ; eauto.
    eapply infering_prod_prod in X as (?&?&[]).
    4: econstructor.
    2-4: eauto.
    2: now apply closed_red_red.
    econstructor.
    1: econstructor ; tea.
    1: now apply closed_red_red.
    econstructor ; tea.
    eapply equality_forget_cumul.
    etransitivity.
    - eapply into_equality ; tea.
      1,3: fvs.
      now eapply type_is_open_term, infering_typing.
    - etransitivity.
      1: now eapply red_equality.
      now eapply red_equality_inv.
  Defined.

  Next Obligation.
    pose hΣ. sq.
    inversion HT; subst. 
    rewrite <- wf_env_lookup_correct in e. 
    rewrite isdecl in e. inversion e. subst.   
    now constructor.
  Qed.
  Next Obligation.
    inversion HT ; subst.
    clear wildcard. rewrite <- wf_env_lookup_correct in e. 
    rewrite isdecl in e. inversion e.
  Qed.
  Next Obligation.
    inversion HT ; subst.
    clear wildcard. rewrite <- wf_env_lookup_correct in e. 
    rewrite isdecl in e. inversion e.
  Qed.

  Next Obligation.
    sq.
    inversion HT.
    clear e.
    destruct decl as (?&?&isdecl').
    cbn.
    eapply declared_inductive_inj in isdecl' as []; tea.
    subst.
    now econstructor.
  Qed.
  Next Obligation.
    sq.
    inversion HT ; subst.
    eapply lookup_ind_decl_complete.
    1: now symmetry.
    now do 2 eexists.
  Qed.

  Next Obligation.
    sq.
    inversion HT ; subst.
    clear e.
    destruct decl as (?&?&isdecl').
    cbn in *.
    eapply declared_constructor_inj in isdecl as (?&[]).
    2: now econstructor.
    subst.
    econstructor ; tea.
    now split.
  Qed.
  Next Obligation.
    sq.
    inversion HT ; subst.
    clear e.
    destruct decl as (?&?&isdecl').
    destruct isdecl as [isdecl]; cbn -[lookup_ind_decl] in *.
    eapply declared_inductive_inj in isdecl' as []; tea.
    subst.
    now congruence.
  Qed.
  Next Obligation.
    sq.
    inversion HT ; subst.
    destruct isdecl.
    eapply lookup_ind_decl_complete.
    1: now symmetry.
    now do 2 eexists.
  Qed.
  
  Next Obligation. eauto. Defined.  

  Next Obligation. eauto. Defined.   
 
  Next Obligation.
    inversion HT ; subst.
    inversion X.
    now econstructor.
  Qed.
  Next Obligation.
    destruct infer.
    pose hΣ; sq.
    cbn.
    apply infering_typing, validity in s as [] ; eauto.
    now eexists.
  Defined.


  Next Obligation.
    destruct infer.
    destruct indargs as (?&?&?&?).
    cbn in *.
    pose hΣ; sq.
    inversion HT ; subst.
    move: (X) => inf.
    eapply infering_ind_ind in inf as [? []].
    2,3: eauto.
    2: now econstructor ; tea ; apply closed_red_red.
    subst.
    rewrite /ptm.
    erewrite <- PCUICCasesContexts.inst_case_predicate_context_eq ; tea.
    econstructor ; tea.
    + econstructor ; tea.
      now apply closed_red_red.
    + replace #|x2| with #|args| ; tea.
      etransitivity.
      2: symmetry.
      all: eapply All2_length ; eassumption.
    + eapply All2_impl.
      2:intros; now eapply equality_forget_conv.
      etransitivity.
      1: eapply All2_firstn.
      1: etransitivity.
      1: now eapply red_terms_equality_terms.
      1: symmetry.
      1: now eapply red_terms_equality_terms.
      eapply PCUICConvCumInversion.alt_into_equality_terms ; tea.
      * fvs.
      * eapply infering_ind_typing, validity, isType_open in X ; auto.
        rewrite on_free_vars_mkApps in X.
        move: X => /andP [] _ /forallb_All ?.
        now eapply All_forallb, All_firstn.
      * apply infering_typing, subject_is_open_term in HT ; auto.
        move: HT => /= /andP [] //.
  Defined.
  Next Obligation.
    destruct infer as [? i].
    cbn in *.
    pose hΣ; sq.
    apply a0.
    inversion HT ; subst.
    eapply infering_ind_infering in i as [? []] ; eauto.
  Defined.

  Next Obligation. eauto. Defined. 

  Next Obligation. eauto. Defined.

  Next Obligation.  
    inversion HT.
    inversion X.
    now econstructor.
  Qed.
  Next Obligation.
    destruct infer.
    pose hΣ; sq.
    cbn.
    eapply infering_typing, validity in s as []; eauto.
    now eexists.
  Defined.
  Next Obligation.
    destruct infer.
    destruct indargs as (?&?&?&?).
    destruct d as (?&?&isdecl).
    clear e.
    cbn -[lookup_ind_decl] in *.
    pose hΣ; sq. 
    inversion HT ; subst.
    destruct H1 as [[isdecl' ] []].
    cbn -[nth_error] in *.
    eapply declared_inductive_inj in isdecl' as [].
    2: eexact isdecl.
    subst.
    eapply infering_ind_ind in X as [? []].
    2-3: eauto.
    2: now econstructor ; tea ; apply closed_red_red.
    subst.
    econstructor.
    - now do 2 split.
    - econstructor ; tea.
      now apply closed_red_red.
    - etransitivity ; tea.
      etransitivity.
      2: symmetry; eapply All2_length ; eassumption.
      now eapply All2_length.
  Defined.
  Next Obligation.
    destruct infer.
    cbn -[lookup_ind_decl] in *.
    pose hΣ; sq.
    inversion HT.
    eapply infering_ind_infering in s as [? []] ; eauto.
    apply a0.
    do 3 eexists.
    now sq.
  Defined.
  Next Obligation.
    destruct d as (?&?&isdecl).
    clear e.
    inversion HT.
    destruct H1 as [[] []].
    cbn -[lookup_ind_decl nth_error] in *.
    eapply declared_inductive_inj in isdecl as [] ; tea.
    subst.
    now congruence.
  Qed.
  Next Obligation.
    cbn -[lookup_ind_decl] in *.
    inversion HT.
    eapply lookup_ind_decl_complete ; eauto.
    do 2 eexists.
    exact H1.
  Qed.

  Next Obligation.
    sq.
    inversion HT ; subst.
    now econstructor.
  Qed.
  Next Obligation.
    cbn in e.
    inversion HT.
    congruence.
  Qed.

  Next Obligation.
    sq.
    inversion HT ; subst.
    now econstructor.
  Qed.
  Next Obligation.
    cbn in e.
    inversion HT.
    congruence.
  Qed.

  Next Obligation.
    inversion HT.
  Qed.

  Definition type_of Γ wfΓ t wt : term := (infer Γ wfΓ t wt).
  
  Definition principal_typing Σ Γ t P := 
    forall T, Σ ;;; Γ |- t : T -> Σ ;;; Γ ⊢ P ≤ T.

  Program Definition type_of_typing Γ t (wt : welltyped gΣ Γ t) : ∑ T, ∥ (gΣ ;;; Γ |- t : T) × principal_typing gΣ Γ t T ∥ :=
    let it := infer Γ _ t _ in
    (it.π1; _).
  Next Obligation.
    destruct wt; sq; pcuic.
  Qed.
  Next Obligation.
    pose hΣ; sq.
    destruct wt as [T Ht].
    eapply BDFromPCUIC.typing_infering in Ht as [T' [inf _]].
    now exists T'.
  Qed.
  Next Obligation.
    cbn in *. subst it. destruct hΣ as [wΣ]. 
    destruct infer as []; cbn.
    destruct wt as [T' HT'].
    sq.
    split.
    eapply BDToPCUIC.infering_typing in s; pcuic.
    intros T'' HT''.
    apply typing_infering in HT'' as [P [HP HP']].
    eapply infering_checking;tea. 1-2: pcuic.
    admit. (* fvs. *)
    econstructor; tea. now eapply equality_forget in HP'.
  Admitted.
    
  Open Scope type_scope.
  
  Definition map_typing_result {A B} (f : A -> B) (e : typing_result A) : typing_result B :=
    match e with
    | Checked a => Checked (f a)
    | TypeError e => TypeError e
    end.

  Arguments iswelltyped {cf Σ Γ t A}.

  Equations? type_of_subtype {Γ t T} (wt : ∥ gΣ ;;; Γ |- t : T ∥) :
    ∥ gΣ ;;; Γ ⊢ type_of Γ _ t _ ≤ T ∥ :=
    type_of_subtype wt := _.
  Proof.
    - case wt as [wt'].
      apply sq.
      now exact (typing_wf_local wt').
    - case wt as [wt'].
      case hΣ as [hΣ'].
      apply typing_infering in wt'.
      case wt' as [T' [i]].
      exists T'.
      exact i.
    - unfold type_of.
      destruct infer as [P HP].
      pose hΣ; sq. simpl.
      eapply infering_checking ; eauto.
      + now eapply typing_wf_local.
      + now eapply type_is_open_term.
      + now eapply typing_checking.   
  Defined.

  (* Note the careful use of squashing here: the principal type is accessible 
    computationally but the proof it is principal is squashed (in Prop).
    The [PCUICPrincipality.principal_type] proof gives an unsquashed version of the same theorem. *)
    
  Theorem principal_types {Γ t} (wt : welltyped gΣ Γ t) : 
    ∑ P, ∥ forall T, gΣ ;;; Γ |- t : T -> (gΣ ;;; Γ |- t : P) * (gΣ ;;; Γ ⊢ P ≤ T) ∥.
  Proof.
    unshelve eexists (infer Γ _ t _).
    - destruct wt.
      pose hΣ; sq.
      now eapply typing_wf_local.
    - pose hΣ; sq.
      destruct wt as [? wt].
      eapply typing_infering in wt as [? []].
      econstructor.
      eassumption.
    - destruct infer as [T [i]].
      cbn.
      pose hΣ; sq.
      intros T' ; split.
      + apply infering_typing ; eauto.
        now eapply typing_wf_local.
      + eapply infering_checking ; eauto.
        * now eapply typing_wf_local.
        * now eapply type_is_open_term.
        * now eapply typing_checking.
  Qed.

End TypeOf.
