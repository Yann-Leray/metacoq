(* Distributed under the terms of the MIT license. *)
From Coq Require Import CMorphisms.
From MetaCoq.Utils Require Import LibHypsNaming utils.
From MetaCoq.Common Require Import config Reflect.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICReflect PCUICClosed PCUICOnFreeVars.

Require Import ssreflect ssrbool.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

#[global]
Instance All2_fold_len {A} P (Γ Δ : list A) : HasLen (All2_fold P Γ Δ) #|Γ| #|Δ| :=
  All2_fold_length.

Implicit Types (cf : checker_flags).

Definition cmp_universe_instance (cmp_univ : Universe.t -> Universe.t -> Prop) : Instance.t -> Instance.t -> Prop :=
  Forall2 (on_rel cmp_univ Universe.make').

Definition cmp_universe_instance_dep cmp_univ P' :=
  fun {u u'} (H : cmp_universe_instance cmp_univ u u') => Forall2_dep P' H.

(** Cumulative inductive types:

  To simplify the development, we allow the variance list to not exactly
  match the instances, so as to keep syntactic ws_cumul_pb an equivalence relation
  even on ill-formed terms. It corresponds to the right notion on well-formed terms.
*)

Definition cmp_universe_variance (cmp_univ : conv_pb -> Universe.t -> Universe.t -> Prop) pb v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => on_rel (cmp_univ pb) Universe.make' u u'
  | Variance.Invariant => on_rel (cmp_univ Conv) Universe.make' u u'
  end.

Definition cmp_universe_instance_variance cmp_univ pb v u u' :=
  Forall3 (cmp_universe_variance cmp_univ pb) v u u'.

Definition global_variance_gen lookup gr napp :=
  match gr with
  | IndRef ind =>
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => if (context_assumptions ctx) <=? napp then
          match mdecl.(ind_variance) with
          | Some var => Variance var
          | None => AllEqual
          end
        else AllEqual
      | None => AllEqual
      end
    | None => AllEqual
    end
  | ConstructRef ind k =>
    match lookup_constructor_gen lookup ind k with
    | Some (mdecl, idecl, cdecl) =>
      if (cdecl.(cstr_arity) + mdecl.(ind_npars))%nat <=? napp then
        (** Fully applied constructors are always compared at the same supertype,
          which implies that no universe ws_cumul_pb needs to be checked here.
          We will still check that the instances have the same length. *)
        AllIrrelevant
      else AllEqual
    | _ => AllEqual
    end
  | _ => AllEqual
  end.

Notation global_variance Σ := (global_variance_gen (lookup_env Σ)).

Definition cmp_opt_variance cmp_univ pb v :=
  match v with
  | AllEqual => cmp_universe_instance (cmp_univ Conv)
  | AllIrrelevant => fun l l' => #|l| = #|l'|
  | Variance v => fun u u' => cmp_universe_instance (cmp_univ Conv) u u' \/ cmp_universe_instance_variance cmp_univ pb v u u'
  end.

Lemma cmp_universe_universe_variance (cmp_univ : conv_pb -> Universe.t -> Universe.t -> Prop) pb v u u' :
  RelationClasses.subrelation (cmp_univ Conv) (cmp_univ pb) ->
  on_rel (cmp_univ Conv) Universe.make' u u' -> cmp_universe_variance cmp_univ pb v u u'.
Proof.
  destruct v => //=.
  intros H H1; apply H, H1.
Qed.

Lemma cmp_instance_variance cmp_univ pb v u u' :
  RelationClasses.subrelation (cmp_univ Conv) (cmp_univ pb) ->
  #|v| = #|u| ->
  cmp_universe_instance (cmp_univ Conv) u u' -> cmp_universe_instance_variance cmp_univ pb v u u'.
Proof.
  intros Hsub Hlen Hu.
  apply Forall2_triv in Hlen.
  eapply Forall2_Forall2_Forall3 in Hu; tea.
  apply Forall3_impl with (1 := Hu) => v1 u1 u1' [] _ H1.
  now apply cmp_universe_universe_variance.
Qed.

Lemma cmp_instance_opt_variance cmp_univ pb v :
  RelationClasses.subrelation (cmp_opt_variance cmp_univ pb AllEqual) (cmp_opt_variance cmp_univ pb v).
Proof.
  intros u u' H.
  destruct v as [| |v] => //=.
  1: now apply Forall2_length in H.
  now left.
Qed.

Lemma cmp_opt_variance_var_dec cmp_univ pb v ui ui' :
  RelationClasses.subrelation (cmp_univ Conv) (cmp_univ pb) ->
  cmp_universe_instance (cmp_univ Conv) ui ui' \/ cmp_universe_instance_variance cmp_univ pb v ui ui' ->
  { cmp_universe_instance (cmp_univ Conv) ui ui' } + { cmp_universe_instance_variance cmp_univ pb v ui ui' }.
Proof.
  intros subr H.
  elim:(eq_dec #|v| #|ui|).
  - right.
    destruct H as [|]; tas.
    now eapply cmp_instance_variance.
  - left.
    destruct H as [|]; tas.
    eapply @Forall3_Forall2_left with (Q := fun _ _ => True) in H => //.
    apply Forall2_length in H.
    now exfalso.
Qed.

Lemma cmp_opt_variance_length cmp_univ pb v ui ui' :
  cmp_opt_variance cmp_univ pb v ui ui' -> #|ui| = #|ui'|.
Proof.
  destruct v => //=.
  1: apply Forall2_length.
  move => [|].
  1: apply Forall2_length.
  intro H.
  eapply @Forall2_length with (P := fun _ _ => True).
  now eapply Forall3_Forall2_right => //.
Qed.

Lemma cmp_opt_variance_or_impl cmp_universe1 cmp_universe2 cmp_universe3 pb1 pb2 pb3 v u1 u1' u2 u2' u3 u3' :
  RelationClasses.subrelation (cmp_universe1 Conv) (cmp_universe1 pb1) ->
  RelationClasses.subrelation (cmp_universe2 Conv) (cmp_universe2 pb2) ->
  (cmp_universe_instance (cmp_universe1 Conv) u1 u1' -> cmp_universe_instance (cmp_universe2 Conv) u2 u2' -> cmp_universe_instance (cmp_universe3 Conv) u3 u3') ->
  (cmp_universe_instance_variance cmp_universe1 pb1 v u1 u1' -> cmp_universe_instance_variance cmp_universe2 pb2 v u2 u2' -> cmp_universe_instance_variance cmp_universe3 pb3 v u3 u3') ->
  (#|u1| = #|u1'| -> #|u2| = #|u2'| -> #|u1| = #|u2|) ->
  cmp_universe_instance (cmp_universe1 Conv) u1 u1' \/ cmp_universe_instance_variance cmp_universe1 pb1 v u1 u1' ->
  cmp_universe_instance (cmp_universe2 Conv) u2 u2' \/ cmp_universe_instance_variance cmp_universe2 pb2 v u2 u2' ->
  cmp_universe_instance (cmp_universe3 Conv) u3 u3' \/ cmp_universe_instance_variance cmp_universe3 pb3 v u3 u3'.
Proof.
  intros Hsub1 Hsub2 Hl Hr e [H|H] [H'|H']; [left; apply Hl| right; apply Hr ..]; auto.
  all: apply cmp_instance_variance; tas.
  - rewrite e.
    all: eapply Forall2_length; tea.
    + eapply @Forall3_Forall2_right with (Q := fun _ _ => True); eauto.
    + eapply @Forall3_Forall2_left with (Q := fun _ _ => True); eauto.
  - rewrite -e.
    all: eapply Forall2_length; tea.
    + eapply @Forall3_Forall2_right with (Q := fun _ _ => True); eauto.
    + eapply @Forall3_Forall2_left with (Q := fun _ _ => True); eauto.
Qed.

Definition cmp_global_instance_gen Σ cmp_universe pb gr napp :=
  cmp_opt_variance cmp_universe pb (global_variance_gen Σ gr napp).

Notation cmp_global_instance Σ := (cmp_global_instance_gen (lookup_env Σ)).

Definition cmp_ind_universes {cf:checker_flags} (Σ : global_env_ext) ind n i i' :=
  cmp_global_instance Σ (compare_universe (global_ext_constraints Σ)) Cumul (IndRef ind) n i i'.

Lemma cmp_universe_instance_impl R R' :
  RelationClasses.subrelation R R' ->
  RelationClasses.subrelation (cmp_universe_instance R) (cmp_universe_instance R').
Proof.
  intros H x y xy. eapply Forall2_impl; tea; unfold on_rel; auto.
Qed.

Lemma cmp_universe_instance_impl' R R' :
  RelationClasses.subrelation R R' ->
  forall u u', cmp_universe_instance R u u' -> cmp_universe_instance R' u u'.
Proof.
  intros H x y xy. eapply Forall2_impl; tea; unfold on_rel; auto.
Qed.

Lemma cmp_universe_variance_impl R R' pb pb' v :
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R pb) (R' pb') ->
  RelationClasses.subrelation (cmp_universe_variance R pb v) (cmp_universe_variance R' pb' v).
Proof.
  intros HConv Hpb x y.
  destruct v => //=.
  all: unfold on_rel; now auto.
Qed.

Lemma cmp_universe_instance_variance_impl R R' pb pb' v :
  RelationClasses.subrelation (R Conv) (R' Conv) ->
  RelationClasses.subrelation (R pb) (R' pb') ->
  RelationClasses.subrelation (cmp_universe_instance_variance R pb v) (cmp_universe_instance_variance R' pb' v).
Proof.
  intros HConv Hpb x y xy.
  eapply Forall3_impl; tea.
  intros ???.
  now apply cmp_universe_variance_impl.
Qed.


(* TODO MOVE *)
#[global]
Existing Instance All2_symP.

(* TODO MOVE *)
#[global]
Existing Instance Forall2_symP.

#[global]
Instance cmp_universe_instance_refl cmp_universe :
  RelationClasses.Reflexive cmp_universe ->
  RelationClasses.Reflexive (cmp_universe_instance cmp_universe).
Proof.
  intros refl_univ u.
  apply Forall2_same; reflexivity.
Qed.

#[global]
Instance cmp_universe_instance_sym cmp_universe :
  RelationClasses.Symmetric cmp_universe ->
  RelationClasses.Symmetric (cmp_universe_instance cmp_universe).
Proof. intros tRe x y. now eapply Forall2_symP. Qed.

#[global]
Instance cmp_universe_instance_trans cmp_universe :
  RelationClasses.Transitive cmp_universe ->
  RelationClasses.Transitive (cmp_universe_instance cmp_universe).
Proof. intros tRe x y z. eapply Forall2_trans. tc. Qed.

#[global]
Instance cmp_universe_variance_sym cmp_universe pb v :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_universe_variance cmp_universe pb v).
Proof.
  intros univ_sym univ_sym' u u' u''.
  destruct v as [| |] => //=.
  all: now symmetry.
Qed.

#[global]
Instance cmp_universe_variance_trans cmp_universe pb v :
  RelationClasses.Transitive (cmp_universe Conv) ->
  RelationClasses.Transitive (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_universe_variance cmp_universe pb v).
Proof.
  intros univ_trans univ_trans' u u' u''.
  destruct v as [| |] => //=.
  all: now etransitivity.
Qed.

#[global]
Instance cmp_universe_instance_variance_sym cmp_universe pb v :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_universe_instance_variance cmp_universe pb v).
Proof.
  intros univ_sym univ_sym' u u'.
  apply Forall3_symP. tc.
Qed.

#[global]
Instance cmp_universe_instance_variance_trans cmp_universe pb v :
  RelationClasses.Transitive (cmp_universe Conv) ->
  RelationClasses.Transitive (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_universe_instance_variance cmp_universe pb v).
Proof.
  intros univ_trans univ_trans' u u' u''.
  apply Forall3_transP. tc.
Qed.

#[global]
Instance cmp_global_instance_refl Σ cmp_universe pb gr napp :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_global_instance Σ cmp_universe pb gr napp).
Proof.
  intros rRE rRle.
  unfold cmp_global_instance_gen.
  destruct global_variance_gen as [| |v] => //= u.
  - now apply cmp_universe_instance_refl.
  - left. now apply cmp_universe_instance_refl.
Qed.

#[global]
Instance cmp_global_instance_sym Σ cmp_universe pb gr napp :
  RelationClasses.Symmetric (cmp_universe Conv) ->
  RelationClasses.Symmetric (cmp_universe pb) ->
  RelationClasses.Symmetric (cmp_global_instance Σ cmp_universe pb gr napp).
Proof.
  intros univ_sym univ_sym'.
  unfold cmp_global_instance_gen.
  destruct global_variance_gen as [| |v] => //= u u'.
  - now symmetry.
  - intros [H | H]; [left|right].
    all: now symmetry.
Qed.

#[global]
Instance cmp_global_instance_trans Σ cmp_universe pb gr napp :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_universe Conv) ->
  RelationClasses.Transitive (cmp_universe pb) ->
  RelationClasses.Transitive (cmp_global_instance Σ cmp_universe pb gr napp).
Proof.
  intros univ_sub univ_trans univ_trans'.
  unfold cmp_global_instance_gen.
  destruct global_variance_gen as [| |v] => //= u u' u''.
  1,2: now etransitivity.

  apply cmp_opt_variance_or_impl; tas.
  all: now etransitivity.
Qed.


#[global]
Instance cmp_universe_instance_equiv R (hR : RelationClasses.Equivalence R)
  : RelationClasses.Equivalence (cmp_universe_instance R).
Proof.
  split.
  - intro. apply Forall2_same. reflexivity.
  - intros x y xy. eapply Forall2_sym, Forall2_impl; tea. now symmetry.
  - intros x y z xy yz. eapply Forall2_trans; tea. apply on_rel_trans. apply hR.
Qed.

Lemma cmp_universe_instance_antisym cmp_universe pb (hE : RelationClasses.Equivalence (cmp_universe Conv)) :
  RelationClasses.Antisymmetric _ (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Antisymmetric _ (cmp_universe_instance (cmp_universe Conv)) (cmp_universe_instance (cmp_universe pb)).
Proof.
  intros H x y H1 H2.
  eapply Forall2_sym in H2.
  eapply Forall2_impl; [eapply Forall2_and|]; [exact H1|exact H2|].
  cbn; intros ? ? [? ?]. eapply H; assumption.
Qed.

#[global]
Instance cmp_global_instance_equiv Σ cmp_universe (hE : RelationClasses.Equivalence (cmp_universe Conv)) gr napp
  : RelationClasses.Equivalence (cmp_global_instance Σ cmp_universe Conv gr napp).
Proof.
  split.
  - intro. apply cmp_global_instance_refl; typeclasses eauto.
  - intros x y xy. eapply cmp_global_instance_sym; auto; typeclasses eauto.
  - intros x y z xy yz. eapply cmp_global_instance_trans; eauto; typeclasses eauto.
Qed.

Lemma cmp_universe_variance_antisym cmp_universe pb (hRe : RelationClasses.Equivalence (cmp_universe Conv)) v u u' :
  RelationClasses.Antisymmetric _ (cmp_universe Conv) (cmp_universe pb) ->
  cmp_universe_variance cmp_universe pb v u u' ->
  cmp_universe_variance cmp_universe pb v u' u ->
  cmp_universe_variance cmp_universe Conv v u u'.
Proof.
  intro hAntisym.
  destruct v => //=.
  apply hAntisym.
Qed.

Lemma cmp_universe_instance_variance_antisym cmp_universe pb (hRe : RelationClasses.Equivalence (cmp_universe Conv)) l u v :
  RelationClasses.Antisymmetric _ (cmp_universe Conv) (cmp_universe pb) ->
  cmp_universe_instance_variance cmp_universe pb l u v ->
  cmp_universe_instance_variance cmp_universe pb l v u ->
  cmp_universe_instance_variance cmp_universe Conv l u v.
Proof.
  intro hAntisym.
  apply Forall3_antisymP. intros ???.
  now eapply cmp_universe_variance_antisym.
Qed.

#[global]
Instance cmp_global_instance_antisym Σ cmp_universe pb (hRe : RelationClasses.Equivalence (cmp_universe Conv)) gr napp :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Antisymmetric _ (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.Antisymmetric _ (cmp_global_instance Σ cmp_universe Conv gr napp) (cmp_global_instance Σ cmp_universe pb gr napp).
Proof.
  intros hsub hR u v.
  unfold cmp_global_instance_gen, cmp_opt_variance.
  destruct global_variance_gen; auto.
  apply cmp_opt_variance_or_impl; auto.
  eapply cmp_universe_instance_variance_antisym; tea.
Qed.


Lemma cmp_universe_variance_flip cmp_universe cmp_universe' pb pb' v u u' :
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  cmp_universe_variance cmp_universe pb v u u' ->
  cmp_universe_variance cmp_universe' pb' v u' u.
Proof.
  intros conv_sym pb_sym.
  destruct v => //=.
  all: unfold on_rel, flip in *; now auto.
Qed.

Lemma cmp_universe_instance_variance_flip cmp_universe cmp_universe' pb pb' v u u' :
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  cmp_universe_instance_variance cmp_universe pb v u u' ->
  cmp_universe_instance_variance cmp_universe' pb' v u' u.
Proof.
  intros conv_sym pb_sym H.
  induction H; constructor; eauto.
  now eapply cmp_universe_variance_flip.
Qed.


Lemma cmp_universe_instance_flip eq_universe eq_universe' u u' :
  RelationClasses.subrelation eq_universe (flip eq_universe') ->
  cmp_universe_instance eq_universe u u' ->
  cmp_universe_instance eq_universe' u' u.
Proof.
  intros Hsub H.
  apply Forall2_sym, Forall2_impl with (1 := H).
  intros ??. apply Hsub.
Qed.

Lemma cmp_global_instance_flip Σ cmp_universe cmp_universe' pb pb' gr napp u u':
  RelationClasses.subrelation (cmp_universe Conv) (flip (cmp_universe' Conv)) ->
  RelationClasses.subrelation (cmp_universe pb) (flip (cmp_universe' pb')) ->
  cmp_global_instance Σ cmp_universe pb gr napp u u' ->
  cmp_global_instance Σ cmp_universe' pb' gr napp u' u.
Proof.
  intros conv_sym pb_sym.
  unfold cmp_global_instance_gen, cmp_opt_variance.
  destruct global_variance_gen as [| |v] => //.
  2: intros [H|H]; [left|right]; move:H.
  1,2: apply cmp_universe_instance_flip; tas; reflexivity.
  now apply cmp_universe_instance_variance_flip.
Qed.

Inductive eq_decl_upto_names : context_decl -> context_decl -> Type :=
  | compare_vass {na na' T} :
    eq_binder_annot na na' -> eq_decl_upto_names (vass na T) (vass na' T)
  | compare_vdef {na na' b T} :
    eq_binder_annot na na' -> eq_decl_upto_names (vdef na b T) (vdef na' b T).
Derive Signature NoConfusion for eq_decl_upto_names.
#[global] Hint Constructors eq_decl_upto_names : pcuic.

Definition compare_decls cmp_term pb := PCUICConversion.All_decls_alpha_pb pb cmp_term.

Notation eq_context_upto_names := (All2 eq_decl_upto_names).

Notation eq_context_gen cmp_term pb :=
  (All2_fold (fun Γ _ => compare_decls (cmp_term Γ) pb)).

Lemma eq_decl_upto_names_gen decl decl' pb : eq_decl_upto_names decl decl' <~> compare_decls (fun _ => eq) pb decl decl'.
Proof.
  split; intros e; depind e; subst; constructor; auto.
Qed.

Lemma eq_context_upto_names_gen Γ Γ' pb : eq_context_upto_names Γ Γ' <~> eq_context_gen (fun _ _ => eq) pb Γ Γ'.
Proof.
  split; intros e; depind e; constructor; tas; now eapply eq_decl_upto_names_gen.
Qed.

Lemma compare_decls_impl cmp_term cmp_term' pb pb' :
  subrelation (cmp_term Conv) (cmp_term' Conv) ->
  subrelation (cmp_term pb) (cmp_term' pb') ->
  subrelation (compare_decls cmp_term pb) (compare_decls cmp_term' pb').
Proof.
  intros he hle x y []; constructor; auto.
Qed.

Lemma eq_context_gen_impl cmp_term cmp_term' pb pb' :
  (forall Γ, subrelation (cmp_term Γ Conv) (cmp_term' Γ Conv)) ->
  (forall Γ, subrelation (cmp_term Γ pb) (cmp_term' Γ pb')) ->
  subrelation (eq_context_gen cmp_term pb) (eq_context_gen cmp_term' pb').
Proof.
  intros he hle x y eq.
  eapply All2_fold_impl; tea => /=.
  intros; eapply compare_decls_impl; tea.
  all: cbn; auto.
Qed.

Lemma compare_decl_impl_ondecl P cmp_term cmp_term' pb pb' d d' :
  ondecl P d ->
  (forall x y, P x -> cmp_term Conv x y -> cmp_term' Conv x y) ->
  (forall x y, P x -> cmp_term pb x y -> cmp_term' pb' x y) ->
  compare_decls cmp_term pb d d' ->
  compare_decls cmp_term' pb' d d'.
Proof.
  intros ond he hle cd; depelim cd; depelim ond; constructor => //; eauto.
Qed.

Lemma compare_decl_map cmp_term pb f g d d' :
  compare_decls (fun pb x y => cmp_term pb (f x) (g y)) pb d d' ->
  compare_decls cmp_term pb (map_decl f d) (map_decl g d').
Proof.
  intros h; depelim h; constructor; intuition auto.
Qed.

#[global]
Polymorphic Instance compare_decl_refl cmp_term pb :
  CRelationClasses.Reflexive (cmp_term Conv) ->
  CRelationClasses.Reflexive (cmp_term pb) ->
  CRelationClasses.Reflexive (compare_decls cmp_term pb).
Proof.
  intros heq hle d.
  destruct d as [na [b|] ty]; constructor; auto; reflexivity.
Qed.

#[global]
Polymorphic Instance compare_decl_sym cmp_term pb :
  CRelationClasses.Symmetric (cmp_term Conv) ->
  CRelationClasses.Symmetric (cmp_term pb) ->
  CRelationClasses.Symmetric (compare_decls cmp_term pb).
Proof.
  intros heq hle d d' []; constructor; auto; now symmetry.
Qed.

#[global]
Polymorphic Instance compare_decl_trans cmp_term pb :
  CRelationClasses.Transitive (cmp_term Conv) ->
  CRelationClasses.Transitive (cmp_term pb) ->
  CRelationClasses.Transitive (compare_decls cmp_term pb).
Proof.
  intros hle hre x y z h h'; depelim h; depelim h'; constructor; auto;
  etransitivity; eauto.
Qed.

#[global]
Polymorphic Instance eq_decl_upto_names_refl :
  CRelationClasses.Reflexive eq_decl_upto_names.
Proof.
  intros d.
  destruct d as [na [b|] ty]; constructor; auto; reflexivity.
Qed.

#[global]
Polymorphic Instance eq_decl_upto_names_sym :
  CRelationClasses.Symmetric eq_decl_upto_names.
Proof.
  intros d d' []; constructor; auto; now symmetry.
Qed.

#[global]
Polymorphic Instance eq_decl_upto_names_trans :
  CRelationClasses.Transitive eq_decl_upto_names.
Proof.
  intros x y z h h'; depelim h; depelim h'; constructor; auto;
  etransitivity; eauto.
Qed.

#[global]
Instance alpha_eq_reflexive : CRelationClasses.Reflexive eq_context_upto_names.
Proof.
  intros x. eapply All2_refl. reflexivity.
Qed.

#[global]
Instance alpha_eq_symmmetric : CRelationClasses.Symmetric eq_context_upto_names.
Proof.
  intros x. eapply All2_symP. tc.
Qed.

#[global]
Instance alpha_eq_trans : CRelationClasses.Transitive eq_context_upto_names.
Proof.
  intros x y z. apply All2_trans. tc.
Qed.

#[global]
Polymorphic Instance eq_context_refl cmp_term pb :
  (forall Γ, CRelationClasses.Reflexive (cmp_term Γ Conv)) ->
  (forall Γ, CRelationClasses.Reflexive (cmp_term Γ pb)) ->
  CRelationClasses.Reflexive (eq_context_gen cmp_term pb).
Proof.
  intros heq hle x.
  eapply All2_fold_refl.
  intros. reflexivity.
Qed.

#[global]
Polymorphic Instance eq_context_sym cmp_term pb :
  (forall pb0 pb Γ Γ', eq_context_gen cmp_term pb0 Γ Γ' -> subrelation (cmp_term Γ pb) (cmp_term Γ' pb)) ->
  (forall Γ, CRelationClasses.Symmetric (cmp_term Γ Conv)) ->
  (forall Γ, CRelationClasses.Symmetric (cmp_term Γ pb)) ->
  CRelationClasses.Symmetric (eq_context_gen cmp_term pb).
Proof.
  intros hΓ heq hle.
  eapply All2_fold_sym.
  intros. symmetry.
  eapply compare_decls_impl; tea.
  all: cbn; eauto.
Qed.

#[global]
Polymorphic Instance eq_context_trans cmp_term pb :
  (forall pb0 pb Γ Γ', eq_context_gen cmp_term pb0 Γ Γ' -> subrelation (cmp_term Γ pb) (cmp_term Γ' pb)) ->
  (forall Γ, CRelationClasses.Symmetric (cmp_term Γ Conv)) ->
  (forall Γ, CRelationClasses.Symmetric (cmp_term Γ pb)) ->
  (forall Γ, CRelationClasses.Transitive (cmp_term Γ Conv)) ->
  (forall Γ, CRelationClasses.Transitive (cmp_term Γ pb)) ->
  CRelationClasses.Transitive (eq_context_gen cmp_term pb).
Proof.
  intros hΓ hs hs' hr hr'.
  eapply All2_fold_trans; intros.
  transitivity y; tas.
  eapply compare_decls_impl; tea.
  all: cbn; eapply hΓ.
  all: now symmetry.
Qed.

Lemma eq_context_gen_context_assumptions {P pb} {Γ Δ} :
  eq_context_gen P pb Γ Δ ->
  context_assumptions Γ = context_assumptions Δ.
Proof using Type.
  induction 1; simpl; auto. depelim p => /=; now auto using f_equal.
Qed.

Definition eq_predicate (eq_term : context -> term -> term -> Type) eq_universe Γ p p' :=
  All2 (eq_term Γ) p.(pparams) p'.(pparams) ×
  cmp_universe_instance eq_universe p.(puinst) p'.(puinst) ×
  eq_context_upto_names p.(pcontext) p'.(pcontext) ×
  eq_term (Γ ,,, inst_case_predicate_context p) p.(preturn) p'.(preturn).

Definition eq_branch (eq_term : context -> term -> term -> Type) Γ p br br' :=
  eq_context_upto_names br.(bcontext) br'.(bcontext) ×
  eq_term (Γ ,,, inst_case_branch_context p br) br.(bbody) br'.(bbody).

Definition eq_branches eq_term Γ p brs brs' := All2 (eq_branch eq_term Γ p) brs brs'.

Notation eq_mfixpoint0 eq_term Γ types mfix mfix' :=
  (All2 (fun d d' =>
    eq_term Γ d.(dtype) d'.(dtype) ×
    eq_term (Γ ,,, types) d.(dbody) d'.(dbody) ×
    d.(rarg) = d'.(rarg) ×
    eq_binder_annot d.(dname) d'.(dname)
  ) mfix mfix') (Γ in scope empty).

Definition eq_mfixpoint (eq_term : context -> term -> term -> Type) Γ mfix mfix' :=
  eq_mfixpoint0 eq_term Γ (fix_context mfix) mfix mfix'.

(** ** Syntactic ws_cumul_pb up-to universes
  We don't look at printing annotations *)

(** ws_cumul_pb is indexed by a natural number that counts the number of applications
  that surround the current term, used to implement cumulativity of inductive types
  correctly (only fully applied constructors and inductives benefit from it). *)

Reserved Notation " Σ ;;; Γ ⊢ t <==[ pb , napp ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  <==[ pb , napp ]  u").
Unset Elimination Schemes.
Inductive eq_term_upto_univ_napp Σ
  (cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop)
  (cmp_sort : conv_pb -> sort -> sort -> Prop)
  (Γ : context)
  (pb : conv_pb) (napp : nat) : term -> term -> Type :=
| eq_Rel : forall n,
    Σ ;;; Γ ⊢ tRel n <==[ pb , napp ] tRel n

| eq_Evar : forall e args args',
    All2 (fun arg arg' => (Σ ;;; Γ ⊢ arg <==[ Conv , 0 ] arg')) args args' ->
    Σ ;;; Γ ⊢ tEvar e args <==[ pb , napp ] tEvar e args'

| eq_Var : forall id,
    Σ ;;; Γ ⊢ tVar id <==[ pb , napp ] tVar id

| eq_Sort : forall s s',
    cmp_sort pb s s' ->
    Σ ;;; Γ ⊢ tSort s  <==[ pb , napp ] tSort s'

| eq_App : forall t t' u u',
    Σ ;;; Γ ⊢ t <==[ pb , S napp ] t' ->
    Σ ;;; Γ ⊢ u <==[ Conv , 0 ] u' ->
    Σ ;;; Γ ⊢ tApp t u <==[ pb , napp ] tApp t' u'

| eq_Const : forall c u u',
    cmp_universe_instance (cmp_universe Conv) u u' ->
    Σ ;;; Γ ⊢ tConst c u <==[ pb , napp ] tConst c u'

| eq_Ind : forall i u u',
    cmp_global_instance Σ cmp_universe pb (IndRef i) napp u u' ->
    Σ ;;; Γ ⊢ tInd i u <==[ pb , napp ] tInd i u'

| eq_Construct : forall i k u u',
    cmp_global_instance Σ cmp_universe pb (ConstructRef i k) napp u u' ->
    Σ ;;; Γ ⊢ tConstruct i k u <==[ pb , napp ] tConstruct i k u'

| eq_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ ty <==[ Conv , 0 ] ty' ->
    Σ ;;; Γ ,, vass na ty ⊢ t <==[ pb , 0 ] t' ->
    Σ ;;; Γ ⊢ tLambda na ty t <==[ pb , napp ] tLambda na' ty' t'

| eq_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ a <==[ Conv , 0 ] a' ->
    Σ ;;; Γ ,, vass na a ⊢ b <==[ pb , 0 ] b' ->
    Σ ;;; Γ ⊢ tProd na a b <==[ pb , napp ] tProd na' a' b'

| eq_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ t <==[ Conv , 0 ] t' ->
    Σ ;;; Γ ⊢ ty <==[ Conv , 0 ] ty' ->
    Σ ;;; Γ ,, vdef na t ty ⊢ u <==[ pb , 0 ] u' ->
    Σ ;;; Γ ⊢ tLetIn na t ty u <==[ pb , napp ] tLetIn na' t' ty' u'

| eq_Case : forall indn p p' c c' brs brs',
    eq_predicate (fun Γ t t' => Σ ;;; Γ ⊢ t <==[ Conv , 0 ] t') (cmp_universe Conv) Γ p p' ->
    Σ ;;; Γ ⊢ c <==[ Conv , 0 ] c' ->
    eq_branches (fun Γ t t' => Σ ;;; Γ ⊢ t <==[ Conv , 0 ] t') Γ p brs brs' ->
    Σ ;;; Γ ⊢ tCase indn p c brs <==[ pb , napp ] tCase indn p' c' brs'

| eq_Proj : forall p c c',
    Σ ;;; Γ ⊢ c <==[ Conv , 0 ] c' ->
    Σ ;;; Γ ⊢ tProj p c <==[ pb , napp ] tProj p c'

| eq_Fix : forall mfix mfix' idx,
    eq_mfixpoint (fun Γ t t' => Σ ;;; Γ ⊢ t <==[ Conv , 0 ] t') Γ mfix mfix' ->
    Σ ;;; Γ ⊢ tFix mfix idx <==[ pb , napp ] tFix mfix' idx

| eq_CoFix : forall mfix mfix' idx,
    eq_mfixpoint (fun Γ t t' => Σ ;;; Γ ⊢ t <==[ Conv , 0 ] t') Γ mfix mfix' ->
    Σ ;;; Γ ⊢ tCoFix mfix idx <==[ pb , napp ] tCoFix mfix' idx

| eq_Prim i i' :
    onPrims (fun t t' => Σ ;;; Γ ⊢ t <==[ Conv , 0 ] t') (cmp_universe Conv) i i' ->
    Σ ;;; Γ ⊢ tPrim i <==[ pb , napp ] tPrim i'
where " Σ ;;; Γ ⊢ t <==[ pb , napp ] u " := (eq_term_upto_univ_napp Σ _ _ Γ pb napp t u) : type_scope.
Derive Signature for eq_term_upto_univ_napp.
Set Elimination Schemes.

Lemma eq_term_upto_univ_napp_rect (Σ : global_env)
  (cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop)
  (cmp_sort : conv_pb -> sort -> sort -> Prop)
  (P : forall (Γ : context) (pb : conv_pb) (napp : nat) (t u : term), Type) :

  (forall Γ pb napp (n : nat), P Γ pb napp (tRel n) (tRel n)) ->

  (forall Γ pb napp (e : nat) (args args' : list term),
    All2 (fun arg arg' => eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 arg arg' × P Γ Conv 0 arg arg') args args' ->
    P Γ pb napp (tEvar e args) (tEvar e args')) ->

  (forall Γ pb napp (id : ident),
    P Γ pb napp (tVar id) (tVar id)) ->

  (forall Γ pb napp (s s' : sort),
    cmp_sort pb s s' ->
    P Γ pb napp (tSort s) (tSort s')) ->

  (forall Γ pb napp (t t' u u' : term),
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb (S napp) t t' ->
    P Γ pb (S napp) t t' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 u u' ->
    P Γ Conv 0 u u' ->
    P Γ pb napp (tApp t u) (tApp t' u')) ->

  (forall Γ pb napp (c : kername) (u u' : Instance.t),
    cmp_universe_instance (cmp_universe Conv) u u' ->
    P Γ pb napp (tConst c u) (tConst c u')) ->

  (forall Γ pb napp (ind : inductive) (u u' : Instance.t),
    cmp_global_instance Σ cmp_universe pb (IndRef ind) napp u u' ->
    P Γ pb napp (tInd ind u) (tInd ind u')) ->

  (forall Γ pb napp (ind : inductive) (k : nat) (u u' : Instance.t),
    cmp_global_instance Σ cmp_universe pb (ConstructRef ind k) napp u u' ->
    P Γ pb napp (tConstruct ind k u) (tConstruct ind k u')) ->

  (forall Γ pb napp (na na' : binder_annot name) (ty ty' t t' : term),
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 ty ty' ->
    P Γ Conv 0 ty ty' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort (Γ,, vass na ty) pb 0 t t' ->
    P (Γ,, vass na ty) pb 0 t t' ->
    P Γ pb napp (tLambda na ty t) (tLambda na' ty' t')) ->

  (forall Γ pb napp (na na' : binder_annot name) (a a' b b' : term),
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 a a' ->
    P Γ Conv 0 a a' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort (Γ,, vass na a) pb 0 b b' ->
    P (Γ,, vass na a) pb 0 b b' ->
    P Γ pb napp (tProd na a b) (tProd na' a' b')) ->

  (forall Γ pb napp (na na' : binder_annot name) (t t' ty ty' u u' : term),
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 t t' ->
    P Γ Conv 0 t t' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 ty ty' ->
    P Γ Conv 0 ty ty' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort (Γ,, vdef na t ty) pb 0 u u' ->
    P (Γ,, vdef na t ty) pb 0 u u' ->
    P Γ pb napp (tLetIn na t ty u) (tLetIn na' t' ty' u')) ->

  (forall Γ pb napp (indn : case_info) (p p' : predicate term) (c c' : term) (brs brs' : list (branch term)),
    eq_predicate (fun Γ t t' => eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 t t' × P Γ Conv 0 t t') (cmp_universe Conv) Γ p p' ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 c c' ->
    P Γ Conv 0 c c' ->
    eq_branches (fun Γ t t' => eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 t t' × P Γ Conv 0 t t') Γ p brs brs' ->
    P Γ pb napp (tCase indn p c brs) (tCase indn p' c' brs')) ->

  (forall Γ pb napp (p : projection) (c c' : term),
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 c c' ->
    P Γ Conv 0 c c' ->
    P Γ pb napp (tProj p c) (tProj p c')) ->

  (forall Γ pb napp (mfix mfix' : mfixpoint term) (idx : nat),
    eq_mfixpoint (fun Γ t t' => eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 t t' × P Γ Conv 0 t t') Γ mfix mfix' ->
    P Γ pb napp (tFix mfix idx) (tFix mfix' idx)) ->

  (forall Γ pb napp (mfix mfix' : mfixpoint term) (idx : nat),
    eq_mfixpoint (fun Γ t t' => eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 t t' × P Γ Conv 0 t t') Γ mfix mfix' ->
    P Γ pb napp (tCoFix mfix idx) (tCoFix mfix' idx)) ->

  (forall Γ pb napp (prim prim' : prim_val),
    onPrims (fun t t' : term => eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv 0 t t' × P Γ Conv 0 t t') (cmp_universe Conv) prim prim' ->
    P Γ pb napp (tPrim prim) (tPrim prim')) ->

  forall Γ pb napp t u, eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp t u -> P Γ pb napp t u.
Proof.
  intros until Γ.
  revert Γ.
  fix rec 6. move rec at top.
  intros Γ pb napp t u H.
  destruct H.
  all: match goal with h : _ |- _ => eapply h; eauto end.
  - apply All2_impl with (1 := a) => t u h.
    split; tas. now apply rec.
  - destruct e as (ep & eu & ec & er).
    repeat split; tas.
    + apply All2_impl with (1 := ep) => t u h.
      split; tas. now apply rec.
    + now apply rec.
  - apply All2_impl with (1 := e0) => br br' [ec eb].
    split; tas.
    split; tas. now apply rec.
  - apply All2_impl with (1 := e); intros d d' (et & eb & er & en).
    repeat split; tas.
    all: now apply rec.
  - apply All2_impl with (1 := e); intros d d' (et & eb & er & en).
    repeat split; tas.
    all: now apply rec.
  - destruct o; constructor; tas.
    1,2: split; [assumption|now apply rec].
    apply All2_impl with (1 := a0) => t u h.
    split; tas. now apply rec.
Qed.
Definition eq_term_upto_univ_napp_ind := eq_term_upto_univ_napp_rect.

Notation eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb := (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb 0) (only parsing).

(* ** Syntactic conparison up-to universes *)

Definition compare_term_napp `{checker_flags} Σ φ Γ (pb : conv_pb) napp (t u : term) :=
  eq_term_upto_univ_napp Σ (compare_universe φ) (compare_sort φ) Γ pb napp t u.

Definition compare_term `{checker_flags} Σ φ Γ (pb : conv_pb) (t u : term) :=
  eq_term_upto_univ Σ (compare_universe φ) (compare_sort φ) Γ pb t u.

(* ** Syntactic conversion up-to universes *)

Notation eq_term Σ φ Γ := (compare_term Σ φ Γ Conv).

(* ** Syntactic cumulativity up-to universes *)

Notation leq_term Σ φ Γ := (compare_term Σ φ Γ Cumul).

Definition compare_opt_term `{checker_flags} (pb : conv_pb) Σ φ Γ (t u : option term) :=
  match t, u with
  | Some t, Some u => compare_term Σ φ Γ pb t u
  | None, None => True
  | _, _ => False
  end.

Definition compare_decl `{checker_flags} Σ φ Γ pb (d d' : context_decl) :=
  compare_decls (compare_term Σ φ Γ) pb d d'.

Notation eq_decl Σ φ Γ := (compare_decl Σ φ Γ Conv).
Notation leq_decl Σ φ Γ := (compare_decl Σ φ Γ Cumul).

Definition compare_context `{checker_flags} Σ φ pb (Γ Δ : context) :=
  eq_context_gen (compare_term Σ φ) pb Γ Δ.

Definition compare_context_rel `{checker_flags} Σ φ pb Γ0 (Γ Δ : context) :=
  eq_context_gen (fun Γ => compare_term Σ φ (Γ0 ,,, Γ)) pb Γ Δ.

Notation eq_context Σ φ := (compare_context Σ φ Conv).
Notation leq_context Σ φ := (compare_context Σ φ Cumul).

Definition eq_context_upto Σ cmp_universe cmp_sort pb :=
  (eq_context_gen (fun Γ pb0 => eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb0) pb).

Definition eq_context_upto_rel Σ cmp_universe cmp_sort pb Γ :=
  (eq_context_gen (fun Δ pb0 => eq_term_upto_univ Σ cmp_universe cmp_sort (Γ ,,, Δ) pb0) pb).

(* Reflexivity *)

#[global]
Polymorphic Instance creflexive_eq A : CRelationClasses.Reflexive (@eq A).
Proof. intro x. constructor. Qed.

#[global]
Polymorphic Instance eq_predicate_refl Re Ru Γ :
  (forall Γ, CRelationClasses.Reflexive (Re Γ)) ->
  RelationClasses.Reflexive Ru ->
  CRelationClasses.Reflexive (eq_predicate Re Ru Γ).
Proof.
  intros hre hru.
  intros p. unfold eq_predicate; intuition auto; try reflexivity.
  eapply All2_same; reflexivity.
Qed.

#[global]
Polymorphic Instance eq_branches_refl Re Γ p :
  (forall Γ, CRelationClasses.Reflexive (Re Γ)) ->
  CRelationClasses.Reflexive (eq_branches Re Γ p).
Proof.
  intros hre.
  intros brs. unfold eq_branches, eq_branch.
  apply All2_same. intuition auto; try reflexivity.
Qed.

#[global]
Polymorphic Instance eq_mfixpoint_refl Re Γ :
  (forall Γ, CRelationClasses.Reflexive (Re Γ)) ->
  CRelationClasses.Reflexive (eq_mfixpoint Re Γ).
Proof.
  intros hre.
  intros mfix.
  apply All2_same. intuition auto; try reflexivity.
Qed.


#[global]
Polymorphic Instance eq_term_upto_univ_refl Σ cmp_universe cmp_sort Γ pb napp :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  Reflexive (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp).
Proof.
  intros refl_univ refl_univ' refl_sort refl_sort' t.
  induction t in Γ, napp, pb, refl_univ', refl_sort' |- * using term_forall_list_ind.
  all: simpl.
  all: try constructor. all: eauto.
  all: try reflexivity.
  all: try solve [eapply All_All2 ; eauto].
  - unfold eq_predicate. solve_all.
    2,3: reflexivity.
    eapply All_All2; eauto.
  - unfold eq_branches, eq_branch.
    eapply All_All2; eauto.
    intros br [_ ?]; split; eauto. reflexivity.
  - eapply All_All2; eauto; simpl; intuition eauto.
  - eapply All_All2; eauto; simpl; intuition eauto.
  - destruct p as [? []]; constructor; cbn in X; intuition eauto.
    eapply All_All2; eauto.
Qed.

#[global]
Polymorphic Instance All2_eq_refl Σ cmp_universe cmp_sort Γ :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  CRelationClasses.Reflexive (All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv)).
Proof using Type.
  intros h h' x. apply All2_same. reflexivity.
Qed.

#[global]
Instance compare_term_refl {cf} pb {Σ : global_env} φ Γ : Reflexive (compare_term Σ φ Γ pb).
Proof. eapply eq_term_upto_univ_refl; tc. Qed.

Lemma eq_context_upto_refl Σ cmp_universe cmp_sort pb :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  Reflexive (eq_context_upto Σ cmp_universe cmp_sort pb).
Proof. exact _. Qed.

Lemma eq_context_upto_rel_refl Σ cmp_universe cmp_sort Γ pb :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  Reflexive (eq_context_upto_rel Σ cmp_universe cmp_sort pb Γ).
Proof. exact _. Qed.

(* Implication *)
Lemma global_variance_napp_mon Σ gr {napp napp'} :
  napp <= napp' ->
  match global_variance Σ gr napp with
  | Variance v => global_variance Σ gr napp' = Variance v
  | AllEqual => True
  | AllIrrelevant => global_variance Σ gr napp' = AllIrrelevant
  end.
Proof.
  intros hnapp.
  rewrite /global_variance_gen.
  destruct gr => //=.
  - destruct lookup_inductive_gen as [[mdecl idec]|] => //=.
    destruct destArity as [[ctx s]|] => //=.
    elim: Nat.leb_spec => // cass.
    destruct ind_variance => //=.
    elim: Nat.leb_spec => //. lia.
  - destruct lookup_constructor_gen as [[[mdecl idecl] cdecl]|] => //=.
    elim: Nat.leb_spec => // cass.
    elim: Nat.leb_spec => //. lia.
Qed.

#[global]
Instance cmp_global_instance_impl_same_napp Σ cmp_universe cmp_universe' pb pb' gr napp :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  subrelation (cmp_global_instance Σ cmp_universe pb gr napp) (cmp_global_instance Σ cmp_universe' pb' gr napp).
Proof.
  intros sub_conv sub_pb u u'.
  unfold cmp_global_instance_gen, cmp_opt_variance.
  destruct global_variance_gen as [| |v] => //.
  1: now apply cmp_universe_instance_impl.

  intros [H | H]; [left | right].
  1: eapply cmp_universe_instance_impl; tea.
  eapply cmp_universe_instance_variance_impl; eassumption.
Qed.

#[global]
Instance cmp_global_instance_impl Σ cmp_universe cmp_universe' pb pb' gr napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  napp <= napp' ->
  subrelation (cmp_global_instance Σ cmp_universe pb gr napp) (cmp_global_instance Σ cmp_universe' pb' gr napp').
Proof.
  intros sub_conv sub_pb lenapp u u'.
  unfold cmp_global_instance_gen.
  move: (global_variance_napp_mon Σ gr lenapp).
  destruct global_variance_gen as [| |v] => //.
  all: [> intros _ | intros ->; cbn ..]; auto.
  1: intro H; apply: cmp_instance_opt_variance; move: H => /=.
  - now apply cmp_universe_instance_impl.
  - intros [H | H]; [left | right].
    1: eapply cmp_universe_instance_impl; tea.
    eapply cmp_universe_instance_variance_impl; eassumption.
Qed.

Lemma global_variance_empty gr napp env : env.(declarations) = [] -> global_variance env gr napp = AllEqual.
Proof.
  destruct env; cbn => ->. destruct gr; auto.
Qed.

(** Pure syntactic equality, without cumulative inductive types subtyping *)

#[global]
Instance cmp_global_instance_empty_impl Σ cmp_universe cmp_universe' pb pb' gr napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  subrelation (cmp_global_instance empty_global_env cmp_universe pb gr napp) (cmp_global_instance Σ cmp_universe' pb' gr napp').
Proof.
  intros he t t'.
  unfold cmp_global_instance_gen.
  rewrite global_variance_empty //.
  intro H; apply: cmp_instance_opt_variance; move: H => /=.
  now apply cmp_universe_instance_impl.
Qed.

(* Subject to change *)
Definition contexts_pres_eq (Γ Γ' : context) := All2 (fun d d' => d.(decl_name).(binder_relevance) = d'.(decl_name).(binder_relevance)) Γ Γ'.

#[global] Instance contexts_pres_eq_equiv : Equivalence contexts_pres_eq.
Proof.
  split.
  - intro. apply All2_refl. reflexivity.
  - apply All2_symP. intros d d'; now symmetry.
  - apply All2_trans. intros d d' d''; now etransitivity.
Qed.

Lemma eq_term_upto_univ_ctx_impl Σ Γ Γ' cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  contexts_pres_eq Γ Γ' ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp) (eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' Γ' pb' napp').
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb eqctx hnapp t t' h.
  induction h in Γ', eqctx, napp', hnapp, pb', univ_sub_pb, sort_sub_pb |- *.
  all: try solve [constructor; eauto using cmp_universe_instance_impl' ].
  - constructor.
    eapply All2_impl; tea.
    intros ??[]; eauto.
  - constructor; eauto.
    eapply IHh1. all:auto with arith.
  - constructor.
    eapply cmp_global_instance_impl. 4:eauto. all:auto.
  - constructor.
    eapply cmp_global_instance_impl. 4:eauto. all:eauto.
  - constructor; eauto.
    eapply IHh2; eauto.
    constructor; tas. reflexivity.
  - constructor; eauto.
    eapply IHh2; eauto.
    constructor; tas. reflexivity.
  - constructor; eauto.
    eapply IHh3; eauto.
    constructor; tas. reflexivity.
  - constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
    * eapply cmp_universe_instance_impl'; eauto.
    * eapply b0; eauto.
      apply All2_app; tas. reflexivity.
    * eapply b1; eauto.
      apply All2_app; tas. reflexivity.
  - constructor.
    eapply All2_impl; tea.
    intros d d' ([e ihe]&[e0 ihe0]&?&?). repeat split; eauto.
    eapply ihe0; eauto. apply All2_app; tas. reflexivity.
  - constructor.
    eapply All2_impl; tea.
    intros d d' ([e ihe]&[e0 ihe0]&?&?). repeat split; eauto.
    eapply ihe0; eauto. apply All2_app; tas. reflexivity.
  - constructor.
    destruct X; constructor; intuition eauto.
    solve_all.
Qed.


Lemma eq_term_upto_univ_ctx_cheat Σ Γ Γ' cmp_universe cmp_sort pb napp :
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp) (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ' pb napp).
Proof.
  intros t t' h.
  induction h in Γ' |- *.
  all: try solve [constructor; eauto ].
  all: try solve [constructor; unfold eq_mfixpoint in *; solve_all; eauto ].
  - constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
  - constructor.
    destruct X; constructor; intuition eauto.
    solve_all.
Qed.

Lemma eq_term_upto_univ_contexts_pres_eq Σ Γ Γ' cmp_universe cmp_sort pb napp :
  contexts_pres_eq Γ Γ' ->
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp) (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ' pb napp).
Proof.
  move/eq_term_upto_univ_ctx_impl.
  apply. auto.
Qed.

Lemma eq_context_upto_pres_eq Σ Γ Γ' cmp_universe0 cmp_sort0 pb0 :
  eq_context_upto Σ cmp_universe0 cmp_sort0 pb0 Γ Γ' ->
  contexts_pres_eq Γ Γ'.
Proof.
  induction 1; constructor; auto.
  destruct p; auto.
Qed.

Lemma eq_term_upto_univ_eq_ctx_upto_names Σ Γ Γ' cmp_universe cmp_sort pb napp :
  eq_context_upto_names Γ Γ' ->
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp) (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ' pb napp).
Proof.
  intro X.
  apply eq_term_upto_univ_contexts_pres_eq.
  induction X; constructor; tas.
  destruct r; assumption.
Qed.

Lemma eq_term_upto_univ_eq_ctx Σ Γ Γ' cmp_universe0 cmp_sort0 pb0 cmp_universe cmp_sort pb napp :
  eq_context_upto Σ cmp_universe0 cmp_sort0 pb0 Γ Γ' ->
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp) (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ' pb napp).
Proof.
  move/eq_context_upto_pres_eq.
  apply eq_term_upto_univ_contexts_pres_eq.
Qed.

Lemma eq_term_upto_univ_eq_ctx_rev Σ Γ Γ' cmp_universe0 cmp_sort0 pb0 cmp_universe cmp_sort pb napp :
  eq_context_upto Σ cmp_universe0 cmp_sort0 pb0 Γ' Γ ->
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp) (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ' pb napp).
Proof.
  move/eq_context_upto_pres_eq/symmetry/eq_term_upto_univ_contexts_pres_eq.
  apply.
Qed.

#[global]
Instance eq_term_upto_univ_impl Σ Γ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp) (eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' Γ pb' napp').
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb hnapp t t' h.
  induction h in napp', hnapp, pb', univ_sub_pb, sort_sub_pb |- *.
  all: try solve [constructor; eauto using cmp_universe_instance_impl' ].
  - constructor.
    eapply All2_impl; tea.
    intros ??[]; eauto.
  - constructor; eauto.
    eapply IHh1. all:auto with arith.
  - constructor.
    eapply cmp_global_instance_impl. 4:eauto. all:auto.
  - constructor.
    eapply cmp_global_instance_impl. 4:eauto. all:eauto.
  - constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
    * eapply cmp_universe_instance_impl'; eauto.
  - constructor.
    eapply All2_impl; tea.
    intros d d' ([e ihe]&[e0 ihe0]&?&?). repeat split; eauto.
  - constructor.
    eapply All2_impl; tea.
    intros d d' ([e ihe]&[e0 ihe0]&?&?). repeat split; eauto.
  - constructor.
    destruct X; constructor; intuition eauto.
    solve_all.
Qed.

#[global]
Instance eq_term_upto_univ_empty_impl Σ Γ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  subrelation (eq_term_upto_univ_napp empty_global_env cmp_universe cmp_sort Γ pb napp) (eq_term_upto_univ_napp Σ cmp_universe' cmp_sort' Γ pb' napp').
Proof.
  intros univ_sub_conv univ_sub_pb sort_sub_conv sort_sub_pb t t' h.
  induction h in napp', pb', univ_sub_pb, sort_sub_pb |- *.
  all: try solve [constructor; eauto using cmp_universe_instance_impl' ].
  - constructor.
    eapply All2_impl; tea.
    intros ??[]; eauto.
  - constructor.
    eapply cmp_global_instance_empty_impl. 2:eauto. all:auto.
  - constructor.
    eapply cmp_global_instance_empty_impl. 2:eauto. all:eauto.
  - constructor; unfold eq_predicate, eq_branches, eq_branch in *; eauto; solve_all.
    * eapply cmp_universe_instance_impl'; eauto.
  - constructor.
    eapply All2_impl; tea.
    intros d d' ([e ihe]&[e0 ihe0]&?&?). repeat split; eauto.
  - constructor.
    eapply All2_impl; tea.
    intros d d' ([e ihe]&[e0 ihe0]&?&?). repeat split; eauto.
  - constructor.
    destruct X; constructor; intuition eauto.
    solve_all.
Qed.

#[global]
Instance eq_term_upto_univ_leq Σ cmp_universe cmp_sort Γ pb napp napp' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ Conv napp) (eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp').
Proof.
  intros H. eapply eq_term_upto_univ_impl; exact _.
Qed.

#[global]
Instance eq_term_leq_term {cf:checker_flags} Σ φ Γ
  : subrelation (eq_term Σ φ Γ) (leq_term Σ φ Γ).
Proof.
  eapply eq_term_upto_univ_leq; auto; exact _.
Qed.

#[global]
Instance eq_term_compare_term {cf:checker_flags} Σ φ Γ pb
  : subrelation (eq_term Σ φ Γ) (compare_term Σ φ Γ pb).
Proof.
  eapply eq_term_upto_univ_leq; auto; exact _.
Qed.

#[global]
Instance eq_term_compare_term_napp {cf:checker_flags} Σ φ Γ pb napp
  : subrelation (eq_term Σ φ Γ) (compare_term_napp Σ φ Γ pb napp).
Proof.
  eapply eq_term_upto_univ_leq; auto with arith; exact _.
Qed.

Lemma eq_context_upto_impl Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  subrelation (eq_context_upto Σ cmp_universe cmp_sort pb) (eq_context_upto Σ cmp_universe' cmp_sort' pb').
Proof.
  intros.
  apply eq_context_gen_impl.
  all: intro; apply eq_term_upto_univ_impl; tc.
  all: auto.
Qed.

#[global]
Instance eq_context_upto_leq Σ cmp_universe cmp_sort pb :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  subrelation (eq_context_upto Σ cmp_universe cmp_sort Conv) (eq_context_upto Σ cmp_universe cmp_sort pb).
Proof.
  intros H. eapply eq_context_upto_impl; exact _.
Qed.

Lemma eq_context_upto_rel_impl Σ cmp_universe cmp_universe' cmp_sort cmp_sort' pb pb' Γ :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe' Conv) ->
  RelationClasses.subrelation (cmp_universe pb) (cmp_universe' pb') ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort' Conv) ->
  RelationClasses.subrelation (cmp_sort pb) (cmp_sort' pb') ->
  subrelation (eq_context_upto_rel Σ cmp_universe cmp_sort pb Γ) (eq_context_upto_rel Σ cmp_universe' cmp_sort' pb' Γ).
Proof.
  intros.
  apply eq_context_gen_impl.
  all: intro; apply eq_term_upto_univ_impl; tc.
  all: auto.
Qed.

#[global]
Instance eq_context_upto_rel_leq Σ cmp_universe cmp_sort pb Γ :
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  RelationClasses.subrelation (cmp_sort Conv) (cmp_sort pb) ->
  subrelation (eq_context_upto_rel Σ cmp_universe cmp_sort Conv Γ) (eq_context_upto_rel Σ cmp_universe cmp_sort pb Γ).
Proof.
  intros H. eapply eq_context_upto_rel_impl; exact _.
Qed.

Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
| rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
| rel_none : rel_option R None None.

Derive Signature NoConfusion for rel_option.

Definition eq_decl_upto_gen Σ cmp_universe cmp_sort Γ pb d d' : Type :=
  eq_binder_annot d.(decl_name) d'.(decl_name) *
  rel_option (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) d.(decl_body) d'.(decl_body) *
  eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb d.(decl_type) d'.(decl_type).

Lemma compare_decls_eq_decl_up_to_gen Σ cmp_universe cmp_sort Γ pb d d' :
  compare_decls (fun pb => eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb) pb d d' ->
  eq_decl_upto_gen Σ cmp_universe cmp_sort Γ pb d d'.
Proof.
  intros [].
  all: repeat split; tas.
  all: constructor; tas.
Qed.

Lemma eq_context_upto_cat Σ cmp_universe cmp_sort pb Γ Δ Γ' Δ' :
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Γ' ->
  eq_context_upto_rel Σ cmp_universe cmp_sort pb Γ Δ Δ' ->
  eq_context_upto Σ cmp_universe cmp_sort pb (Γ ,,, Δ) (Γ' ,,, Δ').
Proof. intros. eapply All2_fold_app; eauto. Qed.

Lemma eq_context_upto_length {Σ cmp_universe cmp_sort pb Γ Δ} :
    eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
    #|Γ| = #|Δ|.
Proof.
  apply All2_fold_length.
Qed.

Lemma eq_context_upto_nth_error Σ cmp_universe cmp_sort pb ctx ctx' n :
  eq_context_upto Σ cmp_universe cmp_sort pb ctx ctx' ->
  rel_option (eq_decl_upto_gen Σ cmp_universe cmp_sort (skipn (S n) ctx) pb) (nth_error ctx n) (nth_error ctx' n).
Proof.
  induction 1 in n |- *.
  - rewrite nth_error_nil. constructor.
  - destruct n; simpl; auto.
    constructor. now apply compare_decls_eq_decl_up_to_gen.
Qed.

(** ws_cumul_pb of binder annotations *)
Notation eq_annots Γ Δ :=
  (Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ Δ).

Lemma eq_context_upto_names_binder_annot Γ Δ :
  eq_context_upto_names Γ Δ -> eq_annots (forget_types Γ) Δ.
Proof.
  induction 1; constructor; auto.
  destruct r; auto.
Qed.

Lemma eq_annots_fold (Γ : list aname) (f : nat -> term -> term) (Δ : context) :
  eq_annots Γ (fold_context_k f Δ) <-> eq_annots Γ Δ.
Proof.
  induction Δ in Γ |- *.
  - cbn; auto. reflexivity.
  - rewrite fold_context_k_snoc0 /=.
    destruct Γ; split; intros H; depelim H; constructor; auto;
    now apply IHΔ.
Qed.

Lemma eq_annots_subst_context (Γ : list aname) s k (Δ : context) :
  eq_annots Γ (subst_context s k Δ) <-> eq_annots Γ Δ.
Proof.
  apply eq_annots_fold.
Qed.

Lemma eq_annots_lift_context (Γ : list aname) n k (Δ : context) :
  eq_annots Γ (lift_context n k Δ) <-> eq_annots Γ Δ.
Proof.
  apply eq_annots_fold.
Qed.

#[global]
Instance Forall2_ext {A B} :
  Proper (pointwise_relation A (pointwise_relation B iff) ==> eq ==> eq ==> iff) (@Forall2 A B).
Proof.
  intros f g Hfg ?? -> ?? ->.
  split; intro; eapply Forall2_impl; tea; apply Hfg.
Qed.

Lemma eq_annots_subst_instance_ctx (Γ : list aname) u (Δ : context) :
  eq_annots Γ Δ@[u] <-> eq_annots Γ Δ.
Proof.
  etransitivity. eapply Forall2_map_right.
  eapply Forall2_ext; auto.
  intros x y; reflexivity.
Qed.

Lemma eq_annots_inst_case_context (Γ : list aname) pars puinst (ctx : context) :
  eq_annots Γ ctx <->
  eq_annots Γ (PCUICCases.inst_case_context pars puinst ctx).
Proof.
  etransitivity. symmetry; eapply (eq_annots_subst_instance_ctx _ puinst).
  etransitivity.
  symmetry; eapply (eq_annots_subst_context _ (List.rev pars) 0).
  reflexivity.
Qed.

Lemma eq_context_upto_names_eq_context_upto Σ cmp_universe cmp_sort pb :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  subrelation eq_context_upto_names (eq_context_upto Σ cmp_universe cmp_sort pb).
Proof.
  intros ** Δ Δ'.
  move/(eq_context_upto_names_gen _ _ pb).
  apply eq_context_gen_impl.
  all: intros Ξ x y <-; reflexivity.
Qed.

Lemma eq_context_upto_names_eq_context_upto_rel Σ cmp_universe cmp_sort pb Γ :
  RelationClasses.Reflexive (cmp_universe Conv) ->
  RelationClasses.Reflexive (cmp_universe pb) ->
  RelationClasses.Reflexive (cmp_sort Conv) ->
  RelationClasses.Reflexive (cmp_sort pb) ->
  subrelation eq_context_upto_names (eq_context_upto_rel Σ cmp_universe cmp_sort pb Γ).
Proof.
  intros ** Δ Δ'.
  move/(eq_context_upto_names_gen _ _ pb).
  apply eq_context_gen_impl.
  all: intros Ξ x y <-; reflexivity.
Qed.

Lemma eq_context_upto_names_map2_set_binder_name_eq nas Γ Δ :
  eq_context_upto_names Γ Δ ->
  map2 PCUICEnvironment.set_binder_name nas Γ =
  map2 PCUICEnvironment.set_binder_name nas Δ.
Proof.
  induction 1 in nas |- *; cbn; auto.
  destruct nas; cbn; auto.
  f_equal. destruct r; subst; unfold set_binder_name; f_equal.
  apply IHX.
Qed.

Lemma trans_eq_context_upto_names trans Γ Δ :
  eq_context_upto_names Γ Δ ->
  eq_context_upto_names (map (map_decl trans) Γ) (map (map_decl trans) Δ).
Proof.
  intro.
  eapply All2_map. solve_all.
  destruct X; cbn; subst; constructor; auto.
Qed.

Lemma eq_context_upto_names_fold (f : nat -> term -> term) Γ Δ :
  eq_context_upto_names Γ Δ ->
  eq_context_upto_names (fold_context_k f Γ) (fold_context_k f Δ).
Proof.
  induction 1.
  - cbn; auto.
  - rewrite !fold_context_k_snoc0 /=.
    constructor; auto.
    rewrite -(All2_length X).
    destruct r; now constructor.
Qed.

Lemma eq_context_upto_names_smash_context {Γ Δ} :
  eq_context_upto_names Γ Δ ->
  eq_context_upto_names (smash_context [] Γ) (smash_context [] Δ).
Proof.
  assert (eq_context_upto_names [] []) as X by constructor. move: X.
  set (Γ0 := []) at 1 3. set (Δ0 := []). clearbody Γ0 Δ0. intro X.
  induction 1 in Γ0, Δ0, X |- *; cbn; try constructor; tas.
  destruct r; cbn; apply IHX0.
  - apply All2_app; tas. repeat constructor. assumption.
  - now apply eq_context_upto_names_fold.
Qed.

Lemma eq_context_upto_names_context_assumptions {Γ Δ} :
  eq_context_upto_names Γ Δ ->
  context_assumptions Γ = context_assumptions Δ.
Proof.
  induction 1; simpl; auto.
  destruct r => /= //; try lia.
Qed.

Lemma eq_context_upto_names_extended_subst {Γ Δ n} :
  eq_context_upto_names Γ Δ ->
  extended_subst Γ n = extended_subst Δ n.
Proof.
  induction 1 in n |- *; cbn; auto.
  destruct r; subst; cbn. f_equal; auto.
  rewrite IHX.
  now rewrite (eq_context_upto_names_context_assumptions X).
Qed.

Lemma eq_context_upto_names_closedn_ctx {Γ Δ k} :
  eq_context_upto_names Γ Δ ->
  closedn_ctx k Γ = closedn_ctx k Δ.
Proof.
  induction 1 in k |- *; cbnr.
  rewrite IHX -(All2_length X); f_equal.
  destruct r; cbnr.
Qed.

Lemma eq_context_upto_names_on_free_vars_eq P (Γ Δ : context) :
  eq_context_upto_names Γ Δ ->
  on_free_vars_ctx P Γ = on_free_vars_ctx P Δ.
Proof.
  induction 1; cbn; auto.
  rewrite !alli_app /= !andb_true_r.
  f_equal; tas.
  len. rewrite -(All2_length X).
  destruct r; cbn in *; subst; auto.
Qed.

Lemma eq_context_upto_names_on_free_vars P Γ Δ :
  eq_context_upto_names Γ Δ ->
  on_free_vars_ctx P Γ -> on_free_vars_ctx P Δ.
Proof.
  move/eq_context_upto_names_on_free_vars_eq => -> //.
Qed.

(** Currently provable, but not if we add eta / sprop *)
Lemma eq_term_upto_univ_napp_on_free_vars_eq Σ P cmp_universe cmp_sort Γ pb napp t u :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp t u ->
  on_free_vars P t = on_free_vars P u.
Proof.
  induction 1 in P |- *; intros; cbn; eauto.
  all: try solve [rtoProp; solve_all].
  - induction X => //=.
  f_equal; tas. apply r.
  - destruct X as (Xp & Xu & Xc & Xr & Xr'). repeat apply (f_equal2 andb); eauto.
    + induction Xp => //=.
      f_equal; tas. apply r.
    + rewrite -(All2_length Xc) //.
    + rewrite -(All2_length Xp).
      rewrite !test_context_k_closed_on_free_vars_ctx.
      now apply eq_context_upto_names_on_free_vars_eq.
    + unfold eq_branches, eq_branch in *.
      rewrite -(All2_length Xp).
      induction X1 => //=.
      f_equal; tas. f_equal.
      * rewrite !test_context_k_closed_on_free_vars_ctx.
        now apply eq_context_upto_names_on_free_vars_eq.
      * erewrite All2_length; apply r.
  - unfold eq_mfixpoint, test_def in *.
    rewrite -(All2_length X). set N := #|mfix|. clearbody N.
    induction X => //=.
    f_equal; tas. f_equal; apply r.
  - unfold eq_mfixpoint, test_def in *.
    rewrite -(All2_length X). set N := #|mfix|. clearbody N.
    induction X => //=.
    f_equal; tas. f_equal; apply r.
  - destruct X; cbn in *; auto.
    repeat apply (f_equal2 andb).
    + induction a0 => //=.
      f_equal; tas. apply r.
    + apply p.
    + apply p0.
Qed.

Lemma eq_term_upto_univ_napp_on_free_vars Σ P cmp_universe cmp_sort Γ pb napp u v :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  on_free_vars P u -> on_free_vars P v.
Proof.
  move/eq_term_upto_univ_napp_on_free_vars_eq => -> //.
Qed.

Lemma eq_term_upto_univ_napp_closedn_eq Σ k cmp_universe cmp_sort Γ pb napp t u :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp t u ->
  closedn k t = closedn k u.
Proof.
  induction 1 in k |- *; intros; cbn; eauto.
  all: try solve [rtoProp; solve_all].
  - induction X => //=.
  f_equal; tas. apply r.
  - destruct X as (Xp & Xu & Xc & Xr & Xr'). repeat apply (f_equal2 andb); eauto.
    + induction Xp => //=.
      f_equal; tas. apply r.
    + rewrite -(All2_length Xp).
      now apply eq_context_upto_names_closedn_ctx.
    + now rewrite -(All2_length Xc).
    + unfold eq_branches, eq_branch, test_branch_k in *.
      rewrite -(All2_length Xp).
      induction X1 => //=.
      f_equal; tas. unfold test_branch_k. f_equal.
      * now apply eq_context_upto_names_closedn_ctx.
      * erewrite All2_length; apply r.
  - unfold eq_mfixpoint, test_def in *.
    rewrite -(All2_length X). set N := #|mfix|. clearbody N.
    induction X => //=.
    f_equal; tas. f_equal; apply r.
  - unfold eq_mfixpoint, test_def in *.
    rewrite -(All2_length X). set N := #|mfix|. clearbody N.
    induction X => //=.
    f_equal; tas. f_equal; apply r.
  - destruct X; cbn in *; auto.
    repeat apply (f_equal2 andb).
    + induction a0 => //=.
      f_equal; tas. apply r.
    + apply p.
    + apply p0.
Qed.

Lemma eq_term_upto_univ_napp_closedn k Σ cmp_universe cmp_sort Γ pb napp u v :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  closedn k u -> closedn k v.
Proof.
  move/eq_term_upto_univ_napp_closedn_eq => -> //.
Qed.

Lemma eq_term_upto_univ_napp_wf_term_eq Σ cmp_universe cmp_sort Γ pb napp u v :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  wf_term u = wf_term v.
Proof.
  induction 1; intros; inv_wf_term; cbn; eauto.
  all: try solve [rtoProp; solve_all].
  - induction X => //=.
    f_equal; tas. apply r.
  - destruct X as (Xp & Xu & Xc & Xr & Xr'). repeat apply (f_equal2 andb); eauto.
    + induction Xp => //=.
      f_equal; tas. apply r.
    + rewrite -(All2_length Xp).
      now apply eq_context_upto_names_closedn_ctx.
    + unfold eq_branches, eq_branch in *.
      rewrite -(All2_length Xp).
      induction X1 => //=.
      f_equal; tas. f_equal.
      * eapply eq_context_upto_names_closedn_ctx. apply r.
      * apply r.
  - unfold eq_mfixpoint, test_def in *.
    induction X => //=.
    f_equal; tas. f_equal; apply r.
  - unfold eq_mfixpoint, test_def in *.
    induction X => //=.
    f_equal; tas. f_equal; apply r.
  - destruct X; cbn in *; auto.
    repeat apply (f_equal2 andb).
    + induction a0 => //=.
      f_equal; tas. apply r.
    + apply p.
    + apply p0.
Qed.

Lemma eq_term_upto_univ_napp_wf_term Σ cmp_universe cmp_sort Γ pb napp u v :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  wf_term u -> wf_term v.
Proof.
  move/eq_term_upto_univ_napp_wf_term_eq => -> //.
Qed.

Lemma eq_context_upto_wf_term_eq Σ cmp_universe cmp_sort pb Γ Δ :
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
  wf_term_ctx Γ = wf_term_ctx Δ.
Proof.
  induction 1; intros; inv_wf_term; cbn in *; eauto.
  f_equal; tas.
  destruct p; cbn. 2: unfold test_decl; cbn; f_equal.
  all: eapply eq_term_upto_univ_napp_wf_term_eq; tea.
Qed.

Lemma eq_context_upto_wf_term Σ cmp_universe cmp_sort pb Γ Δ :
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Δ ->
  wf_term_ctx Γ -> wf_term_ctx Δ.
Proof.
  move/eq_context_upto_wf_term_eq => -> //.
Qed.

(** ** Behavior on mkApps and it_mkLambda_or_LetIn **  *)

Lemma eq_term_eq_term_napp Σ cmp_universe cmp_sort Γ pb napp t t' :
  eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb t t' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp t t'.
Proof.
  intros. eapply eq_term_upto_univ_impl. 6:eauto.
  5:auto with arith. all:typeclasses eauto.
Qed.

Lemma leq_term_leq_term_napp Σ cmp_universe cmp_sort Γ pb napp t t' :
  eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb t t' ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp t t'.
Proof.
  intros. eapply eq_term_upto_univ_impl. 6:eauto.
  5:auto with arith. all:try typeclasses eauto.
Qed.

Lemma eq_term_upto_univ_napp_mkApps Σ cmp_universe cmp_sort Γ pb u1 l1 u2 l2 napp :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb (#|l1| + napp) u1 u2 ->
    All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) l1 l2 ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros hu hl. induction l1 in napp, u1, u2, l2, hu, hl |- *.
  - inversion hl. subst. assumption.
  - inversion hl. subst. simpl.
    eapply IHl1.
    + constructor. all: assumption.
    + assumption.
Qed.

Lemma eq_term_upto_univ_napp_mkApps_l_inv Σ cmp_universe cmp_sort Γ pb napp u l t :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb (#|l| + napp) u u' *
      All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) l l' *
      (t = mkApps u' l').
Proof.
  intros h. induction l in napp, u, t, h, pb |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma eq_term_upto_univ_napp_mkApps_r_inv Σ cmp_universe cmp_sort Γ pb napp u l t :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp t (mkApps u l) ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb (#|l| + napp) u' u *
      All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) l' l *
      (t = mkApps u' l').
Proof.
  intros h. induction l in napp, u, t, h, pb |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps Σ cmp_universe cmp_sort Γ pb u1 l1 u2 l2 :
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb #|l1| u1 u2 ->
    All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) l1 l2 ->
    eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros; apply eq_term_upto_univ_napp_mkApps; rewrite ?Nat.add_0_r; auto.
Qed.

Lemma eq_term_upto_univ_mkApps_l_inv Σ cmp_universe cmp_sort Γ pb u l t :
    eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb #|l| u u' *
      All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) l l' *
      (t = mkApps u' l').
Proof.
  intros H; apply eq_term_upto_univ_napp_mkApps_l_inv in H; rewrite ?Nat.add_0_r in H; auto.
Qed.

Lemma eq_term_upto_univ_mkApps_r_inv Σ cmp_universe cmp_sort Γ pb u l t :
    eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb t (mkApps u l) ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb #|l| u' u *
      All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) l' l *
      (t = mkApps u' l').
Proof.
  intros H; apply eq_term_upto_univ_napp_mkApps_r_inv in H;
    rewrite Nat.add_0_r in H; auto.
Qed.

Lemma eq_term_upto_univ_isApp Σ cmp_universe cmp_sort Γ pb napp u v :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb napp u v ->
  isApp u = isApp v.
Proof.
  induction 1.
  all: reflexivity.
Qed.

Lemma decompose_app_upto Σ cmp_universe cmp_sort Γ pb u v hd args :
  eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb u v ->
  decompose_app u = (hd, args) ->
  ∑ hd' args', v = mkApps hd' args' ×
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb #|args| hd hd' ×
  negb (isApp hd') ×
  All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) args args'.
Proof using Type.
  intros eq dapp.
  pose proof (decompose_app_notApp _ _ _ dapp).
  apply decompose_app_inv in dapp as ->.
  eapply eq_term_upto_univ_mkApps_l_inv in eq as [u' [l' [[eqh eqtl] ->]]].
  eexists _, _; intuition eauto.
  revert H.
  inv eqh; simpl in *; try discriminate; auto.
Qed.

Lemma eq_term_upto_univ_it_mkLambda_or_LetIn Σ cmp_universe cmp_sort pb Γ Δ Δ' u v :
  eq_context_upto_rel Σ cmp_universe cmp_sort Conv Γ Δ Δ' ->
  eq_term_upto_univ Σ cmp_universe cmp_sort (Γ ,,, Δ) pb u v ->
  eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb (it_mkLambda_or_LetIn Δ u) (it_mkLambda_or_LetIn Δ' v).
Proof.
  intros eq h.
  induction eq in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply IHeq => //.
    destruct p; cbn; constructor ; tas; try reflexivity.
Qed.

Lemma eq_term_upto_univ_it_mkProd_or_LetIn Σ cmp_universe cmp_sort pb Γ Δ Δ' u v :
  eq_context_upto_rel Σ cmp_universe cmp_sort Conv Γ Δ Δ' ->
  eq_term_upto_univ Σ cmp_universe cmp_sort (Γ ,,, Δ) pb u v ->
  eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb (it_mkProd_or_LetIn Δ u) (it_mkProd_or_LetIn Δ' v).
Proof.
  intros eq h.
  induction eq in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply IHeq => //.
    destruct p; cbn; constructor ; tas; try reflexivity.
Qed.

Lemma eq_term_it_mkLambda_or_LetIn_inv {cf:checker_flags} Σ φ Γ Δ u v :
    eq_term Σ φ Γ (it_mkLambda_or_LetIn Δ u) (it_mkLambda_or_LetIn Δ v) ->
    eq_term Σ φ (Γ ,,, Δ) u v.
Proof.
  revert u v. induction Δ as [| [na [b|] A] Δ ih ] ; intros u v h.
  - assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
Qed.

Lemma eq_term_it_mkProd_or_LetIn_inv {cf:checker_flags} Σ φ Γ Δ u v :
    eq_term Σ φ Γ (it_mkProd_or_LetIn Δ u) (it_mkProd_or_LetIn Δ v) ->
    eq_term Σ φ (Γ ,,, Δ) u v.
Proof.
  revert u v. induction Δ as [| [na [b|] A] Δ ih ] ; intros u v h.
  - assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
Qed.

Lemma eq_term_upto_univ_mkApps_inv Σ cmp_universe cmp_sort Γ pb u l u' l' :
  isApp u = false ->
  isApp u' = false ->
  eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb (mkApps u l) (mkApps u' l') ->
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort Γ pb #|l| u u' * All2 (eq_term_upto_univ Σ cmp_universe cmp_sort Γ Conv) l l'.
Proof.
  intros hu hu' h.
  apply eq_term_upto_univ_mkApps_l_inv in h as hh.
  destruct hh as [v [args [[h1 h2] h3]]].
  apply eq_term_upto_univ_isApp in h1 as hh1. rewrite hu in hh1.
  apply mkApps_notApp_inj in h3 ; auto.
  destruct h3 as [? ?]. subst. split ; auto.
Qed.

Lemma isConstruct_app_eq_term_l Σ cmp_universe cmp_sort Γ pb u v :
    isConstruct_app u ->
    eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb u v ->
    isConstruct_app v.
Proof.
  intros h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e1 in h. cbn in h.
  rewrite e2. cbn.
  destruct t1 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - reflexivity.
  - eapply decompose_app_notApp. eassumption.
Qed.

Lemma isConstruct_app_eq_term_r Σ cmp_universe cmp_sort Γ pb u v :
    isConstruct_app v ->
    eq_term_upto_univ Σ cmp_universe cmp_sort Γ pb u v ->
    isConstruct_app u.
Proof.
  intros h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e2 in h. cbn in h.
  rewrite e1. cbn.
  destruct t2 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - eapply decompose_app_notApp. eassumption.
  - reflexivity.
Qed.
