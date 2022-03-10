
(* Distributed under the terms of the MIT license. *)
From Coq Require Import Lia MSetList OrderedTypeAlt OrderedTypeEx MSetAVL MSetFacts MSetProperties.
From MetaCoq.Template Require Import utils.
From Coq Require Import ssreflect.

Local Open Scope string_scope2.
Definition compare_ident := string_compare.

(** ** Reification of names ** *)

(** [Comment taken from Coq's code]
    - Id.t is the type of identifiers, that is morally a subset of strings which
      only contains Unicode characters of the Letter kind (and a few more).
      => [ident]
    - Name.t is an ad-hoc variant of Id.t option allowing to handle optionally
      named objects.
      => [name]
    - DirPath.t represents generic paths as sequences of identifiers.
      => [dirpath]
    - Label.t is an equivalent of Id.t made distinct for semantical purposes.
      => [ident]
    - ModPath.t are module paths.
      => [modpath]
    - KerName.t are absolute names of objects in Coq.
      => [kername]

    And also :
    - Constant.t => [kername]
    - variable => [ident]
    - MutInd.t => [kername]
    - inductive => [inductive]
    - constructor => [inductive * nat]
    - Projection.t => [projection]
    - GlobRef.t => global_reference

    Finally, we define the models of primitive types (uint63 and floats64).
*)

Definition ident   := string. (* e.g. nat *)
Definition qualid  := string. (* e.g. Datatypes.nat *)

(** Type of directory paths. Essentially a list of module identifiers. The
    order is reversed to improve sharing. E.g. A.B.C is ["C";"B";"A"] *)
Definition dirpath := list ident.

Module IdentOT := StringOT.

Module DirPathOT := ListOrderedType IdentOT.

#[global] Instance dirpath_eqdec : Classes.EqDec dirpath := _.

Definition string_of_dirpath (dp : dirpath) : string := 
  String.concat "." (List.rev dp).

(** The module part of the kernel name.
    - MPfile is for toplevel libraries, i.e. .vo files
    - MPbound are parameters of functors
    - MPdot is for submodules
*)
Inductive modpath :=
| MPfile  (dp : dirpath)
| MPbound (dp : dirpath) (id : ident) (i : nat)
| MPdot   (mp : modpath) (id : ident).
Derive NoConfusion for modpath.

Fixpoint string_of_modpath (mp : modpath) : string :=
  match mp with
  | MPfile dp => string_of_dirpath dp
  | MPbound dp id _ => string_of_dirpath dp ^ "." ^ id
  | MPdot mp id => string_of_modpath mp ^ "." ^ id
  end.

(** The absolute names of objects seen by kernel *)
Definition kername := modpath × ident.

Definition string_of_kername (kn : kername) :=
  string_of_modpath kn.1 ^ "." ^ kn.2.

(* Eval compute in DirPathOT.compare ["foo"; "bar"] ["baz"].
 *)

Module ModPathComp.
  Definition t := modpath.

  Definition eq := @eq modpath.
  Definition eq_univ : RelationClasses.Equivalence eq := _.

  Definition mpbound_compare dp id k dp' id' k' :=
    compare_cont (DirPathOT.compare dp dp')
      (compare_cont (IdentOT.compare id id') (Nat.compare k k')).

  Fixpoint compare mp mp' :=
    match mp, mp' with
    | MPfile dp, MPfile dp' => DirPathOT.compare dp dp'
    | MPbound dp id k, MPbound dp' id' k' => 
      mpbound_compare dp id k dp' id' k'
    | MPdot mp id, MPdot mp' id' => 
      compare_cont (compare mp mp') (IdentOT.compare id id')
    | MPfile _, _ => Gt
    | _, MPfile _ => Lt
    | MPbound _ _ _, _ => Gt
    | _, MPbound _ _ _ => Lt
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma nat_compare_sym : forall x y, Nat.compare x y = CompOpp (Nat.compare y x).
  Proof.
    intros; apply PeanoNat.Nat.compare_antisym.
  Qed.

  Lemma compare_eq x y : x ?= y = Eq -> x = y.
  Proof.
    induction x in y |- *; destruct y; simpl; auto; try congruence.
    intros c. eapply DirPathOT.compare_eq in c; now subst.
    unfold mpbound_compare.
    destruct (DirPathOT.compare dp dp0) eqn:eq => //.
    destruct (IdentOT.compare id id0) eqn:eq' => //.
    destruct (Nat.compare i i0) eqn:eq'' => //.
    apply DirPathOT.compare_eq in eq.
    apply string_compare_eq in eq'.
    apply PeanoNat.Nat.compare_eq in eq''. congruence.
    destruct (x ?= y) eqn:eq; try congruence.
    specialize (IHx _ eq). subst.
    now intros c; apply string_compare_eq in c; subst.
    all:simpl; discriminate.
  Qed.

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    apply DirPathOT.compare_sym.
    unfold mpbound_compare.
    rewrite DirPathOT.compare_sym.
    rewrite IdentOT.compare_sym.
    destruct (DirPathOT.compare dp dp0); auto.
    simpl. destruct (IdentOT.compare id id0); simpl; auto.
    apply nat_compare_sym.
    rewrite IHx.
    destruct (x ?= y); simpl; auto.
    apply IdentOT.compare_sym.
  Qed.
 
  Lemma nat_compare_trans :
    forall c x y z, Nat.compare x y = c -> Nat.compare y z = c -> Nat.compare x z = c.
  Proof.
    intros c x y z.
    destruct (PeanoNat.Nat.compare_spec x y); subst; intros <-;
    destruct (PeanoNat.Nat.compare_spec y z); subst; try congruence;
    destruct (PeanoNat.Nat.compare_spec x z); subst; try congruence; lia.
  Qed.
 
  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c x y z. revert c.
    induction x in y, z |- *; destruct y, z; intros c; simpl; auto; try congruence.
    apply DirPathOT.compare_trans.
    unfold mpbound_compare.
    eapply compare_cont_trans; eauto using DirPathOT.compare_trans, DirPathOT.compare_eq.
    intros c'.
    eapply compare_cont_trans; eauto using StringOT.compare_trans, StringOT.compare_eq, nat_compare_trans.
    intros x y. apply StringOT.compare_eq.
    destruct (x ?= y) eqn:eq.
    apply compare_eq in eq. subst.
    destruct (IdentOT.compare id id0) eqn:eq.
    apply string_compare_eq in eq; red in eq; subst. all:intros <-; auto.
    destruct (y ?= z) eqn:eq'; auto.
    apply compare_eq in eq'; subst.
    intros eq'.
    eapply IdentOT.compare_trans; eauto. cbn in *.
    destruct (y ?= z) eqn:eq'; auto. cbn.
    now apply IdentOT.compare_trans.
    destruct (y ?= z) eqn:eq'; auto; cbn; try congruence.
    apply compare_eq in eq'; subst.
    intros eq'. now rewrite eq.
    rewrite (IHx _ _ _ eq eq') //.
    destruct (y ?= z) eqn:eq'; cbn; auto; try congruence.
    apply compare_eq in eq'; subst.
    intros eq'. now rewrite eq. 
    now rewrite (IHx _ _ _ eq eq').
  Qed.

End ModPathComp.

Module ModPathOT := OrderedType_from_Alt ModPathComp.

Program Definition modpath_eq_dec (x y : modpath) : { x = y } + { x <> y } := 
  match ModPathComp.compare x y with
  | Eq => left _
  | _ => right _
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  now eapply ModPathComp.compare_eq in Heq_anonymous.
Qed.
Next Obligation.
  rewrite ModPathOT.eq_refl in H. congruence.
Qed.

#[global] Instance modpath_EqDec : Classes.EqDec modpath := { eq_dec := modpath_eq_dec }.

Module KernameComp.
  Definition t := kername.

  Definition eq := @eq kername.
  Lemma eq_equiv : RelationClasses.Equivalence eq.
  Proof. apply _. Qed.

  Definition compare kn kn' := 
    match kn, kn' with
    | (mp, id), (mp', id') => 
      compare_cont (ModPathComp.compare mp mp') (IdentOT.compare id id')
    end.

  Infix "?=" := compare (at level 70, no associativity).

  Lemma compare_sym : forall x y, (y ?= x) = CompOpp (x ?= y).
  Proof.
    induction x; destruct y; simpl; auto.
    unfold compare_ident.
    rewrite ModPathComp.compare_sym IdentOT.compare_sym.
    destruct ModPathComp.compare, IdentOT.compare; auto.
  Qed.
   
  Lemma compare_trans :
    forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
  Proof.
    intros c [] [] [] => /=.
    eapply compare_cont_trans; eauto using ModPathComp.compare_trans, ModPathComp.compare_eq, 
      StringOT.compare_trans.
  Qed.
    
End KernameComp.

Module KernameOT.
 Include KernameComp.
 Module OT := OrderedType_from_Alt KernameComp.

 Definition lt := OT.lt.
 Global Instance lt_strorder : StrictOrder OT.lt.
  Proof.
    constructor.
    - intros x X. apply OT.lt_not_eq in X. apply X. apply OT.eq_refl.
    - intros x y z X1 X2. eapply OT.lt_trans; eauto.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) OT.lt.
  Proof.
    intros x x' H1 y y' H2.
    red in H1, H2. subst. reflexivity.
  Qed.

  Definition compare_spec : forall x y, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    induction x; destruct y.
    simpl. 
    destruct (ModPathComp.compare a m) eqn:eq.
    destruct (IdentOT.compare b i) eqn:eq'.
    all:constructor. red. eapply ModPathComp.compare_eq in eq. eapply string_compare_eq in eq'. congruence.
    all:hnf; simpl; rewrite ?eq ?eq' //.
    rewrite ModPathComp.compare_sym eq /= IdentOT.compare_sym eq' //.
    now rewrite ModPathComp.compare_sym eq /=.
  Defined.

  Lemma compare_eq x y : compare x y = Eq <-> x = y.
  Proof.
    split.
    - destruct (compare_spec x y); try congruence.
    - intros <-. destruct (compare_spec x x); auto.
      now apply irreflexivity in H.
      now apply irreflexivity in H.
  Qed.

  Program Definition eqb_dec (x y : t) : { x = y } + { x <> y } := 
    match compare x y with
    | Eq => left _
    | _ => right _
    end.
  Next Obligation.
    symmetry in Heq_anonymous.
    now eapply compare_eq in Heq_anonymous.
  Qed.
  Next Obligation.
    apply H. rewrite OT.eq_refl in H. congruence.
  Qed.

  Global Instance eq_dec : Classes.EqDec t := { eq_dec := eqb_dec }.

End KernameOT.

(* Local Open Scope string_scope.*)
(* Eval compute in KernameOT.compare (MPfile ["fdejrkjl"], "A") (MPfile ["lfrk;k"], "B"). *)
  
Module KernameSet := MSetAVL.Make KernameOT.
Module KernameSetFact := MSetFacts.WFactsOn KernameOT KernameSet.
Module KernameSetProp := MSetProperties.WPropertiesOn KernameOT KernameSet.

Lemma knset_in_fold_left {A} kn f (l : list A) acc : 
  KernameSet.In kn (fold_left (fun acc x => KernameSet.union (f x) acc) l acc) <->
  (KernameSet.In kn acc \/ exists a, In a l /\ KernameSet.In kn (f a)).
Proof.
  induction l in acc |- *; simpl.
  - split; auto. intros [H0|H0]; auto. now destruct H0.
  - rewrite IHl. rewrite KernameSet.union_spec.
    intuition auto.
    * right. now exists a; intuition auto.
    * destruct H0 as [a' [ina inkn]].
      right. now exists a'; intuition auto.
    * destruct H0 as [a' [ina inkn]].
      destruct ina as [<-|ina'];
      intuition auto. right. now exists a'.
Qed.
