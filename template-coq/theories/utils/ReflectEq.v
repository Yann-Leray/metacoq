From Coq Require Import ssreflect ssrbool List.
From Equations Require Import Equations.
Import ListNotations.

(* Some reflection / EqDec lemmata *)

Class ReflectEq A := {
  eqb : A -> A -> bool ;
  eqb_spec : forall x y : A, reflect (x = y) (eqb x y)
}.
Arguments eqb : simpl never.
Infix "==" := eqb (at level 70).

Lemma eqb_eq {A} `{ReflectEq A} (x y : A) : x == y -> x = y.
Proof.
  elim: eqb_spec; auto.
  discriminate.
Qed.

Lemma eqb_refl {A} {R : ReflectEq A} (x : A) : x == x.
Proof.
  destruct (eqb_spec x x); auto.
Qed.

Lemma neqb {A} {R : ReflectEq A} (x y : A) : ~~ (x == y) <-> x <> y.
Proof.
  destruct (eqb_spec x y); auto; subst; intuition auto.
Qed.

#[global] Instance ReflectEq_EqDec :
  forall A, ReflectEq A -> EqDec A.
Proof.
  intros A [eqb h] x y.
  destruct (h x y).
  - left. assumption.
  - right. assumption.
Defined.

Definition eq_dec_to_bool {A} `{EqDec A} x y :=
  match eq_dec x y with
  | left _ => true
  | right _ => false
  end.

(* Not an instance to avoid loops and making boolean definitions depend on sumbool ones *)
#[global]
Lemma EqDec_ReflectEq : forall A `{EqDec A}, ReflectEq A.
Proof.
  intros A h.
  unshelve econstructor.
  - eapply eq_dec_to_bool.
  - unfold eq_dec_to_bool.
    intros x y. destruct (eq_dec x y).
    all: constructor ; assumption.
Defined.

Ltac nodec :=
  let bot := fresh "bot" in
  try solve [ constructor ; intro bot ; inversion bot ; subst ; tauto ].

Definition eq_option {A} (eqA : A -> A -> bool) (u v : option A) : bool :=
  match u, v with
  | Some u, Some v => eqA u v
  | None, None => true
  | _, _ => false
  end.

#[global] Instance reflect_option : forall {A}, ReflectEq A -> ReflectEq (option A).
Proof.
  intros A RA. refine {| eqb := eq_option eqb |}.
  intros x y. destruct x, y.
  all: cbn.
  all: try solve [ constructor ; easy ].
  destruct (eqb_spec a a0) ; nodec.
  constructor. f_equal. assumption.
Defined.

Fixpoint eq_list {A} (eqA : A -> A -> bool) (l l' : list A) : bool :=
  match l, l' with
  | a :: l, a' :: l' =>
    if eqA a a' then eq_list eqA l l'
    else false
  | [], [] => true
  | _, _ => false
  end.

#[global] Instance reflect_list : forall {A}, ReflectEq A -> ReflectEq (list A).
Proof.
  intros A RA. refine {| eqb := eq_list eqb |}.
  intro x. induction x ; intro y ; destruct y.
  - cbn. constructor. reflexivity.
  - cbn. constructor. discriminate.
  - cbn. constructor. discriminate.
  - cbn. destruct (eqb_spec a a0) ; nodec.
    destruct (IHx y) ; nodec.
    subst. constructor. reflexivity.
Defined.

#[global] Instance reflect_nat : ReflectEq nat := {
  eqb_spec := PeanoNat.Nat.eqb_spec
}.


Definition eq_bool b1 b2 : bool :=
  if b1 then b2 else negb b2.

Local Obligation Tactic := idtac.

#[global, program] Instance reflect_bool : ReflectEq bool := {
  eqb := eq_bool
}.
Next Obligation.
  intros x y. unfold eq_bool.
  destruct x, y.
  all: constructor.
  all: try reflexivity.
  all: discriminate.
Defined.

Definition eq_sig_true {A f} `{ReflectEq A} (x y : { z : A | f z = true }) : bool :=
  proj1_sig x == proj1_sig y.

#[global, program] Instance reflect_sig_true {A f} `{ReflectEq A} : ReflectEq ({ z : A | f z = true }) := {
  eqb := eq_sig_true
}.
Next Obligation.
  intros A f RA. intros [x hx] [y hy]. unfold eq_sig_true; cbn.
  destruct (eqb_spec x y) ; nodec. subst.
  constructor. pose proof (uip hx hy). subst. reflexivity.
Defined.


Definition eq_prod {A B} (eqA : A -> A -> bool) (eqB : B -> B -> bool) x y :=
  let '(a1, b1) := x in
  let '(a2, b2) := y in
  if eqA a1 a2 then eqB b1 b2
  else false.

#[global, program] Instance reflect_prod : forall {A B}, ReflectEq A -> ReflectEq B -> ReflectEq (A * B) := {
  eqb := eq_prod eqb eqb
}.
Next Obligation.
  intros A B RA RB [x y] [u v].
  unfold eq_prod.
  destruct (eqb_spec x u) ; nodec.
  destruct (eqb_spec y v) ; nodec.
  subst. constructor. reflexivity.
Defined.

Lemma eq_prod_refl :
  forall A B (eqA : A -> A -> bool) (eqB : B -> B -> bool),
    (forall a, eqA a a) ->
    (forall b, eqB b b) ->
    forall p, eq_prod eqA eqB p p.
Proof.
  intros A B eqA eqB eqA_refl eqB_refl [a b].
  simpl. rewrite eqA_refl. apply eqB_refl.
Qed.

