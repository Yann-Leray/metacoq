From Coq Require Import Byte.
From MetaCoq.Template Require Import Reflect ByteCompare.
From Equations Require Import Equations.

Ltac solve_noconf ::= idtac.
Derive NoConfusion for byte.
Next Obligation.
  destruct a; abstract (destruct b; try exact (False_ind _ H); exact eq_refl).
Defined.
Next Obligation.
  destruct b; cbn; exact I.
Defined.
Next Obligation.
  destruct a; abstract (destruct b; try (exact (False_ind _ e)); destruct e; exact eq_refl).
Defined.
Next Obligation.
  destruct b; cbn; exact eq_refl.
Defined.

Lemma reflect_equiv P Q b : P <-> Q -> Bool.reflect P b -> Bool.reflect Q b.
Proof.
  intros eq r. destruct r.
  - now constructor; apply eq.
  - constructor. now rewrite <- eq.
Qed.

Program Instance eqb_spec : ReflectEq byte := 
  {| ReflectEq.eqb := eqb |}.
Next Obligation.
  apply (reflect_equiv (NoConfusion x y)).
  split; intros. now apply noConfusion. now apply noConfusion_inv.
  destruct x; cbn; abstract (destruct y; cbn; constructor; try exact (fun f => f); exact I).
Qed.

Definition lt x y := compare x y = Lt.

Require Import MCCompare.

Lemma compare_opp x y : compare x y = CompOpp (compare y x).
Proof.
  destruct x; abstract (destruct y; exact eq_refl).
Qed.

Lemma compare_eq x y : compare x y = Eq -> x = y.
Proof.
  intros. eapply noConfusion.
  destruct x; abstract (apply noConfusion_inv in H; destruct y; exact H).
Qed.

Lemma compare_spec x y : CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Proof.
  destruct (compare x y) eqn:comp.
  - constructor. now apply compare_eq in comp.
  - constructor. exact comp.
  - constructor. red. now rewrite compare_opp, comp.
Qed.

Lemma compare_equiv x y : compare x y = Nat.compare (Strings.Byte.to_nat x) (Strings.Byte.to_nat y).
Proof.
  destruct x; abstract (destruct y; exact eq_refl).
Qed.

From Coq Require Import Lia.

Lemma lt_trans x y z : lt x y -> lt y z -> lt x z.
Proof.
  unfold lt.
  rewrite !compare_equiv.
  rewrite <- !Compare_dec.nat_compare_lt. lia.
Qed.

Lemma lt_not_eq x y : lt x y -> x <> y.
Proof.
  unfold lt.
  rewrite !compare_equiv.
  rewrite <- !Compare_dec.nat_compare_lt. intros Hlt Heq. subst. lia.
Qed.

Lemma compare_eq' x y : compare x y = Eq -> x = y.
Proof.
  rewrite compare_equiv.
  intros Hcomp.
  eapply PeanoNat.Nat.compare_eq in Hcomp.
  eapply (f_equal of_nat) in Hcomp.
  rewrite !of_to_nat in Hcomp. now noconf Hcomp.
Qed.

Lemma compare_eq_refl x : compare x x = Eq.
Proof.
  rewrite compare_equiv.
  eapply PeanoNat.Nat.compare_refl.
Qed.
