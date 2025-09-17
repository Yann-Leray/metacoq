(* Distributed under the terms of the MIT license. *)
(* For primitive integers and floats  *)
From Coq Require Numbers.Cyclic.Int63.Uint63 Floats.PrimFloat Floats.FloatAxioms.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Universes Kernames.
Require Import ssreflect.
From Equations Require Import Equations.

From MetaCoq.Common Require Export Reflect.
From MetaCoq.PCUIC Require Import TypedBasicAst.

Local Obligation Tactic := idtac.

Definition eq_def {A} `{ReflectEq A} (d1 d2 : def A) : bool :=
  match d1, d2 with
  | mkdef n1 s1 t1 b1 a1, mkdef n2 s2 t2 b2 a2 =>
    eqb n1 n2 && eqb s1 s2 && eqb t1 t2 && eqb b1 b2 && eqb a1 a2
  end.

#[global, program] Instance reflect_def : forall {A} `{ReflectEq A}, ReflectEq (def A) := {
  eqb := eq_def
}.
Next Obligation.
  intros A RA.
  intros x y. destruct x as [n1 s1 t1 b1 a1], y as [n2 s2 t2 b2 a2].
  unfold eq_def.
  destruct (eqb_spec n1 n2) ; nodec.
  destruct (eqb_spec s1 s2) ; nodec.
  destruct (eqb_spec t1 t2) ; nodec.
  destruct (eqb_spec b1 b2) ; nodec.
  destruct (eqb_spec a1 a2) ; nodec.
  cbn. constructor. subst. reflexivity.
Qed.


Definition eqb_context_decl {term : Type} (eqterm : term -> term -> bool)
  (x y : context_decl term) :=
  let (na, b, ty, s) := x in
  let (na', b', ty', s') := y in
  eqb na na' && eq_option eqterm b b' && eqterm ty ty' && eqb s s'.

#[global, program] Instance eq_decl_reflect {term} {Ht : ReflectEq term} : ReflectEq (context_decl term) :=
  {| eqb := eqb_context_decl eqb |}.
Next Obligation.
  intros. unfold eqb_context_decl.
  destruct x as [na b ty s], y as [na' b' ty' s']. cbn -[eqb].
  change (eq_option eqb b b') with (eqb b b').
  destruct (eqb_spec na na'); subst;
    destruct (eqb_spec b b'); subst;
      destruct (eqb_spec ty ty');
        destruct (eqb_spec s s'); subst; constructor; congruence.
Qed.


Definition string_of_predicate {term} (f : term -> string) (p : predicate term) :=
  "(" ^ "(" ^ String.concat "," (map f (pparams p)) ^ ")"
  ^ "," ^ string_of_universe_instance (puinst p)
  ^ ",(" ^ String.concat "," (map string_of_name (pcontext p)) ^ ")"
  ^ "," ^ f (preturn p) ^ ")".

Definition eqb_predicate {term} (eqterm : term -> term -> bool) (p p' : predicate term) :=
  forallb2 eqterm p.(pparams) p'.(pparams) &&
  eqb p.(puinst) p'.(puinst) &&
  eqb p.(pcontext) p'.(pcontext) &&
  eqterm p.(preturn) p'.(preturn).
