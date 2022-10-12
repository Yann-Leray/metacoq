(* Distributed under the terms of the MIT license. *)
From Coq Require Import Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction PCUICRelevance
  PCUICLiftSubst PCUICUnivSubst
  PCUICSigmaCalculus PCUICTyping.

Require Import ssreflect ssrbool.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Set Equations With UIP.

(** * Type preservation for σ-calculus operations *)

Open Scope sigma_scope.
Set Keyed Unification.

Set Default Goal Selector "!".

Section Renaming.

Context `{cf : checker_flags}.


(* Notion of valid renaming without typing information. *)

(** We might want to relax this to allow "renamings" that change e.g. 
  the universes or names, but should generalize the renaming operation at 
  the same time *)
(** Remark: renaming allows instantiating an assumption with a well-typed body *)

Definition urenaming (P : nat -> bool) Γ Δ f :=
  forall i decl, P i -> 
    nth_error Δ i = Some decl ->
    ∑ decl', (nth_error Γ (f i) = Some decl') ×
    eq_binder_annot decl.(decl_name) decl'.(decl_name) ×
    rename (f ∘ rshiftk (S i)) decl.(decl_type) = 
      rename (rshiftk (S (f i))) decl'.(decl_type) ×
    on_Some_or_None (fun body => Some (rename (f ∘ rshiftk (S i)) body) =
      option_map (rename (rshiftk (S (f i)))) decl'.(decl_body)) decl.(decl_body).

Definition umarks_renaming (P : nat -> bool) (Γ Δ : mark_context) f :=
  forall i rel, P i -> 
    nth_error Δ i = Some rel ->
    nth_error Γ (f i) = Some rel.

Lemma urenaming_umarks_renaming (P : nat -> bool) Γ Δ f :
  urenaming P Γ Δ f -> umarks_renaming P (marks_of_context Γ) (marks_of_context Δ) f.
Proof.
  intros H i rel HP Hn.
  rewrite nth_error_map in Hn.
  destruct (nth_error Δ i) eqn:Hn' => //. cbn in Hn.
  destruct (H i _ HP Hn') as (decl' & Hn'' & e & _).
  rewrite nth_error_map Hn'' /= -e Hn //.
Qed.

(* Definition of a good renaming with respect to typing *)
Definition renaming P Σ Γ Δ f :=
  wf_local Σ Γ × urenaming P Γ Δ f.

End Renaming.

