(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool Morphisms.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Export Primitive Universes.
From MetaCoq.PCUIC Require Export TypedBasicAst TypedReflect Environment EnvironmentTyping.
From MetaCoq.PCUIC Require Export PCUICPrimitive.
From Equations Require Import Equations.
(** * AST of the Polymorphic Cumulative Calculus of Inductive Constructions

   This AST is a cleaned-up version of Coq's internal AST better suited for
   reasoning.
   In particular, it has binary applications and all terms are well-formed.
   Casts are absent as well. *)

Declare Scope pcuic.
Delimit Scope pcuic with pcuic.
Open Scope pcuic.

Variant global_reference :=
  | ConstRef (kn : kername)
  | IndRef (ind : inductive)
  | ConstructRef (ind : inductive) (k : nat).

Definition evar := nat.

Inductive term :=
  | tRel (n : nat) (ty : term) (s : sort)
  | tVar (id : ident) (ty : term) (s : sort)
  | tEvar (evk : evar) (inst : list term) (ty : term) (s : sort)
  | tSort (s : sort)
  | tProd (na : name) (A : term) (s : sort) (B : term) (s' : sort)
  | tLambda (na : name) (A : term) (s : sort) (t : term) (ty : term) (s' : sort)
  | tLetIn (na : name) (b B : term) (s : sort) (t : term) (ty : term) (s' : sort) (* let na := b : B : tSort s in t : ty : tSort s' *)
  | tApp (na : name) (A : term) (s : sort) (B : term) (s' : sort) (t u : term)
  | tRef (ref : global_reference) (ui : Instance.t) (args : list term)
  | tCase (indn : case_info) (p : predicate term) (c : term) (brs : list (branch term))
  | tProj (p : projection) (c : term)
  | tFix (mfix : mfixpoint term) (idx : nat)
  | tCoFix (mfix : mfixpoint term) (idx : nat)
  | tPrim (prim : prim_val term)
  | tCast (c ty : term) (s : sort).
Derive NoConfusion for term.

Notation prim_val := (prim_val term).

Notation tInd ind := (tRef (IndRef ind)).
Notation tConst cst := (tRef (ConstRef cst)).
Notation tConstruct ind k := (tRef (ConstructRef ind k)).
Notation tInt i := (tPrim (_; primIntModel i)) (only parsing).
Notation tFloat f := (tPrim (_; primFloatModel f)) (only parsing).

Definition isApp t :=
  match t with
  | tApp _ _ _ _ _ _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | tLambda _ _ _ _ _ _ => true
  | _ => false
  end.

Definition isSort t :=
  match t with
  | tSort _ => true
  | _ => false
  end.

Definition isRel t :=
  match t with
  | tRel _ _ _ => true
  | _ => false
  end.

Lemma isLambda_inv t : isLambda t -> exists na ty s bod ty' s', t = tLambda na ty s bod ty' s'.
Proof. destruct t => //; eauto 7. Qed.

(** Basic operations on the AST: lifting, substitution and tests for variable occurrences. *)

Definition map_with_binders {A} f g (k : A) c :=
  match c with
  | tRel i ty s => tRel i (f k ty) s
  | tVar i ty s => tVar i (f k ty) s
  | tEvar evk args ty s => tEvar evk (List.map (f k) args) (f k ty) s
  | tLambda na A s t ty s' => tLambda na (f k A) s (f (g 1 k) t) (f (g 1 k) ty) s'
  | tApp na A s B s' u v => tApp na (f k A) s (f (g 1 k) B) s' (f k u) (f k v)
  | tProd na A s B s' => tProd na (f k A) s (f (g 1 k) B) s'
  | tLetIn na b ty s b' ty' s' => tLetIn na (f k b) (f k ty) s (f (g 1 k) b') (f (g 1 k) ty') s'
  | tCase ind p c brs =>
    let p' := map_predicate_k id f g k p in
    let brs' := map_branches_k f g k brs in
    tCase ind p' (f k c) brs'
  | tProj p c => tProj p (f k c)
  | tFix mfix idx =>
    let k' := g #|mfix| k in
    let mfix' := List.map (map_def (f k) (f k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := g #|mfix| k in
    let mfix' := List.map (map_def (f k) (f k')) mfix in
    tCoFix mfix' idx
  | tPrim p => tPrim (map_prim (f k) p)
  | tCast c ty s => tCast (f k c) (f k ty) s
  | tRef ref ui args => tRef ref ui (map (f k) args)
  | tSort _ => c
  end.


Notation lift_rel n k i := (if Nat.leb k i then (n + i) else i) (i in scope nat_scope).

Fixpoint lift n k t : term :=
  match t with
  | tRel i ty s => tRel (lift_rel n k i) (lift n k ty) s
  | _ => map_with_binders (lift n) Nat.add k t
  end.
Notation lift0 n := (lift n 0).


(** Shift a renaming [f] by [k]. *)
Definition shiftn k f :=
  fun n => if Nat.ltb n k then n else k + (f (n - k)).

Fixpoint rename ρ t :=
  match t with
  | tRel i ty s => tRel (ρ i) (rename ρ ty) s
  | _ => map_with_binders rename shiftn ρ t
  end.


Notation subst_rel σ k n ty s := (
  if Nat.leb k n then
      match nth_error σ (n - k) with
      | Some b => (* tCast *) (lift0 k b)
      | None => tRel (n - #|σ|) ty s
      end
    else tRel n ty s) (n, k in scope nat_scope).


(** Parallel substitution: it assumes that all terms in the substitution live in the
    same context *)
(** Substitutes [t1 ; .. ; tn] in u for [Rel 0; .. Rel (n-1)] *in parallel* *)
Fixpoint subst σ k t :=
  match t with
  | tRel n ty s =>
      subst_rel σ k n (subst σ k ty) s
  | _ => map_with_binders (subst σ) Nat.add k t
  end.

Notation subst0 t := (subst t 0).
Notation subst10 t := (subst0 [t]) (only parsing).
Notation "M { j := N }" := (subst [N] j M) (at level 10, right associativity).

(** * Universe substitution

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)
#[global] Instance subst_instance_constr : UnivSubst term :=
  fix subst_instance_constr u t {struct t} :=
  let rec t := map_with_binders (fun _ => subst_instance_constr u) (fun _ t => t) tt t in
  match t with
  | tRef ref ui args =>
      rec (tRef ref ui@[u] args)
  | tCase ind p c brs =>
      rec (tCase ind (map_predicate_instance (fun ui => ui@[u]) p) c brs)
  | _ => rec t
  end.



Module PCUICTerm <: Term.

  Definition term := term.

  Definition tRel := tRel.
  Definition tSort := tSort.
  Definition tProd := tProd.
  Definition tLambda := tLambda.
  Definition tLetIn := tLetIn.
  Definition tInd ind := tRef (IndRef ind).
  Definition tProj := tProj.
  (* Definition mkApps := mkApps. *)

  Definition lift := lift.
  Definition subst := subst.
  (* Definition closedn := closedn. *)
  (* Definition noccur_between := noccur_between. *)
  Definition subst_instance_constr := subst_instance.
End PCUICTerm.

(* These functors derive the notion of local context and lift substitution, term lifting,
  the closed predicate to them. *)
Module PCUICEnvironment := Environment PCUICTerm.
Export PCUICEnvironment.


Module PCUICTermUtils <: TermUtils PCUICTerm PCUICEnvironment.

(* Definition destArity := destArity.
Definition inds := inds. *)

End PCUICTermUtils.


Ltac unf_term := unfold PCUICTerm.term in *; unfold PCUICTerm.tRel in *;
                 unfold PCUICTerm.tSort in *; unfold PCUICTerm.tProd in *;
                 unfold PCUICTerm.tLambda in *; unfold PCUICTerm.tLetIn in *;
                 unfold PCUICTerm.tInd in *; unfold PCUICTerm.tProj in *;
                 unfold PCUICTerm.lift in *; unfold PCUICTerm.subst in *;
                 (* unfold PCUICTerm.closedn in *; unfold PCUICTerm.noccur_between in *; *)
                 unfold PCUICTerm.subst_instance_constr in *;
                 (* unfold PCUICTermUtils.destArity in *; unfold PCUICTermUtils.inds in *. *)
                 idtac.

Lemma context_assumptions_mapi_context f (ctx : context) :
  context_assumptions (mapi_context f ctx) = context_assumptions ctx.
Proof.
  now rewrite mapi_context_fold; len.
Qed.
#[global]
Hint Rewrite context_assumptions_mapi_context : len.

Module PCUICEnvTyping := EnvironmentTyping.EnvTyping PCUICTerm PCUICEnvironment PCUICTermUtils.
(** Included in PCUICTyping only *)

Module PCUICConversion := EnvironmentTyping.Conversion PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping.


Module PCUICLookup := EnvironmentTyping.Lookup PCUICTerm PCUICEnvironment.
Include PCUICLookup.

Derive NoConfusion for global_decl.

Module PCUICGlobalMaps := EnvironmentTyping.GlobalMaps
  PCUICTerm
  PCUICEnvironment
  PCUICTermUtils
  PCUICEnvTyping
  PCUICConversion
  PCUICLookup
.


Include PCUICGlobalMaps.
