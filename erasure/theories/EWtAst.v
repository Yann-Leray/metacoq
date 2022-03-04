(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect.
From MetaCoq.Template Require Import utils BasicAst Universes.
From MetaCoq.PCUIC Require Import PCUICPrimitive.
From MetaCoq.Erasure Require Import EAst ECSubst ELiftSubst ETyping EEtaExpanded.
From Equations Require Import Equations.

Import MCMonadNotation.

(** * Well-scoped and well-formed extracted terms *)

Definition isSome {A} (o : option A) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Section WellScoped.
  Context (Σ : global_context).

  Definition lookup_constant kn : option constant_body :=
    decl <- ETyping.lookup_env Σ kn;; 
    match decl with
    | ConstantDecl decl => Some decl
    | InductiveDecl mdecl => None
    end.
  
  Definition lookup_minductive kn : option mutual_inductive_body :=
    decl <- ETyping.lookup_env Σ kn;; 
    match decl with
    | ConstantDecl _ => None
    | InductiveDecl mdecl => ret mdecl
    end.

  Definition lookup_inductive kn : option (mutual_inductive_body * one_inductive_body) :=
    mdecl <- lookup_minductive (inductive_mind kn) ;;
    idecl <- nth_error mdecl.(ind_bodies) (inductive_ind kn) ;;
    ret (mdecl, idecl).

  Definition lookup_constructor kn c : option (mutual_inductive_body * one_inductive_body * (ident × nat)) :=
    '(mdecl, idecl) <- lookup_inductive kn ;;
    cdecl <- nth_error idecl.(ind_ctors) c ;;
    ret (mdecl, idecl, cdecl).

  Definition lookup_projection (proj : projection) :=
    '(mdecl, idecl) <- lookup_inductive (fst (fst proj)) ;;
    pdecl <- List.nth_error idecl.(ind_projs) (snd proj) ;; 
    ret (mdecl, idecl, pdecl).
  
  Definition declared_constant id : bool :=
    isSome (lookup_constant id).
  
  Definition declared_minductive mind :=
    isSome (lookup_minductive mind).
  
  Definition declared_inductive ind :=
    isSome (lookup_inductive ind).
  
  Definition declared_constructor kn c :=
    isSome (lookup_constructor kn c).
  
  Definition declared_projection kn :=
    isSome (lookup_projection kn).
  
  Equations well_scoped (n : nat) (t : EAst.term) : bool :=
  { | n, tBox => true
    | n, tRel i := i <? n
    | n, tVar _ := false
    | n, tEvar m l := well_scoped_terms n l
    | _, tConst kn := declared_constant kn
    | _, tConstruct kn k := declared_constructor kn k
    | n, tLambda na b := well_scoped (S n) b
    | n, tLetIn na b b' := well_scoped n b && well_scoped (S n) b'
    | n, tApp f u := well_scoped n f && well_scoped n u
    | n, tCase (ind, pars) c brs :=
      declared_inductive ind && well_scoped n c && well_scoped_brs n brs
    | n, tProj p c := 
      declared_projection p && well_scoped n c
    | n, tFix mfix idx :=
      well_scoped_mfix (#|mfix| + n) mfix 
    | n, tCoFix mfix idx :=
      well_scoped_mfix (#|mfix| + n) mfix }
  where well_scoped_terms (n : nat) (l : list term) : bool :=
  { | n, [] := true;
    | n, (t :: ts) := well_scoped n t && well_scoped_terms n ts }
  where well_scoped_brs (n : nat) (brs : list (list name × term)) : bool :=
  { | n, [] := true;
    | n, (br :: brs) := well_scoped (#|br.1| + n) br.2 && well_scoped_brs n brs }
  where well_scoped_mfix (n : nat) (mfix : mfixpoint term) : bool :=
  { | n, [] := true;
    | n, (d :: defs) := well_scoped n d.(dbody) && well_scoped_mfix n defs }.

  Lemma well_scoped_closed n t : well_scoped n t -> closedn n t.
  Proof.
    revert n t.
    apply (well_scoped_elim
      (fun n t e => e -> closedn n t)
      (fun n l e => e -> forallb (closedn n) l)
      (fun n l e => e -> forallb (fun br => closedn (#|br.1| + n) (snd br)) l)
      (fun n l e => e -> forallb (closedn n ∘ dbody) l)); cbn => //.
    all:intros *; intros; simp well_scoped.
    all:rtoProp; intuition eauto.
  Qed.

  Definition eterm n := { t : EAst.term | well_scoped n t && isEtaExp Σ t }.

  
End WellScoped.

Module TermSpineView.

  Inductive t (A : Type) : term -> Set :=
  | tBox       : t EAst.tBox
  | tRel (n : nat) : t (EAst.tRel n)
  | tVar (n : ident) : t (EAst.tVar n)
  | tEvar (n : nat) (e : list A) : t (EAst.tEvar n e)
  | tLambda n b : t (EAst.tLambda n b)
  | tLetIn n b b' : t (EAst.tLetIn n b b')
  | tApp (f : term) (l : list term) (napp : ~~ isApp f) (nnil : l <> nil) : t (mkApps f l)
  | tConst kn : t (tConst kn)
  | tConstruct i n : t (tConstruct i n)
  | tCase ci p brs : t (tCase ci p brs)
  | tProj p c : t (tProj p c)
  | tFix mfix idx : t (tFix mfix idx)
  | tCoFix mfix idx : t (tCoFix mfix idx).
  Derive Signature for t.

Definition view : forall x : term, t x :=
  MkAppsInd.case (P:=fun x => t x)
    tBox tRel tVar 
    (fun n l => tEvar n l) 
    (fun n t => tLambda n t)
    (fun n b t => tLetIn n b t)
    (fun f l napp nnil => tApp f l napp nnil)
    tConst
    tConstruct
    (fun p t l => tCase p t l)
    (fun p t => tProj p t)
    (fun mfix n => tFix mfix n)
    (fun mfix n => tCoFix mfix n).

Lemma view_mkApps


