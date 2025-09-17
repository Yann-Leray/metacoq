(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect Morphisms Orders Setoid.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Export Kernames.
From Coq Require Floats.SpecFloat.
From Equations Require Import Equations.

From MetaCoq.Common Require Export BasicAst.
From MetaCoq.Common Require Import Universes.

Set Primitive Projections.

(* name : keep old *)
(* relevance : keep old *)

(* binder_annot : stop using *)

(* string_of_* : keep old *)

(* cast_kind : keep old *)

(* case_info : keep old *)

(* recursivity_kind : keep old *)

(* conv_pb : keep old *)

(* def : don't use annotated names *)

(* Parametrized by term because term is not yet defined *)
Record def term := mkdef {
  dname : name; (* the name **)
  dsort : sort;
  dtype : term;
  dbody : term; (* the body (a lambda term). Note, this may mention other (mutually-defined) names **)
  rarg  : nat  (* the index of the recursive argument, 0 for cofixpoints **) }.

Arguments dname {term} _.
Arguments dsort {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Derive NoConfusion for def.
#[global] Instance def_eq_dec {A} : Classes.EqDec A -> Classes.EqDec (def A).
Proof. ltac:(Equations.Prop.Tactics.eqdec_proof). Qed.

Definition string_of_def {A} (f : A -> string) (def : def A) :=
  "(" ^ string_of_name (dname def)
      ^ "," ^ string_of_sort (dsort def)
      ^ "," ^ f (dtype def)
      ^ "," ^ f (dbody def)
      ^ "," ^ string_of_nat (rarg def) ^ ")".

Definition print_def {A} (f : A -> string) (g : A -> string) (def : def A) :=
  string_of_name (dname def) ^ " { struct " ^ string_of_nat (rarg def) ^ " }" ^
                 " : " ^ f (dtype def) ^ " := " ^ nl ^ g (dbody def).


Definition map_def {A B} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := d.(dname); dsort := d.(dsort); dtype := tyf d.(dtype); dbody := bodyf d.(dbody); rarg := d.(rarg) |}.

Lemma map_dtype {A B} (f : A -> B) (g : A -> B) (d : def A) :
  f (dtype d) = dtype (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma map_dbody {A B} (f : A -> B) (g : A -> B) (d : def A) :
  g (dbody d) = dbody (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma map_dname {A B} (f : A -> B) (g : A -> B) (d : def A) :
  dname d = dname (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Lemma map_dsort {A B} (f : A -> B) (g : A -> B) (d : def A) :
  dsort d = dsort (map_def f g d).
Proof. destruct d; reflexivity. Qed.

Definition mfixpoint term := list (def term).

Definition test_def {A} (tyf bodyf : A -> bool) (d : def A) :=
  tyf d.(dtype) && bodyf d.(dbody).

Definition tFixProp {A} (P P' : A -> Type) (m : mfixpoint A) :=
  All (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.

Lemma map_def_map_def {A B C} (f f' : B -> C) (g g' : A -> B) (d : def A) :
  map_def f f' (map_def g g' d) = map_def (f ∘ g) (f' ∘ g') d.
Proof.
  destruct d; reflexivity.
Qed.

Lemma compose_map_def {A B C} (f f' : B -> C) (g g' : A -> B) :
  (map_def f f') ∘ (map_def g g') = map_def (f ∘ g) (f' ∘ g').
Proof. reflexivity. Qed.

Lemma map_def_id {t} x : map_def (@id t) (@id t) x = id x.
Proof. now destruct x. Qed.
#[global] Hint Rewrite @map_def_id @map_id : map.

Lemma map_def_spec {A B} (P P' : A -> Type) (f f' g g' : A -> B) (x : def A) :
  P' x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. destruct x. unfold map_def. simpl.
  now rewrite !H // !H0.
Qed.

#[global] Hint Extern 10 (_ < _)%nat => lia : all.
#[global] Hint Extern 10 (_ <= _)%nat => lia : all.
#[global] Hint Extern 10 (@eq nat _ _) => lia : all.
#[global] Hint Extern 0 (_ = _) => progress f_equal : all.
#[global] Hint Unfold on_snd snd : all.

Lemma on_snd_eq_id_spec {A B} (f : B -> B) (x : A * B) :
  f (snd x) = snd x <->
  on_snd f x = x.
Proof.
  destruct x; simpl; unfold on_snd; simpl. split; congruence.
Qed.
#[global] Hint Resolve -> on_snd_eq_id_spec : all.
#[global] Hint Resolve -> on_snd_eq_spec : all.

Lemma map_def_eq_spec {A B} (f f' g g' : A -> B) (x : def A) :
  f (dtype x) = g (dtype x) ->
  f' (dbody x) = g' (dbody x) ->
  map_def f f' x = map_def g g' x.
Proof.
  intros. unfold map_def; f_equal; auto.
Qed.
#[global] Hint Resolve map_def_eq_spec : all.

Lemma map_def_id_spec {A} (f f' : A -> A) (x : def A) :
  f (dtype x) = (dtype x) ->
  f' (dbody x) = (dbody x) ->
  map_def f f' x = x.
Proof.
  intros. rewrite (map_def_eq_spec _ _ id id); auto.
Qed.
#[global] Hint Resolve map_def_id_spec : all.

Lemma tfix_map_spec {A B} {P P' : A -> Type} {l} {f f' g g' : A -> B} :
  tFixProp P P' l -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Proof.
  intros.
  eapply All_map_eq. red in X. eapply All_impl; eauto. simpl.
  intros. destruct X0;
  eapply map_def_spec; eauto.
Qed.


Record judgment_ {term} := Judge {
  j_term : option term;
  j_typ : term;
  j_sort : option sort;
}.
Arguments judgment_ : clear implicits.
Arguments Judge {term} _ _ _.

Definition judgment_map {T A} (f: T -> A) (j : judgment_ T) :=
  Judge (option_map f (j_term j)) (f (j_typ j)) (j_sort j).


Section Contexts.
  Context {term : Type}.
  (** *** The context of De Bruijn indices *)

  Record context_decl := mkdecl {
    decl_name : name ;
    decl_body : option term ;
    decl_type : term ;
    decl_sort : sort ;
  }.
  Derive NoConfusion for context_decl.
End Contexts.

Arguments context_decl : clear implicits.

Notation Typ T := (Judge None T None).
Notation j_vass ty s := (Judge None ty (Some s)).
Notation j_vdef b ty s := (Judge (Some b) ty (Some s)).
Notation j_decl d := (Judge (decl_body d) (decl_type d) (Some (decl_sort d))).

Definition map_decl {term term'} (f : term -> term') (d : context_decl term) : context_decl term' :=
  {| decl_name := d.(decl_name);
     decl_body := option_map f d.(decl_body);
     decl_type := f d.(decl_type);
     decl_sort := d.(decl_sort) |}.

Lemma compose_map_decl {term term' term''} (g : term -> term') (f : term' -> term'') x :
  map_decl f (map_decl g x) = map_decl (f ∘ g) x.
Proof.
  destruct x as [? [?|] ?]; reflexivity.
Qed.

Lemma map_decl_ext {term term'} (f g : term -> term') x : (forall x, f x = g x) -> map_decl f x = map_decl g x.
Proof.
  intros H; destruct x as [? [?|] ?]; rewrite /map_decl /=; f_equal; auto.
  now rewrite (H t).
Qed.

#[global] Instance map_decl_proper {term term'} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@map_decl term term').
Proof.
  intros f g Hfg x y ->. now apply map_decl_ext.
Qed.

#[global] Instance map_decl_pointwise {term term'} : Proper (`=1` ==> `=1`) (@map_decl term term').
Proof. intros f g Hfg x. rewrite /map_decl.
  destruct x => /=. f_equal.
  - now rewrite Hfg.
  - apply Hfg.
Qed.
(*

#[global] Instance pointwise_subrelation {A B} : subrelation (`=1`) (@Logic.eq A ==> @Logic.eq B)%signature.
Proof.
  intros f g Hfg x y ->. now rewrite Hfg.
Qed.

#[global] Instance pointwise_subrelation_inv {A B} : subrelation (@Logic.eq A ==> @Logic.eq B)%signature  (`=1`).
Proof.
  intros f g Hfg x. now specialize (Hfg x x eq_refl).
Qed.*)

Definition map_context {term term'} (f : term -> term') (c : list (context_decl term)) :=
  List.map (map_decl f) c.

#[global] Instance map_context_proper {term term'} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@map_context term term').
Proof.
  intros f g Hfg x y ->.
  now rewrite /map_context Hfg.
Qed.

Lemma map_context_length {term term'} (f : term -> term') l : #|map_context f l| = #|l|.
Proof. now unfold map_context; rewrite map_length. Qed.
#[global] Hint Rewrite @map_context_length : len.

Definition test_decl {term} (f : term -> bool) (d : context_decl term) : bool :=
  option_default f d.(decl_body) true && f d.(decl_type).

#[global] Instance test_decl_proper {term} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@test_decl term).
Proof.
  intros f g Hfg [na [b|] ty] ? <- => /=; rewrite /test_decl /=;
  now rewrite Hfg.
Qed.


Definition ondecl {A} (P : A -> Type) (d : context_decl A) :=
  option_default P d.(decl_body) unit × P d.(decl_type).

Notation onctx P := (All (ondecl P)).

Section ContextMap.
  Context {term term' : Type} (f : nat -> term -> term').

  Fixpoint mapi_context (c : list (context_decl term)) : list (context_decl term') :=
    match c with
    | d :: Γ => map_decl (f #|Γ|) d :: mapi_context Γ
    | [] => []
  end.
End ContextMap.

#[global] Instance mapi_context_proper {term term'} : Proper (`=2` ==> Logic.eq ==> Logic.eq) (@mapi_context term term').
Proof.
  intros f g Hfg Γ ? <-.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto; f_equal; auto; now rewrite Hfg.
Qed.

Lemma mapi_context_length {term} (f : nat -> term -> term) l : #|mapi_context f l| = #|l|.
Proof.
  induction l; simpl; auto.
Qed.
#[global] Hint Rewrite @mapi_context_length : len.

Section ContextTest.
  Context {term : Type} (f : term -> bool).

  Fixpoint test_context (c : list (context_decl term)) : bool :=
    match c with
    | d :: Γ => test_context Γ && test_decl f d
    | [] => true
    end.
End ContextTest.

#[global] Instance test_context_proper {term} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@test_context term).
Proof.
  intros f g Hfg Γ ? <-.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto; f_equal; auto; now rewrite Hfg.
Qed.

Section ContextTestK.
  Context {term : Type} (f : nat -> term -> bool) (k : nat).

  Fixpoint test_context_k (c : list (context_decl term)) : bool :=
    match c with
    | d :: Γ => test_context_k Γ && test_decl (f (#|Γ| + k)) d
    | [] => true
    end.
End ContextTestK.

#[global] Instance test_context_k_proper {term} : Proper (`=1` ==> Logic.eq ==> Logic.eq ==> Logic.eq) (@test_context_k term).
Proof.
  intros f g Hfg k ? <- Γ ? <-.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto; f_equal; auto; now rewrite Hfg.
Qed.

Section Contexts.
  Context {term term' term'' : Type}.
  Notation context term := (list (context_decl term)).

  Lemma test_decl_impl (f g : term -> bool) x : (forall x, f x -> g x) ->
    test_decl f x -> test_decl g x.
  Proof using Type.
    intros Hf; rewrite /test_decl.
    move/andb_and=> [Hd Hb].
    apply/andb_and; split; eauto.
    destruct (decl_body x); simpl in *; eauto.
  Qed.

  Definition onctx_k (P : nat -> term -> Type) k (ctx : context term) :=
    Alli (fun i d => ondecl (P (Nat.pred #|ctx| - i + k)) d) 0 ctx.

  Lemma ondeclP {P : term -> Type} {p : term -> bool} {d : context_decl term} :
    (forall x, reflectT (P x) (p x)) ->
    reflectT (ondecl P d) (test_decl p d).
  Proof using Type.
    intros hr.
    rewrite /ondecl /test_decl; destruct d as [decl_name decl_body decl_type]; cbn.
    destruct (hr decl_type) => //;
    destruct (reflect_option_default hr decl_body) => /= //; now constructor.
  Qed.

  Lemma onctxP {p : term -> bool} {ctx : context term} :
    reflectT (onctx p ctx) (test_context p ctx).
  Proof using Type.
    eapply equiv_reflectT.
    - induction 1; simpl; auto. rewrite IHX /= //.
      now move/(ondeclP reflectT_pred): p0.
    - induction ctx.
      * constructor.
      * move => /= /andb_and [Hctx Hd]; constructor; eauto.
        now move/(ondeclP reflectT_pred): Hd.
  Qed.

  Lemma map_decl_type (f : term -> term') decl : f (decl_type decl) = decl_type (map_decl f decl).
  Proof using Type. destruct decl; reflexivity. Qed.

  Lemma map_decl_body (f : term -> term') decl : option_map f (decl_body decl) = decl_body (map_decl f decl).
  Proof using Type. destruct decl; reflexivity. Qed.

  Lemma map_decl_id : @map_decl term term id =1 id.
  Proof using Type. intros d; now destruct d as [? [] ?]. Qed.

  Lemma option_map_decl_body_map_decl (f : term -> term') x :
    option_map decl_body (option_map (map_decl f) x) =
    option_map (option_map f) (option_map decl_body x).
  Proof using Type. destruct x; reflexivity. Qed.

  Lemma option_map_decl_type_map_decl (f : term -> term') x :
    option_map decl_type (option_map (map_decl f) x) =
    option_map f (option_map decl_type x).
  Proof using Type. destruct x; reflexivity. Qed.

  Definition fold_context_k (f : nat -> term -> term') Γ :=
    List.rev (mapi (fun k' decl => map_decl (f k') decl) (List.rev Γ)).

  Arguments fold_context_k f Γ%_list_scope.

  Lemma fold_context_k_alt f Γ :
    fold_context_k f Γ =
    mapi (fun k' d => map_decl (f (Nat.pred (length Γ) - k')) d) Γ.
  Proof using Type.
    unfold fold_context_k. rewrite rev_mapi. rewrite List.rev_involutive.
    apply mapi_ext. intros. f_equal. now rewrite List.rev_length.
  Qed.

  Lemma mapi_context_fold f Γ :
    mapi_context f Γ = fold_context_k f Γ.
  Proof using Type.
    setoid_replace f with (fun k => f (k - 0)) using relation
      (pointwise_relation nat (pointwise_relation term (@Logic.eq term')))%signature at 1.
    rewrite fold_context_k_alt. unfold mapi.
    generalize 0.
    induction Γ as [|d Γ]; intros n; simpl; auto. f_equal.
    rewrite IHΓ. rewrite mapi_rec_Sk.
    apply mapi_rec_ext => k x. intros.
    apply map_decl_ext => t. lia_f_equal.
    intros k. now rewrite Nat.sub_0_r.
  Qed.

  Lemma fold_context_k_tip f d : fold_context_k f [d] = [map_decl (f 0) d].
  Proof using Type. reflexivity. Qed.

  Lemma fold_context_k_length f Γ : length (fold_context_k f Γ) = length Γ.
  Proof using Type.
    unfold fold_context_k. now rewrite !List.rev_length mapi_length List.rev_length.
  Qed.

  Lemma fold_context_k_snoc0 f Γ d :
    fold_context_k f (d :: Γ) = fold_context_k f Γ ,, map_decl (f (length Γ)) d.
  Proof using Type.
    unfold fold_context_k.
    rewrite !rev_mapi !rev_involutive. unfold mapi; rewrite mapi_rec_eqn.
    unfold snoc. f_equal. now rewrite Nat.sub_0_r List.rev_length.
    rewrite mapi_rec_Sk. simpl. apply mapi_rec_ext. intros.
    rewrite app_length !List.rev_length. simpl. f_equal. f_equal. lia.
  Qed.

  Lemma fold_context_k_app f Γ Δ :
    fold_context_k f (Δ ++ Γ)
    = fold_context_k (fun k => f (length Γ + k)) Δ ++ fold_context_k f Γ.
  Proof using Type.
    unfold fold_context_k.
    rewrite List.rev_app_distr.
    rewrite mapi_app. rewrite <- List.rev_app_distr. f_equal. f_equal.
    apply mapi_ext. intros. f_equal. rewrite List.rev_length. f_equal.
  Qed.

  Local Set Keyed Unification.

  Equations mapi_context_In (ctx : context term) (f : nat -> forall (x : context_decl term), In x ctx -> context_decl term) : context term :=
  mapi_context_In nil _ := nil;
  mapi_context_In (cons x xs) f := cons (f #|xs| x _) (mapi_context_In xs (fun n x H => f n x _)).

  Lemma mapi_context_In_spec (f : nat -> term -> term) (ctx : context term) :
    mapi_context_In ctx (fun n (x : context_decl term) (_ : In x ctx) => map_decl (f n) x) =
    mapi_context f ctx.
  Proof using Type.
    remember (fun n (x : context_decl term) (_ : In x ctx) => map_decl (f n) x) as g.
    funelim (mapi_context_In ctx g) => //=; rewrite (H f0) ; trivial.
  Qed.

  Equations fold_context_In (ctx : context term) (f : context term -> forall (x : context_decl term), In x ctx -> context_decl term) : context term :=
  fold_context_In nil _ := nil;
  fold_context_In (cons x xs) f :=
    let xs' := fold_context_In xs (fun n x H => f n x _) in
    cons (f xs' x _) xs'.

  Equations fold_context (f : context term -> context_decl term -> context_decl term) (ctx : context term) : context term :=
    fold_context f nil := nil;
    fold_context f (cons x xs) :=
      let xs' := fold_context f xs in
      cons (f xs' x ) xs'.

  Lemma fold_context_length f Γ : #|fold_context f Γ| = #|Γ|.
  Proof using Type.
    now apply_funelim (fold_context f Γ); intros; simpl; auto; f_equal.
  Qed.


  Lemma fold_context_In_spec (f : context term -> context_decl term -> context_decl term) (ctx : context term) :
    fold_context_In ctx (fun n (x : context_decl term) (_ : In x ctx) => f n x) =
    fold_context f ctx.
  Proof using Type.
    remember (fun n (x : context_decl term) (_ : In x ctx) => f n x) as g.
    funelim (fold_context_In ctx g) => //=; rewrite (H f0); trivial.
  Qed.

  #[global]
  Instance fold_context_Proper : Proper (`=2` ==> `=1`) fold_context.
  Proof using Type.
    intros f f' Hff' x.
    funelim (fold_context f x); simpl; auto. simp fold_context.
    now rewrite (H f' Hff').
  Qed.

  (** This function allows to forget type annotations on a binding context.
  Useful to relate the "compact" case representation in terms, with
  its typing relation, where the context has types *)
  Definition forget_types (c : list (context_decl term)) : list aname :=
    map (fun d => BasicAst.mkBindAnn d.(decl_name) (relevance_of_sort d.(decl_sort))) c.

End Contexts.
#[global] Hint Rewrite @fold_context_length @fold_context_k_length : len.

Section Contexts.
  Context {term term' term'' : Type}.
  Notation context term := (list (context_decl term)).

  Lemma fold_context_k_id (x : context term) : fold_context_k (fun i x => x) x = x.
  Proof using Type.
    rewrite fold_context_k_alt.
    rewrite /mapi. generalize 0.
    induction x; simpl; auto.
    intros n.
    f_equal; auto.
    now rewrite map_decl_id.
  Qed.

  Lemma fold_context_k_compose (f : nat -> term' -> term) (g : nat -> term'' -> term') Γ :
    fold_context_k f (fold_context_k g Γ) =
    fold_context_k (fun i => f i ∘ g i) Γ.
  Proof using Type.
    rewrite !fold_context_k_alt mapi_mapi.
    apply mapi_ext => i d.
    rewrite compose_map_decl. apply map_decl_ext => t.
    now len.
  Qed.

  Lemma fold_context_k_ext (f g : nat -> term' -> term) Γ :
    f =2 g ->
    fold_context_k f Γ = fold_context_k g Γ.
  Proof using Type.
    intros hfg.
    induction Γ; simpl; auto; rewrite !fold_context_k_snoc0.
    simpl. rewrite IHΓ. f_equal. apply map_decl_ext.
    intros. now apply hfg.
  Qed.

  #[global] Instance fold_context_k_proper : Proper (pointwise_relation nat (pointwise_relation _ Logic.eq) ==> Logic.eq ==> Logic.eq)
    (@fold_context_k term' term).
  Proof using Type.
    intros f g Hfg x y <-. now apply fold_context_k_ext.
  Qed.

  Lemma alli_fold_context_k_prop (f : nat -> context_decl term -> bool) (g : nat -> term' -> term) ctx :
    alli f 0 (fold_context_k g ctx) =
    alli (fun i x => f i (map_decl (g (Nat.pred #|ctx| - i)) x)) 0 ctx.
  Proof using Type.
    now rewrite fold_context_k_alt /mapi alli_mapi.
  Qed.

  Lemma test_decl_map_decl f g x : (@test_decl term) f (map_decl g x) = @test_decl term (f ∘ g) x.
  Proof using Type.
    rewrite /test_decl /map_decl /=.
    f_equal. rewrite /option_default.
    destruct (decl_body x) => //.
  Qed.

  Lemma map_fold_context_k (f : term' -> term) (g : nat -> term'' -> term') ctx :
    map (map_decl f) (fold_context_k g ctx) = fold_context_k (fun i => f ∘ g i) ctx.
  Proof using Type.
    rewrite !fold_context_k_alt map_mapi.
    apply mapi_ext => i d. now rewrite compose_map_decl.
  Qed.

  Lemma map_context_mapi_context (f : term' -> term) (g : nat -> term'' -> term') (ctx : list (context_decl term'')) :
    map_context f (mapi_context g ctx) =
    mapi_context (fun i => f ∘ g i) ctx.
  Proof using Type.
    rewrite !mapi_context_fold. now unfold map_context; rewrite map_fold_context_k.
  Qed.

  Lemma mapi_context_map (f : nat -> term' -> term) (g : context_decl term'' -> context_decl term') ctx :
    mapi_context f (map g ctx) = mapi (fun i => map_decl (f (Nat.pred #|ctx| - i)) ∘ g) ctx.
  Proof using Type.
    rewrite mapi_context_fold fold_context_k_alt mapi_map. now len.
  Qed.

  Lemma map_context_map (f : term' -> term) (g : context_decl term'' -> context_decl term') ctx :
    map_context f (map g ctx) = map (map_decl f ∘ g) ctx.
  Proof using Type.
    induction ctx; simpl; f_equal; auto.
  Qed.

  Lemma map_map_context (f : context_decl term' -> term) (g : term'' -> term') ctx :
    map f (map_context g ctx) = map (f ∘ map_decl g) ctx.
  Proof using Type.
    now rewrite /map_context map_map_compose.
  Qed.

  Lemma fold_context_k_map (f : nat -> term' -> term) (g : term'' -> term') Γ :
    fold_context_k f (map_context g Γ) =
    fold_context_k (fun k => f k ∘ g) Γ.
  Proof using Type.
    rewrite !fold_context_k_alt mapi_map.
    apply mapi_ext => n d //. len.
    now rewrite compose_map_decl.
  Qed.

  Lemma fold_context_k_map_comm (f : nat -> term -> term) (g : term -> term) Γ :
    (forall i x, f i (g x) = g (f i x)) ->
    fold_context_k f (map_context g Γ) = map_context g (fold_context_k f Γ).
  Proof using Type.
    intros Hfg.
    rewrite !fold_context_k_alt mapi_map.
    rewrite /map_context map_mapi.
    apply mapi_ext => i x.
    rewrite !compose_map_decl.
    apply map_decl_ext => t.
    rewrite Hfg.
    now len.
  Qed.

  Lemma mapi_context_map_context (f : nat -> term' -> term) (g : term'' -> term') ctx :
    mapi_context f (map_context g ctx) =
    mapi_context (fun i => f i ∘ g) ctx.
  Proof using Type.
    now rewrite !mapi_context_fold fold_context_k_map.
  Qed.

  Lemma map_mapi_context (f : context_decl term' -> term) (g : nat -> term'' -> term') ctx :
    map f (mapi_context g ctx) = mapi (fun i => f ∘ map_decl (g (Nat.pred #|ctx| - i))) ctx.
  Proof using Type.
    now rewrite mapi_context_fold fold_context_k_alt map_mapi.
  Qed.

  Lemma map_context_id (ctx : context term) : map_context id ctx = ctx.
  Proof using Type.
    unfold map_context.
    now rewrite map_decl_id map_id.
  Qed.

  Lemma forget_types_length (ctx : list (context_decl term)) :
    #|forget_types ctx| = #|ctx|.
  Proof using Type.
    now rewrite /forget_types map_length.
  Qed.

  Lemma map_decl_name_fold_context_k (f : nat -> term' -> term) ctx :
    map decl_name (fold_context_k f ctx) = map decl_name ctx.
  Proof using Type.
    now rewrite fold_context_k_alt map_mapi /= mapi_cst_map.
  Qed.

  Lemma forget_types_fold_context_k (f : nat -> term' -> term) ctx :
    forget_types (fold_context_k f ctx) = forget_types ctx.
  Proof using Type.
    now rewrite /forget_types fold_context_k_alt map_mapi /= mapi_cst_map.
  Qed.

  Lemma All2_fold_impl_onctx (P : context term -> context term -> context_decl term -> context_decl term -> Type) P' Γ Δ Q :
    onctx Q Γ ->
    All2_fold P Γ Δ ->
    (forall Γ Δ d d',
      All2_fold P Γ Δ ->
      P Γ Δ d d' ->
      ondecl Q d ->
      P' Γ Δ d d') ->
    All2_fold P' Γ Δ.
  Proof using Type.
    intros onc cr Hcr.
    induction cr; depelim onc; constructor; intuition eauto.
  Qed.

  Lemma All2_fold_mapi (P : context term -> context term -> context_decl term -> context_decl term -> Type) (Γ Δ : context term) f g :
    All2_fold (fun Γ Δ d d' =>
      P (mapi_context f Γ) (mapi_context g Δ) (map_decl (f #|Γ|) d) (map_decl (g #|Γ|) d')) Γ Δ
    <~> All2_fold P (mapi_context f Γ) (mapi_context g Δ).
  Proof using Type.
    split.
    - induction 1; simpl; constructor; intuition auto;
      now rewrite <-(All2_fold_length X).
    - induction Γ as [|d Γ] in Δ |- *; destruct Δ as [|d' Δ]; simpl; intros H;
      depelim H; constructor; simpl in *; auto.
      pose proof (All2_fold_length H). len in H0.
      now rewrite <- H0 in p.
  Qed.

  Lemma All2_fold_map {P : context term -> context term -> context_decl term -> context_decl term -> Type} {Γ Δ : context term} f g :
    All2_fold (fun Γ Δ d d' =>
      P (map_context f Γ) (map_context g Δ) (map_decl f d) (map_decl g d')) Γ Δ <~>
    All2_fold P (map_context f Γ) (map_context g Δ).
  Proof using Type.
    split.
    - induction 1; simpl; constructor; intuition auto;
      now rewrite <-(All2_fold_length X).
    - induction Γ as [|d Γ] in Δ |- *; destruct Δ as [|d' Δ]; simpl; intros H;
        depelim H; constructor; auto.
  Qed.

  Lemma All2_fold_cst_map {P : context_decl term -> context_decl term -> Type} {Γ Δ : context term} {f g} :
    All2_fold (fun _ _ d d' => P (f d) (g d')) Γ Δ <~>
    All2_fold (fun _ _ => P) (map f Γ) (map g Δ).
  Proof using Type.
    split.
    - induction 1; simpl; constructor; intuition auto;
      now rewrite <-(All2_fold_length X).
    - induction Γ as [|d Γ] in Δ |- *; destruct Δ as [|d' Δ]; simpl; intros H;
        depelim H; constructor; auto.
  Qed.


End Contexts.

#[global] Hint Rewrite @map_mapi_context
  @map_fold_context_k @mapi_context_map @map_context_map @map_map_context
  @mapi_context_map_context @map_context_mapi_context : map.
#[global] Hint Rewrite @forget_types_length : len.

(** Primitive types models (axiom free) *)

(** Model of unsigned integers *)
Definition uint_size := 63.
Definition uint_wB := (2 ^ (Z.of_nat uint_size))%Z.
Definition uint63_model := { z : Z | ((0 <=? z) && (z <? uint_wB))%Z }.

Definition string_of_uint63_model (i : uint63_model) := string_of_Z (proj1_sig i).

(** Model of floats *)
Definition prec := 53%Z.
Definition emax := 1024%Z.
(** We consider valid binary encordings of floats as our model *)
Definition float64_model := sig (SpecFloat.valid_binary prec emax).


Record predicate {term} := mk_predicate {
  puinst : Instance.t; (* The universe instance *)
  pparams : list term; (* The parameters *)
  pindices : list term; (* The indices *)
  pcontext : list name; (* The predicate context, as names *)
  preturn : term; (* The return type *) }.
Derive NoConfusion for predicate.
Arguments predicate : clear implicits.
Arguments mk_predicate {_}.

Definition map_predicate_instance {term} uf (p : predicate term) := {|
  puinst := uf p.(puinst);
  pparams := p.(pparams);
  pindices := p.(pindices);
  pcontext := p.(pcontext);
  preturn := p.(preturn) |}.

Section map_predicate.
  Context {term term' : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (paramf indicesf preturnf : term -> term').

  Definition map_predicate (p : predicate term) := {|
    puinst := uf p.(puinst);
    pparams := map paramf p.(pparams);
    pindices := map indicesf p.(pindices);
    pcontext := p.(pcontext);
    preturn := preturnf p.(preturn) |}.

  Lemma map_pparams (p : predicate term) :
    map paramf (pparams p) = pparams (map_predicate p).
  Proof using Type. reflexivity. Qed.

  Lemma map_pindices (p : predicate term) :
    map indicesf (pindices p) = pindices (map_predicate p).
  Proof using Type. reflexivity. Qed.

  Lemma map_preturn (p : predicate term) :
    preturnf (preturn p) = preturn (map_predicate p).
  Proof using Type. reflexivity. Qed.

  Lemma map_pcontext (p : predicate term) :
    pcontext p = pcontext (map_predicate p).
  Proof using Type. reflexivity. Qed.

  Lemma map_puinst (p : predicate term) :
    uf (puinst p) = puinst (map_predicate p).
  Proof using Type. reflexivity. Qed.

End map_predicate.

Definition shiftf {A B} (f : nat -> A -> B) k := (fun k' => f (k' + k)).

Section map_predicate_k.
  Context {term A : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (f : A -> term -> term).
  Context (g : nat -> A -> A).

  Definition map_predicate_k k (p : predicate term) := {|
    puinst := uf p.(puinst);
    pparams := map (f k) p.(pparams);
    pindices := map (f k) p.(pindices);
    pcontext := p.(pcontext);
    preturn := f (g #|p.(pcontext)| k) p.(preturn) |}.

  Lemma map_k_pparams k (p : predicate term) :
    map (f k) (pparams p) = pparams (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Lemma map_k_pindices k (p : predicate term) :
    map (f k) (pindices p) = pindices (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Lemma map_k_preturn k (p : predicate term) :
    f (g #|p.(pcontext)| k) (preturn p) = preturn (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Lemma map_k_pcontext k (p : predicate term) :
    (pcontext p) = pcontext (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Lemma map_k_puinst k (p : predicate term) :
    uf (puinst p) = puinst (map_predicate_k k p).
  Proof using Type. reflexivity. Qed.

  Definition test_predicate (instp : Instance.t -> bool) (p : term -> bool)
    (pred : predicate term) :=
    instp pred.(puinst) &&
    forallb p pred.(pparams) && forallb p pred.(pindices) &&
    p pred.(preturn).

  Definition test_predicate_k (instp : Instance.t -> bool)
    (p : nat -> term -> bool) k (pred : predicate term) :=
    instp pred.(puinst) &&
    forallb (p k) pred.(pparams) && forallb (p k) pred.(pindices) &&
    p (#|pred.(pcontext)| + k) pred.(preturn).

  Definition test_predicate_ku (instp : nat -> Instance.t -> bool)
    (p : nat -> term -> bool) k (pred : predicate term) :=
    instp k pred.(puinst) &&
    forallb (p k) pred.(pparams) && forallb (p k) pred.(pindices) &&
    p k pred.(preturn).

End map_predicate_k.

Section Branch.
  Context {term : Type}.
  (* Parameterized by term types as they are not yet defined. *)
  Record branch := mk_branch {
    bcontext : list name;
    (* Context of names in the branch, including lets. *)
    bbody : term; (* The branch body *) }.
  Derive NoConfusion for branch.

  Definition string_of_branch (f : term -> string) (b : branch) :=
  "([" ^ String.concat "," (map string_of_name (bcontext b)) ^ "], "
  ^ f (bbody b) ^ ")".

  Definition pretty_string_of_branch (f : term -> string) (b : branch) :=
    String.concat " " (map string_of_name (bcontext b)) ^ " => " ^ f (bbody b).

  Definition test_branch (p : term -> bool) (b : branch) :=
    p b.(bbody).

  Definition test_branch_k (p : nat -> term -> bool) k (b : branch) :=
    p (#|b.(bcontext)| + k) b.(bbody).

End Branch.
Arguments branch : clear implicits.

Section map_branch.
  Context {term term' : Type}.
  Context (f : term -> term').

  Definition map_branch (b : branch term) :=
  {| bcontext := b.(bcontext);
      bbody := f b.(bbody) |}.

  Lemma map_bbody (b : branch term) :
    f (bbody b) = bbody (map_branch b).
  Proof using Type. reflexivity. Qed.

  Lemma map_bcontext (b : branch term) :
    (bcontext b) = bcontext (map_branch b).
  Proof using Type. reflexivity. Qed.
End map_branch.

Definition map_branches {term B} (f : term -> B) l := List.map (map_branch f) l.

Section map_branch_k.
  Context {term term' A : Type}.
  Context (f : A -> term -> term').
  Context (g : nat -> A -> A).

  Definition map_branch_k k (b : branch term) :=
  {| bcontext := b.(bcontext);
     bbody := f (g #|b.(bcontext)| k) b.(bbody) |}.

  Lemma map_k_bbody k (b : branch term) :
    f (g #|b.(bcontext)| k) (bbody b) = bbody (map_branch_k k b).
  Proof using Type. reflexivity. Qed.

  Lemma map_k_bcontext k (b : branch term) :
    (bcontext b) = bcontext (map_branch_k k b).
  Proof using Type. reflexivity. Qed.
End map_branch_k.

Notation map_branches_k f g k brs :=
  (List.map (map_branch_k f g k) brs).

Notation test_branches_k test k brs :=
  (List.forallb (test_branch_k test k) brs).


(** Theory of [map] variants on branches and predicates. *)

(* The [map] rewrite database gathers all the map composition rewrite lemmas
  on these types. *)
  #[global]
  Hint Rewrite map_map_compose @compose_map_def map_length : map.

  #[global]
  Hint Rewrite @forallb_map : map.

  Lemma map_predicate_map_predicate
        {term term' term''}
        (finst finst' : Instance.t -> Instance.t)
        (f g h : term' -> term'')
        (f' g' h' : term -> term')
        (p : predicate term) :
    map_predicate finst f g h (map_predicate finst' f' g' h' p) =
    map_predicate (finst ∘ finst') (f ∘ f') (g ∘ g') (h ∘ h') p.
  Proof.
    unfold map_predicate. cbn.
    f_equal.
    all: apply map_map.
  Qed.

  Lemma map_predicate_id {term} x : map_predicate (@id _) (@id term) (@id _) (@id _) x = id x.
  Proof.
    unfold map_predicate; destruct x; cbn; unfold id.
    f_equal. all: apply map_id.
  Qed.
  #[global]
  Hint Rewrite @map_predicate_id : map.

  Definition tCasePredProp_k {term}
              (P : nat -> term -> Type)
              k (p : predicate term) :=
    All (P k) p.(pparams) × All (P k) p.(pindices) ×
    P (#|p.(pcontext)| + k) p.(preturn).

  Definition tCasePredProp {term}
              (Pparams Preturn : term -> Type)
              (p : predicate term) :=
    All Pparams p.(pparams) ×
    All Pparams p.(pindices) ×
    Preturn p.(preturn).

  Lemma map_predicate_eq_spec {A B} (finst finst' : Instance.t -> Instance.t)
    (f f' g g' : A -> B) h h' (p : predicate A) :
    finst (puinst p) = finst' (puinst p) ->
    map f (pparams p) = map f' (pparams p) ->
    map g (pindices p) = map g' (pindices p) ->
    h (preturn p) = h' (preturn p) ->
    map_predicate finst f g h p = map_predicate finst' f' g' h' p.
  Proof.
    intros. unfold map_predicate; f_equal; auto.
  Qed.
  #[global] Hint Resolve map_predicate_eq_spec : all.

  Lemma map_predicate_k_eq_spec {term A} (finst finst' : Instance.t -> Instance.t)
    (f f' : A -> term -> term) (g g' : nat -> A -> A) k k' (p : predicate term) :
    finst (puinst p) = finst' (puinst p) ->
    map (f k) (pparams p) = map (f' k') (pparams p) ->
    map (f k) (pindices p) = map (f' k') (pindices p) ->
    f (g #|pcontext p| k) (preturn p) = f' (g' #|pcontext p| k') (preturn p) ->
    map_predicate_k finst f g k p = map_predicate_k finst' f' g' k' p.
  Proof.
    intros. unfold map_predicate_k; f_equal; auto.
  Qed.
  #[global] Hint Resolve map_predicate_k_eq_spec : all.

  Lemma map_decl_id_spec {term} P f d :
    ondecl P d ->
    (forall x : term, P x -> f x = x) ->
    map_decl f d = d.
  Proof.
    intros Hc Hf.
    destruct Hc.
    unfold map_decl; destruct d; cbn in *. f_equal; eauto.
    destruct decl_body0; simpl; eauto. f_equal.
    eauto.
  Qed.

  Lemma map_decl_id_spec_cond {term} P p f d :
    ondecl P d ->
    test_decl p d ->
    (forall x : term, P x -> p x -> f x = x) ->
    map_decl f d = d.
  Proof.
    intros [].
    unfold map_decl; destruct d; cbn in *.
    unfold test_decl; simpl.
    intros [pty pbody]%andb_and. intros Hx.
    f_equal; eauto.
    destruct decl_body0; simpl; eauto. f_equal.
    eauto.
  Qed.

  Lemma map_context_id_spec {term} P f ctx :
    onctx P ctx ->
    (forall x : term, P x -> f x = x) ->
    map_context f ctx = ctx.
  Proof.
    intros Hc Hf. induction Hc; simpl; auto.
    rewrite IHHc. f_equal; eapply map_decl_id_spec; eauto.
  Qed.
  #[global] Hint Resolve map_context_id_spec : all.

  Lemma map_context_id_spec_cond {term} P p f ctx :
    onctx P ctx ->
    test_context p ctx ->
    (forall x : term, P x -> p x -> f x = x) ->
    map_context f ctx = ctx.
  Proof.
    intros Hc Hc' Hf. induction Hc in Hc' |- *; simpl; auto.
    revert Hc'; simpl; intros [hx hl]%andb_and.
    rewrite IHHc; auto. f_equal. eapply map_decl_id_spec_cond; eauto.
  Qed.
  #[global] Hint Resolve map_context_id_spec_cond : all.

  Lemma map_predicate_id_spec {A} finst (f g h : A -> A) (p : predicate A) :
    finst (puinst p) = puinst p ->
    map f (pparams p) = pparams p ->
    map g (pindices p) = pindices p ->
    h (preturn p) = preturn p ->
    map_predicate finst f g h p = p.
  Proof.
    unfold map_predicate.
    intros -> -> -> ->; destruct p; auto.
  Qed.
  #[global] Hint Resolve map_predicate_id_spec : all.

  Lemma map_predicate_k_id_spec {term A} finst (f : A -> term -> term) (g : nat -> A -> A) k (p : predicate term) :
    finst (puinst p) = puinst p ->
    map (f k) (pparams p) = pparams p ->
    map (f k) (pindices p) = pindices p ->
    f (g #|p.(pcontext)| k) (preturn p) = preturn p ->
    map_predicate_k finst f g k p = p.
  Proof.
    unfold map_predicate_k.
    intros -> -> -> ->; auto.
  Qed.
  #[global] Hint Resolve map_predicate_k_id_spec : all.

  #[global]
  Instance map_predicate_proper {term} :
    Proper (`=1` ==> `=1` ==> `=1` ==> Logic.eq ==> Logic.eq)%signature (@map_predicate term term id).
  Proof.
    intros eqf0 eqf1 eqf.
    intros eqf'0 eqf'1 eqf' h h' eqh'.
    intros x y ->.
    apply map_predicate_eq_spec; auto.
    all: now apply map_ext => x.
  Qed.

  #[global]
  Instance map_predicate_proper' {term} f g : Proper (`=1` ==> Logic.eq ==> Logic.eq)
    (@map_predicate term term id f g).
  Proof.
    intros h h' eqh'.
    intros x y ->.
    apply map_predicate_eq_spec; auto.
  Qed.

  Lemma shiftf0 {A B} (f : nat -> A -> B) : shiftf f 0 =2 f.
  Proof. intros x. unfold shiftf. now rewrite Nat.add_0_r. Qed.

  #[global]
  Hint Rewrite @shiftf0 : map.

  Definition tCaseBrsProp {A} (P : A -> Type) (brs : list (branch A)) :=
    All (fun br => P (bbody br)) brs.

  Definition tCaseBrsProp_k {A} (P : nat -> A -> Type) (p : predicate A) k (brs : list (branch A)) :=
    All (fun br => P (#|br.(bcontext)| + k) (bbody br)) brs.

  Lemma map_predicate_k_map_predicate_k term
    (finst finst' : Instance.t -> Instance.t)
    (f f' : nat -> term -> term) k k' (p : predicate term) :
    map_predicate_k finst f Nat.add k (map_predicate_k finst' f' Nat.add k' p) =
    map_predicate_k (finst ∘ finst') (fun i => f (i + k) ∘ f' (i + k')) Nat.add 0 p.
  Proof.
    unfold map_predicate, map_predicate_k. destruct p; cbn.
    f_equal.
    1,2: now rewrite map_map.
    now len.
  Qed.
  #[global]
  Hint Rewrite map_predicate_k_map_predicate_k : map.

  Lemma map_predicate_map_predicate_k {term A}
    (finst finst' : Instance.t -> Instance.t)
    (f : term -> term) (f' : A -> term -> term) g
    k (p : predicate term) :
    map_predicate finst f f f (map_predicate_k finst' f' g k p) =
    map_predicate_k (finst ∘ finst') (fun k => f ∘ f' k) g k p.
  Proof.
    unfold map_predicate, map_predicate_k. destruct p; cbn.
    f_equal.
    all: apply map_map.
  Qed.
  #[global]
  Hint Rewrite @map_predicate_map_predicate_k : map.

  Lemma map_predicate_k_map_predicate {term A}
    (finst finst' : Instance.t -> Instance.t)
    (f' : term -> term) (f : A -> term -> term) g
    k (p : predicate term) :
    map_predicate_k finst f g k (map_predicate finst' f' f' f' p) =
    map_predicate_k (finst ∘ finst') (fun k => (f k) ∘ f') g k p.
  Proof.
    unfold map_predicate, map_predicate_k. destruct p; cbn.
    f_equal; len; auto.
    all: apply map_map.
  Qed.
  #[global]
  Hint Rewrite @map_predicate_k_map_predicate : map.

  Lemma map_branch_map_branch
        {term term' term''}
        (f : term' -> term'')
        (f' : term -> term')
        (b : branch term) :
    map_branch f (map_branch f' b) =
    map_branch (f ∘ f') b.
  Proof.
    unfold map_branch; destruct b; cbn.
    f_equal.
  Qed.
  #[global]
  Hint Rewrite @map_branch_map_branch : map.

  Lemma map_branch_k_map_branch_k term (f f' : nat -> term -> term) k k' (b : branch term) :
    map_branch_k f Nat.add k (map_branch_k f' Nat.add k' b) =
    map_branch_k (fun i => f (i + k) ∘ f' (i + k')) Nat.add 0 b.
  Proof.
    unfold map_branch, map_branch_k; destruct b; cbn. len.
    f_equal.
  Qed.

  #[global]
  Hint Rewrite map_branch_k_map_branch_k : map.

  Lemma map_branch_map_branch_k term A
        (f : term -> term)
        (f' : A -> term -> term) g k
        (b : branch term) :
    map_branch f (map_branch_k f' g k b) =
    map_branch_k (fun k => f ∘ (f' k)) g k b.
  Proof.
    unfold map_branch, map_branch_k; destruct b; cbn.
    f_equal.
  Qed.

  #[global]
  Hint Rewrite map_branch_map_branch_k : map.
  Lemma map_branch_k_map_branch term A
        (f' : term -> term)
        (f : A -> term -> term) g k
        (b : branch term) :
    map_branch_k f g k (map_branch f' b) =
    map_branch_k (fun k => f k ∘ f') g k b.
  Proof.
    unfold map_branch, map_branch_k; destruct b; cbn. len.
    f_equal.
  Qed.

  #[global]
  Hint Rewrite map_branch_k_map_branch : map.

  Lemma map_branch_id term x : map_branch (@id term) x = id x.
  Proof.
    unfold map_branch, id; destruct x; cbn.
    f_equal.
  Qed.
  #[global]
  Hint Rewrite @map_branch_id : map.

  Lemma map_decl_eq_spec {A B} {P : A -> Type} {d} {f g : A -> B} :
    ondecl P d ->
    (forall x, P x -> f x = g x) ->
    map_decl f d = map_decl g d.
  Proof.
    destruct d; cbn; intros [Pty Pbod] Hfg.
    unfold map_decl; cbn in *; f_equal.
    * destruct decl_body0; cbn in *; eauto. f_equal.
      eauto.
    * eauto.
  Qed.

  Lemma map_context_eq_spec {A B} P (f g : A -> B) ctx :
    onctx P ctx ->
    (forall x, P x -> f x = g x) ->
    map_context f ctx = map_context g ctx.
  Proof.
    intros onc Hfg.
    induction onc; simpl; auto.
    rewrite IHonc. f_equal.
    eapply map_decl_eq_spec; eauto.
  Qed.

  Lemma map_branch_eq_spec {A B} (f g : A -> B) (x : branch A) :
    f (bbody x) = g (bbody x) ->
    map_branch f x = map_branch g x.
  Proof.
    intros. unfold map_branch; f_equal; auto.
  Qed.
  #[global] Hint Resolve map_branch_eq_spec : all.

  Lemma map_branch_k_eq_spec {A B K} (f g : K -> A -> B) h h' k k' (x : branch A) :
    f (h #|x.(bcontext)| k) (bbody x) = g (h' #|x.(bcontext)| k') (bbody x) ->
    map_branch_k f h k x = map_branch_k g h' k' x.
  Proof.
    intros. unfold map_branch_k; f_equal; auto.
  Qed.
  #[global] Hint Resolve map_branch_eq_spec : all.

  #[global]
  Instance map_branch_proper {term} : Proper (`=1` ==> Logic.eq ==> Logic.eq)
    (@map_branch term term).
  Proof.
    intros eqf0 eqf1 eqf.
    intros x y ->.
    apply map_branch_eq_spec; auto.
  Qed.

  Lemma id_id {A} : @id A =1 id.
  Proof. now intros x. Qed.
  #[global] Hint Resolve id_id : core.

  Lemma map_branch_id_spec term (f : term -> term) (x : branch term) :
    f (bbody x) = (bbody x) ->
    map_branch f x = x.
  Proof.
    intros. rewrite (map_branch_eq_spec _ id); auto.
  Qed.
  #[global] Hint Resolve map_branch_id_spec : all.

  Lemma map_branch_k_id_spec term A (f : A -> term -> term) h k (x : branch term) :
    f (h #|x.(bcontext)| k) (bbody x) = (bbody x) ->
    map_branch_k f h k x = x.
  Proof.
    intros. unfold map_branch_k.
    destruct x; simpl in *; f_equal; eauto.
  Qed.
  #[global] Hint Resolve map_branch_k_id_spec : all.

  Lemma map_branches_map_branches
        {term term' term''}
        (f : term' -> term'')
        (f' : term -> term')
        (l : list (branch term)) :
    map (fun b => map_branch f (map_branch f' b)) l =
    map (map_branch (f ∘ f')) l.
  Proof.
    eapply map_ext => b. apply map_branch_map_branch.
  Qed.

From MetaCoq.PCUIC Require Import PCUICPrimitive.
Require Import ssreflect ssrbool.

  Lemma mapu_prim_compose {term term' term''}
    f (g : term' -> term'') f' (g' : term -> term') : mapu_prim f g ∘ mapu_prim f' g' =1 mapu_prim (f ∘ f') (g ∘ g').
  Proof.
    intros [? []]; cbn => //. do 3 f_equal.
    unfold mapu_array_model; destruct a => //=. now rewrite map_map_compose.
  Qed.

  Lemma mapu_prim_compose_rew {term term' term''}
    f (g : term' -> term'') f' (g' : term -> term') :
    forall x, mapu_prim f g (mapu_prim f' g' x) = mapu_prim (f ∘ f') (g ∘ g') x.
  Proof. intros x. now rewrite (mapu_prim_compose _ _ _ _ x). Qed.

  #[global] Hint Rewrite @mapu_prim_compose_rew : map.

  Lemma prim_val_tag_map {term term'} (p : PCUICPrimitive.prim_val term) fu (ft : term -> term') :
    prim_val_tag (mapu_prim fu ft p) = prim_val_tag p.
  Proof.
    destruct p as [? []] => //.
  Qed.

  Lemma mapu_array_model_proper {term term'} (l l' : Level.t -> Level.t) (f g : term -> term') a :
    l =1 l' -> f =1 g ->
    mapu_array_model l f a = mapu_array_model l' g a.
  Proof.
    destruct a; cbn ; rewrite /mapu_array_model /=. intros; f_equal; eauto. now eapply map_ext.
  Qed.

  Lemma mapu_array_model_proper_cond {term term'} (P : term -> Type) (l l' : Level.t -> Level.t) (f g : term -> term') a :
    l =1 l' -> (forall x, P x -> f x = g x) ->
    P a.(array_type) × P a.(array_default) × All P a.(array_value) ->
    mapu_array_model l f a = mapu_array_model l' g a.
  Proof.
    destruct a; cbn ; rewrite /mapu_array_model /=. intros hl hf [? []]; f_equal; eauto.
    induction a; cbn => //. rewrite IHa. rewrite hf //.
  Qed.

  Lemma primProp_map_eq {term term'} P p l l' (f g : term -> term') :
    tPrimProp P p ->
    l =1 l' ->
    (forall x, P x -> f x = g x) ->
    mapu_prim l f p = mapu_prim l' g p.
  Proof.
    destruct p as [? []]; cbn => //.
    intros [? []] hl hp. do 2 f_equal.
    eapply mapu_array_model_proper_cond; tea. intuition auto.
  Qed.

  Lemma primProp_map_id {term} P p (f : term -> term) :
    tPrimProp P p ->
    (forall x, P x -> f x = x) ->
    map_prim f p = p.
  Proof.
    intros hp hf.
    rewrite (primProp_map_eq P p id id f id) //.
    destruct p as [? []]; cbn => //.
    destruct a => //=. rewrite /mapu_array_model /=. rewrite map_id //.
  Qed.

  Lemma test_prim_primProp {term} {P p} : @test_prim term P p -> tPrimProp P p.
  Proof.
    destruct p as [? []]; cbn => //.
    move/andP => [] /andP[]. intuition auto.
    now eapply forallb_All in a0.
  Qed.

  Lemma primProp_test_prim {term} {P : term -> bool} {p} : tPrimProp P p -> test_prim P p.
  Proof.
    destruct p as [? []]; cbn => //. intros. rtoProp.
    intuition auto.
    now eapply All_forallb.
  Qed.

  Lemma tPrimProp_impl {term} {P Q : term -> Type} {p} : tPrimProp P p -> (forall x, P x -> Q x) -> tPrimProp Q p.
  Proof.
    intros hp hpq; destruct p as [? []]; cbn in * => //. intuition auto.
    eapply All_impl; tea.
  Qed.

  Lemma tPrimProp_prod {term} {P Q : term -> Type} {p} : tPrimProp P p -> tPrimProp Q p -> tPrimProp (fun x => P x × Q x) p.
  Proof.
    destruct p as [? []]; cbn => //. intuition auto.
    now eapply All_prod.
  Qed.

  Lemma primProp_map {term} (P : term -> Type) f (p : PCUICPrimitive.prim_val term) :
    tPrimProp (fun x => P (f x)) p ->
    tPrimProp P (map_prim f p).
  Proof.
    destruct p as [? []]; cbn => //. intuition eauto. now eapply All_map.
  Qed.

  Lemma primProp_map_inv {term} (P : term -> Type) f (p : PCUICPrimitive.prim_val term) :
    tPrimProp P (map_prim f p) ->
    tPrimProp (fun x => P (f x)) p.
  Proof.
    destruct p as [? []]; cbn => //. intuition eauto; now eapply All_map_inv.
  Qed.

  Lemma primProp_mapu_id {term} {P : term -> Type} {pu put} p f g :
    tPrimProp P p -> test_primu pu put p ->
    (forall u, pu u -> f u = u) ->
    (forall t, P t -> put t -> g t = t) ->
    mapu_prim f g p = p.
  Proof.
    intros hp ht hf hg.
    destruct p as [? []]; cbn => //. f_equal. f_equal.
    destruct a; destruct hp; cbn in *. unfold mapu_array_model; cbn.
    rtoProp. destruct p0. f_equal; intuition eauto.
    eapply forallb_All in H2. eapply All_prod in a; tea.
    eapply All_map_id, All_impl; tea. intuition eauto. apply hg; intuition auto.
  Qed.

  Lemma test_primu_test_primu_tPrimProp {term} {P : term -> Type} {pu put} {pu' : Level.t -> bool} {put' : term -> bool} p f g :
    tPrimProp P p -> test_primu pu put p ->
    (forall u, pu u -> pu' (f u)) ->
    (forall t, P t -> put t -> put' (g t)) ->
    test_primu pu' put' (mapu_prim f g p).
  Proof.
    intros hp ht hf hg.
    destruct p as [? []]; cbn => //.
    destruct a; destruct hp; cbn in *.
    rtoProp. destruct p0. intuition eauto.
    eapply forallb_All in H2. eapply All_prod in a; tea.
    eapply All_forallb, All_map, All_impl; tea. intuition eauto. apply hg; intuition auto.
  Qed.

  Lemma test_prim_mapu {term term'} {put : term' -> bool} {l} {f : term -> term'} {p} :
    test_prim put (mapu_prim l f p) = test_prim (fun x => put (f x)) p.
  Proof.
    destruct p as [? []]; cbn; eauto.
    now rewrite forallb_map.
  Qed.
  #[global] Hint Rewrite @test_prim_mapu : map.

  Lemma test_prim_eq_spec {term} {P : term -> Type} {put} {put' : term -> bool} p :
    tPrimProp P p ->
    (forall t, P t -> put t = put' t) ->
    test_prim put p = test_prim put' p.
  Proof.
    destruct p as [? []]; cbn => //. intuition eauto.
    f_equal; eauto. f_equal; eauto.
    eapply All_forallb_eq_forallb; tea.
  Qed.

  Lemma case_brs_map_spec {A B} {P : A -> Type} {l} {f g : A -> B}
    {h h' : list (BasicAst.context_decl A) -> list (BasicAst.context_decl B)} :
    tCaseBrsProp P l -> (forall x, P x -> f x = g x) ->
    map_branches f l = map_branches g l.
  Proof.
    intros. red in X.
    eapply All_map_eq. eapply All_impl; eauto. simpl; intros.
    apply map_branch_eq_spec; eauto.
  Qed.

  Lemma map_decl_eqP_spec {A B} {P : A -> Type} {p : A -> bool}
     {d} {f g : A -> B} :
    ondecl P d ->
    test_decl p d ->
    (forall x, P x -> p x -> f x = g x) ->
    map_decl f d = map_decl g d.
  Proof.
    destruct d; cbn; intros [Pty Pbod] [pty pbody]%andb_and Hfg.
    unfold map_decl; cbn in *; f_equal.
    * destruct decl_body0; cbn in *; eauto. f_equal.
      eauto.
    * eauto.
  Qed.

  Lemma map_context_eqP_spec {A B} {P : A -> Type} {p : A -> bool}
     {ctx} {f g : A -> B} :
    All (ondecl P) ctx ->
    test_context p ctx ->
    (forall x, P x -> p x -> f x = g x) ->
    map_context f ctx = map_context g ctx.
  Proof.
    intros Ha Hctx Hfg. induction Ha; simpl; auto.
    revert Hctx; simpl; intros [Hx Hl]%andb_and.
    rewrite IHHa; f_equal; auto.
    eapply map_decl_eqP_spec; eauto.
  Qed.

  Lemma mapi_context_eqP_spec {A B} {P : A -> Type} {ctx} {f g : nat -> A -> B} :
    All (ondecl P) ctx ->
    (forall k x, P x -> f k x = g k x) ->
    mapi_context f ctx = mapi_context g ctx.
  Proof.
    intros Ha Hfg. induction Ha; simpl; auto.
    rewrite IHHa; f_equal.
    destruct p as [Hty Hbody].
    unfold map_decl; destruct x ; cbn in *; f_equal.
    * destruct decl_body0; cbn in *; auto.
      f_equal. eauto.
    * eauto.
  Qed.

  Lemma mapi_context_eqP_id_spec {A} {P : A -> Type} {ctx} {f : nat -> A -> A} :
    All (ondecl P) ctx ->
    (forall k x, P x -> f k x = x) ->
    mapi_context f ctx = ctx.
  Proof.
    intros Ha Hfg. induction Ha; simpl; auto.
    rewrite IHHa; f_equal.
    destruct p as [Hty Hbody].
    unfold map_decl; destruct x ; cbn in *; f_equal.
    * destruct decl_body0; cbn in *; auto.
      f_equal. eauto.
    * eauto.
  Qed.

  Lemma mapi_context_eqP_test_id_spec {A} {P : A -> Type} (p : nat -> A -> bool)
    k {ctx} {f : nat -> A -> A} :
    All (ondecl P) ctx ->
    test_context_k p k ctx ->
    (forall k (x : A), P x -> p k x -> f k x = x) ->
    mapi_context (shiftf f k) ctx = ctx.
  Proof.
    intros Ha ht Hfg. revert ht.
    induction Ha; simpl; auto.
    intros [hl [hty hbod]%andb_and]%andb_and.
    rewrite IHHa; auto; f_equal.
    destruct p0 as [Hty Hbody].
    unfold map_decl; destruct x ; cbn in *; f_equal; eauto.
    destruct decl_body0; cbn in *; auto.
    f_equal. unfold shiftf. eapply Hfg; auto.
  Qed.

  Lemma test_context_k_eqP_id_spec {A} {P : A -> Type} (p q : nat -> A -> bool) k k' {ctx} :
    All (ondecl P) ctx ->
    test_context_k p k ctx ->
    (forall i (x : A), P x -> p (i + k) x -> q (i + k') x) ->
    test_context_k q k' ctx.
  Proof.
    intros Ha ht Hfg. revert ht.
    induction Ha; simpl; auto.
    intros [hl [hty hbod]%andb_and]%andb_and.
    rewrite IHHa; simpl; auto.
    destruct p0 as [Hty Hbody].
    unfold test_decl; destruct x ; cbn in *; eauto.
    destruct decl_body0; cbn in *; auto.
    rewrite !Hfg; auto.
  Qed.

  Lemma test_context_k_eqP_eq_spec {A} {P : A -> Type} (p q : nat -> A -> bool) k k' {ctx} :
    All (ondecl P) ctx ->
    (forall i (x : A), P x -> p (i + k) x = q (i + k') x) ->
    test_context_k p k ctx = test_context_k q k' ctx.
  Proof.
    intros Ha Hfg.
    induction Ha; simpl; auto.
    rewrite IHHa; auto; f_equal.
    destruct p0 as [Hty Hbody].
    unfold test_decl; destruct x ; cbn in *; f_equal; eauto.
    destruct decl_body0; cbn in *; auto;
    rewrite !Hfg; auto.
  Qed.

  Lemma test_context_k_eq_spec {term} (p q : nat -> term -> bool) k k' {ctx} :
    (p =2 q) ->
    k = k' ->
    test_context_k p k ctx = test_context_k q k' ctx.
  Proof.
    intros Hfg <-.
    induction ctx as [|[na [b|] ty] ctx]; simpl; auto; now rewrite IHctx Hfg.
  Qed.

  Lemma test_context_k_eq {term} (p : nat -> term -> bool) n ctx :
    test_context_k p n ctx = alli (fun k d => test_decl (p (n + k)) d) 0 (List.rev ctx).
  Proof.
    induction ctx; simpl; auto.
    rewrite IHctx alli_app /= andb_comm andb_true_r andb_comm. f_equal.
    len. now rewrite Nat.add_comm.
  Qed.

  #[global]
  Instance test_context_k_Proper {term} : Proper (`=2` ==> Logic.eq ==> `=1`) (@test_context_k term).
  Proof.
    intros f g Hfg k k' <- ctx.
    now apply test_context_k_eq_spec.
  Qed.

  #[global]
  Instance test_predicate_k_Proper {term} : Proper (`=1` ==> `=2` ==> Logic.eq ==> `=1`) (@test_predicate_k term).
  Proof.
    intros hi hi' eqhi f g Hfg k k' <- ctx.
    unfold test_predicate_k. rewrite eqhi.
    now setoid_rewrite Hfg.
  Qed.

  #[global]
  Instance test_predicate_ku_Proper {term} : Proper (`=2` ==> `=2` ==> Logic.eq ==> `=1`) (@test_predicate_ku term).
  Proof.
    intros hi hi' eqhi f g Hfg k k' <- ctx.
    unfold test_predicate_ku. rewrite eqhi.
    now setoid_rewrite Hfg.
  Qed.

  #[global]
  Instance test_branch_k_Proper {term} : Proper (`=2` ==> Logic.eq ==> `=1`) (@test_branch_k term).
  Proof.
    intros f g Hfg k k' <- ctx.
    unfold test_branch_k.
    now setoid_rewrite Hfg.
  Qed.

  Lemma case_brs_map_spec_cond {A B} {P : A -> Type} p {l} {f g : A -> B} :
    tCaseBrsProp P l ->
    forallb (test_branch p) l ->
    (forall x, P x -> p x -> f x = g x) ->
    map_branches f l = map_branches g l.
  Proof.
    intros. red in X.
    eapply forallb_All in H.
    eapply All_map_eq.
    eapply All_prod in X; tea. clear H.
    eapply All_impl; eauto. simpl; intros br [].
    apply map_branch_eq_spec; eauto.
  Qed.

  Lemma case_brs_map_k_spec {A B K} {P : A -> Type} {k l} {f g : K -> A -> B} {h h'} :
    tCaseBrsProp P l ->
    (forall k x, P x -> f k x = g k x) ->
    h =1 h' ->
    map_branches_k f h k l = map_branches_k g h' k l.
  Proof.
    intros. red in X.
    eapply All_map_eq. eapply All_impl; eauto. simpl; intros.
    apply map_branch_k_eq_spec; eauto.
    rewrite -H0. now apply H.
  Qed.

  Lemma case_brs_forallb_map_spec {A B} {P : A -> Type} {p : A -> bool}
        {l} {f g : A -> B} :
    tCaseBrsProp P l ->
    forallb (test_branch p) l ->
    (forall x, P x -> p x -> f x = g x) ->
    map (map_branch f) l = map (map_branch g) l.
  Proof.
    intros.
    eapply All_map_eq. red in X. apply forallb_All in H.
    eapply All_impl. eapply All_prod. exact X. exact H. simpl.
    intros [bctx bbod] [Hbr hb]. cbn in *.
    unfold map_branch; cbn. f_equal.
    - eapply H0; eauto.
  Qed.

  Lemma test_context_map {term} (p : term -> bool) f (ctx : list (context_decl term)) :
    test_context p (map_context f ctx) = test_context (p ∘ f) ctx.
  Proof.
    induction ctx; simpl; auto.
    rewrite IHctx. f_equal.
    now rewrite test_decl_map_decl.
  Qed.
  #[global]
  Hint Rewrite @test_context_map : map.

  Lemma test_context_app {term} (p : term -> bool) Γ Δ :
    test_context p (Γ ,,, Δ) = test_context p Γ && test_context p Δ.
  Proof using Type.
    induction Δ; simpl; auto.
    - now rewrite andb_true_r.
    - now rewrite IHΔ andb_assoc.
  Qed.

  Lemma onctx_test {term} P (p q : term -> bool) ctx :
    onctx P ctx ->
    test_context p ctx ->
    (forall t, P t -> p t -> q t) ->
    test_context q ctx.
  Proof.
    intros Hc tc HP. revert tc.
    induction Hc; simpl; auto.
    destruct p0.
    intros [pl [pbod pty]%andb_and]%andb_and.
    rewrite (IHHc pl); simpl.
    unfold test_decl.
    rewrite (HP _ p0 pty) andb_true_r; simpl.
    destruct (decl_body x); simpl in *; eauto.
  Qed.

  (** Useful for inductions *)
  Lemma onctx_k_rev {term} {P : nat -> term -> Type} {k} {ctx} :
    onctx_k P k ctx <~>
    Alli (fun i => ondecl (P (i + k))) 0 (List.rev ctx).
  Proof.
    split.
    - unfold onctx_k.
      intros Hi.
      eapply forall_nth_error_Alli => i x hx.
      pose proof (nth_error_Some_length hx).
      rewrite nth_error_rev // in hx.
      rewrite List.rev_involutive in hx.
      len in hx.
      eapply Alli_nth_error in Hi; tea.
      simpl in Hi. simpl.
      replace (Nat.pred #|ctx| - (#|ctx| - S i) + k) with (i + k) in Hi => //.
      len in H; by lia.
    - intros Hi.
      eapply forall_nth_error_Alli => i x hx.
      eapply Alli_rev_nth_error in Hi; tea.
      simpl.
      replace (#|ctx| - S i + k) with (Nat.pred #|ctx| - i + k) in Hi => //.
      lia.
  Qed.

  Lemma onctx_k_shift {term} {P : nat -> term -> Type} {k} {ctx} :
    onctx_k P k ctx ->
    onctx_k (fun k' => P (k' + k)) 0 ctx.
  Proof.
    intros Hi%onctx_k_rev.
    eapply onctx_k_rev.
    eapply Alli_impl; tea => /= n x.
    now rewrite Nat.add_0_r.
  Qed.

  Lemma onctx_k_P {term} {P : nat -> term -> Type} {p : nat -> term -> bool} {k} {ctx : list (context_decl term)} :
    (forall x y, reflectT (P x y) (p x y)) ->
    reflectT (onctx_k P k ctx) (test_context_k p k ctx).
  Proof.
    intros HP.
    eapply equiv_reflectT.
    - intros Hi%onctx_k_rev.
      rewrite test_context_k_eq.
      induction Hi; simpl; auto.
      rewrite Nat.add_comm.
      rewrite IHHi /= //.
      now move/(ondeclP (HP _)): p0 => ->.
    - intros Hi. eapply onctx_k_rev.
      move: ctx Hi. induction ctx.
      * constructor.
      * move => /= /andb_and [Hctx Hd].
        eapply Alli_app_inv; eauto. constructor.
        + move/(ondeclP (HP _)): Hd. now len.
        + constructor.
  Qed.
