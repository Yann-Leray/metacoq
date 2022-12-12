From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPattern PCUICPosition PCUICTactics.
Require Import ssreflect.

Module PCUICTermUtils <: TermUtils PCUICTerm PCUICEnvironment.

Definition destArity := destArity.
Definition inds := inds.

Definition symbols_subst := symbols_subst.
Definition context_env_clos := context_env_clos.
Definition pattern_matches := pattern_matches.
Definition pattern_holes := pattern_holes.
Definition pattern_head := pattern_head.

End PCUICTermUtils.

Ltac unf_term := unfold PCUICTerm.term in *; unfold PCUICTerm.tRel in *;
                 unfold PCUICTerm.tSort in *; unfold PCUICTerm.tProd in *;
                 unfold PCUICTerm.tLambda in *; unfold PCUICTerm.tLetIn in *;
                 unfold PCUICTerm.tInd in *; unfold PCUICTerm.tProj in *;
                 unfold PCUICTerm.lift in *; unfold PCUICTerm.subst in *;
                 unfold PCUICTerm.closedn in *; unfold PCUICTerm.noccur_between in *;
                 unfold PCUICTerm.subst_instance_constr in *;
                 unfold PCUICTermUtils.destArity in *; unfold PCUICTermUtils.inds in *;
                 unfold PCUICTermUtils.symbols_subst in *; unfold PCUICTermUtils.context_env_clos in *;
                 unfold PCUICTermUtils.pattern_matches in *; unfold PCUICTermUtils.pattern_holes in *;
                 unfold PCUICTermUtils.pattern_head in *.

Module PCUICGlobalMaps := EnvironmentTyping.GlobalMaps
  PCUICTerm
  PCUICEnvironment
  PCUICEnvTyping
  PCUICConversion
  PCUICTermUtils
  PCUICLookup
.
Include PCUICGlobalMaps.

Lemma on_declared_rules0 {cf : checker_flags} {Pcmp red P} {Σ kn rdecl} :
  on_global_env Pcmp red P Σ -> declared_rules Σ kn rdecl ->
  All (on_rewrite_rule kn (context_of_symbols (symbols rdecl))) (rules rdecl) ×
  All (on_rewrite_rule kn (context_of_symbols (symbols rdecl))) (prules rdecl).
Proof.
  intros X Hin.
  eapply @declared_rules_to_gen in Hin; tea.
  revert Hin.
  destruct X as [onu onΣ].
  destruct Σ as [univs Σ retro]; cbn in *.
  unfold declared_rules_gen; cbn.
  induction onΣ; simpl in *. 1: congruence.
  destruct o as [??? onr]. case: eqb_specT; intro e; subst.
  - intros [= ->].
    destruct onr as (? & onr & onp & onpr).
    now split.
  - auto.
Qed.

Lemma on_declared_rule {cf : checker_flags} {Pcmp red P} {Σ kn r rdecl decl} :
  on_global_env Pcmp red P Σ -> declared_rule Σ kn r rdecl decl ->
  on_rewrite_rule kn (context_of_symbols rdecl.(symbols)) decl.
Proof.
  intros X [H Hnth].
  eapply on_declared_rules0 in H as [onr onpr]; tea.
  eapply All_nth_error in onr; tea.
Qed.

Lemma on_declared_prule {cf : checker_flags} {Pcmp red P} {Σ kn r rdecl decl} :
  on_global_env Pcmp red P Σ -> declared_prule Σ kn r rdecl decl ->
  on_rewrite_rule kn (context_of_symbols rdecl.(symbols)) decl.
Proof.
  intros X [H Hnth].
  eapply on_declared_rules0 in H as [onr onpr]; tea.
  eapply All_nth_error in onpr; tea.
Qed.

Ltac discr_lhs_hyp H :=
  repeat match type of H with
  | symb_hd (mkApps _ _) = _ => rewrite symb_hd_mkApps_inv in H
  | symb_hd _ = _ => simpl in H
  | None = Some _ => discriminate
  | is_true (rigid_shape (mkApps _ _)) => rewrite rigid_shape_mkApps_inv in H
  | is_true (rigid_shape _) => simpl in H
  | is_true false => discriminate
  end.

Ltac finish_discr :=
  repeat PCUICAstUtils.finish_discr ||
         match goal with
         | [ H : symb_hd _ = _ |- _ ] => discr_lhs_hyp H
         | [ H : is_true (rigid_shape _) |- _ ] => discr_lhs_hyp H
         end.

Ltac prepare_discr :=
  (try match goal with
  | [ H : first_match _ ?lhs = Some _ |- _ ] =>
      match goal with [ X : symb_hd lhs = _ |- _ ] =>
      try match goal with
      | [ e : _ = lhs |- _ ] => rewrite -e //= in X
      | [ e : lhs = _ |- _ ] => rewrite  e //= in X
      end
      | |- _ =>
      let X := fresh "X" in
      apply first_match_to_symb_hd in H as X;
      try match goal with
      | [ e : _ = lhs |- _ ] => rewrite -e //= in X
      | [ e : lhs = _ |- _ ] => rewrite  e //= in X
      end
      end
  | [ H : pattern_matches _ ?lhs _ |- _ ] =>
      match goal with [ X : symb_hd lhs = _ |- _ ] =>
      try match goal with
      | [ e : _ = lhs |- _ ] => rewrite -e //= in X
      | [ e : lhs = _ |- _ ] => rewrite  e //= in X
      end
      | |- _ =>
      let X := fresh "X" in
      apply pattern_to_symb_hd in H as X;
      try match goal with
      | [ e : _ = lhs |- _ ] => rewrite -e //= in X
      | [ e : lhs = _ |- _ ] => rewrite  e //= in X
      end
      end
  | [ H : rigid_arg_pattern_matches _ ?lhs _ |- _ ] =>
      let X := fresh "X" in
      apply rigid_to_shape in H as X
  end);
  repeat PCUICAstUtils.prepare_discr ||
          match goal with
          | H : symb_hd ?t = _, H' : mkApps ?t ?args = ?t' |- _ => rewrite -(symb_hd_mkApps_inv t args) H' in H; discr_lhs_hyp H
          | H : is_true (rigid_shape ?t), H' : mkApps ?t ?args = ?t' |- _ => rewrite -(rigid_shape_mkApps_inv t args) H' in H; discr_lhs_hyp H
          | [ H : symb_hd _ = _ |- _ ] => discr_lhs_hyp H
          | [ H : is_true (rigid_shape _) |- _ ] => discr_lhs_hyp H
          end.

Ltac solve_discr ::=
  (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * ))).
