From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.

From ExtLib Require Core.RelDec.

(* General purpose tactics *)
Ltac inv H := inversion H; try subst; clear H.

Ltac destruct_match_goal :=
  repeat match goal with
    | |- context[match ?x with | _ => _ end] =>
        destruct x; cbn
  end.

Ltac destruct_match_sum :=
  repeat match goal with
    | [ H : match ?x with
            | inl _ => _
            | inr _ => _
            end = _ |- _] =>
        let Hx := fresh "H" in
      destruct x eqn: Hx; inversion H; subst
end.

Ltac destruct_match :=
  repeat match goal with
    | [ H : match ?x with
            | _ => _
            end = _ |- _] =>
        let Hx := fresh "H" in
      destruct x eqn: Hx; inversion H; subst
end.

Ltac destruct_if :=
  repeat match goal with
    | [ H : (if ?x then _ else _) = _ |- _] =>
        let Hx := fresh "H" in
      destruct x eqn: Hx; inversion H; subst
end.

Ltac destruct_if_goal :=
  repeat match goal with
    | [ |- context[if ?x then _ else _] ] =>
        let Hx := fresh "H" in
      destruct x eqn: Hx; inversion Hx; subst
  end.

Ltac reldec :=
  repeat match goal with
  | [ H: RelDec.rel_dec _ _ = true |- _] =>
      rewrite RelDec.rel_dec_correct in H; subst
  | [ H: RelDec.rel_dec _ _ = false |- _] =>
      apply RelDec.neg_rel_dec_correct in H
  end.

From ITree Require Import ITree Eq.Eqit Basics Eq.EqAxiom.
From ITree.Interp Require Import TranslateFacts InterpFacts.

(* ITree-related tactics *)
Module DenoteTactics.

  #[export] Hint Rewrite @bind_ret_l : rwexp.
  #[export] Hint Rewrite @bind_bind : rwexp.
  #[export] Hint Rewrite @TranslateFacts.translate_ret : rwexp.
  #[export] Hint Rewrite @TranslateFacts.translate_bind : rwexp.
  #[export] Hint Rewrite @TranslateFacts.translate_trigger : rwexp.

  Ltac go := autorewrite with rwexp.

End DenoteTactics.

Ltac to_eq :=
  apply EqAxiom.bisimulation_is_eq.

Tactic Notation "to_eq" "in" hyp(H) :=
  apply EqAxiom.bisimulation_is_eq in H.

Tactic Notation "unfold_cat" "in" hyp(H) :=
    rewrite /resum in H;
    rewrite /ReSum_inr in H;
    rewrite /ReSum_inl in H;
    rewrite /ReSum_id in H;
    rewrite /cat in H;
    rewrite /Cat_IFun in H;
    rewrite /id_ in H;
    rewrite /inr_ in H;
    rewrite /Inr_sum1 in H;
    rewrite /inl_ /Inl_sum1 /resum /Id_IFun in H.

Ltac unfold_cat :=
    rewrite /resum ;
    rewrite /ReSum_inr ;
    rewrite /ReSum_inl ;
    rewrite /ReSum_id ;
    rewrite /cat ;
    rewrite /Cat_IFun ;
    rewrite /id_ ;
    rewrite /inr_ ;
    rewrite /Inr_sum1;
    rewrite /inl_ /Inl_sum1 /resum /Id_IFun.

Ltac bind_bind :=
  let BIND := fresh "Hbind" in
  match goal with
  | |- context [ ITree.bind (ITree.bind ?s ?k) ?h  ] =>
      pose proof (@bind_bind _ _ _ _ s k h) as BIND;
      eapply bisimulation_is_eq in BIND; rewrite BIND; clear BIND
  end.
