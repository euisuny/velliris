From Coq Require Import Lists.List String.
From iris.prelude Require Import options.

From Vellvm Require Import
     Utils.Tactics
     Syntax
     Semantics
     Theory
     Utils.PostConditions.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv
     Structures.Monads.

From ITree Require Import
     ITree
     Eq.Eqit
     RecursionFacts.

From Paco Require Import paco.

Import ListNotations.
Import MonadNotation.

(* Syntactic formulation of contexts that work for transformations at the
  block-level on the context of open cfg's *)

(* Example transformation (within a block, doesn't change control flow)

  f (x) -> int y = x;
          while (true) { print 4; read x }

  g () -> int x = 0; f (x)

  ---"optimized"---

  f (x) -> int y = x;
          while (true) { read x; print 4 }

  g () -> int x = 0; f (x)

  *)
Section block_ctxt.

  Notation ocfg := (ocfg dtyp).
  Notation code := (code dtyp).

  (* A context is an open CFG with a hole for the code in a block *)
  Definition ctxt := code -> ocfg.

  Fixpoint remove_block (x : block_id) (l : ocfg) : ocfg :=
    match l with
      | [] => []
      | y::tl => if (eq_dec x (blk_id y)) then remove_block x tl else y::(remove_block x tl)
    end.

  (* Replace a block once in the CFG (block id's should be unique within a list) *)
  Fixpoint replace_block (x : block_id) (b : block dtyp) (l : ocfg) : ocfg :=
    match l with
    | [] => []
    | y::tl => if (eqv_dec_p (blk_id y) x)
             then b::tl
             else y::(replace_block x b tl)
    end.

  Definition bk_change_code (c : code): block dtyp -> block dtyp :=
    fun b =>
      {|
        blk_id := blk_id b;
        blk_phis := blk_phis b;
        blk_code := c;
        blk_term := blk_term b;
        blk_comments := blk_comments b
      |}.

  (* We can transform a CFG into a context by taking the block_id
     of the expected hole. *)
  Definition mk_ctxt : ocfg -> block_id -> ctxt :=
    fun bks id code =>
      match find_block bks id with
      | Some b =>
          replace_block id (bk_change_code code b) bks
      | None => bks
      end.

  Definition code_of_block : ocfg -> block_id -> option code :=
    fun bks id =>
      x <- find_block bks id ;; ret (blk_code x).

  Lemma bk_change_code_ident b:
    bk_change_code (blk_code b) b = b.
  Proof.
    unfold bk_change_code; destruct b; reflexivity.
  Qed.

  Lemma replace_block_ident :
    forall CFG b id,
    find_block CFG id = Some b ->
    replace_block id b CFG = CFG.
  Proof.
    intros.
    revert b id H.
    induction CFG; eauto.
    intros.
    cbn in *.
    destruct (eqv_dec_p (blk_id a) id) eqn : Ha.
    - repeat red in e. subst. inv H; auto.
    - Morphisms.f_equiv. eapply IHCFG. eauto.
  Qed.

  Lemma mk_ctxt_ident :
    forall CFG id entry code,
      code_of_block CFG id = Some code ->
      denote_ocfg (mk_ctxt CFG id code) (id, entry) ≈
      denote_ocfg CFG (id, entry).
  Proof.
    intros CFG id entry code H.
    unfold code_of_block in H.
    unfold bind in H; repeat red in H.
    unfold OptionMonad.Monad_option in H.
    unfold mk_ctxt.
    destruct (find_block CFG id) eqn: Hb; inv H.
    rewrite bk_change_code_ident.
    rewrite (replace_block_ident _ _ _ Hb).
    reflexivity.
  Qed.

  Lemma find_block_stable:
    forall bid entry CFG code code',
      bid <> entry ->
      find_block (mk_ctxt CFG bid code) entry = find_block (mk_ctxt CFG bid code') entry.
  Proof.
    intros.
    unfold find_block, mk_ctxt.
    destruct (find_block CFG bid) eqn: Hb; [ | auto ].
    revert code code' b Hb.
    induction CFG; intros; [ inv Hb | ].
    cbn in Hb. cbn.
    destruct (eqv_dec_p (blk_id a) bid).
    { inv e. inv Hb. cbn.
      destruct (eqv_dec_p (blk_id b) (blk_id b)).
      2 : exfalso; apply n; reflexivity.
      cbn.
      destruct (eqv_dec_p (blk_id b) entry) eqn: Hb'.
      { exfalso. apply H. auto. }
      reflexivity. }
    { specialize (IHCFG code code' _ Hb).
      cbn.
      destruct (eqv_dec_p (blk_id a) entry); auto. }
  Qed.

  Lemma mk_ctxt_eq:
    forall CFG iblk blk code,
      find_block CFG (blk_id blk) = Some iblk ->
      find_block (mk_ctxt CFG (blk_id blk) code) (blk_id (T := dtyp)blk) =
        Some (bk_change_code code iblk).
  Proof.
    intros. unfold mk_ctxt in H.
    revert blk iblk H.
    induction CFG; intros; [ inv H | ].
    unfold find_block in *.
    cbn in *.
    destruct (eqv_dec_p (blk_id a) (blk_id blk)) eqn: Ha.
    - inv H. repeat red in e.
      clear Ha. inv e.
      unfold mk_ctxt. destruct iblk, blk. cbn in *. subst.
      destruct (eqv_dec_p blk_id0 blk_id0).
      2 : { exfalso. apply n; reflexivity. }

      setoid_rewrite find_block_eq.
      2 : { cbn; auto. }
      reflexivity.
    - specialize (IHCFG blk iblk H).
      unfold mk_ctxt.
      cbn. rewrite Ha. rewrite H. cbn.
      rewrite Ha.
      unfold mk_ctxt in IHCFG. unfold find_block in IHCFG.
      rewrite H in IHCFG.
      auto.
  Qed.

  Lemma ocfg_contextual_refinement :
    forall blk id entry CFG code,
      find_block CFG (blk_id blk) = Some blk ->
      (forall id, denote_block blk id ≈ denote_block (bk_change_code code blk) id) ->
      denote_ocfg (mk_ctxt CFG (blk_id blk) (blk_code blk)) (id, entry) ≈
      denote_ocfg (mk_ctxt CFG (blk_id blk) code) (id, entry).
  Proof.
    einit. ecofix CIH.
    intros.
    unfold denote_ocfg.
    setoid_rewrite unfold_iter.
    ebind.
    eapply pbc_intro_h with (RU := eq).
    - clear gL' INCL gH' INCH CIHL CIHH.
      destruct (eqv_dec_p (blk_id blk) entry) eqn : Hb.
      + repeat red in e; subst; clear Hb.
        do 2 rewrite (mk_ctxt_eq _ _ _ _ H0).
        rewrite bk_change_code_ident.
        rewrite H1. reflexivity.

      + rewrite (find_block_stable _ _ _ _ code n).
        reflexivity.

    - intros; subst.
      destruct u2.
      + etau. ebase. right.
        unfold denote_ocfg, iter in CIHL.
        unfold CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree in CIHL.
        destruct p.
        eapply CIHL; eauto.
      + efinal; reflexivity.
  Qed.

End block_ctxt.

