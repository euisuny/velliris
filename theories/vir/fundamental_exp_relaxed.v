From Coq Require Import String List Program.Equality.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export gen_heap ghost_map.
From iris.base_logic Require Import gset_bij.

From ITree Require Import
  ITree Eq
  Interp.InterpFacts Interp.RecursionFacts Events.StateFacts TranslateFacts.

From Vellvm Require Import Syntax.LLVMAst Syntax.DynamicTypes
  Semantics.InterpretationStack Handlers Utils.Util Semantics.LLVMEvents.

From Equations Require Import Equations.

From Paco Require Import paco.

From velliris.logic Require Import satisfiable.
From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
   vir spec globalbij heapbij frame_laws primitive_laws bij_laws logical_relations.
From velliris.utils Require Import no_event.

Set Default Proof Using "Type*".

Import ListNotations.
Import SemNotations.
Import LLVMAst.


(** *Reflexivity theorems for logical relations *)
Section fundamental_exp.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

  Ltac exp_logrel_pre d :=
    destruct d; try iApply exp_conv_raise.

  Ltac exp_logrel_ret :=
    setoid_rewrite interp_ret; iApply sim_expr_base; iExists _, _; iFrame;
    iSplitL ""; [ | iSplitL ""]; try (iPureIntro; reflexivity);
      iApply uval_rel_lift; eauto;
      rewrite unfold_dval_rel; auto.

  Ltac exp_logrel_num dt d :=
    exp_logrel_pre dt; exp_logrel_pre d; exp_logrel_ret;
    iExists _, _; do 2 (iSplitL ""; [ by iPureIntro | ]);
      cbn; eauto.

  (* Utility lemma about [expr_inv]. TODO move to [logical_relations] *)
  Lemma expr_inv_local_env_includes {T} x {i_t i_s L_t L_s} (e_t e_s : exp T):
    x ∈ (exp_local_ids e_t) ->
    x ∈ (exp_local_ids e_s) ->
    expr_inv i_t i_s L_t L_s e_t e_s -∗
    ⌜x ∈ L_t.*1 /\ x ∈ L_s.*1⌝.
  Proof. Admitted.

  (* ------------------------------------------------------------------------ *)

  Lemma expr_logrel_EXP_Ident :
    forall (id : LLVMAst.ident) (dt : option dtyp) i_t i_s L_t L_s,
      expr_inv i_t i_s L_t L_s (EXP_Ident id) (EXP_Ident id : exp uvalue) -∗
      exp_conv (denote_exp dt (EXP_Ident id)) ⪯
      exp_conv (denote_exp dt (EXP_Ident id))
      [{ (v_t, v_s),
          uval_rel v_t v_s ∗
          expr_inv i_t i_s L_t L_s (EXP_Ident id) (EXP_Ident id : exp uvalue) }].
  Proof.
    iIntros (id dt i_t i_s L_t L_s) "HC"; cbn.
    rewrite /lookup_id; destruct id; cbn.
    { (* Global *)
      rewrite /exp_conv.

      rewrite interp_translate interp_bind interp_vis.
      rewrite bind_bind bind_trigger.
      cbn. setoid_rewrite interp_ret.
      iApply sim_expr_vis.
      iApply (sim_expr_bupd_mono with "[HC]"); [ | iApply sim_global_read; eauto].
      iIntros (??) "H".
      iDestruct "H" as (????) "H".
      rewrite H H0; do 2 rewrite bind_ret_l.
      rewrite !bind_tau !bind_ret_l.
      iApply sim_expr_tau. iApply sim_expr_base. iModIntro.
      iExists (dvalue_to_uvalue v_t), (dvalue_to_uvalue v_s).
      do 2 (iSplitL ""; [ iPureIntro; reflexivity | ]); iFrame.
      iApply (dval_rel_lift with "H"). }
    { (* Local *)
      rewrite /exp_conv.

      rewrite interp_translate interp_vis.
      setoid_rewrite InterpFacts.interp_ret.
      rewrite bind_trigger.
      iApply sim_expr_vis; rewrite !subevent_subevent.

      iDestruct (expr_inv_local_env_includes id with "HC") as %(Ht & Hs);
      [ set_solver | set_solver | ].

      iApply sim_expr_bupd_mono ;
        [ | iApply (expr_local_read_refl with "HC")]; eauto.
      iIntros (??) "H".
      iDestruct "H" as (????) "H".
      rewrite H H0. rewrite !bind_ret_l.
      iApply sim_expr_tau; iApply sim_expr_base.
      iExists _, _; by iFrame. }
   Qed.

  (* TODO: Factor out the [expr_inv] into an arbitrary invariant *)
   Lemma expr_logrel_ind_case :
     forall (elts : list (dtyp * exp dtyp)) i_t i_s L_t L_s Vexp (Exp : _ -> exp dtyp),
    (* [uval_rel] nil case *)
    □ (uval_rel (Vexp []) (Vexp [])) -∗
    (* [uval_rel] cons case *)
    □ (∀ v_t v_s l_t l_s,
      uval_rel v_t v_s -∗
      uval_rel (Vexp l_t) (Vexp l_s) -∗
      uval_rel (Vexp (v_t :: l_t)) (Vexp (v_s :: l_s))) -∗
    (* [expr_inv] over the struct values *)
    □ (expr_inv i_t i_s L_t L_s (Exp elts) (Exp elts) -∗
       expr_frame_inv i_t i_s L_t L_s ∗
        (∀ x, ⌜In x elts⌝ -∗
          expr_local_env_inv i_t i_s (filter_local_ids L_t L_s x.2 x.2))) -∗
    □ (∀ x : dtyp * exp dtyp,
      ⌜In x elts⌝
      → ∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp),
          expr_inv i_t i_s L_t L_s x.2 x.2 -∗
            exp_conv (denote_exp a x.2) ⪯
            exp_conv (denote_exp a x.2)
            [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv i_t i_s L_t L_s x.2 x.2 }]) -∗
      expr_inv i_t i_s L_t L_s (Exp elts) (Exp elts) -∗
      r <- exp_conv
            (map_monad (λ '(dt0, ex), (denote_exp (Some dt0) ex)) elts);;
      Ret (Vexp r)
      ⪯
      r <-  exp_conv (map_monad (λ '(dt0, ex), (denote_exp (Some dt0) ex)) elts);;
      Ret (Vexp r)
    [{ (v_t, v_s),
        uval_rel v_t v_s ∗
          expr_inv i_t i_s L_t L_s (Exp elts) (Exp elts) }].
  Proof.
    iIntros (elts i_t i_s L_t L_s Vexp Exp) "#Hbase #Hind #Hinvp #IH HI".
    rewrite /exp_conv.
    (* We follow by induction on the structure elements. *)
    iInduction elts as [] "IHl".
    (* nil case *)
    { cbn; rewrite interp_ret bind_ret_l.
      iApply sim_expr_base; iExists _, _; iFrame;
      iSplitL ""; [ | iSplitL ""]; try (iPureIntro; reflexivity); done. }
    (* cons case *)
    { cbn. destruct a. rewrite /exp_conv.
      rewrite interp_bind bind_bind.
      iApply sim_expr_bind.
      iAssert (□
        (∀ x : dtyp * exp dtyp,
          ⌜In x elts⌝ →
          ∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp),
            expr_inv i_t i_s L_t L_s x.2 x.2 -∗
            exp_conv (denote_exp a x.2) ⪯ exp_conv (denote_exp a x.2)
        [{ (v_t, v_s), uval_rel v_t v_s ∗ expr_inv i_t i_s L_t L_s x.2 x.2  }]))%I as "#Helts".
      { iModIntro. iIntros (x Hin dt' l') "Hinv".
        assert ((d, e) = x \/ In x elts) by (by right).
        by iSpecialize ("IH" $! _ H _  l' with "Hinv"). }

  (*     iSpecialize ("IHl" with "Helts"); iClear "Helts". *)
  (*     assert (EQ: (d, e) = (d, e) ∨ In (d, e) elts) by (left; auto). *)
  (*     iSpecialize ("IH" $! (d, e) EQ _ _); clear EQ; cbn. *)
  (*     iSpecialize ("IH" with "HI"). *)
  (*     iApply (sim_expr_bupd_mono with "[IHl]"); [ | done]. *)
  (*     iIntros (??) "Hr". *)
  (*     iDestruct "Hr" as (????) "[Hv Hinv]". *)
  (*     rewrite H H0. do 2 rewrite bind_ret_l. *)
  (*     iSpecialize ("IHl" with "Hinv"). iModIntro. *)
  (*     do 2 rewrite interp_bind bind_bind. *)
  (*     setoid_rewrite interp_ret. *)
  (*     setoid_rewrite bind_ret_l. *)
  (*     iPoseProof sim_expr_fmap_inv as "Hfmap". *)
  (*     iSpecialize ("Hfmap" with "IHl"). *)
  (*     iApply sim_expr_bind. *)
  (*     iApply (sim_expr_bupd_mono with "[Hv]"); [ | done]. *)
  (*     iIntros (??) "Hp". rewrite /lift_post. *)
  (*     iDestruct "Hp" as (????????) "[Hp CI]". *)
  (*     apply eqit_inv_Ret in H3, H4; subst. rewrite H1 H2. do 2 rewrite bind_ret_l. *)
  (*     iApply sim_expr_base. iModIntro; do 2 iExists _. eauto. *)
  (*     iSplitL ""; [| iSplitL ""]; auto; iFrame. *)
  (*     iApply ("Hind" with "Hv Hp"). } *)
  (* Qed. *)
  Abort.

  Lemma expr_logrel_EXP_Integer:
    ∀ (x : int) (dt : option dtyp),
      ⊢ exp_conv (denote_exp dt (EXP_Integer x))
        ⪯ exp_conv (denote_exp dt (EXP_Integer x))
      [{ (v_t, v_s), uval_rel v_t v_s }].
  Proof.
    iIntros (x dt).
    exp_logrel_pre dt. exp_logrel_pre d.
    rewrite /denote_exp /lift_undef_or_err.
    destruct (Functor.fmap dvalue_to_uvalue (coerce_integer_to_int sz x)) eqn: Hx;
      destruct unEitherT, s;
      [iApply exp_conv_raiseUB
      | iApply exp_conv_raiseUB
      | iApply exp_conv_raise | ].
    setoid_rewrite interp_ret. iApply sim_expr_base; iExists _, _; iFrame.
    iSplitL ""; [ | iSplitL ""]; try (iPureIntro; reflexivity).
    inversion Hx.
    destruct (EitherMonad.unEitherT (coerce_integer_to_int sz x));
      destruct s; inversion H0; clear H0; subst.

    assert (sz = 1%N \/ sz = 8%N \/ sz = 32%N \/ sz = 64%N).
    { destruct sz; inversion Hx; destruct p; cbn in H0; inversion H0.
      - repeat (destruct p; inversion H1); tauto.
      - tauto. }
    destruct H as [H | [H | [H | H ] ] ]; subst; cbn in Hx; inversion Hx;
      iApply uval_rel_lift; eauto;
      rewrite unfold_dval_rel; cbn; subst; eauto.
    Unshelve. all : try eauto.
  Qed.

  Lemma expr_logrel_EXP_Float:
    ∀ x (dt : option dtyp),
      ⊢ exp_conv (denote_exp dt (EXP_Float x))
        ⪯ exp_conv (denote_exp dt (EXP_Float x))
      [{ (v_t, v_s),uval_rel v_t v_s }].
  Proof.
    iIntros (??); exp_logrel_num dt d.
  Qed.

  Lemma expr_logrel_EXP_Hex:
    ∀ x (dt : option dtyp),
      ⊢ exp_conv (denote_exp dt (EXP_Hex x))
        ⪯ exp_conv (denote_exp dt (EXP_Hex x))
      [{ (v_t, v_s), uval_rel v_t v_s }].
  Proof.
    iIntros (??); exp_logrel_num dt d.
  Qed.

  Lemma expr_logrel_EXP_Double:
    ∀ x (dt : option dtyp),
      ⊢ exp_conv (denote_exp dt (EXP_Double x))
        ⪯ exp_conv (denote_exp dt (EXP_Double x))
      [{ (v_t, v_s),uval_rel v_t v_s }].
  Proof.
    iIntros (??); exp_logrel_num dt d.
  Qed.

  Lemma expr_logrel_EXP_Bool:
    ∀ x (dt : option dtyp),
      ⊢ exp_conv (denote_exp dt (EXP_Bool x))
        ⪯ exp_conv (denote_exp dt (EXP_Bool x))
      [{ (v_t, v_s),uval_rel v_t v_s }].
  Proof.
    iIntros (b?).
    exp_logrel_pre b; exp_logrel_ret.
  Qed.

  (* Lemma expr_logrel_EXP_Cstring: *)
  (*   ∀ (elts : list (dtyp * exp dtyp)) (dt : option dtyp) C i_t i_s A_t A_s , *)
  (*     □ (∀ x : dtyp * exp dtyp, *)
  (*         ⌜In x elts⌝ → *)
  (*         ∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp), *)
  (*         expr_inv a0 i_t i_s A_t A_s  -∗ *)
  (*         exp_conv (denote_exp a x.2) ⪯ *)
  (*         exp_conv (denote_exp a x.2) *)
  (*         [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv a0 i_t i_s A_t A_s  }]) -∗ *)
  (*       expr_inv C i_t i_s A_t A_s  -∗ *)
  (*       exp_conv (denote_exp dt (EXP_Cstring elts)) ⪯ *)
  (*       exp_conv (denote_exp dt (EXP_Cstring elts)) *)
  (*       [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv C i_t i_s A_t A_s  }]. *)
  (* Proof. *)
  (*   intros elts dt C ? ? ? ? . *)
  (*   cbn; setoid_rewrite interp_bind; setoid_rewrite interp_ret. *)
  (*   iApply expr_logrel_ind_case; auto. *)
  (*   { iModIntro; cbn; iApply uval_rel_lift; eauto; *)
  (*       rewrite unfold_dval_rel; auto. cbn; done. } *)
  (*   iModIntro. *)
  (*   iIntros (v_t v_s l_t l_s) "Hv Hl". *)
  (*   iApply (uval_rel_array_cons with "Hv Hl"); cbn; iFrame. *)
  (* Qed. *)

  (* Lemma expr_logrel_EXP_Struct: *)
  (*   ∀ (elts : list (dtyp * exp dtyp)) (dt : option dtyp) C i_t i_s A_t A_s , *)
  (*     □ (∀ x : dtyp * exp dtyp, *)
  (*         ⌜In x elts⌝ → *)
  (*         ∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp), *)
  (*         expr_inv a0 i_t i_s A_t A_s  -∗ *)
  (*         exp_conv (denote_exp a x.2) ⪯ *)
  (*         exp_conv (denote_exp a x.2) *)
  (*         [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv a0 i_t i_s A_t A_s  }]) -∗ *)
  (*       expr_inv C i_t i_s A_t A_s  -∗ *)
  (*       exp_conv (denote_exp dt (EXP_Struct elts)) ⪯ *)
  (*       exp_conv (denote_exp dt (EXP_Struct elts)) *)
  (*     [{ (v_t, v_s), uval_rel v_t v_s ∗ expr_inv C i_t i_s A_t A_s  }]. *)
  (* Proof. *)
  (*   intros elts dt C ? ? ? ? . *)
  (*   cbn; setoid_rewrite interp_bind; setoid_rewrite interp_ret. *)
  (*   iApply expr_logrel_ind_case. *)
  (*   { iModIntro; cbn; iApply uval_rel_lift; eauto; *)
  (*       rewrite unfold_dval_rel; auto. cbn; done. } *)
  (*   iModIntro. *)
  (*   iIntros (v_t v_s l_t l_s) "Hv Hl". *)
  (*   iApply (uval_rel_struct_cons with "Hv Hl"). *)
  (* Qed. *)

  (* Lemma expr_logrel_EXP_Array: *)
  (*   ∀ (elts : list (dtyp * exp dtyp)) (dt : option dtyp) C i_t i_s A_t A_s , *)
  (*       □ (∀ x : dtyp * exp dtyp, *)
  (*         ⌜In x elts⌝ → *)
  (*         ∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp), *)
  (*         expr_inv a0 i_t i_s A_t A_s  -∗ *)
  (*         exp_conv (denote_exp a x.2) ⪯ *)
  (*         exp_conv (denote_exp a x.2) *)
  (*         [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv a0 i_t i_s A_t A_s  }]) -∗ *)
  (*       expr_inv C i_t i_s A_t A_s  -∗ *)
  (*       exp_conv (denote_exp dt (EXP_Array elts)) ⪯ *)
  (*       exp_conv (denote_exp dt (EXP_Array elts)) *)
  (*     [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv C i_t i_s A_t A_s  }]. *)
  (* Proof. *)
  (*   iIntros (elts dt C ? ? ? ? ) "#IH HI". *)
  (*   cbn; setoid_rewrite interp_bind; setoid_rewrite interp_ret. *)
  (*   iApply expr_logrel_ind_case; auto. *)
  (*   { iModIntro; cbn; iApply uval_rel_lift; eauto; *)
  (*       rewrite unfold_dval_rel; auto. cbn; done. } *)
  (*   iModIntro. *)
  (*   iIntros (v_t v_s l_t l_s) "Hv Hl". *)
  (*   iApply (uval_rel_array_cons with "Hv Hl"). *)
  (* Qed. *)

  (* TODO Move *)
  Lemma exp_local_ids_acc_commute {T} (e : exp T) acc :
    exp_local_ids_ e acc = exp_local_ids e ++ acc.
  Proof.
    revert acc.
    induction e; cbn; try rewrite app_nil_r; eauto.
    (* Ident *)
    { destruct id; eauto. }
    (* Binop *)
    { intros.
      do 2 rewrite IHe2. rewrite app_nil_r.
      do 2 rewrite IHe1. by rewrite app_assoc. }
    (* ICmp *)
    { intros.
      do 2 rewrite IHe2. rewrite app_nil_r.
      do 2 rewrite IHe1. by rewrite app_assoc. }
    (* GEP *)
    { intros. destruct ptrval; cbn.
      by rewrite app_assoc. }
  Qed.

  (* TODO Move to [stdpp] ? -- general utility *)
  Lemma list_intersection_subset {A} `{EqDecision A} (l l' : list A):
    l ⊆ l' ->
    list_intersection l l' = l.
  Proof.
    revert l'.
    dependent induction l; eauto; cbn.
    intros.
    destruct (decide_rel elem_of a l'); try set_solver.
    f_equiv. eapply IHl; set_solver.
  Qed.

  Lemma list_intersection_eq {A} `{EqDecision A} (l : list A):
    list_intersection l l = l.
  Proof.
    apply list_intersection_subset; set_solver.
  Qed.

  (* TODO Move: lemma about filter keys *)
  Lemma filter_keys_nil L_t L_s :
    filter_keys nil L_t L_s = nil.
  Proof. done. Qed.

  Opaque filter_keys.

  (* TODO Move: more about [expr_local_env_inv] *)
  Lemma expr_local_env_inv_nil i_t i_s :
    (expr_local_env_inv i_t i_s [] ⊣⊢ emp)%I.
  Proof.
    rewrite /expr_local_env_inv; by cbn.
  Qed.

  Lemma expr_local_env_inv_binop_invert
    {T} i_t i_s L_t L_s τ iop (e1 e2: exp T):
    expr_local_env_inv i_t i_s
      (filter_local_ids L_t L_s
        (OP_IBinop iop τ e1 e2) (OP_IBinop iop τ e1 e2)) -∗
    expr_local_env_inv i_t i_s
      (filter_keys (exp_local_ids e1 ++ exp_local_ids e2) L_t L_s).
  Proof.
    rewrite {1}/filter_local_ids; cbn -[filter_keys]; iIntros "Hv".
    repeat rewrite exp_local_ids_acc_commute; rewrite app_nil_r.
    by rewrite /filter_local_ids list_intersection_eq.
  Qed.

  Lemma expr_local_env_inv_app_invert i_t i_s L_t L_s l1 l2:
    expr_local_env_inv i_t i_s (filter_keys (l1 ++ l2) L_t L_s) -∗
    expr_local_env_inv i_t i_s (filter_keys l1 L_t L_s) ∗
    expr_local_env_inv i_t i_s (filter_keys l2 L_t L_s).
  Proof.
    iInduction l1 as [ | ] "IH" forall (l2); cbn -[filter_keys].
    { (* nil case *)
      rewrite filter_keys_nil expr_local_env_inv_nil; iIntros "$". }

    (* cons case *)
  Admitted.

  (* Inversion rule for [expr_inv] for binop expression. *)
  Lemma expr_inv_binop_invert
    {T} i_t i_s L_t L_s τ iop (e1 e2 : exp T):
    expr_inv
      i_t i_s L_t L_s
      (OP_IBinop iop τ e1 e2)
      (OP_IBinop iop τ e1 e2) -∗
    expr_inv i_t i_s L_t L_s e1 e1 ∗
    expr_local_env_inv i_t i_s (filter_local_ids L_t L_s e2 e2).
  Proof.
    iIntros "Hb"; iDestruct "Hb" as "(Hf_inv & Hl)"; iFrame.
    iPoseProof (expr_local_env_inv_binop_invert with "Hl") as "Hl".
  Qed.

  Lemma expr_logrel_OP_IBinop:
    ∀ (iop : ibinop) (t : dtyp) (e1 e2 : exp dtyp) (dt : option dtyp)
      i_t i_s L_t L_s,
      □ (∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp),
          expr_inv i_t i_s L_t L_s e1 e1 -∗
          exp_conv (denote_exp a e1) ⪯
          exp_conv (denote_exp a e1)
          [{ (v_t, v_s),
              uval_rel v_t v_s ∗
              expr_inv i_t i_s L_t L_s e1 e1 }]) -∗
        (∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp),
          expr_inv i_t i_s L_t L_s e2 e2 -∗
          exp_conv (denote_exp a e2) ⪯
          exp_conv (denote_exp a e2)
          [{ (v_t, v_s),
              uval_rel v_t v_s ∗
              expr_inv i_t i_s L_t L_s e2 e2  }]) -∗
        expr_inv i_t i_s L_t L_s
          (OP_IBinop iop t e1 e2)
          (OP_IBinop iop t e1 e2)  -∗
        exp_conv (denote_exp dt (OP_IBinop iop t e1 e2)) ⪯
        exp_conv (denote_exp dt (OP_IBinop iop t e1 e2))
      [{ (v_t, v_s),
          uval_rel v_t v_s ∗
          expr_inv i_t i_s L_t L_s
            (OP_IBinop iop t e1 e2)
            (OP_IBinop iop t e1 e2) }].
  Proof.
    iIntros (iop t e1 e2 dt ????) "#IH IH1 HI".

    (* FIXME repair *)
    iSpecialize ("IH" with "HI").
    cbn; setoid_rewrite interp_bind.
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[IH1]"); [ | iApply "IH"].
    iIntros (e_t e_s) "H".
    iDestruct "H" as (?? Ht Hs) "(Hv & HI)".
    rename v_t into v1', v_s into v1.
    rewrite Ht Hs; clear Ht Hs.
    do 2 rewrite bind_ret_l interp_bind.

    iSpecialize ("IH1" with "HI").
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[Hv]"); [ | iApply "IH1"].
    clear e_t e_s.
    iIntros (e_t e_s) "H".
    iDestruct "H" as (?? Ht Hs) "(Hv0 & HI)".
    rewrite Ht Hs; clear Ht Hs.
    do 2 rewrite bind_ret_l. subst.
    rename v_t into v2', v_s into v2.

    do 2 rewrite interp_ret. iApply sim_expr_base.
    do 2 iExists _. do 2 (iSplitL ""; [ done | ]).
    iFrame.
    iApply (uval_rel_binop with "Hv Hv0").
  Qed.

  (* Lemma expr_logrel_OP_Conversion: *)
  (*   ∀ (conv : conversion_type) (t_from : dtyp) (e : exp dtyp) (t_to : dtyp) *)
  (*     (dt : option dtyp) (C : gmap (vir.loc * vir.loc) Qp) i_t i_s A_t A_s , *)
  (*     □ (∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp), *)
  (*         expr_inv a0 i_t i_s A_t A_s  -∗ *)
  (*         exp_conv (denote_exp a e) ⪯ *)
  (*         exp_conv (denote_exp a e) *)
  (*         [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv a0 i_t i_s A_t A_s  }]) -∗ *)
  (*       expr_inv C i_t i_s A_t A_s  -∗ *)
  (*     exp_conv (denote_exp dt (OP_Conversion conv t_from e t_to)) ⪯ *)
  (*     exp_conv (denote_exp dt (OP_Conversion conv t_from e t_to)) *)
  (*     [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv C i_t i_s A_t A_s  }]. *)
  (* Proof. *)
  (*   iIntros (conv t_from e t_to dt C ? ? ? ? ) "#IH HI". *)

  (*   iSpecialize ("IH" with "HI"). *)
  (*   cbn; setoid_rewrite interp_bind. *)
  (*   iApply sim_expr_bind. *)
  (*   iApply sim_expr_bupd_mono; [ | iApply "IH"]. *)
  (*   iIntros (e_t e_s) "H". *)
  (*   iDestruct "H" as (?? Ht Hs) "(Hv & HI)". *)
  (*   subst. *)
  (*   rewrite Ht Hs; clear Ht Hs. *)
  (*   do 2 rewrite bind_ret_l. *)
  (*   do 2 rewrite interp_ret. iApply sim_expr_base. *)
  (*   do 2 iExists _. do 2 (iSplitL ""; [ done | ]). *)
  (*   rewrite /uval_rel. iFrame. *)
  (*   iModIntro; iIntros (??). inversion H. *)
  (* Qed. *)

  (* Lemma expr_logrel_OP_ICmp: *)
  (*   forall (cmp : icmp) (t : dtyp) (e1 e2 : exp dtyp) (dt : option dtyp) *)
  (*     (C : gmap (vir.loc * vir.loc) Qp) i_t i_s A_t A_s , *)
  (*     □ (∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp), *)
  (*         expr_inv a0 i_t i_s A_t A_s  -∗ *)
  (*         exp_conv (denote_exp a e1) ⪯ *)
  (*         exp_conv (denote_exp a e1) *)
  (*         [{ (v_t, v_s), uval_rel v_t v_s ∗ expr_inv a0 i_t i_s A_t A_s  }]) -∗ *)
  (*     □ (∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp), *)
  (*         expr_inv a0 i_t i_s A_t A_s  -∗ *)
  (*         exp_conv (denote_exp a e2) ⪯ *)
  (*         exp_conv (denote_exp a e2) *)
  (*         [{ (v_t, v_s), uval_rel v_t v_s ∗ expr_inv a0 i_t i_s A_t A_s  }]) -∗ *)
  (*     expr_inv C i_t i_s A_t A_s  -∗ *)
  (*     exp_conv (denote_exp dt (OP_ICmp cmp t e1 e2)) ⪯ *)
  (*     exp_conv (denote_exp dt (OP_ICmp cmp t e1 e2)) *)
  (*     [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv C i_t i_s A_t A_s  }]. *)
  (* Proof. *)
  (*   iIntros (cmp t e1 e2 dt C ? ? ? ? ) "#IH1 #IH2 HI". *)

  (*   iSpecialize ("IH1" with "HI"). *)
  (*   cbn; setoid_rewrite interp_bind. *)
  (*   iApply sim_expr_bind. *)

  (*   iApply sim_expr_bupd_mono; [ | iApply "IH1"]. *)
  (*   iIntros (e_t e_s) "H". *)
  (*   iDestruct "H" as (?? Ht Hs) "(Hv & HI)". *)
  (*   subst. *)
  (*   rewrite Ht Hs; clear Ht Hs. *)
  (*   do 2 rewrite bind_ret_l. *)
  (*   rewrite /uvalue_to_dvalue_uop. *)
  (*   cbn. *)
  (*   do 2 rewrite interp_bind. *)
  (*   iApply sim_expr_bind. *)
  (*   iSpecialize ("IH2" with "HI"). *)

  (*   iApply (sim_expr_bupd_mono with "[Hv]"); [ | iApply "IH2"]. *)
  (*   clear e_t e_s. *)
  (*   iIntros (e_t e_s) "H". *)
  (*   iDestruct "H" as (?? Ht Hs) "(Hv' & HI)". *)
  (*   subst. *)
  (*   rewrite Ht Hs; clear Ht Hs. *)
  (*   do 2 rewrite bind_ret_l. *)
  (*   do 2 rewrite interp_ret. *)
  (*   iApply sim_expr_base. *)
  (*   do 2 iExists _. do 2 (iSplitL ""; [ done | ]). *)
  (*   iModIntro; iSplitL "Hv Hv'"; [ | done]. *)
  (*   iApply (uval_rel_icmp with "Hv Hv'"). *)
  (* Qed. *)

  (* Lemma expr_logrel_EXP_GEP : *)
  (*   forall (t : dtyp) (ptrval : dtyp * exp dtyp) (dt : option dtyp) *)
  (*     (idxs : list (dtyp * exp dtyp)) (C : gmap (vir.loc * vir.loc) Qp) *)
  (*     i_t i_s A_t A_s , *)
  (*     □ (∀ x : dtyp * exp dtyp, *)
  (*       ⌜In x idxs⌝ *)
  (*       → ∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp), *)
  (*         expr_inv a0 i_t i_s A_t A_s  -∗ *)
  (*         exp_conv (denote_exp a x.2) ⪯ *)
  (*         exp_conv (denote_exp a x.2) *)
  (*       [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv a0 i_t i_s A_t A_s  }]) -∗ *)
  (*     □ (∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp), *)
  (*         expr_inv a0 i_t i_s A_t A_s  -∗ *)
  (*         exp_conv (denote_exp a ptrval.2) ⪯ *)
  (*         exp_conv (denote_exp a ptrval.2) *)
  (*       [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv a0 i_t i_s A_t A_s  }]) -∗ *)
  (*     expr_inv C i_t i_s A_t A_s  -∗ *)
  (*     exp_conv (denote_exp dt (OP_GetElementPtr t ptrval idxs)) ⪯ *)
  (*     exp_conv (denote_exp dt (OP_GetElementPtr t ptrval idxs)) *)
  (*   [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv C i_t i_s A_t A_s  }]. *)
  (* Proof. *)
  (*   iIntros (t (ptr_t &e1) dt idxs C ? ? ? ? ) "#IH1 #IH2 HI". *)

  (*   cbn; setoid_rewrite interp_bind. *)
  (*   iSpecialize ("IH2" with "HI"). *)
  (*   iApply sim_expr_bind. *)
  (*   iApply (sim_expr_bupd_mono with "[IH1]"); [ | iApply "IH2"]. *)
  (*   iIntros (e_t e_s) "H". *)

  (*   iDestruct "H" as (?? Ht Hs) "(Hv & HI)". *)
  (*   rename v_t into v1', v_s into v1. *)
  (*   rewrite Ht Hs; clear Ht Hs. *)
  (*   do 2 rewrite bind_ret_l interp_bind. *)

  (*   setoid_rewrite interp_ret. *)

  (*   iInduction idxs as [] "IHl". *)
  (*   - cbn. rewrite interp_ret bind_ret_l. *)
  (*     rewrite bind_ret_l. iApply sim_expr_base. *)
  (*     iExists (UVALUE_GetElementPtr t v1' []), (UVALUE_GetElementPtr t v1 []). *)
  (*     iModIntro. do 2 (iSplitL ""; [ done | ]). *)
  (*     iSplitL "Hv"; [ | done]. *)
  (*     rewrite /uval_rel; cbn. *)
  (*     iIntros (??). inversion H. *)

  (*   - cbn. destruct a. rewrite interp_bind; do 2 rewrite bind_bind. *)
  (*     iApply sim_expr_bind. *)
  (*     iAssert (□ *)
  (*       (∀ x : dtyp * exp dtyp, *)
  (*         ⌜In x idxs⌝ → *)
  (*         ∀ (a : option dtyp) (a0 : gmap (vir.loc * vir.loc) Qp), *)
  (*         expr_inv a0 i_t i_s A_t A_s  -∗ *)
  (*           exp_conv (denote_exp a x.2) ⪯exp_conv (denote_exp a x.2) *)
  (*           [{ (v_t, v_s),uval_rel v_t v_s ∗ expr_inv a0 i_t i_s A_t A_s  }]))%I as "Helts". *)
  (*     { iModIntro. iIntros (x Hin dt' C') "Hinv". *)
  (*       assert ((d, e) = x \/ In x idxs) by (by right). *)
  (*       by iSpecialize ("IH1" $! _ H with "Hinv"). } *)
  (*     assert (EQ : ((d, e) = (d, e) \/ In (d, e) idxs)). { by left. } *)
  (*     iSpecialize ("IH1" $! _ EQ with "HI"). *)
  (*     iApply (sim_expr_bupd_mono with "[Hv]"); [ | done]. *)

  (*     iIntros (??) "Hr". *)
  (*     iDestruct "Hr" as (????) "[Hv' Hinv]". *)
  (*     rewrite H H0. do 2 rewrite bind_ret_l. *)
  (*     iSpecialize ("IHl" with "Helts"). *)
  (*     do 2 rewrite interp_bind bind_bind. *)
  (*     setoid_rewrite interp_ret. *)
  (*     setoid_rewrite bind_ret_l. *)
  (*     iPoseProof sim_expr_fmap_inv as "Hfmap". *)
  (*     iSpecialize ("IHl" with "Hv Hinv"). *)
  (*     iMod "IHl". iSpecialize ("Hfmap" with "IHl"). *)
  (*     iApply sim_expr_bind. *)
  (*     iApply (sim_expr_bupd_mono with "[Hv']"); [ | done]. *)
  (*     iIntros (??) "Hp". rewrite /lift_post. *)
  (*     iDestruct "Hp" as (????????) "[Hp CI]". *)
  (*     apply eqit_inv_Ret in H3, H4; subst. rewrite H1 H2. do 2 rewrite bind_ret_l. *)
  (*     iApply sim_expr_base. iModIntro; do 2 iExists _. eauto. *)
  (* Qed. *)

  Tactic Notation "expr_case" constr(lem) :=
    iApply (sim_expr_mono with "[HI]"); last iApply lem;
        eauto;
      iIntros (??) "H"; iDestruct "H" as (????) "Hv";
      iExists _, _; by iFrame.

  (* Reflexivity theorems *)
  Theorem expr_logrel_relaxed_refl e:
    (⊢ expr_logrel_relaxed e e)%I.
  Proof.
    iIntros. rewrite /expr_logrel_relaxed.
    iInduction e as [] "IH" using AstLib.exp_ind;
    iIntros (τ ? ? L_t L_s) "HI".
    { (* EXP_Ident *)
      by iApply expr_logrel_EXP_Ident. }
    (* Numeric cases *)
    { iApply (sim_expr_mono with "[HI]"); last iApply expr_logrel_EXP_Integer;
        eauto.
      iIntros (??) "H". iDestruct "H" as (????) "Hv".
      iExists _, _; by iFrame. }
    { expr_case expr_logrel_EXP_Float. }
    { expr_case expr_logrel_EXP_Double. }
    { expr_case expr_logrel_EXP_Hex. }
    { expr_case expr_logrel_EXP_Bool. }

    { (* EXP_Null *)
      iApply sim_null_bij. iIntros "#Hn".
      setoid_rewrite interp_ret; iApply sim_expr_base; iExists _ , _;
        iFrame; iSplitL ""; [  | iSplitL "" ]; try (iPureIntro; reflexivity).
      iApply uval_rel_lift; eauto.
      by rewrite unfold_dval_rel. }

    (* TODO Repair *)
    { (* EXP_Zero_initializer *) admit. }
      (* iApply sim_null_bij. iIntros "#Hn". *)
      (* exp_logrel_pre dt. rewrite /exp_conv /denote_exp /lift_err; cbn. *)
      (* destruct (dv_zero_initializer d) eqn: Hzi. *)
      (* - iApply exp_conv_raise. *)
      (* - setoid_rewrite interp_ret; iApply sim_expr_base; iExists _, _; iFrame; *)
      (*   iSplitL ""; [ | iSplitL ""]; try (iPureIntro; reflexivity). *)
      (*   iApply dval_rel_lift. *)
      (*   iApply (@zero_initializer_uval_refl _ _ _ _ Hzi with "Hn"). } *)

    (* EXP_CString *)
    { admit. }

    (* { iApply expr_logrel_EXP_Cstring ; eauto; *)
    (*   iModIntro. iIntros; iApply "IH"; eauto. } *)

    { (* EXP_Undef *)
      destruct τ; cbn; [ | iApply exp_conv_raise ].
      iApply sim_null_bij. iIntros "#Hnull".
      setoid_rewrite interp_ret; iApply sim_expr_base; iExists _ , _;
        iFrame; iSplitL ""; [  | iSplitL "" ]; try (iPureIntro; reflexivity).
      by iApply uval_rel_undef. }

    { iApply expr_logrel_EXP_Struct; eauto;
      iModIntro; iIntros; iApply "IH"; done. }
    { iApply expr_logrel_EXP_Array; eauto;
      iModIntro; iIntros; iApply "IH"; done. }
    { iApply expr_logrel_OP_IBinop; eauto.
      - iModIntro; iIntros; iApply "IH"; done.
      - iIntros; iApply "IH1"; done. }
    { iApply expr_logrel_OP_ICmp; eauto.
      - iModIntro; iIntros; iApply "IH"; done.
      - iModIntro; iIntros; iApply "IH1"; done. }
    { iApply expr_logrel_OP_Conversion; eauto;
      iModIntro; iIntros; iApply "IH"; done. }
    { iApply expr_logrel_EXP_GEP; eauto.
      - iModIntro. iIntros. iApply "IH1"; done.
      - iModIntro; iIntros; iApply "IH"; done. }
    all: exp_logrel_pre dt.
    Unshelve. all : eauto.
  Qed.

End fundamental_exp.
