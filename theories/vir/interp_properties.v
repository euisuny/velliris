From iris.prelude Require Import options.

From Coq Require Import String List Program.Equality.
From iris.base_logic.lib Require Export gen_heap ghost_map.
From iris.base_logic Require Import gset_bij.

From ITree Require Import ITree Eq Interp.InterpFacts Interp.RecursionFacts.

From Vellvm Require Import Syntax.LLVMAst Syntax.DynamicTypes
  Semantics.InterpretationStack Handlers Utils.Util Semantics.LLVMEvents.

From Equations Require Import Equations.

From velliris.logic Require Import satisfiable.
From velliris.program_logic Require Import program_logic.
From velliris.utils Require Import tactics.
From velliris.vir Require Import vir.

Set Default Proof Using "Type*".

Local Open Scope nat_scope.

Import StateFacts.
Import ListNotations.
Import SemNotations.
Import LLVMEvents.
Opaque denote_function.

Lemma nat_lt_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k) -> P m)%nat ->
    forall n, P n.
Proof.
  intros H n; enough (H0: (forall p, p <= n -> P p)%nat).
    - apply H0, le_n. 
    - induction n.
      + intros. inversion H0. apply H. intros. inversion H2.
      + intros. apply H. intros. apply IHn.  inversion H0.
        * rewrite H2 in H1. apply Lt.lt_n_Sm_le in H1. assumption.
        * specialize (PeanoNat.Nat.lt_le_trans k p n H1 H3). apply PeanoNat.Nat.lt_le_incl.
Qed.

(* Equality utils *)
Definition eq_rect_ret {E : Type -> Type} {X Y : Type} (H : X = Y) : E X -> E Y.
  by rewrite H.
Defined.

Definition eq_rect' {X Y : Type} (H : X = Y) : X -> Y.
  by rewrite H.
Defined.


(* Some tactics *)
Ltac destruct_match_goal :=
  repeat match goal with
    | |- context[match ?x with | _ => _ end] =>
        destruct x; cbn
  end.


Ltac noncall_solve' :=
  destruct_match_goal;
  try match goal with
    | |- context[raise] =>
      right; left; repeat eexists _ ; by tau_steps
    | |- context[raiseUB] =>
      right; right; left; repeat eexists _ ; by tau_steps
    end;
    try (left; repeat eexists _ ; by tau_steps).

Section n_taus_utils.

  (* Generic definitions *)
  Fixpoint n_taus {E R} (t : itree E R) (n : nat) : itree E R :=
    match n with
    | 0%nat => t
    | S n => Tau (n_taus t n)
    end.

  Lemma conv_n_taus {R} (e : _ R) n:
    ⟅ n_taus e n ⟆ ≅ n_taus ⟅ e ⟆ n.
  Proof.
    revert e; induction n; cbn; first done.
    intros; rewrite -IHn.
    by setoid_rewrite interp_tau.
  Qed.

  Lemma n_taus_S {E X} (e : itree E X) n:
    n_taus (Tau e) n ≅ n_taus e (S n).
  Proof.
    induction n; first done.
    cbn; by rewrite IHn.
  Qed.

  Lemma n_taus_add {E X} (e : itree E X) x1 x2:
    n_taus e (x1 + x2) ≅ n_taus (n_taus e x1) x2.
  Proof.
    revert x2 e.
    induction x1; cbn; first done.
    intros; rewrite IHx1. by rewrite n_taus_S.
  Qed.

  Global Instance n_taus_Proper_eq_itree {R E} n:
    Proper (eq_itree (R1 := R) (E := E) eq ==> eq) (fun x => n_taus x n).
  Proof.
    repeat intro; to_eq in H; by rewrite H.
  Qed.

  Section sim_n_taus.

    Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
    Context {Λ : language} {η : handlers Λ}.
    Context {si : simulirisGS PROP Λ}.

    Lemma sim_indF_n_taus_L {R1 R2} G `{NonExpansive G} Ψ t1 t2 n:
      sim_indF G (R1 := R1) (R2 := R2) Ψ (observe t1) t2 -∗
      sim_indF G (R1 := R1) (R2 := R2) Ψ (observe (n_taus t1 n)) t2.
    Proof.
      iInduction n as [n | H] "IH" forall (Ψ t1 t2);
        cbn; iIntros "H"; try done.
      setoid_rewrite sim_indF_unfold at 4; last done.
      provide_case: STUTTER_L.
      iApply ("IH" with "H").
    Qed.

    Lemma sim_indF_n_taus_R {R1 R2} G `{NonExpansive G} Ψ t1 t2 n:
      sim_indF G (R1 := R1) (R2 := R2) Ψ t1 (observe t2) -∗
      sim_indF G (R1 := R1) (R2 := R2) Ψ t1 (observe (n_taus t2 n)).
    Proof.
    iInduction n as [n | H] "IH" forall (Ψ t1 t2);
        cbn; iIntros "H"; try done.
    setoid_rewrite sim_indF_unfold at 4; last done.
    provide_case: STUTTER_R.
    iApply ("IH" with "H").
    Qed.

    Lemma sim_coindF_n_taus_L_inv {R1 R2} Ψ t1 t2 n:
      <pers> (∀ (e_t0 : L2_expr _ R1) (e_s0 : st_exprO' R2),
        Ψ (TauF e_t0) e_s0 -∗ Ψ (observe e_t0) e_s0) -∗
      sim_coindF (R1 := R1) (R2 := R2) Ψ (observe (n_taus t1 n)) t2 -∗
      sim_coindF (R1 := R1) (R2 := R2) Ψ (observe t1) t2.
    Proof.
      iIntros "#HΨ".
      iInduction n as [n | H] "IH" forall (t1 t2);
        cbn; iIntros "H"; try done.
      iPoseProof (sim_indF_tau_invL with "HΨ H") as "H".
      iApply ("IH" with "H").
    Qed.

    Lemma sim_coindF_n_taus_R_inv {R1 R2} Ψ t1 t2 n:
      <pers> (∀ (e_t0 : st_exprO' R1) (e_s0 : L2_expr _ R2),
        Ψ e_t0 (TauF e_s0) -∗ Ψ e_t0 (observe e_s0)) -∗
      sim_coindF (R1 := R1) (R2 := R2) Ψ t1 (observe (n_taus t2 n)) -∗
      sim_coindF (R1 := R1) (R2 := R2) Ψ t1 (observe t2).
    Proof.
      iIntros "#HΨ".
      iInduction n as [n | H] "IH" forall (t1 t2);
        cbn; iIntros "H"; try done.
      iPoseProof (sim_indF_tau_invR with "HΨ H") as "H".
      iApply ("IH" with "H").
    Qed.

  End sim_n_taus.

End n_taus_utils.

Section interp_mrec_properties.

  (* Commuting properties for [interp_mrec]*)
  Lemma interp_mrec_ret {U} {D E : Type -> Type} (ctx : D ~> itree (D +' E)) (r : U) :
    interp_mrec ctx (Ret r) ≅ Ret r.
  Proof.
    rewrite /interp_mrec.
    rewrite unfold_iter. cbn. rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma interp_mrec_tau D T f a σ :
    ⟦ interp_mrec f (Tau a) ⟧ σ = Tau (⟦ interp_mrec (D := D) (T := T) f a ⟧ σ).
  Proof.
    apply EqAxiom.bisimulation_is_eq.
    rewrite /interp_mrec. cbn.
    rewrite unfold_iter; cbn.
    rewrite bind_ret_l.
    rewrite /interp_L2. by rewrite interp_state_tau.
  Qed.

  Lemma interp_mrec_call T f σ dt uv args attr k:
    ⟦ interp_mrec f (Vis (inl1 (Call dt uv args attr)) k) ⟧ σ =
      Tau (⟦ interp_mrec (T := T) f (x <- f uvalue (Call dt uv args attr);; k x) ⟧ σ).
  Proof.
    apply EqAxiom.bisimulation_is_eq.
    rewrite /interp_mrec. cbn.
    rewrite unfold_iter; cbn.
    rewrite bind_ret_l.
    rewrite /interp_L2. by rewrite interp_state_tau.
  Qed.

  Lemma interp_mrec_external_call {T D} f σ dt uv args attr k:
    ⟦ interp_mrec (T := T) f (Vis (inr1 (inl1 (ExternalCall dt uv args attr))) k) ⟧ σ =
    vis (StateEff vir_calls (σ, ExternalCall dt uv args attr))
        (fun x => Tau (Tau ( ⟦ interp_mrec (D := D) f (k x.2) ⟧ x.1 ))).
  Proof.
    apply EqAxiom.bisimulation_is_eq.
    rewrite /interp_mrec. cbn.
    rewrite unfold_iter; cbn.
    rewrite bind_vis; setoid_rewrite interp_state_vis; cbn.
    rewrite /handle_stateEff. rewrite bind_vis.
    repeat setoid_rewrite bind_ret_l.
    by setoid_rewrite interp_state_tau.
  Qed.

  Notation noncall_events :=
      (intrinsics_events vir_lang +'
        global_events vir_lang +'
        local_events vir_lang +'
        memory_events vir_lang +'
        E vir_lang +'
        UB_events vir_lang +' F vir_lang +' exc_events vir_lang).

  Definition handle_noncall_L0_L2 :
    intrinsics_events vir_lang +'
    global_events vir_lang +' local_events vir_lang +' memory_events vir_lang +'
    E vir_lang +' UB_events vir_lang +' F vir_lang +' exc_events vir_lang ~> _ :=
      (case_ (C := IFun) (bif := sum1) (intrinsics_handler (Λ := vir_lang))
            (case_ (bif := sum1) (global_handler (Λ := vir_lang))
                (case_ (bif := sum1) (local_handler (Λ := vir_lang))
                    (case_ (bif := sum1) (memory_handler (Λ := vir_lang))
                        (case_ (bif := sum1) (E_handler (Λ := vir_lang))
                        (case_ (bif := sum1) (pure_state (state vir_lang)) (pure_state (state vir_lang)))))))).

  Ltac noncall_solve :=
    destruct_match_goal;
    try match goal with
      | |- context[raise] =>
        right; left; eexists _;
        rewrite /raise; rewrite !bind_bind;
        eapply eq_itree_clo_bind; first reflexivity;
        intros; done
      | |- context[raiseUB] =>
        right; right; left; eexists _;
        rewrite /raise; rewrite !bind_bind;
        eapply eq_itree_clo_bind; first reflexivity;
        intros; done
      end;
      try (left; repeat eexists _ ; by tau_steps).

  Lemma handle_noncall_L0_L2_case1 x x0 σ:
    (∃ t, handle_noncall_L0_L2 x x0 σ ≅ Ret t) \/
    (∃ str, handle_noncall_L0_L2 x x0 σ ≅ raise str) \/
    (∃ str, handle_noncall_L0_L2 x x0 σ ≅ raiseUB str) \/
    (∃ e, handle_noncall_L0_L2 x x0 σ ≅
        Vis (subevent _ (e : F _ _)) (fun x => Ret (σ, x)) /\
        x0 = (subevent _ (e : F _ _))).
  Proof.
    destruct σ as ((?&(?&?))&(?&?)&?).
    destruct x0 as [ | [ | [ | [ | [ | [ | [ | ] ] ] ] ] ] ]; cbn.
    - noncall_solve.
    - destruct g2; cbn; noncall_solve.
    - destruct l1; cbn; [ | destruct l1 ]; try destruct l1; cbn.
      all : noncall_solve.

    - cbn. destruct m; cbn;
        rewrite /lift_pure_err /lift_err /allocate.

      1-5,7 : noncall_solve.
      { destruct p; noncall_solve. }
      { noncall_solve. }
      { noncall_solve. }

    - rewrite /concretize_picks /lift_undef_or_err.
      noncall_solve.

    - rewrite /pure_state. destruct u.
      right; right; left; eexists _;
      rewrite /raiseUB; rewrite ?bind_bind;
      eapply eq_itree_clo_bind; first reflexivity;
      intros; done.

    - rewrite /pure_state.
      repeat right; repeat eexists _; split; eauto; tau_steps; cbn.
      apply eqit_Vis; intros. by setoid_rewrite bind_ret_l.

    - rewrite /pure_state. destruct e. destruct u.
      right; left; eexists _;
      rewrite /raise; rewrite ?bind_bind;
      eapply eq_itree_clo_bind; first reflexivity;
      intros; done.
      Unshelve. all : exact "H".
  Qed.

  (* Inversion lemmas for [interp_L2] used for proving simulation *)
  Lemma interp_L2_ret_inv {R} (a : _ R) σ t:
    ⟦ a ⟧ σ ≅ Ret t ->
    a ≅ Ret t.2.
  Proof.
    destruct t.
    rewrite /interp_L2 /L0'expr_conv.
    intros H; cbn.
    rewrite (itree_eta a) in H.
    destruct (observe a) eqn: Ha; cbn in H.
    { rewrite interp_state_ret in H.
      apply eqit_inv in H; inversion H; cbn in H; subst.
      rewrite (itree_eta a). rewrite Ha; by cbn. }

    { rewrite interp_state_tau in H.
      by apply eqit_inv in H. }

    { destruct e.
      - destruct c; cbn in *.
        simp L0'_conv in H.
        rewrite interp_state_vis in H.
        cbn in H. rewrite /handle_stateEff in H.
        rewrite bind_vis in H. by apply eqit_inv in H.
      - destruct s0.
        + rewrite interp_state_vis in H.
          rewrite /handle_L0_L2 in H. cbn in H.
          rewrite /handle_stateEff in H.
          rewrite bind_tau in H.
          by apply eqit_inv in H.
        + rewrite interp_state_vis in H.
          rewrite /handle_L0_L2 in H. cbn in H.
          rewrite /handle_stateEff in H.
          rewrite bind_tau in H.
          by apply eqit_inv in H. }
  Qed.

  (* Inversion lemmas for [interp_L2] used for proving simulation *)
  Lemma interp_L2_tau_inv {R} (a : _ R) σ t:
    ⟦ a ⟧ σ ≅ Tau t ->
    (∃ x, a ≅ Tau x /\ t ≅ ⟦ x ⟧ σ) \/
    (∃ X (e : _ X) k,
        observe a = VisF (inr1 e) k
        /\ t ≅ sx <- handle_noncall_L0_L2 X e σ;; Tau (⟦ k sx.2 ⟧ sx.1)).
  Proof.
    rewrite /interp_L2 /L0'expr_conv.
    intros H.
    rewrite (itree_eta a) in H.
    destruct (observe a) eqn: Ha; cbn in H.

    { rewrite interp_state_ret in H.
      by apply eqit_inv in H. }

    { rewrite interp_state_tau in H.
      apply eqit_inv in H; cbn in H. left.
      eexists _; rewrite (itree_eta a). rewrite Ha. split; done. }

    { destruct e.
      - destruct c; cbn in *.
        simp L0'_conv in H.
        rewrite interp_state_vis in H.
        cbn in H. rewrite /handle_stateEff in H.
        rewrite bind_vis in H. by apply eqit_inv in H.
      - rewrite interp_state_vis in H.
        rewrite {1} /handle_L0_L2 in H.
        rewrite bind_tau in H. cbn in H.
        apply eqit_inv_Tau in H.
        right. repeat eexists _; split; eauto.
        rewrite -H. cbn. reflexivity. }
  Qed.

  Lemma handle_noncall_L0_L2_case x x0 σ:
    (∃ t, handle_noncall_L0_L2 x x0 σ ≅ Ret t) \/
    (∃ X k (e : _ X), handle_noncall_L0_L2 x x0 σ ≅ Vis (subevent _ (e : FailureE _)) k) \/
    (∃ X k (e : _ X), handle_noncall_L0_L2 x x0 σ ≅ Vis (subevent _ (e : UBE _)) k) \/
    (∃ e, handle_noncall_L0_L2 x x0 σ ≅
        Vis (subevent _ (e : F _ _)) (fun x => Ret (σ, x)) /\
        x0 = (subevent _ (e : F _ _))).
  Proof.
    destruct σ as ((?&(?&?))&(?&?)&?).
    destruct x0 as [ | [ | [ | [ | [ | [ | [ | ] ] ] ] ] ] ]; cbn.
    - noncall_solve'.
    - destruct g2; cbn; noncall_solve'.
    - destruct l1; cbn; [ | destruct l1 ]; try destruct l1; cbn.
      all : noncall_solve'.
      all: destruct l1; cbn; noncall_solve'.

     - cbn. destruct m; cbn;
         rewrite /lift_pure_err /lift_err /allocate.

       1-5,7 : noncall_solve'.
       { destruct p; noncall_solve'. }
       { noncall_solve'. }
       { noncall_solve'. }

     - rewrite /concretize_picks /lift_undef_or_err.
       noncall_solve'.

     - rewrite /pure_state.
        right; right; left ; repeat eexists _; by tau_steps.

     - rewrite /pure_state.
        repeat right; repeat eexists _; split; eauto; tau_steps; cbn.
        apply eqit_Vis; intros. by setoid_rewrite bind_ret_l.

     - rewrite /pure_state.
        right; left ; repeat eexists _.
        rewrite bind_vis. apply eqit_Vis.
        intros; subst. rewrite bind_ret_l. apply eqit_Ret. reflexivity.
  Qed.

  Typeclasses eauto :=.
  Lemma interp_mrec_vis D T X (e : _ X) f σ k:
    ⟦ interp_mrec f (Vis (inr1 (inr1 e)) k) ⟧ σ =
    Tau (r <- handle_noncall_L0_L2 X e σ ;;
      Tau (Tau (⟦ interp_mrec (D := D) (T := T) f (k r.2) ⟧ (r.1)))).
  Proof.
    apply EqAxiom.bisimulation_is_eq.
    rewrite /interp_mrec. cbn.
    rewrite unfold_iter; cbn.
    rewrite /interp_L2.
    rewrite interp_state_bind interp_state_vis bind_bind.
    unfold handle_L0_L2.
    remember ((case_ intrinsics_handler
          (case_ global_handler
             (case_ local_handler
                (case_ memory_handler
                   (case_ E_handler
                      (case_ (pure_state (state vir_lang))
                         (pure_state (state vir_lang))))))))).
    cbn.
    rewrite /add_tau bind_tau.
    setoid_rewrite interp_state_ret.
    setoid_rewrite bind_tau.
    setoid_rewrite bind_ret_l.
    setoid_rewrite interp_state_tau.
    subst. cbn. reflexivity.
  Qed.

End interp_mrec_properties.


Section interp_L2_conv_properties.

  Lemma interp_L2_conv_bind {R1 R2} (e : _ R1) (k : _ -> _ R2) σ:
    ⟦ ⟅ x <- e ;; k x ⟆ ⟧ σ = x <- ⟦ ⟅ e ⟆ ⟧ σ ;; ⟦ ⟅ k x.2 ⟆ ⟧ x.1.
  Proof.
    to_eq. setoid_rewrite interp_bind.
    setoid_rewrite interp_state_bind; done.
  Qed.

  Lemma interp_L2_conv_ret {R} (x:R) σ:
    ⟦ ⟅ Ret x ⟆ ⟧ σ = Ret (σ, x).
  Proof.
    to_eq. setoid_rewrite interp_ret.
    setoid_rewrite interp_state_ret; done.
  Qed.

  (* Inversion lemmas for [interp_L2_conv] used for proving simulation *)
  Lemma interp_L2_conv_ret_inv {R} (a : _ R) σ t:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ Ret t ->
    a ≅ Ret t.2.
  Proof.
    destruct t.
    rewrite /interp_L2 /L0'expr_conv.
    intros H; cbn.
    rewrite (itree_eta a) in H.
    destruct (observe a) eqn: Ha; cbn in H.
    { rewrite interp_ret interp_state_ret in H.
      apply eqit_inv in H; inversion H; cbn in H; subst.
      rewrite (itree_eta a). rewrite Ha; by cbn. }

    { rewrite interp_tau interp_state_tau in H.
      by apply eqit_inv in H. }

    { rewrite interp_vis in H.

      destruct e.
      - destruct c; cbn in *.
        simp L0'_conv in H.
        rewrite interp_state_bind in H.
        rewrite interp_state_vis bind_bind in H.
        cbn in H. rewrite /handle_stateEff in H.
        rewrite bind_vis in H. by apply eqit_inv in H.
      - destruct s0.
        + destruct e. simp call_conv in H.
          rewrite bind_vis in H.
          rewrite interp_state_vis in H.
          rewrite /handle_L0_L2 in H. cbn in H.
          rewrite /handle_stateEff in H.
          rewrite bind_vis in H.
          by apply eqit_inv in H.
        + simp call_conv in H.
          rewrite bind_vis in H.
          rewrite interp_state_vis in H.
          rewrite {1} /handle_L0_L2 in H. cbn in H.
          rewrite /handle_stateEff in H; cbn in H.
          rewrite bind_tau in H; by apply eqit_inv in H. }
  Qed.

  Lemma interp_L2_conv_tau_inv {R} (a : _ R) σ t:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ Tau t ->
    (∃ a', observe a = TauF a' /\ t ≅ ⟦ ⟅ a' ⟆ ⟧ σ)
    \/ (∃ X (e : _ X) k,
        observe a = VisF (inr1 (inr1 e)) k
        /\ t ≅ sx <- handle_noncall_L0_L2 X e σ;; Tau (Tau (⟦ ⟅ k sx.2 ⟆ ⟧ sx.1))).
  Proof.
    rewrite /interp_L2 /L0'expr_conv.
    intros H.
    rewrite (itree_eta a) in H.
    destruct (observe a) eqn: Ha; cbn in H.

    { rewrite interp_ret interp_state_ret in H.
      by apply eqit_inv in H. }

    { rewrite interp_tau interp_state_tau in H.
      apply eqit_inv in H; cbn in H.
      left; eauto. eexists _; split; symmetry; eauto. }

    { rewrite interp_vis in H.
      destruct e.
      - destruct c; cbn in *.
        simp L0'_conv in H.
        rewrite interp_state_bind in H.
        rewrite interp_state_vis bind_bind in H.
        cbn in H. rewrite /handle_stateEff in H.
        rewrite bind_vis in H. by apply eqit_inv in H.
      - destruct s.
        + destruct e. simp call_conv in H. rewrite bind_vis in H.
          rewrite interp_state_vis in H.
          rewrite /handle_L0_L2 in H.
          cbn in H. rewrite /case_ /add_tau in H.
          rewrite /handle_stateEff in H. rewrite bind_vis in H.
          by apply eqit_inv in H.
        + simp call_conv in H. rewrite bind_vis in H.
          rewrite interp_state_vis in H.
          rewrite bind_tau in H.
          apply eqit_inv_Tau in H.
          Typeclasses eauto := 5.
          setoid_rewrite interp_state_bind in H.
          setoid_rewrite interp_state_ret in H;
          setoid_rewrite bind_ret_l in H;
          setoid_rewrite interp_state_tau in H;
          cbn in H;

          right;
          by repeat eexists _. }
  Qed.

  Lemma interp_L2_conv_tau {R} (a : _ R) σ :
    ⟦ ⟅ Tau a ⟆ ⟧ σ = Tau (⟦ ⟅ a ⟆ ⟧ σ).
  Proof.
    apply EqAxiom.bisimulation_is_eq.
    setoid_rewrite interp_tau.
    by setoid_rewrite interp_state_tau.
  Qed.

  Definition noncall_events :=
    (IntrinsicE +'
      LLVMGEnvE +'
      (LLVMEnvE +' LLVMStackE) +'
       MemoryE +' PickE +' UBE +' DebugE +' FailureE).

  Definition stateful_events :=
    (IntrinsicE +'
      LLVMGEnvE +'
      (LLVMEnvE +' LLVMStackE) +'
       MemoryE +' PickE).

  Typeclasses eauto :=.
  Lemma interp_L2_conv_vis_inv {R X}
    (a : itree L0' R) σ (e : language.L2 vir_lang X) k:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ Vis e k ->
    (∃ dt uv args attr (k : _ → itree L0' R),
      a ≅ vis (Call dt uv args attr) k) \/
    (∃ X (e : (ExternalCallE +' stateful_events) X)
      (k : X → itree L0' R),
      a ≅ vis e k).
  Proof.
    rewrite /interp_L2 /L0'expr_conv.
    intros H. rewrite (itree_eta a) in H.
    setoid_rewrite (itree_eta a).
    remember (observe a). clear Heqi a.
    induction i; cbn.
    - rewrite interp_ret interp_state_ret in H.
      by apply eqit_inv in H.
    - rewrite interp_tau interp_state_tau in H.
      by apply eqit_inv in H.
    - rewrite interp_vis in H. rewrite interp_state_bind in H.
      destruct e0 eqn: He0.
      + destruct c. simp L0'_conv in H.
        rewrite interp_state_vis bind_bind in H.
        cbn in H. rewrite /handle_stateEff in H.
        rewrite bind_vis in H.
        setoid_rewrite bind_ret_l in H.
        apply eqit_inv in H; cbn in H.
        destruct H as (?&?&?). red in H, H0.
        dependent destruction x.

        left; exists t, f, args, attr, k0. split; auto.
        apply eqit_Vis.
        reflexivity.

      + destruct s.
        * destruct e1. simp call_conv in H.
          rewrite interp_state_vis in H.
          rewrite /handle_L0_L2 in H.
          cbn in H. rewrite /case_ /add_tau in H.
          rewrite /handle_stateEff in H. rewrite bind_vis in H.
          apply eqit_inv in H. right.
          (* VisF (inr1 (inl1 e0)) k0 = VisF e1 k1 *)
          eexists _, (inl1 (ExternalCall t f args attr)), k0. done.

        * simp call_conv in H.
          rewrite interp_state_vis in H.
          rewrite {1} /handle_L0_L2 in H.
          rewrite /subevent in H. unfold_cat in H.
          rewrite bind_bind bind_tau in H.
          by apply eqit_inv in H.
  Qed.

  (* Variants of inversion lemmas with [n_tau] information gathered *)
  Lemma interp_L2_conv_tau_n_inv {R} (a : _ R) σ t (n : nat):
    ⟦ ⟅ a ⟆ ⟧ σ ≅ n_taus t (S n) ->
    (∃ a', a ≅ n_taus (Tau a') n /\ t ≅ ⟦ ⟅ a' ⟆ ⟧ σ)
    \/
    (∃ X (e : _ X) k (n' n'': nat),
        n' <= n /\ n'' <= n
        /\ a ≅ n_taus (Vis (inr1 (inr1 e)) k) n'
        /\ n_taus t n'' ≅
            sx <- handle_noncall_L0_L2 X e σ;; Tau (Tau (⟦ ⟅ k sx.2 ⟆ ⟧ sx.1)))%nat.
  Proof.
    revert a σ t.
    induction n; cbn; intros.
    - apply interp_L2_conv_tau_inv in H.
      destruct H as
        [ (?&?&?) | (?&?&?&?&?) ]; subst.
      + left; eexists _; split; eauto.
        rewrite (itree_eta a); by rewrite H.
      + right; eexists _, _, _, 0%nat, 0%nat; split; eauto; try lia.
        split; eauto.
        split; eauto.
        rewrite (itree_eta a); by rewrite H.

   - pose proof (H' := H).
     apply interp_L2_conv_tau_inv in H.

      destruct H as
        [ (?&?&?) | (?&?&?&?&?) ]; subst.

      + symmetry in H0.
        specialize (IHn _ _ _ H0).
        destruct IHn as
          [ (?&?&?) | (?&?&?&?&?&?&?&?&?) ]; subst.
        * left. eexists x0.
          rewrite (itree_eta a).
          rewrite H; cbn; split; eauto.
          by rewrite {1}H1.
        * right. eexists _, x1, _, (S x3), x4. cbn in *.
          split; [ lia | ].
          do 2 (split; eauto).
          rewrite (itree_eta a); cbn.
          rewrite H. rewrite H3. by apply eqit_Tau.

      + right.
        eexists _, _, _, 0%nat, (S n)%nat.
        split; first lia; split; cbn; auto. split.
        * rewrite (itree_eta a). rewrite H; done.
        * done.
  Qed.

  Lemma interp_L2_conv_tau_n_inv' {R} (a : _ R) σ t n:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ n_taus t (S n) ->
    (∃ a', a ≅ n_taus (Tau a') n /\ t ≅ ⟦ ⟅ a' ⟆ ⟧ σ)
    \/
    (∃ X (e : _ X) k n n',
        a ≅ n_taus (Vis (inr1 (inr1 e)) k) n
        /\ n_taus t n' ≅
            sx <- handle_noncall_L0_L2 X e σ;; Tau (Tau (⟦ ⟅ k sx.2 ⟆ ⟧ sx.1))).
  Proof.
    revert a σ t.
    induction n; cbn; intros.
    - apply interp_L2_conv_tau_inv in H.
      destruct H as
        [ (?&?&?) | (?&?&?&?&?) ]; subst.
      + left; eexists _; split; eauto.
        rewrite (itree_eta a); by rewrite H.
      + right; eexists _, _, _, 0%nat, 0%nat; split; eauto.
        rewrite (itree_eta a); by rewrite H.

   - pose proof (H' := H).
     apply interp_L2_conv_tau_inv in H.

      destruct H as
        [ (?&?&?) | (?&?&?&?&?) ]; subst.

      + symmetry in H0.
        specialize (IHn _ _ _ H0).
        destruct IHn as
          [ (?&?&?) | (?&?&?&?&?&?&?) ]; subst.
        * left. eexists x0.
          rewrite (itree_eta a).
          rewrite H; cbn; split; eauto.
          by rewrite {1}H1.
        * right. eexists _, x1, _, (S x3), x4.
          split; eauto.
          rewrite (itree_eta a).
          rewrite H H1. cbn. reflexivity.

      + right. eexists _, _, _, 0%nat, (S n).
        split; last done.
        rewrite (itree_eta a); cbn.
        by rewrite H.
  Qed.

  Lemma interp_L2_conv_failure_inv {R X} (a : itree L0' R) σ (e : _ X) k:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ vis (e : FailureE _) k -> False.
  Proof.
    intros H; pose proof (H' := H).
    apply interp_L2_conv_vis_inv in H.
    destruct H as [ (?&?&?&?&?&?) | (?&?&?&?)].
    - (* absurd: goal is call *)
      exfalso; rewrite /interp_L2 /L0'expr_conv in H'.
      rewrite (itree_eta a) in H'.
      rewrite H in H'. cbn in H'.
      rewrite interp_vis in H'. rewrite interp_state_bind in H'.
      rewrite
        /subevent /resum /ReSum_inl /cat /Cat_IFun /inl_ /Inl_sum1 in H'.
      rewrite
        /resum /ReSum_id /id_ /Id_IFun in H'.
      cbn in H'.
      simp L0'_conv in H'.
      rewrite interp_state_vis bind_bind in H'.
      cbn in H'. rewrite /handle_stateEff in H'.
      rewrite bind_vis in H'. apply eqit_inv in H'. cbn in H'.
      destruct H' as (?&?&?). dependent destruction x4. inversion H0.

    - rewrite /interp_L2 /L0'expr_conv in H'.
      rewrite H in H'. rewrite interp_vis in H'.
      rewrite /subevent /resum /ReSum_sum /case_ /Case_sum1
        /case_sum1 in H'.
      destruct x0.
      + (* absurd : goal is a call *)
        rewrite /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 in H'.
        simp L0'_conv in H'. rewrite bind_vis in H'.
        rewrite interp_state_vis in H'. unfold_cat in H'. destruct e0.
        simp call_conv in H'. cbn in H'. rewrite /handle_stateEff in H'.
        rewrite bind_vis in H'.
        apply eqit_inv in H'; destruct H' as (?&?&?).
        dependent destruction x. inversion H0.
      + rewrite /resum in H'.
        simp L0'_conv in H'.
        destruct s as [ | [ | [ | [ |  ] ] ] ];
          unfold_cat in H'; simp L0'_conv in H'.
        all : try solve [ rewrite bind_vis in H';
          apply eqit_inv in H'; by cbn in H' ].
        destruct s.
        * simp L0'_conv in H'. rewrite interp_state_bind in H'.
          rewrite interp_state_vis bind_bind in H'.
          rewrite /handle_L0_L2 in H'; cbn in H'.
          by apply eqit_inv in H'.
        * simp L0'_conv in H'. rewrite interp_state_bind in H'.
          rewrite interp_state_vis bind_bind in H'.
          rewrite /handle_L0_L2 in H'; cbn in H'.
          by apply eqit_inv in H'.
  Qed.

  Lemma interp_mrec_n_taus {D E T} f e n:
    interp_mrec f (n_taus e n) ≅ n_taus (interp_mrec (D := D) (E := E) (T := T) f e) n.
  Proof.
    revert f e; induction n; cbn; [ done | ].
    intros. rewrite -IHn. rewrite /interp_mrec.
    rewrite unfold_iter. cbn. rewrite bind_ret_l.
    by apply eqit_Tau.
  Qed.

  Lemma interp_L2_conv_n_taus {R} (e : _ R) n σ:
    ⟦ n_taus e n ⟧ σ ≅ n_taus (⟦ e ⟧ σ) n.
  Proof.
    revert e σ; induction n; cbn; first done.
    intros; rewrite -IHn. rewrite /interp_L2.
    by rewrite interp_state_tau.
  Qed.

  Lemma interp_L2_conv_failure_tau_n_inv {R X} (a : itree L0' R) σ (e : _ X) k n g:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ n_taus (vis (e : FailureE _) k) n ->
    (∃ m k, (⟦ interp_mrec g a ⟧ σ) ≅ n_taus (vis (e : FailureE _ ) k) m).
  Proof.
    revert a σ e k g.
    induction n using nat_lt_ind; cbn.
    destruct n.
    { intros; by apply interp_L2_conv_failure_inv in H0. }

    intros.
    pose proof (H' := H).
    apply interp_L2_conv_tau_n_inv in H0.
    destruct H0 as
      [ (?&?&?) | (?&?&?&?&?&?&?&?&?) ]; subst.
    - symmetry in H1.
      by apply interp_L2_conv_failure_inv in H1.

    - Typeclasses eauto := 4.
       setoid_rewrite H2. setoid_rewrite interp_mrec_n_taus.
      setoid_rewrite interp_L2_conv_n_taus.
      rewrite interp_mrec_vis.
      setoid_rewrite n_taus_S.
      Typeclasses eauto :=.

      change (fun sx => Tau (Tau (⟦ ⟅ x1 sx.2 ⟆ ⟧ sx.1))) with
          (fun sx => n_taus (⟦ ⟅ x1 sx.2 ⟆ ⟧ sx.1) 2) in H0.

      remember 1. clear Heqn0.
      revert σ x2 x3 n n0 H0 H H0 H1 H2 H3 H'.
      induction x3; cbn in *; intros.
      { pose proof (handle_noncall_L0_L2_case x x0 σ).
        destruct H5 as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].
        - rewrite H5 in H4. rewrite bind_ret_l in H4.
          destruct n0; cbn in *. 2 : by apply eqit_inv in H4.
          to_eq in H5. rewrite H5.
          by apply eqit_inv in H4.
        - rewrite H5 in H4. rewrite bind_vis in H4.
          apply eqit_inv in H4. destruct H4 as (?&?&?).
          dependent destruction x6. inversion H4; subst.
          to_eq in H5; rewrite H5.
          eexists (S x2), (fun u => r <- x4 u;; Tau (Tau (⟦ interp_mrec g (x1 r.2) ⟧ r.1))).
          cbn. apply eqit_Tau.
          f_equiv. to_eq. rewrite bind_vis. done.
        - rewrite H5 in H4. rewrite bind_vis in H4.
          apply eqit_inv in H4. destruct H4 as (?&?&?).
          dependent destruction x6. inversion H4; subst.
        - rewrite H5 in H4. rewrite bind_vis in H4.
          apply eqit_inv in H4. destruct H4 as (?&?&?).
          dependent destruction x4. inversion H4; subst. }
      { cbn in H4.
        pose proof (handle_noncall_L0_L2_case x x0 σ).
        destruct H5 as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].
        - rewrite H5 in H4. rewrite bind_ret_l in H4.
          apply eqit_inv in H4; cbn in H4.
          to_eq in H5. rewrite H5 in IHx3.
          destruct x3; cycle 1.
          { cbn in H4. apply eqit_inv_Tau in H4.
            symmetry in H4.
            assert (x3 < S n)%nat by lia.
            specialize (H' _ H6 _ _ _ _ g H4).
            destruct H' as (?&?&?).
            rewrite H5. eexists (S (S (S (x5 + x2)))), _.
            pose proof (@bind_ret_l _ (state vir_lang * x) _ x4
                          (fun (r : (state vir_lang * x)%type) =>
                                        Tau (Tau (⟦ interp_mrec g (x1 r.2) ⟧ r.1)))).
            to_eq in H8.
            cbn. apply eqit_Tau.
            rewrite H8. rewrite !n_taus_S. cbn.
            to_eq in H7. rewrite H7. rewrite n_taus_add. reflexivity. }
          { cbn in *. by apply eqit_inv in H4. }

        - rewrite H5 in H4. rewrite bind_vis in H4.
          by apply eqit_inv in H4.
        - rewrite H5 in H4. rewrite bind_vis in H4.
          by apply eqit_inv in H4.
        - rewrite H5 in H4. rewrite bind_vis in H4.
          by apply eqit_inv in H4. }
  Qed.

  Lemma interp_L2_conv_UB_inv {R X} (a : itree L0' R) σ (e : _ X) k:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ vis (e : UBE _) k -> False.
  Proof.
    intros H; pose proof (H' := H).
    apply interp_L2_conv_vis_inv in H.
    destruct H as [ (?&?&?&?&?&?) | (?&?&?&?)].
    - (* absurd: goal is call *)
      exfalso; rewrite /interp_L2 /L0'expr_conv in H'.
      rewrite (itree_eta a) in H'.
      rewrite H in H'. cbn in H'.
      rewrite interp_vis in H'. rewrite interp_state_bind in H'.
      rewrite
        /subevent /resum /ReSum_inl /cat /Cat_IFun /inl_ /Inl_sum1 in H'.
      rewrite
        /resum /ReSum_id /id_ /Id_IFun in H'.
      cbn in H'.
      simp L0'_conv in H'.
      rewrite interp_state_vis bind_bind in H'.
      cbn in H'. rewrite /handle_stateEff in H'.
      rewrite bind_vis in H'. apply eqit_inv in H'. cbn in H'.
      destruct H' as (?&?&?). dependent destruction x4. inversion H0.

    - rewrite /interp_L2 /L0'expr_conv in H'.
      rewrite H in H'. rewrite interp_vis in H'.
      rewrite /subevent /resum /ReSum_sum /case_ /Case_sum1
        /case_sum1 in H'.
      destruct x0.
      + (* absurd : goal is a call *)
        rewrite /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1 in H'.
        simp L0'_conv in H'. rewrite bind_vis in H'.
        rewrite interp_state_vis in H'.
        unfold_cat in H'. destruct e0. simp call_conv in H'.
        cbn in H'. rewrite bind_vis in H'.
        apply eqit_inv in H'; destruct H' as (?&?&?).
        dependent destruction x. inversion H0.
      + rewrite /resum in H'.
        simp L0'_conv in H'.
        destruct s as [ | [ | [ | [ |  ] ] ] ];
          unfold_cat in H'; simp L0'_conv in H'.
        all : try solve [ rewrite bind_vis in H';
          apply eqit_inv in H'; by cbn in H' ].
        destruct s; simp L0'_conv in H'.
        * rewrite interp_state_bind in H'.
          rewrite interp_state_vis bind_bind in H'.
          rewrite /handle_L0_L2 in H'.
          setoid_rewrite bind_tau in H'.
          by apply eqit_inv in H'.
        * rewrite interp_state_bind in H'.
          rewrite interp_state_vis bind_bind in H'.
          rewrite /handle_L0_L2 in H'.
          setoid_rewrite bind_tau in H'.
          by apply eqit_inv in H'.
  Qed.

  Lemma interp_L2_conv_UB_tau_n_inv {R X} (a : itree L0' R) σ (e : UBE X) k k' n g:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ n_taus (vis e k) n ->
    (∃ m, (⟦ interp_mrec g a ⟧ σ) ≅ n_taus (vis (e : UBE _ ) k') m).
  Proof.
    intros. setoid_rewrite (itree_eta a).
    revert R X a σ e k k' g H.
    induction n using nat_lt_ind; cbn.
    destruct n.
    { intros. setoid_rewrite <-itree_eta.
      by apply interp_L2_conv_UB_inv in H0. }

    intros.

    pose proof (H' := H).
    apply interp_L2_conv_tau_n_inv in H0.

    destruct H0 as
      [ (?&?&?) | ? ]; subst.
    - symmetry in H1.
      by apply interp_L2_conv_UB_inv in H1.
    - destruct H0 as (Y & e' & k'' & n1 & n2 & Hbound1 & Hbound2 & Ha & Htau).
      setoid_rewrite <-itree_eta. setoid_rewrite Ha; clear a Ha.
      setoid_rewrite interp_mrec_n_taus.
      setoid_rewrite interp_L2_conv_n_taus.
      rewrite interp_mrec_vis.
      setoid_rewrite n_taus_S.

      change (fun sx => Tau (Tau (⟦ ⟅ k'' sx.2 ⟆ ⟧ sx.1))) with
          (fun sx => n_taus (⟦ ⟅ k'' sx.2 ⟆ ⟧ sx.1) 2) in Htau.

      revert σ n n1 Hbound1 Hbound2 Htau H H'.
      induction n2; cbn in *; intros.
      { pose proof (handle_noncall_L0_L2_case Y e' σ) as Hcall.
        destruct Hcall as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].
        - rewrite H0 in Htau.
          rewrite bind_ret_l in Htau.
          by apply eqit_inv in Htau.
        - rewrite H0 in Htau.
          rewrite bind_vis in Htau.
          apply eqit_inv in Htau. cbn in Htau.
          destruct Htau as (?&?&?).
          dependent destruction x2. inversion H1; subst.
        - rewrite H0 in Htau.
          rewrite bind_vis in Htau.
          apply eqit_inv in Htau. cbn in Htau.
          destruct Htau as (?&?&?).
          dependent destruction x2. inversion H1; subst.
          to_eq in H0; rewrite H0.
          eexists (S n1).
          cbn. apply eqit_Tau.
          f_equiv. to_eq. rewrite bind_vis. destruct x1.
          apply eqit_Vis. done.
        - rewrite H0 in Htau.
          rewrite bind_vis in Htau.
          apply eqit_inv in Htau. cbn in Htau.
          destruct Htau as (?&?&?).
          dependent destruction x0. inversion H2; subst. }

      { cbn in Htau.

        pose proof (handle_noncall_L0_L2_case Y e' σ).
        destruct H0 as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].

        - rewrite H0 in Htau; to_eq in H0; rewrite H0; clear H0.
          rewrite bind_ret_l in Htau.
          apply eqit_inv in Htau; cbn in Htau; clear IHn2.

          assert (n2 < S n) by lia. symmetry in Htau.
          rewrite -interp_L2_conv_tau in Htau.
          epose proof (H'' := H' _ H0 _ _ _ _ _ _ _ g Htau); clear H'.
          destruct H'' as (?&?).
          setoid_rewrite <-itree_eta in H1.
          rewrite interp_mrec_tau in H1.
          destruct x0; apply eqit_inv in H1; try done.
          cbn in H1. to_eq in H1.
          exists (x0 + (S n1 + 2)). rewrite n_taus_add.
          cbn. rewrite n_taus_add.
          rewrite -H1. cbn. apply eqit_Tau.
          pose proof
            (bind_ret_l x
               (fun r => Tau (Tau (⟦ interp_mrec g (k'' r.2) ⟧ r.1)))).
          to_eq in H2; rewrite H2; clear H2.
          by rewrite !n_taus_S.

        - rewrite H0 in Htau. rewrite bind_vis in Htau.
          by apply eqit_inv in Htau.
        - rewrite H0 in Htau. rewrite bind_vis in Htau.
          by apply eqit_inv in Htau.
        - rewrite H0 in Htau. rewrite bind_vis in Htau.
          by apply eqit_inv in Htau. }
      Unshelve. eauto.
  Qed.

  Lemma interp_L2_conv_vis_ECall_noncall {R} x σ_t:
    ∀ (x0 : (ExternalCallE +' stateful_events) x) (x1 : x → itree L0' R) (X : Type)
      (et : language.L2 vir_lang X) (kt : X → L2_expr vir_lang R),
      ⟦ ⟅ vis x0 x1 : itree L0' R ⟆ ⟧ σ_t ≅ (Vis et kt : L2_expr vir_lang R)
      → ∃ (τ : dtyp) (u : dvalue) (l : list uvalue) (f : list fn_attr)
          (H : (uvalue : Type) = x) (H' : (vir_state * x)%type = X),
          x0 = (eq_rect_ret H (inl1 (ExternalCall τ u l f)) : (ExternalCallE +' stateful_events) x)
          ∧ (∀ x2 : vir_state * x, kt (eq_rect' H' x2) ≅ Tau (Tau (⟦ ⟅ x1 x2.2 ⟆ ⟧ x2.1))).
  Proof.
    intros.
    rewrite /subevent in H. unfold_cat in H.
    rewrite /ReSum_sum /case_ /Case_sum1 /case_sum1 in H.
    destruct x0.
    - rewrite /resum in H; unfold_cat in H.
      simp L0'_conv in H. setoid_rewrite interp_vis in H.
      simp L0'_conv in H.
      setoid_rewrite interp_state_bind in H.
      setoid_rewrite interp_state_vis in H.
      rewrite bind_bind in H; cbn in H.
      rewrite /handle_stateEff in H. destruct e.
      simp call_conv in H.
      rewrite bind_vis in H.
      apply eqit_inv in H; cbn in H.
      destruct H as (?&?&?). dependent destruction x.
      red in H, H0.
      setoid_rewrite bind_ret_l in H0.
      setoid_rewrite interp_state_ret in H0.
      setoid_rewrite bind_tau in H0.
      setoid_rewrite bind_ret_l in H0. cbn in H0.
      subst.
      do 4 eexists _. do 2 eexists eq_refl. split; eauto.
      cbn. symmetry. rewrite -H0.
      rewrite interp_state_tau; done.
    - setoid_rewrite interp_vis in H.
      rewrite /resum in H.
      destruct s as [ | [ | [ | [ |  ] ] ] ] ; simp L0'_conv in H.
      all: try solve [rewrite bind_vis in H; setoid_rewrite interp_state_vis in H; cbn in H;
        rewrite bind_tau in H; by apply eqit_inv in H].
      destruct s.
      all: try solve [rewrite bind_vis in H; setoid_rewrite interp_state_vis in H; cbn in H;
        rewrite bind_tau in H; by apply eqit_inv in H].
  Qed.

  Lemma interp_L2_conv_F_inv {R X} (a : itree L0' R) σ (e : F _ X) k:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ (vis e k) -> False.
  Proof.
    intros H.
    rewrite /interp_L2 /L0'expr_conv (itree_eta a) in H.

    remember (observe a); clear a Heqi.
    induction i; cbn.
    - rewrite interp_ret interp_state_ret in H.
      by apply eqit_inv in H.
    - rewrite interp_tau interp_state_tau in H.
      by apply eqit_inv in H.
    - rewrite interp_vis interp_state_bind in H.
      destruct e0 eqn: He0.
      + destruct c. simp L0'_conv in H.
        rewrite interp_state_vis bind_bind in H.
        cbn in H. rewrite /handle_stateEff in H.
        rewrite bind_vis in H.
        setoid_rewrite bind_ret_l in H.
        apply eqit_inv in H; cbn in H.
        destruct H as (?&?&?). red in H, H0.
        dependent destruction x; inversion H.

      + destruct s.
        * simp L0'_conv in H.
          rewrite interp_state_vis in H.
          rewrite bind_bind in H. destruct e1.
          simp call_conv in H. rewrite bind_vis in H.
          apply eqit_inv in H. cbn in H.
          destruct H as (?&?&?). red in H, H0.
          dependent destruction x; inversion H.
        * simp L0'_conv in H.
          rewrite interp_state_vis in H.
          rewrite /handle_L0_L2 in H.
          cbn in H. rewrite /case_ /add_tau in H.
          rewrite /handle_stateEff in H.
          rewrite bind_bind bind_tau in H.
          by apply eqit_inv in H.
  Qed.

  Lemma interp_L2_conv_tau_F_inv {R X} (a : itree L0' R) σ σ' (e : F _ X) k:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ Tau (vis e (λ x, Tau (Tau (⟦ ⟅ k x ⟆ ⟧ σ')))) ->
    ∃ k', a ≅ vis e k' /\ (forall x, ⟦ ⟅ k x ⟆ ⟧ σ' ≅ ⟦ ⟅ k' x ⟆ ⟧ σ).
  Proof.
    intros * H. setoid_rewrite (itree_eta a).
    rewrite /interp_L2 /L0'expr_conv (itree_eta a) in H.

    remember (observe a); clear a Heqi.
    induction i; cbn.
    - rewrite interp_ret interp_state_ret in H.
      by apply eqit_inv in H.
    - rewrite interp_tau interp_state_tau in H.
      apply eqit_inv in H. cbn in H.
      exfalso. eapply interp_L2_conv_F_inv; eauto.
    - rewrite interp_vis interp_state_bind in H.
      destruct e0 eqn: He0.
      + destruct c. simp L0'_conv in H.
        rewrite interp_state_vis bind_bind in H.
        cbn in H. rewrite /handle_stateEff in H.
        rewrite bind_vis in H.
        setoid_rewrite bind_ret_l in H.
        by apply eqit_inv in H.
      + destruct s.
        * simp L0'_conv in H.
          rewrite interp_state_vis in H.
          destruct e1; simp call_conv in H; rewrite bind_bind bind_vis in H.
          by apply eqit_inv in H.
        * simp L0'_conv in H.
          rewrite interp_state_vis bind_bind in H.
          setoid_rewrite interp_state_ret in H.
          do 2 setoid_rewrite bind_tau in H.
          setoid_rewrite bind_ret_l in H.
          setoid_rewrite interp_state_tau in H.
          pose proof (handle_noncall_L0_L2_case X0 s σ).

          destruct H0 as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].
          -- setoid_rewrite H0 in H.
             rewrite bind_ret_l in H.
             by repeat (apply eqit_inv in H).
          -- setoid_rewrite H0 in H.
             apply eqit_inv_Tau in H. rewrite bind_vis in H.
             apply eqit_inv in H. cbn in H.
             destruct H as (?&?&?). dependent destruction x2; inversion H.
          -- setoid_rewrite H0 in H.
             apply eqit_inv_Tau in H. rewrite bind_vis in H.
             apply eqit_inv in H. cbn in H.
             destruct H as (?&?&?). dependent destruction x2; inversion H.
          -- setoid_rewrite H0 in H.
             apply eqit_inv_Tau in H. rewrite bind_vis in H.
             apply eqit_inv in H. cbn in H.
             destruct H as (?&?&?). dependent destruction x0; inversion H.
             rewrite /resum /ReSum_id /id_ /Id_IFun in H4; subst.
             eexists k0. split; first done.
             destruct e.
             specialize (H2 tt).
             rewrite bind_ret_l in H2.
             do 2 apply eqit_inv_Tau in H2; cbn in H2.
             intros; eauto. destruct x. symmetry. done.
  Qed.

  Lemma interp_L2_conv_tau_F_inv' {R X} (a : itree L0' R) σ (e : F _ X) k g:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ Tau (vis e (λ x, Tau (Tau (⟦ ⟅ k x ⟆ ⟧ σ)))) ->
    ∃ k', a ≅ vis e k' /\ (forall x, ⟦ ⟅ k x ⟆ ⟧ σ ≅ ⟦ ⟅ k' x ⟆ ⟧ σ) /\
    ⟦ interp_mrec g a ⟧ σ ≅
       Tau (vis (e : F _ _) (fun x => Tau (Tau (⟦ interp_mrec g (k' x) ⟧ σ)))).
  Proof.
    intros H.
    apply interp_L2_conv_tau_F_inv in H.
    destruct H as (?&?&?).
    exists x.  do 2 (split; first done).
    rewrite H interp_mrec_vis.
    apply eqit_Tau; cbn.
    rewrite /pure_state bind_bind bind_vis.
    apply eqit_Vis.
    intros. rewrite !bind_ret_l.
    do 2 apply eqit_Tau. by cbn.
  Qed.

  Lemma interp_L2_conv_F_tau_n_inv {R X} (a : itree L0' R) σ (e : F _ X) k n g:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ n_taus (vis e k) n ->
    (∃ m k' σ'',
      (forall x, k x ≅ Tau (Tau (⟦ ⟅ k' x ⟆ ⟧ σ''))) /\
      (⟦ interp_mrec g a ⟧ σ) ≅
        n_taus (vis (e : F _ _) (fun x => Tau (Tau (⟦ interp_mrec g (k' x) ⟧ σ'')))) m).
  Proof.
    revert a σ e k g.
    induction n; cbn; intros; first by apply interp_L2_conv_F_inv in H.

    apply interp_L2_conv_tau_inv in H.
    destruct H as
      [ (?&?&?) | (?&?&?&?&?) ]; subst.

    - symmetry in H0.
      specialize (IHn _ _ _ _ g H0).
      destruct IHn as (?&?&?&?&?).
      exists (S x0), x1, x2. split; first done.
      rewrite (itree_eta a). rewrite H. rewrite interp_mrec_tau.
      cbn.
      apply eqit_Tau.
      by rewrite H2.

    - pose proof (handle_noncall_L0_L2_case x x0 σ) as Hcase.
      destruct Hcase as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].
      + rewrite H1 bind_ret_l in H0.
        rewrite -!interp_L2_conv_tau in H0.
        symmetry in H0.
        specialize (IHn _ _ _ _ g H0).
        destruct IHn as (?&?&?&?&?).
        exists (S x3), x4, x5. split; try done.
        rewrite (itree_eta a) H interp_mrec_vis H1 bind_ret_l.
        do 2 rewrite -interp_mrec_tau; rewrite H3.
        cbn; by apply eqit_Tau.

      + rewrite H1 bind_vis in H0.
        destruct n; apply eqit_inv in H0; try done.
        destruct H0 as (x'&?&?); dependent destruction x'; inversion H0.

      + rewrite H1 bind_vis in H0.
        destruct n; apply eqit_inv in H0; try done.
        destruct H0 as (x'&?&?); dependent destruction x'; inversion H0.

      + destruct n;
          try solve [
            rewrite H1 bind_vis in H0; apply eqit_inv in H0; done ].
        cbn in *.

        rewrite H1 bind_vis in H0; apply eqit_inv in H0; cbn in H0; clear IHn.

        destruct H0 as (x'&Hev&Hk); dependent destruction x'; inversion Hev.
        unfold_cat in H3; rewrite /Id_IFun in H3; subst.

        red in Hk; setoid_rewrite bind_ret_l in Hk; cbn in Hk.

        exists 1, x1, σ; split; intros.
        { by specialize (Hk x). }


        rewrite (itree_eta a) H interp_mrec_vis H1.
        apply eqit_Tau.

        rewrite bind_vis; apply eqit_Vis.
        by intros; rewrite bind_ret_l.
  Qed.

  Lemma interp_L2_conv_F_tau_S_n_inv {R X} (a : itree L0' R) σ σ' (e : F _ X) k n g:
    ⟦ ⟅ a ⟆ ⟧ σ ≅ n_taus (vis e (λ x, Tau (Tau (⟦ ⟅ k x ⟆ ⟧ σ')))) (S n) ->
    (∃ m k' σ'',
      (forall x, ⟦ ⟅ k x ⟆ ⟧ σ' ≅ ⟦ ⟅ k' x ⟆ ⟧ σ'') /\
      (⟦ interp_mrec g a ⟧ σ) ≅
        n_taus (vis (e : F _ _) (fun x => Tau (Tau (⟦ interp_mrec g (k' x) ⟧ σ'')))) (S m)).
  Proof.
    revert a σ σ' e k g.
    induction n; intros.
    { apply interp_L2_conv_tau_F_inv in H.
      destruct H as (?&?&?). exists 0, x, σ.
      split; auto. rewrite H interp_mrec_vis; cbn.
      rewrite /pure_state bind_bind bind_vis.
      apply eqit_Tau; apply eqit_Vis; intros; by rewrite !bind_ret_l. }

    apply interp_L2_conv_tau_inv in H.

    destruct H as
      [ (?&?&?) | (?&?&?&?&?) ]; subst.

    - symmetry in H0.
      specialize (IHn _ _ σ' _ _ g H0).
      destruct IHn as (?&?&?&?&?).
      exists (S x0), x1, x2. split; first done.
      rewrite (itree_eta a). rewrite H. rewrite interp_mrec_tau.
      cbn.
      apply eqit_Tau.
      by rewrite H2.

    - pose proof (handle_noncall_L0_L2_case x x0 σ) as Hcase.
      destruct Hcase as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].
      + rewrite H1 bind_ret_l in H0.
        rewrite -!interp_L2_conv_tau in H0.
        symmetry in H0.
        specialize (IHn _ _ _ _ _ g H0).
        destruct IHn as (?&?&?&?&?).
        exists (S x3), x4, x5. split; try done.
        rewrite (itree_eta a) H interp_mrec_vis H1 bind_ret_l.
        do 2 rewrite -interp_mrec_tau; rewrite H3.
        cbn; by apply eqit_Tau.

      + rewrite H1 bind_vis in H0.
        destruct n; apply eqit_inv in H0; try done.

      + rewrite H1 bind_vis in H0.
        destruct n; apply eqit_inv in H0; try done.

      + destruct n;
          try solve [
            rewrite H1 bind_vis in H0; apply eqit_inv in H0; done ].
  Qed.

End interp_L2_conv_properties.

From velliris Require Import vir.spec.

Section vir_sim_expr_util.

  Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  Local Open Scope nat_scope.

  Notation st_expr_rel' R1 R2 :=
    (@st_exprO' vir_lang R1 -d> @st_exprO' vir_lang R2 -d> iPropI Σ).

  Definition base {R1 R2} : st_expr_rel' R1 R2 := fun e_t e_s =>
    (∃ (v_t : state vir_lang * R1)
        (v_s : state vir_lang * R2),
        ⌜go e_t = Ret v_t⌝ ∗ ⌜go e_s = Ret v_s⌝)%I.

  Local Definition fail_inv_ind {R1 R2} :
    (st_exprO' (Λ := vir_lang) R1 →
      st_exprO' (Λ := vir_lang) R2 → iPropI Σ) →
      itree' (language.L2 vir_lang) (state vir_lang * R1) →
      itree' (language.L2 vir_lang) (state vir_lang * R2) → iPropI Σ :=
    (λ Φ e_t e_s,
      ∀ X (e : _ X) k k',
        □ (∀ x y, (base x y ∗ Φ x y) ∗-∗ Φ x y) -∗
        ⌜e_t = (VisF (subevent _ (e : FailureE _)) k)⌝ -∗
        ⌜∃ n e, go e_s ≅
          n_taus (Vis (subevent _ (e : exc_events _ void)) k') n⌝
      ∨ ⌜∃ n (e : UBE void), go e_s ≅ n_taus (Vis (subevent _ e) k') n⌝)%I.

  Local Instance fail_inv_ne {R1 R2}:
    NonExpansive (fail_inv_ind: st_expr_rel' _ _ -d> st_expr_rel' R1 R2).
  Proof.
    solve_proper_prepare. clear -H. repeat f_equiv.
  Qed.

  Lemma sim_coindF_fail_inv {R1 R2 X} Ψ (e : _ X) k k' t:
    □ (∀ x y, (base x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    sim_coindF (R1 := R1) (R2 := R2) Ψ (VisF (subevent _ (e : FailureE _)) k) (observe t) -∗
    ⌜∃ n (e : Exception.exceptE () void), t ≅ n_taus (Vis (subevent _ e) k') n⌝
    ∨ ⌜∃ n (e : UBE void), t ≅ n_taus (Vis (subevent _ e) k') n⌝.
  Proof.
    rewrite sim_coindF_unfold.
    iIntros "H Hind".

    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗
      fail_inv_ind (R1 := R1) (R2 := R2) Ψ e_t e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "Hind").
      iSpecialize ("Hgen" $! X _ k k' with "H").
      rewrite /fail_inv_ind.
      iDestruct ("Hgen" $! eq_refl) as %H.
      destruct H; destruct H as (?&?&?); iPureIntro; eauto.
      - rewrite -itree_eta in H. left. eexists _, x0; done.
      - rewrite -itree_eta in H. right. eexists _, x0; done. }

    clear Ψ e k t X k'.

    iIntros (Ψ e_t e_s) "Hsim".

    iApply (sim_indF_strong_ind with "[] Hsim"); clear Ψ e_t e_s.

    iModIntro. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (????) "#H %Ht".

    iMod "Hinner".

    iDestruct "Hinner" as ( c ) "Hinner";
      destruct c; try case_solve; try done.
    - iDestruct ("H" $! e_t e_s) as "(H1 & H2)".
      iSpecialize ("H2" with "Hinner").
      iDestruct "H2" as "(%H' & H2)".
      destruct H' as (?&?&?&?). rewrite Ht in H.
      inversion H.

    - iDestruct "Hinner" as "(Hinner & _)".
      rewrite /fail_inv_ind.
      iSpecialize ("Hinner" $! X _ k k' with "H").
      iDestruct ("Hinner" $! eq_refl) as %H.
      destruct H; [iLeft | iRight];
       destruct H as (?&?&?);
      rewrite -itree_eta in H; setoid_rewrite H;
      iPureIntro; exists (S x), x0; done.

    - inversion H0. dependent destruction H3.
      rewrite /handle_event. cbn; done.

    - iPureIntro. red in e0. destruct e0 eqn: H.
      cbn in e0. right. eexists 0, e0. rewrite Heq. cbn.
      rewrite /subevent H.
      apply eqit_Vis. done.

    - iPureIntro. red in e0. destruct e0 eqn: H.
      cbn in e0. left. eexists 0, e0. rewrite Heq. cbn.
      rewrite /subevent H.
      apply eqit_Vis. done.
  Qed.

  Local Definition UB_inv_ind {R1 R2} :
    (st_exprO' (Λ := vir_lang) R1 →
      st_exprO' (Λ := vir_lang) R2 → iPropI Σ) →
      itree' (language.L2 vir_lang) (state vir_lang * R1) →
      itree' (language.L2 vir_lang) (state vir_lang * R2) → iPropI Σ :=
    (λ Φ e_t e_s,
      ∀ X (e : _ X) k k',
        □ (∀ x y, (base x y ∗ Φ x y) ∗-∗ Φ x y) -∗
        ⌜e_t = (VisF (subevent _ (e : UBE _)) k)⌝ -∗
        ⌜∃ n e, go e_s ≅
          n_taus (Vis (subevent _ (e : exc_events _ void)) k') n⌝
      ∨ ⌜∃ n (e : UBE void), go e_s ≅ n_taus (Vis (subevent _ e) k') n⌝)%I.

  Local Instance UB_inv_ne {R1 R2}:
    NonExpansive (UB_inv_ind: st_expr_rel' _ _ -d> st_expr_rel' R1 R2).
  Proof.
    solve_proper_prepare. clear -H. repeat f_equiv.
  Qed.

  Lemma sim_coindF_UBE_inv {R1 R2 X} Ψ (e : _ X) k k' t:
    □ (∀ x y, (base x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    sim_coindF (R1 := R1) (R2 := R2) Ψ (VisF (subevent _ (e : UBE _)) k) (observe t) -∗
    ⌜∃ n (e : Exception.exceptE () void), t ≅ n_taus (Vis (subevent _ e) k') n⌝
    ∨ ⌜∃ n (e : UBE void), t ≅ n_taus (Vis (subevent _ e) k') n⌝.
  Proof.
    rewrite sim_coindF_unfold.
    iIntros "H Hind".

    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗
      UB_inv_ind (R1 := R1) (R2 := R2) Ψ e_t e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "Hind").
      iSpecialize ("Hgen" $! X _ k k' with "H").
      rewrite /UB_inv_ind.
      iDestruct ("Hgen" $! eq_refl) as %H.
      destruct H; destruct H as (?&?&?); iPureIntro; eauto.
      - rewrite -itree_eta in H. left. eexists _, x0; done.
      - rewrite -itree_eta in H. right. eexists _, x0; done. }

    clear Ψ e k t X k'.

    iIntros (Ψ e_t e_s) "Hsim".

    iApply (sim_indF_strong_ind with "[] Hsim"); clear Ψ e_t e_s.

    iModIntro. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (????) "#H %Ht".

    iMod "Hinner".

    iDestruct "Hinner" as ( c ) "Hinner";
      destruct c; try case_solve; try done.
    - iDestruct ("H" $! e_t e_s) as "(H1 & H2)".
      iSpecialize ("H2" with "Hinner").
      iDestruct "H2" as "(%H' & H2)".
      destruct H' as (?&?&?&?). rewrite Ht in H.
      inversion H.

    - iDestruct "Hinner" as "(Hinner & _)".
      rewrite /fail_inv_ind.
      iSpecialize ("Hinner" $! X _ k k' with "H").
      iDestruct ("Hinner" $! eq_refl) as %H.
      destruct H; [iLeft | iRight];
       destruct H as (?&?&?);
      rewrite -itree_eta in H; setoid_rewrite H;
      iPureIntro; exists (S x), x0; done.

    - inversion H0. dependent destruction H3.
      rewrite /handle_event. cbn; done.

    - iPureIntro. red in e0. destruct e0 eqn: H.
      cbn in e0. right. eexists 0, e0. rewrite Heq. cbn.
      rewrite /subevent H.
      apply eqit_Vis. done.

    - iPureIntro. red in e0. destruct e0 eqn: H.
      cbn in e0. left. eexists 0, e0. rewrite Heq. cbn.
      rewrite /subevent H.
      apply eqit_Vis. done.
  Qed.

  Lemma contains_base_tauL {R1 R2} Ψ :
    □ (∀ x y, (base (R1 := R1) (R2 := R2) x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    □ (∀ x y, Ψ (TauF x) y -∗ Ψ (observe x) y).
  Proof.
    iIntros "#H".
    iModIntro. iIntros (??) "HΨ".
    iSpecialize ("H" $! (TauF x) y).
    iDestruct "H" as "(H1 & H2)".
    iSpecialize ("H2" with "HΨ").
    iDestruct "H2" as "(H2 & _)".
    iDestruct "H2" as (???) "H2".
    inversion H.
  Qed.

  Lemma contains_base_tauR {R1 R2} Ψ :
    □ (∀ x y, (base (R1 := R1) (R2 := R2) x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    □ (∀ x y, Ψ x (TauF y) -∗ Ψ x (observe y)).
  Proof.
    iIntros "#H".
    iModIntro. iIntros (??) "HΨ".
    iSpecialize ("H" $! x (TauF y)).
    iDestruct "H" as "(H1 & H2)".
    iSpecialize ("H2" with "HΨ").
    iDestruct "H2" as "(H2 & _)".
    iDestruct "H2" as (???) "%H2".
    inversion H2.
  Qed.

  Local Definition F_inv_L_ind {R} :
    (st_exprO' (Λ := vir_lang) R →
      st_exprO' (Λ := vir_lang) R → iPropI Σ) →
      itree' (language.L2 vir_lang) (state vir_lang * R) →
      itree' (language.L2 vir_lang) (state vir_lang * R) → iPropI Σ :=
    (λ Φ e_t e_s,
      ∀ X (e : _ X) k σ_t,
      □ (∀ x y, (base x y ∗ Φ x y) ∗-∗ Φ x y) -∗
      ⌜e_t = VisF (subevent _ (e : F _ _)) (λ x, Tau (Tau (⟦ ⟅ k x ⟆ ⟧ σ_t)))⌝ ==∗
      (∃ n k',
          ⌜go e_s ≅
            n_taus (Vis (subevent _ (e : F _ _)) k')
            n⌝ ∗
        ∀ x, sim_coindF (R1 := R) (R2 := R) Φ
            (observe (⟦ ⟅ k x ⟆ ⟧ σ_t)) (observe (k' x))) ∨
      (* Or [e_s] is an error or UB *)
      (∃ n Y (e : _ Y) k', ⌜go e_s ≅ n_taus (vis (e : UBE Y) k') n⌝ ∗
        ∀ x y, ⌜x ~= y⌝ -∗
          sim_coindF (R1 := R) (R2 := R) Φ
            (observe (⟦ ⟅ k x ⟆ ⟧ σ_t)) (observe (k' y))) ∨
      (∃ n Y (e : _ Y) k', ⌜go e_s ≅ n_taus (vis (e : FailureE _) k') n⌝ ∗
        ∀ x y, ⌜x ~= y⌝ -∗
          sim_coindF (R1 := R) (R2 := R) Φ
            (observe (⟦ ⟅ k x ⟆ ⟧ σ_t)) (observe (k' y))))%I.

  Local Instance F_inv_L_ne {R}:
    NonExpansive (F_inv_L_ind: st_expr_rel' _ _ -d> st_expr_rel' R R).
  Proof.
    solve_proper_prepare. clear -H. by repeat f_equiv.
  Qed.

  Lemma sim_coindF_F_inv_L {R X} Ψ (e : _ X) k σ_t e_s:
    □ (∀ x y, (base x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    sim_coindF (R1 := R) (R2 := R) Ψ
        (VisF (subevent _ (e : F _ _)) (λ x, Tau (Tau (⟦ ⟅ k x ⟆ ⟧ σ_t))))
        e_s ==∗
    (∃ n k', ⌜go e_s ≅ n_taus (Vis (subevent _ (e : F _ _)) k') n⌝ ∗
      ∀ x, sim_coindF (R1 := R) (R2 := R) Ψ
          (observe (⟦ ⟅ k x ⟆ ⟧ σ_t)) (observe (k' x))) ∨
    (* Or [e_s] is an error or UB*)
    (∃ n Y (e : _ Y) k', ⌜go e_s ≅ n_taus (vis (e : UBE Y) k') n⌝ ∗
      ∀ x y, ⌜x ~= y⌝ -∗
        sim_coindF (R1 := R) (R2 := R) Ψ
          (observe (⟦ ⟅ k x ⟆ ⟧ σ_t)) (observe (k' y))) ∨
    (∃ n Y (e : _ Y) k', ⌜go e_s ≅ n_taus (vis (e : FailureE _) k') n⌝ ∗
      ∀ x y, ⌜x ~= y⌝ -∗
        sim_coindF (R1 := R) (R2 := R) Ψ
          (observe (⟦ ⟅ k x ⟆ ⟧ σ_t)) (observe (k' y))).
  Proof.
    rewrite sim_coindF_unfold.
    iIntros "#HΨ Hind".

    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗
      F_inv_L_ind (R := R) Ψ e_t e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "Hind HΨ").
      by iSpecialize ("Hgen" $!  eq_refl). }

    iClear "HΨ".
    clear Ψ e k X σ_t e_s.

    iIntros (Ψ e_t e_s) "Hsim".

    iApply (sim_indF_strong_ind with "[] Hsim"); clear Ψ e_t e_s.

    iModIntro. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (????) "#HΦ"; iIntros (Ht).
    rewrite /sim_expr_inner.

    iMod "Hinner".

    iDestruct "Hinner" as ( c ) "Hinner";
      destruct c; try case_solve; try done.
    - iDestruct ("HΦ" $! e_t e_s) as "(H1 & H2)".
      iSpecialize ("H2" with "Hinner").
      iDestruct "H2" as "(%H' & H2)".
      destruct H' as (?&?&?&?). rewrite Ht in H.
      inversion H.

    - iDestruct "Hinner" as "(Hinner & _)".
      rewrite /F_inv_L_ind.
      iSpecialize ("Hinner" with "HΦ").
      iSpecialize ("Hinner" $! eq_refl).
      iMod "Hinner";
        iDestruct "Hinner" as "[ Hinner | [ Hinner | Hinner ] ]".
      { iDestruct "Hinner" as (???) "Hinner".
        iLeft. iExists (S n), k'.
        iModIntro; iSplitL "".
        { rewrite -itree_eta in H. rewrite H. cbn.
          iPureIntro; reflexivity. }
        done. }
      { iRight; iLeft.
        iDestruct "Hinner" as (?????) "Hinner".
        iExists (S n), _, e0, k'.
        destruct e0.
        iSplitL ""; try done.
        iPureIntro. rewrite -itree_eta in H; by rewrite H. }
      { iRight; iRight.
        iDestruct "Hinner" as (?????) "Hinner".
        iExists (S n), _, e0, k'.
        iSplitL ""; try done.
        iPureIntro. rewrite -itree_eta in H; by rewrite H. }

    - inversion H0. dependent destruction H3.
      rewrite /handle_event. cbn.
      destruct es; try done; repeat (try destruct s; try done).
      rewrite /handle_E.
      iDestruct "Hinner" as (?) "Hinner".
      destruct H as (?&?). dependent destruction x.
      red in H; subst.
      iLeft. iExists 0, ks.
      iSplitL "".
      { iPureIntro; by apply eqit_Vis. }
      { iModIntro. iIntros (x').
        assert (x' ~= x') by done.
        iSpecialize ("Hinner" $! _ _ H).
        setoid_rewrite sim_coindF_unfold at 2.
        rewrite sim_indF_unfold. rewrite /sim_expr_inner.
        iMod "Hinner".
        iPoseProof (contains_base_tauL with "HΦ") as "HT".
        iPoseProof (sim_coindF_TauL_inv with "HT Hinner") as "H".
        iPoseProof (sim_coindF_TauL_inv with "HT H") as "H".
        setoid_rewrite sim_coindF_unfold.
        rewrite sim_indF_unfold. by rewrite /sim_expr_inner. }

    - iRight; iLeft.
      iExists 0, _, e0, k0.
      iSplitL "".
      { iPureIntro; cbn. rewrite Heq. apply eqit_Vis; done. }
      iModIntro. iIntros. destruct e0; done.

    - iRight; iRight.
      iExists 0, _, e0, k0.
      iSplitL "".
      { iPureIntro; cbn. rewrite Heq. apply eqit_Vis; done. }
      iModIntro. iIntros. destruct e0; done.
  Qed.

  Local Definition F_inv_R_ind {R} :
    (st_exprO' (Λ := vir_lang) R →
      st_exprO' (Λ := vir_lang) R → iPropI Σ) →
      itree' (language.L2 vir_lang) (state vir_lang * R) →
      itree' (language.L2 vir_lang) (state vir_lang * R) → iPropI Σ :=
    (λ Φ e_t e_s,
      ∀ X (e : _ X) k σ_s,
      □ (∀ x y, (base x y ∗ Φ x y) ∗-∗ Φ x y) -∗
      ⌜e_s = VisF (subevent _ (e : F _ _)) (fun x => Tau (Tau (⟦⟅ k x ⟆⟧ σ_s)))⌝ ==∗
      (∃ n k', ⌜go e_t ≅ n_taus (Vis (subevent _ (e : F _ _)) k') n⌝ ∗
        ∀ x, sim_coindF (R1 := R) (R2 := R) Φ
            (observe (k' x)) (observe (⟦ ⟅ k x ⟆ ⟧ σ_s))))%I.

  Local Instance F_inv_R_ne {R}:
    NonExpansive (F_inv_R_ind: st_expr_rel' _ _ -d> st_expr_rel' R R).
  Proof.
    solve_proper_prepare. clear -H. by repeat f_equiv.
  Qed.

  Lemma sim_coindF_F_inv_R {R X} Ψ (e : _ X) k σ_s t:
    □ (∀ x y, (base x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    sim_coindF (R1 := R) (R2 := R) Ψ t
        (VisF (subevent _ (e : F _ _)) (λ x, Tau (Tau (⟦ ⟅ k x ⟆ ⟧ σ_s)))) ==∗
    (∃ n k', ⌜go t ≅ n_taus (Vis (subevent _ (e : F _ _)) k') n⌝ ∗
      ∀ x, sim_coindF (R1 := R) (R2 := R) Ψ
          (observe (k' x)) (observe (⟦ ⟅ k x ⟆ ⟧ σ_s))).
  Proof.
    rewrite sim_coindF_unfold.
    iIntros "#HΨ Hind".

    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗
      F_inv_R_ind (R := R) Ψ e_t e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "Hind HΨ").
      by iSpecialize ("Hgen" $!  eq_refl). }

    iClear "HΨ".
    clear Ψ e k X σ_s t.

    iIntros (Ψ e_t e_s) "Hsim".

    iApply (sim_indF_strong_ind with "[] Hsim"); clear Ψ e_t e_s.

    iModIntro. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (????) "#HΦ"; iIntros (Ht).
    rewrite /sim_expr_inner.

    iMod "Hinner".

    iDestruct "Hinner" as ( c ) "Hinner";
      destruct c; try case_solve; try done.
    - iDestruct ("HΦ" $! e_t e_s) as "(H1 & H2)".
      iSpecialize ("H2" with "Hinner").
      iDestruct "H2" as "(%H' & H2)".
      destruct H' as (?&?&?&?). rewrite Ht in H0.
      inversion H0.

    - iDestruct "Hinner" as "(Hinner & _)".
      rewrite /F_inv_R_ind.
      iSpecialize ("Hinner" with "HΦ").
      iSpecialize ("Hinner" $! eq_refl).
      iMod "Hinner".
      iDestruct "Hinner" as (???) "Hinner".
      iExists (S n), k'.
      iModIntro; iSplitL "".
      { rewrite -itree_eta in H. rewrite H. cbn.
        iPureIntro; reflexivity. }
      done.

    - dependent destruction H1.
      rewrite /handle_event. cbn.
      destruct et; try done; repeat (try destruct s; try done).
      rewrite /handle_E.
      iDestruct "Hinner" as (?) "Hinner".
      destruct H as (?&?). dependent destruction x.
      red in H; subst.
      iExists 0, kt.
      iSplitL "".
      { iPureIntro; by apply eqit_Vis. }
      { iModIntro. iIntros (x').
        assert (x' ~= x') by done.
        iSpecialize ("Hinner" $! _ _ H).
        setoid_rewrite sim_coindF_unfold at 2.
        rewrite sim_indF_unfold. rewrite /sim_expr_inner.
        iMod "Hinner".
        iPoseProof (contains_base_tauR with "HΦ") as "HT".
        iPoseProof (sim_coindF_TauR_inv with "HT Hinner") as "H".
        iPoseProof (sim_coindF_TauR_inv with "HT H") as "H".
        setoid_rewrite sim_coindF_unfold.
        rewrite sim_indF_unfold. by rewrite /sim_expr_inner. }

    - rewrite Ht in Heq; inversion Heq.
    - rewrite Ht in Heq; inversion Heq.
  Qed.

  Ltac to_inner G :=
    change
      (|==>
        ∃ c : sim_case,
          match c with
          | BASE => ?Φ ?x ?y
          | STUTTER_L => stutter_l
          | STUTTER_R => stutter_r
          | TAU_STEP => tau_step
          | VIS_STEP => vis_step ?x ?y
          | SOURCE_UB => source_ub
          | SOURCE_EXC => source_exc
          end)%I with
          (sim_expr_inner G (sim_indF G) Φ x y).

  Lemma interp_L2_vis_inv' {R X}
    (a : itree _ R) σ (e : language.L2 vir_lang X) k:
    ⟦ a ⟧ σ ≅ Vis e k ->
    (∃ X (e : (ExternalCallE) X)
      (k : X → itree _ R),
      a ≅ vis e k).
  Proof.
    rewrite /interp_L2 /L0'expr_conv.
    intros H. rewrite (itree_eta a) in H.
    setoid_rewrite (itree_eta a).
    remember (observe a). clear Heqi a.
    induction i; cbn.
    - rewrite interp_state_ret in H.
      by apply eqit_inv in H.
    - rewrite interp_state_tau in H.
      by apply eqit_inv in H.
    - rewrite interp_state_vis in H.
      destruct e0 eqn: He0.
      + destruct c. simp L0'_conv in H.
        cbn in H. rewrite /handle_stateEff in H.
        rewrite bind_vis in H.
        setoid_rewrite bind_ret_l in H.
        apply eqit_inv in H; cbn in H.
        destruct H as (?&?&?). red in H, H0.
        dependent destruction x.
        eexists _, (ExternalCall t f args attr), _; reflexivity.
      + destruct s.
        * rewrite bind_tau in H. by apply eqit_inv in H.
        * rewrite bind_tau in H. by apply eqit_inv in H.
  Qed.

  Local Definition F_inv_L_ind1 {R1 R2} :
    (st_exprO' (Λ := vir_lang) R1 →
      st_exprO' (Λ := vir_lang) R2 → iPropI Σ) →
      itree' (language.L2 vir_lang) (state vir_lang * R1) →
      itree' (language.L2 vir_lang) (state vir_lang * R2) → iPropI Σ :=
    (λ Φ e_t e_s,
      ∀ X (e : _ X) k σ_t,
      □ (∀ x y, (base x y ∗ Φ x y) ∗-∗ Φ x y) -∗
      ⌜e_t = VisF (subevent _ (e : F _ _)) (λ x, (Tau (⟦ k x ⟧ σ_t)))⌝ ==∗
      (∃ n k', ⌜go e_s ≅ n_taus (Vis (subevent _ (e : F _ _)) k') n⌝ ∗
        ∀ x, sim_coindF (R1 := R1) (R2 := R2) Φ
            (observe (⟦ k x ⟧ σ_t)) (observe (k' x))) ∨
      (* Or [e_s] is an error or UB *)
      (∃ n Y (e : _ Y) k', ⌜go e_s ≅ n_taus (vis (e : UBE Y) k') n⌝ ∗
        ∀ x y, ⌜x ~= y⌝ -∗
          sim_coindF (R1 := R1) (R2 := R2) Φ
            (observe (⟦ k x ⟧ σ_t)) (observe (k' y))) ∨
      (∃ n Y (e : _ Y) k', ⌜go e_s ≅ n_taus (vis (e : FailureE _) k') n⌝ ∗
        ∀ x y, ⌜x ~= y⌝ -∗
          sim_coindF (R1 := R1) (R2 := R2) Φ
            (observe (⟦ k x ⟧ σ_t)) (observe (k' y))))%I.

  Local Instance F_inv_L_ne1 {R1 R2}:
    NonExpansive (F_inv_L_ind1: st_expr_rel' _ _ -d> st_expr_rel' R1 R2).
  Proof.
    solve_proper_prepare. clear -H. by repeat f_equiv.
  Qed.

  Lemma interp_L2_F_inv' {R X} (a : itree _ R) σ (e : F _ X) k:
    ⟦ a ⟧ σ ≅ (vis e k) -> False.
  Proof.
    intros H.
    rewrite /interp_L2 /L0'expr_conv (itree_eta a) in H.

    remember (observe a); clear a Heqi.
    induction i; cbn.
    - rewrite interp_state_ret in H.
      by apply eqit_inv in H.
    - rewrite interp_state_tau in H.
      by apply eqit_inv in H.
    - rewrite interp_state_vis in H.
      destruct e0 eqn: He0.
      + destruct c.
        cbn in H. rewrite /handle_stateEff in H.
        rewrite bind_vis in H.
        setoid_rewrite bind_ret_l in H.
        apply eqit_inv in H; cbn in H.
        destruct H as (?&?&?). red in H, H0.
        dependent destruction x; inversion H.

      + destruct s.
        * simp L0'_conv in H.
          apply eqit_inv in H. by cbn in H.
        * simp L0'_conv in H.
          apply eqit_inv in H. by cbn in H.
  Qed.

  Lemma interp_L2_F_tau_n_inv {R X} (a : itree _ R) σ (e : F _ X) k n:
    ⟦ a ⟧ σ ≅ n_taus (vis e k) n ->
    (∃ m k' σ'',
      (forall x, k x ≅ Tau (⟦ k' x ⟧ σ'')) /\
      (⟦ a ⟧ σ) ≅
        n_taus (vis (e : F _ _) (fun x => Tau (⟦ (k' x) ⟧ σ''))) m).
  Proof.
    revert a σ e k.
    induction n; cbn; intros; first by apply interp_L2_F_inv' in H.

    apply interp_L2_tau_inv in H.
    destruct H as
      [ (?&?&?) | (?&?&?&?&?) ]; subst.

    - symmetry in H0.
      specialize (IHn _ _ _ _ H0).
      destruct IHn as (?&?&?&?&?).
      exists (S x0), x1, x2. split; first done.
      rewrite (itree_eta a). rewrite H. rewrite -itree_eta.
      setoid_rewrite interp_state_tau; cbn.
      apply eqit_Tau.
      by setoid_rewrite H2.

    - pose proof (handle_noncall_L0_L2_case x x0 σ) as Hcase.
      destruct Hcase as [ (?&?) | [ (?&?&?&?) | [ (?&?&?&?) | (?&?&?) ] ] ].
      + rewrite H1 bind_ret_l in H0.
        rewrite -!interp_state_tau in H0.
        symmetry in H0.
        specialize (IHn _ _ _ _ H0).
        destruct IHn as (?&?&?&?&?).
        exists (S x3), x4, x5. split; try done.
        rewrite (itree_eta a) H. setoid_rewrite interp_state_vis.
        rewrite bind_tau. setoid_rewrite H1. rewrite bind_ret_l.
        cbn; rewrite -interp_state_tau. setoid_rewrite H3. by apply eqit_Tau.

      + rewrite H1 bind_vis in H0.
        destruct n; apply eqit_inv in H0; try done.
        destruct H0 as (x'&?&?); dependent destruction x'; inversion H0.

      + rewrite H1 bind_vis in H0.
        destruct n; apply eqit_inv in H0; try done.
        destruct H0 as (x'&?&?); dependent destruction x'; inversion H0.

      + destruct n;
          try solve [
            rewrite H1 bind_vis in H0; apply eqit_inv in H0; done ].
        cbn in *.

        rewrite H1 bind_vis in H0; apply eqit_inv in H0; cbn in H0; clear IHn.

        destruct H0 as (x'&Hev&Hk); dependent destruction x'; inversion Hev.
        unfold_cat in H3; rewrite /Id_IFun in H3; subst.

        red in Hk; setoid_rewrite bind_ret_l in Hk; cbn in Hk.

        exists 1, x1, σ; split; intros.
        { specialize (Hk x). symmetry. done. }


        rewrite (itree_eta a) H. setoid_rewrite interp_state_vis.
        rewrite bind_tau; setoid_rewrite H1.
        apply eqit_Tau.

        rewrite bind_vis; apply eqit_Vis.
        by intros; rewrite bind_ret_l.
  Qed.

  Lemma sim_coindF_F_inv_L' {R1 R2 X} Ψ (e : _ X) k σ_t e_s:
    □ (∀ x y, (base x y ∗ Ψ x y) ∗-∗ Ψ x y) -∗
    sim_coindF (R1 := R1) (R2 := R2) Ψ
        (VisF (subevent _ (e : F _ _)) (λ x, (Tau (⟦ k x ⟧ σ_t))))
        e_s ==∗
    (∃ n k', ⌜go e_s ≅ n_taus (Vis (subevent _ (e : F _ _)) k') n⌝ ∗
      ∀ x, sim_coindF (R1 := R1) (R2 := R2) Ψ
          (observe (⟦ k x ⟧ σ_t)) (observe (k' x))) ∨
    (* Or [e_s] is an error or UB*)
    (∃ n Y (e : _ Y) k', ⌜go e_s ≅ n_taus (vis (e : UBE Y) k') n⌝ ∗
      ∀ x y, ⌜x ~= y⌝ -∗
        sim_coindF (R1 := R1) (R2 := R2) Ψ
          (observe (⟦ k x ⟧ σ_t)) (observe (k' y))) ∨
    (∃ n Y (e : _ Y) k', ⌜go e_s ≅ n_taus (vis (e : FailureE _) k') n⌝ ∗
      ∀ x y, ⌜x ~= y⌝ -∗
        sim_coindF (R1 := R1) (R2 := R2) Ψ
          (observe (⟦ k x ⟧ σ_t)) (observe (k' y))).
  Proof.
    rewrite sim_coindF_unfold.
    iIntros "#HΨ Hind".

    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗
      F_inv_L_ind1 Ψ e_t e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "Hind HΨ").
      by iSpecialize ("Hgen" $!  eq_refl). }

    iClear "HΨ".
    clear Ψ e k X σ_t e_s.

    iIntros (Ψ e_t e_s) "Hsim".

    iApply (sim_indF_strong_ind with "[] Hsim"); clear Ψ e_t e_s.

    iModIntro. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (????) "#HΦ"; iIntros (Ht).
    rewrite /sim_expr_inner.

    iMod "Hinner".

    iDestruct "Hinner" as ( c ) "Hinner";
      destruct c; try case_solve; try done.
    - iDestruct ("HΦ" $! e_t e_s) as "(H1 & H2)".
      iSpecialize ("H2" with "Hinner").
      iDestruct "H2" as "(%H' & H2)".
      destruct H' as (?&?&?&?). rewrite Ht in H.
      inversion H.

    - iDestruct "Hinner" as "(Hinner & _)".
      rewrite /F_inv_L_ind.
      iSpecialize ("Hinner" with "HΦ").
      iSpecialize ("Hinner" $! eq_refl).
      iMod "Hinner";
        iDestruct "Hinner" as "[ Hinner | [ Hinner | Hinner ] ]".
      { iDestruct "Hinner" as (???) "Hinner".
        iLeft. iExists (S n), k'.
        iModIntro; iSplitL "".
        { rewrite -itree_eta in H. rewrite H. cbn.
          iPureIntro; reflexivity. }
        done. }
      { iRight; iLeft.
        iDestruct "Hinner" as (?????) "Hinner".
        iExists (S n), _, e0, k'.
        destruct e0.
        iSplitL ""; try done.
        iPureIntro. rewrite -itree_eta in H; by rewrite H. }
      { iRight; iRight.
        iDestruct "Hinner" as (?????) "Hinner".
        iExists (S n), _, e0, k'.
        iSplitL ""; try done.
        iPureIntro. rewrite -itree_eta in H; by rewrite H. }

    - inversion H0. dependent destruction H2.
      rewrite /handle_event. cbn.
      destruct es; try done; repeat (try destruct s; try done).
      rewrite /handle_E.
      iDestruct "Hinner" as (?) "Hinner".
      destruct H as (?&?). dependent destruction x.
      red in H; subst.
      iLeft. iExists 0, ks.
      iSplitL "".
      { iPureIntro; by apply eqit_Vis. }
      { iModIntro. iIntros (x').
        assert (x' ~= x') by done.
        iSpecialize ("Hinner" $! _ _ H).
        setoid_rewrite sim_coindF_unfold at 2.
        rewrite sim_indF_unfold. rewrite /sim_expr_inner.
        iMod "Hinner".
        iPoseProof (contains_base_tauL with "HΦ") as "HT".
        iPoseProof (sim_coindF_TauL_inv with "HT Hinner") as "H".
        setoid_rewrite sim_coindF_unfold.
        rewrite sim_indF_unfold. by rewrite /sim_expr_inner. }

    - iRight; iLeft.
      iExists 0, _, e0, k0.
      iSplitL "".
      { iPureIntro; cbn. rewrite Heq. apply eqit_Vis; done. }
      iModIntro. iIntros. destruct e0; done.

    - iRight; iRight.
      iExists 0, _, e0, k0.
      iSplitL "".
      { iPureIntro; cbn. rewrite Heq. apply eqit_Vis; done. }
      iModIntro. iIntros. destruct e0; done.
  Qed.

  Definition lift_expr_rel_leaf {R1 R2}
    (Φ : expr vir_lang R1 -d> expr vir_lang R2 -d> iPropI Σ)
    (e_t : st_expr' vir_lang R1) (e_s : st_expr' vir_lang R2) :
    (st_expr' vir_lang R1 -d> st_expr' vir_lang R2 -d> iPropI Σ) :=
    fun t s => (∃ σ_t v_t σ_s v_s,
      ⌜Ret (σ_t, v_t) ≅ go t⌝ ∗ ⌜Ret (σ_s, v_s) ≅ go s⌝ ∗
      state_interp σ_t σ_s ∗ Φ (Ret v_t) (Ret v_s) ∗
      ⌜Leaf.Leaf (σ_t, v_t) (go e_t)⌝ ∗ ⌜Leaf.Leaf (σ_s, v_s) (go e_s)⌝)%I.

  Local Definition coind_leaf_pred {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' vir_lang R1) (e_s:st_expr' vir_lang R2) =>
      (∃ Q,
        (∀ x y,
          (lift_expr_rel_leaf
            (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q x y)) e_t e_s) x y ==∗
            Φ x y) ∗
      sim_coindF
        (lift_expr_rel (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q x y)))
         e_t e_s)%I.

  Local Definition coind_leaf_rec {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' vir_lang R1) (e_s:st_expr' vir_lang R2) =>
      ((∃ Q,
        (∀ x y,
          (lift_expr_rel_leaf
            (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q x y)) e_t e_s) x y ==∗
            Φ x y) ∗
      sim_coindF
        (lift_expr_rel (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q x y)))
         e_t e_s)
      ∨ sim_coindF Φ e_t e_s)%I.

  Local Instance coind_leaf_pred_ne {R1 R2}:
    NonExpansive (coind_leaf_pred: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H. solve_proper_prepare. do 18 f_equiv; try solve_proper.
  Qed.

  Local Instance coind_leaf_rec_ne {R1 R2}:
    NonExpansive (coind_leaf_rec: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H. solve_proper_prepare. repeat f_equiv; try solve_proper.
  Qed.

  Local Definition coind_leaf_ind {R1 R2} :
    (st_exprO' (Λ := vir_lang) R1 -d>
      st_exprO' (Λ := vir_lang) R2 -d> iPropI Σ) -d>
      itree' (language.L2 vir_lang) (state vir_lang * R1) -d>
      itree' (language.L2 vir_lang) (state vir_lang * R2) -d> iPropI Σ :=
    (λ Φ e_t e_s,
      ∀ Q,
        □ (∀ x y, (Φ x y ∗-∗
              (lift_expr_rel
                (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q x y))) x y)) -∗
      sim_indF coind_leaf_rec
          (lift_expr_rel_leaf
            (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q x y)) e_t e_s)
          e_t e_s)%I.

  Local Instance coind_leaf_ind_pred_ne {R1 R2} :
    NonExpansive (@coind_leaf_ind R1 R2).
  Proof.
    intros x y * H *.
    solve_proper_prepare. repeat f_equiv.
  Qed.

  Lemma coind_leaf_rec_post_mono {R1 R2} :
    ⊢ <pers>
    (∀ Φ0 Φ' : st_exprO' R1 → st_exprO' R2 → iPropI Σ,
        (∀ (e_t : st_exprO' R1) (e_s : st_exprO' R2),
            Φ0 e_t e_s ==∗ Φ' e_t e_s) -∗
        ∀ (e_t : st_exprO' R1) (e_s : st_exprO' R2),
          coind_leaf_rec Φ0 e_t e_s -∗ coind_leaf_rec Φ' e_t e_s).
  Proof.
    iModIntro.
    iIntros (??) "HΦ".
    iIntros (??) "Hl".
    rewrite /coind_leaf_rec.
    iDestruct "Hl" as "[ H | H ]".
    { iDestruct "H" as (?)"(H & Hs)".
      iLeft.
      repeat iExists _; repeat (iSplitL ""; first done); iFrame.
      iIntros (??).
      iIntros "Hrel"; iSpecialize ("H" with "Hrel").
      iMod "H". iApply ("HΦ" with "H"). }
    iRight.
    iApply (sim_coindF_bupd_mono with "[HΦ]"); [ | iApply "H"]; done.
  Qed.

  Lemma sim_coindF_leaf {R1 R2} Q (e_t : _ R1) (e_s : _ R2):
    sim_coindF
      (lift_expr_rel
         (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q x y))) e_t e_s -∗
    sim_coindF
      (lift_expr_rel_leaf
          (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q x y)) e_t e_s)%I
      e_t e_s.
  Proof.
    iIntros "H".

    (* Coinductive schema *)
    iApply (sim_coindF_strong_coind coind_leaf_pred); cycle 1.
    { rewrite /coind_leaf_pred.
      repeat iExists _. repeat (iSplitL ""; first done).
      iSplitL "".
      { iIntros (??); iIntros "H"; done. }
      done. }

    clear Q e_t e_s.
    iModIntro.

    iIntros (Φ e_t e_s) "IH".
    iDestruct "IH" as (?) "(HΦ & CIH)"; subst.

    rewrite sim_coindF_unfold.
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗
      coind_leaf_ind Ψ e_t e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "CIH").
      rewrite /coind_leaf_ind.
      iApply (sim_indF_mono coind_leaf_rec).
      { iModIntro; iIntros (???) "H".
        rewrite /coind_leaf_rec. done. }
      iApply (sim_indF_post_mono with "[] [HΦ] [Hgen]");
        [  | | iApply "Hgen"]; eauto.
      { iApply coind_leaf_rec_post_mono. }
      iModIntro.
      iIntros (??); iSplit; iIntros "H"; done. }

    clear Φ Q e_t e_s.
    iIntros (Ψ e_t e_s) "Hsim".

    iApply (sim_indF_strong_ind with "[] Hsim"); clear Ψ e_t e_s.

    iModIntro.
    iIntros (???) "IH"; iIntros (?) "#H".

    rewrite !sim_indF_unfold.
    iMod "IH".

    to_inner (coind_leaf_rec (R1 := R1) (R2 := R2)).
    iDestruct "IH" as (?) "IH".
    destruct c eqn: Hc; try solve case_solve.

    { (* BASE CASE *)
      rewrite /lift_expr_rel.

      iSpecialize ("H" with "IH").
      iDestruct "H" as (??????) "(SI & H)".
      iDestruct "H" as (????) "HQ".
      provide_case: BASE; iFrame.
      apply eqit_inv_Ret in H1, H2; subst.
      iSplitL "HQ".
      { repeat iExists _; repeat (iSplitL ""; first done); iFrame. }
      iPureIntro. to_eq in H; to_eq in H0. rewrite -H -H0.
      split; by apply Leaf.LeafRet. }

    { (* STUTTER L case *)
      case_solve.

      iDestruct "IH" as "(IH & _)".
      iSpecialize ("IH" with "H").
      provide_case: STUTTER_L.
      iApply sim_indF_post_mono ; [ | | iApply "IH"]; eauto.
      { iApply coind_leaf_rec_post_mono. }

      iIntros (??) "Hl".
      rewrite /lift_expr_rel_leaf.
      iDestruct "Hl" as (??????) "(SI & (Hl & %Hl1 & %Hl2))".
      iDestruct "Hl" as (????) "HQ".
      repeat iExists _. repeat (iSplitL ""; first done); iFrame.
      iSplitL "HQ".
      { repeat iExists _. repeat (iSplitL ""; first done); by iFrame. }
      iModIntro. iSplitL; iPureIntro; [ | done].
      eapply Leaf.LeafTau; eauto; by rewrite -itree_eta in Hl1. }

    { (* STUTTER R case *)
      case_solve.

      iDestruct "IH" as "(IH & _)".
      iSpecialize ("IH" with "H").
      provide_case: STUTTER_R.
      iApply sim_indF_post_mono ; [ | | iApply "IH"]; eauto.
      { iApply coind_leaf_rec_post_mono. }

      iIntros (??) "Hl".
      rewrite /lift_expr_rel_leaf.
      iDestruct "Hl" as (??????) "(SI & (Hl & %Hl1 & %Hl2))".
      iDestruct "Hl" as (????) "HQ".
      repeat iExists _. repeat (iSplitL ""; first done); iFrame.
      iSplitL "HQ".
      { repeat iExists _. repeat (iSplitL ""; first done); by iFrame. }
      iModIntro. iSplitL; iPureIntro; [ done | ].
      eapply Leaf.LeafTau; eauto; by rewrite -itree_eta in Hl2. }

    { (* TAU case *)
      case_solve; provide_case: TAU_STEP.
      iLeft. iExists Q. iSplitL "".
      { iIntros (??) "Hl".
        rewrite /lift_expr_rel_leaf.
        iDestruct "Hl" as (??????) "(SI & (Hl & %Hl1 & %Hl2))".
        iDestruct "Hl" as (????) "HQ".
        repeat iExists _. repeat (iSplitL ""; first done); iFrame.
        iSplitL "HQ".
        { repeat iExists _. repeat (iSplitL ""; first done); by iFrame. }
        apply eqit_inv_Ret in H1, H2; subst.
        iModIntro. iSplitL; iPureIntro.
        { eapply Leaf.LeafTau; eauto; by rewrite -itree_eta in Hl1. }
        { eapply Leaf.LeafTau; eauto; by rewrite -itree_eta in Hl2. } }
      iApply sim_coindF_bupd_mono; [ | done].
      iIntros (??) "HΦ"; iModIntro. iApply "H"; done. }

    { (* VIS case *)
      case_solve; provide_case: VIS_STEP.
      rewrite /handle_event.
      destruct et, es; try done.
      { destruct c, c0. destruct p, p0.
        simp handle_call_events.

        iDestruct "IH" as "[IH | IH]".
        { iDestruct "IH" as (?) "(SI&Hcall&IH)".
          iLeft; iFrame.
          iExists C; iFrame.
          iIntros (??) "Hpre".
          iSpecialize ("IH" with "Hpre"); iMod "IH".
          iLeft. iModIntro.
          cbn in v_t, v_s.
          iExists Q. iSplitL "".
          { iIntros (??) "Hl".
            rewrite /lift_expr_rel_leaf.
            iDestruct "Hl" as (??????) "(SI & (Hl & %Hl1 & %Hl2))".
            iDestruct "Hl" as (????) "HQ".
            repeat iExists _. repeat (iSplitL ""; first done); iFrame.
            iSplitL "HQ".
            { repeat iExists _. repeat (iSplitL ""; first done); by iFrame. }
            apply eqit_inv_Ret in H1, H2; subst.
            iModIntro. iSplitL; iPureIntro.
            { eapply Leaf.LeafVis; eauto; by rewrite -itree_eta in Hl1. }
            { eapply Leaf.LeafVis; eauto; by rewrite -itree_eta in Hl2. } }

          iApply sim_coindF_bupd_mono; [ | iApply "IH"].
          iIntros (??) "H'". iModIntro; by iApply "H". }

        { iDestruct "IH" as (?) "(SI&Hcall&IH)".
          iRight; iFrame.
          iExists C; iFrame.
          iIntros (??) "Hpre".
          iSpecialize ("IH" with "Hpre"); iMod "IH".
          iLeft. iModIntro.
          cbn in v_t, v_s.
          iExists Q. iSplitL "".

          { iIntros (??) "Hl".
            rewrite /lift_expr_rel_leaf.
            iDestruct "Hl" as (??????) "(SI & (Hl & %Hl1 & %Hl2))".
            iDestruct "Hl" as (????) "HQ".
            repeat iExists _. repeat (iSplitL ""; first done); iFrame.
            iSplitL "HQ".
            { repeat iExists _. repeat (iSplitL ""; first done); by iFrame. }
            apply eqit_inv_Ret in H1, H2; subst.
            iModIntro. iSplitL; iPureIntro.
            { eapply Leaf.LeafVis; eauto; by rewrite -itree_eta in Hl1. }
            { eapply Leaf.LeafVis; eauto; by rewrite -itree_eta in Hl2. } }

          iApply sim_coindF_bupd_mono; [ | iApply "IH"].
          iIntros (??) "H'". iModIntro; by iApply "H". } }

      destruct s, s0; try destruct s, s0; try done.
      destruct f, f0; rewrite /handle_E.
      iDestruct "IH" as (?) "IH". destruct H as (?&?).
      dependent destruction x; red in H; inv H.
      iSplitL "".
      { iPureIntro; exists eq_refl; done. }
      iIntros (???). iSpecialize ("IH" $! _ _ H).
      dependent destruction H. iMod "IH".

      iModIntro. iLeft.
      iExists Q. iSplitL "".

      { iIntros (??) "Hl".
        rewrite /lift_expr_rel_leaf.
        iDestruct "Hl" as (??????) "(SI & (Hl & %Hl1 & %Hl2))".
        iDestruct "Hl" as (????) "HQ".
        repeat iExists _. repeat (iSplitL ""; first done); iFrame.
        iSplitL "HQ".
        { repeat iExists _. repeat (iSplitL ""; first done); by iFrame. }
        apply eqit_inv_Ret in H1, H2; subst.
        iModIntro. iSplitL; iPureIntro.
        { eapply Leaf.LeafVis; eauto; by rewrite -itree_eta in Hl1. }
        { eapply Leaf.LeafVis; eauto; by rewrite -itree_eta in Hl2. } }

      iApply sim_coindF_bupd_mono; [ | iApply "IH"].
      iIntros (??) "H'". iModIntro; by iApply "H". }

    (* UB *)
    { case_solve. inversion Heq.
      by provide_case: SOURCE_UB. }

    (* EXC *)
    { case_solve. inversion Heq.
      by provide_case: SOURCE_EXC. }
  Qed.

  Lemma sim_expr_leaf {R1 R2} Q (e_t : _ R1) (e_s : _ R2):
    e_t ⪯ e_s
      [{ (v_t, v_s), Q v_t v_s }] -∗
    e_t ⪯ e_s
      [{ (v_t, v_s),
          ∃ σ_t σ_s σ_t' σ_s',
            Q v_t v_s ∗
            ⌜Leaf.Leaf (σ_t', v_t) (⟦ e_t ⟧ σ_t)⌝ ∗
            ⌜Leaf.Leaf (σ_s', v_s) (⟦ e_s ⟧ σ_s)⌝ }].
  Proof.
    iIntros "H".

    rewrite sim_expr_eq.
    iIntros (??) "SI". iSpecialize ("H" with "SI"); iMod "H".
    rewrite /sim_coind.
    iPoseProof (sim_coindF_leaf with "H") as "H".
    iApply sim_coindF_bupd_mono; [ | iApply "H"].
    iIntros (??) "H".
    iDestruct "H" as (??????) "(SI & H & %Hl1 & %Hl2)".
    iDestruct "H" as (????) "H".
    repeat iExists _; repeat (iSplitL ""; first done); iFrame.
    repeat iExists _; repeat (iSplitL ""; first done); iFrame.
    apply eqit_inv_Ret in H1, H2; subst.
    rewrite -itree_eta in Hl1.
    rewrite -itree_eta in Hl2.
    repeat iExists _; iSplitL; by iPureIntro.
  Qed.

End vir_sim_expr_util.
