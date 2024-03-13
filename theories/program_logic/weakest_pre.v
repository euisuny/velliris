(** * SLSLS, Separation Logic Stuttering Local Simulation *)

From iris.algebra Require Export ofe.
From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.
From iris.bi Require Import bi fixpoint.
From simuliris.simulation Require Export language.
From simuliris.simulation Require Export simulation.
From simuliris.utils Require Import tactics.
From iris.prelude Require Import options.
Import bi.

From ITree Require Import ITree
     Eq Events.State Events.StateFacts Props.Leaf.

From Coq Require Import Program.Equality.

From Paco Require Import paco.

From Equations Require Import Equations.

Section fix_lang.
  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language} {η : handlers Λ}.
  Context {si : simulirisGS PROP Λ}.

  Set Default Proof Using "Type*".
  Section sim_def.

    Context {R1 R2 : Type}.
    Notation expr_rel' := (@exprO' Λ R1 -d> @exprO' Λ R2 -d> PROP).
    Notation st_expr_rel' := (@st_exprO' Λ R1 -d> @st_exprO' Λ R2 -d> PROP).
    Notation expr_rel := (@exprO Λ R1 -d> @exprO Λ R2 -d> PROP).
    Notation st_expr_rel := (@st_exprO Λ R1 -d> @st_exprO Λ R2 -d> PROP).

    Definition call_args_eq {X Y} :
      CallE (call_events Λ) X -> CallE (call_events Λ) Y -> checkedout_sets -> PROP :=
      λ (X0 : CallE (call_events Λ) X) (X1 : CallE (call_events Λ) Y) C,
        let Data0 := call_data (call_events Λ) X X0 in
        let Data1 := call_data (call_events Λ) Y X1 in
        let X2 := args (call_events Λ) X X0 in
        let X3 := args (call_events Λ) Y X1 in
        (arg_val_rel X2 X3 C ∗ ⌜Data0 = Data1⌝)%I.

    Definition call_returns {X}
      (e : @CallE (call_events Λ) X) (v : Res (call_events Λ)) : X.
    Proof.
      apply Hval in e. by rewrite -e in v.
    Defined.

    (* Each kind of event is handled with separate handlers. *)
    Equations handle_call_events {X Y}
               (greatest_rec : st_expr_rel')
               (k_t : X -> itree (L2 Λ) (language.state Λ * R1)) (k_s : Y -> itree (L2 Λ) (language.state Λ * R2))
               (e_t : CallEvents Λ X)
               (e_s : CallEvents Λ Y) : PROP :=
      handle_call_events _ k_t k_s
         (StateEff (call_events Λ) (σ_t, ev_t))
         (StateEff (call_events Λ) (σ_s, ev_s)) :=
        ((* arguments and answers are related and these are in simulation, or *)
          (∃ C, state_interp σ_t σ_s ∗ call_args_eq ev_t ev_s C ∗
            (∀ v_t v_s,
                state_interp v_t.1 v_s.1 ∗ res_val_rel v_t.2 v_s.2 C ==∗
              greatest_rec
                (observe (k_t (v_t.1, call_returns ev_t v_t.2)))
                (observe (k_s (v_s.1, call_returns ev_s v_s.2))))) ∨

        (* we check that the calls meet a specification *)
         ((∃ C, state_interp σ_t σ_s ∗ call_ev ev_t ev_s C ∗
            (∀ v_t v_s, state_interp v_t.1 v_s.1 ∗
                call_ans ev_t v_t.2 ev_s v_s.2 C ==∗
                  greatest_rec (observe (k_t v_t)) (observe (k_s v_s))))))%I.

    Definition handle_E {Ev} {X Y}
               (greatest_rec : st_expr_rel')
               (k_t : X -> itree (L2 Λ) (language.state Λ * R1)) (k_s : Y -> itree (L2 Λ) (language.state Λ * R2))
               (e_t : Ev X) (e_s : Ev Y) : PROP :=
      ⌜exists p : X = Y, eqeq _ p e_t e_s⌝ ∗
        (∀ v_t v_s, ⌜v_t ~= v_s⌝ ==∗ greatest_rec (observe (k_t v_t)) (observe (k_s v_s))%I).

    Definition handle_event {X Y}
               (greatest_rec : st_expr_rel')
               (k_t : X -> itree (L2 Λ) (language.state Λ * R1)) (k_s : Y -> itree (L2 Λ) (language.state Λ * R2))
               (e_t : (L2 Λ) X) (e_s : (L2 Λ) Y) : PROP :=
      let handle_call_events_ := handle_call_events greatest_rec k_t k_s in
      let handle_E_ := handle_E greatest_rec k_t k_s in
      match e_t, e_s with
      | inl1 e_t, inl1 e_s => handle_call_events_ e_t e_s
      | inr1 (inr1 (inr1 e_t)), inr1 (inr1 (inr1 e_s)) => handle_E_ e_t e_s
      | _, _ => False
      end.

    (* Simulation relation over itrees with state, which has a similar definition
      to [euttEv] (eutt parameterized by a relation on uninterpreted events).

      The relation is over [st_expr_rel], which is the state paired with an itree.

      The simulation relation is parameterized by a relation on values ([expr_rel]).

      The intermediate states resulting from events are quantified existentially,
      and must satisfy [env_interp]. [env_interp] is a predicate over the
      visible events, state change, and value passed onto the continuation.

      This definition does not keep track of thread pools, and is a symmetric
      definition (no "only-stuttering" in the source side). *)
    Variant sim_case : Type :=
      | BASE
      | STUTTER_L
      | STUTTER_R
      | TAU_STEP
      | VIS_STEP
      | SOURCE_UB
      | SOURCE_EXC.

    Definition stutter_l (least_rec : st_expr_rel' -d> st_expr_rel')
      : st_expr_rel' -d> st_expr_rel' :=
      fun Φ st_t st_s =>
        (∃ t, ⌜go st_t = Tau t⌝ ∧ least_rec Φ (observe t) st_s)%I.

    Definition stutter_r (least_rec : st_expr_rel' -d> st_expr_rel')
      : st_expr_rel' -d> st_expr_rel' :=
      fun Φ st_t st_s =>
        (∃ s, ⌜go st_s = Tau s⌝ ∧ least_rec Φ st_t (observe s))%I.

    Definition tau_step (greatest_rec : st_expr_rel' -d> st_expr_rel')
      : st_expr_rel' -d> st_expr_rel' :=
      fun Φ st_t st_s =>
        (∃ t s, ⌜go st_t = Tau t⌝ ∧ ⌜go st_s = Tau s⌝
                ∧ greatest_rec Φ (observe t) (observe s))%I.

    Definition vis_step (greatest_rec : st_expr_rel' -d> st_expr_rel')
      : st_expr_rel' -d> st_expr_rel' :=
      fun Φ st_t st_s =>
        (∃ X Y (e_t : _ X) (e_s : _ Y) k_t k_s,
            ⌜go st_t = Vis e_t k_t⌝ ∧ ⌜go st_s = Vis e_s k_s⌝
            ∧ handle_event (greatest_rec Φ) k_t k_s e_t e_s)%I.

    Definition source_ub : st_expr_rel' :=
      fun st_t st_s => (∃ X (e : _ X) k, ⌜go st_s = Vis (inr1 (inl1 e)) k⌝)%I.

    Definition source_exc : st_expr_rel' :=
      fun st_t st_s => (∃ X (e : _ X) k, ⌜go st_s = Vis (inr1 (inr1 (inl1 e))) k⌝)%I.

    Definition sim_expr_inner
                (greatest_rec : st_expr_rel' -d> st_expr_rel')
                (least_rec : st_expr_rel' -d> st_expr_rel')
      : st_expr_rel' -d> st_expr_rel' :=
      fun Φ st_t st_s =>
        (|==> ∃ (c : sim_case),
              match c with
              | BASE => Φ st_t st_s
              | STUTTER_L => stutter_l least_rec Φ st_t st_s
              | STUTTER_R => stutter_r least_rec Φ st_t st_s
              | TAU_STEP => tau_step greatest_rec Φ st_t st_s
              | VIS_STEP => vis_step greatest_rec Φ st_t st_s
              | SOURCE_UB => source_ub st_t st_s
              | SOURCE_EXC => source_exc st_t st_s
              end)%I.

    Definition sim_indF (greatest_rec : st_expr_rel' -d> st_expr_rel') :
      st_expr_rel' -d> st_expr_rel' :=
      curry3 (bi_least_fixpoint
                (λ (least_rec: prodO (prodO (@st_exprO' Λ R1 -d> @st_exprO' Λ R2 -d> PROP) (@st_exprO' Λ R1)) (@st_exprO' Λ R2) -d> PROP),
          uncurry3 (sim_expr_inner greatest_rec (curry3 least_rec)))).

    Definition sim_coindF : st_expr_rel' -d> st_expr_rel' :=
      curry3 (bi_greatest_fixpoint
          (λ (greatest_rec: prodO (prodO ((st_exprO' R1) -d> (st_exprO' R2) -d> PROP) (st_exprO' R1)) (st_exprO' R2) → PROP),
            uncurry3 (sim_indF (curry3 greatest_rec)))).

    Definition lift_expr_rel (Φ : expr_rel) : st_expr_rel' :=
      fun t s => (∃ σ_t v_t σ_s v_s, ⌜Ret (σ_t, v_t) ≅ go t⌝ ∗
                                  ⌜Ret (σ_s, v_s) ≅ go s⌝ ∗
                                  state_interp σ_t σ_s ∗ Φ (Ret v_t) (Ret v_s))%I.

    Definition sim_coind : expr_rel -d> st_expr_rel :=
      fun Φ x y => sim_coindF (lift_expr_rel Φ) (observe x) (observe y).

    Definition sim_expr_ : expr_rel -d> expr_rel :=
      fun Φ e_t e_s =>
        (∀ σ_t σ_s, state_interp σ_t σ_s ==∗
              sim_coind Φ (⟦η⟨e_t⟩⟧ σ_t) (⟦η⟨e_s⟩⟧ σ_s))%I.
    Arguments sim_expr /.

  End sim_def.

  Arguments sim_expr_ / {R1 R2}.

End fix_lang.

Ltac case_solve :=
  match goal with
  | [ |- context[environments.Esnoc _ (INamed ?H) (stutter_l _ _ _ _)]] =>
      let Heq := fresh "Heq" in
      let t := fresh "t" in
      iDestruct H as (t Heq) H; try inv Heq
  | [ |- context[environments.Esnoc _ (INamed ?H) (stutter_r _ _ _ _)]] =>
      let Heq := fresh "Heq" in
      let t := fresh "t" in
      iDestruct H as (t Heq) H; try inv Heq
  | [ |- context[environments.Esnoc _ (INamed ?H) (tau_step _ _ _ _)]] =>
      let Heq_t := fresh "Heq_t" in
      let Heq_s := fresh "Heq_s" in
      let t := fresh "t" in
      let s := fresh "s" in
      iDestruct H as (t s Heq_t Heq_s) H;
      try inv Heq_t; try inv Heq_s
  | [ |- context[environments.Esnoc _ (INamed ?H) (vis_step _ _ _ _)]] =>
      let Heq_t := fresh "Heq_t" in
      let Heq_s := fresh "Heq_s" in
      let et := fresh "et" in
      let es := fresh "es" in
      let kt := fresh "kt" in
      let ks := fresh "ks" in
      iDestruct H as (? ? et es kt ks Heq_t Heq_s) H;
      try inv Heq_t; try inv Heq_s
  | [ |- context[environments.Esnoc _ (INamed ?H) (source_ub _ _)]] =>
      let Heq := fresh "Heq" in
      iDestruct H as (? ? ?) "%Heq"; try solve [inv Heq]
  | [ |- context[environments.Esnoc _ (INamed ?H) (source_exc _ _)]] =>
      let Heq := fresh "Heq" in
      iDestruct H as (? ? ?) "%Heq"; try solve [inv Heq]
  end.

Ltac case_simp H :=
  let c := fresh "c" in
  iMod H; iDestruct H as (c) H; iExists c;
  destruct c; try case_solve; try done.

Ltac provide_case := iModIntro; repeat iExists _; repeat (iSplitL ""; [ done |]).
Tactic Notation "provide_case:" constr(H) :=
  iModIntro; iExists H; repeat iExists _; repeat (iSplitL ""; [ done | ]).

Arguments sim_expr_ {_ _ _ _ _ _ _} [_ _] /.

Section sim_properties.

  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language} {η : handlers Λ}.
  Context {si : simulirisGS PROP Λ}.

  Set Default Proof Using "Type*".

  Notation expr_rel' R1 R2 := (@exprO' Λ R1 -d> @exprO' Λ R2 -d> PROP).
  Notation st_expr_rel' R1 R2 := (@st_exprO' Λ R1 -d> @st_exprO' Λ R2 -d> PROP).
  Notation expr_rel R1 R2 := (@exprO Λ R1 -d> @exprO Λ R2 -d> PROP).
  Notation st_expr_rel R1 R2 := (@st_exprO Λ R1 -d> @st_exprO Λ R2 -d> PROP).

  Local Instance expr_rel'_func_ne {R1 R2} (F: expr_rel' R1 R2 -d> expr_rel' R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance st_expr_rel'_func_ne {R1 R2} (F: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance expr_rel_func_ne {R1 R2} (F: expr_rel R1 R2 -d> expr_rel R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance st_expr_rel_func_ne {R1 R2} (F: st_expr_rel R1 R2 -d> st_expr_rel R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  (** Instantiate Sim typeclasses. Instances are local, see hitn and comment at
  the bottom of this file. *)
  Definition sim_expr_aux : seal (@sim_expr_ _ _ _ _ Λ η _).
  Proof. by eexists. Qed.
  Local Instance sim_expr_stutter : SimE PROP Λ := (sim_expr_aux).(unseal).
  Lemma sim_expr_eq {R1 R2} : sim_expr =
    λ Φ e_t e_s, sim_expr_ (η := η) (R1 := R1) (R2 := R2) Φ e_t e_s.
  Proof. rewrite -sim_expr_aux.(seal_eq) //. Qed.

  Definition lift_post {E} {R1 R2} (Φ: R1 → R2 → PROP) :=
    (λ (e_t : itree E R1) (e_s : itree E R2), ∃ v_t v_s, ⌜e_t ≅ Ret  v_t⌝
                           ∗ ⌜e_s ≅ Ret v_s ⌝ ∗ Φ v_t v_s)%I.
  Definition sim_def {R1 R2} (Φ : R1 → R2 → PROP) e_t e_s  :=
    sim_expr (lift_post Φ) e_t e_s.
  Local Instance sim_stutter : SimV PROP Λ := @sim_def.

  Definition lift_post_val {R1 R2} (Φ: R1 → R2 → PROP) :=
    (λ (e_t : @st_exprO' Λ R1) (e_s : @st_exprO' Λ R2),
      ∃ σ_t v_t σ_s v_s,
        ⌜e_t = RetF (σ_t, v_t)⌝ ∗ ⌜e_s = RetF (σ_s, v_s)⌝ ∗ Φ v_t v_s)%I.

  #[global] Instance sim_val: Sim PROP Λ :=
      λ (R1 R2 : Type) (Φ : R1 → R2 → PROP) (e_t : L2_expr Λ R1) (e_s : L2_expr Λ R2),
      sim_coindF (lift_post_val Φ) (observe e_t) (observe e_s).

  Lemma lift_post_leaf {E R1 R2} (Φ : R1 -> R2 -> _) (e_t : _ R1) (e_s : _ R2) :
    lift_post Φ e_t e_s ⊣⊢
    lift_post (E := E)
      (fun v_t v_s =>
          Φ v_t v_s ∗
            ⌜Leaf.Leaf v_t e_t⌝ ∗ ⌜Leaf.Leaf v_s e_s⌝) e_t e_s.
  Proof.
    iSplit.
    { rewrite /lift_post.
      iIntros "H".
      iDestruct "H" as (????) "H".
      subst. repeat iExists _; eauto.
      do 2 (iSplitL ""; [ done | ]). iFrame.
      rewrite H H0.
      iSplitL ""; iPureIntro; by constructor. }
    { rewrite /lift_post.
      iIntros "H".
      iDestruct "H" as (????) "(H&H')".
      subst. repeat iExists _; eauto. }
  Qed.

  Lemma lift_post_val_leaf {R1 R2} (Φ : R1 -> R2 -> _) (e_t : _ R1) (e_s : _ R2) :
    lift_post_val Φ e_t e_s ⊣⊢
    lift_post_val
      (fun v_t v_s =>
          Φ v_t v_s ∗
            ∃ σ_t σ_s, ⌜Leaf.Leaf (σ_t, v_t) (go e_t)⌝ ∗
                       ⌜Leaf.Leaf (σ_s, v_s) (go e_s)⌝) e_t e_s.
  Proof.
    iSplit.
    { rewrite /lift_post_val.
      iIntros "H".
      iDestruct "H" as (??????) "H".
      subst. repeat iExists _; eauto.
      do 2 (iSplitL ""; [ done | ]). iFrame.
      repeat iExists _; eauto.
      iSplitL ""; iPureIntro; by constructor. }
    { rewrite /lift_post_val.
      iIntros "H".
      iDestruct "H" as (??????) "(H&H')".
      subst. repeat iExists _; eauto. }
  Qed.

  Lemma handle_event_mono {R1 R2} X Y Φ Φ' k k0 e e0 :
    (∀ e_t e_s, Φ e_t e_s -∗ Φ' e_t e_s) -∗
      handle_event (X := X) (Y := Y) Φ k k0 e e0 -∗
      handle_event (R1 := R1) (R2 := R2) Φ' k k0 e e0.
  Proof.
    iIntros "Hmon Hcont".
    destruct e, e0; try done; cbn;
        [ simp handle_call_events | rewrite /handle_E].
    { destruct c, p, c0, p.
      simp handle_call_events.
      iDestruct "Hcont" as "[Hcont | Hcont ]".
      { iDestruct "Hcont" as (?) "(SI & Hev & Hcont)".
        iLeft; iFrame.
        iExists C; iFrame.
        iIntros (??) "H"; iDestruct ("Hcont" with "H") as ">Hcont".
        iModIntro; iApply ("Hmon" with "Hcont"). }
      { iDestruct "Hcont" as (?) "(SI & Hev & Hcont)".
        iRight; iFrame.
        iExists C; iFrame.
        iIntros (??) "H"; iDestruct ("Hcont" with "H") as ">Hcont".
        iModIntro; iApply ("Hmon" with "Hcont"). } }
    { destruct s, s0; [ done.. |].
      destruct s, s0; [ done.. |].
      iDestruct "Hcont" as "[HCEI HCI]". iFrame.
      iIntros (v_t v_s) "ECI".
      iSpecialize ("HCI" with "ECI").
        by iApply "Hmon". }
  Qed.

  Lemma handle_event_bupd_mono {R1 R2} X Y (Φ Φ' : st_expr_rel' R1 R2) k k0 e e0 :
    (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s)%I -∗
      handle_event (X := X) (Y := Y) Φ k k0 e e0 -∗
      handle_event (R1 := R1) (R2 := R2) Φ' k k0 e e0.
  Proof.
    iIntros "Hmon Hcont".
    destruct e, e0; try done; cbn;
        [ simp handle_call_events | rewrite /handle_E].
    { destruct c, p, c0, p.
      simp handle_call_events.

      iDestruct "Hcont" as "[ Hcont | Hcont ]".
      { iDestruct "Hcont" as (?) "(?&?&Hcont)".
        iLeft; iFrame.
        iExists C; iFrame.
        iIntros (??) "H"; iDestruct ("Hcont" with "H") as ">Hcont".
        iApply ("Hmon" with "Hcont"). }
      { iDestruct "Hcont" as (?) "(?&?&Hcont)".
        iRight; iFrame. iExists C; iFrame.
        iIntros (??) "H"; iDestruct ("Hcont" with "H") as ">Hcont".
        iApply ("Hmon" with "Hcont"). } }
    { destruct s, s0; [ done.. |].
      destruct s, s0; [ done.. |].
      iDestruct "Hcont" as "[HCEI HCI]". iFrame.
      iIntros (v_t v_s) "ECI".
      iSpecialize ("HCI" with "ECI"). iMod "HCI".
        by iApply "Hmon". }
  Qed.

  (* Several lemmas about monotonicity of [sim_expr]. *)
  Lemma sim_expr_inner_mono {R1 R2} (l1 l2 g1 g2 : st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2):
    ⊢ □ (∀ Φ e_t e_s, l1 Φ e_t e_s -∗ l2 Φ e_t e_s)
    → □ (∀ Φ e_t e_s, g1 Φ e_t e_s -∗ g2 Φ e_t e_s)
    → ∀ Φ e_t e_s, sim_expr_inner g1 l1 Φ e_t e_s -∗ sim_expr_inner g2 l2 Φ e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ e_t e_s) "Hsim".
    rewrite /sim_expr_inner.
    destruct e_t eqn: He_t; destruct e_s eqn: He_s; try done; cycle 2.
    all : case_simp "Hsim"; provide_case.
    all: try solve [by iApply "Hleast" | by iApply "Hgreatest" ]; try done.
    dependent destruction H3; iApply (handle_event_mono with "Hgreatest Hsim").
  Qed.

  (* the strongest monotonicity lemma we can prove, allows for changing the post
      condition and recursive occurrences *)
  Lemma sim_expr_inner_strong_mono {R1 R2} l1 l2 g1 g2:
    ⊢ □ (∀ Φ Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, l1 Φ e_t e_s -∗ l2 Ψ e_t e_s)
    → □ (∀ Φ Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ ∀ e_t e_s, g1 Φ e_t e_s -∗ g2 Ψ e_t e_s)
    → ∀ Φ Ψ, (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s)
               -∗ ∀ e_t e_s, sim_expr_inner (R1 := R1) (R2 := R2) g1 l1 Φ e_t e_s -∗ sim_expr_inner g2 l2 Ψ e_t e_s.
  Proof.
    iIntros "#Hleast #Hgreatest" (Φ Ψ) "HΦΨ". iIntros (e_t e_s) "Hsim".
    rewrite /sim_expr_inner.
    destruct e_t eqn: He_t; destruct e_s eqn: He_s; try done.
    all : case_simp "Hsim"; provide_case.
    all: try solve [ by iApply ("HΦΨ" with "Hsim")
                    | by iApply ("Hleast" with "HΦΨ")
                    | by iApply ("Hgreatest" with "HΦΨ") ]; try done.
    dependent destruction H3;
      iSpecialize ("Hgreatest" with "HΦΨ");
      iApply (handle_event_mono with "Hgreatest Hsim").
  Qed.

  Instance sim_expr_inner_ne {R1 R2}:
    ∀n, Proper ((dist n ==> dist n) ==>
                (dist n ==> dist n) ==>
                dist n ==> dist n ==> dist n ==> dist n) (sim_expr_inner (R1 := R1) (R2 := R2)).
  Proof.
    intros n G1 G2 HG L1 L2 HL Φ Ψ HΦΨ e_s e_s'
            ->%discrete_iff%leibniz_equiv  e_t e_t' ->%discrete_iff%leibniz_equiv; [ | eapply _..].
    subst;
      rewrite /sim_expr_inner /stutter_l /stutter_r /tau_step /vis_step
              /source_ub /handle_event /handle_E; simp handle_call_events.
    do 5 f_equiv.
    1-3 : repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
    do 15 (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
    2 : repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
    destruct c, c0, p, p0.
    simp handle_call_events.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
  Qed.

  Instance sim_expr_inner_proper {R1 R2}:
    Proper ((equiv ==> equiv) ==>
            (equiv ==> equiv) ==>
            equiv ==> equiv ==> equiv ==> equiv)
           (sim_expr_inner (R1 := R1) (R2 := R2)).
  Proof.
    intros G1 G2 HG L1 L2 HL Φ Ψ HΦΨ e_s e_s'
          ->%leibniz_equiv e_t e_t' ->%leibniz_equiv; [|eapply _..].
    subst;
      rewrite /sim_expr_inner /stutter_l /stutter_r /tau_step /vis_step
              /source_ub /handle_event /handle_E.
    do 5 f_equiv.
    1-3 : repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
    do 15 (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
    2 : repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
    destruct c, c0, p, p0.
    simp handle_call_events.
    repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity).
  Qed.

  Local Instance sim_indF_body_mono {R1 R2}
        (greatest_rec : st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2) :
    (NonExpansive greatest_rec) →
    BiMonoPred
      (λ (least_rec: prodO (prodO ((st_exprO' R1) -d> (st_exprO' R2) -d> PROP) (st_exprO' R1)) (st_exprO' R2) -d> PROP),
                uncurry3 (sim_expr_inner greatest_rec (curry3 least_rec))).
  Proof.
    intros Hg; constructor.
    - intros L1 L2 HL1 HL2. iIntros "#H" (x).
      destruct x as ((Φ & e_t) & e_s); simpl.
      iApply (sim_expr_inner_mono with "[] []"); iModIntro; clear.
      { iIntros (G e_t e_s); unfold curry4; iApply "H". }
      iIntros (G e_t e_s) "$".
    - intros l Hne n x y Heq.
      destruct x as ((Φ & e_t) & e_s); simpl.
      destruct y as ((Ψ & e_t') & e_s'); simpl.
      destruct Heq as [[Heq1 Heq2] Heq3]; simpl in Heq1, Heq2, Heq3.
      eapply sim_expr_inner_ne; eauto.
      + intros ?????. by eapply Hg.
      + intros ?????; rewrite /curry3. eapply Hne.
        repeat split; simpl; done.
  Qed.

  Global Instance sim_indF_ne {R1 R2}:
    NonExpansive3 (sim_indF (R1 := R1) (R2 := R2)).
  Proof.
    rewrite /sim_indF; intros n x y Heq ???????.
    rewrite {1 3}/curry3. apply least_fixpoint_ne; last by repeat split.
    intros ? [[??] ?]; simpl.
    rewrite /sim_expr_inner /stutter_l /stutter_r /tau_step /vis_step
            /source_ub /handle_event /handle_E.
    do 10 f_equiv; [ apply Heq | ].
    do 10 f_equiv.
    2:repeat (f_equiv || apply HΦΨ || eapply HL || eapply HG || reflexivity); apply Heq.
    destruct c, p, c0, p. simp handle_call_events; repeat f_equiv; apply Heq.
  Qed.

  Lemma sim_indF_mono {R1 R2} (R R' : st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2)
    `{NonExpansive R} `{NonExpansive R'}
    Φ e_t e_s:
    <pers> (∀ Φ e_t e_s, R Φ e_t e_s -∗ R' Φ e_t e_s) -∗
    sim_indF R Φ e_t e_s -∗ sim_indF R' Φ e_t e_s.
  Proof.
    iIntros "#Hmon". rewrite /sim_indF {1 3}/curry3.
    iIntros "Hleast".
    iApply (least_fixpoint_ind with "[] Hleast"); clear Φ e_t e_s.
    iModIntro. iIntros ([[Φ e_t] e_s]).
    erewrite least_fixpoint_unfold; last first.
    { eapply sim_indF_body_mono, _. }
    rewrite {1 3}/uncurry3.
    iApply (sim_expr_inner_mono with "[] []").
    { iModIntro. iIntros (G e_t' e_s') "H"; unfold curry3.
      iDestruct "H" as "[$ _]". }

    iModIntro; iIntros (Φ' e_t' e_s'); by iApply "Hmon".
  Qed.

  Lemma sim_indF_unfold {R1 R2} G `{NonExpansive G} Φ e_t e_s:
    sim_indF (R1 := R1) (R2 := R2) G Φ e_t e_s ≡ sim_expr_inner G (sim_indF G) Φ e_t e_s.
  Proof.
    rewrite {1}/sim_indF {1}/curry3 least_fixpoint_unfold {1}/uncurry3 //=.
  Qed.

  Instance sim_coindF_body_mono {R1 R2}:
    BiMonoPred (λ (greatest_rec: prodO (prodO ((st_exprO' R1) -d> (st_exprO' R2) -d> PROP) (st_exprO' R1)) (st_exprO' R2)→ PROP), uncurry3 (sim_indF (curry3 greatest_rec))).
  Proof.
    constructor.
    - intros G1 G2 HG1 HG2. iIntros "#H" (x).
      destruct x as [[Φ e_t] e_s]; rewrite /uncurry3.
      iApply sim_indF_mono.
      { (* FIXME: TC inference should solve this *) solve_proper. }
      { (* FIXME: TC inference should solve this *) solve_proper. }
      iModIntro.
      iIntros (Φ' e_t' e_s'); iApply "H".
    - intros G Hne n x y Heq. rewrite /sim_indF !uncurry3_curry3.
      eapply least_fixpoint_ne'; last done.
      intros L HL m [[Φ e_t] e_s] [[Ψ e_t'] e_s'] Heq'; simpl.
      eapply sim_expr_inner_ne; [| |eapply Heq'..].
      + solve_proper.
      + solve_proper.
  Qed.

  Lemma sim_coindF_unfold {R1 R2} Φ e_t e_s:
    sim_coindF (R1 := R1) (R2 := R2) Φ e_t e_s ≡ sim_indF sim_coindF Φ e_t e_s.
  Proof.
    rewrite {1}/sim_coindF {1}/curry3 greatest_fixpoint_unfold {1}/uncurry3 //=.
  Qed.

  Global Instance sim_coindF_ne {R1 R2} : NonExpansive (sim_coindF (R1 := R1) (R2 := R2)).
  Proof. solve_proper. Qed.

  Global Instance sim_coindF_proper {R1 R2} :
     Proper (equiv ==> equiv ==> equiv ==> equiv) (sim_coindF (R1 := R1) (R2 := R2)).
  Proof.
    intros Φ Ψ Heq e_t e_t' <-%leibniz_equiv e_s e_s' <-%leibniz_equiv.
    revert e_t e_s. change (sim_coindF Φ ≡ sim_coindF Ψ).
    eapply ne_proper; first apply _. done.
  Qed.

  Lemma sim_coindF_fixpoint {R1 R2} Φ e_t e_s:
    sim_coindF (R1 := R1) (R2 := R2) Φ e_t e_s ≡ sim_expr_inner sim_coindF sim_coindF Φ e_t e_s.
  Proof.
    rewrite sim_coindF_unfold sim_indF_unfold.
    eapply sim_expr_inner_proper; eauto.
    - solve_proper.
    - intros Φ' Ψ' Heq. intros ??. rewrite -sim_coindF_unfold.
      f_equiv; done.
  Qed.

  Lemma sim_expr_fixpoint {R1 R2} (Φ: itree (L0 Λ) R1 -> itree (L0 Λ) R2 -> PROP) e_t e_s:
    sim_expr Φ e_t e_s ⊣⊢
    (∀ σ_t σ_s : language.state Λ, state_interp σ_t σ_s ==∗
      sim_coind Φ (⟦η⟨e_t⟩⟧ σ_t) (⟦η⟨e_s⟩⟧ σ_s)).
  Proof.
    rewrite sim_expr_eq; simpl. setoid_rewrite sim_coindF_fixpoint. done.
  Qed.

  Lemma sim_expr_unfold {R1 R2} (Φ: itree (L0 Λ) R1 -> itree (L0 Λ) R2 -> PROP) e_t e_s:
    sim_expr Φ e_t e_s
    ⊣⊢ (∀ σ_t σ_s : language.state Λ,
        state_interp σ_t σ_s ==∗
        ∃ c,
         match c with
         | BASE => lift_expr_rel Φ (observe (⟦ η ⟨ e_t ⟩ ⟧ σ_t)) (observe (⟦ η ⟨ e_s ⟩ ⟧ σ_s))
         | STUTTER_L =>
             stutter_l (sim_indF sim_coindF) (lift_expr_rel Φ) (observe (⟦ η ⟨ e_t ⟩ ⟧ σ_t)) (observe (⟦ η ⟨ e_s ⟩ ⟧ σ_s))
         | STUTTER_R =>
             stutter_r (sim_indF sim_coindF) (lift_expr_rel Φ) (observe (⟦ η ⟨ e_t ⟩ ⟧ σ_t)) (observe (⟦ η ⟨ e_s ⟩ ⟧ σ_s))
         | TAU_STEP => tau_step sim_coindF (lift_expr_rel Φ) (observe (⟦ η ⟨ e_t ⟩ ⟧ σ_t)) (observe (⟦ η ⟨ e_s ⟩ ⟧ σ_s))
         | VIS_STEP => vis_step sim_coindF (lift_expr_rel Φ) (observe (⟦ η ⟨ e_t ⟩ ⟧ σ_t)) (observe (⟦ η ⟨ e_s ⟩ ⟧ σ_s))
         | SOURCE_UB => source_ub (observe (⟦ η ⟨ e_t ⟩ ⟧ σ_t)) (observe (⟦ η ⟨ e_s ⟩ ⟧ σ_s))
         | SOURCE_EXC => source_exc (observe (⟦ η ⟨ e_t ⟩ ⟧ σ_t)) (observe (⟦ η ⟨ e_s ⟩ ⟧ σ_s))
         end).
  Proof.
    rewrite sim_expr_fixpoint /sim_expr_inner //. setoid_rewrite sim_coindF_unfold.
    iSplit; iIntros "HΦ %σ_t %σ_s SI";
      iSpecialize ("HΦ" with "SI"); iMod "HΦ"; by rewrite sim_indF_unfold /sim_expr_inner.
  Qed.

  Global Instance sim_expr_ne {R1 R2} n:
    Proper
    ((pointwise_relation (expr Λ R1) (pointwise_relation (expr Λ R2) (dist n))) ==>
      eq ==>
      eq ==>
      (dist n))
    (sim_expr).
  Proof.
    intros p1 p2 Heq2 e e' -> e1 e1' ->.
    rewrite !sim_expr_eq. unfold sim_expr_. repeat (f_equiv; intro).
    do 2 f_equiv. eapply sim_coindF_ne. repeat intro.
    unfold lift_expr_rel. repeat f_equiv.
  Qed.

  Global Instance sim_expr_proper {R1 R2}:
    Proper ((pointwise_relation (expr Λ R1) (pointwise_relation (expr Λ R2) (≡))) ==> eq ==> eq ==> (≡)) sim_expr.
  Proof.
    intros p1 p2 Heq2 e e' -> e1 e1' ->.
    rewrite !sim_expr_eq. unfold sim_expr_. repeat (f_equiv; intro).
    do 2 f_equiv. eapply sim_coindF_proper; eauto.
    repeat intro. unfold lift_expr_rel. repeat f_equiv.
  Qed.

  Existing Instances sim_indF_body_mono sim_coindF_body_mono.
  (* any post-fixed point is included in the gfp *)

  Lemma sim_expr_inner_base {R1 R2} G L (Φ: st_expr_rel' R1 R2) e_t e_s:
      ⊢ Φ e_t e_s -∗
      sim_expr_inner G L Φ e_t e_s.
  Proof.
    iIntros "He". rewrite /sim_expr.
    rewrite /sim_expr_inner.
    iExists BASE; by iModIntro.
  Qed.

  Lemma sim_coindF_base {R1 R2} (Φ: st_expr_rel' R1 R2) e_t e_s:
    ⊢ Φ e_t e_s -∗
      sim_coindF Φ e_t e_s.
  Proof.
    iIntros "He".
    iApply sim_coindF_fixpoint.
    iApply sim_expr_inner_base; iFrame.
  Qed.

  Lemma sim_expr_base {R1 R2} (Φ: expr_rel R1 R2) v_t v_s:
    ⊢ Φ (Ret v_t) (Ret v_s) -∗
      sim_expr Φ (Ret v_t) (Ret v_s).
  Proof.
    iIntros "He". iApply sim_expr_fixpoint.
    iIntros (σ_t σ_s) "SI".
    rewrite /sim_coind sim_coindF_unfold sim_indF_unfold.
    iApply sim_expr_inner_base; iFrame.

    rewrite /lift_expr_rel.

    iModIntro. iIntros. iExists σ_t, v_t, σ_s, v_s.
    iFrame; eauto.
  Qed.

  Lemma sim_coindF_strong_coind {R1 R2} (F : st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2) :
    NonExpansive F ->
    ⊢ (□ ∀ Φ e_t e_s, F Φ e_t e_s -∗ sim_indF (λ Φ e_t e_s, F Φ e_t e_s ∨ sim_coindF Φ e_t e_s) Φ e_t e_s)
      -∗ ∀ Φ e_t e_s, F Φ e_t e_s -∗ sim_coindF Φ e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (Φ e_t e_s) "HF".
   rewrite /sim_coindF {3}/curry3.
    change (F Φ e_t e_s) with (uncurry3 F (Φ, e_t, e_s)).
    remember (Φ, e_t, e_s) as p eqn:Heqp.
    clear Φ e_t e_s Heqp.
    iApply (greatest_fixpoint_coind _ (uncurry3 F) with "[] HF").
    iModIntro. iIntros ([[Φ e_t] e_s]) "Hf"; simpl.
    iApply ("HPre" $! Φ e_t e_s with "Hf").
  Qed.

  Lemma sim_coindF_coind {R1 R2} (F : st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2) :
    NonExpansive F →
    ⊢ (□ ∀ Φ e_t e_s, F Φ e_t e_s -∗ sim_indF F Φ e_t e_s)
      -∗ ∀ Φ e_t e_s, F Φ e_t e_s -∗ sim_coindF Φ e_t e_s.
  Proof.
    iIntros (Hprop) "#HPre". iIntros (Φ e_t e_s) "HF".
    iApply (sim_coindF_strong_coind with "[] HF"); clear Φ e_t e_s.
    iModIntro; iIntros (Φ e_t e_s) "HF".
    iDestruct ("HPre" with "HF") as "HF". rewrite /sim_coindF.
    iApply (sim_indF_mono with "[] HF"); first by solve_proper.
    iModIntro. clear Φ e_t e_s. iIntros (Φ e_t e_s) "HF". by iLeft.
  Qed.

  Lemma sim_indF_strong_ind {R1 R2} (F R: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2):
    NonExpansive F ->
    NonExpansive R ->
    ⊢ (□ ∀ Φ e_t e_s, sim_expr_inner R (λ Ψ e_t e_s, F Ψ e_t e_s ∧ sim_indF R Ψ e_t e_s) Φ e_t e_s -∗ F Φ e_t e_s)
      -∗ ∀ Φ e_t e_s, sim_indF R Φ e_t e_s -∗ F Φ e_t e_s.
  Proof.
    iIntros (Hne1 Hne2) "#HPre". iIntros (Φ e_t e_s) "HF".
    rewrite {2}/sim_indF {1}/curry3.
    change (F Φ e_t e_s) with (uncurry3 F (Φ, e_t, e_s)).
    remember (Φ, e_t, e_s) as p eqn:Heqp. clear Φ e_t e_s Heqp.
    iApply (least_fixpoint_ind _ (uncurry3 F) with "[] HF").
    iModIntro. iIntros ([[Φ e_t] e_s]); simpl.
    rewrite {1}/curry3 {1}/uncurry3.
    iIntros "H". iApply "HPre". iExact "H".
  Qed.

  Lemma sim_indF_ind {R1 R2} (F R: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2):
    NonExpansive R →
    NonExpansive F →
    ⊢ (□ ∀ Φ e_t e_s, sim_expr_inner R F Φ e_t e_s -∗ F Φ e_t e_s)
      -∗ ∀ Φ e_t e_s, sim_indF R Φ e_t e_s -∗ F Φ e_t e_s.
  Proof.
    iIntros (Hne1 Hne2) "#HPre". iApply sim_indF_strong_ind.
    iModIntro. iIntros (Φ e_t e_s) "Hsim".
    iApply "HPre". iApply (sim_expr_inner_mono with "[] [] Hsim"); last by auto.
    iModIntro. iIntros (Φ' e_t' e_s') "H". iApply bi.and_elim_l. iApply "H".
  Qed.

  (* we change the predicate beause at every recursive occurrence, *)
  (*      we give back ownership of the monotonicity assumption *)
  Lemma sim_indF_strong_mono {R1 R2} (rec : st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2) Φ Φ' e_t e_s:
    NonExpansive rec →
     (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗
     sim_indF rec Φ e_t e_s -∗
     sim_indF (λ Ψ e_t e_s, rec Φ e_t e_s ∗ (∀ e_t e_s, Φ e_t e_s ==∗ Ψ e_t e_s) ∨ rec Ψ e_t e_s) Φ' e_t e_s.
  Proof.
    iIntros (Hne) "Hmon Hleast". iRevert (Φ') "Hmon".
    pose (rec' := (
      (λ Φ (Ψ : st_exprO' R1 -d> st_exprO' R2 -d> PROP) (e_t0 : st_exprO' R1) (e_s0 : st_exprO' R2),
         rec Φ e_t0 e_s0 ∗ (∀ (e_t1 : st_exprO' R1) (e_s1 : st_exprO' R2), Φ e_t1 e_s1 ==∗ Ψ e_t1 e_s1) ∨ rec Ψ e_t0 e_s0))%I).
    pose (F_ind := (λ Φ e_t e_s, ∀ Φ', (∀ (e_t : st_expr' Λ R1) (e_s : st_expr' Λ R2), Φ e_t e_s ==∗ Φ' e_t e_s) -∗
                                            sim_indF (rec' Φ) Φ' e_t e_s)%I).
    assert (NonExpansive2 (rec': st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2)) as Rne.
    { intros m ??? Φ' Φ'' Heq1 Ψ Ψ'. rewrite /rec'.
      solve_proper_core ltac:(fun x => f_equiv || apply Heq1 || apply Heq2 || apply H). }
    assert (NonExpansive (F_ind: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2)).
    { clear Φ e_t e_s.
      intros n Φ Ψ Heq e_s e_s'.
      rewrite /F_ind; do 3 f_equiv; first (repeat f_equiv; by apply Heq).
      eapply sim_indF_ne; [ |done..]. intros ?. repeat intro. eapply Rne; eauto. }

    iApply (sim_indF_ind F_ind rec with "[] Hleast"); clear e_t e_s.
    iModIntro. iIntros (Φ' e_t e_s) "Hrec". iIntros (Ψ') "Hmon".
    setoid_rewrite sim_indF_unfold; [ |typeclasses eauto].
    rewrite /sim_expr_inner.
    case_simp "Hrec";
      try (iSpecialize ("Hmon" with "Hrec"); iMod "Hmon");
      try iSpecialize ("Hrec" with "Hmon"); provide_case; try done.
    2: iApply (handle_event_mono with "[Hmon]"); [ | done]; iIntros (e_t' e_s') "Hr".
    all : iLeft; iFrame.
  Qed.

  Lemma sim_indF_post_mono {R1 R2} (rec : st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2) Φ Φ' e_t e_s:
     NonExpansive rec ->
     <pers> (∀ Φ Φ', (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗
        ∀ e_t e_s, rec Φ e_t e_s -∗ rec Φ' e_t e_s) -∗
     (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗
     sim_indF rec Φ e_t e_s -∗
     sim_indF rec Φ' e_t e_s.
  Proof.
    iIntros (Hne) "#Hne Hmon Hleast".
    pose (rec' := (
      (λ Φ (Ψ : st_exprO' R1 -d> st_exprO' R2 -d> PROP) (e_t0 : st_exprO' R1) (e_s0 : st_exprO' R2),
         rec Φ e_t0 e_s0 ∗ (∀ (e_t1 : st_exprO' R1) (e_s1 : st_exprO' R2), Φ e_t1 e_s1 ==∗ Ψ e_t1 e_s1) ∨ rec Ψ e_t0 e_s0))%I).
    pose (F_ind := (λ Φ e_t e_s, ∀ Φ', (∀ (e_t : st_expr' Λ R1) (e_s : st_expr' Λ R2), Φ e_t e_s ==∗ Φ' e_t e_s) -∗
                                            sim_indF rec Φ' e_t e_s)%I).
    assert (NonExpansive2 (rec': st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2)) as Rne.
    { intros m ??? Φ1 Φ2 Heq1 Ψ Ψ'. rewrite /rec'.
      solve_proper_core ltac:(fun x => f_equiv || apply Heq1 || apply Heq2 || apply H). }
    assert (NonExpansive (F_ind: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2)).
    { clear Φ e_t e_s.
      intros n Φ Ψ Heq e_s e_s'.
      rewrite /F_ind; do 3 f_equiv; first (repeat f_equiv; by apply Heq). }

    iApply (sim_indF_ind F_ind rec with "[] Hleast"); clear e_t e_s; [ | done].
    iModIntro. iIntros (Φ1 e_t e_s) "Hrec". iIntros (Ψ') "Hmon".
    setoid_rewrite sim_indF_unfold; [ |typeclasses eauto].
    rewrite /sim_expr_inner.
    case_simp "Hrec";
      try (iSpecialize ("Hmon" with "Hrec"); iMod "Hmon");
      try iSpecialize ("Hrec" with "Hmon"); provide_case; try done.
    2: iApply (handle_event_mono with "[Hmon]"); [ | done]; iIntros (e_t' e_s') "Hr".
    { iApply ("Hne" with "Hmon Hrec"). }
    { iApply ("Hne" with "Hmon Hr"). }
  Qed.

  Lemma sim_coindF_bupd_mono R1 R2 (Φ : st_expr_rel' R1 R2) Φ' e_t e_s:
    (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗
      sim_coindF Φ e_t e_s -∗ sim_coindF Φ' e_t e_s.
  Proof.
    iIntros "Ha Hmon".
    iApply (sim_coindF_strong_coind (λ Ψ e_t e_s, sim_coindF Φ e_t e_s ∗ (∀ (e_t : st_expr' Λ R1) (e_s : st_expr' Λ R2), Φ e_t e_s ==∗ Ψ e_t e_s))%I); last by iFrame.
    { repeat intro. repeat f_equiv; eauto. }
    iModIntro. clear Φ' e_t e_s. iIntros (Φ' e_t e_s) "[Ha Hmon]".
    rewrite sim_coindF_unfold.
    iApply (sim_indF_strong_mono with "Hmon Ha").
  Qed.

  Lemma lift_expr_rel_mono {R1 R2} (Φ: expr_rel R1 R2) Φ' e_t e_s:
    (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗
    lift_expr_rel Φ e_t e_s ==∗
    lift_expr_rel Φ' e_t e_s.
  Proof.
    iIntros "Ha Hmon".
    rewrite /lift_expr_rel.
    iDestruct "Hmon" as (σ_t v_t σ_s v_s) "[%H [%H' [SI HΦ]]]".
    iSpecialize ("Ha" with "HΦ"); iMod "Ha".
    iModIntro.
    iExists σ_t, v_t, σ_s, v_s.
    iFrame. done.
  Qed.

  Lemma sim_expr_bupd_mono {R1 R2} (Φ:expr_rel R1 R2) Φ' e_t e_s:
    (∀ e_t e_s, Φ e_t e_s ==∗ Φ' e_t e_s) -∗
    e_t ⪯ e_s [{ Φ }] -∗ e_t ⪯ e_s [{ Φ' }].
  Proof.
    iIntros "Ha Hmon". rewrite sim_expr_eq; simpl.
    iIntros (σ_t σ_s) "SI".
    iSpecialize ("Hmon" with "SI").
    iApply (sim_coindF_bupd_mono with "[Ha]"); [ | done].
    iIntros (e_t' e_s') "HΦ".
    iApply (lift_expr_rel_mono with "Ha HΦ").
  Qed.

  Lemma sim_expr_bupd {R1 R2} (Φ:expr_rel R1 R2) e_t e_s:
    (e_t ⪯ e_s [{ λ e_t' e_s', |==> Φ e_t' e_s' }]) -∗ e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "H". iApply (sim_expr_bupd_mono with "[] H").
    iIntros (??) "$".
  Qed.

  Lemma sim_expr_mono {R1 R2} (Φ:expr_rel R1 R2) Φ' e_t e_s:
    (∀ e_t e_s, Φ e_t e_s -∗ Φ' e_t e_s) -∗ e_t ⪯ e_s [{ Φ }] -∗ e_t ⪯ e_s [{ Φ' }].
  Proof.
    iIntros "Hmon Ha". iApply (sim_expr_bupd_mono with "[Hmon] Ha").
    iIntros (??) "?". iModIntro. by iApply "Hmon".
  Qed.

  Lemma sim_expr_leaf' {R1 R2} (Q : expr_rel R1 R2) et es:
    sim_expr (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q e_t e_s)%I) et es ⊣⊢
    sim_expr (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q e_t e_s ∗
                              ⌜Leaf.Leaf x e_t⌝ ∗ ⌜Leaf.Leaf y e_s⌝)) et es.
  Proof.
    iSplit.
    { iIntros "H"; iApply sim_expr_mono; [ | done].
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "HQ".
      iExists _, _; iFrame. rewrite H H0.
      repeat (iSplitL ""; [ iPureIntro; done | ]).
      iSplitL ""; iPureIntro; by constructor. }
    { iIntros "H"; iApply sim_expr_mono; [ | done].
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "(HQ & %H1 & %H2)".
      iExists _, _; iFrame. rewrite H H0.
      repeat (iSplitL ""; [ iPureIntro; done | ]).
      iPureIntro; done. }
  Qed.

  Local Definition tau_invR_pred {R1 R2} :=
    λ (Φ:st_exprO' R1 -d> st_exprO' R2 -d> PROP)
      (e_t: st_expr' Λ R1) (e_s: st_expr' Λ R2),
      ((∀ e_t e_s, Φ e_t (TauF e_s) -∗ Φ e_t (observe e_s)) -∗
        ∀ (e_s' : itree (L2 Λ) (language.state Λ * _)),
         ⌜e_s = TauF e_s'⌝ -∗
          sim_coindF Φ e_t (observe e_s'))%I.

  Local Instance tau_invR_pred_ne {R1 R2}:
    NonExpansive (tau_invR_pred: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv. repeat intro.
    destruct x0, x1; cbn; f_equiv; auto.
  Qed.

  Lemma sim_indF_tau_invR {R1 R2} Φ e_t e_s:
    (∀ e_t e_s, Φ e_t (TauF e_s) -∗ Φ e_t (observe e_s)) -∗
    sim_coindF Φ e_t (TauF e_s) -∗
    sim_coindF (R1 := R1) (R2 := R2) Φ e_t (observe e_s).
  Proof.
    iIntros "HΦ H".

    rewrite sim_coindF_unfold.
    iPoseProof (sim_indF_strong_ind tau_invR_pred with "[] H") as "H"; cycle 1.
    { rewrite /tau_invR_pred; iFrame.
      by iApply ("H" with "HΦ"). }

    iModIntro. clear Φ e_t e_s.
    iIntros (Φ e_t e_s) "IH".
    rewrite {1}/tau_invR_pred.
    rewrite /tau_invR_pred.
    iIntros "H" (??). subst.

    rewrite !sim_coindF_unfold !sim_indF_unfold /sim_expr_inner.
    iMod "IH".
    iDestruct "IH" as (?) "IH".
    destruct c eqn: Hc; try solve case_solve.
    { provide_case: BASE. iApply ("H" with "IH"). }
    { case_solve. iDestruct "IH" as "(IH & _)".
      iSpecialize ("IH" with "H").
      iSpecialize ("IH" $! _ eq_refl).
      provide_case: STUTTER_L.
      by rewrite !sim_coindF_unfold. }
    { case_solve. iDestruct "IH" as "(_ & IH)".
      by rewrite !sim_indF_unfold /sim_expr_inner. }
    { case_solve. provide_case: STUTTER_L;
      by rewrite !sim_coindF_unfold. }
  Qed.

  Local Definition tau_invL_pred {R1 R2} :=
    λ (Φ:st_exprO' R1 -d> st_exprO' R2 -d> PROP)
      (e_t: st_expr' Λ R1) (e_s: st_expr' Λ R2),
      ((∀ e_t e_s, Φ (TauF e_t) e_s -∗ Φ (observe e_t) e_s) -∗
        ∀ (e_t' : itree (L2 Λ) (language.state Λ * _)),
         ⌜e_t = TauF e_t'⌝ -∗
          sim_coindF Φ (observe e_t') e_s)%I.

  Local Instance tau_invL_pred_ne {R1 R2}:
    NonExpansive (tau_invL_pred: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv. repeat intro.
    destruct x0, x1; cbn; f_equiv; auto.
  Qed.

  Lemma sim_indF_tau_invL {R1 R2} Φ e_t e_s:
    (∀ e_t e_s, Φ (TauF e_t) e_s -∗ Φ (observe e_t) e_s) -∗
    sim_coindF Φ (TauF e_t) e_s -∗
    sim_coindF (R1 := R1) (R2 := R2) Φ (observe e_t) e_s.
  Proof.
    iIntros "HΦ H".

    rewrite sim_coindF_unfold.
    iPoseProof (sim_indF_strong_ind tau_invL_pred with "[] H") as "H"; cycle 1.
    { rewrite /tau_invL_pred; iFrame.
      by iApply ("H" with "HΦ"). }

    iModIntro. clear Φ e_t e_s.
    iIntros (Φ e_t e_s) "IH".
    rewrite {2}/tau_invL_pred.
    iIntros "H" (??). subst.

    rewrite !sim_coindF_unfold !sim_indF_unfold /sim_expr_inner.
    iMod "IH".
    iDestruct "IH" as (?) "IH".
    destruct c eqn: Hc; try solve case_solve.
    { provide_case: BASE. iApply ("H" with "IH"). }
    { case_solve. iDestruct "IH" as "(_ & IH)".
      by rewrite !sim_indF_unfold /sim_expr_inner. }
    { case_solve. iDestruct "IH" as "(IH & _)".
      iSpecialize ("IH" with "H").
      iSpecialize ("IH" $! _ eq_refl).
      provide_case: STUTTER_R.
      by rewrite !sim_coindF_unfold. }
    { case_solve. provide_case: STUTTER_R;
      by rewrite !sim_coindF_unfold. }
    { case_solve. inversion Heq.
      by provide_case: SOURCE_UB. }
    { case_solve. inversion Heq.
      by provide_case: SOURCE_EXC. }
  Qed.

  (* WTS: This bind principle is morally equiexprent to [eutt_clo_bind], the bind
   cut rule from the ITree library. *)
  Local Definition bind_coind_pred {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
      (∃ X1 X2 (e_t' : itree (L2 Λ) (language.state Λ * X1)) k_t
         (e_s' : itree (L2 Λ) (language.state Λ * X2)) k_s,
          ⌜e_t = observe (ITree.bind e_t' k_t)⌝ ∗ ⌜e_s = observe (ITree.bind e_s' k_s)⌝ ∗
      (sim_coindF (fun e_t'' e_s'' =>
          sim_coindF Φ
            (observe (ITree.bind (go e_t'') k_t))
            (observe (ITree.bind (go e_s'') k_s))) (observe e_t') (observe e_s')))%I.

  Local Definition bind_coind_rec {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
      ((∃ X1 X2 (e_t' : itree (L2 Λ) (language.state Λ * X1)) k_t
          (e_s' : itree (L2 Λ) (language.state Λ * X2)) k_s,
           ⌜e_t = observe (ITree.bind e_t' k_t)⌝ ∗ ⌜e_s = observe (ITree.bind e_s' k_s)⌝ ∗
        (sim_coindF (fun e_t'' e_s'' =>
          sim_coindF Φ (observe (ITree.bind (go e_t'') k_t))
            (observe (ITree.bind (go e_s'') k_s))) (observe e_t') (observe e_s')))%I
        ∨ sim_coindF Φ e_t e_s)%I.

  Local Instance bind_coind_pred_ne {R1 R2}:
    NonExpansive (bind_coind_pred: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv. repeat intro.
    destruct x0, x1; cbn; f_equiv; auto.
  Qed.

  Local Instance bind_coind_rec_ne {R1 R2}:
    NonExpansive (bind_coind_rec: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv. 2 : auto. repeat intro.
    destruct x0, x1; cbn; f_equiv; auto.
  Qed.

  Lemma handle_event_bind_coind {R1 R2} X Y Φ k k0 e e0 :
    handle_event (X := X) (Y := Y) (sim_coindF Φ) k k0 e e0 -∗
      handle_event (R1 := R1) (R2 := R2) (bind_coind_rec Φ) k k0 e e0.
  Proof.
    iApply handle_event_mono.
    iIntros (e_t e_s) "Hmon"; by iRight.
  Qed.

  Lemma sim_indF_bind_coind {R1 R2} Φ e_t e_s :
    sim_indF (R1 := R1) (R2 := R2) sim_coindF Φ e_t e_s -∗ sim_indF bind_coind_rec Φ e_t e_s.
  Proof.
    iIntros "Hcont"; iApply (sim_indF_mono with "[] Hcont");
      clear; iModIntro; iIntros (Φ' e_t e_s) "Hrec"; iRight;
        by rewrite /sim_expr_inner.
  Qed.

  Lemma sim_coindF_coind_bind {R1 R2 Re1 Re2} (Φ : st_expr_rel' R1 R2) (e_t: L2_expr Λ Re1) (e_s: L2_expr Λ Re2) k_t k_s:
    sim_coindF (fun e_t'' e_s'' => sim_coindF Φ (observe (ITree.bind (go e_t'') k_t)) (observe (ITree.bind (go e_s'') k_s))) (observe e_t) (observe e_s) -∗
    sim_coindF Φ (observe (ITree.bind e_t k_t)) (observe (ITree.bind e_s k_s)).
  Proof.
    iIntros "Hpre".

    iApply (sim_coindF_strong_coind bind_coind_pred); last first.
    {  rewrite /bind_coind_pred. iExists _, _, e_t, k_t, e_s, k_s. iFrame.
       iSplit; done. }
    iModIntro. clear Φ e_t e_s k_t k_s.
    iIntros (Φ e_t e_s) "IH".

    change (sim_indF _ Φ e_t e_s) with (sim_indF bind_coind_rec Φ e_t e_s).
    rewrite /bind_coind_pred.
    iDestruct "IH" as (X1 X2 e_tp k_t e_sp k_s) "[%Eqt [%Eqs H]]". subst.

    rewrite {1}sim_coindF_unfold.
    rename e_tp into e_t; rename e_sp into e_s.
    (* We introduce a functor [F] that, when it takes as premise the [sim_indF]
       information about the prefix, and as argument the [sim_coindF] of the bind,
       it holds. *)
    pose (F := (λ Ψ e_t e_s,
                ∀ Φ,
                  (∀ e_t' e_s', Ψ e_t' e_s' -∗
                    sim_coindF Φ (observe (ITree.bind (go e_t') k_t)) (observe (ITree.bind (go e_s') k_s))) -∗
                sim_indF bind_coind_rec Φ (observe (ITree.bind (go e_t) k_t)) (observe (ITree.bind (go e_s) k_s)))%I).
    (* Assertion [Ω] *)
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗ F Ψ e_t e_s)%I as "Hgen"; last first.
    { iApply ("Hgen" with "H"). iIntros (??) "$". }
    (* Now we prove the assertion [Ω]. *)
    clear Φ e_t e_s.
    iIntros (Ψ e_t e_s) "Hsim".
    iApply (sim_indF_ind with "[] Hsim"); clear Ψ e_t e_s.
    { solve_proper_prepare. clear -H. repeat f_equiv. }

    iModIntro. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (Φ) "Hcont".

    (* [Hinner] for the "inner" expression, i.e. [e_s] *)
    rewrite /sim_expr_inner.
    cbn -[F] in *. unfold observe.

    rewrite sim_indF_unfold /sim_expr_inner.
    iMod "Hinner"; iDestruct "Hinner" as ( c ) "Hinner";
      destruct c; try case_solve; try done.

    { (* [BASE] case *)
      iSpecialize ("Hcont" with "Hinner"). rewrite sim_coindF_unfold.
      iPoseProof (sim_indF_bind_coind with "Hcont") as "HΦ".
      by rewrite sim_indF_unfold /sim_expr_inner. }

    { (* [STUTTER_L] case*)
      iSpecialize ("Hinner" with "Hcont"); subst.
      provide_case: STUTTER_L; cbn; by repeat (iSplitL ""; [ done | ]). }

    { (* [STUTTER_R] case*)
      iSpecialize ("Hinner" with "Hcont"); subst.
      provide_case: STUTTER_R; cbn; by repeat (iSplitL ""; [ done | ]). }

    { (* [TAU_STEP] case *)
      subst; provide_case: TAU_STEP; cbn; repeat (iSplitL ""; [ done | ]).
      iLeft. repeat iExists _.
      iSplitR; [done | iSplitR; [done |]].
      iApply (sim_coindF_bupd_mono with "[Hcont] Hinner").
      iIntros (e_t' e_s') "HΨ"; iModIntro; by iSpecialize ("Hcont" with "HΨ"). }

    { (* [VIS_STEP] case *)
      subst; provide_case: VIS_STEP; cbn; repeat (iSplitL ""; [ done | ]).
      destruct et eqn: Het, es eqn: Hes; cbn;
        rewrite /handle_E; try done;
        [destruct c, p, c0, p; simp handle_call_events | destruct s, s0; [ done ..|]].
      { iDestruct "Hinner" as "[Hinner | Hinner ]";
          [ iLeft | iRight];
          iDestruct "Hinner" as (?) "(SI & Hcall & Hinner)"; iExists _; iFrame ;
          iFrame;
          iIntros (v_t v_s) "ECI"; iSpecialize ("Hinner" with "ECI"); iLeft;
          repeat iExists _; iMod "Hinner"; iModIntro.
          all : iSplitR; [done | iSplitR; [done |]];
          iApply (sim_coindF_bupd_mono with "[Hcont] Hinner");
          iIntros (e_t' e_s') "HΨ"; iModIntro;
              iSpecialize ("Hcont" with "HΨ"); done. }

      { destruct s, s0; try iDestruct "Hinner" as "%Hinner"; try done.
        iDestruct "Hinner" as "[HCI Hinner]".
        unfold handle_E. iFrame. iIntros (v_t v_s) "EI". iSpecialize ("Hinner" with "EI").
        iFrame; iLeft.
        repeat iExists _. iMod "Hinner"; iModIntro.
        iSplitR; [done | iSplitR; [done |]];
          iApply (sim_coindF_bupd_mono with "[Hcont] Hinner");
        iIntros (e_t' e_s') "HΨ"; iModIntro;
          iSpecialize ("Hcont" with "HΨ"); destruct e_t', e_s'; done. } }

    { (* [SOURCE_UB] case *)
      subst; provide_case: SOURCE_UB; inv Heq; by cbn. }
    { (* [SOURCE_UB] case *)
      subst; provide_case: SOURCE_EXC; inv Heq; by cbn. }
  Qed.

  Local Definition eqitree_pred {R1 R2} :=
      fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
        (∃ e_t' e_s', ⌜go e_t ≅ go e_t'⌝ ∗ ⌜go e_s ≅ go e_s'⌝ ∗
                      sim_coindF (fun e_t'' e_s'' => ∀ e_t''' e_s''', ⌜go e_t''' ≅ go e_t''⌝ -∗ ⌜go e_s''' ≅ go e_s''⌝ -∗ Φ e_t''' e_s''') e_t' e_s')%I.

  Local Definition eqitree_rec {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
      ((∃ e_t' e_s', ⌜go e_t ≅ go e_t'⌝ ∗ ⌜go e_s ≅ go e_s'⌝ ∗
                      sim_coindF (fun e_t'' e_s'' => ∀ e_t''' e_s''', ⌜go e_t''' ≅ go e_t''⌝ -∗ ⌜go e_s''' ≅ go e_s''⌝ -∗ Φ e_t''' e_s''') e_t' e_s')%I
       ∨ sim_coindF Φ e_t e_s)%I.

  Local Instance eqitree_pred_ne {R1 R2}: NonExpansive (eqitree_pred: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv. repeat intro. repeat f_equiv.
  Qed.

  Local Instance eqitree_rec_ne {R1 R2}: NonExpansive (eqitree_rec: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv; eauto. repeat intro. repeat f_equiv.
  Qed.

  Instance sim_coindF_entails {R1 R2} :
    Proper (((fun x y => eq_itree eq (go x) (go y)) ==> (fun x y => eq_itree eq (go x) (go y)) ==> equiv) ==> eq_itree eq ==> eq_itree eq ==> bi_entails)
           (fun Φ e_t e_s => sim_coindF (si := si) (R1 := R1) (R2 := R2) Φ (observe e_t) (observe e_s)).
  Proof.
    intros Φ Φ' HΦ e_t e_t' Ht e_s e_s' Hs.
    iIntros "HΦ".
    - iApply (sim_coindF_strong_coind eqitree_pred); last first.
      {  rewrite /eqitree_pred. iExists (observe e_t), (observe e_s).
         iSplit.
         { iPureIntro. symmetry. rewrite <- !itree_eta. apply Ht. }
         iSplit.
         { iPureIntro. symmetry. rewrite <- !itree_eta. apply Hs. }
         iApply sim_coindF_bupd_mono; [ | done].
         clear e_t e_t' Ht e_s e_s' Hs.
         iIntros (e_t e_s) "HΦ'".
         iModIntro. iIntros (e_t' e_s') "%Ht %Hs".
         symmetry in Ht; symmetry in Hs.
         iApply HΦ; eauto. }
      iModIntro.
      iIntros (Ψ t s) "IH".

      change (sim_indF _ Ψ t s) with (sim_indF eqitree_rec Ψ t s).
      rewrite /eqitree_pred.
      iDestruct "IH" as (e_tp e_sp) "[%Eqt [%Eqs H]]".

      rewrite {1}sim_coindF_unfold.
      (* We introduce a functor [F] that, when it takes as premise the [sim_indF]
        information about the prefix, and as argument the [sim_coindF] of the bind,
        it holds. *)
      pose (F := (λ Ψ e_t e_s,
        ∀ Φ e_t'' e_s'',
          ⌜go e_t'' ≅ go e_t⌝ -∗ ⌜go e_s'' ≅ go e_s⌝ -∗
           (∀ e_t' e_s', Ψ e_t' e_s' -∗
                  ∀ e_t'' e_s'', ⌜go e_t'' ≅ go e_t'⌝ -∗ ⌜go e_s'' ≅ go e_s'⌝ -∗ Φ e_t'' e_s'') -∗
          sim_indF (R1 := R1) (R2 := R2) eqitree_rec Φ e_t'' e_s'')%I).
      (* Assertion [Ω] *)
      iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗ F Ψ e_t e_s)%I as "Hgen"; last first.
      { iApply ("Hgen" with "H"); try done.
        iIntros (e_t'' e_s'') "H". iIntros (e_t''' e_s''') "Ht Hs".
        by iSpecialize ("H" with "Ht Hs"). }

      clear Φ Φ' HΦ e_t e_s Ht Hs e_tp e_sp Eqt Eqs t s Ψ e_t' e_s'.
      iIntros (Ψ e_t e_s) "Hsim".

      iApply (sim_indF_ind with "[] Hsim"); clear Ψ e_t e_s.
      { solve_proper_prepare. clear -H. repeat f_equiv. }

      iModIntro. iIntros (Ψ e_t e_s) "Hinner".
      iIntros (Φ e_t' e_s') "%Ht %Hs Hcont".

      (* [Hinner] for the "inner" expression, i.e. [e_s] *)
      rewrite /sim_expr_inner.
      cbn -[F] in *. unfold observe.

      rewrite sim_indF_unfold /sim_expr_inner.
      iMod "Hinner"; iDestruct "Hinner" as ( c ) "Hinner";
        destruct c; try case_solve; try done.

      { (* [BASE] case *)
        iSpecialize ("Hcont" with "Hinner").
        iSpecialize ("Hcont" $! _ _ Ht Hs).
        by provide_case: BASE. }

      { (* [STUTTER_L] case *)
        subst; destruct e_t'; apply eqit_inv in Ht; cbn in Ht; try contradiction.
        iSpecialize ("Hinner" $! Φ (observe t0) e_s'); cbn.
        do 2 rewrite <- itree_eta.
        iSpecialize ("Hinner" $! Ht Hs with "Hcont").
        by provide_case: STUTTER_L. }

      { (* [STUTTER_R] case *)
        subst; destruct e_s'; apply eqit_inv in Hs; cbn in Hs; try contradiction.
        iSpecialize ("Hinner" $! Φ e_t' (observe t0)); cbn.
        do 2 rewrite <- itree_eta.
        iSpecialize ("Hinner" $! Ht Hs with "Hcont").
        by provide_case: STUTTER_R. }

      { (* [TAU_STEP] case *)
        subst.
        destruct e_t'; apply eqit_inv in Ht; cbn in Ht; try contradiction.
        destruct e_s'; apply eqit_inv in Hs; cbn in Hs; try contradiction.
        provide_case: TAU_STEP; cbn; repeat (iSplitL ""; [ done | ]).
        iLeft. repeat iExists _.
        iSplitR; [ | iSplitR ]; last first.
        { iApply (sim_coindF_bupd_mono with "[Hcont] Hinner").
          iIntros (e_t' e_s') "HΨ"; iModIntro; by iSpecialize ("Hcont" with "HΨ"). }
        all : by do 2 rewrite <- itree_eta. }

      { (* [VIS_STEP] case *)
        subst.
        destruct e_t'; apply eqit_inv in Ht; cbn in Ht; try contradiction.
        destruct e_s'; apply eqit_inv in Hs; cbn in Hs; try contradiction.
        provide_case: VIS_STEP; cbn; repeat (iSplitL ""; [ done | ]).
        destruct Ht as (?&?&?); destruct Hs as (?&?&?).
        dependent destruction x; dependent destruction x0.
        cbn in H, H0, H1, H2; subst.
        destruct et eqn: Het, es eqn: Hes; cbn;
          rewrite /handle_E; try done;
          [destruct c, p, c0, p; simp handle_call_events | destruct s, s0; [ done ..|]]; subst.
        { iDestruct "Hinner" as "[ Hinner | Hinner ]";
            [iLeft | iRight];
              iDestruct "Hinner" as (?) "(SI & Hcall & Hinner)"; iExists _;  iFrame;
          iIntros (v_t v_s) "ECI"; iSpecialize ("Hinner" with "ECI"); iLeft;
          repeat iExists _; iMod "Hinner"; iModIntro.
          all : iSplitR; [ | iSplitR]; last first.
          1,4: iApply (sim_coindF_bupd_mono with "[Hcont] Hinner");
            iIntros (e_t' e_s') "HΨ"; iModIntro;
                iSpecialize ("Hcont" with "HΨ"); done.
          all: do 2 rewrite <- itree_eta; iPureIntro; solve [eapply H0 | eapply H2]. }
        { destruct s, s0; try iDestruct "Hinner" as "%Hinner"; try done.
          iDestruct "Hinner" as "[HCI Hinner]".
          unfold handle_E. iFrame. iIntros (v_t v_s) "EI". iSpecialize ("Hinner" with "EI").
          iFrame; iLeft.
          repeat iExists _. iMod "Hinner"; iModIntro.
          iSplitR; [| iSplitR]; last first.
          { iApply (sim_coindF_bupd_mono with "[Hcont] Hinner");
            iIntros (e_t' e_s') "HΨ"; iModIntro;
              iSpecialize ("Hcont" with "HΨ"); destruct e_t', e_s'; done. }
          all: do 2 rewrite <- itree_eta; iPureIntro; solve [eapply H0 | eapply H2]. } }

      { (* [SOURCE_UB] case *)
        rewrite Heq in Hs.
        subst; destruct e_s'; apply eqit_inv in Hs; cbn in Hs; try contradiction.
        destruct Hs as (?&?&?).
        dependent destruction x. cbn in H, H0.
        subst; provide_case: SOURCE_UB; by cbn. }

      { (* [SOURCE_EXC] case *)
        rewrite Heq in Hs.
        subst; destruct e_s'; apply eqit_inv in Hs; cbn in Hs; try contradiction.
        destruct Hs as (?&?&?).
        dependent destruction x. cbn in H, H0.
        subst; provide_case: SOURCE_EXC; by cbn. }
  Qed.

  Instance sim_coindF_Proper {R1 R2} :
    Proper (((fun x y => eq_itree eq (go x) (go y)) ==> (fun x y => eq_itree eq (go x) (go y)) ==> equiv) ==> eq_itree eq ==> eq_itree eq ==> equiv)
           (fun Φ e_t e_s => sim_coindF (si := si) (R1 := R1) (R2 := R2) Φ (observe e_t) (observe e_s)).
  Proof.
    intros Φ Φ' HΦ e_t e_t' Ht e_s e_s' Hs.
    iSplit; iApply sim_coindF_entails; try done.
    repeat intro. symmetry. eapply HΦ; try done; by symmetry.
  Qed.

  Instance lift_expr_rel_Proper {R1 R2}:
    Proper ((eq_itree eq ==> eq_itree eq ==> equiv) ==>
                (fun x y => eq_itree eq (go x) (go y)) ==>
                (fun x y => eq_itree eq (go x) (go y)) ==> equiv)
           (lift_expr_rel (R1 := R1) (R2 := R2)).
  Proof.
    repeat intro. unfold lift_expr_rel.
    iSplit; iIntros "SI".
    - iDestruct "SI" as (σ_t v_t σ_s v_s) "[%Hr1 [%Hr2 [SI Hx]]]".
      iExists σ_t, v_t, σ_s, v_s; iFrame.
      iSplitL ""; [ iPureIntro; setoid_rewrite <- H0; auto | ].
      iSplitL ""; [ iPureIntro; setoid_rewrite <- H1; auto | ].
      iApply H; eauto; reflexivity.
    - iDestruct "SI" as (σ_t v_t σ_s v_s) "[%Hr1 [%Hr2 [SI Hx]]]".
      iExists σ_t, v_t, σ_s, v_s; iFrame.
      iSplitL ""; [ iPureIntro; setoid_rewrite H0; auto | ].
      iSplitL ""; [ iPureIntro; setoid_rewrite H1; auto | ].
      iApply H; eauto; reflexivity.
  Qed.

  Instance lift_expr_rel_Φ_Proper {R1 R2} Φ:
    Proper ((fun x y => eq_itree eq (go x) (go y)) ==> (fun x y => eq_itree eq (go x) (go y)) ==> equiv)
           (lift_expr_rel (R1 := R1) (R2 := R2) Φ).
  Proof.
    repeat intro. unfold lift_expr_rel.
    iSplit; iIntros "SI".
    - iDestruct "SI" as (σ_t v_t σ_s v_s) "[%Hr1 [%Hr2 [SI Hx]]]".
      iExists σ_t, v_t, σ_s, v_s; iFrame.
      iSplitL ""; [ iPureIntro; setoid_rewrite <- H; auto | ].
      iPureIntro; setoid_rewrite <- H0; auto.
    - iDestruct "SI" as (σ_t v_t σ_s v_s) "[%Hr1 [%Hr2 [SI Hx]]]".
      iExists σ_t, v_t, σ_s, v_s; iFrame.
      iSplitL ""; [ iPureIntro; setoid_rewrite H; auto | ].
      iPureIntro; setoid_rewrite H0; auto.
  Qed.

  Instance lift_expr_rel_FΦ_Proper {R1 R2} F Φ:
    Proper (eq_itree eq ==> eq_itree eq ==> equiv)
          (fun t s => lift_expr_rel (R1 := R1) (R2 := R2) (fun e_t e_s => F Φ e_t e_s ∨ Φ e_t e_s)%I (observe t) (observe s)).
  Proof.
    repeat intro. unfold lift_expr_rel.
    iSplit; iIntros "SI".
    - iDestruct "SI" as (σ_t v_t σ_s v_s) "[%Hr1 [%Hr2 [SI Hx]]]".
      iExists σ_t, v_t, σ_s, v_s; iFrame.
      iSplitL ""; [ iPureIntro; setoid_rewrite <- H; auto | ].
      iPureIntro; setoid_rewrite <- H0; auto.
    - iDestruct "SI" as (σ_t v_t σ_s v_s) "[%Hr1 [%Hr2 [SI Hx]]]".
      iExists σ_t, v_t, σ_s, v_s; iFrame.
      iSplitL ""; [ iPureIntro; setoid_rewrite H; auto | ].
      iPureIntro; setoid_rewrite H0; auto.
  Qed.

  #[global] Instance sim_expr_Proper {R1 R2} :
    Proper ((eq_itree eq ==> eq_itree eq ==> equiv) ==> eq_itree eq ==> eq_itree eq ==> equiv)
           (fun Φ e_t e_s => sim_expr (R1 := R1) (R2 := R2) Φ e_t e_s).
  Proof.
    intros Φ Φ' HΦ e_t e_t' Ht e_s e_s' Hs.
    iSplit; iIntros "HΦ".
    { rewrite sim_expr_eq.
      iIntros (σ_t σ_s) "SI".
      iSpecialize ("HΦ" with "SI").
      iDestruct "HΦ" as ">HΦ". iModIntro.
      pose (lift_expr_rel Φ ) as lΦ.
      pose (lift_expr_rel Φ') as lΦ'.
      pose proof (@sim_coindF_Proper R1 R2) as Hproper. repeat red in Hproper.
      specialize (Hproper lΦ lΦ').
      assert (((fun x y => eq_itree eq (go x) (go y)) ==> (fun x y => eq_itree eq (go x) (go y)) ==> equiv)%signature lΦ lΦ') as HΦProper. {
        repeat intro. iSplit; iIntros "H".
        - unfold lΦ, lΦ'. iApply lift_expr_rel_Proper; [ | by symmetry | by symmetry  | done].
          repeat intro. iSplit; iIntros "H"; iApply HΦ; eauto.
          all : symmetry; auto.
        - unfold lΦ, lΦ'. iApply lift_expr_rel_Proper; done.
      }
      specialize (Hproper HΦProper).
      assert (Hit: (⟦ η ⟨e_t⟩ ⟧ σ_t) ≅ (⟦ η ⟨e_t'⟩ ⟧ σ_t)).
      { unfold interp_L2. rewrite Ht. reflexivity. }
      assert (His: (⟦ η ⟨e_s⟩ ⟧ σ_s) ≅ (⟦ η ⟨e_s'⟩ ⟧ σ_s)).
      { unfold interp_L2. rewrite Hs. reflexivity. }
      specialize (Hproper _ _ Hit _ _ His). unfold lΦ' in Hproper. cbn in Hproper.
      iApply Hproper. done. }
    { rewrite sim_expr_eq.
      iIntros (σ_t σ_s) "SI".
      iSpecialize ("HΦ" with "SI").
      iDestruct "HΦ" as ">HΦ". iModIntro.
      pose (lift_expr_rel Φ) as lΦ.
      pose (lift_expr_rel Φ') as lΦ'.
      pose proof (@sim_coindF_Proper R1 R2) as Hproper. repeat red in Hproper.
      specialize (Hproper lΦ lΦ').
      assert (((fun x y => eq_itree eq (go x) (go y)) ==> (fun x y => eq_itree eq (go x) (go y)) ==> equiv)%signature lΦ lΦ') as HΦProper. {
        repeat intro. iSplit; iIntros "H".
        - unfold lΦ, lΦ'. iApply lift_expr_rel_Proper; [ | by symmetry | by symmetry  | done].
          repeat intro. iSplit; iIntros "H"; iApply HΦ; eauto.
          all : symmetry; auto.
        - unfold lΦ, lΦ'. iApply lift_expr_rel_Proper; done.
      }
      specialize (Hproper HΦProper).
      assert (Hit: (⟦ η ⟨e_t⟩ ⟧ σ_t) ≅ (⟦ η ⟨e_t'⟩ ⟧ σ_t)).
      { unfold interp_L2. rewrite Ht. reflexivity. }
      assert (His: (⟦ η ⟨e_s⟩ ⟧ σ_s) ≅ (⟦ η ⟨e_s'⟩ ⟧ σ_s)).
      { unfold interp_L2. rewrite Hs. reflexivity. }
      specialize (Hproper _ _ Hit _ _ His). cbn in Hproper.
      iApply Hproper. done. }
  Qed.

  Instance sim_expr_Φ_entails {R1 R2} Φ:
    Proper (eq_itree eq ==> eq_itree eq ==> bi_entails) (sim_expr (R1 := R1) (R2 := R2) Φ).
  Proof.
    intros e_t e_t' Ht e_s e_s' Hs.
    iIntros "HΦ".
    { rewrite sim_expr_eq.
      iIntros (σ_t σ_s) "SI".
      iSpecialize ("HΦ" with "SI").
      iDestruct "HΦ" as ">HΦ". iModIntro.
      pose (lift_expr_rel Φ) as lΦ.
      pose proof (@sim_coindF_Proper R1 R2) as Hproper. repeat red in Hproper.
      assert (((fun x y => eq_itree eq (go x) (go y)) ==> (fun x y => eq_itree eq (go x) (go y)) ==> equiv)%signature lΦ lΦ) as HΦProper. {
        repeat intro. iSplit; iIntros "H".
        - unfold lΦ. iApply lift_expr_rel_Φ_Proper; [ by symmetry | by symmetry  | done].
        - unfold lΦ. iApply lift_expr_rel_Φ_Proper; try done.
      }
      specialize (Hproper lΦ lΦ HΦProper).
      assert (Hit: (⟦ η ⟨e_t⟩ ⟧ σ_t) ≅ (⟦ η ⟨e_t'⟩ ⟧ σ_t)).
      { unfold interp_L2. rewrite Ht. reflexivity. }
      assert (His: (⟦ η ⟨e_s⟩ ⟧ σ_s) ≅ (⟦ η ⟨e_s'⟩ ⟧ σ_s)).
      { unfold interp_L2. rewrite Hs. reflexivity. }
      specialize (Hproper _ _ Hit _ _ His). cbn in Hproper.
      iApply Hproper. done. }
  Qed.

  #[global] Instance sim_expr_Φ_Proper {R1 R2} Φ:
    Proper (eq_itree eq ==> eq_itree eq ==> equiv) (sim_expr (R1 := R1) (R2 := R2) Φ).
  Proof.
    repeat intro.
    iSplit; iApply sim_expr_Φ_entails; done.
  Qed.

  #[global] Instance sim_coind_Proper_entails {R1 R2} Φ:
    Proper (eq_itree eq ==> eq_itree eq ==> bi_entails)
      (sim_coind (R1 := R1) (R2 := R2) Φ).
  Proof.
    iIntros (??????) "H".
    iApply sim_coindF_Proper; try done.
    repeat intro; iApply lift_expr_rel_Φ_Proper; try done.
  Qed.

  #[global] Instance sim_coind_Proper {R1 R2} Φ:
    Proper (eq_itree eq ==> eq_itree eq ==> equiv)
      (sim_coind (R1 := R1) (R2 := R2) Φ).
  Proof.
    iIntros (??????).
    iSplit; by iApply sim_coind_Proper_entails.
  Qed.

  Definition join_st_expr {R1 R2} (F: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2 ) : st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2:=
    λ Φ, sim_coindF (λ e_t e_s, F Φ e_t e_s ∨ Φ e_t e_s)%I.

  Global Instance join_st_expr_ne {R1 R2} F:
    NonExpansive F →
    NonExpansive (join_st_expr (R1 := R1) (R2 := R2) F).
  Proof.
    intros HF ??? Heq. rewrite /join_st_expr. repeat intro. f_equiv.
    intros ??. repeat f_equiv. done.
  Qed.

  (* Guarded-ness for coinductive step *)
  Definition lock_st_step {R1 R2} (Φ: st_expr_rel' R1 R2) (e_t: st_expr' Λ R1) (e_s: st_expr' Λ R2) :=
      (|==>
          match e_t, e_s with
          | TauF t, TauF t' => Φ (observe t) (observe t')
          | VisF e k, VisF e' k' => handle_event Φ k k' e e'
          | _, _ => |==> ⌜False⌝
       end
      )%I.

  Lemma sim_coindF_paco {R1 R2} F Φ e_t e_s:
    NonExpansive (F: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2) →
    □ (∀ Φ e_t e_s, F Φ e_t e_s -∗ lock_st_step (join_st_expr F Φ) e_t e_s) -∗
      F Φ e_t e_s -∗ sim_coindF Φ e_t e_s.
  Proof.
    iIntros (Hne) "#Hlock_step HF".
    iApply (sim_coindF_strong_coind (join_st_expr F)%I); last first.
    { rewrite /join_st_expr.
      rewrite sim_coindF_unfold sim_indF_unfold.
      iApply sim_expr_inner_base. by iLeft. }
    iModIntro. clear Φ e_t e_s. iIntros (Φ e_t e_s) "Hs".

    rewrite {2}/join_st_expr sim_coindF_unfold.
    pose (rec := (λ Φ e_t e_s, join_st_expr F Φ e_t e_s ∨ sim_coindF Φ e_t e_s)%I).
    assert (NonExpansive (rec: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2)).
    { intros ??? Heq; solve_proper. }
    pose (Rec := (λ Ψ e_t e_s, ∀ Φ, (∀ e_t e_s, Ψ e_t e_s -∗ F Φ e_t e_s ∨ Φ e_t e_s) -∗ sim_indF rec Φ e_t e_s)%I).
    assert (NonExpansive (Rec: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2)).
    { intros ??? Heq ??. rewrite /Rec. repeat f_equiv. }
    iApply (sim_indF_ind Rec with "[] Hs []"); last auto.

    clear e_t e_s Φ.
    iModIntro. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (Φ) "Hcont".

    (* [Hinner] for the "inner" expression, i.e. [e_s] *)
    rewrite /sim_expr_inner.
    cbn in *. unfold observe.

    rewrite sim_indF_unfold /sim_expr_inner.
    iMod "Hinner"; iDestruct "Hinner" as ( c ) "Hinner";
      destruct c; try case_solve; try done.

    { (* [BASE] case *)
      iSpecialize ("Hcont" with "Hinner").
      iDestruct "Hcont" as "[Hcont | Hcont]"; [ | by provide_case: BASE].
      iSpecialize ("Hlock_step" with "Hcont").
      rewrite /lock_st_step.
      destruct e_t, e_s; try iDestruct "Hlock_step" as ">>%_"; try contradiction;
        iMod "Hlock_step".
      { provide_case: TAU_STEP; rewrite /rec; by iLeft. }
      { provide_case: VIS_STEP.
        iApply handle_event_mono; [ iIntros; by iLeft | done]. } }

    { (* [STUTTER_L] case *)
      iSpecialize ("Hinner" with "Hcont"); subst.
      provide_case: STUTTER_L; cbn; by repeat (iSplitL ""; [ done | ]). }

    { (* [STUTTER_R] case*)
      iSpecialize ("Hinner" with "Hcont"); subst.
      provide_case: STUTTER_R; cbn; by repeat (iSplitL ""; [ done | ]). }

    { (* [TAU_STEP] case *)
      subst; provide_case: TAU_STEP; cbn; repeat (iSplitL ""; [ done | ]).
      iLeft.
      iApply (sim_coindF_bupd_mono with "[Hcont] Hinner").
      iIntros (e_t' e_s') "HΨ"; iModIntro; by iSpecialize ("Hcont" with "HΨ"). }

    { (* [VIS_STEP] case *)
      subst; provide_case: VIS_STEP; cbn; repeat (iSplitL ""; [ done | ]).
      destruct et eqn: Het, es eqn: Hes; cbn;
        rewrite /handle_E; try done;
        [destruct c, p, c0, p; simp handle_call_events | destruct s, s0; [ done ..|]].
      { iDestruct "Hinner" as "[ Hinner | Hinner ]";
          [iLeft | iRight];
            iDestruct "Hinner" as (?) "(SI & Hcall & Hinner)"; iExists _; iFrame ;
        iIntros (v_t v_s) "ECI"; iSpecialize ("Hinner" with "ECI"); iLeft;
        iMod "Hinner"; iModIntro;
        iApply (sim_coindF_bupd_mono with "[Hcont] Hinner");
        iIntros (e_t' e_s') "HΨ"; iModIntro;
            iSpecialize ("Hcont" with "HΨ"); done. }
      { destruct s, s0; try done.
        iDestruct "Hinner" as "[HCI Hinner]".
        unfold handle_E. iFrame. iIntros (v_t v_s) "EI". iSpecialize ("Hinner" with "EI").
        iFrame; iLeft.
        iMod "Hinner"; iModIntro.
        iApply (sim_coindF_bupd_mono with "[Hcont] Hinner");
        iIntros (e_t' e_s') "HΨ"; iModIntro;
          iSpecialize ("Hcont" with "HΨ"); destruct e_t', e_s'; done. } }

    { (* [SOURCE_UB] case *)
      subst; provide_case: SOURCE_UB; by cbn. }

    { (* [SOURCE_EXC] case *)
      subst; provide_case: SOURCE_EXC; by cbn. }
  Qed.

  (* derived things about sim *)
  Lemma simV_value {R1 R2} (Φ: expr_rel R1 R2) v_t v_s σ_t σ_s:
    ⊢ Φ v_t v_s -∗ Ret (σ_t, v_t) ⪯ Ret (σ_s, v_s) ⦃ Φ ⦄.
  Proof.
    iIntros "Hv".
    unfold sim, sim_val.
    rewrite sim_coindF_unfold sim_indF_unfold.
    iApply sim_expr_inner_base; iFrame.

    rewrite /lift_post.
    iExists σ_t, v_t, σ_s, v_s. iFrame.
    iSplit; eauto.
  Qed.

  Lemma sim_value {R1 R2} (Φ: expr_rel R1 R2) v_t v_s:
    ⊢ Φ v_t v_s -∗ Ret v_t ⪯ Ret v_s {{ Φ }}.
  Proof.
    iIntros "Hv". iApply sim_expr_base.
    iExists v_t, v_s. iFrame. iSplit; done.
  Qed.

  Lemma bupd_sim {R1 R2} (Φ:expr_rel R1 R2) e_t e_s:
    ⊢ (|==> e_t ⪯ e_s [{ Φ }]) -∗ e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "Hv". rewrite sim_expr_unfold. iIntros (??) "H". iMod "Hv". iApply ("Hv" with "H").
  Qed.

  Lemma lift_post_val_mon {R1 R2} Φ Φ':
    (∀ (v_t:R1) (v_s:R2), Φ v_t v_s -∗ Φ' v_t v_s) -∗
        (∀ e_t e_s, lift_post_val Φ e_t e_s -∗ lift_post_val Φ' e_t e_s).
  Proof.
    iIntros "Hmon" (e_t e_s). rewrite /lift_post_val. iIntros "He".
    iDestruct "He" as (σ_t v_t σ_s v_s) "(-> & -> & Hp)". iExists σ_t, v_t, σ_s, v_s. do 2 (iSplitR; first done).
    by iApply "Hmon".
  Qed.

  Lemma lift_post_mon {E R1 R2} Φ Φ':
    (∀ (v_t:R1) (v_s:R2), Φ v_t v_s -∗ Φ' v_t v_s) -∗
        (∀ e_t e_s, lift_post (E := E) Φ e_t e_s -∗ lift_post (E := E) Φ' e_t e_s).
  Proof.
    iIntros "Hmon" (e_t e_s). rewrite /lift_post. iIntros "He".
    iDestruct "He" as (v_t v_s) "(%Ht & %Hs & Hp)". iExists v_t, v_s. do 2 (iSplitR; first done).
    by iApply "Hmon".
  Qed.

  Lemma sim_mono {R1 R2} Φ Φ' :
    (∀ v_t v_s, Φ v_t v_s -∗ Φ' v_t v_s) -∗
    ∀ (e_t : exprO R1) (e_s : exprO R2), e_t ⪯ e_s {{ Φ }} -∗ e_t ⪯ e_s {{ Φ' }}.
  Proof.
    iIntros "Hmon" (e_s e_t) "Ha". iApply (sim_expr_mono with "[Hmon] Ha").
    by iApply lift_post_mon.
  Qed.

  Lemma sim_bupd {R1 R2} Φ e_t e_s :
    (e_t ⪯ e_s {{ λ (v_t:R1) (v_s:R2), |==> Φ v_t v_s }}) -∗ e_t ⪯ e_s {{ Φ }}.
  Proof.
    iIntros "Hv". iApply sim_expr_bupd.
    iApply (sim_expr_mono with "[] Hv").
    iIntros (e_t' e_s') "Ha". rewrite /lift_post.
    iDestruct "Ha" as (v_t v_s) "(%Ht & %Hs & >Ha)". iModIntro.
    iExists v_t, v_s. iFrame. iSplit; done.
  Qed.

  (** Corollaries *)
  Lemma sim_frame_r {R1 R2} e_t e_s R Φ :
    e_t ⪯ e_s {{ Φ }} ∗ R ⊢ e_t ⪯ e_s {{λ (v_t:R1) (v_s:R2), Φ v_t v_s ∗ R}}.
  Proof.
    iIntros "[Hsim HR]". iApply (sim_mono with "[HR] [Hsim//]"). iIntros (v_t v_s) "H". iFrame.
  Qed.

  Lemma sim_frame_l {R1 R2} e_t e_s R Φ :
    R ∗ e_t ⪯ e_s {{ Φ }} ⊢ e_t ⪯ e_s {{λ (v_t:R1) (v_s:R2), R ∗ Φ v_t v_s}}.
  Proof.
    iIntros "[HR Hsim]". iApply (sim_mono with "[HR] [Hsim//]"). iIntros (v_t v_s) "H". iFrame.
  Qed.

  Lemma sim_wand {R1 R2} e_t e_s Φ Ψ:
    e_t ⪯ e_s {{ Φ }} -∗ (∀ (v_t:R1) (v_s:R2), Φ v_t v_s -∗ Ψ v_t v_s) -∗ e_t ⪯ e_s {{ Ψ }}.
  Proof. iIntros "H Hv". iApply (sim_mono with "Hv H"). Qed.

  Lemma sim_wand_l {R1 R2} e_t e_s Φ Ψ:
    (∀ (v_t:R1) (v_s:R2), Φ v_t v_s -∗ Ψ v_t v_s) ∗ e_t ⪯ e_s {{ Φ }} ⊢ e_t ⪯ e_s {{ Ψ }}.
  Proof. iIntros "[Hv H]". iApply (sim_wand with "H Hv"). Qed.

  Lemma sim_wand_r {R1 R2} e_t e_s Φ Ψ:
    e_t ⪯ e_s {{ Φ }} ∗ (∀ (v_t:R1) (v_s:R2), Φ v_t v_s -∗ Ψ v_t v_s) ⊢ e_t ⪯ e_s {{ Ψ }}.
  Proof. iIntros "[H Hv]". iApply (sim_wand with "H Hv"). Qed.

  Lemma sim_expr_wand {R1 R2} e_t e_s (Φ:expr_rel R1 R2) Ψ:
    e_t ⪯ e_s [{ Φ }] -∗ (∀ e_t e_s, Φ e_t e_s -∗ Ψ e_t e_s) -∗ e_t ⪯ e_s [{ Ψ }].
  Proof. iIntros "H Hv". iApply (sim_expr_mono with "Hv H"). Qed.

  (** Update the SI. Useful when we use the SI to encode invariants. *)
  Definition update_si_strong (P : PROP) : PROP :=
    (∀ σ_t σ_s,
        state_interp σ_t σ_s ==∗
        state_interp σ_t σ_s ∗ P).
  Instance update_si_strong_proper : Proper ((≡) ==> (≡)) (update_si_strong).
  Proof. solve_proper. Qed.
  Lemma sim_update_si_strong {R1 R2} e_t e_s (Φ:expr_rel R1 R2) :
    update_si_strong (e_t ⪯ e_s [{ Φ }]) -∗ e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "Hupd". rewrite {2}(sim_expr_unfold Φ e_t e_s).
    iIntros (??) "Hstate".
    iMod ("Hupd" with "Hstate") as "[Hstate Hsim]".
    rewrite {1}sim_expr_unfold. iApply "Hsim". by iFrame.
  Qed.

  Definition update_si (P : PROP) :=
    (∀ σ_t σ_s, state_interp σ_t σ_s ==∗ state_interp σ_t σ_s ∗ P)%I.
  Instance update_si_proper : Proper ((≡) ==> (≡)) update_si.
  Proof. solve_proper. Qed.
  Lemma sim_update_si {R1 R2} e_t e_s (Φ:expr_rel R1 R2) :
    update_si (e_t ⪯ e_s [{ Φ }]) -∗ e_t ⪯ e_s [{ Φ }].
  Proof.
    iIntros "Hupd". iApply sim_update_si_strong.
    iIntros (??) "Hstate". by iApply "Hupd".
  Qed.

  Lemma sim_coindF_vis {R1 R2 Re1 Re2} Φ (ev_t : L2 Λ Re1) k_t (ev_s : L2 Λ Re2) k_s:
    (Φ (VisF ev_t k_t) (VisF ev_s k_s)
      ∨ (handle_event (sim_coindF Φ) k_t k_s ev_t ev_s)) -∗
    sim_coindF (R1 := R1) (R2 := R2) Φ (VisF ev_t k_t) (VisF ev_s k_s).
  Proof.
    rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.
    iIntros "H"; destruct ev_s; [ | destruct s]; auto.

    all : iDestruct "H" as "[H | H]";
      by [ provide_case: BASE | provide_case: VIS_STEP ].
  Qed.

  Lemma sim_coindF_tau {R1 R2} (Φ: st_expr_rel' R1 R2) e_t e_s:
    sim_coindF Φ (observe e_t) (observe e_s) -∗
    sim_coindF Φ (TauF e_t) (TauF e_s).
  Proof.
    setoid_rewrite sim_coindF_unfold at 2.
    rewrite sim_indF_unfold /sim_expr_inner.
    iIntros "Hpre". by provide_case: TAU_STEP.
  Qed.

  Lemma sim_coindF_tauR {R1 R2} (Φ: st_expr_rel' R1 R2) e_t e_s:
    sim_coindF Φ e_t (observe e_s) -∗
    sim_coindF Φ e_t (TauF e_s).
  Proof.
    setoid_rewrite sim_coindF_unfold at 2.
    rewrite sim_indF_unfold /sim_expr_inner.
    iIntros "Hpre". provide_case: STUTTER_R.
    by rewrite sim_coindF_unfold.
  Qed.

  Lemma sim_coindF_tauL {R1 R2} (Φ: st_expr_rel' R1 R2) e_t e_s:
    sim_coindF Φ (observe e_t) e_s -∗
    sim_coindF Φ (TauF e_t) e_s.
  Proof.
    setoid_rewrite sim_coindF_unfold at 2.
    rewrite sim_indF_unfold /sim_expr_inner.
    iIntros "Hpre". provide_case: STUTTER_L.
    by rewrite sim_coindF_unfold.
  Qed.

  Lemma sim_coind_base {R1 R2} (Φ: expr_rel R1 R2) v_t v_s:
    ⊢ state_interp v_t.1 v_s.1 ∗ Φ (Ret v_t.2) (Ret v_s.2) -∗
    sim_coind Φ (Ret v_t) (Ret v_s).
  Proof.
    iIntros "He".
    iApply sim_coindF_fixpoint.
    iApply sim_expr_inner_base; iFrame.
    rewrite /lift_expr_rel. repeat iExists _; iFrame.
    rewrite -!itree_eta; iSplitL ""; destruct v_t, v_s; by iPureIntro.
  Qed.

  Lemma sim_coind_ret_inv {R1 R2} (Φ: expr_rel R1 R2) v_t v_s:
    sim_coind Φ (Ret v_t) (Ret v_s) ==∗
    state_interp v_t.1 v_s.1 ∗ Φ (Ret v_t.2) (Ret v_s.2).
  Proof.
    iIntros "He".
    rewrite /sim_coind sim_coindF_fixpoint /sim_expr_inner.
    iMod "He".
    iDestruct "He" as (?) "He".
    destruct c.
    { rewrite /lift_expr_rel.
      iDestruct "He" as (??????) "(SI & HΦ)".
      rewrite -itree_eta in H; rewrite -itree_eta in H0.
      eapply eqit_inv in H, H0; cbn in *; subst; by iFrame. }
    { rewrite /stutter_l.
      iDestruct "He" as (? Habs) "He"; inversion Habs. }
    { rewrite /stutter_r.
      iDestruct "He" as (? Habs) "He"; inversion Habs. }
    { rewrite /tau_step.
      iDestruct "He" as (?? Habs) "He"; inversion Habs. }
    { rewrite /vis_step.
      iDestruct "He" as (?????? Habs) "He"; inversion Habs. }
    { rewrite /source_ub.
      iDestruct "He" as (???) "%Habs"; inversion Habs. }
    { rewrite /source_exc.
      iDestruct "He" as (???) "%Habs"; inversion Habs. }
  Qed.

  Lemma sim_coind_tau {R1 R2} (Φ: expr_rel R1 R2) e_t e_s:
    sim_coind Φ e_t e_s -∗
    sim_coind Φ (Tau e_t) (Tau e_s).
  Proof.
    rewrite /sim_coind. iApply sim_coindF_tau.
  Qed.

  Lemma sim_coind_tauR {R1 R2} (Φ: expr_rel R1 R2) e_t e_s:
    sim_coind Φ e_t e_s -∗
    sim_coind Φ e_t (Tau e_s).
  Proof.
    rewrite /sim_coind. iApply sim_coindF_tauR.
  Qed.

  Lemma sim_coind_tauL {R1 R2} (Φ: expr_rel R1 R2) e_t e_s:
    sim_coind Φ e_t e_s -∗
    sim_coind Φ (Tau e_t) e_s.
  Proof.
    rewrite /sim_coind. iApply sim_coindF_tauL.
  Qed.

  Lemma sim_coindF_TauL_inv {R1 R2} (Φ: st_expr_rel' R1 R2) t1 t2:
    ⊢ <pers>(∀ x y, Φ (TauF x) y -∗ Φ (observe x) y) -∗
     sim_coindF Φ (observe (Tau t1)) t2 -∗
     sim_coindF Φ (observe t1) t2.
  Proof.
    iIntros "#HT H".
    pose (F := (λ (Ψ:st_expr_rel' R1 R2) (e_t:st_exprO' R1) e_s,
                ∀ Φ,
                  (∀ (e_t : st_exprO' R1) (e_s : st_exprO' R2),
                      Ψ e_t e_s -∗
                            ∀ e_t' e_t'', ⌜TauF e_t' = e_t⌝ -∗ ⌜observe e_t' = e_t''⌝ -∗
                               sim_indF sim_coindF Φ e_t'' e_s)%I -∗
                  (* Introduced these for NonExpansive proof obligation, is there a better way around this? *)
                   (∀ x y, sim_coindF Ψ x y -∗ sim_coindF Φ x y) -∗
                   (∀ x y, Ψ x y -∗ Φ x y) -∗
                    (∀ e_t' e_t'', ⌜TauF e_t' = e_t⌝ -∗ ⌜observe e_t' = e_t''⌝ -∗
                         sim_indF (R1 := R1) (R2 := R2) sim_coindF Φ e_t'' e_s)
               )%I).
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ (observe e_t) e_s) -∗ F Ψ (observe e_t) e_s)%I as "Hgen"; last first.
    { rewrite !sim_coindF_unfold.
      iSpecialize ("Hgen" with "H"); try done. unfold F.
      iApply "Hgen"; [ |  | | | ].
      2,3 : iIntros; eauto.
      2,3 : cbn; iPureIntro; reflexivity.
      { iIntros (e_t e_s) "HΦ %e_t' %ot %EQ %EQ'". subst.
        rewrite sim_indF_unfold; eauto. rewrite /sim_expr_inner.
        provide_case: BASE.
        iApply ("HT" with "[HΦ]"); try done. } }

    iIntros (Ψ e_t e_s) "Hsim".
    iApply (sim_indF_strong_ind with "[] Hsim"); clear Ψ e_t e_s.
    { solve_proper_prepare. repeat f_equiv; eauto; apply H. }

    iModIntro. iIntros (Ψ e_t e_s) "IHR".

    rewrite {2}/F. iClear "HT". clear t1 t2 Φ.
    iIntros "%Φ Hcont HΦ Hcont' %e_t' %ot %EQ %EQ'". subst.

    rewrite (sim_indF_unfold). rewrite /sim_expr_inner.
    iMod "IHR".
    iDestruct "IHR" as (c) "IHR".
    destruct c.
    { iSpecialize ("Hcont" with "IHR").
      iSpecialize ("Hcont" $! _ _ eq_refl eq_refl).
      rewrite sim_indF_unfold; by eauto. }
    { rewrite /stutter_l. 
      iDestruct "IHR" as (??) "[_ IHR]"; inv H.
      setoid_rewrite <- sim_indF_unfold; [ | typeclasses eauto].
      setoid_rewrite <- sim_coindF_unfold; eauto.
      iApply ("HΦ" with "IHR").  }
    { rewrite /stutter_r.
      iDestruct "IHR" as (??) "[IHR _]"; subst.
      iSpecialize ("IHR" with "Hcont HΦ Hcont'").
      iSpecialize ("IHR" $! _ _ eq_refl eq_refl).
      by provide_case: STUTTER_R. }
    { rewrite /tau_step.
      iDestruct "IHR" as (????) "IHR"; inv H; subst.
      provide_case: STUTTER_R.
      iSpecialize ("HΦ" with "IHR").
      by rewrite sim_coindF_unfold. }
    { rewrite /vis_step.
      iDestruct "IHR" as (???????) "IHR"; inv H.  }
    { rewrite /source_ub. 
      iDestruct "IHR" as (???) "%H"; subst.
      by provide_case: SOURCE_UB.  }
    { rewrite /source_exc. 
      iDestruct "IHR" as (???) "%H"; subst.
      by provide_case: SOURCE_EXC.  }
  Qed.

  Lemma sim_coindF_TauR_inv {R1 R2} (Φ: st_expr_rel' R1 R2) t1 t2:
    ⊢ <pers>(∀ x y, Φ x (TauF y) -∗ Φ x (observe y)) -∗
     sim_coindF Φ t1 (observe (Tau t2)) -∗
     sim_coindF Φ t1 (observe t2).
  Proof.
    iIntros "#HT H".
    pose (F := (λ (Ψ:st_expr_rel' R1 R2) (e_t:st_exprO' R1) (e_s:st_exprO' R2),
                ∀ Φ,
                  (∀ (e_t : st_exprO' R1) (e_s : st_exprO' R2),
                      Ψ e_t e_s -∗
                            ∀ e_s' e_s'', ⌜TauF e_s' = e_s⌝ -∗ ⌜observe e_s' = e_s''⌝ -∗
                               sim_indF sim_coindF Φ e_t e_s'')%I -∗

                  (* Introduced these for NonExpansive proof obligation, is there a better way around this? *)
                   (∀ x y, sim_coindF Ψ x y -∗ sim_coindF Φ x y) -∗
                   (∀ x y, Ψ x y -∗ Φ x y) -∗

                    (∀ e_s' e_s'', ⌜TauF e_s' = e_s⌝ -∗ ⌜observe e_s' = e_s''⌝ -∗
                         sim_indF (R1 := R1) (R2 := R2) sim_coindF Φ e_t e_s'')
               )%I).
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t (observe e_s)) -∗ F Ψ e_t (observe e_s))%I as "Hgen"; last first.
    { rewrite !sim_coindF_unfold.
      iSpecialize ("Hgen" with "H"); try done. unfold F.
      iApply "Hgen"; [ | | | | ].
      2,3 : iIntros; eauto.
      2,3 : cbn; iPureIntro; reflexivity.
      { iIntros (e_t e_s) "HΦ %e_t' %ot %EQ %EQ'". subst.
        rewrite sim_indF_unfold; eauto. rewrite /sim_expr_inner.
        provide_case: BASE.
        iApply ("HT" with "[HΦ]"); try done. } }

    iIntros (Ψ e_t e_s) "Hsim".
    iApply (sim_indF_strong_ind with "[] Hsim"); clear Ψ e_t e_s.
    { solve_proper_prepare. repeat f_equiv; eauto; apply H. }

    iModIntro. iIntros (Ψ e_t e_s) "IHR".

    rewrite {2}/F. iClear "HT". clear t1 t2 Φ.
    iIntros "%Φ Hcont HΦ Hcont' %e_t' %ot %EQ %EQ'". subst.

    rewrite (sim_indF_unfold). rewrite /sim_expr_inner.
    iMod "IHR".
    iDestruct "IHR" as (c) "IHR".
    destruct c.
    { iSpecialize ("Hcont" with "IHR").
      iSpecialize ("Hcont" $! _ _ eq_refl eq_refl).
      rewrite sim_indF_unfold; by eauto. }
    { rewrite /stutter_l.
      iDestruct "IHR" as (??) "[IHR _ ]"; subst.
      iSpecialize ("IHR" with "Hcont HΦ Hcont'").
      iSpecialize ("IHR" $! _ _ eq_refl eq_refl).
      by provide_case: STUTTER_L. }
    { rewrite /stutter_r.
      iDestruct "IHR" as (??) "[_ IHR]"; inv H; subst.
      setoid_rewrite <- sim_indF_unfold; [ | typeclasses eauto].
      setoid_rewrite <- sim_coindF_unfold; eauto.
      iApply ("HΦ" with "IHR").  }
    { rewrite /tau_step.
      iDestruct "IHR" as (????) "IHR"; inv H0; subst.
      provide_case: STUTTER_L.
      iSpecialize ("HΦ" with "IHR").
      by rewrite sim_coindF_unfold. }
    { rewrite /vis_step.
      iDestruct "IHR" as (????????) "IHR"; inv H0.  }
    { rewrite /source_ub. 
      iDestruct "IHR" as (???) "%H"; subst.
      by provide_case: SOURCE_UB.  }
    { rewrite /source_exc. 
      iDestruct "IHR" as (???) "%H"; subst.
      by provide_case: SOURCE_EXC.  }
    Unshelve. all :eauto.
  Qed.

  #[global] Instance exc_L2_subevent: exc_events Λ -< L2 Λ :=
      λ (T : Type) (X : exc_events Λ T), inr1 (inr1 (inl1 X)).

  #[global] Instance UB_L2_subevent: UB_events Λ -< L2 Λ :=
      λ (T : Type) (X : UB_events Λ T), inr1 (inl1 X).

  #[global] Instance transitive_subevent {A B C}
    {HA: A -< B} {HB: B -< C}: A -< C :=
    λ (T : Type) (X : A T), HB T (HA T X).

  Lemma sim_coind_exc {R1 R2 X}
    (Φ: expr_rel R1 R2) (ev: exc_events Λ X) e_t k:
    ⊢ sim_coind (η := η) Φ e_t (vis ev k).
  Proof.
    rewrite /sim_coind. rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.
    by provide_case: SOURCE_EXC.
  Qed.

  Lemma sim_coind_ub {R1 R2 X}
    (Φ: expr_rel R1 R2) (ev: UB_events _ X) e_t k:
    ⊢ sim_coind Φ e_t (vis ev k).
  Proof.
    rewrite /sim_coind. rewrite sim_coindF_unfold sim_indF_unfold /sim_expr_inner.
    by provide_case: SOURCE_UB.
  Qed.

  Lemma sim_coind_tauR_inv {R1 R2} (Φ: expr_rel R1 R2) e_t e_s:
    sim_coind Φ e_t (Tau e_s) -∗
    sim_coind Φ e_t e_s.
  Proof.
    rewrite /sim_coind.
    iApply sim_coindF_TauR_inv.
    iModIntro. rewrite /lift_expr_rel.
    iIntros (??) "H".
    iDestruct "H" as (??????) "(SI & HΦ)".
    by eapply eqit_inv in H0.
  Qed.

  Lemma sim_coind_tauL_inv {R1 R2} (Φ: expr_rel R1 R2) e_t e_s:
    sim_coind Φ (Tau e_t) e_s -∗
    sim_coind Φ e_t e_s.
  Proof.
    rewrite /sim_coind.
    iApply sim_coindF_TauL_inv.
    iModIntro. rewrite /lift_expr_rel.
    iIntros (??) "H".
    iDestruct "H" as (??????) "(SI & HΦ)".
    by eapply eqit_inv in H.
  Qed.

  Notation res_rel R1 R2 := ((state Λ * R1) -d> (state Λ * R2) -d> PROP).

  Definition lift_pure_rel {R1 R2} (Φ : res_rel R1 R2) : st_expr_rel' R1 R2 :=
    fun t s => (∃ v_t v_s, ⌜Ret v_t ≅ go t⌝ ∗ ⌜Ret v_s ≅ go s⌝ ∗
        Φ v_t v_s)%I.

  #[local] Definition fmap_coind_pred {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
    ((∃ I1 I2
       (f : state Λ * R1 -> state Λ * I1)
       (g : state Λ * R2 -> state Λ * I2)
       (Ψ : state Λ * I1 → state Λ * I2 → PROP),
       <pers> (∀ e_t e_s, lift_pure_rel (fun x y => Ψ (f x) (g y)) e_t e_s -∗ Φ e_t e_s) ∗
        sim_coindF (lift_pure_rel Ψ)
          (observe (ITree.bind (go e_t) (fun x => Ret (f x))))
          (observe (ITree.bind (go e_s) (fun x => Ret (g x)))))%I).

  #[local] Definition fmap_coind_rec {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
    ((∃ I1 I2
      (f : state Λ * R1 -> state Λ * I1)
      (g : state Λ * R2 -> state Λ * I2)
      (Ψ : state Λ * I1 → state Λ * I2 → PROP),
      <pers> (∀ e_t e_s, lift_pure_rel (fun x y => Ψ (f x) (g y)) e_t e_s -∗ Φ e_t e_s) ∗
      sim_coindF (lift_pure_rel Ψ)
        (observe (ITree.bind (go e_t) (fun x => Ret (f x))))
        (observe (ITree.bind (go e_s) (fun x => Ret (g x)))))
     ∨ sim_coindF Φ e_t e_s)%I.

  Local Instance fmap_coind_pred_ne {R1 R2}:
    NonExpansive (fmap_coind_pred: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv.
  Qed.

  Local Instance fmap_coind_rec_ne {R1 R2}:
    NonExpansive (fmap_coind_rec: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. by repeat f_equiv.
  Qed.

  Lemma sim_coindF_fmap_inv :
    ∀ (R1 R2 Re1 Re2 : Type) Ψ
      (e_t : st_expr Λ Re1) (e_s : st_expr Λ Re2)
      (f : state Λ * Re1 → state Λ * R1) (g : state Λ * Re2 -> state Λ * R2),
        sim_coindF (lift_pure_rel Ψ)
          (observe (ITree.bind e_t (fun x => Ret (f x))))
          (observe (ITree.bind e_s (fun x => Ret (g x)))) -∗
        sim_coindF (lift_pure_rel (fun x y => Ψ (f x) (g y)))
        (observe e_t) (observe e_s).
  Proof.
    iIntros (?????????) "Hpre".
    iApply (sim_coindF_strong_coind fmap_coind_pred); last first.
    { rewrite /fmap_coind_pred. iExists _, _, f, g, Ψ.
      iFrame. iModIntro. iIntros. done. }
    iModIntro. clear Ψ e_t e_s R1 R2 f g.
    iIntros (Φ e_t e_s) "IH".

    change (sim_indF _ Φ e_t e_s) with (sim_indF fmap_coind_rec Φ e_t e_s).
    rewrite /fmap_coind_pred.
    iDestruct "IH" as (R1 R2 f g Ψ) "(#HΦ & H)".

    rewrite {1}sim_coindF_unfold.
    rename Re1 into I1.
    rename Re2 into I2.

    pose (F :=
      (λ (Ψ : st_expr_rel' R1 R2) e_t e_s,
        (∀ (e_t' : st_expr Λ I1) (e_s' : st_expr Λ I2),
          ⌜e_t = (observe (ITree.bind e_t' (fun x => Ret (f x))))⌝ -∗
          ⌜e_s = (observe (ITree.bind e_s' (fun x => Ret (g x))))⌝ -∗
          <pers> (∀ e_t' e_s', Ψ e_t' e_s' ==∗
              ∀ (e_t'' : st_expr Λ I1) (e_s'' : st_expr Λ I2),
                ⌜e_t' = (observe (ITree.bind e_t'' (fun x => Ret (f x))))⌝ -∗
                ⌜e_s' = (observe (ITree.bind e_s'' (fun x => Ret (g x))))⌝ -∗
              Φ (observe e_t'') (observe e_s'')) -∗
          ∀ Ψ', <pers> (∀ e_t e_s, lift_pure_rel Ψ' e_t e_s ∗-∗ Ψ e_t e_s) -∗
          <pers> (∀ e_t e_s, lift_pure_rel (fun x y => Ψ' (f x) (g y)) e_t e_s -∗ Φ e_t e_s) -∗
          sim_indF fmap_coind_rec Φ (observe e_t') (observe e_s'))%I)).
    (* Assertion [Ω] *)
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗ F Ψ e_t e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "H"). rewrite /F.
      iSpecialize ("Hgen" $! (go e_t) (go e_s) eq_refl eq_refl).
      iApply "Hgen"; cycle 1.
      { iModIntro. iIntros (??); iSplitL""; iIntros "H"; done. }
      { iModIntro. iIntros (??); done. }
      iModIntro.
      iIntros (??) "H". rewrite /lift_pure_rel.
      iModIntro.
      iDestruct "H" as (????) "H".
      iIntros (????). subst.
      rewrite -itree_eta in H. rewrite -itree_eta in H0.
      iApply "HΦ".
      rewrite (itree_eta e_t'') in H.
      rewrite (itree_eta e_s'') in H0.
      destruct (observe e_t''); apply eqit_inv in H; try solve [inversion H].
      destruct (observe e_s''); apply eqit_inv in H0; try solve [inversion H0].
      cbn in H, H0; subst. iExists _, _; iFrame. done. }

    (* Now we prove the assertion [Ω]. *)
    iClear "HΦ".
    clear Ψ e_t e_s.
    iIntros (Ψ e_t e_s) "Hsim".
    iApply (sim_indF_ind with "[] Hsim"); clear Ψ e_t e_s.
    { solve_proper_prepare. clear -H. repeat f_equiv. }

    iModIntro. iIntros (Ψ e_t e_s) "Hinner".
    iIntros (????) "#Hcont %Ψ' #HΨ' #HP"; subst.

    (* [Hinner] for the "inner" expression, i.e. [e_s] *)
    rewrite /sim_expr_inner.
    cbn -[F] in *. unfold observe.

    rewrite sim_indF_unfold /sim_expr_inner.
    iMod "Hinner"; iDestruct "Hinner" as ( c ) "Hinner";
      destruct c; try case_solve; try done.

    { (* [BASE] case *)
      iSpecialize ("Hcont" with "Hinner").
      iMod "Hcont".
      iSpecialize ("Hcont" $! _ _ eq_refl eq_refl).
      by provide_case: BASE. }

    { (* [STUTTER_L] case*)
      rewrite /F. cbn in H0.
      destruct (observe e_t') eqn: Ht'; inversion H0.
      iSpecialize ("Hinner" $! _ _ eq_refl eq_refl).
      iSpecialize ("Hinner" with "Hcont HΨ' HP"); subst.
      provide_case: STUTTER_L; cbn. unfold observe in Ht'; rewrite Ht'.
      by repeat (iSplitL ""; [ done | ]). }

    { (* [STUTTER_L] case*)
      rewrite /F. cbn in H0.
      destruct (observe e_s') eqn: Hs'; inversion H0.
      iSpecialize ("Hinner" $! _ _ eq_refl eq_refl).
      iSpecialize ("Hinner" with "Hcont HΨ' HP"); subst.
      provide_case: STUTTER_R; cbn. unfold observe in Hs'; rewrite Hs'.
      by repeat (iSplitL ""; [ done | ]). }

    { (* [TAU_STEP] case *)
      cbn in H0, H1.
      destruct (observe e_s') eqn: Hs'; inversion H1.
      destruct (observe e_t') eqn: Ht'; inversion H0.

      subst; provide_case: TAU_STEP; cbn; repeat (iSplitL ""; [ done | ]).
      unfold observe in Ht', Hs'; rewrite Ht' Hs'.

      repeat iExists _.
      iSplitR; [done | iSplitR; [done |]].
      iLeft. iExists _, _, f, g, Ψ'.
      iSplitL "". { iModIntro. done. }
      iApply (sim_coindF_bupd_mono with "[Hcont] Hinner").
      iIntros (e_t'' e_s'') "HΨ"; iModIntro; by iSpecialize ("HΨ'" with "HΨ"). }

    { (* [VIS_STEP] case *)
      cbn in H0, H1.
      destruct (observe e_s') eqn: Hs'; inversion H1.
      destruct (observe e_t') eqn: Ht'; inversion H0.
      unfold observe in Ht', Hs'; rewrite Ht' Hs'.
      dependent destruction H7.

      subst; provide_case: VIS_STEP; cbn; repeat (iSplitL ""; [ done | ]).

      destruct et eqn: Het, es eqn: Hes; cbn;
        rewrite /handle_E; try done;
        [destruct c, p, c0, p; simp handle_call_events | destruct s, s0; [ done ..|]].

      { iDestruct "Hinner" as "[ Hinner | Hinner ]";
          [iLeft | iRight];
            iDestruct "Hinner" as (?) "(SI & Hcall & Hinner)"; iExists _; iFrame;
          iIntros (v_t v_s) "ECI"; iSpecialize ("Hinner" with "ECI"); iLeft;
        iMod "Hinner"; iModIntro;

        iExists _, _, f, g, Ψ'.
        all: iSplitL ""; [ iModIntro; done | ];
        iApply (sim_coindF_bupd_mono with "[Hcont] Hinner");
        iIntros (e_t'' e_s'') "HΨ"; iModIntro; by iSpecialize ("HΨ'" with "HΨ"). }
      { destruct s, s0; try done.
        iDestruct "Hinner" as "[HCI Hinner]".
        unfold handle_E. iFrame. iIntros (v_t v_s) "EI". iSpecialize ("Hinner" with "EI").
        iFrame; iLeft.
        iMod "Hinner"; iModIntro.

        iExists _, _, f, g, Ψ'.
        iSplitL "". { iModIntro. done. }
        iApply (sim_coindF_bupd_mono with "[Hcont] Hinner").
        iIntros (e_t'' e_s'') "HΨ"; iModIntro; by iSpecialize ("HΨ'" with "HΨ"). } }

    { (* [SOURCE_UB] case *)
      cbn in Heq.
      destruct (observe e_s') eqn: Hs'; inversion Heq.
      dependent destruction H2. unfold observe in Hs'; rewrite Hs'.
      subst; provide_case: SOURCE_UB; by cbn. }

    { (* [SOURCE_EXC] case *)
      cbn in Heq.
      destruct (observe e_s') eqn: Hs'; inversion Heq.
      dependent destruction H2. unfold observe in Hs'; rewrite Hs'.
      subst; provide_case: SOURCE_EXC; by cbn. }
  Qed.

  Lemma sim_expr_fmap_inv :
    ∀ (R1 R2 Re1 Re2 : Type) (Φ : exprO R1 -d> exprO R2 -d> PROP)
      (e_t : expr Λ Re1) (e_s : expr Λ Re2) (f : Re1 → R1) (g : Re2 -> R2),
      ⊢ ITree.bind e_t (fun x => Ret (f x)) ⪯
        ITree.bind e_s (fun x => Ret (g x)) [{ Φ }] -∗
        e_t ⪯ e_s [{ lift_post (fun x y => Φ (Ret (f x)) (Ret (g y))) }].
  Proof.
    iIntros (?????????) "H".
    rewrite sim_expr_eq /sim_expr_.
    rewrite sim_expr_eq /sim_expr_.
    iIntros (??) "SI".
    iSpecialize ("H" with "SI"). iMod "H".
    iApply sim_coindF_bupd_mono; [ | iApply sim_coindF_fmap_inv]; cycle 1.
    { iModIntro.
      rewrite /interp_L2.
      iPoseProof (sim_coind_Proper_entails with "H") as "H".
      { rewrite StateFacts.interp_state_bind.
        setoid_rewrite StateFacts.interp_state_ret. reflexivity. }
      { rewrite StateFacts.interp_state_bind.
        setoid_rewrite StateFacts.interp_state_ret. reflexivity. }
      iApply sim_coindF_bupd_mono ; [ | iApply "H"].
      iIntros (??) "H". rewrite /lift_expr_rel.
      Unshelve.
      2 : { exact (fun x y => (state_interp x.1 y.1 ∗ Φ (Ret x.2) (Ret y.2)))%I. }
      iDestruct "H" as (??????) "(SI & H)". rewrite /lift_pure_rel.
      iModIntro. iExists (σ_t0, v_t), (σ_s0, v_s); iFrame. done. }
    iIntros (??) "H".
    iDestruct "H" as (????) "(SI & H)".
    subst; rewrite /lift_expr_rel /lift_post.
    iModIntro.
    destruct v_t, v_s.
    iExists s, r, s0, r0.
    repeat (iSplitL ""; [done | ]). iFrame.
    repeat iExists _; iFrame.
    iSplitL ""; done.
  Qed.

End sim_properties.

Arguments lift_post : simpl never.

(** Coq gives up TC search prematurely for our Sim/SimE instances, so declare
them as hint extern instead. See <https://github.com/coq/coq/pull/13952>. *)
Global Hint Extern 0 (Sim _ _) => apply sim_val : typeclass_instances.
Global Hint Extern 0 (SimE _ _) => apply sim_expr_stutter : typeclass_instances.
Global Hint Extern 0 (NonExpansive sim_coindF) => apply sim_coindF_ne : typeclasses_instances.

Arguments stutter_l {_ _ _ _ _ _ _ _} : simpl never.
Arguments stutter_r {_ _ _ _ _ _ _ _} : simpl never.
Arguments tau_step {_ _ _ _ _ _ _ _} : simpl never.
Arguments vis_step {_ _ _ _ _ _ _ _ _ _ _} : simpl never.
Arguments source_ub {_ _ _ _ _ _} : simpl never.
Arguments source_exc {_ _ _ _ _ _} : simpl never.
