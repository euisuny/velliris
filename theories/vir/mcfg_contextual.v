From iris.prelude Require Import options.

From Coq Require Import Program.Equality.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
  vir val_rel heapbij adequacy spec globalbij logical_relations fundamental
  interp_properties.

From Vellvm Require Import Syntax.DynamicTypes Handlers Syntax.LLVMAst
  Semantics.InterpretationStack.

From Equations Require Import Equations.

From ITree Require Import ITree Recursion Eq.Eqit.
From Equations Require Import Equations.

Import LLVMEvents.

Set Default Proof Using "Type*".

(* -------------------------------------------------------------------------- *)

(* ITree-related tactics *)
Ltac obs_hyp :=
  match goal with
  | [ H : {| _observe := observe _ |} = _ |- _] =>
      let Hobs := fresh "Hobs" in
      inversion H as [ Hobs ]; clear H
  end.

(* Turn an [observe] hypothesis to an ITree equivalence. *)
Ltac simpobs_eqit :=
  try obs_hyp;
  match goal with
  | [ H : observe _ = _ |- _] =>
      symmetry in H; apply Eqit.simpobs in H
  end.

(* -------------------------------------------------------------------------- *)

Section mcfg_contextual.

  Context `(vellirisGS Σ).

  Definition args_rel :=
    fun args_t args_s => ([∗ list] x;y ∈ args_t ;args_s, uval_rel x y)%I.

  (* Invariant for frame-related resources across a single function call that
     is satisfied by the fundamental theorem *)
  Definition frame_inv i_t i_s :=
    (frame_WF i_t i_s ∗ checkout ∅ ∗ stack_tgt i_t ∗ stack_src i_s)%I.

  (* An obligation for each of the defined calls; it satisfies the external
      call specifications *)
  Definition context_rel
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T) :=
    (∀ fn1 fn2 dt1 dt2 args1 args2 C,
          let call1 := ExternalCall dt1 fn1 args1 nil in
          let call2 := ExternalCall dt2 fn2 args2 nil in
          call_ev call1 call2 C -∗
          ⟅ f _ (Call dt1 fn1 args1 nil) ⟆ ⪯
          ⟅ g _ (Call dt2 fn2 args2 nil) ⟆
          [[ (fun v1 v2 => call_ans call1 v1 call2 v2 C) ⤉ ]])%I.

  Notation st_expr_rel' R1 R2 :=
    (@st_exprO' vir_lang R1 -d> @st_exprO' vir_lang R2 -d> iPropI Σ).

  Definition contains_base {T} Φ :=
    (∀ x y : st_exprO' T, base x y ∗ Φ x y ∗-∗ Φ x y : iProp Σ)%I.

  (* Auxiliary definitions for [Proper_interp_mrec] *)
  (* Because [sim_expr] includes stateful interpretation, showing properness result
    for [interp_mrec] amounts to proving a simulation *)
  Local Definition mrec_pred {R} :=
    fun (Φ:st_expr_rel' _ _) (e_t:st_expr' vir_lang R) (e_s:st_expr' vir_lang R) =>
      (∃ f g a_t a_s σ_t σ_s,
          ⌜e_t = observe (⟦ interp_mrec f a_t ⟧ σ_t)⌝ ∗
          ⌜e_s = observe (⟦ interp_mrec g a_s ⟧ σ_s)⌝ ∗
          (* Function is called on related addresses and arguments *)
          (* Postcondition contains [base] predicate*)
          □ contains_base Φ ∗
          (* Contexts are related *)
          □ context_rel f g ∗
          sim_coindF Φ
              (observe (⟦ ⟅ a_t ⟆ ⟧ σ_t)) (observe (⟦ ⟅ a_s ⟆ ⟧ σ_s)))%I.

  Local Definition mrec_rec {R} :=
    fun (Φ:st_expr_rel' _ _) (e_t:st_expr' vir_lang R) (e_s:st_expr' vir_lang R) =>
      ((∃ f g a_t a_s σ_t σ_s,
          ⌜e_t = observe (⟦ interp_mrec f a_t ⟧ σ_t)⌝ ∗
          ⌜e_s = observe (⟦ interp_mrec g a_s ⟧ σ_s)⌝ ∗
          □ contains_base Φ ∗
          □ context_rel f g ∗
         sim_coindF Φ
          (observe (⟦ ⟅ a_t ⟆ ⟧ σ_t)) (observe (⟦ ⟅ a_s ⟆ ⟧ σ_s)))
        ∨ sim_coindF Φ e_t e_s)%I.

  Local Instance mrec_pred_ne {R}:
    NonExpansive (mrec_pred: st_expr_rel' _ _ -d> st_expr_rel' _ R).
  Proof.
    intros x y *. solve_proper_prepare.
  (*   repeat f_equiv; try solve_proper. *)
  (* Qed. *)
  Admitted.

  Local Instance mrec_rec_ne {R}:
    NonExpansive (mrec_rec: st_expr_rel' _ _ -d> st_expr_rel' _ R).
  Proof.
    intros x y *. solve_proper_prepare.
  Admitted.

  (* -------------------------------------------------------------------------- *)
  (* Local notations to make life "easier".. *)
  Local Notation sim_mrec_ind := (sim_expr_inner mrec_rec (sim_indF mrec_rec)).
  Local Notation "o⟦ e ⟧ σ" := (observe (⟦ e ⟧ σ)) (at level 12).
  (* -------------------------------------------------------------------------- *)

  (* Utility lemmas *)
  Lemma vir_call_ev_nil i_t i_s t dv args :
    frame_inv i_t i_s -∗
    dval_rel dv dv -∗
    args_rel args args -∗
    vir_call_ev Σ
    (ExternalCall t dv args []) (ExternalCall t dv args []) (i_t, i_s).
  Proof.
    iIntros "(?&?&?&?&?) Hv Huv".
    simp vir_call_ev; iFrame; eauto.
  Qed.

  (* Access [frame_WF] predicate out of [frame_inv] *)
  Lemma frame_inv_frame_WF i_t i_s :
    frame_inv i_t i_s -∗
    frame_WF i_t i_s.
  Proof. iIntros "(?&?&?&?)"; done. Qed.

(* -------------------------------------------------------------------------- *)

  Notation mrec_body := (∀ T : Type, CallE T → L0'expr T).

  (* Induction hypothesis for [Proper_mrec] *)
  Local Definition mrec_ind {R} :=
    (λ Φ e_t e_s,
      ∀ {f g : mrec_body} {a_t a_s : _ R} {σ_t σ_s},
        ⌜e_t = observe (⟦ ⟅ a_t ⟆ ⟧ σ_t) ⌝ -∗
        ⌜e_s = observe (⟦ ⟅ a_s ⟆ ⟧ σ_s) ⌝ -∗
        □ contains_base Φ -∗
        □ context_rel f g -∗
        sim_indF mrec_rec Φ
        (observe (⟦ interp_mrec f a_t ⟧ σ_t))
        (observe (⟦ interp_mrec g a_s ⟧ σ_s)))%I.

  Local Instance mrec_ind_ne {R}:
    NonExpansive (mrec_ind: st_expr_rel' _ _ -d> st_expr_rel' _ R).
  Proof.
    solve_proper_prepare. clear -H. repeat f_equiv.
  Admitted.

  Lemma Proper_mrec_pred
    {f g : mrec_body} {i_t i_s t dv args σ_t σ_s}:
      (* Function address value and arguments are self-related *)
      dval_rel dv dv -∗
      args_rel args args -∗
      (* Frame invariant holds *)
      frame_inv i_t i_s -∗
      (* Contexts are related *)
      □ context_rel f g -∗
      state_interp σ_t σ_s ==∗
      mrec_pred (lift_rel ((λ _ _ : uvalue, frame_inv i_t i_s) ⤉))
        (observe (⟦ mrec f (Call t dv args []) ⟧ σ_t))
        (observe (⟦ mrec g (Call t dv args []) ⟧ σ_s)).
  Proof.
    rewrite /mrec_pred.
    iIntros "#Hdv #Hargs Hinv #Hrel SI".
    iExists f, g, _, _, σ_t, σ_s.
    rewrite /mrec.
    do 2 (iSplitL ""; first done); iFrame "Hrel".
    rewrite /call_ev; cbn -[state_interp].
    iSpecialize ("Hrel" $! dv dv t t args args (i_t, i_s)).
    iPoseProof (frame_inv_frame_WF with "Hinv") as "%Hframe_WF".
    iPoseProof (vir_call_ev_nil with "Hinv Hdv Hargs") as "Hev".
    iSpecialize ("Hrel" with "Hev SI").

    (* Base postcondition *)
    iSplitL "".
    { do 2 iModIntro. iIntros (??). iSplitL ""; iIntros "H".
      - iDestruct "H" as "(H & Hr)"; done.
      - iDestruct "H" as (????) "(SI&H)". (* TODO fact about [base] *)
        iDestruct "H" as (??????) "H".
        iFrame. iSplit.
        { rewrite /base. subst.
          iExists (σ_t0, v_t), (σ_s0, v_s). iPureIntro; split.
          { apply EqAxiom.bisimulation_is_eq.
            rewrite H2. by rewrite -itree_eta. }
          { apply EqAxiom.bisimulation_is_eq.
            rewrite H3. by rewrite -itree_eta. } }
        subst.
        iExists σ_t0, σ_s0, e_t, e_s; iFrame.
        do 2 (iSplitL ""; [ done | ]).
        iExists v_t, v_s; done. }
    iMod "Hrel".

    (* Establish postcondition. *)
    iApply (sim_coindF_bupd_mono with "[] Hrel").
    iIntros (??) "Hrel". rewrite /lift_rel.
    iDestruct "Hrel" as (????) "(SI & %Ht & %Hs & Hrel)"; subst.
    (* Access lifted postcondition *)
    iDestruct "Hrel" as (????) "Hrel". rewrite /call_ans /=.
    simp vir_call_ans. iDestruct "Hrel" as "(?&?&?&#?)"; iFrame.
    (* Prove postcondition. *)
    iExists σ_t0, σ_s0, e_t0, e_s0; iFrame.
    do 2 (iSplitL ""; first done).
    iExists v_t, v_s; done.
  Qed.

  (* Cases for [Proper_mrec] *)
  Lemma Proper_mrec_base (f g : mrec_body) t dv args attr σ_t σ_s Ψ:
    <pers> contains_base Ψ -∗
    Ψ (o⟦ ⟅ f uvalue (Call t dv args attr) ⟆ ⟧ σ_t)
      (o⟦ ⟅ g uvalue (Call t dv args attr) ⟆ ⟧ σ_s) -∗
    sim_mrec_ind Ψ
      (o⟦ mrec f (Call t dv args attr) ⟧ σ_t)
      (o⟦ mrec g (Call t dv args attr) ⟧ σ_s).
  Proof.
    iIntros "#Hbase HΨ".
    iSpecialize ("Hbase" with "HΨ").
    iDestruct "Hbase" as "(Hb & He)".
    iDestruct "Hb" as (???) "%Hb".

    do 2 simpobs_eqit.
    apply interp_L2_conv_ret_inv in Hobs, Hobs0.
    to_eq in Hobs; to_eq in Hobs0; subst; cbn.

    (* force unfold mrec *)
    with_strategy transparent [mrec] unfold mrec.
    rewrite Hobs Hobs0. cbn.
    by provide_case: BASE.
  Qed.

  Notation sim_ind := (sim_indF sim_coindF).

  (* -------------------------------------------------------------------------- *)

  Lemma Proper_mrec_stutter_l {f g : mrec_body} {e_t t dv args attr σ_t σ_s Ψ}:
    o⟦ ⟅ f uvalue (Call t dv args attr) ⟆ ⟧ σ_t = TauF e_t ->
    args_rel args args -∗
    <pers> contains_base Ψ -∗
    <pers> context_rel f g -∗
    mrec_ind Ψ (observe e_t) (o⟦ ⟅ g uvalue (Call t dv args attr) ⟆ ⟧ σ_s)
      ∧ sim_ind Ψ
        (observe e_t)
        (o⟦ ⟅ g uvalue (Call t dv args attr) ⟆ ⟧ σ_s) -∗
    sim_mrec_ind Ψ
      (o⟦ mrec f (Call t dv args attr) ⟧ σ_t)
      (o⟦ mrec g (Call t dv args attr) ⟧ σ_s).
  Proof.
    iIntros (Hf) "#args #Hbase #Hrel IH".

    simpobs_eqit.
    apply interp_L2_conv_tau_inv in Hf.
  Admitted.

  Lemma Proper_mrec_stutter_r {f g : mrec_body} {e_s t dv args attr σ_t σ_s Ψ}:
    o⟦ ⟅ g uvalue (Call t dv args attr) ⟆ ⟧ σ_s = TauF e_s ->
    args_rel args args -∗
    <pers> contains_base Ψ -∗
    <pers> context_rel f g -∗
    mrec_ind Ψ (o⟦ ⟅ f uvalue (Call t dv args attr) ⟆ ⟧ σ_t) (observe e_s)
    ∧ sim_ind Ψ
        (o⟦ ⟅ f uvalue (Call t dv args attr) ⟆ ⟧ σ_t)
        (observe e_s) -∗
    sim_mrec_ind Ψ
      (o⟦ mrec f (Call t dv args attr) ⟧ σ_t)
      (o⟦ mrec g (Call t dv args attr) ⟧ σ_s).
  Proof. Admitted.

  (* -------------------------------------------------------------------------- *)

  Lemma Proper_mrec_tau  {f g : mrec_body} {e_t e_s t dv args attr σ_t σ_s Ψ}:
    o⟦ ⟅ f uvalue (Call t dv args attr) ⟆ ⟧ σ_t = TauF e_t ->
    o⟦ ⟅ g uvalue (Call t dv args attr) ⟆ ⟧ σ_s = TauF e_s ->
    args_rel args args -∗
    <pers> contains_base Ψ -∗
    <pers> context_rel f g -∗
    sim_coindF Ψ (observe e_t) (observe e_s) -∗
    sim_mrec_ind Ψ
      (o⟦ mrec f (Call t dv args attr) ⟧ σ_t)
      (o⟦ mrec g (Call t dv args attr) ⟧ σ_s).
  Proof.
  Admitted.

  From ITree Require Import Interp.InterpFacts Events.StateFacts.

  Lemma interp_L2_conv_vis_call {X} τ a args attr σ
    (e : language.L2 vir_lang X) k
    (k' : X -> itree (language.L2 vir_lang) (_ * uvalue)) :
    ⟦ ⟅ vis (Call τ a args attr) k ⟆ ⟧ σ ≅ (Vis e k') ->
    X = (state vir_lang * uvalue)%type /\
    e ~= (inl1 (StateEff vir_calls
      (σ, ExternalCall τ a args (FNATTR_Internal :: attr)))
        : language.L2 vir_lang _)
    /\ (forall x y, x ~= y -> Tau (Tau (⟦ ⟅ k x.2 ⟆ ⟧  x.1)) ~= k' y).
  Proof.
    intros Hv.
    setoid_rewrite interp_vis in Hv.
    setoid_rewrite interp_state_bind in Hv.
    setoid_rewrite interp_state_vis in Hv.
    setoid_rewrite bind_bind in Hv.
    rewrite /subevent /resum /ReSum_inl /cat /Cat_IFun /inl_ /Inl_sum1
      /resum /ReSum_id /id_ /Id_IFun in Hv.
    simp call_conv in Hv. cbn in Hv.
    rewrite bind_vis in Hv.
    apply eqit_inv in Hv; cbn in Hv.
    destruct Hv as (?&?&?); subst. red in H0, H1.
    dependent destruction H0.
    do 2 (split; eauto).
    intros.
    specialize (H1 x).
    rewrite bind_ret_l in H1. rewrite interp_state_ret in H1.
    rewrite bind_tau bind_ret_l in H1.
    rewrite interp_state_tau in H1. cbn in *.
    apply EqAxiom.bisimulation_is_eq in H1. rewrite H1.
    dependent destruction H0. reflexivity.
  Qed.

  Lemma Proper_mrec_vis {X Y} {f g : mrec_body}
    {et kt es ks t dv args attr σ_t σ_s Ψ}:
    o⟦ ⟅ f uvalue (Call t dv args attr) ⟆ ⟧ σ_t = VisF et kt ->
    o⟦ ⟅ g uvalue (Call t dv args attr) ⟆ ⟧ σ_s = VisF es ks ->
    args_rel args args -∗
    <pers> contains_base Ψ -∗
    <pers> context_rel f g -∗
    handle_event (X := X) (Y := Y) (sim_coindF Ψ) kt ks et es -∗
    sim_mrec_ind Ψ
      (o⟦ mrec f (Call t dv args attr) ⟧ σ_t)
      (o⟦ mrec g (Call t dv args attr) ⟧ σ_s).
  Proof.
    iIntros (??) "#Hargs #Hbase #Hcrel Hev"; repeat simpobs_eqit.
    (* rename H2 into Hf, H3 into Hg. *)
    (* pose proof (Hf' := Hf); pose proof (Hg' := Hg). *)

    (* apply interp_L2_conv_vis_inv in Hf, Hg. *)

    (* destruct Hf as [ (τ_t&a_t&args_t&attr_t&k_t&Hf) | (X'&ev_t&k_t&Hf) ]; *)
    (*   destruct Hg as [ (τ_s&a_s&args_s&attr_s&k_s&Hg) | (Y'&ev_s&k_s&Hg) ]. *)

    (* 2,3 : admit. (* ABSURD *) *)

    (* { (* Internal *) *)

    (*   (* Prep *) *)
    (*   rewrite Hf in Hf'; rewrite Hg in Hg'. *)

    (*   cbn in *. *)

    (*   rewrite /resum /ReSum_id /id_ /Id_IFun. *)
    (*   simp handle_call_events. *)

    (*   (* force unfold mrec *) *)
    (*   with_strategy transparent [mrec] unfold mrec. *)
    (*   apply EqAxiom.bisimulation_is_eq in Hf, Hg. *)
    (*   rewrite Hf Hg !interp_mrec_call. *)

    (*   (* Invert information out of shape of call *) *)
    (*   apply interp_L2_conv_vis_call in Hf', Hg'. *)
    (*   destruct Hf' as (->&Het&Hkt); destruct Hg' as (->&Hes&Hks). *)
    (*   dependent destruction Het; dependent destruction Hes. *)

    (*   rewrite /handle_event; simp handle_call_events. *)

    (*   iDestruct "Hev" as "[ Hev | Hev ]"; cycle 1. *)

    (*   (* Internal call was "external" and now meets the spec *) *)
    (*   { iDestruct "Hev" as (?) "(SI & Hev & Hinner)". *)
    (*     provide_case: TAU_STEP. *)
    (*     iLeft. iExists f, g, _, _. *)
  Admitted.

  (* -------------------------------------------------------------------------- *)

  Ltac intro_mrec_coind :=
    iIntros (Φ e_t e_s) "IH";
    iDestruct "IH" as (????????) "(#Hbase & #Hcrel & IH)";
    subst.

  Ltac intro_mrec_ind :=
    iModIntro; iIntros (Ψ e_t e_s) "Hinner";
    iIntros (????????) "#Hargs #Hbase #Hcrel"; subst.

  (* Try to [iMod] a [sim_expr_inner] hypothesis. *)
  Ltac iMod_sim_inner :=
    rewrite /sim_expr_inner;
    cbn -[F] in *; rewrite sim_indF_unfold /sim_expr_inner;
    iMod "Hinner"; to_inner mrec_rec.

  (* -------------------------------------------------------------------------- *)

  Theorem Proper_mrec f g i_t i_s t dv args:
    (* Function address value and arguments are self-related *)
    dval_rel dv dv -∗
    args_rel args args -∗
    (* Frame invariant holds *)
    frame_inv i_t i_s -∗
    (* Contexts are related *)
    <pers> context_rel f g -∗
    mrec f (Call t dv args nil) ⪯ mrec g (Call t dv args nil)
    [[ (fun x y => frame_inv i_t i_s) ⤉ ]].
  Proof.
    iIntros "#Hdv #Hargs Hinv #Hrel"; iIntros (??) "SI".

    (* Initialize coinductive hypothesis. *)
    iApply (sim_coindF_strong_coind mrec_pred); cycle 1.
    { iApply (Proper_mrec_pred with "Hdv Hargs Hinv Hrel SI"). }

    (* Set up context *)
    iModIntro; iClear "Hdv Hargs Hrel"; clear.
    intro_mrec_coind.

    (* Induction on simulation between (f call) and (g call). *)
    rewrite sim_coindF_unfold.
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗
      mrec_ind Ψ e_t e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "IH").
      iApply ("Hgen" $! _ _ _ _ _ _ eq_refl eq_refl with "Hbase Hcrel"). }

    (* Set up context *)
    iClear "Hcrel Hbase"; clear.
    iIntros (Ψ e_t e_s) "Hsim".
    iApply (sim_indF_strong_ind with "[] Hsim"); clear.

    iModIntro; iIntros (Ψ e_t e_s) "Hinner".

    iIntros (????????) "#Hbase #Hcrel"; subst.


    rewrite /sim_expr_inner;
    cbn -[F] in *; rewrite sim_indF_unfold /sim_expr_inner;
    iMod "Hinner"; to_inner (mrec_rec (R := uvalue)).

    (* Case analysis on the inductive information. *)
    iDestruct "Hinner" as ( c ) "Hinner"; destruct c; try case_solve;
      try done; try rename H3 into Hf.

    (* ------------------------------------------------------------------ *)

    (* [BASE] case *)
    { admit. }
    (* iApply (Proper_mrec_base with "Hbase Hinner"). } *)

    (* ------------------------------------------------------------------ *)

    (* Inductive cases: [STUTTER_L] and [STUTTER R] *)

    (* [STUTTER_L] case *)
    { admit. }
    (* by iApply (Proper_mrec_stutter_l with "Hargs Hbase Hcrel Hinner"). } *)

    (* [STUTTER_R] case; symmetric to [STUTTER_L] *)
    { admit. }
    (* by iApply (Proper_mrec_stutter_r with "Hargs Hbase Hcrel Hinner"). } *)

    (* ------------------------------------------------------------------ *)

    (* Coinductive cases : [TAU_STEP] and [VIS_STEP] case *)

    (* [TAU_STEP] case *)
    { admit. }

    (* [VIS] case *)
    {
      (* rename H4 into Hg. do 2 simpobs_eqit. *)

      (* pose proof (Hf' := Hf); pose proof (Hg' := Hg). *)

      (* apply interp_L2_conv_vis_inv in Hf, Hg. *)

      (* destruct Hf as [ (τ_t&addr_t&args_t&attr_t&k_t&Hf) | (X'&ev_t&k_t&Hf) ]; *)
      (*   destruct Hg as [ (τ_s&addr_s&args_s&attr_s&k_s&Hg) | (Y'&ev_s&k_s&Hg) ]. *)
      (* 2,3: admit. (* absurd *) *)

      (* { (* Internal *) *)

      (*   cbn in *. *)

      (*   rewrite /resum /ReSum_id /id_ /Id_IFun. *)
      (*   simp handle_call_events. *)

      (*   (* force unfold mrec *) *)
      (*   apply EqAxiom.bisimulation_is_eq in Hf, Hg. *)
      (*   rewrite Hf Hg !interp_mrec_call. *)

      (*   rewrite Hf in Hf'; rewrite Hg in Hg'. *)
      (*   (* Invert information out of shape of call *) *)
      (*   apply interp_L2_conv_vis_call in Hf', Hg'. *)
      (*   destruct Hf' as (->&Het&Hkt); destruct Hg' as (->&Hes&Hks). *)
      (*   dependent destruction Het; dependent destruction Hes. *)

      (*   provide_case: TAU_STEP. *)


      (*   rewrite /handle_event. simp handle_call_events. *)

      (*   iDestruct "Hinner" as "[ Hinner | Hinner ]"; cycle 1. *)

      (*   (* Internal call was "external" and now meets the spec *) *)
      (*   { iLeft. iExists f, g, _, _, σ_t, σ_s. *)
      (*     repeat (iSplitL ""; first done); iFrame. *)
      (*     iDestruct "Hinner" as (?) "(SI & Hev & Hinner)". *)

      (*     (* Cut on internal call *) *)
      (*     rewrite !interp_L2_conv_bind; iApply sim_coindF_coind_bind. *)
      (*     rewrite /context_rel. *)
      (*     admit. } *)
        (*   iSpecialize ("Hcrel" with "Hev"). *)
        (*   match goal with *)
        (*   | |- environments.envs_entails _ (sim_coindF ?Φ _ _) => remember Φ *)
        (*   end. *)

        (*   (* Cut on internal call *) *)
        (*   rewrite !interp_L2_conv_bind. iApply sim_coindF_ *)


        (* by iApply (Proper_mrec_vis with "Hargs Hbase Hcrel Hinner"). } *)

    (* ------------------------------------------------------------------ *)
  Admitted.

(* -------------------------------------------------------------------------- *)

  (* Type declaration for function definitions, i.e. an association list for
     function definitions with [dvalue] keys. *)
  Definition fundefs : Type := list (dvalue * definition dtyp (CFG.cfg dtyp)).

  (* Definition fundef_no_attr (def : definition dtyp (CFG.cfg dtyp)) := *)
  (*   RelDec.rel_dec (dc_attrs (df_prototype def)) nil. *)

  (* The function definition map [fd] does not have any attributes at its
    definition site. *)
  (* Definition fundefs_no_attr (fd : fundefs) := *)
  (*   forallb (fun '(_, def) => fundef_no_attr def) fd. *)

(* -------------------------------------------------------------------------- *)

  Lemma sim_external_call dτ addr_t addr_s args_t args_s l i_t i_s:
    frame_WF i_t i_s -∗
    stack_tgt i_t -∗
    stack_src i_s -∗
    checkout ∅ -∗
    dval_rel addr_t addr_s -∗
    ([∗ list] x;y ∈ args_t;args_s, uval_rel x y) -∗
    ⟅ dargs <- Util.map_monad (λ uv : uvalue, pickUnique uv) args_t;;
    trigger (ExternalCall dτ addr_t (map dvalue_to_uvalue dargs) l) ⟆
      ⪯
      ⟅ dargs <- Util.map_monad (λ uv : uvalue, pickUnique uv) args_s;;
    trigger (ExternalCall dτ addr_s (map dvalue_to_uvalue dargs) l) ⟆
      [[ (fun x y =>
            uval_rel x y ∗ stack_tgt i_t ∗ stack_src i_s ∗
              checkout ∅) ⤉ ]].
  Proof. Admitted.

  (* -------------------------------------------------------------------------- *)

  (* Utility TODO: Move *)
  Lemma dval_rel_lookup_defn_cons {B fn_t fn_s fn_t' fn_s'} e_t e_s F :
    dval_rel fn_t fn_s -∗
    dval_rel fn_t' fn_s' -∗
    ([∗ list] v_t;v_s ∈ F.*1;F.*1, dval_rel v_t v_s) -∗

    (* Both match on the head of the list *)
    ⌜(lookup_defn fn_t ((fn_t', e_t) :: F) = Some e_t /\
        lookup_defn fn_s ((fn_s', e_s) :: F) = Some e_s) ∨

    (* Both match on an element in [F] *)
    (exists f g,
      lookup_defn fn_t F = Some f /\
      lookup_defn fn_s F = Some g /\
      lookup_defn fn_t ((fn_t', e_t) :: F) = Some f /\
      lookup_defn fn_s ((fn_s', e_s) :: F) = Some g) ∨

    (* Or it is not found *)
    (lookup_defn fn_t ((fn_t', e_t) :: F) = None /\
      lookup_defn (B := B) fn_s ((fn_s', e_s) :: F) = None)⌝.
  Proof.
    iIntros "Hv Hv' HF"; cbn.
    destruct (RelDec.rel_dec fn_s fn_s') eqn: Ht;
      [ iLeft; iSplit; eauto; reldec | iRight ]; reldec.
    (* Head *)
    { iDestruct (dval_rel_inj with "Hv Hv'") as "%He"; subst.
      by rewrite Util.eq_dec_eq. }

    (* Rest *)
    { iDestruct (dval_rel_ne_inj with "Hv Hv'") as "%He".
      assert (Hs: fn_s' <> fn_s) by eauto. specialize (He Hs).
      rewrite Util.eq_dec_neq; eauto.

      destruct (lookup_defn fn_s F) eqn: Hf_t.
      { iDestruct (dval_rel_lookup_some with "Hv HF") as %Hft.
        specialize (Hft _ Hf_t); destruct Hft as (?&Hft).
        iLeft; iPureIntro; eauto.
        exists x, b; split; [ | split]; eauto. }

      { iDestruct (dval_rel_lookup_none with "Hv HF") as %Hft.
        specialize (Hft Hf_t).
        iRight; iPureIntro; eauto. } }
  Qed.
  
  (* The contextual refinement on [denote_mcfg]. *)
  Lemma contextual_denote_mcfg :
    ∀ γ_t γ_s addr_t addr_s e_t e_s main F decl,
      fun_WF e_t ->
      fun_WF e_s ->
      fundefs_WF F decl ->
      (* fundefs_no_attr F -> *)
      (* fundef_no_attr e_t -> *)
      (* fundef_no_attr e_s -> *)
      □ fun_logrel e_t e_s ∅ -∗
        checkout ∅ -∗
        stack_tgt [γ_t] -∗
        stack_src [γ_s] -∗
        dval_rel addr_t addr_s -∗
        ([∗ list] v_t;v_s ∈ F.*1;F.*1, dval_rel v_t v_s) -∗
        denote_mcfg ((addr_t, e_t) :: F) DTYPE_Void (DVALUE_Addr main) []
        ⪯
        denote_mcfg ((addr_s, e_s) :: F) DTYPE_Void (DVALUE_Addr main) []
        [[ (λ x y : uvalue, ⌜obs_val x y⌝) ⤉ ]].
  Proof.
    iIntros (????????? WF_t WF_s WF_F) "#Hfun Hc Hs_t Hs_s #Hdv #Hfun_keys".

    (* The frame invariant holds. *)
    iAssert (frame_inv [γ_t] [γ_s])%I with "[Hc Hs_t Hs_s]" as "Hinv".
    { by iFrame. }

    (* rewrite mrec *)
    (* rewrite sim_expr'. *)


    (* iApply sim_coindF_strong_coind; cycle 1. *)
    (* rewrite /fun_logrel. *)

    (* rewrite /denote_mcfg. *)

    (* (* Try to prove this directly on coinduction? *) *)

    (* iPoseProof *)
    (*   (Proper_mrec _ _ (λ x y : uvalue, ⌜obs_val x y⌝)%I [γ_t] [γ_s] *)
    (*     with "Hinv") as "Hrec"; eauto. *)
    (* iApply (sim_expr'_bupd_mono with "[] [Hrec]"); last iApply "Hrec". *)

    (* (* Establish postcondition; trivial  *) *)
    (* { iIntros (??) "HΨ"; iDestruct "HΨ" as (????) "(%HΨ & HI)". *)
    (*   iExists _, _; iFrame. done. } *)

    (* rewrite /context_rel; iModIntro. *)

    (* (* Preparing proof state *) *)
    (* iIntros (fn_t fn_s dτ_t dτ_s args_t args_s C) "Hev"; *)
    (*   destruct C as ((?&i_t)&i_s); *)
    (* rewrite /call_ev; cbn -[denote_function lookup_defn]; simp vir_call_ev; *)
    (* iDestruct "Hev" as *)
    (*   "(#Hfn &%Hdt & %Hattr& #Hargs & HC & #HWF & Hst & Hss & %Hinterp)"; subst. *)

    (* (* Do a case analysis on whether the function is in the list of fundefs. *)

    (*   Because the context applied to the expression results in a closed term, *)
    (*   the function is always found in the context. *) *)

    (* iDestruct (dval_rel_lookup_defn_cons e_t e_s F with "Hfn Hdv Hfun_keys") as %Hlu. *)
    (* destruct Hlu as [ (->&->) | [ Hlu | Hlu ] ]; last admit. (* last case is absurd *) *)

    (* (* It is the hole *) *)
    (* { apply fundef_no_attr_eq in H_t, H_s; rewrite H_t H_s. *)
    (*   assert (Heq : RelDec.rel_dec (T := list fn_attr) nil nil = true) by admit; *)
    (*     rewrite Heq. *)
    (*   admit. } *)

    (* (* It is a function in the context *) *)
    (* { destruct Hlu as (f_t & f_s & Hlu_t & Hlu_s & -> & ->). *)
    (*   admit. } (* Should follow trivially. *) *)

  Admitted.

End mcfg_contextual.
