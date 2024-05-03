(* From Coq Require Import String List Program.Equality. *)
From iris.prelude Require Import options.
(* From iris.base_logic.lib Require Export gen_heap ghost_map. *)
(* From iris.base_logic Require Import gset_bij. *)

(* From Vellvm Require Import Syntax.LLVMAst Syntax.DynamicTypes *)
(*   Semantics.InterpretationStack Handlers Utils.Util Semantics.LLVMEvents. *)

From Equations Require Import Equations.

From Paco Require Import paco.

(* From velliris.logic Require Import satisfiable. *)
From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
  (* vir spec globalbij heapbij frame_laws primitive_laws bij_laws *)
  vir_sim_properties
  vir spec logical_relations fundamental_exp tactics.
(* From velliris.utils Require Import no_event. *)

Set Default Proof Using "Type*".

Import ListNotations.

Tactic Notation "mono:" tactic(tac) :=
  iApply sim_expr_bupd_mono; [ | tac; eauto ].

Tactic Notation "mono:" tactic(tac) "with" constr(hyps) :=
  iApply (sim_expr_bupd_mono with hyps); [ | tac; eauto ].

(** *Reflexivity theorems for logical relations *)
Section fundamental.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

 (* ------------------------------------------------------------------------ *)
  (* Utility *)
  (* LATER: Generalize this helper lemma to any triple that is lifted with *)
  (*   [map_monad] *)
  Lemma denote_exp_map_monad (e: list (texp dtyp)) C i_t i_s A_t A_s :
    code_inv C i_t i_s A_t A_s -∗
    instr_conv
      (map_monad (λ '(t, op), translate exp_to_instr (denote_exp (Some t) op)) e)
      ⪯
    instr_conv
      (map_monad (λ '(t, op), translate exp_to_instr (denote_exp (Some t) op)) e)
      [{ (e_t, e_s), code_inv C i_t i_s A_t A_s
                       ∗ [∗ list] _↦x_t;x_s ∈ e_t;e_s, uval_rel x_t x_s }].
  Proof.
    iIntros "CI".
    iInduction e as [] "IHl".
    { cbn. vsimp. Base.
      iExists _,_; do 2 (iSplitL ""; [done |]); iFrame; done. }
    { cbn. vsimp.
      destruct a.
      Cut. vsimp.

      mono: iApply (expr_logrel_refl with "CI").

      iIntros (??) "H";
      iDestruct "H" as (??->->) "(Hv & CI)".

      vsimp. Cut.
      iSpecialize ("IHl" with "CI").

      mono: iApply "IHl" with "[Hv]".

      clear e_t e_s; iIntros (e_t e_s) "H".
      iDestruct "H" as (?? -> ->) "(CI & H)".
      final.
      iExists _, _; do 2 (iSplitL ""; [ done | ]).
      rewrite big_sepL2_cons; iFrame. }
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Instr-level reflexivity lemmas *)

  Lemma instr_call_refl C fn attrs args id  i_t i_s A_t A_s:
    ⊢ (code_inv C i_t i_s A_t A_s -∗
      instr_conv
       (denote_instr (IId id, INSTR_Call fn args attrs)) ⪯
       instr_conv
       (denote_instr (IId id, INSTR_Call fn args attrs))
       [{ (r_t, r_s),
           code_inv C i_t i_s A_t A_s }])%I.
  Proof.
    iIntros "CI".
    cbn; destruct fn.
    vsimp. Cut.
    mono: iApply (denote_exp_map_monad args _ with "CI").
    iIntros (??) "H".
    iDestruct "H" as (??->->) "(CI & #H)";
    vsimp.

    (* 1. expression refl *)
    Cut. vsimp.
    iApply sim_expr_bupd_mono; [ | by iApply expr_logrel_refl].
    iIntros (??) "Hp"; iDestruct "Hp" as (??->->) "(#Hv & CI)".
    vsimp.

    (* 2. Call simulation *)
    Cut.

    mono: (iApply (instr_conv_concretize_or_pick_strong with "Hv")) with "[CI]".

    iIntros (??) "H'".
    iDestruct "H'" as (??->->) "(Hdv & %Hdu_t & %Hdu_s)".
    vsimp. Cut. vsimp.

    mono: iApply (call_refl with "CI Hdv H").
    cbn. clear e_t e_s.
    iIntros (??) "Hp".
    iDestruct "Hp" as (??->->) "(#Hv2 & CI)".

    vsimp.

    (* 3. Local write simulation *)
    final; vsimp.
    mono: iApply (local_write_refl with "CI Hv2").

    iIntros (??) "Hp".
    iDestruct "Hp" as (??->->) "CI".
    vsimp. final.
    iExists _, _; by iFrame.
  Qed.

  Lemma instr_call_void_refl C fn args attrs n i_t i_s A_t A_s:
    ⊢ (code_inv C i_t i_s A_t A_s -∗
      instr_conv
       (denote_instr (IVoid n, INSTR_Call fn args attrs)) ⪯
       instr_conv
       (denote_instr (IVoid n, INSTR_Call fn args attrs))
       [{ (r_t, r_s), code_inv C i_t i_s A_t A_s }])%I.
  Proof.
    iIntros "CI".
    cbn; destruct fn.
    vsimp; Cut.
    iApply sim_expr_bupd_mono;
      [ | iApply (denote_exp_map_monad args _ with "CI") ]; auto.
    cbn. iIntros (??) "H".
    iDestruct "H" as (??->->) "(CI & #H)"; vsimp.
    (* 1. expression refl *)
    Cut; vsimp.
    iApply sim_expr_bupd_mono; [ | by iApply expr_logrel_refl].
    cbn. iIntros (??) "Hp".
    iDestruct "Hp" as (??->->) "(#Hv & CI)".
    vsimp.

    (* 2. Call simulation *)
    Cut.
    mono: (iApply (instr_conv_concretize_or_pick_strong with "Hv")) with "[CI]".

    iIntros (??) "H'".
    iDestruct "H'" as (??->->) "(Hdv & %Hdu_t & %Hdu_s)".
    vsimp; Cut; vsimp.

    mono: iApply (call_refl with "CI Hdv H").
    cbn. clear e_t e_s.
    iIntros (??) "Hp".
    iDestruct "Hp" as (??->->) "(#Hv2 & CI)".
    vsimp. final. vsimp. final.

    iExists _, _; by iFrame.
  Qed.

  Lemma instr_alloca_refl C id t nb align i_t i_s A_t A_s :
    instr_WF (INSTR_Alloca t nb align) ->
    code_inv C i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IId id, INSTR_Alloca t nb align))
    ⪯
    instr_conv (denote_instr (IId id, INSTR_Alloca t nb align))
    [{ (r_t, r_s),
        ∃ l_t l_s, code_inv C i_t i_s (l_t:: A_t) (l_s:: A_s)}].
  Proof.
    iIntros (WF) "CI". cbn.
    vsimp; Cut; vsimp. cbn in *.
    iApply (sim_expr_bupd_mono with "[] [CI]"); [ |
      iApply (alloca_refl_bij with "CI")]; cycle 1.
    { cbn; intros; apply non_void_b_non_void;
        destruct (non_void_b t); auto. }

    iIntros (??) "H".

    iDestruct "H" as (??->->??) "(#Hv & CI)".
    vsimp. final. vsimp.
    iDestruct (dval_rel_lift with "Hv") as "Hdv".

    mono: iApply (local_write_refl with "CI Hdv").

    iIntros (??) "Hp".
    iDestruct "Hp" as (??->->) "CI".
    final.
    iExists _, _; do 2 (iSplitL ""; first done).
    iExists _, _; by iFrame.
  Qed.

  Lemma instr_load_refl id volatile t ptr align i_t i_s A_t A_s:
    instr_WF (INSTR_Load volatile t ptr align) ->
    code_inv ∅ i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IId id, INSTR_Load volatile t ptr align))
    ⪯
    instr_conv (denote_instr (IId id, INSTR_Load volatile t ptr align))
    [{ (r_t, r_s), code_inv ∅ i_t i_s A_t A_s }].
  Proof.
    iIntros (WF) "CI".
    destruct ptr.

    cbn. vsimp. Cut.

    (* Process the value *)
    iApply sim_expr_mono; cycle 1.
    { iApply exp_conv_to_instr.
      iPoseProof (expr_logrel_refl (Some d) with "CI") as "He".
      iApply "He". }

    iIntros (??) "H".
    iDestruct "H" as (??->->) "(Hv & CI)".
    vsimp. Cut.

    mono: (iApply instr_conv_concretize_or_pick_strong) with "[CI]".

    iIntros (??) "H";
      iDestruct "H" as (??->->) "(#Hv' & %Hc & %Hc')".
    Simp.
    destruct (@dvalue_eq_dec dv_s DVALUE_Poison);
      [ iApply instr_conv_raiseUB | ].

    iDestruct (dval_rel_poison_neg_inv with "Hv'") as "%Hv".
    specialize (Hv n).
    destruct (@dvalue_eq_dec dv_t DVALUE_Poison) eqn: Hb; [ done | ].

    vsimp. Cut. vsimp.

    assert (Hwf_t : dtyp_WF t).
    { cbn in WF. apply andb_prop_elim in WF; destruct WF.
      destruct (dtyp_WF_b t) eqn: Ht; try done.
      apply dtyp_WF_b_dtyp_WF in Ht. done. }

    mono: iApply (load_refl with "CI Hv'").
    iIntros (??) "H".
    iDestruct "H" as (??->->) "(#Hv'' & CI)".
    final. vsimp.

    mono: iApply (local_write_refl with "CI").
    iIntros (??) "H".
    iDestruct "H" as (??->->) "CI".
    final.
    iExists _, _; do 2 (iSplitL ""; first done); by iFrame.
  Qed.

(* ------------------------------------------------------------------------ *)
  (* TODO: WIP repair *)
  Lemma instr_store_refl n volatile val ptr align i_t i_s A_t A_s:
    instr_WF (INSTR_Store volatile val ptr align) ->
    code_inv ∅ i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IVoid n, INSTR_Store volatile val ptr align))
    ⪯
    instr_conv (denote_instr (IVoid n, INSTR_Store volatile val ptr align))
    [{ (r_t, r_s), code_inv ∅ i_t i_s A_t A_s }].
  Proof.
    iIntros (WF) "CI".
    cbn in WF. destruct ptr, d, val; try solve [inversion WF].
    rewrite /instr_conv; rewrite !interp_bind.

    iApply sim_expr_bind; iApply sim_expr_mono; cycle 1.
    { iPoseProof (expr_logrel_refl (Some d) e0 with "CI") as "He"; eauto.
      iApply exp_conv_to_instr.
      iApply "He". }

    iIntros (??) "H".
    iDestruct "H" as (????) "(H & HL)".
    rewrite H H0 !bind_ret_l !interp_bind; clear H H0.

    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[HL] [H]") ;
      [ | by iApply instr_conv_concretize_or_pick_strong ].

    cbn; iIntros (??) "H".
    iDestruct "H" as (????) "(#Hv' & %Hc & %Hc')";
      rewrite H H0; clear H H0; rewrite !bind_ret_l.
    destruct (dvalue_has_dtyp_fun dv_s d) eqn :Hτ; cycle 1.
    { rewrite interp_bind interp_vis bind_bind.
      rewrite -bind_ret_l. iApply sim_expr_bind.
      iApply sim_expr_exception. }

    apply dvalue_has_dtyp_fun_sound in Hτ.
    iDestruct (dval_rel_dvalue_has_dtyp with "Hv'") as %Hτ'.
    specialize (Hτ' Hτ). rewrite -dvalue_has_dtyp_eq in Hτ'.
    rewrite Hτ'; cbn.

    rewrite !interp_bind.
    iApply sim_expr_bind; iApply sim_expr_mono; cycle 1.
    { iPoseProof (expr_logrel_refl (Some DTYPE_Pointer) e with "HL") as "He"; eauto.
      iApply exp_conv_to_instr.
      iApply "He". }

    iIntros (??) "H".
    iDestruct "H" as (????) "(H & HL)".
    rewrite H H0 !bind_ret_l !interp_bind; clear H H0.
    iApply sim_expr_bind.
    iApply (sim_expr_bupd_mono with "[HL] [H]") ;
      [ | by iApply instr_conv_concretize_or_pick_strong ].

    cbn; iIntros (??) "H"; iDestruct "H" as (????) "(#Hv''' & %Hc'' & %Hc''')";
      rewrite H H0; clear H H0; rewrite !bind_ret_l.

    destruct (@dvalue_eq_dec dv_s0 DVALUE_Poison);
      [ iApply instr_conv_raiseUB | ].
    iDestruct (dval_rel_poison_neg_inv with "Hv'''") as "%Hv".
    specialize (Hv n0).
    destruct (@dvalue_eq_dec dv_t0 DVALUE_Poison) eqn: Hb; [ done | ].
    setoid_rewrite interp_vis; cbn.
    simp_instr. rewrite !bind_trigger.
    iApply sim_expr_vis.

    iApply (sim_expr_bupd_mono with "[] [HL]"); cycle 1.
    { iApply store_must_be_addr; [ done | ].
      iIntros (????). rewrite H in Hc'''; rewrite H0 in Hc''.
      cbn in WF; apply andb_prop_elim in WF.
      destruct WF.

      iApply (store_refl with "HL"); eauto.
      { rewrite -dtyp_WF_b_dtyp_WF. destruct (dtyp_WF_b d); auto. }
      rewrite dvalue_has_dtyp_eq in Hτ'; auto. }

    cbn. iIntros (??) "H".
    iDestruct "H" as (????) "CI".
    rewrite H H0; setoid_rewrite bind_ret_l.
    do 2 rewrite interp_ret.
    iApply sim_expr_tau.
    iApply sim_expr_base. iExists _, _; by iFrame.
  Qed.

(* ------------------------------------------------------------------------ *)

(** *Compatibility lemmas *)

  (* LATER: See if the [id] generalization is also possible *)
  Theorem phi_compat bid bid' id ϕ ϕ' C A_t A_s:
    (let '(Phi dt  args )  := ϕ in
     let '(Phi dt' args')  := ϕ' in
     match Util.assoc bid args, Util.assoc bid' args' with
     | Some op, Some op' =>
         expr_logrel C
           (denote_exp (Some dt) op)
           (denote_exp (Some dt') op')
           A_t A_s
     | None, None => True
     | _ , _ => False
     end) -∗
    phi_logrel
       (denote_phi bid (id, ϕ))
       (denote_phi bid' (id, ϕ')) C A_t A_s.
  Proof.
    iIntros "He" (????) "H".
    iDestruct "H" as (Harg Hnd_t Hnd_s)
      "(Hdt&Hds&Hat&Has&Hv&Hs_t&Hs_s&#HWF&HC&Ha_t&Ha_s & #Hl)";
      destruct ϕ, ϕ'; cbn.
    rename t0 into t', args0 into args'.

    destruct (Util.assoc bid' args') eqn: H; [ | iApply exp_conv_raise].
    destruct (Util.assoc bid args) eqn: H'; last done.

    vsimp.

    iAssert (code_inv C i_t i_s A_t A_s) with
      "[Hdt Hds Hv HC Hat Has Hs_t Hs_s Ha_t Ha_s]" as "HI".
    { rewrite /code_inv; repeat iExists _; iFrame.
      iFrame "HWF".
      by iFrame "Hl". }
    iApply sim_expr_mono; [ | iApply "He"]; [ | done].
    iIntros (??) "H".
    iDestruct "H" as (????) "(Hv & CI)".
    rewrite H0 H1.

    vsimp.
    iApply sim_update_si.
    rewrite /update_si.

    iIntros (??) "SI".
    iDestruct "CI" as (??)
      "(Hd_t & Hd_s & Hs_t & Hs_s & HA & %Hc & Ha_t & Ha_s)".

    iFrame. iModIntro. final.

    iExists _,_,_. do 2 (iSplitL ""; [ try done | ]); iFrame; eauto.
    repeat iExists _; by iFrame.
  Qed.

  Lemma phi_list_compat bid (Φ Φ' : list (local_id * phi dtyp)) C i_t i_s A_t A_s:
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
        phi_logrel (denote_phi bid ϕ) (denote_phi bid ϕ') C A_t A_s) -∗
    code_inv C i_t i_s A_t A_s -∗
    instr_conv (map_monad (λ x, translate exp_to_instr ⟦ x ⟧Φ (bid)) Φ) ⪯
      instr_conv (map_monad (λ x, translate exp_to_instr ⟦ x ⟧Φ (bid)) Φ')
    [{ (r_t, r_s),
        ([∗ list] v_t; v_s ∈ r_t; r_s,
           ⌜v_t.1 = v_s.1⌝ ∗ uval_rel v_t.2 v_s.2)
            ∗ code_inv C i_t i_s A_t A_s }].
  Proof.
    iIntros "HΦ CI".
    rewrite /instr_conv; cbn.

    iInduction Φ as [] "IH" forall (Φ').
    { cbn.
      iPoseProof (big_sepL2_nil_inv_l with "HΦ") as "%Heq"; subst.
      rewrite interp_ret; cbn.
      iApply sim_expr_base; iExists _, _; iFrame; repeat (iSplitL ""; try done). }

    destruct a as (?&[]).
    iPoseProof (big_sepL2_cons_inv_l with "HΦ") as (???) "(He & HΦ)"; subst.
    destruct x2 as (l' & []).
    rename t0 into t', args0 into args', l2' into Φ'.
    iSpecialize ("IH" with "HΦ").
    cbn -[denote_phi].
    vsimp.

    iDestruct "CI" as (??)
        "(Hd_t & Hd_s & Hat & Has & #HWF &
        %Hargs & Hs_t & Hs_s & Hv & HC & Ha_t & Ha_s & %Hnd_t & %Hnd_s & #Hl)".

    iApply (sim_expr_bupd_mono with "[IH]"); [ | iApply "He"];
      try iFrame; eauto; cycle 1.

    cbn. iIntros (??) "H".
    iDestruct "H" as (?????) "(H & CI)".
    rewrite H H0. vsimp.

    iSpecialize ("IH" with "CI"). subst.
    iApply (sim_expr_bupd_mono with "[H]"); [ | iApply "IH"].
    cbn. iIntros (??) "H'".
    iDestruct "H'" as (????) "(H' & CI)". rewrite H H0.
    vsimp. final.
    iExists ((l0,v_t) :: r_t), ((l0, v_s) :: r_s); iFrame.
    iSplitL ""; done.
  Qed.

  Theorem phis_compat C bid (Φ Φ' : list (local_id * phi dtyp)) A_t A_s:
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
        phi_logrel (denote_phi bid ϕ) (denote_phi bid ϕ') C A_t A_s) -∗
    phis_logrel (denote_phis bid Φ) (denote_phis bid Φ') C A_t A_s.
  Proof.
    iIntros "HΦ" (??) "CI".
    iPoseProof (phi_list_compat with "HΦ CI") as "H".
    rewrite /denote_phis.
    vsimp. Cut.
    iApply sim_expr_bupd_mono ; [ | iApply "H"]; eauto; try iFrame.

    iIntros (??) "H".
    iDestruct "H" as (??->->) "(H & CI)".
    vsimp. setoid_rewrite instr_conv_ret.

    iInduction r_s as [] "IH" forall (r_t).
    { iDestruct (big_sepL2_nil_inv_r with "H") as %Hx; subst; cbn.
      vsimp. final.
      iExists _, _; iFrame; iSplitL ""; done. }

    iDestruct (big_sepL2_cons_inv_r with "H") as (???) "(CI1 & CI2)";
    destruct a, x1; subst; cbn.
    vsimp; Cut. vsimp.

    iDestruct "CI1" as "(%Hl & Hv)"; subst.

    iApply (sim_expr_bupd_mono with "[CI2]");
      [ | iApply (local_write_refl with "CI Hv")].

    cbn. iIntros (??) "H".
    iDestruct "H" as (??->->) "CI".
    final.
    iSpecialize ("IH" with "CI2 CI"). vsimp.
    iPoseProof (sim_expr_fmap_inv with "IH") as "Hf".
    Cut.

    iApply sim_expr_bupd_mono; [ | iApply "Hf"].

    iIntros (??) "H".
    iDestruct "H" as (????????) "H".
    rewrite H H0; apply eqitree_inv_Ret in H1, H2; subst.
    vsimp. final.
    iExists _, _; iFrame.
    iSplitL ""; done.
  Qed.

  Theorem phi_logrel_refl bid id ϕ C A_t A_s:
    ⊢ (phi_logrel (denote_phi bid (id, ϕ)) (denote_phi bid (id, ϕ)) C A_t A_s)%I.
  Proof.
    iApply phi_compat; destruct ϕ.
    destruct (Util.assoc bid args); try done.
    iApply expr_logrel_refl.
  Qed.

  Theorem phis_logrel_refl C bid (Φ : list (local_id * phi dtyp)) A_t A_s:
    (⊢ phis_logrel (denote_phis bid Φ) (denote_phis bid Φ) C A_t A_s)%I.
  Proof.
    iApply phis_compat.
    iInduction Φ as [ | ] "IH"; first done.
    cbn; iSplitL; [ destruct a; iApply phi_logrel_refl | done ].
  Qed.

  Theorem instr_logrel_refl id e A_t A_s:
    instr_WF e ->
    (⊢ instr_logrel id e id e ∅ A_t A_s)%I.
  Proof.
    iIntros (WF ??) "HI".
    destruct e eqn: He.
    all : destruct id; try iApply instr_conv_raise.
    { (* Comment *)
      rewrite /instr_conv interp_ret.
      iApply sim_expr_base.
      iExists _, _;
        do 2 (iSplitL ""; first done).
      iExists ∅, ∅. by cbn. }

    { (* Pure operations *)
      setoid_rewrite interp_bind.
      iApply sim_expr_bind.
      iApply exp_conv_to_instr.
      iApply (sim_expr_bupd_mono with "[] [HI]");
        [ | iApply expr_logrel_refl ]; eauto.
      cbn; iIntros (??) "H".
      iDestruct "H" as (????) "(Hv & Hc)".
      rewrite H H0 !bind_ret_l.
      do 2 rewrite interp_vis. simp_instr.
      rewrite !bind_vis.
      iApply sim_expr_vis.

      iApply (sim_expr_bupd_mono with "[] [Hc Hv]");
        [ | by iApply (local_write_refl with "Hc")].
      iIntros (??) "H".
      iDestruct "H" as (????) "HC".
      rewrite H1 H2.
      iModIntro.
      rewrite !bind_ret_l !interp_ret.
      iApply sim_expr_tau.
      iApply sim_expr_base.
      iExists _, _;
        do 2 (iSplitL ""; first done).

      by iExists ∅, ∅. }

    { iApply (sim_expr_bupd_mono with "[] [HI]");
        last iApply (instr_call_refl with "HI").
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _;
        do 2 (iSplitL ""; first done).

      by iExists ∅, ∅. }

   { iApply (sim_expr_bupd_mono with "[] [HI]");
        last iApply (instr_call_void_refl with "HI").
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _;
        do 2 (iSplitL ""; first done).
      by iExists ∅, ∅. }

    { iApply (sim_expr_bupd_mono with "[] [HI]");
        last
          iApply (instr_alloca_refl with "HI"); auto.
      cbn. iIntros (??) "H".
      iDestruct "H" as (??????) "H".
      iExists _, _;
        do 2 (iSplitL ""; first done).

      iExists [l_t], [l_s]; by cbn. }

    { iApply (sim_expr_bupd_mono with "[] [HI]");
        last iApply (instr_load_refl with "HI"); auto.
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _;
        do 2 (iSplitL ""; first done).
      by iExists ∅, ∅. }

    { iApply (sim_expr_bupd_mono with "[] [HI]");
        last iApply (instr_store_refl with "HI"); auto.
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _;
        do 2 (iSplitL ""; first done).
      by iExists ∅, ∅. }
  Qed.

  Theorem code_logrel_refl (c : code dtyp) A_t A_s:
    code_WF c ->
    ⊢ code_logrel c c ∅ A_t A_s.
  Proof.
    iIntros (Hwf ??) "HI"; cbn.
    rewrite /instr_conv. rewrite interp_bind.
    setoid_rewrite interp_ret.

    iInduction c as [| a l] "IHl" forall (i_t i_s A_t A_s);
                                    cbn; rewrite /instr_conv.
    { rewrite interp_ret bind_ret_l.
      iApply sim_expr_base; eauto.

      iExists _, _;
        do 2 (iSplitL ""; first done).
      iExists ∅, ∅; iFrame. }
    cbn in Hwf. apply andb_prop_elim in Hwf;
      destruct Hwf as (HW1 & HW2).

    repeat setoid_rewrite interp_bind.
    rewrite bind_bind.
    destruct a.
    iApply sim_expr_bind.
    iApply sim_expr_bupd_mono;
        [ | iApply instr_logrel_refl];
        cycle 1; eauto.

    iIntros (??) "CI".
    iDestruct "CI" as (????) "CI".
    rewrite H H0 !bind_ret_l. setoid_rewrite interp_ret. clear H H0.
    iApply sim_expr_bind.

    iDestruct "CI" as (??) "CI".
    iSpecialize ("IHl" $! HW2 with "CI").
    iPoseProof (sim_expr_fmap_inv with "IHl") as "H".
    iApply sim_expr_bind.

    iApply sim_expr_bupd_mono; [ | iApply "H"]; try done.

    iIntros (??) "H".
    iDestruct "H" as (????????) "H".
    rewrite H H0. rewrite !bind_ret_l.
    iApply sim_expr_base. rewrite !bind_ret_l.
    iApply sim_expr_base. iFrame.
    iDestruct "H" as (??) "H".

    iExists _, _;
      do 2 (iSplitL ""; first done).
    iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
    rewrite !app_assoc. done.
  Qed.

  Theorem term_logrel_refl ϒ C:
    (⊢ term_logrel ϒ ϒ C)%I.
  Proof.
    iIntros (??????) "HI".
    destruct ϒ eqn: Hϒ; try solve [iDestruct "WF" as "[]"]; cbn.
    5-8: iApply exp_conv_raise.
    5 : iApply exp_conv_raiseUB.
    { (* TERM_Ret *)
      destruct v.
      setoid_rewrite interp_bind; setoid_rewrite interp_ret.
      iApply sim_expr_bind. step_expr. iApply sim_expr_base; iFrame.
      iExists _, _; iSplitL ""; auto. }
    { (* TERM_Ret_void *)
      rewrite /exp_conv. rewrite interp_ret.
      iApply sim_expr_base.
      iExists _,_. do 2 (iSplitL ""; [ done |]). iFrame.
      iApply uval_rel_none. }
    { (* TERM_Br *)
      destruct v; step.
      step_expr. step.
      iApply (sim_expr_bupd_mono with "[HC]");
        [ | iApply (exp_conv_concretize_or_pick with "Hu") ].
      cbn.
      iIntros (??) "Hexp".
      iDestruct "Hexp" as (??->->) "Hv"; do 2 rewrite bind_ret_l.
      destruct dv_s; try iApply exp_conv_raise; [ | iApply exp_conv_raiseUB ].
      iDestruct (dval_rel_I1_inv with "Hv") as %->.
      destruct (DynamicValues.Int1.eq x DynamicValues.Int1.one).
      { rewrite interp_ret; iApply sim_expr_base.
        iModIntro. iExists _,_. do 2 (iSplitL ""; [ done | ]); by iFrame. }
      { rewrite interp_ret; iApply sim_expr_base.
        iModIntro. iExists _,_. do 2 (iSplitL ""; [ done | ]); by iFrame. } }
    { (* TERM_Br_1 *)
      rewrite /exp_conv interp_ret.
      iApply sim_expr_base.
      iExists _,_. do 2 (iSplitL ""; [ done | ]); by iFrame. }
  Qed.

  Theorem block_logrel_refl b A_t A_s:
    block_WF b ->
    (⊢ block_logrel b b ∅ A_t A_s)%I.
  Proof.
    iIntros (WF ???) "HI".
    rewrite /denote_block /instr_conv interp_bind.
    iApply sim_expr_bind; iApply sim_expr_mono;
      [ | by iApply phis_logrel_refl].
    iIntros (??) "H".
    iDestruct "H" as (????) "HI".
    rewrite H H0; do 2 rewrite bind_ret_l; clear H H0.
    rewrite interp_bind.
    unfold block_WF in WF.
    apply andb_prop_elim in WF. destruct WF.
    iApply sim_expr_bind; iApply sim_expr_mono;
      [ | iApply code_logrel_refl ]; eauto.

    iIntros (??) "H".
    iDestruct "H" as (??????) "Hi".
    rewrite H1 H2; do 2 rewrite bind_ret_l; clear H1 H2.
    iApply sim_expr_mono; cycle 1.
    { rewrite interp_translate.
      rewrite (eq_itree_interp _ _ eq2_exp_to_L0); last done.
      iApply term_logrel_refl; auto. }
    iIntros (??) "H".
    iDestruct "H" as (????) "(HI & H)".
    iExists _,_. rewrite H1 H2.
    do 2 (iSplitL ""; [ done | ]). iFrame.
    by iExists _, _.
  Qed.

  Theorem ocfg_logrel_refl (c : CFG.ocfg dtyp) b1 b2 A_t A_s:
    ocfg_WF c ->
    (⊢ ocfg_logrel c c ∅ A_t A_s b1 b2)%I.
  Proof.
    iIntros (WF ??) "CI".
    rewrite /ocfg_WF in WF.
    rewrite /denote_ocfg.
    unfold CategoryOps.iter, CategoryKleisli.Iter_Kleisli,
      Basics.iter, MonadIter_itree.

    epose proof
      (@interp_iter' _ _ instrE_conv _ _
      (λ '(bid_from, bid_src),
        match CFG.find_block c bid_src with
        | Some block_src =>
            Monad.bind (denote_block block_src bid_from)
              (λ bd : block_id + uvalue,
                  match bd with
                  | inl bid_target => Monad.ret (inl (bid_src, bid_target))
                  | inr dv => Monad.ret (inr (inr dv))
                  end)
        | None => Monad.ret (inr (inl (bid_from, bid_src)))
        end)
      (λ i, interp instrE_conv
      (let
       '(bid_from, bid_src) := i in
        match CFG.find_block c bid_src with
        | Some block_src =>
            Monad.bind (denote_block block_src bid_from)
              (λ bd : block_id + uvalue,
                 match bd with
                 | inl bid_target => Monad.ret (inl (bid_src, bid_target))
                 | inr dv => Monad.ret (inr (inr dv))
                 end)
        | None => Monad.ret (inr (inl (bid_from, bid_src)))
        end)) _ (b1, b2)).
    Unshelve. 2 : intros; reflexivity.
    eapply EqAxiom.bisimulation_is_eq in H.
    rewrite /instr_conv. rewrite H.

    iApply sim_expr'_tau_inv.
    { iModIntro. iIntros (??). iSplitL.
      - iIntros "(Hb & H & H')"; iFrame.
      - iIntros "(H & H')".
        iDestruct "H'" as (????) "H''".
        iFrame.
        iSplitL "".
        { rewrite /base. eauto. }
        eauto. }

    match goal with
    | |- context[sim_expr' _
          (Tau (ITree.iter ?body1 ?index1)) (Tau (ITree.iter ?body2 ?index2))] =>
        change (Tau (ITree.iter body1 index1)) with (guarded_iter' _ _ _ body1 index1);
        change (Tau (ITree.iter body2 index2)) with (guarded_iter' _ _ _ body2 index2)
    end.

    iApply (sim_expr_guarded_iter' _ _ (fun x y => ⌜x = y⌝
       ∗ code_inv_post ∅ i_t i_s A_t A_s)%I
             with "[] [CI]"); cycle 1.
    { iSplitL ""; first done.
      by iExists ∅, ∅. }
    iModIntro.
    iIntros (??) "(%Heq & CI)"; rewrite Heq. destruct i_s0; clear Heq.
    iDestruct "CI" as (??) "CI".
    iApply sim_expr_lift.

    destruct (CFG.find_block c b0) eqn: Hb0.
    { rewrite interp_bind. iApply sim_expr_bind.
      iApply sim_expr_bupd_mono; [ | iApply block_logrel_refl]; eauto; cycle 1.
      { unfold CFG.find_block in Hb0.
        apply find_some in Hb0. destruct Hb0.
        destruct (forallb block_WF c) eqn: HWF; try done.
        rewrite forallb_forall in HWF.
        specialize (HWF _ H0). destruct (block_WF b3); try done. }

      iIntros (??) "H".
      iDestruct "H" as (????) "(H & l)".
      iDestruct "H" as (??) "H".
      rewrite H0 H1; do 2 rewrite bind_ret_l.
      destruct r_t, r_s; try (iDestruct "l" as %Heq; inversion Heq).
      - rewrite !interp_ret.
        iApply sim_expr_base; iLeft. iModIntro; subst.
        iExists (b0, b5), (b0, b5); iFrame; eauto.
        do 3 (iSplitL ""; first done).
        rewrite !app_assoc.
        by iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
      - do 2 rewrite interp_ret.
        iApply sim_expr_base; iRight.
        iDestruct "l" as "#l".
        iModIntro; subst. iFrame.
        repeat iExists _; do 2 (iSplitL ""; eauto).
        iSplitL.
        { iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
          by rewrite !app_assoc. }

        repeat iExists _; do 2 (iSplitL ""; eauto); done. }

    rewrite interp_ret.
    iApply sim_expr_base; iRight. iFrame.
    do 2 iExists _; do 2 (iSplitL ""; eauto).
    iSplitL "CI".
    { iExists nA_t, nA_s; by iFrame. }

    repeat iExists _; do 2 (iSplitL ""; eauto); done.
  Qed.

  Theorem cfg_logrel_refl c A_t A_s:
    cfg_WF c ->
    (⊢ cfg_logrel c c ∅ A_t A_s)%I.
  Proof.
    iIntros (WF ??) "CI";
    setoid_rewrite interp_bind. destruct c; cbn.
    iApply sim_expr'_bind; iApply (sim_expr'_bupd_mono); cycle 1.
    { cbn; iApply ocfg_logrel_refl; auto. }
    iIntros (??) "(H & HC)".
    iDestruct "H" as (??) "CI".
    iDestruct "HC" as (????) "HC".
    rewrite H H0. do 2 rewrite bind_ret_l.
    destruct v_t as [(?&?) | ], v_s as [(?&?) |];
      try (iDestruct "HC" as "%Hv"; inversion Hv); cycle 1.
    { do 2 rewrite interp_ret. iApply sim_expr'_base.
      iExists _,_.
      do 2 (iSplitL ""; [ done | ]). iFrame.
      by iExists nA_t,nA_s. }

    (* absurd *)
    rewrite /raise.
    rewrite interp_bind. iApply sim_expr_lift.
    iApply sim_expr_bind.
    unfold trigger. rewrite interp_vis.
    iApply sim_expr_bind.
    cbn. rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1.
    simp call_conv.
    iApply sim_expr_exception.
  Qed.

  Theorem fun_logrel_refl f:
    fun_WF f ->
    (⊢ fun_logrel f f ∅)%I.
  Proof.
    iIntros (WF i_t i_s args_t args_s Hlen) "Hs_t Hs_s Hv HC".

    rewrite /denote_function; cbn -[denote_cfg].
    destruct (length (df_args f) =? length args_s) eqn : Hlen_args; cycle 1.
    { rewrite bind_bind bind_vis.

      setoid_rewrite interp_bind.
      setoid_rewrite interp_vis; rewrite bind_trigger.
      iApply sim_expr_lift.
      iApply sim_expr_exception_vis. }

    rewrite /val_rel.Forall2.
    iDestruct (big_sepL2_length  with "Hv") as %Hargs.
    assert (Hlen_f: length (df_args f) =? length args_t = true).
    { apply PeanoNat.Nat.eqb_eq; subst.
      apply PeanoNat.Nat.eqb_eq in Hlen_args; rewrite Hlen_args; done. }
    rewrite Hlen_f.

    rewrite /L0'expr_conv !interp_bind !interp_ret !bind_ret_l.
    setoid_rewrite interp_bind;
    rewrite !interp_vis !bind_bind; cbn -[denote_cfg].
    setoid_rewrite interp_ret.
    setoid_rewrite interp_bind.
    setoid_rewrite interp_vis.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_ret.
    do 2 rewrite -bind_bind.
    rewrite -(bind_bind (Vis (call_conv () (subevent () MemPush)) (λ x : (), Ret x))).
    rewrite -(bind_bind (r <- (Vis (call_conv () (subevent () MemPush)) (λ x : (), Ret x)) ;; Tau (Ret r))).
    iApply sim_expr'_bind.
    rewrite !bind_bind.

    rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1.
    simp L0'_conv.

    iCombine "Hs_t Hs_s" as "Hst".
    apply PeanoNat.Nat.eqb_eq in Hlen_args, Hlen_f.
    apply andb_prop_elim in WF. destruct WF.
    assert (Hnd: NoDup_b (df_args f) = true).
    { destruct (NoDup_b (df_args f)); done. }
    apply NoDup_b_NoDup in Hnd. clear H. rename H0 into WF.

    iApply (sim_expr'_bupd_mono with "[Hv HC]");
      [ | iApply sim_expr_lift; iApply (sim_push_frame' with "Hst") ];
      [ | rewrite combine_fst | rewrite combine_fst ]; eauto.

    cbn.
    iIntros (??) "H".
    iDestruct "H" as (??????) "(Hs_t & Hs_s & Ha_t & Ha_s & Hd_t & Hd_s & Harg_t & Harg_s)".
    rewrite H H0; clear H H0.

    rewrite !bind_ret_l !bind_tau.
    iApply sim_expr'_tau; rewrite !bind_ret_l.

    rewrite interp_bind.

    (* Denote CFG *)
    iApply sim_expr'_bind.
    iApply spec.instr_to_L0'.

    iDestruct "Hv" as "#Hv".
    iApply sim_expr'_bupd_mono;
      [ | iApply (cfg_logrel_refl with
          "[HC Hs_t Hs_s Ha_t Ha_s Hd_t Hd_s Harg_t Harg_s]") ];
      eauto; cycle 1.
    { Unshelve.
      4 : exact (j_t :: i_t). 4 : exact (j_s :: i_s).
      2 : exact ∅. 2 : exact ∅.
      iExists (combine (df_args f) args_t),
              (combine (df_args f) args_s); iFrame.
      iSplitL "".
      { iPureIntro; eauto. }

      iSplitL "".
      { rewrite !combine_fst; auto. }
      { rewrite !combine_snd; eauto; iFrame.
        rewrite /val_rel.Forall2; iFrame "Hv".
        cbn.
        by rewrite NoDup_nil. } }

    clear e_t0 e_s0.

    iIntros (e_t e_s) "H".
    iDestruct "H" as (????) "(#Hr & HC)".
    rewrite H H0 !bind_ret_l.
    iDestruct "HC" as (??) "HC".

    iDestruct "HC" as (??) "CI".
    rewrite !app_nil_r.

    iDestruct "CI" as
      "(Hd_t&Hd_s&Hs_t&Hs_s&#HWF&%Heq&Hargs_t&Hargs_s&#Huv&HC&Ha_t&Ha_s&#Hbij)".
    iApply sim_expr_lift.

    iApply sim_update_si; iModIntro.
    iIntros (??) "SI".
    iDestruct (state_interp_WF with "SI") as "%WF_S".
    iFrame.

    repeat setoid_rewrite interp_bind.
    setoid_rewrite interp_ret.
    rewrite !interp_vis !bind_bind.
    setoid_rewrite interp_ret.
    setoid_rewrite bind_tau;
    setoid_rewrite bind_ret_l.
    setoid_rewrite interp_vis.
    setoid_rewrite bind_bind.
    setoid_rewrite interp_ret.
    setoid_rewrite bind_tau.
    setoid_rewrite bind_ret_l.
    setoid_rewrite <- bind_tau.
    rewrite -!bind_bind.
    iApply sim_expr_bind.
    iApply sim_expr_bupd_mono; cycle 1.
    { iDestruct "Hbij" as (Hnd_t Hnd_s) "Hbij".
      iPoseProof (sim_pop_frame_bij with "Hs_t Hs_s Ha_t Ha_s HC Hbij") as "H";
        eauto.
      { intros. cbn in H1.
        assert (length i_s > 0)%Z by lia.
        specialize (Hlen H2). cbn; lia. } }

    iIntros (??) "H".
    iDestruct "H" as (????) "(HC & Hst & Hss)".
    rewrite H1 H2 !bind_ret_l.
    iApply sim_expr_tau; iApply sim_expr_base.
    iFrame. iExists _, _; iFrame "Hr"; done.
  Qed.

  Theorem fundefs_logrel_refl r Attr:
    ⌜fundefs_WF r Attr⌝ -∗
    fundefs_logrel r r Attr Attr ∅.
  Proof.
    rewrite /fundefs_logrel.
    iInduction r as [ | f l] "H" forall (Attr).
    { iIntros. done. }
    { iIntros (WF).
      iIntros (i f_t' f_s'
        addr_t addr_s attr Hlu_t Hlu_s Hattr_t Hattr_s) "#Hrel".
      iIntros (i_t i_s args_t args_s Hlen) "Hs_t Hs_s #Hargs HC".
      iIntros (τ Hcall).
      pose proof fundefs_WF_cons_inv. destruct Attr.
      { clear -Hattr_t. set_solver. }
      pose proof (fundefs_WF_cons_inv _ _ _ _ WF) as HWF_t.
      destruct HWF_t as (?&?).

      destruct i.
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        inversion Hlu_t; subst.
        inversion Hlu_s; subst.
        inversion Hattr_t; subst.
        rewrite /fundefs_WF in H0.
        cbn in H0.
        do 2 rewrite andb_true_r in H0.
        iApply (fun_logrel_refl f_s' H0 $!
                  i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC"). }
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        iSpecialize ("H" $! Attr H1 i f_t' f_s' _ _ attr Hlu_t Hlu_s Hattr_t Hattr_s with "Hrel").
        iSpecialize ("H" $! i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC").
        by iApply "H". } }
  Qed.

  Theorem mcfg_definitions_refl (defs : CFG.mcfg dtyp) g_t g_s:
    (CFG_WF defs g_t g_s ->
     ⊢ target_globals g_t -∗
     source_globals g_s -∗
     mcfg_definitions defs ⪯ mcfg_definitions defs
      [[ fun e_t e_s =>
          ∃ r_t r_s,
            ⌜e_t = Ret r_t⌝ ∗ ⌜e_s = Ret r_s⌝ ∗
            ⌜Permutation r_t.*1
              (codomain (filter_keys g_t (CFG_names defs)))⌝ ∗
            ⌜Permutation r_s.*1
              (codomain (filter_keys g_s (CFG_names defs)))⌝ ∗
            ([∗ list] i ↦ v_t; v_s ∈ r_t.*1;r_s.*1, dval_rel v_t v_s) ∗
            ⌜Leaf.Leaf r_t (mcfg_definitions defs)⌝ ∗
            ⌜Leaf.Leaf r_s (mcfg_definitions defs)⌝ ∗
            fundefs_rel_WF r_t r_s
                (CFG_attributes defs) (CFG_attributes defs) ∗
            ⌜fundefs_WF r_t (CFG_attributes defs)⌝ ∗
            ⌜fundefs_WF r_s (CFG_attributes defs)⌝ ∗
            □ (fundefs_logrel r_t r_s (CFG_attributes defs) (CFG_attributes defs) ∅) ]])%I.
  Proof.
    rewrite /mcfg_definitions. iIntros (WF) "#Hg_t #Hg_s". destruct defs.
    cbn in *. rewrite /CFG_WF /CFG_names in WF;
      cbn -[defs_names] in WF. destructb.

    rename H into Hlen, H0 into Hdup, H1 into defs, H2 into Hattr,
      H3 into Hdom_t, H4 into Hdom_s, H5 into NoDup_t, H6 into NoDup_s.

    iApply sim_expr_lift.
    iInduction m_definitions as [ | f l] "H"
        forall (m_declarations Hlen Hdup defs Hattr Hdom_t Hdom_s NoDup_t NoDup_s).
    { cbn. iApply sim_expr_base.
      iExists _, _.
      do 2 (iSplitL ""; [ done | ]).
      rewrite /fundefs_logrel. cbn.
      destruct m_declarations; try done; cbn.
      iSplitL "".
      { by rewrite filter_keys_nil codomain_empty. }
      iSplitL "".
      { by rewrite filter_keys_nil codomain_empty. }
      do 3 (iSplitL ""; [ iPureIntro; by constructor | ]).
      iSplitL "".
      { iSplitL ""; auto. iIntros. inv H. }
      do 2 (iSplitL ""; first done).
      iModIntro. iIntros. inversion H0. }

    { cbn. rewrite /CFG_WF; cbn.
      remember (
        b <- address_one_function f;; bs <- map_monad address_one_function l;; Ret (b :: bs)).
      rewrite { 3 4 } Heqi.
      setoid_rewrite bind_bind. rewrite bind_trigger.
      pose proof (global_names_cons_lookup _ _ _  Hdom_t) as Hlu_t.
      destruct Hlu_t as (?&Hlu_t).
      pose proof (global_names_cons_lookup _ _ _  Hdom_s) as Hlu_s.
      destruct Hlu_s as (?&Hlu_s).

      iApply sim_expr_vis; iApply sim_expr_mono;
        [ | iApply (sim_global_read1 with "Hg_t Hg_s") ]; eauto.

      iIntros (??) "HR". iDestruct "HR" as (????) "(#HR & %Hx1 & %Hx2)"; subst.
      rewrite H H0; repeat rewrite bind_ret_l.
      destruct m_declarations; inv Hlen.
      symmetry in H2.

      cbn in Hdup. nodup.
      apply Forall_cons in defs, Hattr; destructb.
      rewrite /defs_names in Hdup. cbn in Hdup.
      nodup. rename H7 into Hnd.
      rename H3 into Hattr, H1 into Hdc_attr.
      iSpecialize ("H" $! m_declarations eq_refl Hnd).
      assert (Hdom_t' := Hdom_t); assert (Hdom_s' := Hdom_s).
      apply contains_keys_cons_inv in Hdom_t, Hdom_s.
      destruct Hdom_t as (Hd_t & Hdom_t).
      destruct Hdom_s as (Hd_s & Hdom_s).

      iApply sim_expr_bind; iApply (sim_expr_mono with "[HR]");
        [ | iApply "H" ]; eauto; cycle 1.
      (* NoDup [target] *)
      { iPureIntro. eapply nodup_codomain_cons_inv; eauto.
        apply NoDup_cons; eauto. }
      { iPureIntro. eapply nodup_codomain_cons_inv; eauto.
        apply NoDup_cons; eauto. }

      iIntros (??) "HI".
      iDestruct "HI" as (??????) "(#Hv & HI)".
      iDestruct "HI" as (??) "#HI"; subst.
      repeat rewrite bind_ret_l.
      iApply sim_expr_base.
      iExists _, _.
      do 2 (iSplitL ""; [ done | ]); iFrame "Hv".
      iFrame "HR".

      iSplitL ""; [iPureIntro | ].
      { cbn.
        eapply mcfg_defs_keys_extend; eauto. }
      iSplitL ""; [iPureIntro | ].
      { eapply mcfg_defs_keys_extend; eauto. }

      iSplitL ""; [iPureIntro | ].
      { subst. rewrite bind_bind bind_trigger.
        eapply Leaf.Leaf_Vis.
        setoid_rewrite bind_ret_l.
        eapply Leaf.Leaf_bind; [ apply H9 | ].
        by econstructor. }

      iSplitL ""; [iPureIntro | ].
      { subst. rewrite bind_bind bind_trigger.
        eapply Leaf.Leaf_Vis.
        setoid_rewrite bind_ret_l.
        eapply Leaf.Leaf_bind; [ apply H10 | ].
        by econstructor. }

      iSplitL "".
      (* fundefs rel *)
      { iDestruct "HI" as "(HI & _)".
        iClear "H".
        iSplitL "".
        { iIntros (????).
          apply lookup_cons_Some in H1. destruct H1.
          { destruct H1; subst; cbn.
            iExists _, _; base; inv H3; iFrame "HR"; base.
            rewrite Hdc_attr H4; done. }
          { destruct H1. cbn.
            iDestruct "HI" as "(H1 & H2)".
            iSpecialize ("H1" $! (i - 1) _ _ H3).
            iDestruct "H1" as (???) "(#Hdv & H1)".
            iDestruct "H1" as (???) "%H'".
            iExists _, _; cbn; base.
            rewrite lookup_cons_Some.
            iSplitL ""; first (iRight; eauto); iFrame "Hdv".
            rewrite lookup_cons_Some.
            do 2 (iSplitL ""; first (iRight; eauto)). done. } }
        { iDestruct "HI" as "(H1 & %H2')".
          iIntros (??). destruct i; cbn in a; inv a.
          cbn. specialize (H2' _ H3). rewrite H2' H3; done. } }

      iSplitL "".
      { iDestruct "HI" as "(H1 & %Ha & %Ha' & _)". iClear "H".
        cbn. rewrite /fundefs_WF.
        do 2 rewrite andb_True; cbn -[NoDup_b].
        rewrite /fundefs_WF in Ha. resolveb.
        iPureIntro. repeat split; eauto.
        { rewrite H1. by rewrite Nat.eqb_refl. }
        { rewrite andb_True. split; auto.
          apply forallb_True; auto. }
        { apply Is_true_true_2. apply NoDup_b_NoDup.
          eapply NoDup_mcfg_extend; eauto. } }

      iSplitL "".
      { iDestruct "HI" as "(H1 & %Ha & %Ha' & _)". iClear "H".
        cbn. rewrite /fundefs_WF.
        do 2 rewrite andb_True; cbn -[NoDup_b].
        rewrite /fundefs_WF in Ha'. resolveb.
        iPureIntro. repeat split; eauto.
        { rewrite H1. by rewrite Nat.eqb_refl. }
        { rewrite andb_True. split; auto.
          apply forallb_True; auto. }
        { apply Is_true_true_2. apply NoDup_b_NoDup.
          eapply NoDup_mcfg_extend; eauto. } }

      iModIntro. clear Hlu_t Hlu_s.
      iIntros (i f_t' f_s' addr_t
                 addr_s attr Hlu_t Hlu_s Hattr_t Hattr_s) "#Hrel".
      iIntros (i_t i_s args_t args_s Hlen)
        "Hs_t Hs_s #Hargs HC".
      destruct i.
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        inv Hlu_t; inv Hlu_s.
        apply Is_true_true_2 in H4.

        iApply (fun_logrel_refl f_s' H4 $!
                  i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC"). }
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        iDestruct "HI" as "(H1 & %Ha & %Ha' & HI)".
        iSpecialize ("HI" $! i f_t' f_s' _ _ attr Hlu_t Hlu_s Hattr_t Hattr_s with "Hrel").
        iSpecialize ("HI" $! i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC").
        by iApply "HI". } }
  Qed.

  Theorem mcfg_definitions_refl' (defs : CFG.mcfg dtyp) g_t g_s:
    (CFG_WF defs g_t g_s ->
     ⊢ target_globals g_t -∗
     source_globals g_s -∗
     mcfg_definitions defs ⪯ mcfg_definitions defs
      [[ fun e_t e_s =>
          ∃ r_t r_s g_t' g_s',
            ⌜e_t = Ret r_t⌝ ∗ ⌜e_s = Ret r_s⌝ ∗
            ⌜Permutation r_t.*1
              (codomain (filter_keys g_t (CFG_names defs)))⌝ ∗
            ⌜Permutation r_s.*1
              (codomain (filter_keys g_s (CFG_names defs)))⌝ ∗
            ([∗ list] i ↦ v_t; v_s ∈ r_t.*1;r_s.*1, dval_rel v_t v_s) ∗
            ⌜Leaf.Leaf (g_t', r_t) (interp_global (mcfg_definitions defs) g_t)⌝ ∗
            ⌜Leaf.Leaf (g_s', r_s) (interp_global (mcfg_definitions defs) g_s)⌝ ∗
            fundefs_rel_WF r_t r_s
                (CFG_attributes defs) (CFG_attributes defs) ∗
            ⌜fundefs_WF r_t (CFG_attributes defs)⌝ ∗
            ⌜fundefs_WF r_s (CFG_attributes defs)⌝ ∗
            □ (fundefs_logrel r_t r_s (CFG_attributes defs) (CFG_attributes defs) ∅) ]])%I.
  Proof.
    rewrite /mcfg_definitions. iIntros (WF) "#Hg_t #Hg_s". destruct defs.
    cbn in *. rewrite /CFG_WF /CFG_names in WF;
      cbn -[defs_names] in WF. destructb.

    rename H into Hlen, H0 into Hdup, H1 into defs, H2 into Hattr,
      H3 into Hdom_t, H4 into Hdom_s, H5 into NoDup_t, H6 into NoDup_s.

    iApply sim_expr_lift.
    iInduction m_definitions as [ | f l] "H"
        forall (m_declarations Hlen Hdup defs Hattr Hdom_t Hdom_s NoDup_t NoDup_s).
    { cbn. iApply sim_expr_base.
      iExists _, _, _, _.
      do 2 (iSplitL ""; [ done | ]).
      rewrite /fundefs_logrel. cbn.
      destruct m_declarations; try done; cbn.
      iSplitL "".
      { by rewrite filter_keys_nil codomain_empty. }
      iSplitL "".
      { by rewrite filter_keys_nil codomain_empty. }

      iSplitL ""; first done.
      iSplitL "".
      { iPureIntro. rewrite interp_global_ret; constructor; eauto. }

      iSplitL "".
      { iPureIntro. rewrite interp_global_ret; constructor; eauto. }
      iSplitL "".
      { iSplitL ""; auto. iIntros. inv H. }
      do 2 (iSplitL ""; first done).
      iModIntro. iIntros. inversion H0. }

    { cbn. rewrite /CFG_WF; cbn.
      remember (
        b <- address_one_function f;; bs <- map_monad address_one_function l;; Ret (b :: bs)).
      rewrite { 3 4 } Heqi.
      setoid_rewrite bind_bind. rewrite bind_trigger.
      pose proof (global_names_cons_lookup _ _ _  Hdom_t) as Hlu_t.
      destruct Hlu_t as (?&Hlu_t).
      pose proof (global_names_cons_lookup _ _ _  Hdom_s) as Hlu_s.
      destruct Hlu_s as (?&Hlu_s).

      iApply sim_expr_vis; iApply sim_expr_mono;
        [ | iApply (sim_global_read1 with "Hg_t Hg_s") ]; eauto.

      iIntros (??) "HR". iDestruct "HR" as (????) "(#HR & %Hx1 & %Hx2)"; subst.
      rewrite H H0; repeat rewrite bind_ret_l.
      destruct m_declarations; inv Hlen.
      symmetry in H2.

      cbn in Hdup. nodup.
      apply Forall_cons in defs, Hattr; destructb.
      rewrite /defs_names in Hdup. cbn in Hdup.
      nodup. rename H7 into Hnd.
      rename H3 into Hattr, H1 into Hdc_attr.
      iSpecialize ("H" $! m_declarations eq_refl Hnd).
      assert (Hdom_t' := Hdom_t); assert (Hdom_s' := Hdom_s).
      apply contains_keys_cons_inv in Hdom_t, Hdom_s.
      destruct Hdom_t as (Hd_t & Hdom_t).
      destruct Hdom_s as (Hd_s & Hdom_s).

      iApply sim_expr_bind; iApply (sim_expr_mono with "[HR]");
        [ | iApply "H" ]; eauto; cycle 1.
      (* NoDup [target] *)
      { iPureIntro. eapply nodup_codomain_cons_inv; eauto.
        apply NoDup_cons; eauto. }
      { iPureIntro. eapply nodup_codomain_cons_inv; eauto.
        apply NoDup_cons; eauto. }

      iIntros (??) "HI".
      iDestruct "HI" as (????????) "(#Hv & HI)".
      iDestruct "HI" as (??) "#HI"; subst.
      repeat rewrite bind_ret_l.
      iApply sim_expr_base.
      iExists _, _, _,_.
      do 2 (iSplitL ""; [ done | ]); iFrame "Hv".
      iFrame "HR".

      iSplitL ""; [iPureIntro | ].
      { cbn.
        eapply mcfg_defs_keys_extend; eauto. }
      iSplitL ""; [iPureIntro | ].
      { eapply mcfg_defs_keys_extend; eauto. }

      iSplitL ""; [iPureIntro | ].
      { do 2 setoid_rewrite interp_global_bind.
        rewrite bind_bind.
        rewrite interp_global_trigger. cbn. rewrite Hlu_t.
        rewrite bind_ret_l.
        rewrite interp_global_ret.
        setoid_rewrite bind_ret_l.
        rewrite interp_global_bind.
        eapply Leaf.Leaf_bind; [ apply H9 | ].
        cbn. rewrite interp_global_ret.
        by econstructor. }

      iSplitL ""; [iPureIntro | ].
      { do 2 setoid_rewrite interp_global_bind.
        rewrite bind_bind.
        rewrite interp_global_trigger. cbn. rewrite Hlu_s.
        rewrite bind_ret_l.
        rewrite interp_global_ret.
        setoid_rewrite bind_ret_l.
        rewrite interp_global_bind.
        eapply Leaf.Leaf_bind; [ apply H10 | ].
        cbn. rewrite interp_global_ret.
        by econstructor. }

      iSplitL "".
      (* fundefs rel *)
      { iDestruct "HI" as "(HI & _)".
        iClear "H".
        iSplitL "".
        { iIntros (????).
          apply lookup_cons_Some in H1. destruct H1.
          { destruct H1; subst; cbn.
            iExists _, _; base; inv H3; iFrame "HR"; base.
            rewrite Hdc_attr H4; done. }
          { destruct H1. cbn.
            iDestruct "HI" as "(H1 & H2)".
            iSpecialize ("H1" $! (i - 1) _ _ H3).
            iDestruct "H1" as (???) "(#Hdv & H1)".
            iDestruct "H1" as (???) "%H'".
            iExists _, _; cbn; base.
            rewrite lookup_cons_Some.
            iSplitL ""; first (iRight; eauto); iFrame "Hdv".
            rewrite lookup_cons_Some.
            do 2 (iSplitL ""; first (iRight; eauto)). done. } }
        { iDestruct "HI" as "(H1 & %H2')".
          iIntros (??). destruct i; cbn in a; inv a.
          cbn. specialize (H2' _ H3). rewrite H2' H3; done. } }

      iSplitL "".
      { iDestruct "HI" as "(H1 & %Ha & %Ha' & _)". iClear "H".
        cbn. rewrite /fundefs_WF.
        do 2 rewrite andb_True; cbn -[NoDup_b].
        rewrite /fundefs_WF in Ha. resolveb.
        iPureIntro. repeat split; eauto.
        { rewrite H1. by rewrite Nat.eqb_refl. }
        { rewrite andb_True. split; auto.
          apply forallb_True; auto. }
        { apply Is_true_true_2. apply NoDup_b_NoDup.
          eapply NoDup_mcfg_extend; eauto. } }

      iSplitL "".
      { iDestruct "HI" as "(H1 & %Ha & %Ha' & _)". iClear "H".
        cbn. rewrite /fundefs_WF.
        do 2 rewrite andb_True; cbn -[NoDup_b].
        rewrite /fundefs_WF in Ha'. resolveb.
        iPureIntro. repeat split; eauto.
        { rewrite H1. by rewrite Nat.eqb_refl. }
        { rewrite andb_True. split; auto.
          apply forallb_True; auto. }
        { apply Is_true_true_2. apply NoDup_b_NoDup.
          eapply NoDup_mcfg_extend; eauto. } }

      iModIntro. clear Hlu_t Hlu_s.
      iIntros (i f_t' f_s' addr_t
                 addr_s attr Hlu_t Hlu_s Hattr_t Hattr_s) "#Hrel".
      iIntros (i_t i_s args_t args_s Hlen)
        "Hs_t Hs_s #Hargs HC".
      destruct i.
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        inv Hlu_t; inv Hlu_s.
        apply Is_true_true_2 in H4.

        iApply (fun_logrel_refl f_s' H4 $!
                  i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC"). }
      { cbn in Hlu_t, Hlu_s, Hattr_t, Hattr_s.
        iDestruct "HI" as "(H1 & %Ha & %Ha' & HI)".
        iSpecialize ("HI" $! i f_t' f_s' _ _ attr Hlu_t Hlu_s Hattr_t Hattr_s with "Hrel").
        iSpecialize ("HI" $! i_t i_s args_t args_s Hlen with "Hs_t Hs_s Hargs HC").
        by iApply "HI". } }
  Qed.

End fundamental.
