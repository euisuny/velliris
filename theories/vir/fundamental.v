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
  vir spec
  logical_relations
  fundamental_exp
  tactics
  vir_sim_properties
.
(* From velliris.utils Require Import no_event. *)

Set Default Proof Using "Type*".

Import ListNotations.

(* TODO: Move *)
Tactic Notation "mono:" tactic(tac) :=
  iApply sim_expr_bupd_mono; [ | tac; eauto ];
  try (iIntros (??) "HΦ"; iDestruct "HΦ" as (??->->) "HΦ").

Tactic Notation "mono:" tactic(tac) "with" constr(hyps) :=
  iApply (sim_expr_bupd_mono with hyps); [ | tac; eauto ];
  try (iIntros (??) "HΦ"; iDestruct "HΦ" as (??->->) "HΦ").

Ltac vfinal :=
  final;
  repeat iExists _;
  repeat (iSplitL ""; first (iPureIntro; done));
  iFrame; try done.

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
  Proof with vsimp.
    iIntros "CI".
    iInduction e as [] "IHl".
    { cbn... Base.
      iExists _,_; do 2 (iSplitL ""; [done |]); iFrame; done. }
    { cbn...
      destruct a. Cut...

      mono: iApply (expr_logrel_refl with "CI").

      iDestruct "HΦ" as "(Hv & CI)"...

      Cut; iSpecialize ("IHl" with "CI").

      mono: iApply "IHl" with "[Hv]".

      iDestruct "HΦ" as "(CI & H)"; vfinal. }
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
  Proof with vsimp.
    iIntros "CI".
    cbn; destruct fn...
    Cut.
    mono: iApply (denote_exp_map_monad args _ with "CI").
    iDestruct "HΦ" as "(CI & #H)"...

    (* 1. expression refl *)
    Cut...
    mono: iApply expr_logrel_refl.
    iDestruct "HΦ" as "(#Hv & CI)"...

    (* 2. Call simulation *)
    Cut.
    mono: (iApply (instr_conv_concretize_or_pick_strong with "Hv")) with "[CI]".
    iDestruct "HΦ" as "(Hdv & %Hdu_t & %Hdu_s)"...
    Cut...

    mono: iApply (call_refl with "CI Hdv H").
    iDestruct "HΦ" as "(#Hv2 & CI)"...

    (* 3. Local write simulation *)
    final...
    mono: iApply (local_write_refl with "CI Hv2").

    vfinal.
  Qed.

  Lemma instr_call_void_refl C fn args attrs n i_t i_s A_t A_s:
    ⊢ (code_inv C i_t i_s A_t A_s -∗
      instr_conv
       (denote_instr (IVoid n, INSTR_Call fn args attrs)) ⪯
       instr_conv
       (denote_instr (IVoid n, INSTR_Call fn args attrs))
       [{ (r_t, r_s), code_inv C i_t i_s A_t A_s }])%I.
  Proof with vsimp.
    iIntros "CI".
    cbn; destruct fn...
    Cut.
    mono: iApply (denote_exp_map_monad args _ with "CI").
    iDestruct "HΦ" as "(CI & #H)"...

    (* 1. expression refl *)
    Cut...
    mono: iApply expr_logrel_refl.
    iDestruct "HΦ" as "(#Hv & CI)"...

    (* 2. Call simulation *)
    Cut.
    mono: (iApply (instr_conv_concretize_or_pick_strong with "Hv")) with "[CI]".

    iDestruct "HΦ" as "(Hdv & %Hdu_t & %Hdu_s)"...
    Cut...

    mono: iApply (call_refl with "CI Hdv H").
    iDestruct "HΦ" as "(#Hv2 & CI)".
    do 2 vfinal.
  Qed.

  Lemma instr_alloca_refl C id t nb align i_t i_s A_t A_s :
    instr_WF (INSTR_Alloca t nb align) ->
    code_inv C i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IId id, INSTR_Alloca t nb align))
    ⪯
    instr_conv (denote_instr (IId id, INSTR_Alloca t nb align))
    [{ (r_t, r_s),
        ∃ l_t l_s, code_inv C i_t i_s (l_t:: A_t) (l_s:: A_s)}].
  Proof with vsimp.
    iIntros (WF) "CI". cbn.
    vsimp; Cut; vsimp. cbn in *.
    iApply (sim_expr_bupd_mono with "[] [CI]"); [ |
      iApply (alloca_refl_bij with "CI")]; cycle 1.
    { cbn; intros; apply non_void_b_non_void;
        destruct (non_void_b t); auto. }

    iIntros (??) "H".

    iDestruct "H" as (??->->??) "(#Hv & CI)"... final.
    iDestruct (dval_rel_lift with "Hv") as "Hdv"...

    mono: iApply (local_write_refl with "CI Hdv").

    vfinal. iExists _, _; by iFrame.
  Qed.

  Lemma instr_load_refl id volatile t ptr align i_t i_s A_t A_s:
    instr_WF (INSTR_Load volatile t ptr align) ->
    code_inv ∅ i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IId id, INSTR_Load volatile t ptr align))
    ⪯
    instr_conv (denote_instr (IId id, INSTR_Load volatile t ptr align))
    [{ (r_t, r_s), code_inv ∅ i_t i_s A_t A_s }].
  Proof with vsimp.
    iIntros (WF) "CI"; cbn; destruct ptr...
    Cut...

    (* Process the value *)
    mono: iApply (expr_logrel_refl (Some d) with "CI")...
    iDestruct "HΦ" as "(#Hv & CI)".
    Cut...

    mono: (iApply instr_conv_concretize_or_pick_strong) with "[CI]".

    iDestruct "HΦ" as "(#Hv' & %Hc & %Hc')"...
    destruct (@dvalue_eq_dec dv_s DVALUE_Poison); [ iApply instr_conv_raiseUB |].

    iDestruct (dval_rel_poison_neg_inv with "Hv'") as "%Hv".
    specialize (Hv n).
    destruct (@dvalue_eq_dec dv_t DVALUE_Poison) eqn: Hb; [ done | ]...

    Cut...

    assert (Hwf_t : dtyp_WF t).
    { cbn in WF. apply andb_prop_elim in WF; destruct WF.
      destruct (dtyp_WF_b t) eqn: Ht; try done.
      apply dtyp_WF_b_dtyp_WF in Ht. done. }

    mono: iApply (load_refl with "CI Hv'")...
    iDestruct "HΦ" as "(#Hv'' & CI)"; vfinal...

    mono: iApply (local_write_refl with "CI")...
    vfinal.
  Qed.

  Lemma instr_store_refl n volatile val ptr align i_t i_s A_t A_s:
    instr_WF (INSTR_Store volatile val ptr align) ->
    code_inv ∅ i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IVoid n, INSTR_Store volatile val ptr align))
    ⪯
    instr_conv (denote_instr (IVoid n, INSTR_Store volatile val ptr align))
    [{ (r_t, r_s), code_inv ∅ i_t i_s A_t A_s }].
  Proof with vsimp.
    iIntros (WF) "CI".
    cbn in WF; destruct ptr, d, val; try solve [inversion WF]; cbn...

    Cut... mono: iApply (expr_logrel_refl with "CI")...
    iDestruct "HΦ" as "(H & HL)"...

    Cut...
    mono: (iApply (instr_conv_concretize_or_pick_strong with "H")) with "[HL]"...

    iDestruct "HΦ" as "(#Hv' & %Hc & %Hc')";
    destruct (dvalue_has_dtyp_fun dv_s d) eqn :Hτ; cycle 1.
    (* TODO: Add to [sim_expr_vsimp]? *)
    { iApply instr_conv_raise. }

    apply dvalue_has_dtyp_fun_sound in Hτ.
    iDestruct (dval_rel_dvalue_has_dtyp with "Hv'") as %Hτ'.
    specialize (Hτ' Hτ). rewrite -dvalue_has_dtyp_eq in Hτ'.
    rewrite Hτ'; cbn...

    Cut... mono: iApply (expr_logrel_refl with "HL")...
    iDestruct "HΦ" as "(H & HL)".
    Cut...
    mono: (iApply instr_conv_concretize_or_pick_strong) with "[HL]"...

    iDestruct "HΦ" as "(#Hv''' & %Hc'' & %Hc''')"...

    destruct (@dvalue_eq_dec dv_s0 DVALUE_Poison);
      [ iApply instr_conv_raiseUB | ].
    iDestruct (dval_rel_poison_neg_inv with "Hv'''") as "%Hv".
    specialize (Hv n0).
    destruct (@dvalue_eq_dec dv_t0 DVALUE_Poison) eqn: Hb; [ done | ].

    assert (Hwf_t : dtyp_WF d).
    { cbn in WF. apply andb_prop_elim in WF; destruct WF.
      destruct (dtyp_WF_b d) eqn: Ht; try done.
      apply dtyp_WF_b_dtyp_WF in Ht. done. }

    vsimp. rewrite !subevent_subevent.
    mono: iApply (store_refl with "HL Hv''' Hv'")...
    2 : rewrite dvalue_has_dtyp_eq in Hτ'; auto.
    vfinal.
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
  Proof with vsimp.
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

    Cut; mono: iApply "He"...
    iDestruct "HΦ" as "(Hv & CI)"...

    iApply sim_update_si; rewrite /update_si.

    iIntros (??) "SI".
    iDestruct "CI" as (??)
      "(Hd_t & Hd_s & Hs_t & Hs_s & HA & %Hc & Ha_t & Ha_s)".

    iFrame. vfinal.
    repeat iExists _; by iFrame.
  Qed.

  Lemma phi_list_compat bid (Φ Φ' : list (local_id * phi dtyp)) C i_t i_s A_t A_s:
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
        phi_logrel (denote_phi bid ϕ) (denote_phi bid ϕ') C A_t A_s) -∗
    code_inv C i_t i_s A_t A_s -∗
    instr_conv (map_monad (λ x, translate exp_to_instr (denote_phi bid x)) Φ) ⪯
      instr_conv (map_monad (λ x, translate exp_to_instr (denote_phi bid x)) Φ')
    [{ (r_t, r_s),
        ([∗ list] v_t; v_s ∈ r_t; r_s,
           ⌜v_t.1 = v_s.1⌝ ∗ uval_rel v_t.2 v_s.2)
            ∗ code_inv C i_t i_s A_t A_s }].
  Proof with vsimp.
    iIntros "HΦ CI".

    iInduction Φ as [] "IH" forall (Φ').
    { cbn.
      iPoseProof (big_sepL2_nil_inv_l with "HΦ") as "%Heq"; subst; cbn...
      vfinal. }

    destruct a as (?&[]).
    iPoseProof (big_sepL2_cons_inv_l with "HΦ") as (???) "(He & HΦ)"; subst.
    destruct x2 as (l' & []).
    rename t0 into t', args0 into args', l2' into Φ'.
    iSpecialize ("IH" with "HΦ").
    cbn -[denote_phi]...

    iDestruct "CI" as (??)
        "(Hd_t & Hd_s & Hat & Has & #HWF &
        %Hargs & Hs_t & Hs_s & Hv & HC & Ha_t & Ha_s & %Hnd_t & %Hnd_s & #Hl)".

    Cut...
    iApply (sim_expr_bupd_mono with "[IH]"); [ | iApply "He"];
      try iFrame; eauto; cycle 1.

    cbn. iIntros (??) "H".
    iDestruct "H" as (?????) "(#H & CI)".
    rewrite H H0...

    iSpecialize ("IH" with "CI"). subst.
    Cut... mono: (iApply "IH")...
    iDestruct "HΦ" as "(H' & CI)".
    vfinal; cbn; vsimp; by iFrame "H".
  Qed.

  Theorem phis_compat C bid (Φ Φ' : list (local_id * phi dtyp)) A_t A_s:
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
        phi_logrel (denote_phi bid ϕ) (denote_phi bid ϕ') C A_t A_s) -∗
    phis_logrel (denote_phis bid Φ) (denote_phis bid Φ') C A_t A_s.
  Proof with vsimp.
    iIntros "HΦ" (??) "CI".
    iPoseProof (phi_list_compat with "HΦ CI") as "H".
    rewrite /denote_phis... Cut...
    mono: iApply "H"...
    iDestruct "HΦ" as "(H & CI)".

    setoid_rewrite instr_conv_ret.

    iInduction r_s as [] "IH" forall (r_t).
    { iDestruct (big_sepL2_nil_inv_r with "H") as %Hx; subst; cbn...
      Cut... do 2 vfinal. }

    iDestruct (big_sepL2_cons_inv_r with "H") as (???) "(CI1 & CI2)";
    destruct a, x1; subst; cbn...
    Cut...

    iDestruct "CI1" as "(%Hl & Hv)"; subst.

    Cut... mono: (iApply (local_write_refl with "CI Hv")) with "[CI2]"...

    final.
    iSpecialize ("IH" with "CI2 HΦ")...
    iPoseProof (sim_expr_fmap_inv with "IH") as "Hf".
    Cut.

    mono: iApply "Hf"...

    iDestruct "HΦ" as (????) "H".
    apply eqitree_inv_Ret in H, H0; subst.
    do 2 vfinal.
  Qed.

  Theorem code_compat (c c' : code dtyp) A_t A_s:
    code_WF c ->
    code_WF c' ->
    ([∗ list] '(id, i); '(id', i') ∈ c; c',
        ∀ A_t A_s, instr_logrel id i id' i' ∅ A_t A_s) -∗
    code_logrel c c' ∅ A_t A_s.
  Proof with vsimp.
    iIntros (Hwf Hwf') "Hi"; iIntros (??) "CI"; cbn.
    vsimp. setoid_rewrite instr_conv_ret.

    iInduction c as [| a l] "IHl" forall (c' Hwf' i_t i_s A_t A_s); cbn...
    { iDestruct (big_sepL2_nil_inv_l with "Hi") as %Hx;
        subst; cbn...
      Cut... do 2 vfinal; iExists ∅, ∅; iFrame. }

    iDestruct (big_sepL2_cons_inv_l with "Hi") as (???) "(CI1 & CI2)".
    destruct a, x2; subst; cbn -[denote_instr]... Cut...

    (* TODO: Pull out lemma *)
    cbn in Hwf; apply andb_prop_elim in Hwf;
      destruct Hwf as (HW1 & HW2).
    cbn in Hwf'; apply andb_prop_elim in Hwf';
      destruct Hwf' as (HW1' & HW2').

    Cut...
    mono: (iApply ("CI1" with "CI")) with "[CI2]"...
    Cut... iDestruct "HΦ" as (??) "CI".
    iSpecialize ("IHl" $! HW2 _ HW2' with "CI2 CI").
    iPoseProof (sim_expr_fmap_inv with "IHl") as "H".

    mono: iApply "H"...
    iDestruct "HΦ" as (??????) "H". destruct r_t, r_s.
    repeat vfinal.
    iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
    by rewrite !app_assoc.
  Qed.

  Theorem block_compat b b' bid A_t A_s:
    block_WF b ->
    block_WF b' ->
    phis_logrel
      (denote_phis bid (blk_phis b))
      (denote_phis bid (blk_phis b'))
      ∅ A_t A_s -∗
    code_logrel
      (blk_code b)
      (blk_code b')
      ∅ A_t A_s -∗
    term_logrel
       (blk_term b)
       (blk_term b')
       ∅ -∗
    block_logrel b b' bid ∅ A_t A_s.
  Proof with vsimp.
    iIntros (WF_b WF_b') "HΦ Hc Ht".
    iIntros (??) "CI".
    cbn -[denote_phis]...
    setoid_rewrite instr_conv_bind at 3. Cut...

    (* Phis *)
    mono: (iApply ("HΦ" with "CI")) with "[Hc Ht]"...
    rewrite instr_conv_bind... Cut...

    (* Code block *)
    iSpecialize ("Hc" with "HΦ").
    rewrite /denote_code /map_monad_.
    rewrite !instr_conv_bind ; setoid_rewrite instr_conv_ret.
    iPoseProof (sim_expr_fmap_inv with "Hc") as "Hc".
    mono: (iApply "Hc") with "[Ht]"...
    iDestruct "HΦ" as ([][] _ _ ??) "HI".

    (* Well-formedness of block *)
    apply andb_prop_elim in WF_b, WF_b';
      destruct WF_b, WF_b'.

    (* Terminator *)
    mono: iApply "Ht"...

    iIntros (??) "H".
    iDestruct "H" as (????) "(Hi & H)".
    iExists _,_. rewrite H3 H4.
    do 2 (iSplitL ""; [ done | ]). iFrame.
    by iExists _, _.
  Qed.

(* ------------------------------------------------------------------------ *)

(** *Fundamental theorems *)
  Theorem phi_logrel_refl bid id ϕ C A_t A_s:
    ⊢ (phi_logrel (denote_phi bid (id, ϕ)) (denote_phi bid (id, ϕ)) C A_t A_s)%I.
  Proof with vsimp.
    iApply phi_compat; destruct ϕ.
    destruct (Util.assoc bid args); try done.
    iApply expr_logrel_refl.
  Qed.

  Theorem phis_logrel_refl C bid (Φ : list (local_id * phi dtyp)) A_t A_s:
    (⊢ phis_logrel (denote_phis bid Φ) (denote_phis bid Φ) C A_t A_s)%I.
  Proof with vsimp.
    iApply phis_compat.
    iInduction Φ as [ | ] "IH"; first done.
    cbn; iSplitL; [ destruct a; iApply phi_logrel_refl | done ].
  Qed.

  Theorem instr_logrel_refl id e A_t A_s:
    instr_WF e ->
    (⊢ instr_logrel id e id e ∅ A_t A_s)%I.
  Proof with vsimp.
    iIntros (WF ??) "HI".
    destruct e eqn: He.
    all : destruct id; try iApply instr_conv_raise.
    { (* Comment *)
      cbn. vfinal. }

    { (* Pure operations *)
      cbn... Cut...
      mono: iApply (expr_logrel_refl with "HI")...
      iDestruct "HΦ" as "(Hv & Hc)".
      mono: iApply (local_write_refl with "Hc Hv")...
      vfinal; by iExists ∅, ∅. }

    { mono: iApply (instr_call_refl with "HI").
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _; do 2 (iSplitL ""; first done).
      by iExists ∅, ∅. }

    { mono: iApply (instr_call_void_refl with "HI").
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _; do 2 (iSplitL ""; first done).
      by iExists ∅, ∅. }

    { mono: iApply (instr_alloca_refl with "HI").
      cbn. iIntros (??) "H".
      iDestruct "H" as (??????) "H".
      iExists _, _; do 2 (iSplitL ""; first done).
      iExists [l_t], [l_s]; by cbn. }

    { mono: iApply (instr_load_refl with "HI").
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _; do 2 (iSplitL ""; first done).
      by iExists ∅, ∅. }

    { mono: iApply (instr_store_refl with "HI").
      cbn. iIntros (??) "H".
      iDestruct "H" as (????) "H".
      iExists _, _; do 2 (iSplitL ""; first done).
      by iExists ∅, ∅. }
  Qed.

  Theorem code_logrel_refl (c : code dtyp) A_t A_s:
    code_WF c ->
    ⊢ code_logrel c c ∅ A_t A_s.
  Proof with vsimp.
    iIntros (Hwf); iApply code_compat; eauto.
    iInduction c as [ | ] "IH"; first done.
    cbn in Hwf; apply andb_prop_elim in Hwf;
      destruct Hwf as (HW1 & HW2).
    cbn; iSplitL; [
      destruct a; iIntros; iApply instr_logrel_refl; eauto |
      by iApply "IH"];
      try done.
  Qed.

  Theorem term_logrel_refl ϒ C:
    (⊢ term_logrel ϒ ϒ C)%I.
  Proof with vsimp.
    iIntros (??????) "HI".
    destruct ϒ eqn: Hϒ; try solve [iDestruct "WF" as "[]"]; cbn.
    5-8: iApply exp_conv_raise.
    5 : iApply exp_conv_raiseUB.
    { (* TERM_Ret *)
      destruct v. vsimp. Cut.
      mono: iApply expr_logrel_refl...
      iDestruct "HΦ" as "(Hv & HΦ)"; vfinal. }
    { (* TERM_Ret_void *)
      vfinal. iApply uval_rel_none. }
    { (* TERM_Br *)
      destruct v; vsimp...
      Cut... mono: iApply expr_logrel_refl...
      Cut... iDestruct "HΦ" as "(Hv & HI)".
      mono: (iApply (exp_conv_concretize_or_pick with "Hv")) with "[HI]"...
      destruct dv_s; try iApply exp_conv_raise; [ | iApply exp_conv_raiseUB ].
      iDestruct (dval_rel_I1_inv with "HΦ") as %->.
      destruct (DynamicValues.Int1.eq x DynamicValues.Int1.one); vfinal. }
    { (* TERM_Br_1 *)
      vfinal. }
  Qed.

  Theorem block_logrel_refl b bid A_t A_s:
    block_WF b ->
    (⊢ block_logrel b b bid ∅ A_t A_s)%I.
  Proof with vsimp.
    iIntros (WF). pose proof (WF' := WF).
    apply andb_prop_elim in WF; destruct WF.
    iApply block_compat; eauto.
    { iApply phis_logrel_refl. }
    { by iApply code_logrel_refl. }
    { by iApply term_logrel_refl. }
  Qed.

  From Vellvm Require Import Syntax.ScopeTheory.

  (* TODO: move to [Syntax.ScopeTheory] *)
  Lemma find_block_cons_inv {T} a c b v:
    find_block (a :: c) b = Some v ->
    (blk_id a = b /\ v = a)
    \/ (blk_id a <> b /\ find_block (T := T) c b = Some v).
  Proof.
    revert a b v.
    induction c; cbn; intros; eauto.
    - destruct_if; by left.
    - destruct_if; destruct_if_goal; destruct_if;
        solve [by left | by right].
  Qed.

  (* TODO : move to Utils *)
  Lemma code_same_block_ids_find_block {T} c c' R:
    (([∗ list] y1;y2 ∈ c;c', ⌜blk_id y1 = blk_id (T := T) y2⌝ ∗ R y1 y2) -∗
      ∀ b v,
      ⌜find_block (T := T) c' b = Some v⌝ -∗
      ∃ v', ⌜find_block (T := T) c b = Some v'⌝ ∗ R v' v : iPropI Σ).
  Proof.
    revert c.
    (* Induction on the list of blocks *)
    induction c'; iIntros (c) "H"; eauto.
    { iPoseProof (big_sepL2_nil_inv_r with "H") as "%Heq";
        subst. iIntros (???). inv H. }

    (* cons case *)
    iPoseProof (big_sepL2_cons_inv_r with "H") as
      (?a' c'' ?) "((%Heq & HR) & H')"; subst.
    rename c'' into c.

    (* Use the IH. *)
    iPoseProof (IHc' with "H'") as "IH".
    iIntros (???).
    apply find_block_cons_inv in H;
      destruct H as [ (Heq' & Hbeq) | (Hineq & H) ]; subst.
    - iClear "IH". iExists a'; iFrame. rewrite -Heq.
      by rewrite find_block_eq.
    - iSpecialize ("IH" $! _ _ H).
      iDestruct "IH" as (??) "IH".
      iExists v'; iFrame.
      rewrite find_block_ineq; try rewrite Heq; try done.
  Qed.

  Lemma code_same_block_ids_find_block_None {T} c c':
    (([∗ list] y1;y2 ∈ c;c', ⌜blk_id y1 = blk_id (T := T) y2⌝) -∗
      ⌜forall b,
      find_block (T := T) c' b = None ->
      (find_block (T := T) c b = None)⌝ : iPropI Σ).
  Proof.
    revert c'.
    (* Induction on the list of blocks *)
    induction c; iIntros (c') "H"; eauto.

    (* cons case *)
    iPoseProof (big_sepL2_cons_inv_l with "H") as (?a' c'' ? Heq) "H"; subst.
    rename c'' into c'.

    (* Use the IH. *)
    iPoseProof (IHc with "H") as "%H".
    iPureIntro. intros.
    cbn. rewrite Heq; clear Heq. cbn in *.
    destruct (Eqv.eqv_dec_p (blk_id a') b) eqn: Heq; eauto.
    inv H0.
  Qed.

  Theorem ocfg_compat (c c' : CFG.ocfg dtyp) b1 b2 A_t A_s:
    ocfg_WF c ->
    ocfg_WF c' ->
    □ ([∗ list] b; b' ∈ c; c',
        (* The blocks have the same block ids, in order  *)
        ⌜blk_id b = blk_id b'⌝ ∗
        (* and are logically related *)
        ∀ A_t A_s be, block_logrel b b' be ∅ A_t A_s) -∗
    ocfg_logrel c c' ∅ A_t A_s b1 b2.
  Proof with vsimp.
    iIntros (WF WF') "#Hb"; iIntros (??) "CI".
    rewrite /ocfg_WF in WF.
    rewrite /denote_ocfg.
    unfold CategoryOps.iter, CategoryKleisli.Iter_Kleisli,
      Basics.iter, MonadIter_itree.

    (* That's really ugly... TODO: Fix *)
    epose proof
      (@interp_iter' _ _ instrE_conv_h _ _
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
      (λ i, interp instrE_conv_h
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
    rewrite /instr_conv. rewrite H; clear H.

    epose proof
      (@interp_iter' _ _ instrE_conv_h _ _
      (λ '(bid_from, bid_src),
        match CFG.find_block c' bid_src with
        | Some block_src =>
            Monad.bind (denote_block block_src bid_from)
              (λ bd : block_id + uvalue,
                  match bd with
                  | inl bid_target => Monad.ret (inl (bid_src, bid_target))
                  | inr dv => Monad.ret (inr (inr dv))
                  end)
        | None => Monad.ret (inr (inl (bid_from, bid_src)))
        end)
      (λ i, interp instrE_conv_h
      (let
       '(bid_from, bid_src) := i in
        match CFG.find_block c' bid_src with
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
      - iIntros "(Hb' & H & H')"; iFrame.
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
             with "[Hb] [CI]"); cycle 1.
    { iSplitL ""; first done.
      by iExists ∅, ∅. }
    iModIntro.
    iIntros (??) "(%Heq & CI)"; rewrite Heq. destruct i_t0, i_s0; inv Heq.
    iDestruct "CI" as (??) "CI".
    iApply sim_expr_lift.

    (* The block for block id [b0] is in the OCFG. *)
    destruct (CFG.find_block c' b4) eqn: Hb0.
    { (* Since the two OCFG's have the same block ids, a related block can be found
         for the other OCFG. *)
      iPoseProof (code_same_block_ids_find_block c c'
        (fun b b' => ∀ A_t A_s be, block_logrel b b' be ∅ A_t A_s) with "Hb")%I
        as "H".
      iSpecialize ("H" $! _ _ Hb0); iDestruct "H" as (??) "Hrel". rewrite H0.

      (* FIXME: Why doesn't [vsimp] work here? *)
      rewrite interp_bind (interp_bind _ (denote_block b b3)).

      apply find_block_has_id in Hb0, H0.
      Cut...
      iSpecialize ("Hrel" with "CI").
      rewrite /instr_conv.
      iApply sim_expr_bupd_mono; [ | iApply "Hrel"]; eauto; cycle 1.

      iIntros (??) "H".
      iDestruct "H" as (??->->) "(H & l)".
      iDestruct "H" as (??) "H".
      vsimp.
      destruct r_t, r_s; try (iDestruct "l" as %Heq; inversion Heq).
      - rewrite !interp_ret. final; iLeft.
        iExists (b4, b5), (b4, b5); iFrame; eauto.
        do 3 (iSplitL ""; first done).
        rewrite !app_assoc.
        by iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
      - do 2 rewrite interp_ret. final; iRight.
        iDestruct "l" as "#l". subst. iFrame.
        repeat iExists _; do 2 (iSplitL ""; eauto).
        iSplitL.
        { iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s).
          by rewrite !app_assoc. }

        repeat iExists _; do 2 (iSplitL ""; eauto); done. }

    rewrite big_sepL2_sep. iDestruct "Hb" as "(Hblk & Hb)".

    iDestruct (code_same_block_ids_find_block_None with "Hblk") as %Heq.
    specialize (Heq b4); rewrite Hb0 in Heq. specialize (Heq eq_refl); rewrite Heq.
    rewrite interp_ret. final. iRight. iFrame.
    do 2 iExists _; do 2 (iSplitL ""; eauto).
    iSplitL "CI".
    { iExists nA_t, nA_s; by iFrame. }

    repeat iExists _; do 2 (iSplitL ""; eauto); done.
  Qed.

  (* TODO: Move to [logical_relations]*)
  Lemma ocfg_WF_cons_inv a c :
    ocfg_WF (a :: c) ->
    block_WF a /\ ocfg_WF c.
  Proof.
    cbn; intros WF; apply andb_prop_elim in WF; by destruct WF.
  Qed.

  Theorem ocfg_logrel_refl (c : CFG.ocfg dtyp) b1 b2 A_t A_s:
    ocfg_WF c ->
    (⊢ ocfg_logrel c c ∅ A_t A_s b1 b2)%I.
  Proof with vsimp.
    iIntros (WF ??) "CI".
    iApply ocfg_compat; try done; iModIntro.
    (* Proceed by induction. *)
    iInduction c as [ | ] "IH"; first done.
    apply ocfg_WF_cons_inv in WF; destruct WF.
    cbn; iSplitL "".
    { iSplitL ""; first done; iIntros; by iApply block_logrel_refl. }

    by iApply "IH".
  Qed.

  Theorem cfg_compat c c' A_t A_s:
    cfg_WF c ->
    cfg_WF c' ->
    CFG.init c = CFG.init c' ->
    ocfg_logrel (blks c) (blks c') ∅ A_t A_s
      (CFG.init c) (CFG.init c) -∗
    cfg_logrel c c' ∅ A_t A_s.
  Proof with vsimp.
    iIntros (WF WF' Heq) "Hocfg". iIntros (??) "CI".
    setoid_rewrite interp_bind.
    destruct c, c'; cbn in *; subst.
    iSpecialize ("Hocfg" with "CI").
    iApply sim_expr'_bind; iApply (sim_expr'_bupd_mono); cycle 1.
    { iApply "Hocfg". }
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

  Theorem cfg_logrel_refl c A_t A_s:
    cfg_WF c ->
    (⊢ cfg_logrel c c ∅ A_t A_s)%I.
  Proof with vsimp.
    iIntros (WF); iApply cfg_compat; eauto.
    by iApply ocfg_logrel_refl.
  Qed.

  Theorem fun_logrel_refl f:
    fun_WF f ->
    (⊢ fun_logrel f f ∅)%I.
  Proof with vsimp.
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
      iPoseProof with (sim_pop_frame_bij with "Hs_t Hs_s Ha_t Ha_s HC Hbij") as "H";
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
  Proof with vsimp.
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
  Proof with vsimp.
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
  Proof with vsimp.
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
