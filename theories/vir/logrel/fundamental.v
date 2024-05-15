From iris.prelude Require Import options.

From Equations Require Import Equations.

From Vellvm Require Import Syntax.ScopeTheory.

From velliris.vir.lang Require Import lang.
From velliris.vir.logrel Require Import
  wellformedness
  logical_relations
  compatibility
  fundamental_exp.
Set Default Proof Using "Type*".

Import ListNotations.

(** *Reflexivity theorems for logical relations *)
Section fundamental.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

  (* TODO *)
  Theorem expr_logrel_relaxed_refl C dt e A_t A_s:
    (⊢ expr_logrel_relaxed C dt dt e e A_t A_s)%I.
  Proof. Admitted.

 (* ------------------------------------------------------------------------ *)
  (* Utility *)
  (* LATER: Generalize this helper lemma to any triple that is lifted with *)
  (*   [map_monad] *)
  Lemma denote_exp_map_monad (e: list (texp dtyp)) C i_t i_s A_t A_s :
    code_refl_inv C i_t i_s A_t A_s -∗
    instr_conv
      (map_monad (λ '(t, op), translate exp_to_instr (denote_exp (Some t) op)) e)
      ⪯
    instr_conv
      (map_monad (λ '(t, op), translate exp_to_instr (denote_exp (Some t) op)) e)
      [{ (e_t, e_s), code_refl_inv C i_t i_s A_t A_s
                       ∗ [∗ list] _↦x_t;x_s ∈ e_t;e_s, uval_rel x_t x_s }].
  Proof with vsimp.
    iIntros "CI".
    iInduction e as [] "IHl".
    { cbn... Base.
      iExists _,_; do 2 (iSplitL ""; [done |]); iFrame; done. }
    { cbn...
      destruct a. Cut...

      mono: iApply (expr_logrel_refl with "CI")...

      iDestruct "HΦ" as "(Hv & CI)"...

      Cut; iSpecialize ("IHl" with "CI").

      mono: iApply "IHl" with "[Hv]".

      iDestruct "HΦ" as "(CI & H)"; vfinal. }
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Instr-level reflexivity lemmas *)

  Lemma instr_call_refl C fn attrs args id  i_t i_s A_t A_s:
    ⊢ (code_refl_inv C i_t i_s A_t A_s -∗
      instr_conv
       (denote_instr (IId id, INSTR_Call fn args attrs)) ⪯
       instr_conv
       (denote_instr (IId id, INSTR_Call fn args attrs))
       [{ (r_t, r_s),
           code_refl_inv C i_t i_s A_t A_s }])%I.
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
    ⊢ (code_refl_inv C i_t i_s A_t A_s -∗
      instr_conv
       (denote_instr (IVoid n, INSTR_Call fn args attrs)) ⪯
       instr_conv
       (denote_instr (IVoid n, INSTR_Call fn args attrs))
       [{ (r_t, r_s), code_refl_inv C i_t i_s A_t A_s }])%I.
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
    code_refl_inv C i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IId id, INSTR_Alloca t nb align))
    ⪯
    instr_conv (denote_instr (IId id, INSTR_Alloca t nb align))
    [{ (r_t, r_s),
        ∃ l_t l_s, code_refl_inv C i_t i_s (l_t:: A_t) (l_s:: A_s)}].
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
    code_refl_inv ∅ i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IId id, INSTR_Load volatile t ptr align))
    ⪯
    instr_conv (denote_instr (IId id, INSTR_Load volatile t ptr align))
    [{ (r_t, r_s), code_refl_inv ∅ i_t i_s A_t A_s }].
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

  (*   assert (Hwf_t : dtyp_WF t). *)
  (*   { cbn in WF. apply andb_prop_elim in WF; destruct WF. *)
  (*     destruct (dtyp_WF_b t) eqn: Ht; try done. *)
  (*     apply dtyp_WF_b_dtyp_WF in Ht. done. } *)

  (*   mono: iApply (load_refl with "CI Hv'")... *)
  (*   iDestruct "HΦ" as "(#Hv'' & CI)"; vfinal... *)

  (*   mono: iApply (local_write_refl with "CI")... *)
  (*   vfinal. *)
  (* Qed. *)
  Admitted.

  Lemma instr_store_refl n volatile val ptr align i_t i_s A_t A_s:
    instr_WF (INSTR_Store volatile val ptr align) ->
    code_refl_inv ∅ i_t i_s A_t A_s -∗
    instr_conv (denote_instr (IVoid n, INSTR_Store volatile val ptr align))
    ⪯
    instr_conv (denote_instr (IVoid n, INSTR_Store volatile val ptr align))
    [{ (r_t, r_s), code_refl_inv ∅ i_t i_s A_t A_s }].
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

    (* assert (Hwf_t : dtyp_WF d). *)
    (* { cbn in WF. apply andb_prop_elim in WF; destruct WF. *)
    (*   destruct (dtyp_WF_b d) eqn: Ht; try done. *)
    (*   apply dtyp_WF_b_dtyp_WF in Ht. done. } *)

    (* vsimp. rewrite !subevent_subevent. *)
    (* mono: iApply (store_refl with "HL Hv''' Hv'")... *)
    (* 2 : rewrite dvalue_has_dtyp_eq in Hτ'; auto. *)
    (* vfinal. *)
  Admitted.


(* ------------------------------------------------------------------------ *)

  (* Lemma refl_inv_mono : *)
  (*   ∀ L_t0 L_s0 L_t' L_s' : local_env, *)
  (*     ⌜L_t' ⊆ L_t0⌝ -∗ *)
  (*     ⌜L_s' ⊆ L_s0⌝ -∗ *)
  (*      refl_inv L_t0 L_s0 -∗ refl_inv L_t' L_s'. *)
  (* Proof. Admitted. *)

(** *Fundamental theorems *)
  Theorem phi_logrel_refl bid id ϕ C A_t A_s l_t l_s:
    ⊢ phi_logrel
         (local_bij_except l_t l_s) alloca_bij
         bid bid (id, ϕ) (id, ϕ) C A_t A_s.
  Proof with vsimp.
    iApply phi_compat; destruct ϕ.
    destruct (Util.assoc bid args); try done.
    iApply expr_logrel_refl.
  Qed.

  Theorem phis_logrel_refl C bid (Φ : list (local_id * phi dtyp)) A_t A_s:
    (⊢ phis_logrel refl_inv (denote_phis bid Φ) (denote_phis bid Φ) C A_t A_s nil nil)%I.
  Proof with vsimp.
    iApply phis_compat.
    { iIntros (????); iApply refl_inv_mono. }
    iInduction Φ as [ | ] "IH"; first done.
    cbn; iSplitL; [ destruct a; iApply phi_logrel_refl | done ].
  Qed.

  Theorem instr_logrel_refl id e A_t A_s:
    instr_WF e ->
    (⊢ instr_logrel refl_inv id e id e ∅ A_t A_s nil nil)%I.
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
    ⊢ code_logrel refl_inv c c ∅ A_t A_s nil nil.
  Proof with vsimp.
    iIntros (Hwf); iApply code_compat; eauto.
    { iIntros (????); iApply refl_inv_mono. }
    iInduction c as [ | ] "IH"; first done.
    cbn in Hwf; apply andb_prop_elim in Hwf;
      destruct Hwf as (HW1 & HW2).
    cbn; iSplitL; [
      destruct a; iIntros; iApply instr_logrel_refl; eauto |
      by iApply "IH"];
      try done.
  Qed.

  Theorem term_logrel_refl ϒ C:
    (⊢ term_logrel refl_inv ϒ ϒ C nil nil)%I.
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
    (⊢ block_logrel refl_inv b b bid ∅ A_t A_s nil nil)%I.
  Proof with vsimp.
    iIntros (WF). pose proof (WF' := WF).
    apply andb_prop_elim in WF; destruct WF.
    iApply block_compat; eauto.
    { iIntros (????); iApply refl_inv_mono. }
    { iApply phis_logrel_refl. }
    { by iApply code_logrel_refl. }
    { by iApply term_logrel_refl. }
  Qed.

  Theorem ocfg_logrel_refl (c : CFG.ocfg dtyp) b1 b2 A_t A_s:
    ocfg_WF c ->
    (⊢ ocfg_logrel refl_inv c c ∅ A_t A_s b1 b2 nil nil)%I.
  Proof with vsimp.
    iIntros (WF ??) "CI".
    iApply ocfg_compat; try done.
    { iIntros (????); iApply refl_inv_mono. }
    iModIntro.
    (* Proceed by induction. *)
    iInduction c as [ | ] "IH"; first done.
    apply ocfg_WF_cons_inv in WF; destruct WF.
    cbn; iSplitL "".
    { iSplitL ""; first done; iIntros; by iApply block_logrel_refl. }

    by iApply "IH".
  Qed.

  Theorem cfg_logrel_refl c A_t A_s:
    cfg_WF c ->
    (⊢ cfg_logrel refl_inv c c ∅ A_t A_s nil nil)%I.
  Proof with vsimp.
    iIntros (WF); iApply cfg_compat; eauto.
    { iIntros (????); iApply refl_inv_mono. }
    by iApply ocfg_logrel_refl.
  Qed.

  Theorem fun_logrel_refl f:
    fun_WF f ->
    (⊢ fun_logrel f f ∅)%I.
  Proof with vsimp.
    iIntros (wf).
    iApply (fun_compat (refl_inv) nil nil); eauto.
    { iIntros (????); iApply refl_inv_mono. }
    { cbn. iIntros (????jk) "H". rewrite /refl_inv; cbn; iFrame.
      rewrite !combine_fst ?combine_snd; eauto; try iFrame. }
    iIntros; iApply cfg_logrel_refl; eauto.
    apply andb_prop_elim in wf; by destruct wf.
  Qed.

  Theorem fundefs_logrel_refl r Attr:
    ⌜fundefs_WF r Attr⌝ -∗
    fundefs_logrel r r Attr Attr ∅.
  Proof with vsimp.
    iIntros (WF); iApply fundefs_compat; eauto.
    iInduction r as [|] "IH" forall (Attr WF); first done.
    destruct Attr; first inv WF.
    eapply fundefs_WF_cons_inv in WF; destruct WF.
    rewrite /fundefs_WF in H.
    cbn; destruct a; iSplitL ""; first iApply fun_logrel_refl; eauto.
    by iApply "IH".
  Qed.

  Theorem mcfg_definitions_refl (defs : CFG.mcfg dtyp) g_t g_s:
    (CFG_WF defs g_t g_s ->
     ⊢ target_globals g_t -∗
     source_globals g_s -∗
     mcfg_definitions defs ⪯ mcfg_definitions defs
      ⦉ fun e_t e_s =>
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
            □ (fundefs_logrel r_t r_s (CFG_attributes defs) (CFG_attributes defs) ∅) ⦊)%I.
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
        [ | iApply (globalbij.sim_global_read1 with "Hg_t Hg_s") ]; eauto.

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
      ⦉ fun e_t e_s =>
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
            □ (fundefs_logrel r_t r_s (CFG_attributes defs) (CFG_attributes defs) ∅) ⦊)%I.
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
        [ | iApply (globalbij.sim_global_read1 with "Hg_t Hg_s") ]; eauto.

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
