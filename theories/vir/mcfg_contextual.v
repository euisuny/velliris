From iris.prelude Require Import options.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
  vir val_rel heapbij adequacy spec globalbij logical_relations fundamental.

From Vellvm Require Import Syntax.DynamicTypes Handlers Syntax.LLVMAst
  Semantics.InterpretationStack.

From ITree Require Import ITree Recursion.
From Equations Require Import Equations.

Import LLVMEvents.

Set Default Proof Using "Type*".

Section mcfg_contextual.

  Context `(sheapGS Σ, checkedoutGS Σ, heapbijGS Σ).

  Definition frame_inv i_t i_s :=
    (frame_WF i_t i_s ∗ checkout ∅ ∗ stack_tgt i_t ∗ stack_src i_s)%I.

  (* An obligation for each of the defined calls; it satisfies the external
      call specifications *)
  Definition context_rel_call_inv
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T) :=
    (□ (∀ fn1 fn2 dt1 dt2 attr1 attr2 args1 args2 C,
          let call1 := ExternalCall dt1 fn1 args1 attr1 in
          let call2 := ExternalCall dt2 fn2 args2 attr2 in
          call_ev call1 call2 C -∗
          ⟅ f _ (Call dt1 fn1 args1 attr1) ⟆ ⪯
          ⟅ g _ (Call dt2 fn2 args2 attr2) ⟆
          [[ (fun v1 v2 => call_ans call1 v1 call2 v2 C) ⤉ ]]) )%I.

  (* Should follow by reflexivity theorem *)
  Definition context_rel_refl
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T) :=
    (□ (∀ fn1 fn2 dt attr args1 args2 C,
          arg_val_rel (fn1, args1) (fn2, args2) C -∗
          ⟅ f _ (Call dt fn1 args1 attr) ⟆ ⪯
          ⟅ g _ (Call dt fn2 args2 attr) ⟆
          [[ (fun x y => res_val_rel x y C) ⤉ ]]))%I.

  (* Definition context_call *)
  (*     (f : ∀ T : Type, CallE T → L0'expr T) := *)
  (*   (forall τ addr args attrs, *)
  (*     f uvalue (Call τ addr args (FNATTR_Internal :: attrs)) = *)
  (*     f uvalue (Call τ addr args attrs)) /\ *)
  (*   (forall τ addr args attrs, *)
  (*     f uvalue (Call τ addr args (FNATTR_External:: attrs)) = *)
  (*     f uvalue (Call τ addr args attrs)). *)

  Definition context_rel
      (f : ∀ T : Type, CallE T → L0'expr T)
      (g : ∀ T : Type, CallE T → L0'expr T) :=
    (context_rel_call_inv f g ∗ context_rel_refl f g)%I.

  Theorem Proper_interp_mrec' {R}
    (f g : ∀ T : Type, LLVMEvents.CallE T → L0'expr T) a1 a2
    (Ψ : R -d> R -d> iPropI Σ) i_t i_s :
    frame_inv i_t i_s -∗
    context_rel f g -∗
    <pers>
    (frame_inv i_t i_s -∗ ⟅ a1 ⟆ ⪯ ⟅ a2 ⟆ [[ (fun x y => Ψ x y ∗ frame_inv i_t i_s) ⤉ ]]) -∗
    interp_mrec f a1 ⪯ interp_mrec g a2
    [[ (fun x y => Ψ x y ∗ frame_inv i_t i_s) ⤉ ]].
  Proof.
    iIntros "Hinv Hrel #Hr".
    iSpecialize ("Hr" with "Hinv").
  Admitted.

  (* Type declaration for function definitions, i.e. an association list for
     function definitions with [dvalue] keys. *)
  Definition fundefs : Type := list (dvalue * definition dtyp (CFG.cfg dtyp)).

  Definition fundef_no_attr (def : definition dtyp (CFG.cfg dtyp)) :=
    RelDec.rel_dec (dc_attrs (df_prototype def)) nil.

  (* The function definition map [fd] does not have any attributes at its
    definition site. *)
  Definition fundefs_no_attr (fd : fundefs) :=
    forallb (fun '(_, def) => fundef_no_attr def) fd.

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

  (* The contextual refinement on [denote_mcfg]. *)
  Lemma contextual_denote_mcfg :
    ∀ γ_t γ_s dv dv' e_t e_s main C,
    fundefs_no_attr C ->
    fundef_no_attr e_t ->
    fundef_no_attr e_s ->
    □ fun_logrel e_t e_s ∅ -∗
      checkout ∅ -∗
      stack_tgt [γ_t] -∗
      stack_src [γ_s] -∗
      dval_rel dv dv' -∗
      ([∗ list] v_t;v_s ∈ C.*1;C.*1, dval_rel v_t v_s) -∗
      denote_mcfg ((dv, e_t) :: C) DTYPE_Void (DVALUE_Addr main) []
      ⪯
      denote_mcfg ((dv', e_s) :: C) DTYPE_Void (DVALUE_Addr main) []
      [[ (λ x y : uvalue, ⌜obs_val x y⌝) ⤉ ]].
  Proof.
    iIntros (???????? HC H_t H_s) "#Hfun Hc Hs_t Hs_s #Hdv #Hfun_keys".
    rewrite /denote_mcfg.

    iAssert (frame_inv [γ_t] [γ_s])%I with "[Hc Hs_t Hs_s]" as "Hinv".
    { by iFrame. }

    iPoseProof
      (Proper_interp_mrec' _ _ _ _ (λ x y : uvalue, ⌜obs_val x y⌝)%I [γ_t] [γ_s]
        with "Hinv") as "Hrec"; eauto.
    iApply (sim_expr'_bupd_mono with "[] [Hrec]"); last iApply "Hrec".
    { iIntros (??) "HΨ"; iDestruct "HΨ" as (????) "(%HΨ & HI)".
      iExists _, _; iFrame. done. }

    { rewrite /context_rel.

      iSplitL ""; cycle 1.
      {  (* REFL *)
        iIntros (??).
        iModIntro.
        iIntros (?????).
        destruct C0 as ((?&?)&?).
        rewrite /arg_val_rel. cbn -[denote_function].
        iIntros "Hev".
        iDestruct "Hev" as "(#HWF & HC & Hst & Hss & #Hfn & #Hargs)".
        subst.

        destruct (lookup_defn fn2 ((dv', e_s) :: C)) eqn: Hs; cycle 1.

        (* External call case *)
        { cbn in Hs. destruct_if; reldec.
          iDestruct (dval_rel_ne_inj with "Hfn Hdv") as %Hne.
          assert (dv' <> fn2) by eauto.
          specialize (Hne H3). cbn -[denote_function].
          destruct (RelDec.rel_dec fn1 dv) eqn: Hfn1; reldec; try done.
          iPoseProof (dval_rel_lookup_none with "Hfn Hfun_keys") as "%Hlu".
          rewrite /lookup_defn.
          specialize (Hlu Hs); rewrite Hlu.

          rewrite /call_ev; cbn; simp vir_call_ev.
          rewrite /lookup_defn in Hs. rewrite Hs.

          iApply (sim_expr'_bupd_mono);
            last iApply (sim_external_call with "HWF Hst Hss HC Hfn Hargs").
          iIntros (??) "H'".
          rewrite /lift_post.
          iDestruct "H'" as (????) "(#Hv' & HC & Hs_t & Hs_s)".
          iExists _, _; iFrame.
          repeat (iSplitL ""; first done).
          simp vir_call_ans; by iFrame. }

        (* Internal call case *)
        { rewrite /fundefs_rel_WF.

          apply lookup_defn_cons_Some in Hs.
          destruct Hs.
          (* It is the [e_s] function (the hole) *)
          { destruct H2; subst; cbn -[denote_function].
            iDestruct (dval_rel_inj with "Hdv Hfn") as %Hdef; subst.
            destruct (RelDec.rel_dec fn1 fn1) eqn: Hf; reldec; subst; last done.
            destruct (RelDec.rel_dec dv' dv') eqn: Hf'; reldec; subst; last done.
            subst.

            iDestruct "HWF" as %HWF; subst.
            rewrite /fundef_no_attr in H_t, H_s.
            assert (attr = nil).
            { admit. }
            rewrite H2.
            destruct (RelDec.rel_dec (dc_attrs (df_prototype d)) []); try done.
            destruct (RelDec.rel_dec (dc_attrs (df_prototype e_t)) []); try done.

            iSpecialize ("Hfun" $! _ _ _ _ HWF with "Hst Hss Hargs HC").
            iApply sim_expr'_bupd_mono; last (iApply "Hfun").
            iIntros (??) "H'".
            rewrite /lift_post.
            iDestruct "H'" as (????) "(Hs_t & Hs_s & HC & Hval)".
            iExists _, _; iFrame. subst; iModIntro.
            repeat (iSplitL ""; first done).
            simp vir_call_ans; by iFrame. }

          (* It is a function in the context *)
          { destruct H2. cbn -[denote_function].

            iDestruct (dval_rel_ne_inj with "Hdv Hfn") as "%Hne"; subst.
            specialize (Hne H2); subst.
            destruct (RelDec.rel_dec fn1 dv) eqn: Hf; reldec; subst; first done.
            destruct (RelDec.rel_dec fn2 dv') eqn: Hf'; reldec; subst; first done.
            clear H2 Hne Hf.
            iPoseProof (dval_rel_lookup_some with "Hfn Hfun_keys") as "%Hlu".
            specialize (Hlu _ H3). destruct Hlu as (?&?).
            rewrite /lookup_defn in H3.
            rewrite /lookup_defn; rewrite H2 H3.

            (* Juicing out information from the WF of fundefs *)
            unfold fundefs_WF in WF_s.
            apply andb_prop_elim in WF_s.
            destruct WF_s as (Hlen & Wdup_s).
            apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
            apply forallb_True in Hfun_wf.
            rewrite List.Forall_forall in Hfun_wf.
            assert (Hr_s := H3).
            apply lookup_defn_Some_In in H3.
            (* Function [d] is well-formed. *)
            specialize (Hfun_wf _ H3); cbn in Hfun_wf.

            (* Using [fundefs_logrel] *)
            assert (Hlen': (length [γf0] > 0)%Z → (length [γf] > 0)%Z) by auto.
            rewrite /fundefs_logrel. rewrite /lookup_defn in Hr_s.
            apply lookup_defn_Some_lookup in Hr_s.
            destruct Hr_s.
            (* Juice information out of fundef rel WF *)
            iDestruct "Hrel" as "(Hrel & Hn)".
            iSpecialize ("Hrel" $! _ _ _ H6).
            iDestruct "Hrel" as (???) "(#Hdv' & %Hattr & %Hattr' & %Hft & %Hfs)".

            iDestruct (dval_rel_inj with "Hfn Hdv'") as %Hf; subst.

            iSpecialize ("Hlr" $! _ _ _ _ _ _ H7 H6 Hattr Hattr'
                          with "Hdv'").
            iDestruct "HWF" as %HWF.
            iSpecialize ("Hlr" $! _ _ _ _ HWF with "Hst Hss Hargs HC").

            eapply lookup_defn_Some in H2; eauto;cycle 1.
            { clear -WF_t.

              unfold fundefs_WF in WF_t.
              apply andb_prop_elim in WF_t.
              destruct WF_t as (Hlen & Wdup_t).
              apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
              apply forallb_True in Hfun_wf.
              rewrite List.Forall_forall in Hfun_wf.
              apply Is_true_true_1 in Wdup_t.
              by apply NoDup_b_NoDup. }
            subst.

            iApply sim_expr'_bupd_mono; last iApply "Hlr".
            iIntros (??) "Hin".
            iDestruct "Hin" as (????) "(Hst & Hss & HC & Hval)".
            iExists _, _.
            repeat (iSplitL ""; first done).
            simp vir_call_ans; subst; by iFrame. } } }

      { (* CALL INV *)
        iIntros (??).
        iModIntro.
        iIntros (???????).
        destruct C0 as ((?&?)&?).
        rewrite /call_ev. cbn -[denote_function].
        iIntros "Hev". simp vir_call_ev.
        iDestruct "Hev" as
          "(#Hfn &%Hdt & %Hattr& #Hargs & HC & #HWF & Hst & Hss & %Hinterp)".
        subst.

        destruct (lookup_defn fn2 ((dv', e_s) :: r_s))
          eqn: Hs; cycle 1.

        (* External call case *)
        { cbn in Hs. destruct_if; reldec.
          iDestruct (dval_rel_ne_inj with "Hfn Hdv") as %Hne.
          assert (dv' <> fn2) by eauto.
          specialize (Hne H3). cbn -[denote_function].
          destruct (RelDec.rel_dec fn1 dv) eqn: Hfn1; reldec; try done.
          iPoseProof (dval_rel_lookup_none with "Hfn Hv") as "%Hlu".
          rewrite /lookup_defn.
          specialize (Hlu Hs); rewrite Hlu.

          rewrite /call_ev; cbn; simp vir_call_ev.
          rewrite /lookup_defn in Hs. rewrite Hs.

          specialize (WF_attr _ _ _ _ _ _ _ _ Hinterp); subst.

          iApply (sim_expr'_bupd_mono);
            last iApply (sim_external_call with "HWF Hst Hss HC Hfn Hargs").
          iIntros (??) "H'".
          rewrite /lift_post.
          iDestruct "H'" as (????) "(#Hv' & HC & Hs_t & Hs_s)".
          iExists _, _; iFrame.
          repeat (iSplitL ""; first done).
          simp vir_call_ans; by iFrame. }

        (* Internal call case *)
        { rewrite /fundefs_rel_WF.

          apply lookup_defn_cons_Some in Hs.
          destruct Hs.
          (* It is the [e_s] function (the hole) *)
          { destruct H2; subst; cbn -[denote_function].
            iDestruct (dval_rel_inj with "Hdv Hfn") as %Hdef; subst.
            destruct (RelDec.rel_dec fn1 fn1) eqn: Hf; reldec; subst; last done.
            destruct (RelDec.rel_dec dv' dv') eqn: Hf'; reldec; subst; last done.
            subst.

            iDestruct "HWF" as %HWF; subst.
            iDestruct ("Hf" $! _ _ _) as "(_ & Hf')".
            specialize (WF_attr _ _ _ _ _ _ _ _ Hinterp); subst.

            iSpecialize ("Hf'" $! _ _ _ _ HWF with "Hst Hss Hargs HC").
            iApply sim_expr'_bupd_mono; last (iApply "Hf'").
            iIntros (??) "H'".
            rewrite /lift_post.
            iDestruct "H'" as (????) "(Hs_t & Hs_s & HC & Hval)".
            iExists _, _; iFrame. subst; iModIntro.
            repeat (iSplitL ""; first done).
            simp vir_call_ans; by iFrame. }

          (* It is a function in the context *)
          { destruct H2. cbn -[denote_function].

            iDestruct (dval_rel_ne_inj with "Hdv Hfn") as "%Hne"; subst.
            specialize (Hne H2); subst.
            destruct (RelDec.rel_dec fn1 dv) eqn: Hf; reldec; subst; first done.
            destruct (RelDec.rel_dec fn2 dv') eqn: Hf'; reldec; subst; first done.
            clear H2 Hne Hf.
            iPoseProof (dval_rel_lookup_some with "Hfn Hv") as "%Hlu".
            specialize (Hlu _ H3). destruct Hlu as (?&?).
            rewrite /lookup_defn in H3.
            rewrite /lookup_defn; rewrite H2 H3.

            (* Juicing out information from the WF of fundefs *)
            unfold fundefs_WF in WF_s.
            apply andb_prop_elim in WF_s.
            destruct WF_s as (Hlen & Wdup_s).
            apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
            apply forallb_True in Hfun_wf.
            rewrite List.Forall_forall in Hfun_wf.
            assert (Hr_s := H3).
            apply lookup_defn_Some_In in H3.
            (* Function [d] is well-formed. *)
            specialize (Hfun_wf _ H3); cbn in Hfun_wf.

            (* Using [fundefs_logrel] *)
            assert (Hlen': (length [γf0] > 0)%Z → (length [γf] > 0)%Z) by auto.
            rewrite /fundefs_logrel. rewrite /lookup_defn in Hr_s.
            apply lookup_defn_Some_lookup in Hr_s.
            destruct Hr_s.
            (* Juice information out of fundef rel WF *)
            iDestruct "Hrel" as "(Hrel & Hn)".
            iSpecialize ("Hrel" $! _ _ _ H6).
            iDestruct "Hrel" as (???) "(#Hdv' & %Hattr & %Hattr' & %Hft & %Hfs)".

            iDestruct (dval_rel_inj with "Hfn Hdv'") as %Hf; subst.

            specialize (WF_attr _ _ _ _ _ _ _ _ Hinterp); subst.
            iSpecialize ("Hlr" $! _ _ _ _ _ _ H7 H6 Hattr Hattr'
                          with "Hdv'").
            iDestruct "HWF" as %HWF.
            iSpecialize ("Hlr" $! _ _ _ _ HWF with "Hst Hss Hargs HC").

            eapply lookup_defn_Some in H2; eauto;cycle 1.
            { clear -WF_t.

              unfold fundefs_WF in WF_t.
              apply andb_prop_elim in WF_t.
              destruct WF_t as (Hlen & Wdup_t).
              apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
              apply forallb_True in Hfun_wf.
              rewrite List.Forall_forall in Hfun_wf.
              apply Is_true_true_1 in Wdup_t.
              by apply NoDup_b_NoDup. }
            subst.

            iApply sim_expr'_bupd_mono; last iApply "Hlr".
            iIntros (??) "Hin".
            iDestruct "Hin" as (????) "(Hst & Hss & HC & Hval)".
            iExists _, _.
            repeat (iSplitL ""; first done).
            simp vir_call_ans; subst; by iFrame. } } } }

    (* Other obligation that "feels like a duplicate obligation",
    but is a separate one coming from the body of the [mrec] *)
    { iModIntro. iIntros "(#HWF & HC & Hst & Hss)".

      iAssert (dval_rel (DVALUE_Addr main) (DVALUE_Addr main))%I as "#Hmain".
      { rewrite (dval_rel_unfold (DVALUE_Addr _)).
        cbn. iSplitL ""; try done.
        iDestruct "Haddr_main" as "(Haddr_main & _)"; done. }

      destruct (lookup_defn (DVALUE_Addr main) ((dv', e_s) :: r_s))
        eqn: Hs; cycle 1.

      (* External call case *)
      { cbn in Hs. destruct_if; reldec.
        iDestruct (dval_rel_ne_inj with "Hmain Hdv") as %Hne.
        assert (dv' <> DVALUE_Addr main) by eauto.
        specialize (Hne H3). cbn -[denote_function map_monad].
        destruct (RelDec.rel_dec (DVALUE_Addr main) dv) eqn: Hfn1;
          reldec; try done.
        iPoseProof (dval_rel_lookup_none with "Hmain Hv") as "%Hlu".
        rewrite /lookup_defn.
        specialize (Hlu Hs); rewrite Hlu.

        iApply (sim_expr'_bupd_mono);
          last iApply (sim_external_call with "HWF Hst Hss HC Hmain"); try done.
        iIntros (??) "H'".
        rewrite /lift_post.
        iDestruct "H'" as (????) "(#Hv' & HC & Hs_t & Hs_s)".
        iExists _, _; iFrame.
        repeat (iSplitL ""; first done).
        (iSplitR ""; last done).

        iApply (uval_rel_implies_obs_val with "Hv'"). }

      (* Internal call case *)
      { apply lookup_defn_cons_Some in Hs.
        destruct Hs.
        (* It is the [e_s] function (the hole) *)
        { destruct H2; inv H2; subst. cbn -[denote_function].
          iDestruct (dval_rel_inj with "Hdv Hmain") as %Hdef; subst.
          destruct (RelDec.rel_dec (DVALUE_Addr main) (DVALUE_Addr main))
            eqn: Hf; reldec; subst; last done.
          rewrite /fun_logrel.
          iDestruct "HWF" as %HWF.
          iDestruct ("Hf" $! _ _ _) as "(_ & Hf')".

          iSpecialize ("Hf'" $! _ _ nil nil HWF with "Hst Hss").
          cbn -[denote_function].
          iSpecialize ("Hf'" $! Logic.I with "HC").

          iApply sim_expr'_bupd_mono; last (iApply "Hf'").
          iIntros (??) "H'".
          rewrite /lift_post.
          iDestruct "H'" as (????) "(Hs_t & Hs_s & HC & Hval)".
          iExists _, _; iFrame. subst; iModIntro.
          repeat (iSplitL ""; first done).
          (iSplitR ""; last done).
          iApply (uval_rel_implies_obs_val with "Hval"). }

        (* It is a function in the context *)
        { destruct H2; cbn -[denote_function].

          iDestruct (dval_rel_ne_inj with "Hdv Hmain") as "%Hne"; subst.
          specialize (Hne H2); subst.
          destruct (RelDec.rel_dec (DVALUE_Addr main) dv) eqn: Hf;
            reldec; subst; first done.
          clear H2 Hne Hf.
          iPoseProof (dval_rel_lookup_some with "Hmain Hv") as "%Hlu".
          specialize (Hlu _ H3). destruct Hlu as (?&?).
          rewrite /lookup_defn H2.

          (* Juicing out information from the WF of fundefs *)
          unfold fundefs_WF in WF_s.
          apply andb_prop_elim in WF_s.
          destruct WF_s as (Hlen & Wdup_s).
          apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
          apply forallb_True in Hfun_wf.
          rewrite List.Forall_forall in Hfun_wf.
          assert (Hr_s := H3).
          apply lookup_defn_Some_In in H3.
          (* Function [d] is well-formed. *)
          specialize (Hfun_wf _ H3); cbn in Hfun_wf.

          (* Using [fundefs_logrel] *)
          assert (Hlen': (length [γf0] > 0)%Z → (length [γf] > 0)%Z) by auto.
          rewrite /fundefs_logrel.
          apply lookup_defn_Some_lookup in Hr_s.
          destruct Hr_s.
          (* Juice information out of fundef rel WF *)
          iDestruct "Hrel" as "(Hrel & Hn)".
          iSpecialize ("Hrel" $! _ _ _ H6).
          iDestruct "Hrel" as (???)
                                "(#Hdv' & %Hattr & %Hattr' & %Hft & %Hfs)".

          iSpecialize ("Hlr" $! _ _ _ _ _ _ H7 H6 Hattr Hattr'
                        with "Hdv'").
          iSpecialize ("Hlr" $! _ _ nil nil Hlen' with "Hst Hss").
          cbn -[denote_function].
          iSpecialize ("Hlr" $! Logic.I with "HC").

          iDestruct (dval_rel_inj with "Hmain Hdv'") as %Hf; subst.

          eapply lookup_defn_Some in H2; eauto;cycle 1.
          { clear -WF_t.

            unfold fundefs_WF in WF_t.
            apply andb_prop_elim in WF_t.
            destruct WF_t as (Hlen & Wdup_t).
            apply andb_prop_elim in Hlen. destruct Hlen as (Hlen & Hfun_wf).
            apply forallb_True in Hfun_wf.
            rewrite List.Forall_forall in Hfun_wf.
            apply Is_true_true_1 in Wdup_t.
            by apply NoDup_b_NoDup. }
          eauto.
          subst.

          iApply sim_expr'_bupd_mono; last iApply "Hlr".
          iIntros (??) "Hin".
          iDestruct "Hin" as (????) "(Hst & Hss & HC & Hval)".
          iExists _, _; subst.
          repeat (iSplitL ""; first done); iFrame.
          (iSplitR ""; last done).

          iApply (uval_rel_implies_obs_val with "Hval"). } } }
      Unshelve.
      all : eauto. all: do 2 constructor.
    Qed.


      { cbn.


    Admitted.

  End mcfg_contextual.
