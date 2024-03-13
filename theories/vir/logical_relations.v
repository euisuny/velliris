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

From simuliris.logic Require Import satisfiable.
From simuliris.simulation Require Import slsls simulation sim_properties
  wellformedness contextual.
From simuliris.vir Require Import
   vir spec globalbij heapbij frame_laws primitive_laws bij_laws.
From simuliris.utils Require Import no_event.

Set Default Proof Using "Type*".

Import ListNotations.
Import SemNotations.

(* FIXME: Why isn't this notation readily available here? *)
Notation "et '⪯' es [[ Φ ]]" :=
  (sim_expr' (η := vir_handler) Φ et es) (at level 70, Φ at level 200,
        format "'[hv' et  '/' '⪯' '/' es  '/' [[  '[ ' Φ  ']' ]] ']'") : bi_scope.

Ltac simp_instr :=
  rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1;
  simp instrE_conv.

Section WF.

  Local Open Scope nat_scope.

  (* Syntactic well-formedness of LLVM IR program that we wish to verify *)
  Definition term_WF (ϒ : terminator dtyp) : bool :=
    match ϒ with
      | TERM_Ret _
      | TERM_Ret_void => true
      | TERM_Br (τ, e) bid1 bid2 => true
      | TERM_Br_1 bid => true
      | TERM_Switch (τ, e) bid l => true
      (* Unsupported terminators *)
      | _ => false
    end.

  Fixpoint dtyp_WF_b (d : dtyp) : bool :=
    match d with
    | DTYPE_I 1
    | DTYPE_I 8
    | DTYPE_I 32
    | DTYPE_I 64
    | DTYPE_Pointer
    | DTYPE_Float
    | DTYPE_Double => true
    | DTYPE_Array sz τ => dtyp_WF_b τ && negb (N.eqb sz 0)
    | DTYPE_Struct (x :: tl) => dtyp_WF_b x && forallb dtyp_WF_b tl
    | _ => false
    end.

  Lemma dtyp_WF_b_dtyp_WF d :
    dtyp_WF_b d = true <-> dtyp_WF d.
  Proof.
    split; intros; induction d; try constructor;
      cbn in *; destruct_match; try constructor;
      inversion H; eauto.
    { apply IHd.
      apply andb_prop in H1; destruct H1; auto. }
    { apply andb_prop in H; destruct H; auto.
      rewrite negb_true_iff in H0.
      intro. rewrite -N.eqb_eq in H2.
      rewrite H0 in H2; inversion H2. }
    { apply andb_prop in H; destruct H; auto.
      apply H0; eauto. apply in_eq. }
    { apply andb_prop in H; destruct H; auto.
      clear H2 H3. revert d H0 H.
      induction l; eauto; cbn. cbn in H1.
      apply andb_prop in H1; destruct H1; auto.
      intros; rewrite Forall_cons; split; eauto. }
    { subst. specialize (IHd H2).
      apply andb_true_intro; split; eauto.
      rewrite negb_true_iff.
      red in H3.
      rewrite -N.eqb_eq in H3.
      destruct ((sz =? 0)%N); eauto.
      exfalso; done. }
    subst. induction fields; eauto.
    rewrite Forall_cons in H3. destruct H3.
    apply andb_true_intro; split.
    { apply H0; eauto. apply in_eq. }
    { destruct fields; eauto.
      cbn. apply IHfields; eauto.
      { intros ; eapply H0; eauto.
        by apply in_cons. }
      { constructor; eauto. } }
  Qed.

  Definition non_void_b (d : dtyp) : bool :=
    match d with
    | DTYPE_Void => false
    | _ => true
    end.

  Lemma non_void_b_non_void d :
    non_void_b d = true <-> non_void d.
  Proof.
    split; unfold non_void_b; cbn; intros; destruct d;
      eauto; done.
  Qed.

  Definition raw_id_eqb (x y : raw_id) : bool :=
    match x, y with
    | Name x, Name y => (x =? y)%string
    | Anon x, Anon y => (x =? y)%Z
    | Raw x, Raw y => (x =? y)%Z
    | _, _ => false
    end.

  Definition instr_WF (i : instr dtyp) :=
    match i with
    | INSTR_Op exp => true
    | INSTR_Load _ t (t', _) _ =>
        dtyp_WF_b t && dtyp_WF_b t'
    | INSTR_Store _ (t, _) (DTYPE_Pointer, _) _ =>
        dtyp_WF_b t && non_void_b t
    | INSTR_Call (d, e) args _ => true
    | INSTR_Alloca t _ _ => non_void_b t && dtyp_WF_b t
    | _ => false
    end.

  Definition code_WF (e : code dtyp) : bool :=
      forallb (fun '(id, c) => instr_WF c) e.

  Definition block_WF (b : LLVMAst.block dtyp) : bool :=
    code_WF (LLVMAst.blk_code b) && term_WF (blk_term b).

  Definition ocfg_WF (c : CFG.ocfg dtyp) : bool :=
    forallb (fun b => block_WF b) c.

  Definition cfg_WF (c : CFG.cfg dtyp) : bool :=
    ocfg_WF (CFG.blks c).

  Definition fun_WF (f : definition dtyp (CFG.cfg dtyp)): bool :=
    NoDup_b (df_args f) && cfg_WF (df_instrs f).

  Definition fundefs_WF (F : list (dvalue * _))
    (Attr : list (list fn_attr)) : bool :=
    (length F =? length Attr) &&
    forallb (fun '(_, f) => fun_WF f) F &&
    NoDup_b F.*1.

  Fixpoint list_eqb (l l' : list dvalue): bool :=
    match l, l' with
      | nil, nil => true
      | x :: tl, x' :: tl' =>
          Coqlib.proj_sumbool (@dvalue_eq_dec x x') && list_eqb tl tl'
      | _ , _ => false
    end.

  Lemma list_eqb_eq l l' :
    list_eqb l l' <-> l = l'.
  Proof.
    split; revert l'; induction l; cbn;
      destruct l'; intros; try done.
    { apply andb_prop_elim in H. destruct H.
      destruct (Coqlib.proj_sumbool dvalue_eq_dec) eqn: H'; try done.
      apply Coqlib.proj_sumbool_true in H'; subst.
      f_equiv; eauto. }
    { inv H.
      specialize (IHl _ eq_refl).
      destruct (list_eqb l' l'); try done.
      compute.
      destruct (dvalue_eq_dec (d1:=d) (d2:=d)) eqn: Hd; eauto. }
  Qed.

  Lemma fundefs_WF_cons_inv f F a Attr:
    fundefs_WF (f :: F) (a :: Attr) ->
    fundefs_WF [f] [a] /\ fundefs_WF F Attr.
  Proof.
    rewrite /fundefs_WF; cbn.
    intros.
    repeat (apply andb_prop_elim in H; destruct H).
    apply andb_prop_elim in H0, H1; destruct H0, H1. destruct f.
    split; repeat (apply andb_prop_intro; eauto).
  Qed.

End WF.

Section logical_relations_def.

  Context {Σ} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

   Definition code_inv C i_t i_s A_t A_s : iPropI Σ :=
    (∃ (args_t args_s : local_env),
        ldomain_tgt i_t (list_to_set args_t.*1) ∗
        ldomain_src i_s (list_to_set args_s.*1) ∗
        stack_tgt i_t ∗ stack_src i_s ∗
        frame_WF i_t i_s ∗
        ⌜args_t.*1 = args_s.*1⌝ ∗
       ([∗ list] '(l_t, v_t) ∈ args_t, [ l_t := v_t ]t i_t) ∗
       ([∗ list] '(l_s, v_s) ∈ args_s, [ l_s := v_s ]s i_s) ∗
       ([∗ list] v_t; v_s ∈ args_t.*2;args_s.*2, uval_rel v_t v_s) ∗
     checkout C ∗
     alloca_tgt i_t (list_to_set A_t : gset _) ∗
     alloca_src i_s (list_to_set A_s : gset _) ∗
     ⌜NoDup A_t⌝ ∗ ⌜NoDup A_s⌝ ∗
      ([∗ list] v_t; v_s ∈ A_t;A_s, (v_t, 0%Z) ↔h (v_s, 0%Z) ∗
           ⌜C !! (v_t, v_s) = None⌝))%I.

   Definition CFG_inv C i_t i_s : iPropI Σ :=
    (∃ args_t args_s,
        ldomain_tgt i_t (list_to_set args_t.*1) ∗
        ldomain_src i_s (list_to_set args_s.*1) ∗
        stack_tgt i_t ∗ stack_src i_s ∗
        ⌜args_t.*1 = args_s.*1⌝ ∗
       ([∗ list] '(l_t, v_t) ∈ args_t, [ l_t := v_t ]t i_t) ∗
       ([∗ list] '(l_s, v_s) ∈ args_s, [ l_s := v_s ]s i_s) ∗
       ([∗ list] v_t; v_s ∈ args_t.*2;args_s.*2, uval_rel v_t v_s) ∗
     checkout C ∗ alloca_tgt i_t ∅ ∗ alloca_src i_s ∅)%I.

  Definition empty_WF :
    gmap (loc * loc) Qp → gmap raw_id uvalue → gmap raw_id uvalue → Prop :=
    fun _ _ _ => True.

   Definition expr_logrel C (e_t e_s : itree exp_E uvalue) A_t A_s : iPropI Σ :=
    (∀ i_t i_s, code_inv C i_t i_s A_t A_s -∗
        exp_conv e_t ⪯ exp_conv e_s
        [{ (v_t, v_s),
            uval_rel v_t v_s ∗ code_inv C i_t i_s A_t A_s }])%I.

   Definition term_logrel ϒ_t ϒ_s C : iPropI Σ :=
    (∀ i_t i_s A_t A_s,
        ⌜term_WF ϒ_t⌝ -∗
        ⌜term_WF ϒ_s⌝ -∗
        code_inv C i_t i_s A_t A_s -∗
        exp_conv (denote_terminator ϒ_t) ⪯
        exp_conv (denote_terminator ϒ_s)
        [{ (r_t, r_s), code_inv C i_t i_s A_t A_s ∗
                        match r_t, r_s with
                        | inl b_t, inl b_s => ⌜b_t = b_s⌝
                        | inr v_t, inr v_s => uval_rel v_t v_s
                        | _, _ => False
                        end}])%I.

   Definition code_inv_post C i_t i_s A_t A_s : iPropI Σ:=
    (∃ nA_t nA_s,
      code_inv C i_t i_s (nA_t ++ A_t) (nA_s ++ A_s))%I.

   Definition instr_logrel id_t e_t id_s e_s C A_t A_s
     : iPropI Σ :=
    (∀ i_t i_s,
        code_inv C i_t i_s A_t A_s -∗
        instr_conv (denote_instr (id_t, e_t)) ⪯
        instr_conv (denote_instr (id_s, e_s))
        [{ (r_t, r_s),
            code_inv_post C i_t i_s A_t A_s}])%I.

   Definition phi_logrel (ϕ_t ϕ_s : itree exp_E (local_id * uvalue)) C A_t A_s : iPropI Σ :=
    (∀ args_t args_s i_t i_s,
       ⌜args_t.*1 = args_s.*1⌝ ∗
       ⌜NoDup A_t⌝ ∗ ⌜NoDup A_s⌝ ∗
       ldomain_tgt i_t (list_to_set args_t.*1) ∗ ldomain_src i_s (list_to_set args_s.*1) ∗
       ([∗ list] '(l_t, v_t) ∈ args_t, [ l_t := v_t ]t i_t) ∗
       ([∗ list] '(l_s, v_s) ∈ args_s, [ l_s := v_s ]s i_s) ∗
       ([∗ list] v_t; v_s ∈ args_t.*2;args_s.*2, uval_rel v_t v_s) ∗
      stack_tgt i_t ∗ stack_src i_s ∗ frame_WF i_t i_s ∗ checkout C ∗
      alloca_tgt i_t (list_to_set A_t) ∗ alloca_src i_s (list_to_set A_s) ∗
      ([∗ list] v_t; v_s ∈ A_t;A_s, (v_t, 0%Z) ↔h (v_s, 0%Z) ∗ ⌜C !! (v_t, v_s) = None⌝) -∗
       exp_conv ϕ_t ⪯ exp_conv ϕ_s
       [{ fun e_t e_s => ∃ l v_t v_s,
              ⌜e_t = Ret (l, v_t)⌝ ∗ ⌜e_s = Ret (l, v_s)⌝ ∗
              uval_rel v_t v_s ∗
              code_inv C i_t i_s A_t A_s }])%I.

   Definition phis_logrel (Φ_t Φ_s : itree instr_E ()) C A_t A_s : iPropI Σ :=
    (∀ i_t i_s, code_inv C i_t i_s A_t A_s -∗
       instr_conv Φ_t ⪯ instr_conv Φ_s
       [{ (r_t, r_s), code_inv C i_t i_s A_t A_s }])%I.

   Definition code_logrel c_t c_s C A_t A_s: iPropI Σ :=
    (∀ i_t i_s,
       code_inv C i_t i_s A_t A_s -∗
       instr_conv (denote_code c_t) ⪯ instr_conv (denote_code c_s)
        [{ (r_t, r_s),
            code_inv_post C i_t i_s A_t A_s }])%I.

   Definition block_logrel b_t b_s C A_t A_s : iPropI Σ :=
    (∀ i_t i_s (bid_from : block_id),
       code_inv C i_t i_s A_t A_s -∗
       instr_conv ((denote_block b_t) bid_from) ⪯
       instr_conv ((denote_block b_s) bid_from)
       [{ (r_t, r_s), code_inv_post C i_t i_s A_t A_s ∗
                      match r_t, r_s with
                      | inl b_t, inl b_s => ⌜b_t = b_s⌝
                      | inr v_t, inr v_s => uval_rel v_t v_s
                      | _, _ => False
                      end }])%I.

   Definition ocfg_logrel o_t o_s C A_t A_s b1 b2 : iPropI Σ :=
    (∀ i_t i_s,
        code_inv C i_t i_s A_t A_s -∗
      instr_conv (denote_ocfg o_t (b1, b2)) ⪯
      instr_conv (denote_ocfg o_s (b1, b2))
      [[ fun e_t e_s =>
           code_inv_post C i_t i_s A_t A_s ∗
            ∃ v_t v_s, ⌜e_t = Ret v_t⌝ ∗ ⌜e_s = Ret v_s⌝ ∗
                        match v_t, v_s with
                          | inl (id_s, id_s'), inl (id_t, id_t') =>
                              ⌜id_s = id_t⌝ ∗ ⌜id_s' = id_t'⌝
                          | inr v_t, inr v_s => uval_rel v_t v_s
                          | _,_ => False
                      end]])%I.

   Definition cfg_logrel c_t c_s C A_t A_s: iPropI Σ :=
    (∀ i_t i_s,
      code_inv C i_t i_s A_t A_s -∗
      instr_conv (denote_cfg c_t) ⪯ instr_conv (denote_cfg c_s)
      [[ fun v_t v_s =>
          ∃ r_t r_s, ⌜v_t = Ret r_t⌝ ∗ ⌜v_s = Ret r_s⌝ ∗ uval_rel r_t r_s ∗
            code_inv_post C i_t i_s A_t A_s ]])%I.

  Definition fun_logrel f_t f_s C: iPropI Σ :=
    ∀ i_t i_s args_t args_s,
     ⌜length i_s > 0 -> length i_t > 0⌝ -∗
     stack_tgt i_t -∗
     stack_src i_s -∗
     val_rel.Forall2 uval_rel args_t args_s -∗
     checkout C -∗
     L0'expr_conv (denote_function f_t args_t) ⪯ L0'expr_conv (denote_function f_s args_s)
     [[ fun v_t v_s =>
         ∃ r_t r_s, ⌜v_t = Ret r_t⌝ ∗ ⌜v_s = Ret r_s⌝ ∗
             stack_tgt i_t ∗ stack_src i_s ∗ checkout C ∗ uval_rel r_t r_s ]].

  Definition fundefs_logrel
      (F_t F_s: list (dvalue * _))
      (Attr_t Attr_s : list (list fn_attr)) C: iPropI Σ :=
      (∀ i f_t f_s (addr_t addr_s : dvalue) (attr : list fn_attr),
        ⌜F_t !! i = Some (addr_t, f_t)⌝ -∗
        ⌜F_s !! i = Some (addr_s, f_s)⌝ -∗
        ⌜Attr_t !! i = Some attr⌝ -∗
        ⌜Attr_s !! i = Some attr⌝ -∗
        dval_rel addr_t addr_s -∗
        ∀ i_t i_s args_t args_s,
          (⌜length i_s > 0 -> length i_t > 0⌝)%Z -∗
          stack_tgt i_t -∗
          stack_src i_s -∗
          val_rel.Forall2 uval_rel args_t args_s -∗
          checkout C -∗
          L0'expr_conv (denote_function f_t args_t) ⪯
          L0'expr_conv (denote_function f_s args_s)
        [[ fun v_t v_s =>
              ∃ r_t r_s, ⌜v_t = Ret r_t⌝ ∗ ⌜v_s = Ret r_s⌝ ∗
                stack_tgt i_t ∗ stack_src i_s ∗ checkout C ∗ uval_rel r_t r_s]])%I.

  Definition address_one_function (df : definition dtyp (CFG.cfg dtyp)) :
    itree LLVMEvents.L0 (dvalue * definition dtyp (CFG.cfg dtyp)) :=
    let fid := (dc_name (df_prototype df)) in
    fv <- trigger (GlobalRead fid) ;;
    Ret (fv, df).

  Definition mcfg_definitions (mcfg : CFG.mcfg dtyp) :
    itree LLVMEvents.L0 (list (dvalue * _)) :=
     (Util.map_monad address_one_function (CFG.m_definitions mcfg)).

End logical_relations_def.

Section logical_relations_properties.

  Context {Σ : gFunctors} `{!sheapGS Σ, !checkedoutGS Σ, !heapbijGS Σ}.

  (* Useful properties for preserving [CFG_inv] *)
  Lemma local_code_inv g l l0 m g0 l1 l2 m0 C i_t i_s A_t A_s:
    ⊢ code_inv C i_t i_s A_t A_s -∗
    state_interp (g, (l, l0), m) (g0, (l1, l2), m0) ==∗
    ∃ args_t args_s,
      ⌜args_t.*1 = args_s.*1⌝ ∗
      ⌜(list_to_set args_t.*1 : gset _) = list_to_set l.*1⌝ ∗
      ⌜(list_to_set args_s.*1 : gset _) = list_to_set l1.*1⌝ ∗
      ⌜NoDup A_t⌝ ∗ ⌜NoDup A_s⌝ ∗
      ([∗ list] '(l_t, v_t) ∈ args_t, [ l_t := v_t ]t i_t) ∗
      ([∗ list] '(l_s, v_s) ∈ args_s, [ l_s := v_s ]s i_s) ∗
      ([∗ list] v_t; v_s ∈ args_t.*2;args_s.*2, uval_rel v_t v_s) ∗
      ([∗ list] v_t;v_s ∈ A_t;A_s, (v_t, 0) ↔h (v_s, 0)
         ∗ ⌜C !! (v_t, v_s) = None⌝) ∗
      state_interp (g, (l, l0), m) (g0, (l1, l2), m0) ∗
      ldomain_tgt i_t (list_to_set l.*1) ∗
      ldomain_src i_s (list_to_set l1.*1) ∗
      checkout C ∗
      stack_tgt i_t ∗ stack_src i_s ∗
      frame_WF i_t i_s ∗
      alloca_tgt i_t (list_to_set A_t) ∗ alloca_src i_s (list_to_set A_s).
  Proof.
    iIntros "CI SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    iDestruct "CI" as  (??) "(Hd_t & Hd_s & Hf_t & Hf_s & WF &
        %Harg & Hargs_t & Hargs_s &
        Hv & HC & Ha_t & Ha_s & %Hnd_t & %Hnd_s & #Hl)"; subst.

    destruct_HC "Hh_s".

    iDestruct "Hh_t" as (cft hFt)
        "(Hσ_t&HB_t&HCF_t&HA_t&HL_t&HD_t&HSA_t&HG_t&%Hdup_t&%Hbs_t&%Hwf_t)".

    iDestruct (ghost_var_agree with "Hf_s HCF") as %Hf_s.
    iDestruct (ghost_var_agree with "Hf_t HCF_t") as %Hf_t. subst.
    iDestruct (ghost_var_agree with "Hd_s HD") as %Hd_s.
    iDestruct (ghost_var_agree with "Hd_t HD_t") as %Hd_t.
    iExists args_t, args_s.
    cbn in *.

    do 5 (iSplitL ""; [ done | ]).
    iFrame.
    iFrame "Hl".

    repeat iExists _; iFrame.

    iSplitL "Hd_s Hf_s HA HL HSA Hb".
    { repeat iExists _; iFrame. rewrite Hd_s. by iFrame. }

    rewrite Hd_t.
    repeat iExists _; iFrame. cbn; done.
  Qed.

  Lemma local_CFG_inv g l l0 m g0 l1 l2 m0 C i_t i_s:
    ⊢ CFG_inv C i_t i_s -∗
    state_interp (g, (l, l0), m) (g0, (l1, l2), m0) ==∗
    ∃ args_t args_s,
      ⌜args_t.*1 = args_s.*1⌝ ∗
      ⌜(list_to_set args_t.*1 : gset _) = list_to_set l.*1⌝ ∗
      ⌜(list_to_set args_s.*1 : gset _) = list_to_set l1.*1⌝ ∗
      ([∗ list] '(l_t, v_t) ∈ args_t, [ l_t := v_t ]t i_t) ∗
      ([∗ list] '(l_s, v_s) ∈ args_s, [ l_s := v_s ]s i_s) ∗
      ([∗ list] v_t; v_s ∈ args_t.*2;args_s.*2, uval_rel v_t v_s) ∗
      state_interp (g, (l, l0), m) (g0, (l1, l2), m0) ∗
      ldomain_tgt i_t (list_to_set l.*1) ∗
      ldomain_src i_s (list_to_set l1.*1) ∗
      checkout C ∗
      stack_tgt i_t ∗ stack_src i_s ∗
      alloca_tgt i_t ∅ ∗ alloca_src i_s ∅.
  Proof.
    iIntros "CI SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & SI)".
    iDestruct "CI" as  (??) "(Hd_t & Hd_s & Hf_t & Hf_s &
                          %Harg & Hargs_t & Hargs_s & Hv & HC & Ha_t & Ha_s)"; subst.

    destruct_HC "Hh_s".

    iDestruct "Hh_t" as (cft hFt)
        "(Hσ_t&HB_t&HCF_t&HA_t&HL_t&HD_t&HSA_t&HG_t&%Hdup_t&%Hbs_t&%Hwf_t)".

    iDestruct (ghost_var_agree with "Hf_s HCF") as %Hf_s.
    iDestruct (ghost_var_agree with "Hf_t HCF_t") as %Hf_t. subst.
    iDestruct (ghost_var_agree with "Hd_s HD") as %Hd_s.
    iDestruct (ghost_var_agree with "Hd_t HD_t") as %Hd_t.
    iExists args_t, args_s.
    cbn in *.

    iFrame.
    do 3 (iSplitL ""; [ done | ]).

    repeat iExists _; iFrame.

    iSplitL "Hd_s Hf_s HA HL HSA Hb".
    { repeat iExists _; iFrame. rewrite Hd_s. by iFrame. }

    rewrite Hd_t.
    repeat iExists _; iFrame. cbn; done.
  Qed.

  Lemma local_write_refl x v_t v_s i_t i_s A_t A_s:
    ⊢ code_inv ∅ i_t i_s A_t A_s -∗ uval_rel v_t v_s -∗
    trigger (LocalWrite x v_t) ⪯ trigger (LocalWrite x v_s)
      [{ (v1, v2), code_inv ∅i_t i_s A_t A_s }].
  Proof.
    iIntros "CI #Hrel".
    iApply sim_update_si.

    iIntros "%σ_t %σ_s SI".
    destruct σ_t as ((?&(?&?))&?).
    destruct σ_s as ((?&(?&?))&?).
    iDestruct (local_code_inv with "CI SI") as ">H".
    iDestruct "H" as (?????)
        "(%Hnd_t & %Hnd_s & Hlt & Hls & Hv & #Ha_v & SI & Hd_t & Hd_s
          & HC & Hf_t & Hf_s & #WF & Ha_t & Ha_s)".
    iFrame.

    destruct (decide (x ∈ l.*1)).
    {
      assert (exists n v, args_t !! n = Some (x, v)).
      { clear -H0 e.
        eapply (@elem_of_list_to_set raw_id
                  (@gset raw_id _ _)) in e; last typeclasses eauto.
        Unshelve. all : try typeclasses eauto.
        setoid_rewrite <-H0 in e. clear -e.
        rewrite elem_of_list_to_set in e.
        by apply elem_of_fst_list_some. }

      assert (exists n v, args_s !! n = Some (x, v)).
      { rewrite H in H0. clear -H0 e.
        eapply (@elem_of_list_to_set raw_id
                  (@gset raw_id _ _)) in e; last typeclasses eauto.
        Unshelve. all : try typeclasses eauto.
        setoid_rewrite <-H0 in e. clear -e.
        rewrite elem_of_list_to_set in e.
        by apply elem_of_fst_list_some. }
      destruct H2 as (?&?&?).
      destruct H3 as (?&?&?).

      iDestruct (lmapsto_no_dup with "Hlt") as "%Hdup_t".
      iDestruct (lmapsto_no_dup with "Hls") as "%Hdup_s".

      iDestruct (big_sepL_delete with "Hlt") as "(Helemt & Hl_t)"; eauto; cbn.
      iDestruct (big_sepL_delete with "Hls") as "(Helems & Hl_s)"; eauto; cbn.

      iApply (sim_expr_bupd_mono with "[Hl_t Hl_s Hd_t Hd_s HC Hv Ha_t Ha_s]");
        [ | iApply (sim_local_write with "Hf_t Hf_s Helemt Helems")].
      iIntros (??) "Hp".
      iDestruct "Hp" as (????) "(Ht & Hs & Hf_t & Hf_s)".

      iModIntro. iExists _,_.
      do 2 (iSplitL ""; [ done | ]); rewrite /CFG_inv.

      pose proof (no_dup_fst_list_some _ _ _ _ _ _ _ Hdup_t Hdup_s H H2 H3); subst.
      iExists (<[x2 := (x, v_t)]> args_t),
              (<[x2 := (x, v_s)]> args_s). iFrame.

      setoid_rewrite (big_sepL_delete (fun i '(l_t, v_t1)=> [ l_t := v_t1 ]t i_t) _ x2 (x, v_t))%I; cycle 1.
      { rewrite list_lookup_insert; eauto.
        by apply lookup_lt_is_Some. }
      setoid_rewrite (big_sepL_delete (fun i '(l_t, v_t1)=> [ l_t := v_t1 ]s i_s) _ x2 (x, v_s))%I; cycle 1.
      { rewrite list_lookup_insert; eauto.
        by apply lookup_lt_is_Some. }
      iFrame.

      do 2 (erewrite list_lookup_insert_list_to_set; eauto);
      rewrite H0 H1; iFrame.
      iFrame "WF".
      cbn; rewrite !list_insert_fst.
      iSplitL ""; first ( iPureIntro; by f_equiv ).

      iSplitL "Hl_t".
      { by iApply big_sepL_delete_insert. }
      iSplitL "Hl_s".
      { by iApply big_sepL_delete_insert. }

      rewrite !list_insert_snd.
      iSplitR ""; last by iFrame "Ha_v".
      iApply (big_sepL2_insert args_t.*2 args_s.*2 uval_rel with "Hrel Hv"). }

    { assert (Hn : x ∉ (list_to_set l.*1 : gset _)) by set_solver.
      assert (Hn1 : x ∉ (list_to_set l1.*1 : gset _)).
      { rewrite -H1 -H H0; set_solver. }
      iApply (sim_expr_bupd_mono with "[HC Ha_t Ha_s Hv Hlt Hls]");
        [ | iApply (sim_local_write_alloc _ _ _ _ _ _ _ _ Hn Hn1 with "Hd_t Hd_s Hf_t Hf_s")].
      iIntros (??) "Hp".
      iDestruct "Hp" as (????) "(Ht & Hs & Hd_t & Hd_s & Hf_t & Hf_s)".
      iModIntro. iExists _,_.
      do 2 (iSplitL ""; [ done | ]). rewrite /CFG_inv.
      iExists ((x, v_t) :: args_t), ((x, v_s) :: args_s); iFrame.
      cbn. rewrite H0 H1; iFrame.
      iFrame "WF".
      iSplitL "".
      { rewrite H; done. }
      by iFrame "Hrel Ha_v". }
  Qed.

  Lemma local_write_refl_cfg C x v_t v_s i_t i_s :
    ⊢ CFG_inv C i_t i_s -∗ uval_rel v_t v_s -∗
    trigger (LocalWrite x v_t) ⪯ trigger (LocalWrite x v_s)
      [{ (v1, v2), CFG_inv C i_t i_s }].
  Proof.
    iIntros "CI #Hrel".
    iApply sim_update_si.

    iIntros "%σ_t %σ_s SI".
    destruct σ_t as ((?&(?&?))&?).
    destruct σ_s as ((?&(?&?))&?).
    iDestruct (local_CFG_inv with "CI SI") as ">H".
    iDestruct "H" as
      (?????)
        "(Hlt & Hls & Hv & SI & Hd_t & Hd_s & HC & Hf_t & Hf_s & Ha_t & Ha_s)".
    iFrame.

    destruct (decide (x ∈ l.*1)).
    {
      assert (exists n v, args_t !! n = Some (x, v)).
      { clear -H0 e.
        eapply (@elem_of_list_to_set raw_id (@gset local_loc _ _)) in e.
        Unshelve. all : try typeclasses eauto.
        setoid_rewrite <-H0 in e. clear -e.
        rewrite elem_of_list_to_set in e.
        by apply elem_of_fst_list_some. }

      assert (exists n v, args_s !! n = Some (x, v)).
      { rewrite H in H0. clear -H0 e.
        eapply (@elem_of_list_to_set raw_id (@gset local_loc _ _)) in e.
        Unshelve. all : try typeclasses eauto.
        setoid_rewrite <-H0 in e. clear -e.
        rewrite elem_of_list_to_set in e.
        by apply elem_of_fst_list_some. }
      destruct H2 as (?&?&?).
      destruct H3 as (?&?&?).

      iDestruct (lmapsto_no_dup with "Hlt") as "%Hdup_t".
      iDestruct (lmapsto_no_dup with "Hls") as "%Hdup_s".

      iDestruct (big_sepL_delete with "Hlt") as "(Helemt & Hl_t)"; eauto; cbn.
      iDestruct (big_sepL_delete with "Hls") as "(Helems & Hl_s)"; eauto; cbn.

      iApply (sim_expr_bupd_mono with "[Hl_t Hl_s Hd_t Hd_s HC Hv Ha_t Ha_s]");
        [ | iApply (sim_local_write with "Hf_t Hf_s Helemt Helems")].
      iIntros (??) "Hp".
      iDestruct "Hp" as (????) "(Ht & Hs & Hf_t & Hf_s)".

      iModIntro. iExists _,_.
      do 2 (iSplitL ""; [ done | ]); rewrite /CFG_inv.

      pose proof (no_dup_fst_list_some _ _ _ _ _ _ _ Hdup_t Hdup_s H H2 H3); subst.
      iExists (<[x2 := (x, v_t)]> args_t),
              (<[x2 := (x, v_s)]> args_s). iFrame.

      setoid_rewrite (big_sepL_delete (fun i '(l_t, v_t1)=> [ l_t := v_t1 ]t i_t) _ x2 (x, v_t))%I; cycle 1.
      { rewrite list_lookup_insert; eauto.
        by apply lookup_lt_is_Some. }
      setoid_rewrite (big_sepL_delete (fun i '(l_t, v_t1)=> [ l_t := v_t1 ]s i_s) _ x2 (x, v_s))%I; cycle 1.
      { rewrite list_lookup_insert; eauto.
        by apply lookup_lt_is_Some. }
      iFrame.

      do 2 (erewrite list_lookup_insert_list_to_set; eauto);
      rewrite H0 H1; iFrame.
      cbn; rewrite !list_insert_fst.
      iSplitL ""; first ( iPureIntro; by f_equiv ).

      iSplitL "Hl_t".
      { by iApply big_sepL_delete_insert. }
      iSplitL "Hl_s".
      { by iApply big_sepL_delete_insert. }

      rewrite !list_insert_snd.
      iApply (big_sepL2_insert args_t.*2 args_s.*2 uval_rel with "Hrel Hv"). }

    { assert (Hn : x ∉ (list_to_set l.*1 : gset _)) by set_solver.
      assert (Hn1 : x ∉ (list_to_set l1.*1 : gset _)).
      { rewrite -H1 -H H0; set_solver. }
      iApply (sim_expr_bupd_mono with "[HC Ha_t Ha_s Hv Hlt Hls]");
        [ | iApply (sim_local_write_alloc _ _ _ _ _ _ _ _ Hn Hn1 with "Hd_t Hd_s Hf_t Hf_s")].
      iIntros (??) "Hp".
      iDestruct "Hp" as (????) "(Ht & Hs & Hd_t & Hd_s & Hf_t & Hf_s)".
      iModIntro. iExists _,_.
      do 2 (iSplitL ""; [ done | ]). rewrite /CFG_inv.
      iExists ((x, v_t) :: args_t), ((x, v_s) :: args_s); iFrame.
      cbn. rewrite H0 H1; iFrame.
      rewrite H; iSplit; done. }
  Qed.

  Lemma local_read_refl C x i_t i_s A_t A_s:
    ⊢ code_inv C i_t i_s A_t A_s -∗
    trigger (LocalRead x) ⪯ trigger (LocalRead x)
      [{ (v1, v2), uval_rel v1 v2 ∗ code_inv C i_t i_s A_t A_s }].
  Proof.
    iIntros "CI".
    iApply sim_update_si.

    iIntros "%σ_t %σ_s SI".
    destruct σ_t as ((?&(?&?))&?).
    destruct σ_s as ((?&(?&?))&?).
    iDestruct (local_code_inv with "CI SI") as ">H".
    iDestruct "H" as
      (args_t args_s Hdom Ht Hs Hnd_t Hnd_s)
        "(Hlt & Hls & Hv & #Hav & SI & Hf_t & Hf_s & HC & Hs_t & Hs_s & #HWF& Ha_t & Ha_s)".
    iFrame.

    destruct (decide (x ∈ l.*1)).
    {
      assert (exists n v, args_t !! n = Some (x, v)).
      { clear -Ht e.
        eapply (@elem_of_list_to_set raw_id (@gset local_loc _ _)) in e.
        Unshelve. all : try typeclasses eauto.
        setoid_rewrite <-Ht in e. clear -e.
        rewrite elem_of_list_to_set in e.
        by apply elem_of_fst_list_some. }

      assert (exists n v, args_s !! n = Some (x, v)).
      { rewrite Hdom in Ht. clear -Ht e.
        eapply (@elem_of_list_to_set raw_id (@gset local_loc _ _)) in e.
        Unshelve. all : try typeclasses eauto.
        setoid_rewrite <-Ht in e. clear -e.
        rewrite elem_of_list_to_set in e.
        by apply elem_of_fst_list_some. }

      destruct H0 as (?&?&?).
      destruct H as (?&?&?).

      iDestruct (lmapsto_no_dup with "Hlt") as "%Hdup_t".
      iDestruct (lmapsto_no_dup with "Hls") as "%Hdup_s".
      pose proof (no_dup_fst_list_some _ _ _ _ _ _ _ Hdup_t Hdup_s Hdom H H0);
        subst.

      iDestruct (big_sepL_delete with "Hlt") as "(Helemt & Hl_t)"; eauto; cbn.
      iDestruct (big_sepL_delete with "Hls") as "(Helems & Hl_s)"; eauto; cbn.

      iApply (sim_expr_bupd_mono with "[Hl_t Hl_s Hf_t Hf_s HC Hv Ha_t Ha_s]");
        [ | iApply (sim_local_read with "Helemt Helems Hs_t Hs_s")].
      iIntros (??) "Hp".
      iDestruct "Hp" as (????) "(%Ht' & %Hs' & Ht' & Hs' & Hf_t' & Hf_s')";
        subst.
      iModIntro. iExists _,_.
      do 2 (iSplitL ""; [ done | ]).
      iAssert (uval_rel v_t' v_s') as "#Hv'".
      { iDestruct (big_sepL2_lookup _ _ _ x0 with "Hv") as "H"; eauto.
        { by eapply list_lookup_snd. }
        { by eapply list_lookup_snd. } }

      iSplitL ""; [ done | ].

      iExists args_t, args_s; iFrame.

      rewrite Ht Hs. iFrame.
      iSplitL ""; [ done | ].

      setoid_rewrite big_sepL_delete at 3; eauto; iFrame.
      setoid_rewrite big_sepL_delete at 2; eauto;
        by iFrame "Hav Hl_s Hs'". }
    { iApply (sim_local_read_not_in_domain with "Hf_s Hs_s").
      rewrite -Hs -Hdom Ht. set_solver. }
  Qed.

  Lemma local_read_refl_cfg C x i_t i_s :
    ⊢ CFG_inv C i_t i_s -∗
    trigger (LocalRead x) ⪯ trigger (LocalRead x)
      [{ (v1, v2), uval_rel v1 v2 ∗ CFG_inv C i_t i_s }].
  Proof.
    iIntros "CI".
    iApply sim_update_si.

    iIntros "%σ_t %σ_s SI".
    destruct σ_t as ((?&(?&?))&?).
    destruct σ_s as ((?&(?&?))&?).
    iDestruct (local_CFG_inv with "CI SI") as ">H".
    iDestruct "H" as
      (args_t args_s Hdom Ht Hs)
        "(Hlt & Hls & Hv & SI & Hf_t & Hf_s & HC & Hs_t & Hs_s & Ha_t & Ha_s)".
    iFrame.

    destruct (decide (x ∈ l.*1)).
    {
      assert (exists n v, args_t !! n = Some (x, v)).
      { clear -Ht e.
        eapply (@elem_of_list_to_set raw_id (@gset local_loc _ _)) in e.
        Unshelve. all : try typeclasses eauto.
        setoid_rewrite <-Ht in e. clear -e.
        rewrite elem_of_list_to_set in e.
        by apply elem_of_fst_list_some. }

      assert (exists n v, args_s !! n = Some (x, v)).
      { rewrite Hdom in Ht. clear -Ht e.
        eapply (@elem_of_list_to_set raw_id (@gset local_loc _ _)) in e.
        Unshelve. all : try typeclasses eauto.
        setoid_rewrite <-Ht in e. clear -e.
        rewrite elem_of_list_to_set in e.
        by apply elem_of_fst_list_some. }

      destruct H0 as (?&?&?).
      destruct H as (?&?&?).

      iDestruct (lmapsto_no_dup with "Hlt") as "%Hdup_t".
      iDestruct (lmapsto_no_dup with "Hls") as "%Hdup_s".
      pose proof (no_dup_fst_list_some _ _ _ _ _ _ _ Hdup_t Hdup_s Hdom H H0);
        subst.

      iDestruct (big_sepL_delete with "Hlt") as "(Helemt & Hl_t)"; eauto; cbn.
      iDestruct (big_sepL_delete with "Hls") as "(Helems & Hl_s)"; eauto; cbn.

      iApply (sim_expr_bupd_mono with "[Hl_t Hl_s Hf_t Hf_s HC Hv Ha_t Ha_s]");
        [ | iApply (sim_local_read with "Helemt Helems Hs_t Hs_s")].
      iIntros (??) "Hp".
      iDestruct "Hp" as (????) "(%Ht' & %Hs' & Ht' & Hs' & Hf_t' & Hf_s')";
        subst.
      iModIntro. iExists _,_.
      do 2 (iSplitL ""; [ done | ]).
      iAssert (uval_rel v_t' v_s') as "#Hv'".
      { iDestruct (big_sepL2_lookup _ _ _ x0 with "Hv") as "H"; eauto.
        { by eapply list_lookup_snd. }
        { by eapply list_lookup_snd. } }

      iSplitL ""; [ done | ].

      iExists args_t, args_s; iFrame.

      rewrite Ht Hs. iFrame.
      iSplitL ""; [ done | ].

      setoid_rewrite big_sepL_delete at 3; eauto; iFrame.
      setoid_rewrite big_sepL_delete at 2; eauto; iFrame. }
    { iApply (sim_local_read_not_in_domain with "Hf_s Hs_s").
      rewrite -Hs -Hdom Ht. set_solver. }
  Qed.

  Ltac destruct_state σ :=
    destruct σ as ((?&?)&(?&?)&?).

  Lemma load_must_be_addr_src τ x_t x_s Φ:
    ⊢ (∀ ptr, ⌜x_s = DVALUE_Addr ptr⌝ -∗
      trigger (Load τ x_t) ⪯ trigger (Load τ x_s) [{ Φ}]) -∗
    trigger (Load τ x_t) ⪯ trigger (Load τ x_s) [{ Φ }].
  Proof.
    iIntros "H".

    destruct x_s; [ by iApply "H" | ..].
    all: rewrite sim_expr_eq /sim_expr_;
      iIntros (??) "SI";
      destruct_state σ_s;
      rewrite /interp_L2;
       rewrite (interp_state_vis _ _ _ (g, p, (g0, g1, f))) ; cbn; rewrite /add_tau;
       rewrite !bind_tau; iApply sim_coind_tauR; cbn;
        rewrite !bind_bind bind_vis; iApply sim_coind_exc.
  Qed.

  Lemma load_must_be_addr τ x_t x_s Φ:
     dval_rel x_t x_s -∗
    (∀ ptr ptr', ⌜x_s = DVALUE_Addr ptr⌝ -∗
          ⌜x_t = DVALUE_Addr ptr'⌝ -∗
      trigger (Load τ x_t) ⪯ trigger (Load τ x_s) [{ Φ}]) -∗
    trigger (Load τ x_t) ⪯ trigger (Load τ x_s) [{ Φ }].
  Proof.
    iIntros "Hr H".
    iApply load_must_be_addr_src.
    iIntros (??); subst.
    iDestruct (dval_rel_addr_inv with "Hr") as (?) "%"; subst.
    rewrite unfold_dval_rel. 
    by iApply "H".
  Qed.

  Lemma load_refl
    (x_t x_s : dvalue) (τ : dtyp)
    (i_t i_s : list frame_names) (A_t A_s : list loc):
    dtyp_WF τ ->
    ⊢ code_inv ∅ i_t i_s A_t A_s -∗
      dval_rel x_t x_s -∗
      trigger (Load τ x_t) ⪯ trigger (Load τ x_s)
      [{ (v1, v2), uval_rel v1 v2 ∗ code_inv ∅ i_t i_s A_t A_s }].
  Proof.
    (* If they are related dvalues, they must be values in the public bijection. *)
    iIntros (Hwf) "CI #Hr".
    iApply load_must_be_addr; [ done | ].
    iIntros (????); subst.
    rewrite /CFG_inv.

    iDestruct "CI" as (??)
      "(Hd_t & Hd_s & Hf_t & Hf_s & #WF& %Harg &
        Hargs_t & Hargs_s & Hv & HC & Ha_t & Ha_s)"; subst.
    rewrite unfold_dval_rel; cbn.
    iApply (sim_expr_bupd_mono with
              "[Hd_t Hd_s Hf_t Hf_s Ha_t Ha_s Hv Hargs_t Hargs_s]"); [
        | iApply (sim_bij_load_None1 with "Hr") ]; eauto.
    2 : set_solver.
    iIntros (??) "H".

    iDestruct "H" as (????) "(H1 & H2)"; iFrame.
    iModIntro; repeat iExists _; iFrame; try done.
    repeat (iSplitL ""; [ done | ]).
    repeat iExists _; iFrame; try done. by iFrame "WF".
  Qed.

  Lemma load_refl_cfg x_t x_s τ C i_t i_s:
    dtyp_WF τ ->
    (forall a_t, x_t = DVALUE_Addr a_t ->
     forall a_s, x_s = DVALUE_Addr a_s ->
            C !! (a_t.1, a_s.1) = None \/
            (∃ q, C !! (a_t.1, a_s.1) = Some q /\ (q < 1)%Qp)) ->
    ⊢ CFG_inv C i_t i_s -∗
      dval_rel x_t x_s -∗
      trigger (Load τ x_t) ⪯ trigger (Load τ x_s)
      [{ (v1, v2), uval_rel v1 v2 ∗ CFG_inv C i_t i_s }].
  Proof.
    (* If they are related dvalues, they must be values in the public bijection. *)
    iIntros (Hwf Hlu) "CI #Hr".
    iApply load_must_be_addr; [ done | ].
    iIntros (????); subst.
    rewrite /CFG_inv.

    iDestruct "CI" as
      (??) "(Hd_t & Hd_s & Hf_t & Hf_s & %Harg & Hargs_t & Hargs_s & Hv & HC & Ha_t & Ha_s)"; subst.
    rewrite unfold_dval_rel; cbn.
    specialize (Hlu _ eq_refl _ eq_refl).
    destruct Hlu.
    { iApply (sim_expr_bupd_mono with
              "[Hd_t Hd_s Hf_t Hf_s Ha_t Ha_s Hv Hargs_t Hargs_s]"); [
        | iApply (sim_bij_load_None1 with "Hr") ]; eauto.
      iIntros (??) "H".

      iDestruct "H" as (????) "(H1 & H2)"; iFrame.
      iModIntro; repeat iExists _; iFrame; try done.
      repeat (iSplitL ""; [ done | ]).
      repeat iExists _; iFrame; try done. }
    { destruct H as (?&HC&Hq).
      iApply (sim_expr_bupd_mono with
              "[Hd_t Hd_s Hf_t Hf_s Ha_t Ha_s Hv Hargs_t Hargs_s]"); [
        | iApply (sim_bij_load_Some with "Hr") ]; eauto.
      iIntros (??) "H".

      iDestruct "H" as (????) "(H1 & H2)"; iFrame.
      iModIntro; repeat iExists _; iFrame; try done.
      repeat (iSplitL ""; [ done | ]).
      repeat iExists _; iFrame; try done. }
  Qed.

  Lemma store_must_be_addr_src x_t p_t x_s p_s Φ:
    ⊢ (∀ ptr, ⌜p_s = DVALUE_Addr ptr⌝ -∗
      trigger (Store p_t x_t) ⪯ trigger (Store p_s x_s) [{ Φ}]) -∗
    trigger (Store p_t x_t) ⪯ trigger (Store p_s x_s) [{ Φ }].
  Proof.
    iIntros "H".
    destruct p_s eqn: Hs; [ by iApply "H" | ..].
    all: rewrite {2} sim_expr_fixpoint; iIntros (??) "SI";
      destruct σ_s as (?&(?&?)&?); destruct p;
      rewrite /interp_L2;
      remember
         (State.interp_state
          (handle_L0_L2 vir_handler) (store x_t p_t) σ_t);
      iApply sim_coind_Proper; [ done |
        rewrite interp_state_vis; cbn;
        rewrite /add_tau; cbn; rewrite bind_tau bind_bind;
        reflexivity | ];
      iApply sim_coind_tauR;
      iApply sim_coind_Proper; [ done |
        setoid_rewrite bind_trigger;
          by rewrite bind_vis | ];
      iModIntro; iApply sim_coind_exc.

    Unshelve. all : try exact vir_handler; eauto.
    all : typeclasses eauto.
  Qed.

  Lemma store_must_be_addr x_t p_t x_s p_s Φ:
    dval_rel p_t p_s -∗
    (∀ ptr ptr',
          ⌜p_s = DVALUE_Addr ptr⌝ -∗
          ⌜p_t = DVALUE_Addr ptr'⌝ -∗
      trigger (Store p_t x_t) ⪯ trigger (Store p_s x_s) [{ Φ}]) -∗
    trigger (Store p_t x_t) ⪯ trigger (Store p_s x_s) [{ Φ }].
  Proof.
    iIntros "Hr H".
    iApply store_must_be_addr_src.
    iIntros (??); subst.
    iDestruct (dval_rel_addr_inv with "Hr") as (?) "%"; subst.
    rewrite unfold_dval_rel; cbn.
    by iApply "H".
  Qed.

  Lemma store_refl
    (x_t x_s v_t v_s : dvalue) (τ : dtyp)
    (i_t i_s : list frame_names) (A_t A_s : list loc):
    dtyp_WF τ ->
    dvalue_has_dtyp v_s τ ->
    dvalue_has_dtyp v_t τ ->
    ⊢ code_inv ∅ i_t i_s A_t A_s -∗
      dval_rel x_t x_s -∗
      dval_rel v_t v_s -∗
    trigger (Store x_t v_t) ⪯ trigger (Store x_s v_s)
      [{ (v1, v2), code_inv ∅ i_t i_s A_t A_s }].
  Proof.
    iIntros (WF1 WF2 WF3) "CI #Dv #Dt".
    iApply store_must_be_addr; [ done | ].
    iIntros (????); subst.
    iApply sim_update_si.
    iIntros (??) "SI".
    iDestruct (dval_rel_addr' with "Dv") as "#Hb".
    iModIntro; iFrame.

    iDestruct "CI" as (??)
      "(Hd_t & Hd_s & Hf_t & Hf_s & #HWF & %Harg & Hargs_t & Hargs_s & Hv &
          HC & Ha_t & Ha_s)"; subst.
    iApply (sim_expr_bupd_mono with "[Hargs_t Hargs_s Hd_t Hd_s Hf_t
        Hf_s Hv Ha_t Ha_s] [HC]"); cycle 1.
    { iApply (sim_bij_store1 with "Dt Hb"); eauto. set_solver. }
    cbn. iIntros (??) "H".
    iDestruct "H" as (????) "H".
    iModIntro; repeat iExists _; iFrame.
    do 2 (iSplitL ""; [done | ]); repeat iExists _; iFrame
    ; by iFrame "HWF".
  Qed.

  Lemma store_refl_cfg x_t x_s v_t v_s τ C i_t i_s:
    dtyp_WF τ ->
    dvalue_has_dtyp v_t τ ->
    dvalue_has_dtyp v_s τ ->
    (forall a_t, x_t = DVALUE_Addr a_t ->
    forall a_s, x_s = DVALUE_Addr a_s ->
            C !! (a_t.1, a_s.1) = None) ->
    ⊢ CFG_inv C i_t i_s -∗
      dval_rel x_t x_s -∗
      dval_rel v_t v_s -∗
    trigger (Store x_t v_t) ⪯ trigger (Store x_s v_s)
      [{ (v1, v2), CFG_inv C i_t i_s }].
  Proof.
    iIntros (Hwf Hdt1 Hdt2 Hlu) "CI #Dv #Dt".
    iApply store_must_be_addr; [ done | ].
    iIntros (????); subst.
    iApply sim_update_si.
    iIntros (??) "SI".
    iDestruct (dval_rel_addr' with "Dv") as "#Hb".
    iModIntro; iFrame.

    iDestruct "CI" as
      (??) "(Hd_t & Hd_s & Hf_t & Hf_s & %Harg & Hargs_t & Hargs_s & Hv & HC & Ha_t & Ha_s)"; subst.
    iApply (sim_expr_bupd_mono with "[Hargs_t Hargs_s Hd_t Hd_s Hf_t Hf_s Hv Ha_t Ha_s] [HC]"); cycle 1.
    { iApply (sim_bij_store1 with "Dt Hb"); eauto. }
    cbn. iIntros (??) "H".
    iDestruct "H" as (????) "H".
    iModIntro; repeat iExists _; iFrame.
    do 2 (iSplitL ""; [done | ]). rewrite /CFG_inv.
    repeat iExists _; by iFrame.
  Qed.

  Lemma alloca_refl_bij
    (τ : dtyp) (C : gmap (loc * loc) Qp)
    (i_t i_s : list frame_names) (A_t A_s : list loc):
    non_void τ ->
    code_inv C i_t i_s A_t A_s -∗
    trigger (Alloca τ) ⪯ trigger (Alloca τ)
    [{ (a, a0), ∃ l_t l_s, dval_rel a a0 ∗
        code_inv C i_t i_s (l_t :: A_t) (l_s :: A_s) }].
  Proof.
    iIntros (WF) "CI".

    rewrite -(bind_ret_r (trigger (Alloca τ))).
    iApply sim_expr_bind.

    iDestruct "CI" as
      (??)
        "(Hd_t & Hd_s & Hf_t & Hf_s & # HWF & %Harg & Hargs_t & Hargs_s & Hv & HC
          & Ha_t & Ha_s & %Hnd_t & %Hnd_s & Ha_bij)";
      subst.
    iApply (sim_expr_bupd_mono with "[Hargs_t Hargs_s Hd_t Hd_s Hv HC Ha_bij]");
      [ | iApply (sim_alloca with "Ha_t Ha_s Hf_t Hf_s")]; eauto.
    iIntros (??) "H".
    iDestruct "H" as (????) "H".
    rewrite H H0; clear H H0; rewrite !bind_ret_l.

    iDestruct "H" as
      (??????) "(Ht & Hs & Ha_t & Ha_s & Hs_t & Hs_s & Hbl_t & Hbl_s)"; subst.

    iApply sim_update_si.
    iModIntro; iIntros (??) "SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %WF_SI & SI)".

    iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), l_t = b_t') S⌝)%I) as "%Hext_t".
    { iIntros (([b_t' b_s'] & Hin & <-)).
      iDestruct "Hbij" as "(Hbij & Hheap)".
      iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin.
      iDestruct "Hr" as (? v_t' v_s') "(Hr_t & Ha_t' & Ha_s')".
      by iApply (heap_block_size_excl with "Hbl_t Ha_t'"). }

    iPoseProof (lb_rel_empty_blocks τ) as "Hrel".
    iDestruct (heapbij_insert_ctx $! _ _ with
          "Hbij Hs_t Hs_s Ha_t Ha_s Hh_t Hh_s Ht Hs Hrel Hbl_t Hbl_s") as
      ">(Hbij & #Hr & Ha_t & Ha_s & Hs_t & Hs_s & Hh_t & Hh_s)".

    destruct_HC "Hh_s".
    iDestruct (ghost_var_agree with "Hs_s HCF") as %Hd_s; subst.
    iDestruct (ghost_var_agree with "HC H_c") as %Hc_s; subst.
    rewrite allocaS_eq.
    iDestruct (ghost_var_agree with "Ha_s HA") as %Hd_s; subst.

    iDestruct "Hh_t" as (cft hFt)
        "(Hσ_t&HB_t&HCF_t&HA_t&HL_t&HD_t&HSA_t&HG_t&%Hdup_t&%Hbs_t&%Hwf_t)".
    iDestruct (ghost_var_agree with "Hs_t HCF_t") as %Hd_t; subst.
    iDestruct (ghost_var_agree with "Ha_t HA_t") as %Hd_t; subst.

    iFrame.

    iSplitR "Hargs_t Hargs_s Hd_t Hd_s Hv HC Ha_t Ha_s Hs_t Hs_s Ha_bij".
    { iExists _, ({[(l_t, l_s)]} ∪ S), G; iFrame.
      iSplitR "HB_t HCF_t HA_t HL_t HD_t HSA_t".
      { iModIntro; iExists _, _; iFrame. done. }
      iSplitR "".
      { iModIntro; iExists _, _; iFrame. done. }
      iModIntro. iPureIntro. set_solver. }

    iApply sim_expr_base.

    iModIntro.
    do 2 iExists _; iFrame.
    do 2 (iSplitL ""; [ done  | ]).
    iExists l_t, l_s; iFrame.

    iSplitL ""; first by iApply dval_rel_addr.
    repeat iExists _; iFrame.
    iFrame "HWF".
    iSplitL ""; first done.
    rewrite allocaS_eq; iFrame "Hr Ha_t Ha_s".
    iPureIntro.
    rewrite -not_elem_of_dom.
    do 2 (split; first (apply NoDup_cons; set_solver)).
    intro. apply Hext_t.
    exists (l_t, l_s); split; auto.

    Unshelve. all : set_solver.
  Qed.


End logical_relations_properties.
