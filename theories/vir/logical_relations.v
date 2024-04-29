From Coq Require Import String List Program.Equality.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export gen_heap ghost_map.
From iris.base_logic Require Import gset_bij.

From ITree Require Import
  ITree Eq Interp.InterpFacts Interp.RecursionFacts Events.StateFacts TranslateFacts.

From Vellvm Require Import Syntax.LLVMAst Syntax.DynamicTypes
  Semantics.InterpretationStack Handlers Utils.Util Semantics.LLVMEvents.

From Equations Require Import Equations.

From Paco Require Import paco.

From velliris.logic Require Import satisfiable.
From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
   vir spec globalbij heapbij frame_laws primitive_laws bij_laws.
From velliris.utils Require Import no_event.

Set Default Proof Using "Type*".

Import ListNotations.
Import SemNotations.

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

  Context {Σ} `{!vellirisGS Σ}.

(* ------------------------------------------------------------------------ *)
  (* Auxiliary definitions for stating invariants for logical relation. *)

  (* Collect the local ids that occur in an expression [e]. *)
  Fixpoint exp_local_ids_ {T} (e : exp T) (acc : list raw_id) : list raw_id :=
    match e with
    | EXP_Ident (ID_Local i) => i :: acc
    | EXP_Cstring l | EXP_Struct l | EXP_Array l =>
       List.concat (List.map (fun x => exp_local_ids_ x.2 nil) l) ++ acc
    | OP_IBinop _ _ v1 v2 | OP_ICmp _ _ v1 v2 =>
        exp_local_ids_ v1 (exp_local_ids_ v2 acc)
    | OP_Conversion _ _ v _ =>
        exp_local_ids_ v acc
    | OP_GetElementPtr _ (_, e) l =>
        exp_local_ids_ e acc ++
        List.concat (List.map (fun x => exp_local_ids_ x.2 nil) l)
    | _ => acc
    end.

  Definition exp_local_ids {T} (e : exp T) := exp_local_ids_ e nil.

  Definition dummy : raw_id * (local_val * local_val) :=
    (Name "dummy", (UVALUE_None, UVALUE_None)).

  Definition empty_WF :
    gmap (loc * loc) Qp → gmap raw_id uvalue → gmap raw_id uvalue → Prop :=
    fun _ _ _ => True.

  (* Filter keys from local environment *)
  Definition filter_keys m L_t L_s :=
    List.map
      (fun (x : raw_id) =>
          match
            FMapAList.alist_find AstLib.eq_dec_raw_id x L_t,
            FMapAList.alist_find AstLib.eq_dec_raw_id x L_s with
          | Some v_t, Some v_s =>
              ((x, (v_t, v_s)) : raw_id * (local_val * local_val))
          | _, _ => dummy
          end) m.

  (* Given the current local environments, filter out the elements
    that exist in both the source and target local environments. *)
  Definition filter_local_ids {T} (L_t L_s : local_env) (e_t e_s : exp T) :=
    let m := list_intersection (exp_local_ids e_t) (exp_local_ids e_s) in
    filter_keys m L_t L_s.

  (* Helper functions for [mcfg]. *)
  Definition address_one_function (df : definition dtyp (CFG.cfg dtyp)) :
    itree LLVMEvents.L0 (dvalue * definition dtyp (CFG.cfg dtyp)) :=
    let fid := (dc_name (df_prototype df)) in
    fv <- trigger (GlobalRead fid) ;;
    Ret (fv, df).

  Definition mcfg_definitions (mcfg : CFG.mcfg dtyp) :
    itree LLVMEvents.L0 (list (dvalue * _)) :=
     (Util.map_monad address_one_function (CFG.m_definitions mcfg)).

  (* ------------------------------------------------------------------------ *)
  (** *Invariants *)
  (* Invariant for expressions. *)
  Definition expr_frame_inv i_t i_s m : iProp Σ :=
     stack_tgt i_t ∗ stack_src i_s ∗ frame_WF i_t i_s ∗
    (([∗ list] '(l, (v_t, v_s)) ∈ m,
      [ l := v_t ]t i_t ∗ [ l := v_s ]s i_s ∗
      uval_rel v_t v_s)).

  Definition expr_inv {T} i_t i_s L_t L_s (e_t e_s : exp T) : iProp Σ :=
    ldomain_tgt i_t (list_to_set L_t.*1) ∗
    ldomain_src i_s (list_to_set L_s.*1) ∗
    expr_frame_inv i_t i_s (filter_local_ids L_t L_s e_t e_s) ∗
    checkout ∅.

  (* Invariant for codes. *)
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

   (* Postcondition that states monotonically increasing alloca set. *)
   Definition code_inv_post C i_t i_s A_t A_s : iPropI Σ:=
    (∃ nA_t nA_s,
      code_inv C i_t i_s (nA_t ++ A_t) (nA_s ++ A_s))%I.

  (* Invariant for CFG. *)
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

  (* ------------------------------------------------------------------------ *)
   (** *Logical relations *)

   Definition expr_logrel C (e_t e_s : itree exp_E uvalue) A_t A_s : iPropI Σ :=
    (∀ i_t i_s, code_inv C i_t i_s A_t A_s -∗
        exp_conv e_t ⪯ exp_conv e_s
        [{ (v_t, v_s),
            uval_rel v_t v_s ∗ code_inv C i_t i_s A_t A_s }])%I.

  (* Relaxed logical relation for expressions TODO comment *)
  Definition expr_logrel_relaxed e_t e_s : iPropI Σ :=
    (∀ τ (i_t i_s : list frame_names) (L_t L_s : local_env),
      expr_inv i_t i_s L_t L_s e_t e_s -∗
      exp_conv (denote_exp τ e_t) ⪯ exp_conv (denote_exp τ e_s)
      [{ (v_t, v_s),
          uval_rel v_t v_s ∗
          expr_inv i_t i_s L_t L_s e_t e_s }])%I.

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

End logical_relations_def.

Section logical_relations_properties.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

  (* Useful properties for preserving [*_inv] *)
  Lemma local_expr_inv {T} σ_t σ_s i_t i_s L_t L_s (e_t e_s: _ T):
    ⊢ expr_inv i_t i_s L_t L_s e_t e_s -∗
    state_interp σ_t σ_s ==∗
      state_interp σ_t σ_s ∗
      (([∗ list] '(l, (v_t, v_s)) ∈ (filter_local_ids L_t L_s e_t e_s),
      [ l := v_t ]t i_t ∗ [ l := v_s ]s i_s ∗
      uval_rel v_t v_s)) ∗
      ⌜(list_to_set L_t.*1 : gset _) =
        (list_to_set (vlocal σ_t).1.*1 : gset _)⌝ ∗
      ⌜(list_to_set L_s.*1 : gset _) =
        (list_to_set (vlocal σ_s).1.*1 : gset _)⌝ ∗
      ldomain_tgt i_t (list_to_set (vlocal σ_t).1.*1) ∗
      ldomain_src i_s (list_to_set (vlocal σ_s).1.*1) ∗
      checkout ∅ ∗
      stack_tgt i_t ∗ stack_src i_s ∗
      frame_WF i_t i_s.
  Proof.
    iIntros "CI SI".
    iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %Hdom_c & SI)".
    iDestruct "CI" as  "(Hd_t & Hd_s & (Hf_t & Hf_s & WF & Harg) & HC)".

    destruct_HC "Hh_s".

    iDestruct "Hh_t" as (cft hFt)
        "(Hσ_t&HB_t&HCF_t&HA_t&HL_t&HD_t&HSA_t&HG_t&%Hdup_t&%Hbs_t&%Hwf_t)".

    iDestruct (ghost_var_agree with "Hf_s HCF") as %Hf_s.
    iDestruct (ghost_var_agree with "Hf_t HCF_t") as %Hf_t. subst.
    iDestruct (ghost_var_agree with "Hd_s HD") as %Hd_s.
    iDestruct (ghost_var_agree with "Hd_t HD_t") as %Hd_t.
    iDestruct (ghost_var_agree with "HC H_c") as %Hc.
    iFrame.

    subst.
    iSplitL
      "Hd_t Hf_t Hd_s Hf_s HA HL HSA Hb HA_t HL_t HSA_t HG_t HG H_c Hbij HB_t".
    { repeat iExists _; iFrame "Hbij".
      iSplitR "Hd_t Hf_t HA_t HL_t HSA_t H_c HG_t HB_t".
      - iExists cf, _; rewrite Hd_s; iFrame.
        done.
      - iFrame "H_c"; iSplitR ""; last done.
        iExists cft, _; rewrite Hd_t; iFrame.
        done. }

    done.
  Qed.

  Lemma local_code_inv σ_t σ_s C i_t i_s A_t A_s:
    ⊢ code_inv C i_t i_s A_t A_s -∗
    state_interp σ_t σ_s ==∗
    ∃ args_t args_s,
      ⌜args_t.*1 = args_s.*1⌝ ∗
      ⌜(list_to_set args_t.*1 : gset _) = list_to_set (vlocal σ_t).1.*1⌝ ∗
      ⌜(list_to_set args_s.*1 : gset _) = list_to_set (vlocal σ_s).1.*1⌝ ∗
      ⌜NoDup A_t⌝ ∗ ⌜NoDup A_s⌝ ∗
      ([∗ list] '(l_t, v_t) ∈ args_t, [ l_t := v_t ]t i_t) ∗
      ([∗ list] '(l_s, v_s) ∈ args_s, [ l_s := v_s ]s i_s) ∗
      ([∗ list] v_t; v_s ∈ args_t.*2;args_s.*2, uval_rel v_t v_s) ∗
      ([∗ list] v_t;v_s ∈ A_t;A_s, (v_t, 0) ↔h (v_s, 0)
         ∗ ⌜C !! (v_t, v_s) = None⌝) ∗
      state_interp σ_t σ_s ∗
      ldomain_tgt i_t (list_to_set (vlocal σ_t).1.*1) ∗
      ldomain_src i_s (list_to_set (vlocal σ_s).1.*1) ∗
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

  Lemma local_CFG_inv σ_t σ_s C i_t i_s:
    ⊢ CFG_inv C i_t i_s -∗
    state_interp σ_t σ_s ==∗
    ∃ args_t args_s,
      ⌜args_t.*1 = args_s.*1⌝ ∗
      ⌜(list_to_set args_t.*1 : gset _) = list_to_set (vlocal σ_t).1.*1⌝ ∗
      ⌜(list_to_set args_s.*1 : gset _) = list_to_set (vlocal σ_s).1.*1⌝ ∗
      ([∗ list] '(l_t, v_t) ∈ args_t, [ l_t := v_t ]t i_t) ∗
      ([∗ list] '(l_s, v_s) ∈ args_s, [ l_s := v_s ]s i_s) ∗
      ([∗ list] v_t; v_s ∈ args_t.*2;args_s.*2, uval_rel v_t v_s) ∗
      state_interp σ_t σ_s ∗
      ldomain_tgt i_t (list_to_set (vlocal σ_t).1.*1) ∗
      ldomain_src i_s (list_to_set (vlocal σ_s).1.*1) ∗
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
      [{ (v1, v2), code_inv ∅ i_t i_s A_t A_s }].
  Proof.
    iIntros "CI #Hrel".
    iApply sim_update_si.

    iIntros "%σ_t %σ_s SI".
    iDestruct (local_code_inv with "CI SI") as ">H".
    iDestruct "H" as (?????)
        "(%Hnd_t & %Hnd_s & Hlt & Hls & Hv & #Ha_v & SI & Hd_t & Hd_s
          & HC & Hf_t & Hf_s & #WF & Ha_t & Ha_s)".
    iFrame.

    destruct (decide (x ∈ (vlocal σ_t).1.*1)).
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

    { assert (Hn : x ∉ (list_to_set (vlocal σ_t).1.*1 : gset _)) by set_solver.
      assert (Hn1 : x ∉ (list_to_set (vlocal σ_s).1.*1 : gset _)).
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
    iDestruct (local_CFG_inv with "CI SI") as ">H".
    iDestruct "H" as
      (?????)
        "(Hlt & Hls & Hv & SI & Hd_t & Hd_s & HC & Hf_t & Hf_s & Ha_t & Ha_s)".
    iFrame.

    destruct (decide (x ∈ (vlocal σ_t).1.*1)).
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

    { assert (Hn : x ∉ (list_to_set (vlocal σ_t).1.*1 : gset _)) by set_solver.
      assert (Hn1 : x ∉ (list_to_set (vlocal σ_s).1.*1 : gset _)).
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

  (* Utility lemmas TODO Move *)
  Lemma nodup_filter_local_ids {T} L_t L_s (e_t e_s : exp T):
    NoDup ((filter_local_ids L_t L_s e_t e_s).*1).
  Proof. Admitted.

  Lemma lookup_filter_local_ids {T} {L_t L_s n m x v_t v_s} (e_t e_s : exp T):
    L_t !! n = Some (x, v_t) ->
    L_s !! m = Some (x, v_s) ->
    exists i, filter_local_ids L_t L_s e_t e_s !! i = Some (x, (v_t, v_s)).
  Proof. Admitted.

  Lemma expr_local_read_refl {T} x i_t i_s L_t L_s (e_t e_s : exp T):
    x ∈ L_t.*1 ->
    x ∈ L_s.*1 ->
    ⊢ expr_inv i_t i_s L_t L_s e_t e_s -∗
    trigger (LocalRead x) ⪯ trigger (LocalRead x)
      [{ (v1, v2), uval_rel v1 v2 ∗ expr_inv i_t i_s L_t L_s e_t e_s }].
  Proof.
    iIntros (Hx_t Hx_s) "CI".
    iApply sim_update_si.

    iIntros "%σ_t %σ_s SI".
    iDestruct (local_expr_inv with "CI SI") as ">H".
    iDestruct "H" as
        "(SI & Hv & %Ht & %Hs & Hd_t & Hd_s & HC & Hs_t & Hs_s & Hwf)".
    iFrame.

    assert (e: x ∈ (vlocal σ_t).1.*1).
    { set_solver. }

    assert (HL_t: exists n v, L_t !! n = Some (x, v)).
    { eapply (@elem_of_list_to_set raw_id (@gset local_loc _ _)) in e.
      Unshelve. all : try typeclasses eauto.
      setoid_rewrite <-Ht in e. clear -e.
      rewrite elem_of_list_to_set in e.
      by apply elem_of_fst_list_some. }

    assert (es: x ∈ (vlocal σ_s).1.*1) by set_solver.

    assert (HL_s: exists n v, L_s !! n = Some (x, v)).
    { eapply (@elem_of_list_to_set raw_id (@gset local_loc _ _)) in e.
      Unshelve. all : try typeclasses eauto.
      setoid_rewrite <-Ht in e.
      rewrite elem_of_list_to_set in e.
      by apply elem_of_fst_list_some. }

    destruct HL_t as (?&?&HL_t).
    destruct HL_s as (?&?&HL_s).

    destruct (lookup_filter_local_ids e_t e_s HL_t HL_s) as (?&?).

    iDestruct (big_sepL_delete with "Hv") as "(Helemt & Hl_t)"; eauto; cbn.
    iDestruct "Helemt" as "(Helemt & Helems & #Hv)".

    iApply (sim_expr_bupd_mono with "[Hd_t Hd_s HC Hwf Hv Hl_t]");
      [ | iApply (sim_local_read with "Helemt Helems Hs_t Hs_s")].
    iIntros (??) "Hp".
    iDestruct "Hp" as (????) "(%Ht' & %Hs' & Ht' & Hs' & Hf_t' & Hf_s')";
      subst.
    iModIntro. iExists _,_.
    do 2 (iSplitL ""; [ done | ]).
    iFrame.
    rewrite Ht Hs; iFrame.

    setoid_rewrite big_sepL_delete at 2; eauto; iFrame; iFrame "Hv".
  Qed.

  Lemma local_read_refl C x i_t i_s A_t A_s:
    ⊢ code_inv C i_t i_s A_t A_s -∗
    trigger (LocalRead x) ⪯ trigger (LocalRead x)
      [{ (v1, v2), uval_rel v1 v2 ∗ code_inv C i_t i_s A_t A_s }].
  Proof.
    iIntros "CI".
    iApply sim_update_si.

    iIntros "%σ_t %σ_s SI".
    iDestruct (local_code_inv with "CI SI") as ">H".
    iDestruct "H" as
      (args_t args_s Hdom Ht Hs Hnd_t Hnd_s)
        "(Hlt & Hls & Hv & #Hav & SI & Hf_t & Hf_s & HC & Hs_t & Hs_s & #HWF& Ha_t & Ha_s)".
    iFrame.

    (* TODO: Refactor *)
    destruct (decide (x ∈ (vlocal σ_t).1.*1)).
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
    iDestruct (local_CFG_inv with "CI SI") as ">H".
    iDestruct "H" as
      (args_t args_s Hdom Ht Hs)
        "(Hlt & Hls & Hv & SI & Hf_t & Hf_s & HC & Hs_t & Hs_s & Ha_t & Ha_s)".
    iFrame.

    destruct (decide (x ∈ (vlocal σ_t).1.*1)).
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

  Lemma load_must_be_addr_src τ x_t x_s Φ:
    ⊢ (∀ ptr, ⌜x_s = DVALUE_Addr ptr⌝ -∗
      trigger (Load τ x_t) ⪯ trigger (Load τ x_s) [{ Φ}]) -∗
    trigger (Load τ x_t) ⪯ trigger (Load τ x_s) [{ Φ }].
  Proof.
    iIntros "H".

    destruct x_s; [ by iApply "H" | ..].
    all: rewrite sim_expr_eq /sim_expr_;
      iIntros (??) "SI";
      rewrite /interp_L2;
       rewrite (interp_state_vis _ _ _ σ_s) ; cbn; rewrite /add_tau;
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
      rewrite /interp_L2;
      remember
         (State.interp_state
          (handle_L0_L2 vir_handler) (trigger (Store x_t p_t)) σ_t);
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

Section logical_relations_util.

Lemma address_one_function_leaf a x0 x:
  Leaf.Leaf x0 (address_one_function a) ->
  Leaf.Leaf x (address_one_function a) ->
  x0.2 = x.2.
Proof.
  rewrite /address_one_function.
  intros.
  apply Leaf.Leaf_bind_inv in H0.
  destruct H0 as (?&?&?).
  apply Leaf.Leaf_bind_inv in H.
  destruct H as (?&?&?).
  apply Leaf.Leaf_Ret_inv in H2, H1; subst. done.
Qed.

Lemma mcfg_definitions_leaf C g g_t' g_s' r_t r_s:
  Leaf.Leaf (g_t', r_t) (interp_global (mcfg_definitions C) g) ->
  Leaf.Leaf (g_s', r_s) (interp_global (mcfg_definitions C) g) ->
  r_t = r_s.
Proof.
  destruct C; cbn in *.
  revert r_t r_s g g_t' g_s'.
  induction m_definitions.
  { cbn in *.
    intros.
    inversion H; inv H1; eauto.
    inversion H0; inv H1; eauto. }
  { intros * Ht Hs. cbn in *.
    rewrite interp_global_bind in Ht, Hs.
    apply Leaf.Leaf_bind_inv in Ht, Hs.
    destruct Ht as ((g_t&p_t)&bleaf_t&Ht).
    destruct Hs as ((g_s&p_s)&bleaf_s&Hs).
    unfold address_one_function in *.
    rewrite interp_global_bind interp_global_trigger in bleaf_t, bleaf_s.
    cbn in *.
    destruct (g !! dc_name (df_prototype a)) eqn: G_lookup; try rewrite G_lookup in bleaf_t, bleaf_s.
    { rewrite bind_ret_l interp_global_ret in bleaf_t, bleaf_s.
      apply Leaf.Leaf_Ret_inv in bleaf_t, bleaf_s.
      destruct p_t, p_s.
      inv bleaf_t. inv bleaf_s.
      rewrite interp_global_bind in Ht, Hs.
      apply Leaf.Leaf_bind_inv in Ht, Hs.
      destruct Ht as ((g_t&p_t)&bleaf_t&Ht).
      destruct Hs as ((g_s&p_s)&bleaf_s&Hs).
      do 2 rewrite interp_global_ret in Ht, Hs.
      apply Leaf.Leaf_Ret_inv in Ht, Hs; inv Ht; inv Hs.
      f_equiv.

      eapply IHm_definitions; eauto. }

    { rewrite bind_bind bind_vis in bleaf_t, bleaf_s.
      inv bleaf_t; inv H; done. } }
Qed.

End logical_relations_util.
