From iris.prelude Require Import options.

From velliris.vir.lang Require Import lang.
From velliris.vir.rules Require Import rules.
From velliris.vir.logrel Require Import wellformedness.

Set Default Proof Using "Type*".

Import ListNotations.
Import SemNotations.

(* ------------------------------------------------------------------------ *)
(** *Logical relations *)
Section logical_relations_def.

  Context {Σ} `{!vellirisGS Σ}.

  Context (ΠL : local_env_spec) (ΠA : alloca_spec).

  (* Well-formedness for function definitions *)
  Definition fundefs_rel_WF
    (F_t F_s : list (dvalue * _)) (Attr_t Attr_s : list (list fn_attr)) :=
    ((∀ i fn_s v_s,
        ⌜F_s !! i = Some (fn_s, v_s)⌝ -∗
        ∃ fn_t v_t,
          ⌜F_t !! i = Some (fn_t, v_t)⌝ ∗
          dval_rel fn_t fn_s ∗
          ⌜Attr_t !! i = Some nil⌝ ∗
          ⌜Attr_s !! i = Some nil⌝ ∗
          ⌜fun_WF v_t⌝ ∗ ⌜fun_WF v_s⌝) ∗
      (∀ i, ⌜F_s !! i = None -> F_t !! i = None⌝))%I.

  (* ------------------------------------------------------------------------ *)
  (** *Invariants *)
  (* Invariant for expressions. *)
  Definition frame_γ γ i (L : local_env) :=
    (⌜NoDup L.*1⌝ ∗
    (* Current stack frame *)
    vir_state.stack γ i ∗
    (* Domain of local environments on source and target *)
    ldomain γ (current_frame i) (list_to_set L.*1))%I.

  Definition frame_tgt := (frame_γ sheapG_heap_target).
  Definition frame_src := (frame_γ sheapG_heap_source).

  Definition frame_inv i_t i_s (L_t L_s : local_env) C : iProp Σ :=
    (* Current stack frame *)
    frame_WF i_t i_s ∗
    (* Checkout set *)
    checkout C ∗
    (* Source and target resources *)
    frame_tgt i_t L_t ∗ frame_src i_s L_s.

  Definition local_inv i_t i_s L_t L_s C : iProp Σ :=
    frame_inv i_t i_s L_t L_s C ∗ ΠL i_t i_s L_t L_s.

  Definition alloca_inv
    (i_t i_s : list frame_names) (A_t A_s : list Z)
    (C : gmap (loc * loc) Qp) :=
    (alloca_tgt i_t (list_to_set A_t : gset _) ∗
     alloca_src i_s (list_to_set A_s : gset _) ∗
     ⌜NoDup A_t⌝ ∗ ⌜NoDup A_s⌝ ∗
     ΠA C A_t A_s)%I.

  (* Invariant for codes. *)
   Definition code_inv C i_t i_s A_t A_s : iPropI Σ :=
    (∃ (args_t args_s : local_env),
       local_inv i_t i_s args_t args_s C ∗
       alloca_inv i_t i_s A_t A_s C)%I.

   (* Postcondition that states monotonically increasing alloca set. *)
   Definition code_inv_post C i_t i_s A_t A_s: iPropI Σ :=
    (∃ nA_t nA_s, code_inv C i_t i_s (nA_t ++ A_t) (nA_s ++ A_s))%I.

  (* Invariant for CFG. *)
   Definition CFG_inv C i_t i_s : iPropI Σ :=
    (∃ args_t args_s,
       local_inv i_t i_s args_t args_s C ∗
       alloca_tgt i_t ∅ ∗ alloca_src i_s ∅)%I.

  (* ------------------------------------------------------------------------ *)
   (** *Logical relations *)
   Definition expr_logrel C τ_t τ_s e_t e_s A_t A_s : iPropI Σ :=
    (∀ i_t i_s, code_inv C i_t i_s A_t A_s -∗
        exp_conv (denote_exp τ_t e_t) ⪯ exp_conv (denote_exp τ_s e_s)
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

   Definition instr_logrel id_t e_t id_s e_s C A_t A_s : iPropI Σ :=
    (∀ i_t i_s,
        code_inv C i_t i_s A_t A_s -∗
        instr_conv (denote_instr (id_t, e_t)) ⪯
        instr_conv (denote_instr (id_s, e_s))
        [{ (r_t, r_s),
            code_inv_post C i_t i_s A_t A_s }])%I.

   Definition phi_logrel (ϕ_t ϕ_s : itree exp_E (local_id * uvalue)) C A_t A_s : iPropI Σ :=
    (∀ args_t args_s i_t i_s,
        local_inv i_t i_s args_t args_s C ∗
        alloca_inv i_t i_s A_t A_s C -∗
        exp_conv ϕ_t ⪯ exp_conv ϕ_s
        [{ fun e_t e_s => ∃ l v_t v_s,
                ⌜e_t = Ret (l, v_t)⌝ ∗ ⌜e_s = Ret (l, v_s)⌝ ∗
                uval_rel v_t v_s ∗
                code_inv C i_t i_s A_t A_s }])%I.

   Definition phis_logrel (Φ_t Φ_s : itree instr_E ()) C A_t A_s : iPropI Σ :=
    (∀ i_t i_s, code_inv C i_t i_s A_t A_s -∗
       instr_conv Φ_t ⪯ instr_conv Φ_s
       [{ (r_t, r_s), code_inv C i_t i_s A_t A_s }])%I.

   Definition code_logrel c_t c_s C A_t A_s : iPropI Σ :=
    (∀ i_t i_s,
       code_inv C i_t i_s A_t A_s -∗
       instr_conv (denote_code c_t) ⪯ instr_conv (denote_code c_s)
        [{ (r_t, r_s),
            code_inv_post C i_t i_s A_t A_s }])%I.

   Definition block_logrel b_t b_s bid C A_t A_s : iPropI Σ :=
    (∀ i_t i_s,
       code_inv C i_t i_s A_t A_s -∗
       instr_conv ((denote_block b_t) bid) ⪯
       instr_conv ((denote_block b_s) bid)
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
      ⦉ fun e_t e_s =>
           code_inv_post C i_t i_s A_t A_s ∗
            ∃ v_t v_s, ⌜e_t = Ret v_t⌝ ∗ ⌜e_s = Ret v_s⌝ ∗
                        match v_t, v_s with
                          | inl (id_s, id_s'), inl (id_t, id_t') =>
                              ⌜id_s = id_t⌝ ∗ ⌜id_s' = id_t'⌝
                          | inr v_t, inr v_s => uval_rel v_t v_s
                          | _,_ => False
                      end⦊)%I.

   Definition cfg_logrel c_t c_s C A_t A_s: iPropI Σ :=
    (∀ i_t i_s,
      code_inv C i_t i_s A_t A_s -∗
      instr_conv (denote_cfg c_t) ⪯ instr_conv (denote_cfg c_s)
      ⦉ fun v_t v_s =>
          ∃ r_t r_s, ⌜v_t = Ret r_t⌝ ∗ ⌜v_s = Ret r_s⌝ ∗ uval_rel r_t r_s ∗
            code_inv_post C i_t i_s A_t A_s ⦊)%I.

  Definition fun_logrel f_t f_s C: iPropI Σ :=
    ∀ i_t i_s args_t args_s,
     ⌜length i_s > 0 -> length i_t > 0⌝ -∗
     stack_tgt i_t -∗
     stack_src i_s -∗
     val_rel.Forall2 uval_rel args_t args_s -∗
     checkout C -∗
     L0'expr_conv (denote_function f_t args_t) ⪯ L0'expr_conv (denote_function f_s args_s)
     ⦉ fun v_t v_s =>
         ∃ r_t r_s, ⌜v_t = Ret r_t⌝ ∗ ⌜v_s = Ret r_s⌝ ∗
             stack_tgt i_t ∗ stack_src i_s ∗ checkout C ∗ uval_rel r_t r_s ⦊.

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
        ⦉ fun v_t v_s =>
              ∃ r_t r_s, ⌜v_t = Ret r_t⌝ ∗ ⌜v_s = Ret r_s⌝ ∗
                stack_tgt i_t ∗ stack_src i_s ∗ checkout C ∗ uval_rel r_t r_s ⦊)%I.

End logical_relations_def.

Section logical_relations_instance.

  Context {Σ} `{!vellirisGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (* Instances for ΠL ΠA. *)

  (* For the ids [m] that are shared by two local environments [L_t L_s],
    the locations store related locations. *)
  Definition local_bij_at m : local_env_spec :=
    fun i_t i_s L_t L_s =>
    ([∗ list] l ∈ m,
      ∃ v_t v_s, ⌜alist_find l L_t = Some v_t⌝ ∗ ⌜alist_find l L_s = Some v_s⌝ ∗
      [ l := v_t ]t i_t ∗ [ l := v_s ]s i_s ∗ uval_rel v_t v_s)%I.

  Definition local_bij_at_exp {T} (e_t e_s : exp T) : local_env_spec :=
    local_bij_at (intersection_local_ids e_t e_s).

  Definition local_bij : local_env_spec :=
    fun i_t i_s L_t L_s =>
      (⌜L_t.*1 = L_s.*1⌝ ∗
        ([∗ list] '(l_t, v_t) ∈ L_t, [ l_t := v_t ]t i_t) ∗
        ([∗ list] '(l_s, v_s) ∈ L_s, [ l_s := v_s ]s i_s) ∗
        ([∗ list] v_t; v_s ∈ L_t.*2;L_s.*2, uval_rel v_t v_s))%I.

  Definition local_inv_bij {T} e_t e_s :=
    local_inv (local_bij_at_exp (T := T) e_t e_s).

  (* [r_t] and [r_s] indicate the excluded local id's from the current arguments;
    these are the local id's that are "out of sync". *)
       (* The [r_t], [r_s] refer to "reserved" locations that will be
          out of sync. *)
  Definition local_bij_except r_t r_s : local_env_spec :=
    fun i_t i_s L_t L_s => local_bij i_t i_s (remove_ids r_t L_t) (remove_ids r_s L_s).

  Definition alloca_bij : alloca_spec :=
    fun C A_t A_s =>
      ([∗ list] v_t; v_s ∈ A_t;A_s, (v_t, 0%Z) ↔h (v_s, 0%Z) ∗
      ⌜C !! (v_t, v_s) = None⌝)%I.

  (* Relaxed logical relation for expressions TODO comment *)
  Definition expr_logrel_relaxed C τ_t τ_s e_t e_s A_t A_s : iPropI Σ :=
    expr_logrel (local_bij_at_exp e_t e_s) alloca_bij C τ_t τ_s e_t e_s A_t A_s.

  Definition CFG_refl_inv C i_t i_s :=
    CFG_inv local_bij C i_t i_s.

  Definition code_refl_inv C i_t i_s A_t A_s :=
    code_inv local_bij alloca_bij C i_t i_s A_t A_s.

End logical_relations_instance.

Arguments local_bij_at : simpl never.

(* ------------------------------------------------------------------------ *)
(* Some tactics for destructing invariants *)
Local Ltac destruct_code_inv :=
  match goal with
  | |- context [environments.Esnoc _ ?CI (code_inv _ _ _ _ _ _ _)] =>
      iDestruct CI as (args_t args_s) "(LI & AI)"
  | |- context [environments.Esnoc _ ?CI (code_inv_post _ _ _ _ _ _ _)] =>
      iDestruct CI as (nA_t nA_s args_t args_s) "(LI & AI)"
  end.

Local Ltac destruct_CFG_inv :=
  match goal with
  | |- context [environments.Esnoc _ ?CI (CFG_inv _ _ _ _)] =>
      iDestruct CI as (args_t args_s) "(LI & Ha_t & Ha_s)"
  end.

Local Ltac destruct_local_inv :=
  match goal with
  | |- context [environments.Esnoc _ ?RI (local_inv_bij _ _ _ _ _ _ _)]=>
      iDestruct RI as "(Hf & HL)"
  | |- context [environments.Esnoc _ ?RI (local_inv _ _ _ _ _ _)]=>
      iDestruct RI as "(Hf & HL)"
  | |- context [environments.Esnoc _ ?RI (local_bij _ _ _ _)]=>
      iDestruct RI as (?) "(Hl_t & Hl_s & Hl_bij)"
  end.

Local Ltac destruct_alloca_inv :=
  match goal with
  | |- context [environments.Esnoc _ ?RI (alloca_inv _ _ _ _ _ _)]=>
      iDestruct RI as "(Ha_t & Ha_s & %Hd_t & %Hd_s & AI)"
  end.

Local Ltac destruct_SI :=
  match goal with
  | |- context [environments.Esnoc _ ?SI (state_interp _ _)]=>
      iDestruct SI as (???) "(Hh_s & Hh_t & H_c & Hbij & %Hdom_c & SI)"
  end.

Local Ltac destruct_frame :=
  match goal with
  | |- context [environments.Esnoc _ ?SI (frame_tgt _ _)]=>
      iDestruct SI as (Hnd_t) "(Hs_t & Hd_t)"
  | |- context [environments.Esnoc _ ?SI (frame_src _ _)]=>
      iDestruct SI as (Hnd_s) "(Hs_s & Hd_s)"
  | |- context [environments.Esnoc _ ?SI (frame_γ _ _ _)]=>
      iDestruct SI as (?) "(Hs & Hd)"
  | |- context [environments.Esnoc _ ?SI (frame_inv _ _ _ _ _)]=>
      iDestruct SI as "(#WF_frame & CI & Hft & Hfs)"
  end.

(* ------------------------------------------------------------------------ *)

Section logical_invariant_properties.

  Context {Σ} `{!vellirisGS Σ}.

  Lemma local_inv_mono {ΠL ΠL' i_t i_s L_t L_s C}:
    (∀ i_t i_s L_t L_s,
        ΠL i_t i_s L_t L_s -∗
        ΠL' i_t i_s L_t L_s) -∗
    local_inv ΠL i_t i_s L_t L_s C  -∗
    local_inv ΠL' i_t i_s L_t L_s C.
  Proof.
    iIntros "HΠL LI".
    destruct_local_inv.
    iFrame. by iApply "HΠL".
  Qed.

  Lemma alloca_inv_mono {ΠA ΠA' i_t i_s A_t A_s C}:
    (∀ C A_t A_s,
        ΠA C A_t A_s -∗
        ΠA' C A_t A_s) -∗
    alloca_inv ΠA i_t i_s A_t A_s C  -∗
    alloca_inv ΠA' i_t i_s A_t A_s C.
  Proof.
    iIntros "HΠI II".
    destruct_alloca_inv.
    iFrame. do 2 (iSplitL ""; first done).
    by iApply "HΠI".
  Qed.

  Lemma code_inv_strong_mono {ΠL ΠL' ΠA ΠA' C i_t i_s A_t A_s}:
    (∀ i_t i_s L_t L_s,
        ΠL i_t i_s L_t L_s -∗
        ΠL' i_t i_s L_t L_s) -∗
    (∀ C A_t A_s,
        ΠA C A_t A_s -∗
        ΠA' C A_t A_s) -∗
    code_inv ΠL ΠA C i_t i_s A_t A_s -∗
    code_inv ΠL' ΠA' C i_t i_s A_t A_s.
  Proof.
    iIntros "HL HA CI".
    destruct_code_inv.
    iExists args_t, args_s.
    iSplitL "LI HL".
    { iApply (local_inv_mono with "HL LI"). }
    iApply (alloca_inv_mono with "HA AI").
  Qed.

  Lemma code_inv_mono {ΠL ΠL' ΠA C i_t i_s A_t A_s}:
    (∀ i_t i_s L_t L_s,
        ΠL i_t i_s L_t L_s -∗
        ΠL' i_t i_s L_t L_s) -∗
    code_inv ΠL ΠA C i_t i_s A_t A_s -∗
    code_inv ΠL' ΠA C i_t i_s A_t A_s.
  Proof.
    iIntros "HL CI". iApply (code_inv_strong_mono with "HL [] CI").
    iIntros; done.
  Qed.

  Lemma code_inv_post_strong_mono {ΠL ΠL' ΠA ΠA' C i_t i_s A_t A_s}:
    (∀ i_t i_s L_t L_s,
        ΠL i_t i_s L_t L_s -∗
        ΠL' i_t i_s L_t L_s) -∗
    (∀ C A_t A_s,
        ΠA C A_t A_s -∗
        ΠA' C A_t A_s) -∗
    code_inv_post ΠL ΠA C i_t i_s A_t A_s -∗
    code_inv_post ΠL' ΠA' C i_t i_s A_t A_s.
  Proof.
    iIntros "HL HA CI".
    destruct_code_inv.
    iExists nA_t, nA_s, args_t, args_s.
    iSplitL "LI HL".
    { iApply (local_inv_mono with "HL LI"). }
    iApply (alloca_inv_mono with "HA AI").
  Qed.

  Lemma code_inv_post_mono {ΠL ΠL' ΠA C i_t i_s A_t A_s}:
    (∀ i_t i_s L_t L_s,
        ΠL i_t i_s L_t L_s -∗
        ΠL' i_t i_s L_t L_s) -∗
    code_inv_post ΠL ΠA C i_t i_s A_t A_s -∗
    code_inv_post ΠL' ΠA C i_t i_s A_t A_s.
  Proof.
    iIntros "HL CI". iApply (code_inv_post_strong_mono with "HL [] CI").
    iIntros; done.
  Qed.

  Lemma CFG_inv_mono {ΠL ΠL' C i_t i_s}:
    (∀ i_t i_s L_t L_s,
        ΠL i_t i_s L_t L_s -∗
        ΠL' i_t i_s L_t L_s) -∗
    CFG_inv ΠL C i_t i_s -∗
    CFG_inv ΠL' C i_t i_s.
  Proof.
    iIntros "HL CI".
    destruct_CFG_inv.
    iExists args_t, args_s.
    iSplitL "LI HL".
    { iApply (local_inv_mono with "HL LI"). }
    iFrame.
  Qed.

  (* Utility about frame resources *)
  Lemma heap_ctx_frame_γ_agrees γ σ G i L:
    heap_ctx γ
        (⊙ vmem σ, vir_dyn (vmem σ)) (frames (vmem σ)) G (vlocal σ).1 (vlocal σ).2 -∗
    frame_γ γ i L -∗
    ⌜(list_to_set L.*1 : gset _) = (list_to_set (vlocal σ).1.*1 : gset _)⌝.
  Proof.
    iIntros "HC HF".
    destruct_HC "HC". destruct_frame.
    iDestruct (ghost_var_agree with "Hs HCF") as %Hf_s; subst.
    iDestruct (ghost_var_agree with "Hd HD") as %Hd; by subst.
  Qed.

  Lemma local_bij_elem_of {i_t i_s L_t L_s x}:
    local_bij i_t i_s L_t L_s -∗
    ⌜x ∈ L_t.*1 <-> x ∈ L_s.*1⌝.
  Proof.
    iIntros "HB". iDestruct "HB" as (?) "HB";
      iPureIntro; split; intros; subst;
      (rewrite H + rewrite -H); auto.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Remove an id that's in the local bijection. *)
  Lemma local_bij_remove {i_t i_s L_t L_s} x:
    x ∈ L_t.*1 ->
    local_bij i_t i_s L_t L_s -∗
    ∃ v_t v_s,
      [ x := v_t ]t i_t ∗
      [ x := v_s ]s i_s ∗
      uval_rel v_t v_s ∗
      local_bij i_t i_s (alist_remove x L_t) (alist_remove x L_s).
  Proof.
    iIntros (H) "Hbij". destruct_local_inv.

    iDestruct (lmapsto_no_dup with "Hl_t") as "%Hdup_t".
    iDestruct (lmapsto_no_dup with "Hl_s") as "%Hdup_s".

    pose proof (elem_of_fst_list_some _ _ H) as (?&?&?). rewrite H0 in H.
    pose proof (elem_of_fst_list_some _ _ H) as (?&?&?).

    iDestruct (big_sepL_delete with "Hl_t") as "(Helemt & Hl_t)";
      eauto; cbn.
    iDestruct (big_sepL_delete with "Hl_s") as "(Helems & Hl_s)";
      eauto; cbn.
    pose proof (no_dup_fst_list_some _ _ _ _ _ _ _ Hdup_t Hdup_s H0 H1 H2);
      subst.
    iExists x1, x3; iFrame.

    iAssert (uval_rel x1 x3) as "#Hv'".
    { iDestruct (big_sepL2_lookup _ _ _ x2 with "Hl_bij") as "H"; eauto.
      { by eapply list_lookup_snd. }
      { by eapply list_lookup_snd. } }

    iFrame "Hv'".
    rewrite /local_bij; iFrame.
    iPoseProof (big_sepL_alist_remove _ _ _ _ _ H1 Hdup_t with "Hl_t")
      as "Hl_t"; iFrame.
    iPoseProof (big_sepL_alist_remove _ _ _ _ _ H2 Hdup_s with "Hl_s")
      as "Hl_s"; iFrame.
    iSplitL "".
    { iPureIntro. by apply alist_remove_fst_eq. }

    iPoseProof (big_sepL2_alist_remove _ _ _ _ _ _ uval_rel with "Hl_bij")
      as "HR"; eauto.
  Qed.

  (* Remove an id that's in the local bijection. *)
  Lemma local_bij_add {i_t i_s L_t L_s} x v_t v_s:
    [ x := v_t ]t i_t -∗
    [ x := v_s ]s i_s -∗
    uval_rel v_t v_s -∗
    local_bij i_t i_s L_t L_s -∗
    local_bij i_t i_s (alist_add x v_t L_t) (alist_add x v_s L_s).
  Proof.
    iIntros "Hvt Hvs Hv Hbij". destruct_local_inv; iFrame.
    iSplitL "".
    { iPureIntro; by eapply alist_add_fst_eq. }

    iDestruct (lmapsto_no_dup with "Hl_t") as "%Hdup_t".
    iDestruct (lmapsto_no_dup with "Hl_s") as "%Hdup_s".
    destruct (decide (x ∈ L_t)).

    (* iDestruct (big_sepL_delete with "Hl_t") as "(Helemt & Hl_t)"; *)
    (*   eauto; cbn. *)
    (* iDestruct (big_sepL_delete with "Hl_s") as "(Helems & Hl_s)"; *)
    (*   eauto; cbn. *)
    (* pose proof (no_dup_fst_list_some _ _ _ _ _ _ _ Hdup_t Hdup_s H0 H1 H2); *)
    (*   subst. *)
    (* iExists x1, x3; iFrame. *)

    (* iAssert (uval_rel x1 x3) as "#Hv'". *)
    (* { iDestruct (big_sepL2_lookup _ _ _ x2 with "Hl_bij") as "H"; eauto. *)
    (*   { by eapply list_lookup_snd. } *)
    (*   { by eapply list_lookup_snd. } } *)
  Admitted.

  Lemma local_bij_add_remove {i_t i_s x v_t v_s L_t L_s}:
    x ∈ L_t.*1 ->
    uval_rel v_t v_s -∗
    local_bij i_t i_s
      (alist_add x v_t (alist_remove x L_t))
      (alist_add x v_s (alist_remove x L_s)) -∗
    local_bij i_t i_s L_t L_s.
  Proof. Admitted.

End logical_invariant_properties.

From ITree Require Import Events.StateFacts.

Section logical_relations_properties.

  Context {Σ : gFunctors} `{!vellirisGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (* Local bij properties *)

  Lemma local_bij_at_nil i_t i_s L_t L_s:
    (local_bij_at nil i_t i_s L_t L_s ⊣⊢ emp)%I.
  Proof.
    rewrite /local_bij_at; by cbn.
  Qed.

  Lemma local_bij_at_cons_invert i_t i_s L_t L_s x l:
    local_bij_at (x :: l) i_t i_s L_t L_s -∗
    local_bij_at [x] i_t i_s L_t L_s ∗
    local_bij_at l i_t i_s L_t L_s.
  Proof.
    iInduction l as [ | ] "IH" forall (x).
    { (* nil case *)
      cbn; iIntros "$".
      by rewrite local_bij_at_nil. }

    (* cons case *)
    iIntros "(Hx & Ha)".
    iSpecialize ("IH" with "Ha"); iDestruct "IH" as "((Ha & H) & IH)";
      cbn; iFrame. by iFrame.
  Qed.

  Lemma local_bij_at_app_invert i_t i_s L_t L_s l1 l2:
    local_bij_at (l1 ++ l2) i_t i_s L_t L_s -∗
    local_bij_at l1 i_t i_s L_t L_s ∗
    local_bij_at l2 i_t i_s L_t L_s.
  Proof.
    iInduction l1 as [ | ] "IH" forall (l2).
    { (* nil case *)
      cbn; iIntros "$".
      by iApply local_bij_at_nil. }

    (* cons case *)
    iIntros "H". cbn -[local_bij_at].
    iDestruct (local_bij_at_cons_invert with "H") as "((Ha & _) & Hl)".
    iSpecialize ("IH" with "Hl"); iDestruct "IH" as "(Hl & IH)".
    iFrame.
  Qed.

  Lemma local_bij_at_cons i_t i_s L_t L_s x l:
    local_bij_at [x] i_t i_s L_t L_s -∗
    local_bij_at l i_t i_s L_t L_s -∗
    local_bij_at (x :: l) i_t i_s L_t L_s.
  Proof.
    iInduction l as [ | ] "IH" forall (x).
    { (* nil case *)
      cbn; by iIntros "$ _". }

    (* cons case *)
    iIntros "Hx (Hl & Ha)".
    iSpecialize ("IH" with "Hx Ha"); iDestruct "IH" as "(H1 & H2)".
    cbn; iFrame.
  Qed.

  Lemma local_bij_at_app i_t i_s L_t L_s l1 l2:
    local_bij_at l1 i_t i_s L_t L_s -∗
    local_bij_at l2 i_t i_s L_t L_s -∗
    local_bij_at (l1 ++ l2) i_t i_s L_t L_s.
  Proof.
    iInduction l1 as [ | ] "IH" forall (l2).
    { (* nil case *)
      cbn; iIntros "_ $". }

    (* cons case *)
    iIntros "H1 H2". cbn -[local_bij_at].
    iDestruct (local_bij_at_cons_invert with "H1") as "((Ha & _) & H1)".
    iSpecialize ("IH" with "H1 H2"); iDestruct "IH" as "(Hl & IH)"; iFrame.
  Qed.

  Lemma local_bij_at_commute
    {T} i_t i_s L_t L_s (e1 e2 : exp T):
    local_bij_at_exp e1 e1 i_t i_s L_t L_s -∗
    local_bij_at (exp_local_ids e2) i_t i_s L_t L_s -∗
    local_bij_at_exp e2 e2 i_t i_s L_t L_s ∗
    local_bij_at (exp_local_ids e1) i_t i_s L_t L_s.
  Proof.
    iIntros "H1 H2"; iFrame. rewrite /local_bij_at_exp.
    rewrite !intersection_local_ids_eq; iFrame.
  Qed.

  Lemma local_bij_at_big_opL {T : Set}
    i_t i_s L_t L_s (l : list (T * exp T)):
    ([∗ list] x ∈ l, local_bij_at (exp_local_ids x.2) i_t i_s L_t L_s) ⊣⊢
    local_bij_at
      (concat (map (λ x, exp_local_ids_ x.2 []) l))
      i_t i_s
      L_t L_s.
  Proof.
    iInduction l as [ | ] "IH"; cbn; try done.
    { by rewrite local_bij_at_nil. }
    iSplit.
    { iIntros "(H1&H2)".
      iApply (local_bij_at_app with "H1").
      iApply ("IH" with "H2"). }
    { iIntros "H".
      iDestruct (local_bij_at_app_invert with "H") as "(H1 & H2)".
      iFrame.
      iApply ("IH" with "H2"). }
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Expression-specific [expr-inv] properties *)
  Lemma local_inv_bij_op_conversion:
    ∀ (conv : conversion_type)
      (t_from t_to : dtyp)
      (e : exp dtyp)
      (i_t i_s : list frame_names)
      (L_t L_s : local_env) C,
      local_inv_bij
        (OP_Conversion conv t_from e t_to)
        (OP_Conversion conv t_from e t_to)
        i_t i_s
        L_t L_s C -∗
      local_inv_bij e e i_t i_s L_t L_s C.
  Proof.
    iIntros (?????????) "H"; done.
  Qed.

  Lemma local_inv_bij_op_gep_invert:
    ∀ {T} i_t i_s L_t L_s t ptr_t (e : exp T) dt C,
      local_inv_bij
        (OP_GetElementPtr t (ptr_t, e) dt)
        (OP_GetElementPtr t (ptr_t, e) dt)
        i_t i_s L_t L_s C -∗
      local_inv_bij e e i_t i_s L_t L_s C ∗
    ([∗ list] x ∈ dt,
      local_bij_at (exp_local_ids x.2) i_t i_s L_t L_s).
  Proof.
    iIntros (??????????) "(Hf & Helts)".
    rewrite /local_bij_at_exp !intersection_local_ids_eq; iFrame.

    cbn -[local_bij_at].
    iDestruct (local_bij_at_app_invert with "Helts") as "(He & Helts)".
    rewrite /local_bij_at_exp !intersection_local_ids_eq; iFrame.
    iApply local_bij_at_big_opL.
    by rewrite app_nil_r.
  Qed.

  (* [expr inv] inversion and cons rule for [struct]-y expressions *)

  (* EXP_Cstring *)
  Lemma local_inv_bij_cstring_invert
    {T : Set} i_t i_s L_t L_s (elts: list (T * exp T)) C:
    local_inv_bij (EXP_Cstring elts) (EXP_Cstring elts)
      i_t i_s L_t L_s C -∗
    frame_inv i_t i_s L_t L_s C ∗
    (∀ x,
        ⌜In x elts⌝ -∗
        local_bij_at_exp x.2 x.2 i_t i_s L_t L_s).
  Proof.
    iIntros "(Hf & Helts)"; iFrame; rewrite /local_inv_bij /local_bij_at_exp.
    rewrite !intersection_local_ids_eq; cbn -[local_bij_at].
    rewrite app_nil_r; iFrame.
    iInduction elts as [ | ] "IH"; iIntros (??); first inv H.
    apply in_inv in H ; first destruct H; subst.
    { cbn -[local_bij_at].
      iDestruct (local_bij_at_app_invert with "Helts") as "(Hx & elts)".
      iSpecialize ("IH" with "elts"); iFrame.
      by rewrite !intersection_local_ids_eq; cbn -[local_bij_at]. }
    { cbn -[local_bij_at].
      iDestruct (local_bij_at_app_invert with "Helts") as "(Hx & elts)".
      iSpecialize ("IH" with "elts"); iFrame.
      by iApply "IH". }
  Qed.

  Lemma local_inv_bij_cstring_cons:
    ∀ (i_t i_s : list frame_names)
      (L_t L_s : local_env)
      (d : dtyp) (e : exp dtyp) (elts : list (dtyp * exp dtyp)) C,
      local_inv_bij e e i_t i_s L_t L_s C ∗
      local_bij_at_exp (EXP_Cstring elts) (EXP_Cstring elts) i_t i_s L_t L_s
      ⊣⊢
      local_inv_bij
        (EXP_Cstring ((d, e) :: elts)) (EXP_Cstring ((d, e) :: elts))
        i_t i_s L_t L_s C.
  Proof.
    iIntros (????????).
    iSplit.
    { iIntros "((Hf & He) & Helts)"; cbn; iFrame.
      rewrite /local_bij_at_exp.
      rewrite !intersection_local_ids_eq;
        cbn -[local_bij_at].
      rewrite !app_nil_r. rewrite /local_inv_bij /local_inv.
      iApply (local_bij_at_app with "He Helts"). }
    { rewrite /local_inv_bij /local_bij_at_exp !intersection_local_ids_eq.
      iIntros "(Hf & He)"; iFrame.
      cbn -[local_inv_bij].
      rewrite !app_nil_r.
      iApply (local_bij_at_app_invert with "He"). }
  Qed.

  (* EXP_Struct *)
  Lemma expr_local_bij_struct_invert
    {T : Set} i_t i_s L_t L_s (elts: list (T * exp T)) C:
    local_inv_bij (EXP_Struct elts) (EXP_Struct elts) i_t i_s L_t L_s C -∗
    frame_inv i_t i_s L_t L_s C ∗
    (∀ x,
        ⌜In x elts⌝ -∗
      local_bij_at_exp x.2 x.2 i_t i_s L_t L_s).
  Proof.
    iIntros "(Hf & Helts)"; iFrame.
    rewrite /local_bij_at_exp.
    rewrite intersection_local_ids_eq; cbn -[local_bij].
    rewrite app_nil_r.
    iInduction elts as [ | ] "IH"; iIntros (??); first inv H.
    apply in_inv in H; first destruct H; subst.
    { cbn -[local_bij].
      iDestruct (local_bij_at_app_invert with "Helts") as "(Hx & elts)".
      iSpecialize ("IH" with "elts"); iFrame.
      by rewrite intersection_local_ids_eq; cbn -[local_bij]. }
    { cbn -[local_bij].
      iDestruct (local_bij_at_app_invert with "Helts") as "(Hx & elts)".
      iSpecialize ("IH" with "elts"); iFrame.
      by iApply "IH". }
  Qed.

  Local Ltac local_bij_cbn :=
    rewrite /local_bij_at_exp !intersection_local_ids_eq; cbn.

  Lemma expr_local_bij_struct_cons:
    ∀ (i_t i_s : list frame_names)
      (L_t L_s : local_env)
      (d : dtyp) (e : exp dtyp) (elts : list (dtyp * exp dtyp)) C,
      local_inv_bij e e i_t i_s L_t L_s C ∗
      local_bij_at_exp (EXP_Struct elts) (EXP_Struct elts)i_t i_s L_t L_s
      ⊣⊢
      local_inv_bij
        (EXP_Struct ((d, e) :: elts))
        (EXP_Struct ((d, e) :: elts))
        i_t i_s L_t L_s C.
  Proof.
    iIntros (????????).
    iSplit.
    { iIntros "((Hf & He) & Helts)"; iFrame.
      local_bij_cbn. rewrite !app_nil_r.
      iApply (local_bij_at_app with "He Helts"). }
    { iIntros "(Hf & He)"; iFrame.
      local_bij_cbn. rewrite !app_nil_r.
      iApply (local_bij_at_app_invert with "He"). }
  Qed.

  (* EXP_Array *)
  Lemma expr_local_bij_array_invert
    {T : Set} i_t i_s L_t L_s (elts: list (T * exp T)) C:
    local_inv_bij (EXP_Array elts) (EXP_Array elts) i_t i_s L_t L_s C -∗
    frame_inv i_t i_s L_t L_s C ∗
    (∀ x,
        ⌜In x elts⌝ -∗
        local_bij_at_exp x.2 x.2 i_t i_s L_t L_s).
  Proof.
    iIntros "(Hf & Helts)"; iFrame.
    local_bij_cbn.
    rewrite app_nil_r.
    iInduction elts as [ | ] "IH"; iIntros (??); first inv H.
    apply in_inv in H; first destruct H; subst.
    { local_bij_cbn.
      iDestruct (local_bij_at_app_invert with "Helts") as "(Hx & elts)".
      iSpecialize ("IH" with "elts"); iFrame. }
    { iDestruct (local_bij_at_app_invert with "Helts") as "(Hx & elts)".
      iSpecialize ("IH" with "elts"); iFrame.
      by iApply "IH". }
  Qed.

  Lemma expr_local_bij_array_cons:
    ∀ (i_t i_s : list frame_names)
      (L_t L_s : local_env)
      (d : dtyp) (e : exp dtyp) (elts : list (dtyp * exp dtyp)) C,
      local_inv_bij e e i_t i_s L_t L_s C ∗
      local_bij_at_exp (EXP_Array elts) (EXP_Array elts)
        i_t i_s L_t L_s
      ⊣⊢
      local_inv_bij
        (EXP_Array ((d, e) :: elts))
        (EXP_Array ((d, e) :: elts))
      i_t i_s L_t L_s
        C.
  Proof.
    iIntros (????????).
    iSplit.
    { iIntros "((Hf & He) & Helts)"; iFrame.
      local_bij_cbn.
      rewrite !app_nil_r.
      iApply (local_bij_at_app with "He Helts"). }
    { iIntros "(Hf & He)"; iFrame.
      local_bij_cbn. iFrame.
      rewrite !app_nil_r.
      iApply (local_bij_at_app_invert with "He"). }
  Qed.

  (* Inversion rule for [expr_local_bij] for [binop]-ey expressions. *)

  (* (* OP_IBinop *) *)
  (* Lemma local_bij_binop_invert *)
  (*   {T} i_t i_s L_t L_s τ iop (e1 e2: exp T): *)
  (*   local_bij i_t i_s *)
  (*     (intersection_local_ids *)
  (*       (OP_IBinop iop τ e1 e2) (OP_IBinop iop τ e1 e2)) L_t L_s -∗ *)
  (*   local_bij i_t i_s *)
  (*     (exp_local_ids e1 ++ exp_local_ids e2) L_t L_s. *)
  (* Proof. *)
  (*   rewrite /local_bij; cbn. *)
  (*   repeat rewrite exp_local_ids_acc_commute; rewrite app_nil_r. *)
  (*   rewrite list_intersection_eq. *)
  (*   by iIntros "H". *)
  (* Qed. *)

  (* Lemma expr_local_bij_binop_invert *)
  (*   {T} i_t i_s L_t L_s τ iop (e1 e2 : exp T): *)
  (*   expr_local_bij *)
  (*     i_t i_s L_t L_s *)
  (*     (OP_IBinop iop τ e1 e2) *)
  (*     (OP_IBinop iop τ e1 e2) -∗ *)
  (*   expr_local_bij i_t i_s L_t L_s e1 e1 ∗ *)
  (*   local_bij i_t i_s (exp_local_ids e2) L_t L_s. *)
  (* Proof. *)
  (*   iIntros "Hb"; iDestruct "Hb" as "(Hf_inv & Hl)"; iFrame. *)
  (*   iPoseProof (local_bij_binop_invert with "Hl") as "Hl". *)
  (*   iDestruct (local_bij_app_invert with "Hl") as "(H1 & H2)". *)
  (*   iFrame; by rewrite intersection_local_ids_eq. *)
  (* Qed. *)

  (* Lemma expr_local_bij_binop *)
  (*   {T} i_t i_s L_t L_s τ iop (e1 e2 : exp T): *)
  (*   expr_local_bij *)
  (*     i_t i_s L_t L_s *)
  (*     (OP_IBinop iop τ e1 e2) *)
  (*     (OP_IBinop iop τ e1 e2) ⊣⊢ *)
  (*   expr_local_bij i_t i_s L_t L_s e1 e1 ∗ *)
  (*   local_bij i_t i_s (exp_local_ids e2) L_t L_s. *)
  (* Proof. *)
  (*   iSplit; first iApply expr_local_bij_binop_invert. *)
  (*   iIntros "((Hf & H1)& H2)"; iFrame. *)
  (*   rewrite !intersection_local_ids_eq; cbn -[local_bij]. *)
  (*   rewrite exp_local_ids_acc_commute. *)
  (*   iApply (local_bij_app with "H1 H2"). *)
  (* Qed. *)

  (* (* OP_ICmp *) *)
  (* Lemma local_bij_icmp_invert *)
  (*   {T} i_t i_s L_t L_s τ iop (e1 e2: exp T): *)
  (*   local_bij i_t i_s *)
  (*     (intersection_local_ids *)
  (*       (OP_ICmp iop τ e1 e2) (OP_ICmp iop τ e1 e2)) L_t L_s -∗ *)
  (*   local_bij i_t i_s *)
  (*     (exp_local_ids e1 ++ exp_local_ids e2) L_t L_s. *)
  (* Proof. *)
  (*   rewrite /local_bij; cbn. *)
  (*   repeat rewrite exp_local_ids_acc_commute; rewrite app_nil_r. *)
  (*   rewrite list_intersection_eq. *)
  (*   by iIntros "H". *)
  (* Qed. *)

  (* Lemma expr_local_bij_icmp_invert *)
  (*   {T} i_t i_s L_t L_s τ iop (e1 e2 : exp T): *)
  (*   expr_local_bij *)
  (*     i_t i_s L_t L_s *)
  (*     (OP_ICmp iop τ e1 e2) *)
  (*     (OP_ICmp iop τ e1 e2) -∗ *)
  (*   expr_local_bij i_t i_s L_t L_s e1 e1 ∗ *)
  (*   local_bij i_t i_s (exp_local_ids e2) L_t L_s. *)
  (* Proof. *)
  (*   iIntros "Hb"; iDestruct "Hb" as "(Hf_inv & Hl)"; iFrame. *)
  (*   iPoseProof (local_bij_icmp_invert with "Hl") as "Hl". *)
  (*   iDestruct (local_bij_app_invert with "Hl") as "(H1 & H2)". *)
  (*   iFrame; by rewrite intersection_local_ids_eq. *)
  (* Qed. *)

  (* Lemma expr_local_bij_icmp *)
  (*   {T} i_t i_s L_t L_s τ iop (e1 e2 : exp T): *)
  (*   expr_local_bij *)
  (*     i_t i_s L_t L_s *)
  (*     (OP_ICmp iop τ e1 e2) *)
  (*     (OP_ICmp iop τ e1 e2) ⊣⊢ *)
  (*   expr_local_bij i_t i_s L_t L_s e1 e1 ∗ *)
  (*   local_bij i_t i_s (exp_local_ids e2) L_t L_s. *)
  (* Proof. *)
  (*   iSplit; first iApply expr_local_bij_icmp_invert. *)
  (*   iIntros "((Hf & H1)& H2)"; iFrame. *)
  (*   rewrite !intersection_local_ids_eq; cbn -[local_bij]. *)
  (*   rewrite exp_local_ids_acc_commute. *)
  (*   iApply (local_bij_app with "H1 H2"). *)
  (* Qed. *)

  (* (* Utility lemma about [expr_local_bij]. *) *)
  (* (* If [x] is included in the local ids of both [e_t] and [e_s] *)
  (*    and we have the [expr_local_bij] on those expressions, the local *)
  (*    environments must contain the local id. *) *)
  (* Lemma expr_local_bij_local_env_includes {T} x {i_t i_s L_t L_s} (e_t e_s : exp T): *)
  (*   x ∈ (exp_local_ids e_t) -> *)
  (*   x ∈ (exp_local_ids e_s) -> *)
  (*   expr_local_bij i_t i_s L_t L_s e_t e_s -∗ *)
  (*   ⌜x ∈ L_t.*1 /\ x ∈ L_s.*1⌝. *)
  (* Proof. *)
  (*   iIntros (Ht Hs) "(Hf & Hl)". *)
  (*   assert (Hint: *)
  (*     x ∈ list_intersection (exp_local_ids e_t) (exp_local_ids e_s)). *)
  (*   { by rewrite elem_of_list_intersection. } *)

  (*   rewrite /local_bij. *)
  (*   apply elem_of_list_lookup_1 in Hint; destruct Hint. *)

  (*   iDestruct (big_sepL_delete with "Hl") as "(Helem & Hl)"; eauto; cbn. *)

  (*   iDestruct "Helem" as (????) "(Hlt & Hls & #Hv)". *)
  (*   iPureIntro. *)
  (*   split; by eapply alist_find_elem_of. *)
  (* Qed. *)

  (* Useful properties for preserving [*_inv] *)
  Lemma local_inv_SI {ΠL σ_t σ_s i_t i_s L_t L_s C}:
    local_inv ΠL i_t i_s L_t L_s C -∗
    state_interp σ_t σ_s -∗
    ⌜(list_to_set L_t.*1 : gset _) = (list_to_set (vlocal σ_t).1.*1 : gset _) /\
    (list_to_set L_s.*1 : gset _) = (list_to_set (vlocal σ_s).1.*1 : gset _)⌝.
  Proof.
    iIntros "CI SI".
    destruct_SI. destruct_local_inv. destruct_frame.
    iDestruct (heap_ctx_frame_γ_agrees with "Hh_t Hft") as %Ht.
    iDestruct (heap_ctx_frame_γ_agrees with "Hh_s Hfs") as %Hs.
    done.
  Qed.

  Lemma code_inv_SI {ΠL ΠA σ_t σ_s C i_t i_s A_t A_s}:
    code_inv ΠL ΠA C i_t i_s A_t A_s -∗
    state_interp σ_t σ_s -∗
    ∃ args_t args_s,
      ⌜(list_to_set args_t.*1 : gset _) = list_to_set (vlocal σ_t).1.*1⌝ ∗
      ⌜(list_to_set args_s.*1 : gset _) = list_to_set (vlocal σ_s).1.*1⌝ ∗
       local_inv ΠL i_t i_s args_t args_s C ∗
       alloca_inv ΠA i_t i_s A_t A_s C ∗
       state_interp σ_t σ_s.
  Proof.
    iIntros "CI SI".
    destruct_code_inv.
    iDestruct (local_inv_SI with "LI SI") as %Heq.
    destruct Heq; iExists _, _; by iFrame.
  Qed.

  Lemma local_CFG_inv {ΠL σ_t σ_s C i_t i_s}:
    ⊢ CFG_inv ΠL C i_t i_s -∗
    state_interp σ_t σ_s -∗
    ∃ args_t args_s,
      ⌜(list_to_set args_t.*1 : gset _) = list_to_set (vlocal σ_t).1.*1⌝ ∗
      ⌜(list_to_set args_s.*1 : gset _) = list_to_set (vlocal σ_s).1.*1⌝ ∗
      local_inv ΠL i_t i_s args_t args_s C ∗
      alloca_tgt i_t ∅ ∗ alloca_src i_s ∅.
  Proof.
    iIntros "CI SI".
    destruct_CFG_inv.
    iDestruct (local_inv_SI with "LI SI") as %Heq.
    destruct Heq; iExists _, _; by iFrame.
  Qed.

  Lemma sim_local_write_frame
    (x_t x_s : LLVMAst.raw_id) (v_t v_s : uvalue) v_t' v_s' i_t i_s L_t L_s C:
    ⊢ frame_inv i_t i_s L_t L_s C -∗
      [ x_t := v_t ]t i_t -∗ [ x_s := v_s ]s i_s -∗
    trigger (LocalWrite x_t v_t') ⪯ trigger (LocalWrite x_s v_s')
      [{ (v_t, v_s),
          [ x_t := v_t' ]t i_t ∗ [ x_s := v_s' ]s i_s ∗ frame_inv i_t i_s L_t L_s C }].
  Proof.
    iIntros "Hf Hxt Hxs".
    destruct_frame.
    iDestruct "Hft" as (?) "(Hs_t & Hd_t)".
    iDestruct "Hfs" as (?) "(Hs_s & Hd_s)".
    mono: iApply (sim_local_write with "Hs_t Hs_s Hxt Hxs") with "[CI Hd_t Hd_s]".
    iIntros (??) "H"; iDestruct "H" as (????) "(Ht & Hs & Hs_t & Hs_s)".
    iExists _, _; iFrame; by iFrame "WF_frame".
  Qed.

  (* Local write reflexivity *)
  Lemma local_write_refl C x v_t v_s i_t i_s A_t A_s:
    ⊢ code_refl_inv C i_t i_s A_t A_s -∗
       uval_rel v_t v_s -∗
      trigger (LocalWrite x v_t) ⪯ trigger (LocalWrite x v_s)
        [{ (v1, v2), code_refl_inv C i_t i_s A_t A_s }].
  Proof.
    iIntros "CI #Hrel"; rewrite /code_refl_inv.
    destruct_code_inv.

    destruct (decide (x ∈ args_t.*1)).
    { destruct_local_inv.
      iDestruct (local_bij_remove x with "HL") as (??) "(Hxt & Hxs & #Hv & HL)";
        auto.

      mono: iApply (sim_local_write_frame with "Hf Hxt Hxs") with "[AI HL]".
      (iIntros (??) "HΦ"; iDestruct "HΦ" as (????) "(Ht & Hs & Hf & H)"); iFrame.
      do 2 sfinal.
      iPoseProof (local_bij_add with "Ht Hs Hrel HL") as "HL".
      iApply (local_bij_add_remove e with "Hrel HL").  }

    { destruct_local_inv.
  Admitted.

  Lemma local_write_refl_cfg C x v_t v_s i_t i_s :
    ⊢ CFG_refl_inv C i_t i_s -∗ uval_rel v_t v_s -∗
    trigger (LocalWrite x v_t) ⪯ trigger (LocalWrite x v_s)
      [{ (v1, v2), CFG_refl_inv C i_t i_s }].
  Proof.
    iIntros "CI #Hrel".
  Admitted.

  Lemma expr_local_read_refl {T} x i_t i_s L_t L_s (e_t e_s : exp T) C :
    x ∈ intersection_local_ids e_t e_s ->
    ⊢ local_inv_bij e_t e_s i_t i_s L_t L_s C -∗
    trigger (LocalRead x) ⪯ trigger (LocalRead x)
      [{ (v1, v2), uval_rel v1 v2 ∗ local_inv_bij e_t e_s i_t i_s L_t L_s C }].
  Proof. Admitted.

  Lemma local_read_refl C x i_t i_s A_t A_s:
    ⊢ code_refl_inv C i_t i_s A_t A_s -∗
    trigger (LocalRead x) ⪯ trigger (LocalRead x)
      [{ (v1, v2), uval_rel v1 v2 ∗ code_refl_inv C i_t i_s A_t A_s }].
  Proof. Admitted.

  Lemma local_read_refl_cfg C x i_t i_s :
    ⊢ CFG_refl_inv C i_t i_s -∗
    trigger (LocalRead x) ⪯ trigger (LocalRead x)
      [{ (v1, v2), uval_rel v1 v2 ∗ CFG_refl_inv C i_t i_s }].
  Proof. Admitted.

  Lemma call_refl v_t v_s e_t e_s d i_t i_s l A_t A_s C:
    code_refl_inv C i_t i_s A_t A_s -∗
    dval_rel v_t v_s -∗
    ([∗ list] x_t; x_s ∈ e_t;e_s, uval_rel x_t x_s) -∗
    (trigger (ExternalCall d v_t e_t l))
    ⪯
    (trigger (ExternalCall d v_s e_s l))
    [{ (v_t, v_s), uval_rel v_t v_s ∗
        code_refl_inv C i_t i_s A_t A_s }].
  Proof. Admitted.

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
    ⊢ code_refl_inv ∅ i_t i_s A_t A_s -∗
      dval_rel x_t x_s -∗
      trigger (Load τ x_t) ⪯ trigger (Load τ x_s)
      [{ (v1, v2), uval_rel v1 v2 ∗ code_refl_inv ∅ i_t i_s A_t A_s }].
  Proof.
    (* If they are related dvalues, they must be values in the public bijection. *)
    iIntros (Hwf) "CI #Hr".
    iApply load_must_be_addr; [ done | ].
    iIntros (????); subst.
    rewrite /CFG_inv /code_refl_inv.

    destruct_code_inv.
    rewrite unfold_dval_rel; cbn.
    destruct_local_inv.
    destruct_frame.
    iApply (sim_expr_bupd_mono with "[Hft Hfs HL AI]"); [
        | iApply (sim_bij_load_None1 with "Hr") ]; eauto.
    2 : set_solver.
    iIntros (??) "H".

    iDestruct "H" as (????) "(H1 & H2)"; iFrame.
    iModIntro; repeat sfinal.
  Qed.

  Ltac destruct_CFG_inv_all :=
    rewrite ?/CFG_refl_inv;
    destruct_CFG_inv; destruct_local_inv; destruct_frame.

  Ltac destruct_code_inv_all :=
    rewrite ?/code_refl_inv;
    destruct_code_inv; destruct_local_inv; destruct_frame.

  Lemma load_refl_cfg x_t x_s τ C i_t i_s:
    dtyp_WF τ ->
    (forall a_t, x_t = DVALUE_Addr a_t ->
     forall a_s, x_s = DVALUE_Addr a_s ->
            C !! (a_t.1, a_s.1) = None \/
            (∃ q, C !! (a_t.1, a_s.1) = Some q /\ (q < 1)%Qp)) ->
    ⊢ CFG_refl_inv C i_t i_s -∗
      dval_rel x_t x_s -∗
      trigger (Load τ x_t) ⪯ trigger (Load τ x_s)
      [{ (v1, v2), uval_rel v1 v2 ∗ CFG_refl_inv C i_t i_s }].
  Proof.
    (* If they are related dvalues, they must be values in the public bijection. *)
    iIntros (Hwf Hlu) "CI #Hr".
    iApply load_must_be_addr; [ done | ].
    iIntros (????); subst.
    destruct_CFG_inv_all.

    rewrite unfold_dval_rel; cbn.
    specialize (Hlu _ eq_refl _ eq_refl).
    destruct Hlu.
    { iApply (sim_expr_bupd_mono with
              "[Hft Hfs HL Ha_t Ha_s]"); [
        | iApply (sim_bij_load_None1 with "Hr") ]; eauto.
      iIntros (??) "H".

      iDestruct "H" as (????) "(H1 & H2)"; iFrame.
      repeat sfinal. }
    { destruct H as (?&HC&Hq).
      iApply (sim_expr_bupd_mono with
              "[Hft Hfs HL Ha_t Ha_s]"); [
        | iApply (sim_bij_load_Some with "Hr") ]; eauto.
      iIntros (??) "H".

      iDestruct "H" as (????) "(H1 & H2)"; iFrame.
      repeat sfinal. }
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
    ⊢ code_refl_inv ∅ i_t i_s A_t A_s -∗
      dval_rel x_t x_s -∗
      dval_rel v_t v_s -∗
    trigger (Store x_t v_t) ⪯ trigger (Store x_s v_s)
      [{ (v1, v2), code_refl_inv ∅ i_t i_s A_t A_s }].
  Proof.
    iIntros (WF1 WF2 WF3) "CI #Dv #Dt".
    iApply store_must_be_addr; [ done | ].
    iIntros (????); subst.
    iApply sim_update_si.
    iIntros (??) "SI".
    iDestruct (dval_rel_addr' with "Dv") as "#Hb".
    iModIntro; iFrame; destruct_code_inv_all.

    iApply (sim_expr_bupd_mono with "[Hft Hfs HL AI]"); cycle 1.
    { iApply (sim_bij_store1 with "Dt Hb"); eauto. set_solver. }
    cbn. iIntros (??) "H".
    iDestruct "H" as (????) "H".
    repeat sfinal.
  Qed.

  Lemma store_refl_cfg x_t x_s v_t v_s τ C i_t i_s:
    dtyp_WF τ ->
    dvalue_has_dtyp v_t τ ->
    dvalue_has_dtyp v_s τ ->
    (forall a_t, x_t = DVALUE_Addr a_t ->
    forall a_s, x_s = DVALUE_Addr a_s ->
            C !! (a_t.1, a_s.1) = None) ->
    ⊢ CFG_refl_inv C i_t i_s -∗
      dval_rel x_t x_s -∗
      dval_rel v_t v_s -∗
    trigger (Store x_t v_t) ⪯ trigger (Store x_s v_s)
      [{ (v1, v2), CFG_refl_inv C i_t i_s }].
  Proof.
    iIntros (Hwf Hdt1 Hdt2 Hlu) "CI #Dv #Dt".
    iApply store_must_be_addr; [ done | ].
    iIntros (????); subst.
    iApply sim_update_si.
    iIntros (??) "SI".
    iDestruct (dval_rel_addr' with "Dv") as "#Hb".
    iModIntro; iFrame. destruct_CFG_inv_all.

    iApply (sim_expr_bupd_mono with "[Hft Hfs HL Ha_t Ha_s] [CI]"); cycle 1.
    { iApply (sim_bij_store1 with "Dt Hb"); eauto. }
    cbn. iIntros (??) "H".
    iDestruct "H" as (????) "H". repeat sfinal.
  Qed.

  Lemma alloca_refl_bij
    (τ : dtyp) (C : gmap (loc * loc) Qp)
    (i_t i_s : list frame_names) (A_t A_s : list loc):
    non_void τ ->
    code_refl_inv C i_t i_s A_t A_s -∗
    trigger (Alloca τ) ⪯ trigger (Alloca τ)
    [{ (a, a0), ∃ l_t l_s, dval_rel a a0 ∗
        code_refl_inv C i_t i_s (l_t :: A_t) (l_s :: A_s) }].
  Proof.
  (*   iIntros (WF) "CI". *)

  (*   rewrite -(bind_ret_r (trigger (Alloca τ))). *)
  (*   iApply sim_expr_bind. *)
  (*   destruct_code_inv_all. destruct_frame. *)
  (*   iApply (sim_expr_bupd_mono with "[]"); *)
  (*     [ | iApply (sim_alloca with "Ha_t Ha_s Hf_t Hf_s")]; eauto. *)
    
  (*   iIntros (??) "H". *)
  (*   iDestruct "H" as (????) "H". *)
  (*   rewrite H H0; clear H H0; rewrite !bind_ret_l. *)

  (*   iDestruct "H" as *)
  (*     (??????) "(Ht & Hs & Ha_t & Ha_s & Hs_t & Hs_s & Hbl_t & Hbl_s)"; subst. *)

  (*   iApply sim_update_si. *)
  (*   iModIntro; iIntros (??) "SI". *)
  (*   iDestruct "SI" as (???) "(Hh_s & Hh_t & H_c & Hbij & %WF_SI & SI)". *)

  (*   iAssert ((¬ ⌜set_Exists (λ '(b_t', b_s'), l_t = b_t') S⌝)%I) as "%Hext_t". *)
  (*   { iIntros (([b_t' b_s'] & Hin & <-)). *)
  (*     iDestruct "Hbij" as "(Hbij & Hheap)". *)
  (*     iPoseProof (big_sepS_elem_of with "Hheap") as "Hr"; first by apply Hin. *)
  (*     iDestruct "Hr" as (? v_t' v_s') "(Hr_t & Ha_t' & Ha_s')". *)
  (*     by iApply (heap_block_size_excl with "Hbl_t Ha_t'"). } *)

  (*   iPoseProof (lb_rel_empty_blocks τ) as "Hrel". *)
  (*   iDestruct (heapbij_insert_ctx $! _ _ with *)
  (*         "Hbij Hs_t Hs_s Ha_t Ha_s Hh_t Hh_s Ht Hs Hrel Hbl_t Hbl_s") as *)
  (*     ">(Hbij & #Hr & Ha_t & Ha_s & Hs_t & Hs_s & Hh_t & Hh_s)". *)

  (*   destruct_HC "Hh_s". *)
  (*   iDestruct (ghost_var_agree with "Hs_s HCF") as %Hd_s; subst. *)
  (*   iDestruct (ghost_var_agree with "HC H_c") as %Hc_s; subst. *)
  (*   rewrite allocaS_eq. *)
  (*   iDestruct (ghost_var_agree with "Ha_s HA") as %Hd_s; subst. *)

  (*   iDestruct "Hh_t" as (cft hFt) *)
  (*       "(Hσ_t&HB_t&HCF_t&HA_t&HL_t&HD_t&HSA_t&HG_t&%Hdup_t&%Hbs_t&%Hwf_t)". *)
  (*   iDestruct (ghost_var_agree with "Hs_t HCF_t") as %Hd_t; subst. *)
  (*   iDestruct (ghost_var_agree with "Ha_t HA_t") as %Hd_t; subst. *)

  (*   iFrame. *)

  (*   iSplitR "Hargs_t Hargs_s Hd_t Hd_s Hv HC Ha_t Ha_s Hs_t Hs_s Ha_bij". *)
  (*   { iExists _, ({[(l_t, l_s)]} ∪ S), G; iFrame. *)
  (*     iSplitR "HB_t HCF_t HA_t HL_t HD_t HSA_t". *)
  (*     { iModIntro; iExists _, _; iFrame. done. } *)
  (*     iSplitR "". *)
  (*     { iModIntro; iExists _, _; iFrame. done. } *)
  (*     iModIntro. iPureIntro. set_solver. } *)

  (*   iApply sim_expr_base. *)

  (*   iModIntro. *)
  (*   do 2 iExists _; iFrame. *)
  (*   do 2 (iSplitL ""; [ done  | ]). *)
  (*   iExists l_t, l_s; iFrame. *)

  (*   iSplitL ""; first by iApply dval_rel_addr. *)
  (*   repeat iExists _; iFrame. *)
  (*   iFrame "HWF". rewrite /refl_inv; iFrame. *)
  (*   iSplitL ""; first iSplitL ""; first done. *)
  (*   { iFrame "Hv". } *)
  (*   rewrite allocaS_eq; iFrame "Hr Ha_t Ha_s". *)
  (*   iPureIntro. *)
  (*   rewrite -not_elem_of_dom. *)
  (*   do 2 (split; first (apply NoDup_cons; set_solver)). *)
  (*   intro. apply Hext_t. *)
  (*   exists (l_t, l_s); split; auto. *)

  (*   Unshelve. all : set_solver. *)
  (* Qed. *)
  Admitted.

  (* Some utility for find_block for [ocfg]. *)
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
  (*     by rewrite find_block_eq. *)
  (*   - iSpecialize ("IH" $! _ _ H). *)
  (*     iDestruct "IH" as (??) "IH". *)
  (*     iExists v'; iFrame. *)
  (*     rewrite find_block_ineq; try rewrite Heq; try done. *)
  (* Qed. *)
  Admitted.

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
