From iris.prelude Require Import options.

From velliris.vir.lang Require Import lang.
From velliris.vir.rules Require Import rules.
From velliris.vir.logrel Require Import wellformedness logical_relations compatibility.

(* Import DenoteTactics. *)
Import CFG.

(* ------------------------------------------------------------------- *)
(* Load-after-store optimization. *)

Section las_example.

  (* [promotable] is the register that will be analyzed for load after store
     [stored_value] is the current register whose value is stored in the address
      at [promotable]. *)
 Definition las_instr {A : Set} {T}
   (promotable : raw_id) (stored_val : option raw_id) (i : A * instr T) :=
    match i with
    (* A load instruction from a stored [raw_id] that hasn't been modified. *)
    | (promotable_id, INSTR_Load _ _ (_, EXP_Ident (ID_Local ptr)) _) =>
      if decide (promotable = ptr) then
        match stored_val with
          | Some c =>
              (* The promotable location has been written to; substitute the load
                 for the local identifier for the promotable location instead. *)
              ((promotable_id, INSTR_Op (EXP_Ident (ID_Local promotable))), stored_val)
          | None => (i, stored_val)
        end
      else (i, stored_val)
    (* A store instruction to the promoted local identifier. *)
    | (_, INSTR_Store _
              (_, EXP_Ident (ID_Local v'))
              (_, EXP_Ident (ID_Local ptr)) _) =>
        if decide (promotable = ptr) then
          (* Update the stored value *)
          (i, Some v')
        else
          (i, stored_val)
    | x => (i, stored_val)
    end.

  (* Given a code block [c] and a promotable location, (i.e. a local identifier
     that stores a non-aliased location that has been allocated in the current block),
     check if that location has a load after having stored a value.

     The [stored_val] keeps track of the most recent store of the code block to the
     promotable location [promotable].

    LATER:
      - Can generalize the [v] values being stored (e.g. storing constants).
      - Generalize [v] to expressions
      - Figure out if there is a normal form that can be enforced to make
                sure expressions refer to [local_id]s. *)
  Fixpoint las_code {T}
    (promotable : local_id) (stored_val : option raw_id) (c : code T) :=
    match c with
    | nil => nil
    | x :: tl =>
        let '(x, v) :=
          las_instr promotable stored_val x
        in
        x :: las_code promotable v tl
    end.

  Definition las_block {T} (a : raw_id) (v : option raw_id) (b : LLVMAst.block T) :
    LLVMAst.block T :=
      mk_block
        (blk_id b)
        (blk_phis b)
        (las_code a v (blk_code b))
        (blk_term b)
        (blk_comments b).

  (* Apply the [las] optimization over an open control flow graph. *)
  Definition las_ocfg {T} a (o : ocfg T) : ocfg T :=
    List.map (las_block a None) o.

  Definition raw_id_not_in_texp {T} (l : list (texp T)) (i : raw_id) : bool :=
    forallb
      (fun x => match x with
             | (_, EXP_Ident (ID_Local i')) => bool_decide (i = i')
             | _ => false
             end) l.

  (* TODO: Generalize to [def use] for computing use information *)
  Fixpoint expr_contains_raw_id {T} (e : exp T) (i : raw_id) : bool :=
    match e with
    | EXP_Ident (ID_Local i') => bool_decide (i = i')
    | EXP_Cstring l | EXP_Struct l | EXP_Array l =>
        List.existsb (fun x => expr_contains_raw_id x.2 i) l
    | OP_IBinop _ _ v1 v2 | OP_ICmp _ _ v1 v2 =>
        expr_contains_raw_id v1 i || expr_contains_raw_id v2 i
    | OP_Conversion _ _ v _ =>
        expr_contains_raw_id v i
    | OP_GetElementPtr _ (_, e) l =>
        expr_contains_raw_id e i ||
        List.existsb (fun x => expr_contains_raw_id x.2 i) l
    | _ => false
    end.

  Definition instr_contains_raw_id {T} (e : instr T) (i : raw_id) : bool :=
    match e with
    | INSTR_Op e
    | INSTR_Alloca _ (Some (_, e)) _
    | INSTR_Load _ _ (_, e) _ =>
        expr_contains_raw_id e i
    | INSTR_Call (_, fn) l _ =>
        expr_contains_raw_id fn i ||
        List.existsb (fun x => expr_contains_raw_id x.2 i) l
    | INSTR_Store _ (_, e1) (_, e2) _ =>
        expr_contains_raw_id e1 i || expr_contains_raw_id e2 i
    | _ => false
    end.

  Definition phi_contains_raw_id {T} (e : phi T) (i : raw_id) : bool :=
    let '(Phi t l) := e in
    List.existsb (fun x => expr_contains_raw_id x.2 i) l.

  (* FUTURE WORK: Alias analysis *)
  Definition promotable_instr {T} (i : instr_id * instr T) a : bool :=
    match i.2 with
      | INSTR_Load _ _ (_, EXP_Ident (ID_Local _)) _ => true
      | INSTR_Store _
                (_, e)
                (_, EXP_Ident (ID_Local _)) _ =>
          negb (expr_contains_raw_id e a)
      | _ => negb (instr_contains_raw_id i.2 a)
    end.

  Definition promotable_block {T} (i : LLVMAst.block T) a : bool :=
    forallb (fun x => promotable_instr x a) (blk_code i).

  Definition promotable_ocfg {T} (c : ocfg T) a :=
    forallb (fun i => promotable_block i a) c.

  Definition promotable_cfg {T} (c : cfg T) a :=
    promotable_ocfg (blks c) a.

  (* Given a control flow graph [c], return a promotable instruction id and
     instruction pair if one is found. *)
  Definition find_promotable_alloca {T} (c : cfg T) :=
    (* LATER: Refactor this [instrs] comptuation? *)
    let instrs := List.concat (List.map (blk_code) (blks c)) in
    List.find
      (fun x => match x with
             | (IId a, INSTR_Alloca _ _ _) => promotable_cfg c a
             | _ => false
             end) instrs.

  (* Load-after-store optimization. *)
  Definition las {T} (c : cfg T) : cfg T :=
    match find_promotable_alloca c with
      | Some (IId i, _) =>
          {| init := init c ;
             blks := las_ocfg i (blks c) ;
             args := args c |}
      | _ => c
    end.

  (* Load-after-store on a function definition. *)
  Definition las_fun (f : definition dtyp (cfg dtyp)) : definition _ _ :=
    {| df_prototype := df_prototype f;
       df_args := df_args f;
       df_instrs := las (df_instrs f) |}.

End las_example.

(* For a sanity check, running some examples... *)
Example code1 : code dtyp :=
  (IId (Name "a"), INSTR_Alloca (DTYPE_I 32%N) None None) ::
  (IId (Name "b"), INSTR_Op (EXP_Integer 42)) ::
  (IVoid 2, INSTR_Store true
                  (DTYPE_I 32, EXP_Ident (ID_Local (Name "b")))
                  (DTYPE_Pointer, EXP_Ident (ID_Local (Name "a")))
                   None) ::
  (IId (Name "b"), INSTR_Load true (DTYPE_I 32)
      (DTYPE_I 32, EXP_Ident (ID_Local (Name "a"))) None) ::
  nil.

Example block1 : LLVMAst.block dtyp :=
  {|
    blk_id    := Name "init_block";
    blk_phis  := nil;
    blk_code  := code1;
    blk_term  := TERM_Ret (DTYPE_I 8%N, (EXP_Integer 8));
    blk_comments := None
  |}.

Example ocfg1 : ocfg dtyp := block1 :: nil.

Example cfg1 : cfg dtyp :=
  {| init := Name "init_block";
     blks := ocfg1;
     args := nil; |}.

Compute (find_promotable_alloca cfg1).

Compute (las cfg1).
Compute (las_code (Name "a") None code1).

(* ------------------------------------------------------------------- *)
(* Specification of the Load-after-store optimization. *)

Notation function := (definition dtyp (cfg dtyp)).

(* TODO Get this definition from [contextual]. *)
Axiom ctx_ref : function -> function -> Prop.
Axiom fun_is_SSA : function -> Prop.
Axiom ocfg_is_SSA : ocfg dtyp -> Prop.
Axiom cfg_is_SSA : cfg dtyp -> Prop.
Axiom code_is_SSA : code dtyp -> Prop.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import logical_relations tactics.

(* ------------------------------------------------------------------- *)

(* TODO: Move and prove on [wellformedness]. *)
Lemma fun_WF_inv f:
  fun_WF f -> cfg_WF (df_instrs f).
Proof. Admitted.

(* TODO: Move *)
Lemma cfg_WF_inv f:
  cfg_WF f ->
  ocfg_WF (blks f).
Proof. Admitted.

(* ------------------------------------------------------------------- *)
(* Well-formedness is preserved in the LAS transformation. *)

Lemma las_block_WF a0 a s:
  block_WF a ->
  block_WF (las_block a0 s a).
Proof. Admitted.

Lemma las_code_WF a0 a s:
  code_WF a0 ->
  code_WF (las_code a s a0).
Proof. Admitted.

Lemma las_fun_WF f:
  fun_WF f ->
  fun_WF (las_fun f).
Proof. Admitted.

Lemma las_ocfg_WF f a:
  ocfg_WF f ->
  ocfg_WF (las_ocfg a f).
Proof.
  intros. induction f; eauto.
Admitted.

Lemma las_cfg_WF f:
  cfg_WF f ->
  cfg_WF (las f).
Proof.
  intros. induction f; eauto.
Admitted.

(* ------------------------------------------------------------------- *)

(* The [las] algorithm does not change the phi nodes. *)
Lemma las_phi_stable {T} a b :
  blk_phis (las_block a None b) = blk_phis (T := T) b.
Proof.
  eauto.
Qed.

(* ------------------------------------------------------------------- *)

Lemma find_promotable_alloca_some {T} f promotable instr:
  find_promotable_alloca f = Some (IId promotable, instr) ->
  let instrs := concat (map (blk_code (T := T)) (blks f)) in
  (IId promotable) ∈ instrs.*1.
Proof. Admitted.

(* SSA definitions *)

(* TODO: Move ? *)
Definition SSA_cfg {T} (c : cfg T) :=
  let ocfg := blks c in
  let code := concat (map (blk_code (T := T)) ocfg) in
  let code_ids : list raw_id :=
    fold_left
      (fun acc x =>
          match x with
          | IId i => i :: acc
          | _ => acc
          end)
      code.*1 [] in
  let phis :=
    concat (map (blk_phis (T := T)) ocfg) in
  (* The code ids and phi ids are disjoint *)
  code_ids ## phis.*1 /\ NoDup code_ids /\ NoDup phis.*1.

Definition SSA_function (f : function) :=
  SSA_cfg (df_instrs f).

Lemma SSA_fun_implies_promotable_phi_disjoint f instr promotable:
  find_promotable_alloca f = Some (IId promotable, instr) ->
  ∀ b : LLVMAst.block dtyp,
    b ∈ blks f → (blk_phis b).*1 ## promotable :: nil.
Proof. Admitted.

(* ------------------------------------------------------------------- *)

Section las_example_proof.

  Context `{vellirisGS Σ}.

  (* ------------------------------------------------------------------- *)

  (* TODO: Get from [fundamental.v] *)
  Theorem fun_logrel_refl f attr:
    fun_WF f ->
    (⊢ fun_logrel attr_inv attr f f ∅)%I.
  Proof. Admitted.

  Definition local_bij_except_promotable promotable i_t i_s L_t L_s :=
    (local_bij_except [promotable] [promotable] i_t i_s L_t L_s ∗
    (* If the promotable location is already part of the domain, get ownership
       over this. *)
    (⌜promotable ∈ L_t.*1⌝ -∗ ∃ v_t : local_val, [ promotable := v_t ]t i_t) ∗
    (⌜promotable ∈ L_s.*1⌝ -∗ ∃ v_s : local_val, [ promotable := v_s ]s i_s))%I.

  Lemma local_bij_implies_local_bij_except_promotable i_t i_s L_t L_s promotable:
    local_bij i_t i_s L_t L_s -∗
    local_bij_except_promotable promotable i_t i_s L_t L_s.
  Proof. Admitted.

  Opaque find_promotable_alloca.

  (* ------------------------------------------------------------------- *)

  (* If it's a well-formed program, it should have allocated the local id before
     trying to perform the optimization, thus we have the ownership for the
     locations. *)

  (* [LAS] case where the load is removed. *)
  (* FIXME: Use simulation relation directly *)
  Lemma las_instr_sim_load
    promotable v_t v_s i_t i_s ptr ptr' A_t A_s id val align b τ τ' l_t l_s:
    let '((id', i'), v) :=
      (las_instr promotable (Some val)
         (IId id, INSTR_Load b τ (τ', EXP_Ident (ID_Local promotable)) align)) in
    (* The promotable local id stores a pointer that is allocated on both source
       and target. *)
    [ id := l_s ]s i_s -∗
    [ id := l_t ]t i_t -∗
    [ promotable := UVALUE_Addr (ptr, 0%Z) ]s i_s -∗
    ptr ↦s v_s  -∗
    [ promotable := UVALUE_Addr (ptr', 0%Z) ]t i_t -∗
    ptr ↦t v_t  -∗
    dval_rel v_t v_s -∗
    instr_logrel
      (local_bij_except [promotable] [promotable])
      alloca_bij
      i_t i_s
      id'
      i'
      (IId id)
      (INSTR_Load b τ (τ', EXP_Ident (ID_Local promotable)) align)
      ∅ A_t A_s.
  Proof.
    cbn; destruct_if_goal; try done.  clear e H0 H2.
    (* Reduced *)
    iIntros "Hids Hidt Hls Hps Hlt Hpt #Hv CI".
    iApply target_red_sim_expr.
    destruct_code_inv_all; repeat destruct_frame.
    iApply (target_instr_local_write1 with "Hs_t Hd_t Hidt [Hlt]");
      cycle 1; eauto.
    { iIntros "Hid Hdt_t Hs_t".
      rewrite /denote_instr_exp; cbn -[denote_op].
      iApply target_red_eq_itree.
      { by rewrite eq_itree_exp_conv_to_instr. }
      iApply (target_local_id with "Hs_t Hlt").
      iIntros "Hs_t Ht"; sfinal. }
    iIntros "Ht Hd_t Hs_t".

    iApply source_red_sim_expr.
    iApply (source_instr_load with "Hps Hls Hd_s Hs_s"); last first.
    (* Hd_s Hids [Hls]"); cycle 1; eauto. *)
    { iIntros "Hid Hdt_t Hs_t' Hd_s Hs_s".
      Base. do 2 sfinal.
      iFrame "WF_frame".
  Abort.

  Lemma las_simulation_code a b A_t A_s :
    code_WF (blk_code b) ->
    ⊢ code_logrel
        (local_bij_except_promotable a)
        alloca_bij
        (blk_code (las_block a None b))
        (blk_code b)
        ∅ A_t A_s.
  Proof.
    iIntros (?); iApply code_compat; eauto;
      first by apply las_code_WF.

    (* TODO: MEDIUM
        [las_instr custom logical relation]. *)
  Admitted.

  Lemma las_simulation_term a b:
    term_WF (blk_term b) ->
    ⊢ term_logrel
        (local_bij_except_promotable a)
        alloca_bij
        (blk_term (las_block a None b))
        (blk_term b)
        ∅.
  Proof.
    (* TODO: Show reflexivity of [except] for terminators, analogous to
            expressions. *)
  Admitted.

   Definition phis_inv ΠL ΠA C i_t i_s A_t A_s L_t L_s : iPropI Σ :=
    (local_inv ΠL i_t i_s L_t L_s C ∗ alloca_inv ΠA i_t i_s A_t A_s C)%I.

   (* Got extended with a new domain *)
   Definition phis_post_inv ΠL ΠA C i_t i_s A_t A_s
     (L_t L_s : local_env) (Φ_t Φ_s : list local_id)
     : iPropI Σ :=
    (∃ (L_t' L_s' : local_env),
        ⌜(list_to_set L_t.*1 ∪ list_to_set Φ_t : gset _) ≡
          (list_to_set L_t'.*1 : gset local_id)⌝ ∗
        ⌜(list_to_set L_s.*1 ∪ list_to_set Φ_s : gset _) ≡
          (list_to_set L_s'.*1 : gset local_id)⌝ ∗
        local_inv ΠL i_t i_s L_t' L_s' C ∗ alloca_inv ΠA i_t i_s A_t A_s C)%I.

   Definition phis_logrel ΠL ΠA bid_t bid_s Φ_t Φ_s C A_t A_s : iPropI Σ :=
    (∀ i_t i_s L_t L_s, phis_inv ΠL ΠA C i_t i_s A_t A_s L_t L_s -∗
       instr_conv (denote_phis bid_t Φ_t) ⪯ instr_conv (denote_phis bid_s Φ_s)
       [{ (r_t, r_s),
           phis_post_inv ΠL ΠA C i_t i_s A_t A_s L_t L_s (Φ_t.*1) (Φ_s.*1) }])%I.

  Theorem block_compat ΠL ΠA b b' bid A_t A_s:
    block_WF b ->
    block_WF b' ->
    phis_logrel ΠL ΠA
      bid bid (blk_phis b) (blk_phis b')
      ∅ A_t A_s -∗
    code_logrel ΠL ΠA
      (blk_code b)
      (blk_code b')
      ∅ A_t A_s -∗
    term_logrel ΠL ΠA
      (blk_term b)
      (blk_term b')
      ∅ -∗
    block_logrel ΠL ΠA b b' bid ∅ A_t A_s.
  Proof with vsimp.
  Admitted.

  Theorem phis_compat ΠA C bid Φ Φ' A_t A_s l_t l_s:
    Φ.*1 ## l_t ->
    Φ'.*1 ## l_s ->
    Φ.*1 = Φ'.*1 ->
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
       phi_logrel (local_bij_except l_t l_s)
         ΠA bid bid ϕ ϕ' C A_t A_s) -∗
    phis_logrel (local_bij_except l_t l_s)
      ΠA bid bid Φ Φ' C A_t A_s.
  Proof with vsimp. Admitted.

  Lemma expr_logrel_refl_bij_except t e A_t A_s L:
    exp_local_ids e ## L ->
    ⊢ expr_logrel
        (local_bij_except L L)
        alloca_bij ∅ (Some t) (Some t) e e A_t A_s.
  Proof. Admitted.

  Lemma las_simulation_phis a be b A_t A_s :
    (blk_phis b).*1 ## (a :: nil) ->
    ⊢ phis_logrel
        (local_bij_except [a] [a]) alloca_bij
        be be
        (blk_phis (las_block a None b))
        (blk_phis b)
        ∅ A_t A_s.
  Proof.
    iIntros (?); iApply phis_compat; cbn; eauto.
    iInduction (blk_phis b) as [ | ] "IH"; eauto.
    cbn; iSplitL; first iClear "IH"; last first.
    { (* Inductive case can be discharged trivially. *)
      iApply "IH"; iPureIntro; set_solver. }

    destruct a0; iApply phi_compat; destruct p.
    destruct (Util.assoc be args) eqn: Hlu; eauto.
    iApply expr_logrel_refl_bij_except; eauto; cbn in *.

    (* TODO: EASY, but tedius.
        [expr_logrel] with [local_bij_except]. *)
    (* TODO: Might need to strengthen
        Propagate from [find_promotable_alloca] that we have
        a disjoint set. *)
    (* TODO: Not sure
        [local_bij_except] does not include the subpredicates
        of [local_bij_except_promotable]. *)
  Admitted.

  Lemma las_simulation_cfg (f : cfg dtyp) a i A_t A_s:
    cfg_WF f ->
    (* The promotable location is not a local id that appears in the phi nodes. *)
    (∀ b, b ∈ blks f -> ((blk_phis b).*1 ## a :: nil)) ->
    (* Promotable location is found. *)
    find_promotable_alloca f = Some (IId a, i) ->
    ⊢ cfg_logrel
        (local_bij_except_promotable a)
        alloca_bij (las f) f ∅ A_t A_s.
  Proof.
    intros Hwf Hnophi Halloc.
    iApply cfg_compat; eauto;
      [ by apply las_cfg_WF | by rewrite /las Halloc | ].

    (* Related ocfg's. *)
    iApply ocfg_compat.
    { rewrite /las Halloc; by apply las_ocfg_WF, cfg_WF_inv. }
    { by apply cfg_WF_inv. }

    rewrite /las Halloc; cbn.
    iModIntro; destruct f; cbn. clear Halloc.
    iInduction blks as [ | ] "IH"; eauto.
    cbn. iSplitL; cycle 1.

    { (* Inductive case can be trivially discharged *)
      iApply "IH"; iPureIntro; eauto.
      (* Well-formedness. *)
      - apply cfg_WF_inv in Hwf; cbn in *; by destructb.
      - intros; eapply Hnophi; set_solver. }

    iSplitL ""; first done; iIntros (???); iClear "IH".

    (* Well-formedness. *)
    apply cfg_WF_inv in Hwf; cbn in *; destructb.
    pose proof (HWF := H0); apply andb_true_iff in H0; destruct H0.

    (* Compatibility of blocks under [las] transformation. *)
    iApply block_compat; eauto; [ by apply las_block_WF | .. ].

    (* Phis logrel *)
    { iIntros (????) "(HL & HA)".
      destruct_local_inv.
      iDestruct "HL" as "(HL & Hp)".

      assert ((blk_phis a0).*1 ## a :: nil). { set_solver. }
      mono: iApply las_simulation_phis with "[Hp]"; last sfinal.
      iIntros (??) "H".
      iDestruct "H" as (????) "H"; sfinal.
      iDestruct "H" as (????) "(HlI & AI)".
      sfinal; destruct_local_inv; iFrame.
      iDestruct "Hp" as "(Hp1 & Hp2)".
      iSplitL "Hp1".
      { iModIntro; iIntros (?); iApply "Hp1". iPureIntro. set_solver. }
      { iModIntro; iIntros (?); iApply "Hp2". iPureIntro. set_solver. } }

    (* Code logrel *)
    { by iApply las_simulation_code. }

    (* Term logrel *)
    { by iApply las_simulation_term. }
  Qed.

  Lemma las_simulation (f : function) :
    SSA_function f ->
    fun_WF f ->
    ⊢ fun_logrel attr_inv nil (las_fun f) f ∅.
  Proof.
    iIntros; rewrite /las_fun /las; cbn.

    (* Has a promotable location been found? *)
    destruct (find_promotable_alloca (df_instrs f)) eqn: Promotable_found;
      cycle 1.

    { (* 1. No promotable location found; conclude by reflexivity. *)
      by iApply fun_logrel_refl. }

    (* 2. (Main case) promotable location has been found. *)
    destruct p, i; last by iApply fun_logrel_refl.

    (* Renaming variables. *)
    rename i0 into promotable_alloca_instr.
    rename id into promotable.
    rename H0 into SSA_f.
    rename H1 into fun_WF_src.

    (* Use compatibility of functions *)
    iApply
      (fun_compat
        (local_bij_except_promotable promotable));
      eauto; cycle 3.

    (* Well-formedness is maintained by the [las] transformation. *)
    { eapply las_fun_WF in fun_WF_src.
      by rewrite /las_fun /las Promotable_found in fun_WF_src. }

    (* State the invariant first. *)
    { cbn; iIntros (??????) "Hlt Hls Hargs".
      iApply local_bij_implies_local_bij_except_promotable;
        rewrite /local_bij; iFrame.
      rewrite -H0; done. }

    (* CFG's are related to each other. *)
    iIntros (??); cbn.
    iPoseProof (las_simulation_cfg (df_instrs f)) as "H";
      eauto; last first.
    { by rewrite /las Promotable_found. }
    { eapply SSA_fun_implies_promotable_phi_disjoint; eauto. }
    apply fun_WF_inv in fun_WF_src; eauto.
  Qed.

  Theorem las_correct (c : function) :
    fun_is_SSA c ->
    ctx_ref (las_fun c) c.
  Proof. Abort. (* TODO *)

End las_example_proof.
