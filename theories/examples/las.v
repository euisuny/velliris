From iris.prelude Require Import options.

From velliris.vir.lang Require Import lang.
From velliris.vir.logrel Require Import wellformedness logical_relations compatibility.

(* Import DenoteTactics. *)
Import CFG.

(* ------------------------------------------------------------------- *)
(* Load-after-store optimization. *)

Section las_example.

  (* [a] is the register that will be analyzed for load after store
     [v] is the current register whose value is stored in the address at [a]. *)

  (* LATER: Can generalize the [v] values being stored (e.g. storing constants).
     FIXME: Generalize [v] to expressions *)
  (* TODO: Figure out if there is a normal form that can be enforced to make
           sure expressions refer to [local_id]s. *)
  Fixpoint las_code {T} (c : code T) (a : raw_id) (v : option raw_id)
    : code T :=
    match c with
    | nil => nil
    | x :: tl =>
        match x with
        (* A load instruction from a stored [raw_id] that hasn't been modified *)
        | (id, INSTR_Load _ _ (_, EXP_Ident (ID_Local ptr)) _) =>
          if decide (a = ptr) then
            match v with
              | Some c =>
                  (id, INSTR_Op (EXP_Ident (ID_Local c))) ::
                  las_code tl a v
              | None => x :: las_code tl a v
            end
          else x :: las_code tl a v
        (* A store instruction to the promoted local identifier *)
        | (id, INSTR_Store _
                  (* TODO Warning! this is enforced by the syntactic
                      condition in the [TODO] above *)
                  (_, EXP_Ident (ID_Local v'))
                  (_, EXP_Ident (ID_Local ptr)) _) =>
            if decide (a = ptr) then
              x :: las_code tl a (Some v')
            else
              x :: las_code tl a v
        | x => x :: las_code tl a v
        end
    end.

  Definition las_block {T} (a : raw_id) (v : option raw_id) (b : LLVMAst.block T) :
    LLVMAst.block T :=
      mk_block
        (blk_id b)
        (blk_phis b)
        (las_code (blk_code b) a v)
        (blk_term b)
        (blk_comments b).

  (* Apply the [las] optimization over an open control flow graph. *)
  Definition las_ocfg {T} (o : ocfg T) a : ocfg T :=
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
             blks := las_ocfg (blks c) i ;
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
Compute (las_code code1 (Name "a")).

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

Lemma block_WF_las a0 a s:
  block_WF a ->
  block_WF (las_block a0 s a).
Proof. Admitted.

Lemma code_WF_las a0 a s:
  code_WF a0 ->
  code_WF (las_code a0 a s).
Proof. Admitted.

(* The [las] algorithm does not change the phi nodes. *)
Lemma las_phi_stable {T} a b :
  blk_phis (las_block a None b) = blk_phis (T := T) b.
Proof.
  eauto.
Qed.

(* Well-formedness of ocfg is preserved in the LAS transformation. *)
Lemma ocfg_WF_las f a:
  ocfg_WF f ->
  ocfg_WF (las_ocfg f a).
Proof.
  intros. induction f; eauto.
Admitted.

(* TODO: Instantiate [ocfg_is_SSA]. *)
Lemma ocfg_is_SSA_cons_inv a0 f :
  ocfg_is_SSA (a0 :: f) ->
  ocfg_is_SSA f.
Proof. Admitted.

Lemma promotable_ocfg_cons_inv {T} a0 (f : _ T) a:
  promotable_ocfg (a0 :: f) a ->
  promotable_ocfg f a.
Proof.
  rewrite /promotable_ocfg; cbn; intros.
  destructb. auto.
Qed.

Section las_example_proof.

Context `{vellirisGS Σ}.

Lemma local_bij_equiv_except l_t l_s:
 ∀ (i_t i_s : list frame_names) (L_t L_s : local_env) Π,
   local_bij i_t i_s L_t L_s ∗-∗
   local_bij_except l_t l_s i_t i_s L_t L_s ∗ Π.
Proof. Admitted.

(* TODO *)
Theorem expr_logrel_relaxed_refl C dt e A_t A_s:
  (⊢ expr_logrel_relaxed C dt dt e e A_t A_s)%I.
Proof. Admitted.

Theorem expr_logrel_refl' C dt e A_t A_s l:
  exp_local_ids e ## l ->
  (⊢ expr_logrel (local_bij_except l l) alloca_bij
     C dt dt e e A_t A_s)%I.
Proof. Admitted.

Definition term_local_ids {T} (e : terminator T) : list raw_id.
Admitted.

Theorem term_logrel_refl ϒ C l:
  term_local_ids ϒ ## l ->
  (⊢ term_logrel (local_bij_except l l) alloca_bij ϒ ϒ C)%I.
Proof with vsimp.
  iIntros (???????) "HI".
  destruct ϒ eqn: Hϒ; try solve [iDestruct "WF" as "[]"]; cbn.
  5-8: iApply exp_conv_raise.
  5 : iApply exp_conv_raiseUB.
  { (* TERM_Ret *)
    destruct v. vsimp. Cut.
    mono: iApply expr_logrel_refl'...
    { iDestruct "HΦ" as "(Hv & HΦ)"; vfinal. }
    admit. }
  { (* TERM_Ret_void *)
    vfinal. iApply uval_rel_none. }
  { (* TERM_Br *)
    destruct v; vsimp...
    Cut...
    mono: iApply expr_logrel_refl'...
    2 : { admit. }
    Cut... iDestruct "HΦ" as "(Hv & HI)".
    mono: (iApply (exp_conv_concretize_or_pick with "Hv")) with "[HI]"...
    destruct dv_s; try iApply exp_conv_raise; [ | iApply exp_conv_raiseUB ].
    iDestruct (dval_rel_I1_inv with "HΦ") as %->.
    destruct (DynamicValues.Int1.eq x DynamicValues.Int1.one); vfinal. }
  { (* TERM_Br_1 *)
    vfinal. }
Admitted.

Lemma las_instr_sim b a:
  ⊢ [∗ list] '(id, i);'(id', i') ∈ las_code b a None; b,
    ∀ A_t0 A_s0,
    instr_logrel
      (local_bij_except [a] [a])
        alloca_bij id i id' i' ∅ A_t0 A_s0.
Proof.
  iInduction b as [ | ] "IH"; eauto.
  { destruct a0. cbn.
    destruct i0; cbn; eauto; try iFrame "IH"; last first.
    all :
      try (iIntros (????) "HI";
      destruct i; try iApply instr_conv_raise).
    (* Follows by weakened reflexivity over instructions *)
    3-7 : admit.
    { (* Load *)
      destruct val.
      destruct e. 2-16: admit. (* weakened reflexivity? *)
      destruct id. 1 : admit. (* weakened reflexivity? *)
      destruct ptr.
      destruct e. 2-16: admit. (* weakened reflexivity? *)
      destruct id0. 1 : admit. (* weakened reflexivity? *)
      
Admitted.

Definition phis_local_ids {T} (e : list (local_id * phi T)) : list raw_id.
Admitted.

Lemma phis' {T} (Φ : list (local_id * phi T)) l:
  phis_local_ids Φ ## l ->
  Φ.*1 ## l /\
  (forall be ϕ,
      In ϕ Φ ->
      let '(Phi _ args) := ϕ.2 in
      forall e, Util.assoc be args = Some e ->
      exp_local_ids e ## l).
Proof. Admitted.

Lemma las_block_sim A_t A_s be b a:
  block_WF b ->
  term_local_ids (blk_term b) ## a :: nil ->
  phis_local_ids (blk_phis b) ## a :: nil ->
  ⊢ block_logrel (local_bij_except [a] [a]) alloca_bij
      (las_block a None b) b be ∅ A_t A_s.
Proof with vsimp.
  iIntros (WF Ht Hp).
  apply phis' in Hp; destruct Hp as (Hp1&Hp2).
  iApply block_compat; eauto.
  { by apply block_WF_las. }
  { iApply phis_compat; eauto.
    cbn. remember (blk_phis b); clear Heql.
    iInduction l as [ | ] "IH"; eauto.
    cbn; iSplitL.
    { destruct a0. iApply phi_compat; destruct p; cbn.
      destruct (Util.assoc be args) eqn: He; eauto.
      iApply expr_logrel_refl'.
      specialize (Hp2 be (l0, Phi t args)); cbn in *.
      eapply Hp2; eauto. }

    iApply "IH"; iPureIntro; eauto.
    { set_solver. }
    { intros. destruct ϕ.
      specialize (Hp2 be0 (l0, p)); destruct p; cbn.
      intros. eapply Hp2; eauto.
      by apply in_cons. } }

  { apply block_WF_inv in WF; destruct WF.
    iApply code_compat; eauto.
    { by apply code_WF_las. }
    cbn. iApply las_instr_sim. }

  { cbn; by iApply term_logrel_refl. }
Qed.

Lemma ocfg_SSA_promotable f a a0:
  ocfg_is_SSA (a0 :: f) ->
  promotable_ocfg (a0 :: f) a ->
  term_local_ids (blk_term a0) ## (a :: nil) /\
  phis_local_ids (blk_phis a0) ## (a :: nil).
Proof. Admitted.

Lemma las_simulation_ocfg
  (f : ocfg dtyp) a A_t A_s b1 b2 :
  ocfg_WF f ->
  ocfg_is_SSA f ->
  promotable_ocfg f a ->
  ⊢ ocfg_logrel
      (local_bij_except [a] [a])
      alloca_bij (las_ocfg f a) f ∅ A_t A_s b1 b2.
Proof.
  iIntros (???).
  iApply ocfg_compat; try done.
  { by eapply ocfg_WF_las. }
  iModIntro.
  iInduction f as [ | ] "IH"; eauto.
  apply ocfg_WF_cons_inv in H0. destruct H0.
  cbn. iSplitL "".
  { iSplitL ""; first done.
    pose proof (ocfg_SSA_promotable _ _ _ H1 H2).
    destruct H4.
    iIntros (???); iApply las_block_sim; eauto. }
  { iApply "IH"; eauto.
    { iPureIntro; eapply ocfg_is_SSA_cons_inv; eauto. }
    { iPureIntro. eapply promotable_ocfg_cons_inv; eauto. } }
Qed.

Lemma las_simulation_cfg (f : cfg dtyp) a A_t A_s:
  cfg_WF f ->
  cfg_is_SSA f ->
  ⊢ cfg_logrel
      (local_bij_except [a] [a])
      alloca_bij (las f) f ∅ A_t A_s.
Proof.
  intros. iApply cfg_compat; eauto; last first.
  { rewrite /las.
    destruct (find_promotable_alloca f) eqn: Hf; eauto; cbn.
    { destruct p, i; cbn.
      {
Admitted.

Lemma las_simulation (f : function) :
  fun_WF (las_fun f) ->
  fun_WF f ->
  fun_is_SSA f ->
  ⊢ fun_logrel (las_fun f) f ∅.
Proof.
  iIntros;
  rewrite /las_fun. destruct f; cbn.
    iApply fun_compat; last first.
  { iIntros; cbn.
    iApply las_simulation_cfg; admit. }
  all : eauto.
Admitted.

Theorem las_correct (c : function) :
  fun_is_SSA c ->
  ctx_ref (las_fun c) c.
Proof. Admitted.

(* TODO: Prove it *)

End las_example_proof.
