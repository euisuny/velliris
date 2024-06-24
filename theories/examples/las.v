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
 Definition las_instr {T}
   (promotable : raw_id) (stored_val : option raw_id) (i : _ * instr T) (allocated : bool) :=
    if allocated then
      match i with
      (* A load instruction from a stored [raw_id] that hasn't been modified. *)
      | (IId promotable_id, INSTR_Load _ _ (_, EXP_Ident (ID_Local ptr)) _) =>
        if decide (promotable = ptr) then
          match stored_val with
            | Some c =>
                (* The promotable location has been written to; substitute the load
                  for the local identifier for the promotable location instead. *)
                ((IId promotable_id, INSTR_Op (EXP_Ident (ID_Local c))), stored_val, allocated)
            | None => (i, stored_val, allocated)
          end
        else (i, stored_val, allocated)
      (* A store instruction to the promoted local identifier. *)
      | (IVoid _, INSTR_Store _
                (_, EXP_Ident (ID_Local v'))
                (_, EXP_Ident (ID_Local ptr)) _) =>
          if decide (promotable = ptr) then
            (* Update the stored value *)
            (i, Some v', allocated)
          else
            (i, stored_val, allocated)
      | x => (i, stored_val, allocated)
      end
    else
      match i with
      (* The alloca instruction with promotable id. *)
      | (IId id, INSTR_Alloca _ _ _) =>
        if decide (promotable = id)
        then (i, stored_val, true)
        else (i, stored_val, allocated)
      | _ => (i, stored_val, allocated)
      end
   .

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
    (promotable : local_id) (stored_val : option raw_id) (c : code T) (allocated : bool) :=
    match c with
    | nil => nil
    | x :: tl =>
        let '(x, v, allocated) :=
          las_instr promotable stored_val x allocated
        in
        x :: las_code promotable v tl allocated
    end.

  Definition las_block {T} (a : raw_id) (v : option raw_id) (b : LLVMAst.block T) :
    LLVMAst.block T :=
      mk_block
        (blk_id b)
        (blk_phis b)
        (las_code a v (blk_code b) false)
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
  (IId (Name "c"), INSTR_Load true (DTYPE_I 32)
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
Compute (las_code (Name "a") None code1 false).

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

(* LATER: FIXME Unify [is_true] and [Is_true] coercion *)
Lemma fun_WF_inv f:
  fun_WF f ->
  NoDup (df_args f) /\ cfg_WF (df_instrs f).
Proof.
  rewrite /fun_WF; intros WF; destructb; split;
    [ apply NoDup_b_NoDup1 ; by rewrite H | done ].
Qed.

(* TODO: Move *)
Lemma cfg_WF_inv f:
  cfg_WF f ->
  ocfg_WF (blks f).
Proof. done. Qed.

(* ------------------------------------------------------------------- *)
Ltac splitb :=
  repeat match goal with
  | |- is_true (_ && _) =>
      apply Bool.andb_true_iff; split
  | |- Is_true (_ && _) =>
      apply andb_True; split
  end.

(* TODO : Write subcases for all [WF] constructs *)
Ltac invert_WF :=
  match goal with
    | [ H : is_true (block_WF _) |- _ ] =>
        let WF_code := fresh "WF_code" in
        let WF_term := fresh "WF_term" in
        apply block_WF_inv in H;
        destruct H as (WF_code & WF_term)
    | [ H : is_true (fun_WF _) |- _ ] =>
        let WF_args := fresh "WF_args" in
        let WF_cfg := fresh "WF_cfg" in
        apply fun_WF_inv in H;
        destruct H as (WF_args & WF_cfg)
    | [ H : is_true (code_WF (cons _ _)) |- _ ] =>
        let WF_hd := fresh "WF_hd" in
        let WF_tl := fresh "WF_tl" in
        apply code_WF_cons_inv in H;
        destruct H as (WF_hd & WF_tl)
  end.

(* TODO *)
Ltac reflectb :=
  repeat match goal with
  | [ H : NoDup_b _ = true |- _] => apply NoDup_b_NoDup in H
  | [ H : Nat.eqb _ _ = true |- _] => apply Nat.eqb_eq in H
  | [ H : forallb _ _ = true |- _] => rewrite forallb_True in H
  end.
(* ------------------------------------------------------------------- *)
(* Well-formedness is preserved in the LAS transformation. *)

Lemma las_instr_WF:
  ∀ (a : instr_id * instr dtyp) (p : local_id) (v : option raw_id)
    (bi bf : bool) (id : instr_id) (instr : instr dtyp) (o : option raw_id),
  instr_WF a.2 ->
  las_instr p v a bi = (id, instr, o, bf) →
  instr_WF instr.
Proof.
  intros * WF Hinstr.
  rewrite /las_instr in Hinstr.
  destruct_if; by destruct_match.
Qed.

Lemma las_code_WF p v c b:
  code_WF c ->
  code_WF (las_code p v c b).
Proof.
  intros WF; revert p v b.
  induction c; first done.
  destruct (code_WF_cons_inv _ _ WF) as (WF_i & WF_c).
  specialize (IHc WF_c).
  intros *; cbn.
  destruct (las_instr p v a b) as (((?&?)&?)&?)
    eqn: Hinstr; cbn.
  splitb; [ by eapply las_instr_WF | apply IHc ].
Qed.

Lemma las_block_WF p v b:
  block_WF b ->
  block_WF (las_block p v b).
Proof.
  intros WF; invert_WF.
  apply (las_code_WF p v _ false) in WF_code.
  rewrite /block_WF; by splitb.
Qed.

Lemma las_ocfg_WF f a:
  ocfg_WF f ->
  ocfg_WF (las_ocfg a f).
Proof.
  intros. induction f; eauto.
Admitted. (* las_ocfg_WF *)

Lemma las_fun_WF f:
  fun_WF f ->
  fun_WF (las_fun f).
Proof.
  intros WF. invert_WF.
  rewrite /fun_WF; splitb.
Admitted. (* las_fun_WF *)

Lemma las_cfg_WF f:
  cfg_WF f ->
  cfg_WF (las f).
Proof.
  intros. induction f; eauto.
Admitted. (* las_cfg_WF *)

(* ------------------------------------------------------------------- *)

(* The [las] algorithm does not change the phi nodes. *)
Lemma las_phi_stable {T} a b :
  blk_phis (las_block a None b) = blk_phis (T := T) b.
Proof.
  eauto.
Qed.

(* ------------------------------------------------------------------- *)

(* If a promotable alloca is found, it must be in the list of instructions
   in the ocfg that it was found in. *)
Lemma find_promotable_alloca_some {T} f promotable instr:
  find_promotable_alloca f = Some (IId promotable, instr) ->
  let instrs := concat (map (blk_code (T := T)) (blks f)) in
  (IId promotable) ∈ instrs.*1.
Proof.
  rewrite /find_promotable_alloca; cbn.
  revert instr promotable.
  remember (map blk_code (blks f)); clear Heql.
  induction l; cbn; intros; inv H.
  destruct a; cbn in *; eauto.
  destruct p; cbn in *; destruct_if; inv H1; first set_solver.
  destruct_match; inv H.
Abort.

(** *SSA definitions *)

(* TODO: Move ? *)
(* There are no duplicate id's in its syntax. *)
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
Proof.
Admitted. (* SSA_fun_implies_promotable_phi_disjoint *)

(* ------------------------------------------------------------------- *)

Section las_example_proof.

  Context `{vellirisGS Σ}.

  (* ------------------------------------------------------------------- *)

  (* TODO: Get from [fundamental.v] *)
  Theorem expr_logrel_refl dt e C A_t A_s :
    (⊢ expr_logrel local_bij alloca_bij C dt dt e e A_t A_s)%I.
  Proof. Admitted. (* MOVE *)

  Theorem instr_logrel_refl id e A_t A_s i_t i_s:
    instr_WF e ->
    (⊢ instr_logrel local_bij alloca_bij i_t i_s id e id e ∅ A_t A_s)%I.
  Proof with vsimp. Admitted. (* MOVE *)

  Theorem fun_logrel_refl f attr:
    fun_WF f ->
    (⊢ fun_logrel attr_inv attr f f ∅)%I.
  Proof. Admitted. (* MOVE *)

  Theorem term_logrel_refl ϒ C:
    (⊢ term_logrel local_bij alloca_bij ϒ ϒ C)%I.
  Proof with vsimp. Admitted. (* MOVE *)

  Theorem phis_compat ΠA C bid Φ Φ' A_t A_s l_t l_s:
    Φ.*1 ## l_t ->
    Φ'.*1 ## l_s ->
    Φ.*1 = Φ'.*1 ->
    ([∗ list] ϕ;ϕ' ∈ Φ; Φ',
       phi_logrel local_bij
         ΠA bid bid ϕ ϕ' C A_t A_s) -∗
    phis_logrel local_bij ΠA bid bid Φ Φ' C A_t A_s.
  Proof with vsimp. Admitted. (* MOVE *)

  Opaque find_promotable_alloca.

  (* ------------------------------------------------------------------- *)

  (* If it's a well-formed program, it should have allocated the local id before
     trying to perform the optimization, thus we have the ownership for the
     locations. *)

  Local Ltac las_trivial Hlas :=
    cbn in *; destruct_match; inv Hlas; destruct_if;
    iIntros; try iApply instr_logrel_refl;
    try by destructb.

  Lemma las_instr_inv {T a o a0 id p b b'}:
    las_instr (T := T) a o a0 b' = (p, id, b) ->
    (* Instruction did not change or *)
    a0 = p \/
    (* It did change and ... *)
     exists id0 t t0 id2 align volatile r,
       b' = true /\
       a  = id2 /\
       o = Some r /\
       a0 = (IId id0, INSTR_Load volatile t (t0, ' id2 ') align) /\
       p = (IId id0, INSTR_Op (' r ')).
  Proof.
    intros; rewrite /las_instr in H0.
    destruct_match; eauto. right. repeat eexists; done.
  Qed.

  (* Case analysis on when the instruction is unchanged. *)
  Lemma las_instr_unchanged_inv {T a o id p b b'}:
    las_instr (T := T) a o p b' = (p, id, b) ->
    (* The allocation state did not change or... *)
    b' = b \/
    (* It was an alloca instruction. *)
    (b = true /\ ∃ τ e i, p.2 = INSTR_Alloca τ e i).
  Proof.
    intros; rewrite /las_instr in H0.
    destruct_match; eauto. right. repeat eexists; done.
  Qed.

  (* Some more case analysis on when the instruction changes *)
  Lemma las_instr_Some_id_inv {T a o a0 id p b b'}:
    las_instr (T := T) a o a0 b' = (p, Some id, b) ->
    (o = Some id /\ a0 = p /\ b' = false /\
        ∃ id0 t nb align, a0 = (IId id0, INSTR_Alloca t nb align)) \/
    (o = Some id /\ a0 = p /\ b' = b) \/
    (o = Some id /\ b' = true) \/
     exists n t id t0 id2 volatile align,
       b' = true /\
       a = id2 /\
       a0 = (IVoid n, INSTR_Store volatile (t, ' id ') (t0, ' id2 ') align) /\
        p = (IVoid n, INSTR_Store volatile (t, ' id ') (t0, ' id2 ') align).
  Proof.
    intros; rewrite /las_instr in H0.
    destruct_match; eauto.
    - right; right; right; repeat eexists; done.
    - left; repeat (split; eauto).
  Qed.

  (* TODO: MOVE *)
  Lemma target_instr_local_read {x : LLVMAst.raw_id} {v : uvalue} {a i L Ψ}:
    ⊢ stack_tgt i -∗ ldomain_tgt i L -∗ [ x := v ]t i -∗
      ([ a := v ]t i -∗
        [ x := v ]t i -∗ ldomain_tgt i L -∗ stack_tgt i -∗ Ψ (Ret ())) -∗
      target_red (η := vir_handler) (<{ %(IId a) = (INSTR_Op (' x ')) }>) Ψ.
  Proof. Admitted. (* MOVE *)

  Lemma las_simulation_code a b A_t A_s :
    code_WF (blk_code b) ->
    ⊢ code_logrel
        local_bij
        alloca_bij
        (blk_code (las_block a None b))
        (blk_code b)
        ∅ A_t A_s.
  Proof.
    iIntros (?).
    (* Prepping the goal for induction. *)
    remember None; clear Heqo; cbn; remember (blk_code b); clear b Heqc; remember false.

    (* If an allocated location has been found, then we can get the points to.
       It holds trivially in the beginning because no location has been found,
        yet. *)
    iAssert (⌜b = true⌝ -∗
        ∀ id, ⌜o = Some id⌝ -∗
          ∀ i_s i_t L_s L_t, frame_src i_s L_s -∗ frame_tgt i_t L_t -∗
          ∃ ptr v_t v_s,
            dval_rel v_t v_s ∗ [ id := dvalue_to_uvalue v_t ]t i_t ∗ [ a := UVALUE_Addr (ptr,0)%Z ]s i_s ∗
            ptr ↦s v_s ∗ frame_tgt i_t L_t ∗ frame_src i_s L_s)%I as "H". { iIntros (?); subst; done. }
    clear Heqb.

    (* Induction on code block. *)
    iInduction c as [ | ] "IH" forall (o b A_t A_s) "H"; eauto; cbn.

    (* Trivial base case *)
    { iIntros (??) "CI". cbn. vsimp. rewrite instr_conv_ret. vsimp.
      vfinal. iExists ∅, ∅. by cbn. }

    (* Inductive case. *)
    rename a into promotable, o into stored_val, a0 into i, b into allocated.

    destruct (las_instr promotable stored_val i) eqn: Hlas; destruct p; cbn.
    iIntros (??) "CI".

    (* Current instruction. *)
    assert (Hlas_orig := Hlas).
    apply las_instr_inv in Hlas. destruct Hlas as [ Heq | (?&?&?&?&?&?&?&?&?&?&?&?) ].

    (* TODO: Factor out *)
    { (* CASE 0: Isntruction unchanged. *) inv Heq.
      rewrite !denote_code_cons; do 2 rewrite instr_conv_bind; Cut...
      invert_WF.

      (* FIXME (?): We need to case analyze on the alloca case here so that we can use the
         inductive hypothesis. *)
      destruct p; destructb; clear H1; rename i into id, i0 into i.

      (* Instructions are reflexive *)
      mono: iApply (instr_logrel_refl with "CI")... vsimp.
      iDestruct "HΦ" as (??) "HΦ".
      iSpecialize ("IH" $! WF_tl _ _ (nA_t ++ A_t) (nA_s ++ A_s)).

      mono: iApply "IH"; eauto...
      { iIntros (??) "H'"; iDestruct "H'" as (????) "H'".
        sfinal. iDestruct "H'" as (??) "H'".
        iExists (nA_t0 ++ nA_t), (nA_s0 ++ nA_s); rewrite !app_assoc; by iFrame. }

      apply las_instr_unchanged_inv in Hlas_orig.
      destruct Hlas_orig; last admit.

      iModIntro; iIntros (???????) "Hf Hs"; subst.
      iApply "H"; try done.
      (* TODO : say something more explicit about the [instr_refl] A_t A_s result. *)
      (* cbn in *; destruct_match; destructb; by (iIntros; iApply instr_logrel_refl). } *)
      admit. }

    rewrite !denote_code_cons. do 2 rewrite instr_conv_bind. Cut...

    match goal with
      | |- environments.envs_entails _ (sim_expr ?Φ _ _) => set (post := Φ)
    end.

    symmetry in H2, H3. subst. rename x5 into stored_val; rename x0 into τ, x1 into τ'.

    (* CASE 1: It was a load instruction from the promotable location that's been stored to;
        things changed. *)
    subst.
    iSpecialize ("H" $! eq_refl _ eq_refl).
    destruct_code_inv; destruct_local_inv; destruct_frame.
    iSpecialize ("H" $! _ _ _ _ with "Hfs Hft");
    iDestruct "H" as (???) "(#Hv & Ht & Hx2 & Hp & Hft & Hfs)".
    do 2 destruct_frame.

    (* Source step. *)
    iApply source_red_sim_expr.
    iApply (source_red_mono with "[CI HL AI Ht Hs_t Hd_t]"); cycle 1.
    { iApply (source_instr_load _ _ _ _ _ _ _ _ _ _ _
              (fun vx => ⌜vx = Ret tt⌝ ∗
              [ promotable := UVALUE_Addr (ptr, 0%Z) ]s i_s ∗
              [ x := v_s ̂ ]s i_s ∗
              ptr ↦s v_s ∗ ldomain_src i_s ({[x]} ∪ list_to_set args_s.*1) ∗ stack_src i_s)%I
              with "Hp Hx2 Hd_s Hs_s"); eauto.
      1-3: admit.
      iIntros "H1 Hv' Hp Hd Hs". by iFrame. }
    iIntros (?) "H"; iDestruct "H" as (?) "(Hx2 & Hx & Hptr & Hd_s & Hs_s)"; subst.

    (* Target step. *)
    iApply target_red_sim_expr.
    iApply (target_red_mono with "[CI HL AI Hx Hptr Hx2 Hs_s Hd_s]"); cycle 1.
    { iApply (target_instr_local_read with "Hs_t Hd_t Ht"); iIntros; iFrame. admit. }
    admit.

  (* assert (code_WF c). (* Well-formedness *) *)
  (* { apply code_WF_cons_inv in H0; destruct H0; eauto. } *)

  (*   iSpecialize ("IH" $! H1). *)

  (*   iApply "IH"; iModIntro; iIntros (???????) "Hft Hfs"; subst. *)
  (*   apply las_instr_Some_id_inv in Hlas. *)
  (*   destruct Hlas as [ (?&?&?&?) | [ (?&?&?) | [ (?&?) | (?&?&?&?&?&?&?&?&?) ] ] ]; subst. *)

  (*   { (* (2) Alloca.  *) *)
  (*     (* FIXME: This is not quite right; we don't get inherited stuff from the previous instr. *) *)
  (*     admit. } *)

  (*   { iSpecialize ("H" $! eq_refl _ eq_refl). iApply ("H" with "Hft Hfs"). } *)
  (*   { iSpecialize ("H" $! eq_refl _ eq_refl). iApply ("H" with "Hft Hfs"). } *)

  (*   (* (3) Store. *) *)
  (*   { admit. } *)
  (*   (* Extended local environment, like the alloca environment. *) *)
  Admitted.

  Lemma las_simulation_term a b:
    term_WF (blk_term b) ->
    ⊢ term_logrel
        local_bij
        alloca_bij
        (blk_term (las_block a None b))
        (blk_term b)
        ∅.
  Proof.
    iIntros (?); iApply term_logrel_refl.
  Qed.

  Lemma las_simulation_phis a be b A_t A_s :
    (blk_phis b).*1 ## (a :: nil) ->
    ⊢ phis_logrel
        local_bij alloca_bij
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
    iApply expr_logrel_refl.
  Qed.

  Lemma las_simulation_cfg (f : cfg dtyp) a i A_t A_s:
    cfg_WF f ->
    (* The promotable location is not a local id that appears in the phi nodes. *)
    (∀ b, b ∈ blks f -> ((blk_phis b).*1 ## a :: nil)) ->
    (* Promotable location is found. *)
    find_promotable_alloca f = Some (IId a, i) ->
    ⊢ cfg_logrel local_bij alloca_bij (las f) f ∅ A_t A_s.
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
    { iApply las_simulation_phis; set_solver. }

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
    iApply (fun_compat local_bij);
      eauto; cycle 3.

    (* Well-formedness is maintained by the [las] transformation. *)
    { eapply las_fun_WF in fun_WF_src.
      by rewrite /las_fun /las Promotable_found in fun_WF_src. }

    (* State the invariant first. *)
    { cbn; iIntros (??????) "Hlt Hls Hargs". iFrame.
      (* iApply local_bij_implies_local_bij_except_promotable; *)
      (*   rewrite /local_bij; iFrame. *)
      rewrite -H0; done. }

    (* CFG's are related to each other. *)
    iIntros (??); cbn.
    iPoseProof (las_simulation_cfg (df_instrs f)) as "H";
      eauto; last first.
    { by rewrite /las Promotable_found. }
    { eapply SSA_fun_implies_promotable_phi_disjoint; eauto. }
    apply fun_WF_inv in fun_WF_src; destruct fun_WF_src; eauto.
  Qed.

  Theorem las_correct (c : function) :
    fun_is_SSA c ->
    ctx_ref (las_fun c) c.
  Proof. Abort. (* TODO *)

End las_example_proof.
