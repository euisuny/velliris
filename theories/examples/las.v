From iris.prelude Require Import options.

From Vellvm Require Import
  Syntax.DynamicTypes
  Handlers
  Syntax.LLVMAst
  Semantics.InterpretationStack.

From velliris.vir Require Import
  spec
  instr_laws
  bij_laws
  tactics
  fundamental_exp
  fundamental
  vir_util.

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
Axiom code_is_SSA : code dtyp -> Prop.

From velliris.program_logic Require Import program_logic.

From velliris.vir Require Import logical_relations tactics.

Section las_example_proof.

Context `{vellirisGS Σ}.

Lemma block_WF_las a0 a s:
  Is_true (block_WF a) ->
  Is_true (block_WF (las_block a0 s a)).
Proof. Admitted.

Lemma code_WF_las a0 a s:
  Is_true (code_WF a0) ->
  Is_true (code_WF (las_code a0 a s)).
Proof.
  intros.
  revert s.
  induction a0; eauto; cbn -[instr_WF] in *; intros.
  destruct a0; eauto. destructb; cbn.
  apply forallb_True in H1.
  destruct i0; eauto; cbn; destructb; eauto;
  apply forallb_True in H1.
  { eapply IHa0; eauto. }
  { apply andb_prop_intro; split; eauto. }
  { apply andb_prop_intro; split; eauto. }
  { destruct ptr, e; cbn; eauto.
    destruct id; cbn; eauto. destruct_if_goal; cbn; eauto.
    destruct s; cbn; eauto. }
  { destruct val, e; cbn; eauto.
    destruct id; cbn; eauto.
    destruct ptr, e; cbn; eauto.
    destruct id0; destruct_if_goal; cbn; eauto. }
Qed.

(* Well-formedness of ocfg is preserved in the LAS transformation. *)
Lemma ocfg_WF_las f a:
  Is_true (ocfg_WF f) ->
  Is_true (ocfg_WF (las_ocfg f a)).
Proof.
  intros. induction f; eauto.
  (* Why is [is_true] being weird here.. *)
  pose proof (ocfg_WF_cons_inv _ _ H0) as H0'. destruct H0'.
  cbn. eapply andb_prop_intro; split; auto.
  apply andb_prop_elim in H1; destruct H1.
  eapply andb_prop_intro; split; auto.
  cbn -[code_WF]. apply code_WF_las; eauto.
Qed.

(* TODO: Instantiate [ocfg_is_SSA]. *)
Lemma ocfg_is_SSA_cons_inv a0 f :
  ocfg_is_SSA (a0 :: f) ->
  ocfg_is_SSA f.
Proof. Admitted.

Lemma promotable_ocfg_cons_inv {T} a0 (f : _ T) a:
  Is_true (promotable_ocfg (a0 :: f) a) ->
  Is_true (promotable_ocfg f a).
Proof.
  rewrite /promotable_ocfg; cbn; intros.
  destructb. apply forallb_True in H1; auto.
Qed.

Lemma block_compat_relaxed
  (a : raw_id) Φ I A_t A_s b_t b_s bid L L_t L_s:
  Is_true (block_WF b_t) ->
  Is_true (block_WF b_s) ->
  ⊢ (∀ i_t i_s, code_inv L ∅ i_t i_s A_t A_s L_t L_s -∗ I) -∗
    (∀ i_t i_s, I -∗ code_inv_post L ∅ i_t i_s A_t A_s L_t L_s) -∗
    (* Related phi nodes *)
    (phis_logrel L
        (denote_phis bid (blk_phis b_t))
        (denote_phis bid (blk_phis b_s))
       ∅ A_t A_s L_t L_s) -∗
    (* Related terminators *)
    (term_logrel L (blk_term b_t) (blk_term b_s) ∅ L_t L_s) -∗
    (* Related instructions *)
    (I -∗
      instr_conv (denote_code (blk_code b_t)) ⪯
      instr_conv (denote_code (blk_code b_s))
      [{ (r_t, r_s), I ∗ Φ r_t r_s }]) -∗
   (* TODO: state [phi_logrel] related for a weakened [phi_logrel] *)
   (* Weaken the postcondition for [ocfg_logrel] *)
   block_logrel L b_t b_s bid ∅ A_t A_s L_t L_s.
Proof with vsimp.
  iIntros (WF_b WF_b') "Hinv I HΦ Hterm Hinst".
  iIntros (??) "CI".
  cbn -[denote_phis]...
  setoid_rewrite instr_conv_bind at 3.
  Cut...

  (* Phis *)
  mono: (iApply ("HΦ" with "CI")) with "[Hinv I Hterm Hinst]"...
  setoid_rewrite instr_conv_bind...
  rewrite <- !bind_bind. Cut...

  (* Code block *)
  iSpecialize ("Hinv" with "HΦ").
  iSpecialize ("Hinst" with "Hinv").
  mono: iApply "Hinst" with "[I Hterm]"...

  iDestruct "HΦ" as "(HI & HΦ)".
  iSpecialize ("I" with "HI"); iDestruct "I" as (??) "HI".

  (* Well-formedness of block *)
  apply andb_prop_elim in WF_b, WF_b';
    destruct WF_b, WF_b'.

  (* Terminator *)
  iSpecialize ("Hterm" with "[] [] HI"); eauto.

  mono: iApply "Hterm" with "[HΦ]"...

  iIntros (??) "H".
  iDestruct "H" as (????) "(Hi & H)".
  iExists _,_. rewrite H4 H5.
  do 2 (iSplitL ""; [ done | ]).
  iFrame "H".
  iModIntro. by iExists _, _.
Qed.

(* The [las] algorithm does not change the phi nodes. *)
Lemma las_phi_stable {T} a b :
  blk_phis (las_block a None b) = blk_phis (T := T) b.
Proof.
  eauto.
Qed.

From velliris.vir Require Import fundamental_exp_relaxed.

Theorem phi_logrel_refl bid id ϕ C A_t A_s L_t L_s:
  ⊢ (phi_logrel expr_inv (denote_phi bid (id, ϕ)) (denote_phi bid (id, ϕ)) C A_t A_s L_t L_s)%I.
Proof with vsimp.
  iApply phi_compat; destruct ϕ.
  { iIntros (????); iApply refl_inv_mono. }
  destruct (Util.assoc bid args); try done.
  iApply expr_logrel_relaxed_refl.
Qed.


Theorem phis_logrel_refl C bid (Φ : list (local_id * phi dtyp)) A_t A_s a:
  (⊢ phis_logrel refl_inv (denote_phis bid Φ) (denote_phis bid Φ) C A_t A_s [a] [a])%I.
Proof with vsimp.
  iApply phis_compat.
  { iIntros (????); iApply refl_inv_mono. }
  iInduction Φ as [ | ] "IH"; first done.
  cbn; iSplitL; [ destruct a; iApply phi_logrel_refl | done ].
Qed.


Lemma las_block_sim A_t A_s be b a:
  Is_true (block_WF b) ->
  ⊢ block_logrel refl_inv
      (las_block a None b) b be ∅ A_t A_s [a] [a].
Proof.
  iIntros (WF).
  iApply block_compat_relaxed; eauto.
  { by eapply block_WF_las. }

  (* Invariant *)
  { iIntros (??) "CI". admit. }

  (* Invariant *)
  { admit. }

  (* Phi compat *)
  { rewrite las_phi_stable.
    iApply phis_compat.
    { iIntros (????); iApply refl_inv_mono. }
    


Admitted.


Lemma las_simulation_ocfg
  (f : ocfg dtyp) a A_t A_s b1 b2 :
  Is_true (ocfg_WF f) ->
  ocfg_is_SSA f ->
  Is_true (promotable_ocfg f a) ->
  ⊢ ocfg_logrel (fun _ _ => True)
    (las_ocfg f a) f ∅ A_t A_s b1 b2 nil nil.
Proof.
  iIntros (???).
  iApply ocfg_compat; first (iIntros; done); eauto.
  { eapply ocfg_WF_las in H0; eauto. }
  iModIntro.
  iInduction f as [ | ] "IH"; eauto.
  apply ocfg_WF_cons_inv in H0. destruct H0.
  cbn. iSplitL "".
  { iSplitL ""; first done.
    iIntros (???); iApply las_block_sim; eauto. }
  { iApply "IH"; eauto.
    { iPureIntro; eapply ocfg_is_SSA_cons_inv; eauto. }
    { iPureIntro; eapply promotable_ocfg_cons_inv; eauto. } }
Qed.

Lemma las_simulation (f : function) :
  fun_is_SSA f ->
  ⊢ fun_logrel (las_fun f) f ∅.
Proof. Admitted.

Theorem las_correct (c : function) :
  fun_is_SSA c ->
  ctx_ref (las_fun c) c.
Proof. Admitted.

(* TODO: Prove it *)

End las_example_proof.
