From iris.prelude Require Import options.

From Equations Require Import Equations.

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
  vir_util.

Import DenoteTactics.
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
  Fixpoint las_block {T} (b : code T) (a : raw_id) (v : option raw_id)
    : code T :=
    match b with
    | nil => nil
    | x :: tl =>
        match x with
        (* A load instruction from a stored [raw_id] that hasn't been modified *)
        | (id, INSTR_Load _ _ (_, EXP_Ident (ID_Local ptr)) _) =>
          if decide (a = ptr) then
            match v with
              | Some c =>
                  (id, INSTR_Op (EXP_Ident (ID_Local c))) ::
                  las_block tl a v
              | None => x :: las_block tl a v
            end
          else x :: las_block tl a v
        (* A store instruction to the promoted local identifier *)
        | (id, INSTR_Store _
                  (* TODO Warning! this is enforced by the syntactic
                      condition in the [TODO] above *)
                  (_, EXP_Ident (ID_Local v'))
                  (_, EXP_Ident (ID_Local ptr)) _) =>
            if decide (a = ptr) then
              x :: las_block tl a (Some v')
            else
              x :: las_block tl a v
        | x => x :: las_block tl a v
        end
    end.

  (* Apply the [las] optimization over an open control flow graph. *)
  Definition las_ocfg {T} (o : ocfg T) a : ocfg T :=
    List.map (fun x =>
      mk_block
        (blk_id x)
        (blk_phis x)
        (las_block (blk_code x) a None)
        (blk_term x)
        (blk_comments x))
      o.

  Definition raw_id_not_in_texp {T} (l : list (texp T)) (i : raw_id) : bool :=
    forallb
      (fun x => match x with
             | (_, EXP_Ident (ID_Local i')) => bool_decide (i = i')
             | _ => false
             end) l.

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

  Definition las_fun (f : definition dtyp (cfg dtyp)) : definition _ _ :=
    {| df_prototype := df_prototype f;
       df_args := df_args f;
       df_instrs := las (df_instrs f) |}.

End las_example.

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
Compute (las_block code1 (Name "a")).

(* ------------------------------------------------------------------- *)
(* Specification of the Load-after-store optimization. *)

Notation function := (definition dtyp (cfg dtyp)).

(* TODO Get this definition from [contextual]. *)
Axiom ctx_ref : function -> function -> Prop.
Axiom fun_is_SSA : function -> Prop.
Axiom ocfg_is_SSA : ocfg dtyp -> Prop.
Axiom code_is_SSA : code dtyp -> Prop.

From velliris Require Import vir.logical_relations.

From velliris.program_logic Require Import program_logic.

Section las_example_proof.

Context `{vellirisGS Σ}.

Definition ocfg_post_inv C i_t i_s A_t A_s : iPropI Σ :=
  (∃ (args_t args_s : local_env),
      ldomain_tgt i_t (list_to_set args_t.*1) ∗
      ldomain_src i_s (list_to_set args_s.*1) ∗
      stack_tgt i_t ∗ stack_src i_s ∗
      frame_WF i_t i_s ∗
      ([∗ list] '(l_t, v_t) ∈ args_t, [ l_t := v_t ]t i_t) ∗
      ([∗ list] '(l_s, v_s) ∈ args_s, [ l_s := v_s ]s i_s) ∗
  checkout C ∗
  alloca_tgt i_t (list_to_set A_t : gset _) ∗
  alloca_src i_s (list_to_set A_s : gset _) ∗
  ⌜NoDup A_t⌝ ∗ ⌜NoDup A_s⌝)%I.

(* TODO : make [logical relations] take in an invariant [I] *)

Definition term_logrel ϒ_t ϒ_s I : iPropI Σ :=
(⌜term_WF ϒ_t⌝ -∗
 ⌜term_WF ϒ_s⌝ -∗
    I -∗
    exp_conv (denote_terminator ϒ_t) ⪯
    exp_conv (denote_terminator ϒ_s)
    [{ (r_t, r_s), I ∗
                    match r_t, r_s with
                    | inl b_t, inl b_s => ⌜b_t = b_s⌝
                    | inr v_t, inr v_s => uval_rel v_t v_s
                    | _, _ => False
                    end}])%I.

(* Factor out for use in general optimizations *)
Lemma simulation_ocfg (a : raw_id) Φ I cfg_t cfg_s i_t i_s A_t A_s b1 b2 :
  ⊢ (code_inv ∅ i_t i_s A_t A_s -∗ I) -∗
    (I -∗ ∃ A_t' A_s',
            ocfg_post_inv ∅ i_t i_s A_t' A_s') -∗
    (* Related terminators *)
    (∀ (i : nat) b_t b_s,
      ⌜cfg_t !! i = Some b_t⌝ -∗
      ⌜cfg_s !! i = Some b_s⌝ -∗
      term_logrel (blk_term b_t) (blk_term b_s) I) -∗
    (* Related instructions *)
    (∀ (i : nat) b_t b_s,
      ⌜cfg_t !! i = Some b_t⌝ -∗
      ⌜cfg_s !! i = Some b_s⌝ -∗
      I -∗
      instr_conv (denote_code (blk_code b_t)) ⪯
      instr_conv (denote_code (blk_code b_s))
      [{ (r_t, r_s), I ∗ Φ r_t r_s }]) -∗
   (* TODO: state [phi_logrel] related for a weakened [phi_logrel] *)
   (* Weaken the postcondition for [ocfg_logrel] *)
    ocfg_logrel cfg_t cfg_s ∅ A_t A_s b1 b2.
Proof. Admitted.

Lemma las_simulation_ocfg
  (f : ocfg dtyp) a A_t A_s b1 b2 :
  ocfg_is_SSA f ->
  promotable_ocfg f a ->
  ⊢ ocfg_logrel (las_ocfg f a) f ∅ A_t A_s b1 b2.
Proof.
Admitted.

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
