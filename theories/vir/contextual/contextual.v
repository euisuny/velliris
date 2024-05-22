From iris.prelude Require Import options.

From velliris.logic Require Import satisfiable.
From velliris.vir Require Import lang logrel.

From velliris.vir.soundness Require Import adequacy.

Set Default Proof Using "Type*".

(** *Initial state *)

Definition empty_vir_state : vir_state :=
  {| vglobal := ∅;
     vlocal := (nil, nil);
     vmem := (∅, ∅, Mem.Singleton nil) |}.

(* Returns `true` only if both function are named and have
     the same name. *)
Definition function_name_eq (a b:function_id) : bool :=
  match a, b with
  | Name aname, Name bname => String.eqb aname bname
  | _, _ => false
  end.

(* Initial state: all function declaration names are allocated in global
   environment, and otherwise the state is empty *)
Definition allocate_declaration_prog (d:declaration dtyp) (σ : vir_state) : vir_state :=
  match List.find (fun x => function_name_eq (dc_name d) (dc_name x))
          IntrinsicsDefinitions.defined_intrinsics_decls with
  | Some _ => σ
  | None =>
      let '(mem, v) := vir_util.allocate_non_void DTYPE_Pointer (vmem σ) in
      let σ := update_mem mem σ in
      apply_global (fun g => <[ dc_name d := DVALUE_Addr v]> g) σ
  end.

Definition allocate_declarations_prog
  (ds:list (declaration dtyp)) (σ : vir_state) : vir_state :=
  List.fold_left (fun acc x => allocate_declaration_prog x acc) ds σ.

Definition init_state ds := allocate_declarations_prog ds empty_vir_state.

(** *Whole-program refinement *)
Section prog_ref.

  Context (ds : list (declaration dtyp)) (main : Addr.addr).

  Definition init_mem : vir.logical_memory :=
    ({[main.1 := dvalue_to_block DVALUE_None;
      Addr.null.1 := dvalue_to_block DVALUE_None]},
    {[main.1; Addr.null.1]}, Mem.Singleton [main.1; Addr.null.1]).

  (* If the initial states are related by some relation, and the expressions
     are well formed (i.e. the source program does not "go wrong" and the
     expressions are closed after denotation), then the resulting programs
     are observationally equivalent to each other using [eutt]. *)
  Definition prog_ref (e_t e_s : expr vir_lang uvalue) :=
    let σ :=
      {| vglobal := vglobal (init_state ds);
         vlocal := (∅, ∅); vmem := init_mem |} in
    well_formed (⟦ e_t ⟧ σ) (⟦ e_s ⟧ σ) ->
    eutt obs_val_res (⟦ e_t ⟧ σ) (⟦ e_s ⟧ σ).

End prog_ref.

Import CFG.

(* A context is a mutually recursive control flow graph [mcfg]. *)
Notation context := (CFG.mcfg dtyp).

(* Well-formedness over contexts *)
Definition ctx_wf (C : context) :=
  let funs := CFG.m_definitions C in
  (* The context has the same definitions *)
  (length (CFG.m_declarations C) = length (CFG.m_definitions C)) /\
  (* There are no duplicate names in the context *)
  NoDup (CFG_names C) /\
  (* All the functions declared are well-formed *)
  Forall fun_WF funs /\
  (* The attributes list is empty for each function declaration *)
  (* TODO : Do we want something a little more generic here?
     This is the strongest statement that would follow automatically as a
     consequence of the fundamental theorem. *)
  Forall (fun x => dc_attrs x = nil) (CFG.m_declarations C)
.

(** *Top-level Contextual Refinement *)

Section CR_definition.

  Context (Σ : gFunctors).
  Context (ret_typ : dtyp) (main : Addr.addr) (args : list uvalue)
          (I : vir_state -> vir_state -> Prop).

  (* The context takes a function (with its declaration and definition) as its
     hole; we can extend the list of declarations and definitions with the hole. *)
  Definition fill_mcfg_defs (C : context)
    (e : declaration dtyp * definition dtyp (CFG.cfg dtyp)) :=
    {| m_name := m_name C;
      m_target := m_target C;
      m_datalayout := m_datalayout C;
      m_type_defs := m_type_defs C;
      m_globals := m_globals C;
      m_declarations := e.1 :: m_declarations C;
      m_definitions := e.2 :: m_definitions C
    |}.

  (* Filling the context involves (1) extending the function declaration map and
    (2) restating the denotation of mutually-recursive control flow graps using
        [denote_mcfg]. *)
  Definition fill_ctx (C : context) e :=
    Monad.bind (mcfg_definitions (fill_mcfg_defs C e))
        (fun defs => denote_mcfg defs ret_typ (DVALUE_Addr main) args).

  (* Contextual refinement. *)
  Definition ctx_ref e_t e_s: Prop :=
    forall (C : CFG.mcfg dtyp),
      (* The context and function needs to be well-formed *)
      ctx_wf C ->
      Addr.null.1 <> main.1 ->
      (* All the attributes are nil *)
      (Forall (fun x => dc_attrs x = nil) (map df_prototype (m_definitions C))) ->
      (* Implies whole-program refinement *)
      prog_ref (m_declarations C) main (fill_ctx C e_t) (fill_ctx C e_s).

End CR_definition.

From Equations Require Import Equations.

Section contextual_refinement.

  Context `{!vellirisGS Σ}.

  Definition function_meets_spec attr f_t f_s C :=
    ∀ i_t i_s args_t args_s,
     ⌜attribute_spec attr C args_t args_s⌝ -∗
     ⌜length i_s > 0 -> length i_t > 0⌝ -∗
     stack_tgt i_t -∗
     stack_src i_s -∗
     val_rel.Forall2 uval_rel args_t args_s -∗
     checkout C -∗
     L0'expr_conv (denote_function f_t args_t) ⪯ L0'expr_conv (denote_function f_s args_s)
     ⦉ fun v_t v_s =>
         ∃ r_t r_s, ⌜v_t = Ret r_t⌝ ∗ ⌜v_s = Ret r_s⌝ ∗
             stack_tgt i_t ∗ stack_src i_s ∗ checkout C ∗ uval_rel r_t r_s ⦊.

  (** *contextual refinement *)
  Theorem contextual_refinement e_t e_s main decl:
    function_meets_spec f_t f_s C -∗
    fun_logrel e_t e_s C -∗
    ctx_ref DTYPE_Void main [] (decl, e_t) (decl, e_s).
  Proof.
    iIntros (Hsat C Hwf Hneq Hattr HWF);
      eapply adequacy; eauto; clear HWF.
    Unshelve.
    rewrite /ctx_ref.

Admitted.

End contextual_refinement.
