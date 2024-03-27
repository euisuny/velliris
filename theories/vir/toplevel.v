
From velliris.logic Require Import satisfiable.
From velliris.program_logic Require Import program_logic.
From velliris.vir Require Import
  vir val_rel heapbij adequacy spec globalbij logical_relations fundamental
  contextual_mcfg.

From Vellvm Require Import Syntax.DynamicTypes Handlers Syntax.LLVMAst
  Semantics.InterpretationStack Utils.Util.

From ITree Require Import ITree Eq.

Require Import LLVMEvents.
Require Import CFG.

(* ------------------------------------------------------------------------ *)

(** *Top-level denotation *)
(* Note: This definition is temporarily living here as a duplicate of
 [Semantics/TopLevel.v] from Vellvm due to universe inconsistencies. *)

Definition initialize_global (g:global dtyp) : itree exp_E unit :=
  let dt := (g_typ g) in
  a <- trigger (GlobalRead (g_ident g));;
  uv <- match (g_exp g) with
       | None => Monad.ret (UVALUE_Undef dt)
       | Some e =>  denote_exp (Some dt) e
       end ;;
  dv <- concretize_or_pick uv True ;;
  trigger (Store a dv).

Definition initialize_globals (gs:list (global dtyp)): itree exp_E unit :=
  map_monad_ initialize_global gs.

Definition allocate_global (g:global dtyp) : itree L0 unit :=
  ITree.bind (trigger (Alloca (g_typ g)))
  (fun v => trigger (GlobalWrite (g_ident g) v)).

Definition allocate_globals (gs:list (global dtyp)) : itree L0 unit :=
  map_monad_ allocate_global gs.

(* Returns `true` only if both function are named and have
     the same name.
 *)
Definition function_name_eq (a b:function_id) : bool :=
  match a, b with
  | Name aname, Name bname => String.eqb aname bname
  | _, _ => false
  end.

Definition allocate_declaration (d:declaration dtyp) : itree L0 unit :=
  match List.find (fun x => function_name_eq (dc_name d) (dc_name x))
          IntrinsicsDefinitions.defined_intrinsics_decls with
  | Some _ => Ret tt (* Don't allocate pointers for LLVM intrinsics declarations *)
  | None =>
    ITree.bind (trigger (Alloca DTYPE_Pointer))
    (fun v => trigger (GlobalWrite (dc_name d) v))
  end.

Definition allocate_declarations (ds:list (declaration dtyp)) : itree L0 unit :=
  map_monad_ allocate_declaration ds.

Definition build_global_environment (CFG : CFG.mcfg dtyp) : itree L0 unit :=
  ITree.bind (allocate_declarations ((m_declarations CFG) ++ (List.map (df_prototype) (m_definitions CFG))))
  (fun _ => ITree.bind (allocate_globals (m_globals CFG))
  (fun _ => translate exp_to_L0 (initialize_globals (m_globals CFG)))).

Definition denote_vellvm
           (ret_typ : dtyp)
           (entry : string)
           (args : list uvalue)
           (mcfg : CFG.mcfg dtyp) : itree L0 uvalue :=
  ITree.bind (build_global_environment mcfg)
  (fun _=>
   ITree.bind (Util.map_monad address_one_function (m_definitions mcfg))
    (fun defns =>
       ITree.bind (trigger (GlobalRead (Name entry)))
          (fun addr => denote_mcfg defns ret_typ addr args))).

Import ListNotations.

Definition main_args :=
  DV.UVALUE_I64 (DynamicValues.Int64.zero) ::
   DV.UVALUE_Addr (Addr.null) :: nil.

Definition denote_vellvm_main (mcfg : CFG.mcfg dtyp) : itree L0 uvalue :=
  denote_vellvm (DTYPE_I (32)%N) "main" main_args mcfg.

(* ------------------------------------------------------------------------ *)

(** Properties about the top-level denotation *)
Section toplevel.

  Context `(sheapGS Σ, checkedoutGS Σ, heapbijGS Σ).

  Lemma denote_vellvm_main_global C_t C_s Φ :
    ⊢ denote_vellvm_main C_t ⪯ denote_vellvm_main C_s [[ Φ ]].
  Proof.
    rewrite /denote_vellvm_main /denote_vellvm.

End toplevel.

(* ------------------------------------------------------------------------ *)
