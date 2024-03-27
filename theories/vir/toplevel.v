
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

(* Definition handle_global {E} `{FailureE -< E} : (GlobalE k v) ~> stateT map (itree E) := *)
(*   fun _ e env => *)
(*     match e with *)
(*     | GlobalWrite k v => ret (<[k:= v]> env, tt) *)
(*     | GlobalRead k => *)
(*       match env !! k with *)
(*       | Some v => Ret (env, v) *)
(*       | None => raise ("Could not look up global id " ++ to_string k) *)
(*       end *)
(*     end. *)


(* Definition initialize_global_prog (g:global dtyp) : vir_state := *)
(*   let dt := (g_typ g) in *)
(*   a <- trigger (GlobalRead (g_ident g));; *)
(*   uv <- match (g_exp g) with *)
(*        | None => Monad.ret (UVALUE_Undef dt) *)
(*        | Some e =>  denote_exp (Some dt) e *)
(*        end ;; *)
(*   dv <- concretize_or_pick uv True ;; *)
(*   trigger (Store a dv). *)

(* Definition initialize_globals_prog (gs:list (global dtyp)): itree exp_E unit := *)
(*   map_monad_ initialize_global gs. *)

(* Definition allocate_global (g:global dtyp) : itree L0 unit := *)
(*   ITree.bind (trigger (Alloca (g_typ g))) *)
(*   (fun v => trigger (GlobalWrite (g_ident g) v)). *)

(* Definition allocate_globals (gs:list (global dtyp)) : itree L0 unit := *)
(*   map_monad_ allocate_global gs. *)

(* (* Returns `true` only if both function are named and have *)
(*      the same name. *)
(*  *) *)
(* Definition function_name_eq (a b:function_id) : bool := *)
(*   match a, b with *)
(*   | Name aname, Name bname => String.eqb aname bname *)
(*   | _, _ => false *)
(*   end. *)

(* TODO: MOVE *)
Definition vir_mem :=
  ((gmap Z logical_block  * gset Z) * frame_stack)%type.

Definition vir_locals :=
  (local_env * lstack)%type.

(* Assumes that τ is not void *)
Definition allocate_non_void τ : vir_mem -> (vir_mem * addr) :=
  fun m =>
    let new_block := make_empty_logical_block τ in
    let key       := next_logical_key m in
    let m         := add_logical_block key new_block m in
    (add_to_frame m key, (key,0)%Z).

Definition global_write (id : global_id) (v : dvalue) (g : vir.globals) : vir.globals :=
  <[id := v]> g.

Definition fmap_global {A} (f : vir.globals -> A) : vir_state -> _ :=
  fun '(g, l, m) => (f g, l, m).

Definition fmap_local {A} (f : vir_locals -> A) : vir_state -> _ :=
  fun '(g, l, m) => (g, f l, m).

Definition fmap_mem {A} (f : vir_mem -> A) : vir_state -> _ :=
  fun '(g, l, m) => (g, l, f m).

Definition update_global (f : vir.globals -> vir.globals) : vir_state -> vir_state :=
  fun '(g, l, m) => (f g, l, m).

Definition update_local (f : vir_locals -> vir_locals) : vir_state -> vir_state :=
  fun '(g, l, m) => (g, f l, m).

Definition update_mem (f : vir_mem -> vir_mem) : vir_state -> vir_state :=
  fun '(g, l, m) => (g, l, f m).

Definition allocate_declaration_prog (d:declaration dtyp) (σ : vir_state) : vir_state :=
  match List.find (fun x => function_name_eq (dc_name d) (dc_name x))
          IntrinsicsDefinitions.defined_intrinsics_decls with
  | Some _ => σ
  | None =>
      let '(g, l, (m, v)) := fmap_mem (allocate_non_void DTYPE_Pointer) σ in
      let g := global_write (dc_name d) (DVALUE_Addr v) g in
      (g, l, m)
  end.

Definition allocate_declarations_prog
  (ds:list (declaration dtyp)) (σ : vir_state) : vir_state :=
  List.fold_left (fun acc x => allocate_declaration_prog x acc) ds σ.

(* (* TODO : Assume [g_typ g] is not void *) *)
(* Definition allocate_global_prog (gl : global dtyp) (σ : vir_state) : vir_state := *)
(*    let '(g, l, (m, v)) := *)
(*      fmap_mem (allocate_non_void (g_typ gl)) σ *)
(*    in *)
(*    let g := global_write (g_ident gl) (DVALUE_Addr v) g in *)
(*    (g, l, m). *)

(* Definition allocate_globals_prog *)
(*   (gs:list (global dtyp)) (σ : vir_state) : vir_state := *)
(*   List.fold_left (fun acc x => allocate_global_prog x acc) gs σ. *)

(* Definition build_global_environment (CFG : CFG.mcfg dtyp) : itree L0 unit := *)
(*   ITree.bind (allocate_declarations ((m_declarations CFG) ++ (List.map (df_prototype) (m_definitions CFG)))) *)
(*   (fun _ => ITree.bind (allocate_globals (m_globals CFG)) *)
(*   (fun _ => translate exp_to_L0 (initialize_globals (m_globals CFG)))). *)

(* Definition denote_vellvm *)
(*            (ret_typ : dtyp) *)
(*            (entry : string) *)
(*            (args : list uvalue) *)
(*            (mcfg : CFG.mcfg dtyp) : itree L0 uvalue := *)
(*   ITree.bind (build_global_environment mcfg) *)
(*   (fun _=> *)
(*    ITree.bind (Util.map_monad address_one_function (m_definitions mcfg)) *)
(*     (fun defns => *)
(*        ITree.bind (trigger (GlobalRead (Name entry))) *)
(*           (fun addr => denote_mcfg defns ret_typ addr args))). *)

(* Import ListNotations. *)

(* Definition main_args := *)
(*   DV.UVALUE_I64 (DynamicValues.Int64.zero) :: *)
(*    DV.UVALUE_Addr (Addr.null) :: nil. *)

(* Definition denote_vellvm_main (mcfg : CFG.mcfg dtyp) : itree L0 uvalue := *)
(*   denote_vellvm (DTYPE_I (32)%N) "main" main_args mcfg. *)

(* (** *Properties about the top-level denotation *) *)
(* Section toplevel. *)

(*   Context `(sheapGS Σ, checkedoutGS Σ, heapbijGS Σ). *)

(*   Lemma sim_allocate_declaration d_t d_s g_t g_s: *)
(*     (* The declarations have the same names *) *)
(*     dc_name d_t = dc_name d_s -> *)
(*     (* The declarations are not intrinsics *) *)
(*     List.find (fun x => function_name_eq (dc_name d_t) (dc_name x)) *)
(*       IntrinsicsDefinitions.defined_intrinsics_decls = None -> *)
(*     ⊢ allocate_declaration d_t ⪯ allocate_declaration d_s *)
(*       [[ fun x y => *)
(*            ∃ l_t l_s, *)
(*              (* Allocated a new pointer *) *)
(*              l_t ↦t [ make_empty_logical_block DTYPE_Pointer ] ∗ *)
(*              l_s ↦s [ make_empty_logical_block DTYPE_Pointer ] ∗ *)
(*              (* Globals: monotonically increasing state that agrees with everything *) *)
(*              target_globals (<[dc_name d_t := DVALUE_Addr (l_t, 0)%Z ]> g_t) ∗ *)
(*              source_globals (<[dc_name d_s := DVALUE_Addr (l_s, 0)%Z ]> g_s) *)
(*       ]]. *)
(*   Proof. *)

(*   Lemma sim_allocate_declarations ds_t ds_s Φ : *)
(*     length ds_t = length ds_s -> *)
(*     ⊢ allocate_declarations ds_t ⪯ allocate_declarations ds_s *)
(*       [[  ]]. *)
(*   Proof. *)
(*     induction ds_t. *)
(*     (* nil case *) *)
(*     {  *)
    
(*   Lemma build_global_environment_sim C_t C_s Φ : *)
(*     ⊢ build_global_environment C_t ⪯ build_global_environment C_s [[ Φ ]]. *)
(*   Proof. *)
(*     rewrite /build_global_environment. *)

(*   Admitted. *)

End toplevel.

(* ------------------------------------------------------------------------ *)
