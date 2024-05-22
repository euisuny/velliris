(** *Specification of attributes and events. *)

From Coq Require Import Program.Equality.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export ghost_var.

From velliris.program_logic Require Import program_logic.
From velliris.vir Require Export vir vir_state heapbij val_rel.

From Vellvm.Semantics Require Import InterpretationStack LLVMEvents.
From Vellvm Require Import Syntax.LLVMAst Handlers.Handlers.

From Equations Require Import Equations.

Set Default Proof Using "Type*".

Open Scope Z_scope.

Notation "# l" := (DVALUE_Addr (to_addr l)) (at level 30).
Notation "d  ̂" := (dvalue_to_uvalue d) (at level 40).

Definition HasAttr : fn_attr -> list fn_attr -> bool :=
  fun attr l => 
    match l with
    | nil => false
    | l => 
      foldl (fun p b => 
        p || (Coqlib.proj_sumbool (decide (b = attr)))) false l
    end.

(** *Attribute specifications *)
Section spec.
  Context Σ `{!vellirisGS Σ}.

  Definition state_lookup (state : language.state vir_lang) (a : Z) v : iProp Σ :=
    let h := (vir_heap state.(vmem)) in
    ⌜h !! a = v⌝.

  Variant attr_case : Type :=
  | ARG_READ
  (* | WRITEONLY *)
  (* | NOFREE *)
  | ARGMONLY
  | READONLY
  | INACC_OR_ARGMONLY
  | OTHER.

  Definition call_ev_spec := gmap (loc * loc) Qp -> list uvalue -> list uvalue -> Prop.

  Definition read_argmemonly_spec : call_ev_spec :=
   fun (C : gmap (loc * loc) Qp) (args_t args_s : list uvalue) =>
    (∀ l_t l_s n,
        nth_error (zip args_t args_s) n =
          Some (UVALUE_Addr l_t, UVALUE_Addr l_s) ->
            ∃ q, C !! (l_t.1, l_s.1) = Some q ∧ Qp.lt q 1).

  Definition argmemonly_spec : call_ev_spec :=
   fun (C : gmap (loc * loc) Qp) (args_t args_s : list uvalue) =>
    (∀ l_t l_s n,
        nth_error (zip args_t args_s) n = Some (UVALUE_Addr l_t, UVALUE_Addr l_s) ->
        C !! (l_t.1, l_s.1) = None).

  Definition readonly_spec : call_ev_spec :=
   fun (C : gmap (loc * loc) Qp) (args_t args_s : list uvalue) =>
     (∀ (l_t l_s : loc) q, C !! (l_t, l_s) = Some q -> Qp.lt q 1).

  Definition inacc_or_argmemonly_spec : call_ev_spec :=
   fun (C : gmap (loc * loc) Qp) (args_t args_s : list uvalue) =>
    (∀ l_t l_s n,
      nth_error (zip args_t args_s) n =
        Some (UVALUE_Addr l_t, UVALUE_Addr l_s) ->
      C !! (l_t.1, l_s.1) = None) /\
    (∀ (l_t l_s : Z * Z),
        (l_t.1, l_s.1) ∈ dom C ->
        (UVALUE_Addr l_t, UVALUE_Addr l_s) ∉ (zip args_t args_s) ->
        C !! (l_t.1, l_s.1) = Some 1%Qp).

  Definition other_spec : call_ev_spec :=
   fun (C : gmap (loc * loc) Qp) (args_t args_s : list uvalue) =>
     args_t = args_s /\ C = ∅.

  Definition attribute_spec (c : attr_case) :=
    match c with
      | ARG_READ => read_argmemonly_spec
      | ARGMONLY => argmemonly_spec
      | READONLY => readonly_spec
      | INACC_OR_ARGMONLY => inacc_or_argmemonly_spec
      | NONE => other_spec
    end.

  Definition has_attr_case (attrs : list fn_attr) (c : attr_case) : Prop :=
    let has := fun attr => HasAttr attr (remove_tag attrs) in
    match c with
    | ARG_READ => has FNATTR_Argmemonly && has FNATTR_Readonly
    | ARGMONLY => has FNATTR_Argmemonly /\ not (has FNATTR_Readonly)
    | READONLY => has FNATTR_Readonly /\ not (has FNATTR_Argmemonly)
    | INACC_OR_ARGMONLY => has FNATTR_Inaccessiblemem_or_argmemonly
    | NONE =>
        not (has FNATTR_Argmemonly) /\
        not (has FNATTR_Readonly) /\
        not (has FNATTR_Writeonly) /\
        not (has FNATTR_Nofree) /\
        not (has FNATTR_Inaccessiblemem_or_argmemonly)
    end.

  (** *Specification of memory-related function attributes

      Invariants about the checked-out set that holds before and after a call. *)
  (* For now, we only express invariants for specific attribute lists (instead of
     allowing for an arbitrary number of attribute combinations and disallowing
     certain combinations). *)
  Equations attribute_interp :
    ∀ {X Y : Type}, ExternalCallE X → ExternalCallE Y → gmap (loc * loc) Qp -> Prop :=
    attribute_interp
      (ExternalCall a f args_t attr_t)
      (ExternalCall a0 f0 args_s attr_s) C :=
      attr_t = attr_s /\
       ∃ (c : attr_case),
         has_attr_case attr_t c /\
         attribute_spec c C args_t args_s.

  Equations vir_call_ev {X Y} :
    language.CallE (call_events vir_lang) X →
    language.CallE (call_events vir_lang) Y →
    (gmap (loc * loc) Qp * list frame_names * list frame_names)%type -> iPropI Σ :=
    vir_call_ev (ExternalCall t f args attr) (ExternalCall t0 f0 args0 attr0) (C, i_t, i_s) :=
      (dval_rel f f0 ∗
        ⌜t = t0⌝ ∗ ([∗ list] x;y ∈ args; args0, uval_rel x y) ∗
        checkout C ∗ frame_WF i_t i_s ∗ stack_tgt i_t ∗ stack_src i_s ∗
        ⌜attribute_interp (ExternalCall t f args attr) (ExternalCall t0 f0 args0 attr0) C⌝)%I.

  Equations vir_call_ans {X Y : Type} :
    language.CallE (call_events vir_lang) X → X ->
    language.CallE (call_events vir_lang) Y → Y ->
    (gmap (loc * loc) Qp * list frame_names * list frame_names) -> iPropI Σ :=
      vir_call_ans (ExternalCall t f args attr) v_t
                  (ExternalCall t0 f0 args0 attr0) v_s (C, i_t, i_s) :=
        (checkout C ∗ stack_tgt i_t ∗ stack_src i_s ∗ uval_rel v_t v_s)%I.

  (* Readonly :
      initial and final states are identical. *)
  Equations readonly_ans_spec {R1 R2}
    (ev_t : CallEvents vir_lang R1) (v_t : R1) (ev_s : CallEvents vir_lang R2) (v_s : R2) : Prop :=
    readonly_ans_spec
      (StateEff (call_events vir_lang) (s, ExternalCall t f args attr)) v_t
      (StateEff (call_events vir_lang) (s0, ExternalCall t0 f0 args0 attr0)) v_s :=
    (v_t.1 = s /\ v_s.1 = s0).

  (* ArgMemOnly :
      All addr arguments have related values stored in the heap *)
  Equations argmemonly_ev_spec {R1 R2}
    (ev_t : CallEvents vir_lang R1) (ev_s : CallEvents vir_lang R2) : Prop :=
    argmemonly_ev_spec
      (StateEff (call_events vir_lang) (s, ExternalCall t f args attr))
      (StateEff (call_events vir_lang) (s0, ExternalCall t0 f0 args0 attr0)) :=
    (forall a v, UVALUE_Addr (a, 0)%Z ∈ args -> vir_heap (vmem s) !! a = Some v ->
            exists a0 v0, UVALUE_Addr (a0, 0)%Z ∈ args0 /\ vir_heap (vmem s0) !! a0 = Some v0 /\ v = v0) /\
    (forall a v, UVALUE_Addr (a, 0) ∈ args0 -> vir_heap (vmem s0) !! a = Some v ->
            exists a0 v0, UVALUE_Addr (a0, 0)%Z ∈ args /\ vir_heap (vmem s) !! a0 = Some v0 /\ v = v0).

  (* Every piece of state that is not part of the arguments is unchanged. *)
  Equations argmemonly_ans_spec {R1 R2}
    (ev_t : CallEvents vir_lang R1) (v_t : R1) (ev_s : CallEvents vir_lang R2) (v_s : R2) : Prop :=
    argmemonly_ans_spec
      (StateEff (call_events vir_lang) (s, ExternalCall t f args attr)) v_t
      (StateEff (call_events vir_lang) (s0, ExternalCall t0 f0 args0 attr0)) v_s :=
    ((∀ a v, vir_heap (vmem v_t.1) !! a = Some v ->
                UVALUE_Addr (a, 0) ∉ args ->
                vir_heap (vmem s) !! a = Some v) /\
          (∀ a v, vir_heap (vmem v_s.1) !! a = Some v ->
                  UVALUE_Addr (a, 0) ∉ args ->
                  vir_heap (vmem s0) !! a = Some v)).

  (* Specification for [nofree] and [writeonly] *)
  Equations no_free_ans_spec {R1 R2}
    (ev_t : CallEvents vir_lang R1) (v_t : R1) (ev_s : CallEvents vir_lang R2) (v_s : R2) : Prop :=
    no_free_ans_spec
      (StateEff (call_events vir_lang) (s, ExternalCall t f args attr)) v_t
      (StateEff (call_events vir_lang) (s0, ExternalCall t0 f0 args0 attr0)) v_s :=
      (forall a v, vir_heap (vmem s) !! a = Some v ->
             exists v', vir_heap (vmem v_t.1) !! a = Some v') /\
      (forall a v, vir_heap (vmem s0) !! a = Some v ->
             exists v', vir_heap (vmem v_s.1) !! a = Some v').

  Definition vir_E_ans : ∀ X Y : Type, E vir_lang X → X → E vir_lang Y → Y → Prop :=
    λ (X Y : Type) (X0 : E vir_lang X) (X1 : X) (X2 : E vir_lang Y) (X3 : Y),
      (X1 ~= X3 ∧ X0 ~= X2).

  Definition vir_call_ev_ : ∀ X Y : Type, CallEvents vir_lang X → CallEvents vir_lang Y → Prop :=
    λ (X Y : Type) (e1 : CallEvents vir_lang X) (e2 : CallEvents vir_lang Y),
    argmemonly_ev_spec e1 e2.

  Definition vir_E_ev : ∀ X Y : Type, E vir_lang X → E vir_lang Y → Prop :=
    λ (X Y : Type) (X0 : E vir_lang X) (X2 : E vir_lang Y), X0 ~= X2.

  Definition globalbij_interp (gs_t gs_s : global_env) : iProp Σ :=
      (Addr.null ↔h Addr.null) ∗
     ⌜dom gs_s ⊆ dom gs_t⌝ ∗ (* LATER: duplicated info: remove? *)
      target_globals (gs_t : leibnizO _) ∗ source_globals gs_s  ∗
     ([∗ map] g ↦ v ∈ gs_s, ∃ v', ⌜gs_t !! g = Some v'⌝ ∗ dval_rel v' v).

  #[global] Instance globalbij_interp_persistent gs_t gs_s:
    Persistent (globalbij_interp gs_t gs_s).
  Proof. apply _. Qed.

  Definition frames (m : mem) : frame_stack := m.2.

  #[global]
   Instance vir_simulirisGS : simulirisGS (iPropI Σ) vir_lang :=
    {| state_interp :=
        (fun (σ_t σ_s : vir_state) =>
           ∃ C S G,
                heap_ctx sheapG_heap_source
                  (vir_heap σ_s.(vmem), vir_dyn σ_s.(vmem)) (frames σ_s.(vmem)) G
                  (σ_s.(vlocal).1)
                  (σ_s.(vlocal).2)
              ∗ heap_ctx sheapG_heap_target
                  (vir_heap σ_t.(vmem), vir_dyn σ_t.(vmem)) (frames σ_t.(vmem)) G
                  (σ_t.(vlocal).1)
                  (σ_t.(vlocal).2)
              ∗ ghost_var checkedoutG_bij_name (1/2) C
              ∗ heapbij_interp S C ∗ ⌜dom C ⊆ S⌝
              ∗ globalbij_interp σ_t.(vglobal) σ_s.(vglobal)
        )%I;
      call_ev := @vir_call_ev;
      call_ans := @vir_call_ans;
      arg_val_rel :=
        (λ '(u0, l0) '(u, l) '(C, i_t, i_s),
          frame_WF i_t i_s ∗
          checkout C ∗ stack_tgt i_t ∗ stack_src i_s ∗
            dval_rel u0 u ∗ [∗ list] x;y ∈ l0; l, uval_rel x y)%I;
      res_val_rel :=
        (λ u v '(C, i_t, i_s),
          checkout C ∗ stack_tgt i_t ∗ stack_src i_s ∗
           uval_rel u v)%I ; |}.

End spec.

Arguments frame_WF {_ _}.

#[global] Instance SimE_vir_iProp {Σ} `{!vellirisGS Σ}:
  SimE (iPropI Σ) vir_lang := sim_expr_stutter (η := vir_handler).

Arguments sim_coind_ub {_ _ _ _ _} [_] {_ _ _ _ _}.
Arguments sim_coind_exc {_ _ _ _ _} [_] {_ _ _ _ _}.
