From iris.prelude Require Import options.

From Equations Require Import Equations.

From velliris.program_logic Require Import program_logic.
From velliris.utils Require Import tactics.

From Coq Require Import String.

From ITree Require Import
     ITree
     ITreeFacts
     Events.StateFacts.

From Vellvm Require Export
     Handlers.Handlers
     LLVMAst
     Semantics.LLVMEvents.

Import DenoteTactics.

(* We can instantiate the ITree-based Vellvm IR, [VIR], with our simulation
  relation.*)

(* We start from the interpretation layer of VIR that has [MemoryE] memory events
 and [ExternalCallE] call events uninterpreted.


    Recall the original VIR interpretation stack:


           Layer    |   Interpreted Information
        ------------------------------------------------

         [ L0  ]   ---- NONE
            ↓
         [ L1  ]   ---- intrinsics, global
            ↓
         [ L2  ]   ---- intrinsics, global, local
            ↓
         [ L3  ]   ---- intrinsics, global, local, memory   (! FIX !)

    * See: [interp_mcfg1], [interp_mcfg2], ... etc in
        [Vellvm/Semantics/InterpretationStack.v]

   This original stack is unrealistic, in the sense that we must *simultaneously*
   interpret _external calls_ when interpreting _memory_ (since external call
    may affect memory in a certain way)


    The ⋆NEW⋆ VIR interpretation stack:

           Layer    |   Interpreted Information
        ------------------------------------------------

         [ L0  ]   ---- NONE
            ↓
         [ L1  ]   ---- intrinsics, global
            ↓
         [ L2  ]   ---- intrinsics, global, local
            ↓
         [ L3' ]   ---- intrinsics, global, local, memory,
                        ***partially interpreted external calls***  (! NEW !)

        The new interpretation layer [ L3' ] gives partially interpreted external
        calls, where it uses information from the LLVM Fn Attributes to give
        a lightweight specification to how call events may affect memory.
 *)

(** *Instantiation of [VIR] language *)

(* ------------------------------------------------------------------------ *)
(* Auxillary functions for function calls in VIR *)

Definition call_args : forall X, LLVMEvents.ExternalCallE X -> dvalue * list uvalue.
  intros. inversion H.
  exact (f, args).
Defined.

Definition call_data : forall X, LLVMEvents.ExternalCallE X -> (DynamicTypes.dtyp * list fn_attr).
  intros. by inversion H.
Defined.

Definition call_hval : forall X, LLVMEvents.ExternalCallE X -> X = uvalue.
  intros. by inversion H.
Defined.

Canonical Structure vir_calls : call_event :=
  Build_call_event LLVMEvents.ExternalCallE
                   _
                   uvalue
                   _
                   call_args
                   call_data
                   call_hval.

(* ------------------------------------------------------------------------ *)
(* VIR is an instance of the [lang] for the simulitree-style simulation. *)


(* Local environment and local stack *)
Definition local : Type := (local_env * lstack)%type.

(* We observe the [logical] memory part of the quasi-concrete memory model
  inherited from VIR.

  N.B. For future work, we can support the full quasi-concrete memory model
        to support integer arithmetic. *)
Definition logical_memory : Type :=
  ((gmap Z logical_block  * gset Z) * frame_stack)%type.

Notation mem := logical_memory.

(** *VIR state *)

(* [VIR] state is composed of a global environment, local environment (and stack),
   and logical view of the [VIR] memory. *)
Record vir_state : Type := virState {
  vglobal : global_env ;
  vlocal : local;
  vmem : mem }.

(* Stateful operations on [vir_state] *)

Definition apply_global (f : global_env -> global_env) : vir_state -> vir_state :=
  fun σ => (virState (f σ.(vglobal)) σ.(vlocal) σ.(vmem)).

Definition apply_local (f : local -> local) : vir_state -> vir_state :=
  fun σ => (virState σ.(vglobal) (f σ.(vlocal)) σ.(vmem)).

Definition apply_mem (f : mem -> mem) : vir_state -> vir_state :=
  fun σ => (virState σ.(vglobal) σ.(vlocal) (f σ.(vmem))).

Definition update_global (g : global_env) : vir_state -> vir_state :=
  fun σ => (virState g σ.(vlocal) σ.(vmem)).

Definition update_local (l : local) : vir_state -> vir_state :=
  fun σ => (virState σ.(vglobal) l σ.(vmem)).

Definition update_mem (l : mem) : vir_state -> vir_state :=
  fun σ => (virState σ.(vglobal) σ.(vlocal) l).

Definition write_global (id : global_id) (v : dvalue) : vir_state ->  vir_state :=
  apply_global (fun g => <[id := v]> g).

(* ------------------------------------------------------------------------ *)
(* Basic properties about [update_X] *)

Lemma update_local_id σ:
  update_local (vlocal σ) σ = σ.
Proof. by destruct σ. Qed.

Lemma update_global_id σ:
  update_global (vglobal σ) σ = σ.
Proof. by destruct σ. Qed.

Lemma update_mem_id σ:
  update_mem (vmem σ) σ = σ.
Proof. by destruct σ. Qed.

(* ------------------------------------------------------------------------ *)
(* Instantiation of the [language] instance for the weakest precondition definition. *)
Canonical Structure vir_lang : language :=
  Language vir_state
           LLVMGEnvE
           (Handlers.LLVMEvents.LLVMEnvE +' Handlers.LLVMEvents.LLVMStackE)
           LLVMEvents.MemoryE
           vir_calls
           IntrinsicE
           LLVMEvents.UBE
           (Exception.exceptE ())
           LLVMEvents.PickE
           LLVMEvents.DebugE.

Definition vir_simulirisGS {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}
  := simulirisGS PROP vir_lang.

From Vellvm Require Export
     Semantics.InterpretationStack
     Utilities
     Syntax
     Numeric.Integers.

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

(* ------------------------------------------------------------------------ *)

(* This [vir_expr_] corresponds to the VIR [ L2 ] layer. *)
Definition vir_expr_ :=
  itree (ExternalCallE +' MemoryE +' PickE +' UBE +' DebugE +' FailureE).

(* The semantics of [vir] is given through [vir_handler].  *)
#[global] Instance vir_handler : handlers vir_lang := {|

  local_handler := fun T X σ =>
    ITree.bind
      (interp_local_stack_h (handle_local (v := uvalue))
        (inr1 (inr1 (inl1 X))) σ.(vlocal))
              (fun '(l, v) => Ret (update_local l σ, v)) ;

  global_handler := fun T X σ =>
    ITree.bind
      (interp_global_h (inr1 (inr1 (inl1 X))) σ.(vglobal))
        (fun '(g, v) => Ret (update_global g σ, v));

  memory_handler := fun T X σ =>
    (ITree.bind (handle_memory X σ.(vmem))
      (fun '(l, v) => Ret (update_mem l σ, v))) ;

  intrinsics_handler := fun T X σ =>
    (ITree.bind (handle_intrinsic X σ.(vmem))
        (fun '(l, v) => Ret (update_mem l σ, v))) ;

  E_handler := fun T X σ =>
    (ITree.bind (concretize_picks (E := language.L2 vir_lang) X)
          (fun x => ret (σ, x)))

|}.

(* Instantiation of simulation definition *)

#[global]
Instance SimE_vir {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}
         `{simulirisGS PROP vir_lang}
  : SimE PROP vir_lang:= sim_expr_stutter (η := vir_handler).

(* ------------------------------------------------------------------------ *)

(* Address identifier *)
Definition loc := Z.
(* Address offset *)
Definition offset := Z.
(* The [val] stored in a heap is a logical block. *)
Definition val := logical_block.

(* Leibniz equality for [VIR] constructs *)
Canonical Structure locO := leibnizO loc.
Canonical Structure offsetO := leibnizO offset.
Canonical Structure valO := leibnizO val.
Canonical Structure bytesO := leibnizO (list byte).
Canonical Structure dvalO := leibnizO dvalue.

(* FIXME/MOVE: Notation conflict: Need to shift a level *)
Notation "x <- c1 ;; c2" := (ITree.bind c1 (fun x => c2))
                             (at level 63, c1 at next level, right associativity).

(* ------------------------------------------------------------------------ *)

(* Instead of SProp, we axiomatize irrelevance of proof of byte range  *)
Axiom proof_irrel_byte_range :
  forall intval, ProofIrrel (-1 < intval < Byte.modulus)%Z.

Definition byte_range intval := (-1 < intval < Byte.modulus)%Z.

(* ------------------------------------------------------------------------ *)

(* Bureaucratic instances (Countable, EqDecision) *)

Global Program Instance byte_countable : Countable byte :=
  inj_countable Byte.intval (fun x => _) _.
Next Obligation.
  destruct (decide (-1 < x < Byte.modulus)%Z); last exact None.
  exact (Some (Byte.mkint x a)).
Defined.
Next Obligation.
  destruct x; rewrite /byte_countable_obligation_1; cbn.
  destruct (decide (-1 < intval < Byte.modulus)%Z); try lia.
  by rewrite (proof_irrel_byte_range intval intrange a).
Qed.

Global Instance sbyte_countable : Countable SByte.
Proof.
  refine (inj_countable' (λ sb, match sb with
  | Byte b => inl (encode b) | Ptr p => (inr (inl (encode p)))
  | PtrFrag => (inr (inr (inl tt))) | SUndef => (inr (inr (inr tt)))
  end) (fun n => match n with
  | inl b => (match (decode b) with | Some x => Byte x | None => PtrFrag end)
  | inr (inl p) => (match (decode p) with | Some x => Ptr x | None => PtrFrag end)
  | inr (inr (inl _)) => PtrFrag
  | _ => SUndef
  end) _); intros []; eauto; by rewrite decode_encode.
Qed.

Global Instance intmap_eq_dec : EqDecision (IntMap SByte).
Proof. apply _. Defined.
Global Instance intmap_countable : Countable (IntMap SByte).
Proof. apply _. Qed.

Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Qed.

Global Instance val_countable : Countable val.
Proof.
  refine (inj_countable'
            (λ l, match l with
                  | LBlock n m o => (n, m, o) end)
            (λ '(n, m, o), LBlock n m o) _);
  by intros [].
Qed.

(* ------------------------------------------------------------------------ *)

Definition local_loc := LLVMAst.raw_id.
Definition local_val := uvalue.
Definition local_valO := leibnizO local_val.

#[global] Instance local_val_eq_dec : EqDecision local_val := @uvalue_eq_dec.
#[global] Instance dval_eq_dec : EqDecision dvalue := @dvalue_eq_dec.

(* ------------------------------------------------------------------------ *)

#[global] Instance fbinop_eq_dec : EqDecision fbinop.
Proof. solve_decision. Qed.
#[global] Instance fbinop_countable : Countable fbinop.
Proof.
  refine (inj_countable' (λ fb, match fb with
    | FAdd => 0
    | FSub => 1
    | FMul => 2
    | FDiv => 3
    | FRem => 4
   end) (λ n, match n with
    | 0 => FAdd
    | 1 => FSub
    | 2 => FMul
    | 3 => FDiv
    | _ => FRem end) _); by intros [].
Qed.

#[global] Instance fcmp_eq_dec : EqDecision fcmp.
Proof. solve_decision. Qed.
#[global] Instance fcmp_countable : Countable fcmp.
Proof.
  refine (inj_countable' (λ fc, match fc with
  | FFalse => 0 | FOeq => 1 | FOgt => 2 | FOge => 3 | FOlt => 4
  | FOle => 5 | FOne => 6 | FOrd => 7 | FUno => 8 | FUeq => 9
  | FUgt => 10 | FUge => 11 | FUlt => 12 | FUle => 13 | FUne => 14
  | FTrue => 15 end) (λ n, match n with
  | 0 => FFalse | 1 => FOeq | 2 => FOgt | 3 => FOge | 4 => FOlt
  | 5 => FOle | 6 => FOne | 7 => FOrd | 8 => FUno | 9 => FUeq
  | 10 => FUgt | 11 => FUge | 12 => FUlt | 13 => FUle | 14 => FUne
  | _ => FTrue end) _); by intros [].
Qed.

#[global] Instance conversion_type_eq_dec : EqDecision conversion_type.
Proof. solve_decision. Qed.
#[global] Instance conversion_type_countable : Countable conversion_type.
Proof.
  refine (inj_countable' (λ ct, match ct with
  | Trunc => 0 | Zext => 1 | Sext => 2 | Fptrunc => 3
  | Fpext => 4 | Uitofp => 5 | Sitofp => 6 | Fptoui => 7
  | Fptosi => 8 | Inttoptr => 9 | Ptrtoint => 10 | Bitcast => 11 end)
  (λ ct, match ct with
  | 0 => Trunc | 1 => Zext | 2 => Sext | 3 => Fptrunc
  | 4 => Fpext | 5 => Uitofp | 6 => Sitofp | 7 => Fptoui
  | 8 => Fptosi | 9 => Inttoptr | 10 => Ptrtoint
  | _ =>  Bitcast end) _); by intros [].
Qed.

#[global] Instance N_eq_dec : EqDecision N.
Proof. solve_decision. Qed.
#[global] Instance dtyp_eq_dec : EqDecision dtyp := dtyp_eq_dec.

From Vellvm.Semantics Require Export DynamicValues.

#[global] Instance int1_eq_dec : EqDecision DynamicValues.int1.
Proof. repeat intro; red; apply Int1.eq_dec. Qed.
#[global] Instance int8_eq_dec : EqDecision DynamicValues.int8.
Proof. repeat intro; red; apply Int8.eq_dec. Qed.
#[global] Instance int32_eq_dec : EqDecision DynamicValues.int32.
Proof. repeat intro; red; apply Int32.eq_dec. Qed.
#[global] Instance int64_eq_dec : EqDecision DynamicValues.int64.
Proof. repeat intro; red; apply Int64.eq_dec. Qed.

(* ------------------------------------------------------------------------ *)

(* Functions about event signature conversion and lifting *)

Notation L0'expr :=
    (itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +'
     (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE)).

Definition find_fun e (τ : dtyp)
  (fn : dvalue) (args : list uvalue) (attrs : list fn_attr) :
  L0'expr uvalue :=
    match lookup_defn fn e with
    | Some f_den => f_den args
    | None =>
        ITree.bind (map_monad (λ uv : uvalue, pickUnique uv) args)
          (λ dargs : list dvalue,
              (trigger (ExternalCall τ fn (dvalue_to_uvalue <$> dargs) attrs)))
    end.

Definition instr_to_L0 : IntrinsicE +' exp_E ~> L0 :=
  fun T e =>
    inr1
      (match e with
      (* Intrinsic *)
      | inl1 l => inl1 l
      (* LLVMGEnvE *)
      | inr1 x => inr1 (match x with
                          | inl1 l => inl1 l
                          | inr1 x => inr1
                                    (match x with
                                      | inl1 e => (inl1 (inl1 e))
                                      | inr1 e => inr1 e
                                      end)
                        end)
      end).

Equations instrE_conv:
  forall T : Type, instr_E T -> L0 T :=
  instrE_conv T (inl1 (Call t f args attr)) :=
    inl1 (ExternalCall t f args (FNATTR_Internal :: attr));
  instrE_conv T (inr1 e) := instr_to_L0 _ e.

Equations call_conv:
  forall T : Type, L0' T -> L0 T :=
  call_conv T (inl1 (Call t f args attr)) :=
    inl1 (ExternalCall t f args (FNATTR_Internal :: attr));
  call_conv T (inr1 (inl1 (ExternalCall t f args attr))) :=
    inl1 (ExternalCall t f args (FNATTR_External :: attr));
  call_conv T (inr1 (inr1 e)) := inr1 e.

Definition instr_conv {R} : itree instr_E R -> expr vir_lang R :=
  λ X : itree instr_E R,
    interp (M := itree (language.L0 vir_lang))
      (fun _ x => Vis (instrE_conv _ x) ret) X.

Definition exp_conv {R} : itree exp_E R -> expr vir_lang R :=
  fun e1 =>
    interp (M := itree (language.L0 vir_lang))
      (fun _ x => Vis (exp_to_L0 x) ret) e1.

Definition L0'expr_conv {R} : itree L0' R -> expr vir_lang R :=
  fun X =>
    interp (M := itree (language.L0 vir_lang))
      (fun _ x => Vis (call_conv _ x) ret) X.

(* ------------------------------------------------------------------------ *)

(* Properties of conversion *)

Lemma instr_conv_ret {R} (x : R):
  instr_conv (Ret x) ≅ Ret x.
Proof.
  by rewrite /instr_conv interp_ret.
Qed.

#[global] Instance eq_itree_L0'expr_conv {R} :
  Proper (eq_itree eq ==> eq_itree (R2 := R) eq) L0'expr_conv.
Proof.
  repeat intro.
  unfold L0'expr_conv. rewrite H; done.
Qed.

#[global] Instance eq_itree_instr_conv {R} :
  Proper (eq_itree eq ==> eq_itree (R2 := R) eq) instr_conv.
Proof.
  repeat intro.
  unfold instr_conv. rewrite H; done.
Qed.

Lemma instr_conv_bind {X R} (e : _ X) (k : _ -> _ R) :
  instr_conv (x <- e ;; k x) ≅ x <- instr_conv e ;; instr_conv (k x).
Proof.
  rewrite /instr_conv.
  by setoid_rewrite interp_bind.
Qed.

Lemma instr_conv_nil :
  instr_conv (denote_code nil) ≅ Ret tt.
Proof.
  cbn. go.
  by setoid_rewrite interp_ret.
Qed.

Lemma exp_conv_ret {R} (r : R):
  exp_conv (Ret r) ≅ Ret r.
Proof.
  by setoid_rewrite interp_ret.
Qed.

Lemma instr_conv_localwrite :
  forall x v,
    instr_conv (trigger (LocalWrite x v)) ≅
      vis (LocalWrite x v) (fun x => Tau (Ret x)).
Proof.
  intros. rewrite /instr_conv.
  rewrite interp_vis. setoid_rewrite interp_ret.
  rewrite {1}/subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1.
  simp instrE_conv. rewrite bind_trigger.
  reflexivity.
Qed.

Lemma eq_handler_instrE_conv :
  eq_Handler
    (λ T (e : exp_E T), Vis (instrE_conv T (inr1 (inr1 e)))
                          (λ x0 : T, Ret x0))
    (λ T (e : exp_E T), Vis (exp_to_L0 e) Monad.ret).
Proof.
  repeat intro. simp instrE_conv.
  rewrite /instr_to_L0 /exp_to_L0;
    destruct a; try destruct s; try reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)

Ltac simp_instr :=
  rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1;
  simp instrE_conv.

(* ------------------------------------------------------------------------ *)

(* Notations for [vir] *)
Notation "⟅ e ⟆" := (L0'expr_conv e).
Notation " e ⤉" := (lift_post e) (at level 50).
Notation "⟦ e ⟧ σ" := (interp_L2 vir_handler e σ) (at level 50).
