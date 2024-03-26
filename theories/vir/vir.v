From iris.prelude Require Import options.

From Equations Require Import Equations.

From velliris.program_logic Require Import program_logic.
From velliris.utils Require Import tactics.

From Coq Require Import String.

From ITree Require Import
     ITree
     ITreeFacts
     Events.StateFacts.

From Vellvm Require Import
     Handlers.Handlers
     LLVMAst
     Semantics.LLVMEvents.

Import DenoteTactics.


(* Instantiation for [VIR] language *)

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

(* VIR is an instance of the [lang] for the simulitree-style simulation. *)
Definition vir_state : Type := (global_env * (local_env * lstack) *
                                  ((gmap Z logical_block  * gset Z) * frame_stack))%type.
Arguments vir_state /.

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

From Vellvm Require Import
     Semantics.InterpretationStack
     Utilities
     Syntax
     Numeric.Integers.

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

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

(* This [vir_expr_] corresponds to the VIR [ L2 ] layer. *)
Definition vir_expr_ :=
  itree (ExternalCallE +' MemoryE +' PickE +' UBE +' DebugE +' FailureE).

(** *Logical state

  The language has a *logical state* representation that corresponds to the
  high-level heaps that are typically manipulated in the Iris logic.

  The logical state will correspond to an Iris resource (i.e. an Iris heap),
  and the adequacy statement should express the soundness between [state] and
  [logical state].

  The logical state is a *logical view* of the state, which is indicated by
  [logical view]. *)

Definition id := Z.
Definition offset := Z.

Canonical Structure bytesO := leibnizO (list byte).
Canonical Structure idO := leibnizO id.
Canonical Structure offsetO := leibnizO offset.

#[global] Instance vir_handler : handlers vir_lang.
  constructor; intros.
- (* local_events *)
  intro σ; unfold state in *; cbn in *.
  destruct σ as ((?&?)&?).
  (* Global environment and memory remain constant *)
  eapply
    ((fun x =>
      ITree.bind (E := language.L2 vir_lang) x (fun '(a, c) => ret (g, a, p0, c)))
      : itree (language.L2 vir_lang) (_ * T) ->
        itree (language.L2 vir_lang) (global_env * _ * _ * T)).

  eapply interp_local_stack_h; eauto; cycle 3.
  { exact (inr1 (inr1 (inl1 X))). }
  all : try typeclasses eauto.
  eapply handle_local; typeclasses eauto.

- (* global_events *)
  intro σ; unfold state in *; cbn in *.
  destruct σ as ((?&?)&?).
  (* Local environment and memory remain constant *)
  eapply
    ((fun x =>
      ITree.bind (E := language.L2 vir_lang) x (fun '(a, c) => ret (a, p, p0, c)))
      : itree (language.L2 vir_lang) (global_env * T) ->
        itree (language.L2 vir_lang) (global_env * _ * _ * T)).

  eapply (@interp_global_h raw_id dvalue); eauto; cycle 3.
  3: exact (inr1 (inr1 (inl1 X))).
  all : try typeclasses eauto.

- (* MemoryE *)
  intro σ; unfold state in *; cbn in *.
  destruct σ as ((?&?)&?).

  (* Global and local environment remain constant *)
  eapply
    ((fun x =>
      ITree.bind (E := language.L2 vir_lang) x (fun '(a, c) => ret (g, p, a, c)))
      : itree (language.L2 vir_lang) (_ * T) ->
        itree (language.L2 vir_lang) (global_env * _ * _ * T)).

  eapply handle_memory; eauto.

-  (* IntrinsicE *)
  intros σ; unfold state in *; cbn in *.
  destruct σ as ((?&?)&?).

  (* Global and local environment remain constant *)
  eapply
    ((fun x =>
      ITree.bind (E := language.L2 vir_lang) x (fun '(a, c) => ret (g, p, a, c)))
      : itree (language.L2 vir_lang) (_ * T) ->
        itree (language.L2 vir_lang) (global_env * _ * _ * T)).
  eapply handle_intrinsic; eauto.
- intros σ.
  exact (ITree.bind (concretize_picks (E := language.L2 vir_lang) X)
                 (fun x => ret (σ, x))).
Defined.

#[global]
Instance SimE_vir {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}
         `{simulirisGS PROP vir_lang}
  : SimE PROP vir_lang:= sim_expr_stutter (η := vir_handler).

(* VIR definitions *)

Definition globals := gmap LLVMAst.global_id dvalue.
Definition locals := gmap LLVMAst.raw_id uvalue.

Definition vir_locals :
  language.state vir_lang -> local_env :=
  fun '((_,(l,_)),_) => l.

Definition vir_local_stack :
  language.state vir_lang -> stack :=
  fun '((_,(_,s)),_) => s.

Fixpoint frame_at (i : nat) (F : frame_stack) : mem_frame :=
  match i with
    | 0%nat =>
        (match F with
          | Snoc _ f => f
          | Mem.Singleton f => f
          end)
    | S n =>
      (match F with
      | Snoc F f => frame_at n F
      | Mem.Singleton _ => []
      end)
  end.

Definition peek_frame := frame_at 0.

Definition local_state : vir_state -> local_env := fun x => x.1.2.1.
Definition frames : vir_state -> frame_stack := fun x => x.2.2.
Definition frames1 {R} : (global_env * (local_env * lstack) * memory_stack * R) -> frame_stack :=
  fun x => (x.1.2.2).

Definition frame : (global_env * (local_env * lstack) * memory_stack) -> mem_frame :=
  fun x => peek_frame (x.2.2).

(* Utility functions on frame stack *)
Definition flatten_frame_stack (m : frame_stack) : mem_frame :=
  let fix _aux (m : frame_stack) (acc : mem_frame) :=
    match m with
      | Mem.Singleton m => (m ++ acc)%list
      | Snoc m f => (f ++ _aux m acc)%list
    end
  in _aux m [].

Fixpoint frame_count (m : frame_stack) : nat :=
  match m with
    | Mem.Singleton m => 1
    | Snoc m f => S (frame_count m)
  end.

Definition add_to_frame_stack (f : frame_stack) (k : Z) : frame_stack :=
  match f with
  | Mem.Singleton f => Mem.Singleton (k :: f)
  | Snoc s f => Snoc s (k :: f)
  end.

Definition delete_from_frame (f : mem_frame) (k : Z) : mem_frame :=
  remove Z.eq_dec k f.

Definition delete_from_frame_stack (f : frame_stack) (k : Z) : frame_stack :=
  match f with
  | Mem.Singleton f => Mem.Singleton (delete_from_frame f k)
  | Snoc s f => Snoc s (delete_from_frame f k)
  end.

Definition free_locations_from_frame (mf d : mem_frame):=
  (fold_left (fun m key => remove Z.eq_dec key m) d mf).

Definition vir_allocaS :
  language.state vir_lang -> gset Z :=
  fun '((_,(_,_)),(_,l)) => list_to_set (peek_frame l).

(* FIXME: Notation conflict: Need to shift a level *)
Notation "x <- c1 ;; c2" := (ITree.bind c1 (fun x => c2))
                             (at level 63, c1 at next level, right associativity).

(* vir instr notations *)
Notation store l r := (trigger (Store l r)).
Notation load τ l := (trigger (Load τ l)).

(* Utilities for vir *)
Definition new_lb := make_empty_logical_block.

Definition interp_call :
  itree L0 ~> Monads.stateT vir_state (itree (language.L2 vir_lang)) :=
  fun _ t => State.interp_state (handle_L0_L2 vir_handler) t.

(* Utilities for associative map for function lookup at the top-level *)
Definition includes_keys : relation (list (dvalue * D.function_denotation)) :=
  fun fundefs fundefs' =>
  forall key value,
    lookup_defn key fundefs = Some value ->
    exists value', lookup_defn key fundefs' = Some value'.

Definition same_keys : relation (list (dvalue * D.function_denotation)) :=
  fun fundefs fundefs' =>
    includes_keys fundefs fundefs' /\ includes_keys fundefs' fundefs.

Instance same_keys_Symmetric : Symmetric same_keys.
intros x y []; split; eauto.
Qed.

Instance same_keys_Reflexive : Reflexive same_keys.
intros x; intros; split; repeat intro; eauto.
Qed.

Instance includes_keys_Transitive : Transitive includes_keys.
  repeat intro. specialize (H _ _ H1).
  destruct H as (?&?).
  specialize (H0 _ _ H). eauto.
Qed.

Instance same_keys_Transitive : Transitive same_keys.
  intros x y z [] []. split; etransitivity; eauto.
Qed.

Definition doesnt_include_keys {A} : relation (list (dvalue * A)) :=
  fun fundefs fundefs' =>
  forall key value,
    lookup_defn key fundefs = Some value ->
    not (exists value', lookup_defn key fundefs' = Some value').

Definition disjoint_keys {A} : relation (list (dvalue * A)) :=
  fun fundefs fundefs' =>
    doesnt_include_keys fundefs fundefs' /\ doesnt_include_keys fundefs' fundefs.

Notation L0'expr :=
    (itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE)).

(* Locations and values *)
Canonical Structure dvalO := leibnizO dvalue.

Definition loc := Z.
Definition val := logical_block.
Canonical Structure valO := leibnizO val.

(* Instead of SProp, we axiomatize irrelevance of proof of byte range  *)
Axiom proof_irrel_byte_range :
  forall intval, ProofIrrel (-1 < intval < Byte.modulus)%Z.

Definition byte_range intval := (-1 < intval < Byte.modulus)%Z.

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

Definition local_loc := LLVMAst.raw_id.
Definition local_val := uvalue.
Definition local_valO := leibnizO local_val.

#[global] Instance local_val_eq_dec : EqDecision local_val := @uvalue_eq_dec.
#[global] Instance dval_eq_dec : EqDecision dvalue := @dvalue_eq_dec.

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

From Vellvm.Semantics Require Import DynamicValues.
#[global] Instance int1_eq_dec : EqDecision DynamicValues.int1.
Proof. repeat intro; red; apply Int1.eq_dec. Qed.
#[global] Instance int8_eq_dec : EqDecision DynamicValues.int8.
Proof. repeat intro; red; apply Int8.eq_dec. Qed.
#[global] Instance int32_eq_dec : EqDecision DynamicValues.int32.
Proof. repeat intro; red; apply Int32.eq_dec. Qed.
#[global] Instance int64_eq_dec : EqDecision DynamicValues.int64.
Proof. repeat intro; red; apply Int64.eq_dec. Qed.

Definition to_addr : Z -> Z * Z :=
  fun b => (b, 0)%Z.

Section AuxDefs.

  Definition find_fun e (τ : dtyp)
    (fn : dvalue) (args : list uvalue) (attrs : list fn_attr) : L0'expr uvalue :=
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
      inl1 (ExternalCall t f args attr);
    instrE_conv T (inr1 e) := instr_to_L0 _ e.

  Equations call_conv:
    forall T : Type, L0' T -> L0 T :=
    call_conv T (inl1 (Call t f args attr)) :=
      inl1 (ExternalCall t f args attr);
    call_conv T (inr1 (inl1 (ExternalCall t f args attr))) :=
      inl1 (ExternalCall t f args attr);
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
End AuxDefs.

Section conv_properties.

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

End conv_properties.

Ltac simp_instr :=
  rewrite /subevent /resum /ReSum_inr /cat /Cat_IFun /inr_ /Inr_sum1;
  simp instrE_conv.

Lemma CFG_find_block_in {A} c i b :
  CFG.find_block (T:= A) c i = Some b -> b ∈ c.
Proof.
  induction c; cbn; intros; [ inversion H | ].
  destruct (Eqv.eqv_dec_p (blk_id a) i) eqn : Ha;
    inversion H; subst; clear H;
    [ apply elem_of_cons ; by left |].
  apply elem_of_cons; right; eapply IHc; eauto.
Qed.

Definition lb_mem (b : logical_block) : mem_block :=
  match b with
    | LBlock _ m _ => m
  end.

(* Notations for [vir] *)
Notation "⟅ e ⟆" := (L0'expr_conv e).
Notation " e ⤉" := (lift_post e) (at level 50).
Notation "⟦ e ⟧ σ" := (interp_L2 vir_handler e σ) (at level 50).
