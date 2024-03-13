From stdpp Require Import relations strings gmap.
From iris.algebra Require Import ofe.
From iris.prelude Require Import options.
From iris.bi Require Import bi.
Import bi.

From ITree Require Import ITree Eq Events.State Events.StateFacts.
Import ITree.Basics.Basics.Monads.

(* The interpretation of an external call may affect memory. [mem_callE]
   represents an "event transformer", which is parameterized by any event
   type [{E}] (representing an external function call), and expects as parameter
   the current state and an event of the parameterized type, and returns a
   new state with the return value of the event. *)
Section call.

  Context (S : Type).

  Definition pure_state {E F} `{E -< F} : E ~> stateT S (itree F)
    := fun _ e s => ITree.bind (trigger e) (fun x => Ret (s, x)).

  Structure call_event := {
    (* Call event *)
    CallE : Type -> Type;
    (* Metadata of the call *)
    Data : Type;
    (* Result Type *)
    Res : Type;
    (* Argument type *)
    Arg : Type;
    (* Arguments of the call *)
    args: forall X, CallE X -> Arg;
    (* Data of the call *)
    call_data : forall X, CallE X -> Data;
    (* Call always receives and returns values of a certain type *)
    Hval: forall X (e : CallE X), X = Res;
  }.

  Context (Call_event: call_event).

  Variant stateEff : Type -> Type :=
    | StateEff {X} : S * CallE Call_event X -> stateEff (S * X).

  Definition handle_stateEff {F : Type -> Type} `{@stateEff -< F}:
      CallE Call_event ~> stateT S (itree F) := fun _ e env => trigger (StateEff (env, e)).

  (* Note that this interpretation expects three kinds of events, [stateE S]
     which affect state but are not external calls, [E] corresponding to external
     call events, and [F] corresponding to all other events which are guaranteed to
     not affect state. *)
  (* Definition interp_call_state {E F} : *)
  (*     itree (@stateE S +' E +' F) ~> stateT S (itree (@stateEff E +' F)) := *)
  (*   interp_state (case_ h_state (case_ handle_stateEff (pure_state)). *)

End call.

Arguments StateEff {_} _ {_}.

(** *Abstract Language Specification

  A language has events, state, and values.

   There are three kinds of events in this language:
     - [state_events], the events that affect state but are not external calls
     - [call_events], the call events that may affect state
     - [E], all other kinds of events which do not affect state.

   Intuitively, these capture computations have no interpretations on state.
   The simulation relation defined in [slsls.v] define a "small-step"
   interpretation of state events and call events (the call events are
   translated into [mem_callE] events) , while the [E] events are left
   uninterpreted. *)
Structure language := Language {
  state : Type;
  global_events : Type -> Type;
  local_events : Type -> Type;
  memory_events : Type -> Type;
  call_events : call_event;
  intrinsics_events : Type -> Type;
  UB_events : Type -> Type;
  exc_events : Type -> Type;
  E : Type -> Type;
  F : Type -> Type; }.

Section lang.
  Context {PROP: bi}.

  Definition state_events Λ := (global_events Λ +' local_events Λ +' memory_events Λ).

  Definition CallEvents Λ := (@stateEff (state Λ) (call_events Λ)).

  (* Layers of interpretation *)
  Definition L0 Λ :=
    CallE (call_events Λ) +' intrinsics_events Λ +' global_events Λ +' local_events Λ +'
      memory_events Λ +' E Λ +' UB_events Λ +' F Λ +' exc_events Λ.
  (* Definition L1 Λ := StateEvents Λ +' CallEvents Λ +' intrinsics_events Λ +' UB_events Λ +' exc_events Λ +' intrinsics_events Λ +' E Λ. *)
  Definition L2 Λ := CallEvents Λ +' UB_events Λ +' exc_events Λ +' F Λ.
  Definition L3 Λ := UB_events Λ +' exc_events Λ +' E Λ.

  (* Handlers for the language : necessary for interpretation from [L0] to [L2] *)
  Class handlers Λ :=
    Handlers {
        local_handler : local_events Λ ~> stateT (language.state Λ) (itree (L2 Λ));
        global_handler : global_events Λ ~> stateT (language.state Λ) (itree (L2 Λ));
        memory_handler : memory_events Λ ~> stateT (language.state Λ) (itree (L2 Λ));
        intrinsics_handler : intrinsics_events Λ ~> stateT (language.state Λ) (itree (L2 Λ));
        E_handler : E Λ ~> stateT (language.state Λ) (itree (L2 Λ))}.

  Definition add_tau {Λ} {E : Type -> Type}:
    (E ~> stateT (language.state Λ) (itree (L2 Λ))) -> (E ~> stateT (language.state Λ) (itree (L2 Λ))) :=
    fun h t e s => (Tau (h t e s)).

  Definition handle_L0_L2 {Λ } (η : handlers Λ) : L0 Λ ~> stateT (language.state Λ) (itree (L2 Λ)) :=
    case_ (handle_stateEff (state Λ) (call_events Λ))
      (add_tau (case_ intrinsics_handler
        (case_ global_handler
            (case_ local_handler
                (case_ memory_handler
                    (case_ E_handler
                        (case_ (pure_state (state Λ)) (pure_state (state Λ))))))))).

  Definition handle_L0_L2_no_tau {Λ : language} (η : handlers Λ) : L0 Λ ~> stateT (language.state Λ) (itree (L2 Λ)) :=
    case_ (handle_stateEff (state Λ) (call_events Λ))
      (case_ intrinsics_handler
        (case_ global_handler
            (case_ local_handler
                (case_ memory_handler
                    (case_ E_handler
                        (case_ (pure_state (state Λ)) (pure_state (state Λ)))))))).

  Definition L0_expr' (Λ : language) R := (itree' (L0 Λ) R).
  (* Definition L1_expr' (Λ : language) R := (itree' (L1 Λ) (language.state Λ * R)). *)
  Definition L2_expr' (Λ : language) R := (itree' (L2 Λ) (language.state Λ * R)).
  Canonical Structure L0_exprO' {Λ : language} R := leibnizO (L0_expr' Λ R).

  (* An expression of a language is an itree instantiated by the events and values. *)
  Definition expr' (Λ : language) := L0_expr' Λ.
  Canonical Structure exprO' {Λ : language} R := leibnizO (L0_expr' Λ R).

  (* A stateful expression is an itree that returns a state and a value *)
  Definition st_expr' (Λ : language) R := (L2_expr' Λ R)%type.
  Canonical Structure st_exprO' {Λ : language} R := leibnizO (L2_expr' Λ R).

  (* We use this interpretation for our simulation *)
  Definition interp_L2' {Λ : language} (η : handlers Λ) {R} : expr' Λ R -> language.state Λ -> st_expr' Λ R :=
    λ (t : L0_expr' Λ R) (s : language.state Λ), observe (interp_state (handle_L0_L2 η) (go t) s).

  Instance expr_equiv' {Λ : language} R: Equiv (@expr' Λ R). eapply (@exprO' Λ). Defined.
  Instance st_expr_equiv' {Λ : language} R: Equiv (@st_expr' Λ R). apply (@st_exprO' Λ). Defined.

End lang.

Notation expr Λ := (itree (L0 Λ)).
(* Notation L1_expr Λ R := (itree (L1 Λ) (language.state Λ * R)). *)
Notation L2_expr Λ R := (itree (L2 Λ) (language.state Λ * R)).

(* Seal projections for [itree'].
    Top-level simulation is defined in terms of [expr] for ease of use. *)
Definition st_expr (Λ : language) R := (L2_expr Λ R)%type.
Canonical Structure exprO {Λ : language} R := leibnizO (expr Λ R).
Canonical Structure st_exprO {Λ : language} R := leibnizO (L2_expr Λ R).
Definition interp_L2 {Λ : language} (η : handlers Λ) {R} : itree (L0 Λ) R -> language.state Λ -> itree (L2 Λ) (language.state Λ * R) :=
  λ t (s : language.state Λ), interp_state (handle_L0_L2 η) t s.
Instance expr_equiv {Λ : language} R: Equiv (@expr Λ R). eapply (@exprO Λ). Defined.
Instance st_expr_equiv {Λ : language} R: Equiv (@st_expr Λ R). apply (@st_exprO Λ). Defined.

Notation "⟦ h ⟨ e ⟩ ⟧ σ" := (interp_L2 h e σ) (at level 50).
Notation "⟦ e ⟧ σ" := (@interp_L2 _ _ _ e σ) (at level 50).
Declare Scope expr_scope.
Bind Scope expr_scope with expr.

From Equations Require Import Equations.

(* Unbundled class definitions *)
Class simulirisGS (PROP : bi) (Λ : language) := SimulirisGSI {
  state_interp : state Λ → state Λ → PROP;
  checkedout_sets : Type;
  call_ev :
    forall {X Y},
      @CallE (call_events Λ) X → CallE (call_events Λ) Y →
        checkedout_sets -> PROP;
  call_ans :
    forall {X Y},
      CallE (call_events Λ) X → X ->
      CallE (call_events Λ) Y → Y ->
      checkedout_sets -> PROP;
  (* Value relation for calls *)
  arg_val_rel : @Arg (call_events Λ) ->
                @Arg (call_events Λ) ->
                checkedout_sets -> PROP;
  res_val_rel : @Res (call_events Λ) ->
                @Res (call_events Λ) ->
                checkedout_sets -> PROP;}.
