(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)
(* begin hide *)

From Coq Require Import
     ZArith String List
     FSets.FMapWeakList
     Bool.Bool.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

From Vellvm Require Import
     Numeric.Integers
     Numeric.Floats
     Utilities
     Syntax
     Semantics.DynamicValues
     Semantics.MemoryAddress
     Semantics.LLVMEvents.

Require Import Ceres.Ceres.

Import Sum.
Import Subevent.
Import EqvNotation.
Import ListNotations.
Import MonadNotation.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope monad_scope.
Open Scope string_scope.
Open Scope N_scope.

(* end hide *)

(** ** Uninterpreted denotation
    In this file, we define the first layer of denotation of _VIR_.

    More specifically, we follow the overall structure of itree-based denotations which consist
    in splitting the process in two main phases:
    1. Denote syntactic entities in terms of uninterpreted itrees, where syntactic events are carried in the tree.
    2. Interpret these itrees into the appropriate monad to implement the effect of these events.

    This file implements step 1: to a [mcfg], and to every internal syntactic constructs of _VIR_, we associate
    an uninterpreted interaction tree.

    The interface of events used for this denotation is defined in LLVMEvents.v. Roughly speaking, they include:
     - Internal Calls                                 (CallE)
     - External Calls                                 (ExtrernalCallE)
     - Calls to Intrinsics                            (IntrinsicE and MemoryIntrinsicE)
     - Manipulation of the global environment         (LLVMGEnvE)
     - Manipulation of the local environment          (LLVMEnvE)
     - Manipulation of the stack of local environment (LLVMStackE)
     - Manipulation of the memory                     (MemoryE)
     - Determination of undef                         (PickE)
     - Undefined behavior                             (UBE)
     - Failure                                        (FailureE)
     - Debugging                                      (DebugE)


    The exact interface used by each denotation function depends slightly on the object of consideration.
    Most specifically, three interfaces are used.
    - At the top level, in order to denote whole _VIR_ programs, we use the interface:
      L0 ::=  ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE. 
      Noticeable:
      * there are no more internal calls, they are resolved through the itree combinator
        for mutual recursiion [mrec].
    - For individual [cfg] (i.e. VIR functions) and most of their internal components:
      [instr_E ::= CallE +' IntrinsicE +' LLVMGEnvE +' LLVMEnvE +' MemoryE +' PickE +' UBE +' DebugE +' FailureE].
      Noticeable:
      * there are no external calls: the distinction between internal and external is only made once we
        tie the mutually recursive knot.
      * there are no manipulation of the stack: internally to a function, the denotation only sees the
        current local stack. The stack discipline is handled when tying the knot.
    - For expressions [exp], we specialize further the interface:
      [exp_E ::= LLVMGEnvE +' LLVMEnvE +' MemoryE +' PickE +' UBE +' DebugE +' FailureE].
      The rationale for this restriction is that we need to denote expressions both internally to cfgs
      of course, but also at the [mcfg] level to perform the initialization of the memory.
      We therefore need to be able to inject their signature into both [L0] and [instr_E].

    The effect of each event used through this first phase is defined by the corresponding [handler] in
    the Handlers repository. These handlers are chained together to form the interpretation of the
    itrees in the second phase.
 *)

Module Denotation(A:MemoryAddress.ADDRESS)(LLVMEvents:LLVM_INTERACTIONS(A)).
  Import LLVMEvents.

  Section CONVERSIONS.

    (** ** Typed conversion
        Performs a dynamic conversion of a [dvalue] of type [t1] to one of type [t2].
        For instance, convert an integer over 8 bits to one over 1 bit by truncation.

        The conversion function is not pure, i.e. in particular cannot live in [DynamicValues.v]
        as would be natural, due to the [Int2Ptr] and [Ptr2Int] cases. At those types, the conversion
        needs to cast between integers and pointers, which depends on the memory model.
     *)

    (* Note: Inferring the subevent instance takes a small but non-trivial amount of time,
       and has to be done here hundreds and hundreds of times due to the brutal pattern matching on
       several values. Factoring the inference upfront is therefore necessary.
     *)

    (* A trick avoiding proofs that involve thousands of cases: we split the conversion into
      the composition of a huge case analysis that builds a value of [conv_case], and a function
      with only four cases to actually build the tree.
    *)
    Variant conv_case : Set :=
    | Conv_Pure (x : dvalue) 
    | Conv_ItoP (x : dvalue) 
    | Conv_PtoI (x : dvalue)
    | Conv_Illegal (s: string).

    Definition get_conv_case conv (t1:dtyp) (x:dvalue) (t2:dtyp) : conv_case :=
      match conv with
      | Trunc =>
        match t1, x, t2 with
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 1 
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 1 
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 1 =>
          Conv_Pure (DVALUE_I1 (repr (unsigned i1)))

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 8 
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (unsigned i1)))

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 1
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 1 
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 8
        | DTYPE_I 64, DVALUE_Poison, DTYPE_I 1 
        | DTYPE_I 64, DVALUE_Poison, DTYPE_I 8 
        | DTYPE_I 64, DVALUE_Poison, DTYPE_I 32 =>
          Conv_Pure DVALUE_Poison

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Zext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32 
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64 
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          Conv_Pure (DVALUE_I64 (repr (unsigned i1)))

        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 8
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 32 
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 32
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 64
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 64 
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 64 =>
          Conv_Pure DVALUE_Poison

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Sext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          Conv_Pure (DVALUE_I8 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32 
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          Conv_Pure (DVALUE_I32 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64 
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          Conv_Pure (DVALUE_I64 (repr (signed i1)))

        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 8
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 32 
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 32
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 64
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 64 
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 64 =>
          Conv_Pure DVALUE_Poison

        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Bitcast =>
        match t1, x, t2 with
        | DTYPE_I bits1, x, DTYPE_I bits2 =>
          if bits1 =? bits2 then Conv_Pure x else Conv_Illegal "unequal bitsize in cast"
        | DTYPE_Pointer, DVALUE_Addr a, DTYPE_Pointer =>
          Conv_Pure (DVALUE_Addr a)
        | DTYPE_Pointer, DVALUE_Poison, DTYPE_Pointer =>
          Conv_Pure DVALUE_Poison
        | _, _, _ => Conv_Illegal "ill-typed conv"
        end

      | Uitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          Conv_Pure (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          Conv_Pure (DVALUE_Double (Float.of_longu (repr (unsigned i1))))

        | DTYPE_I 1, DVALUE_Poison, DTYPE_Float 
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Float 
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Float 
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Float 
        | DTYPE_I 1, DVALUE_Poison, DTYPE_Double 
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Double 
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Double 
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Double =>
          Conv_Pure DVALUE_Poison

        | _, _, _ => Conv_Illegal "ill-typed Uitofp"
        end

      | Sitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          Conv_Pure (DVALUE_Float (Float32.of_intu (repr (signed i1))))

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          Conv_Pure (DVALUE_Double (Float.of_longu (repr (signed i1))))

        | DTYPE_I 1, DVALUE_Poison, DTYPE_Float 
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Float 
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Float 
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Float 
        | DTYPE_I 1, DVALUE_Poison, DTYPE_Double 
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Double 
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Double 
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Double =>
          Conv_Pure DVALUE_Poison

        | _, _, _ => Conv_Illegal "ill-typed Sitofp"
        end

      | Inttoptr =>
        match t1, t2 with
        | DTYPE_I 64, DTYPE_Pointer => Conv_ItoP x
        | _, _ => Conv_Illegal "ERROR: Inttoptr got illegal arguments"
        end
      | Ptrtoint =>
        match t1, t2 with
        | DTYPE_Pointer, DTYPE_I _ => Conv_PtoI x
        | _, _ => Conv_Illegal "ERROR: Ptrtoint got illegal arguments"
        end
          
      | Fptoui
      | Fptosi
      | Fptrunc
      | Fpext
        => Conv_Illegal "TODO: unimplemented numeric conversion"
      end.
    Arguments get_conv_case _ _ _ _ : simpl nomatch.

    Definition eval_conv_h conv (t1:dtyp) (x:dvalue) (t2:dtyp) : itree conv_E dvalue :=
      match get_conv_case conv t1 x t2 with
      | Conv_Pure x => ret x
      | Conv_ItoP x => trigger (ItoP x)
      | Conv_PtoI x => trigger (PtoI t2 x)
      | Conv_Illegal s => raise s
      end.

    Definition eval_conv (conv : conversion_type) (t1 : dtyp) (x : dvalue) (t2:dtyp) : itree conv_E dvalue :=
      match t1, x with
      | _, _ => eval_conv_h conv t1 x t2
      end.
    Arguments eval_conv _ _ _ _ : simpl nomatch.

  End CONVERSIONS.

  Definition dv_zero_initializer (t:dtyp) : err dvalue :=
    default_dvalue_of_dtyp t.

  (** ** Ident lookups
      Look-ups depend on the nature of the [ident], that may be local or global.
      In each case, we simply trigger the corresponding read event.
      Note: global maps contain [dvalue]s, while local maps contain [uvalue]s.
      We perform the conversion here.
   *)
  Definition lookup_id (i:ident) : itree lookup_E uvalue :=
    match i with
    | ID_Global x => dv <- trigger (GlobalRead x);; ret (dvalue_to_uvalue dv)
    | ID_Local x  => trigger (LocalRead x)
    end.

  (* Predicate testing whether a [dvalue] is equal to zero at its type *)
  Definition dvalue_is_zero (dv : dvalue) : Prop :=
    match dv with
    | DVALUE_I1 x     => x = zero
    | DVALUE_I8 x     => x = zero
    | DVALUE_I32 x    => x = zero
    | DVALUE_I64 x    => x = zero
    | DVALUE_Double x => x = Float.zero
    | DVALUE_Float x  => x = Float32.zero
    | _               => False
    end.

  Definition dvalue_not_zero dv := ~ (dvalue_is_zero dv).

  (* A trivially concrete [uvalue] does not need to go through a pick event to get concretize.
     This function therefore either trigger [pick], or perform a direct cast.
     The value of this "optimization" is debatable. *)
  Definition concretize_or_pick {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (uv : uvalue) (P : Prop) : itree E dvalue :=
    if is_concrete uv
    then lift_err ret (uvalue_to_dvalue uv)
    else trigger (pick uv P).
  
  (* Pick a possibly poison value, treating poison as nondeterminism.
     This is used for freeze. *)
  Definition pick_your_poison {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (dt : dtyp) (uv : uvalue) : itree E dvalue :=
    match uv with
    | UVALUE_Poison => concretize_or_pick (UVALUE_Undef dt) True
    | _             => concretize_or_pick uv True
    end.

  Definition pickUnique {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (uv : uvalue) : itree E dvalue
    := concretize_or_pick uv (unique_prop uv).

  (** ** Denotation of expressions
      [denote_exp top o] is the main entry point for evaluating itree expressions.
      top : the type at which the expression should be evaluated (if any)
      o   : the expression to be evaluated
      INVARIANT:
       - top may be None only for
        + EXP_Ident
        + OP_* cases

     Note that when top is Some t, the resulting dvalue can never be a function pointer
     for a well-typed itree program.

     Expressions are denoted as itrees that return a [uvalue].
 *)
  Fixpoint denote_exp
           (top:option dtyp) (o:exp dtyp) {struct o} : itree exp_E uvalue :=
        let eval_texp '(dt,ex) := denote_exp (Some dt) ex
        in
        match o with

        (* The translation injects the [lookup_E] interface used by [lookup_id] to the ambient one *)
        | EXP_Ident i =>
          translate LU_to_exp (lookup_id i)

        | EXP_Integer x =>
          match top with
          | None                => raise "denote_exp given untyped EXP_Integer"
          | Some (DTYPE_I bits) => lift_undef_or_err ret (fmap dvalue_to_uvalue (coerce_integer_to_int bits x))
          | Some typ            => raise ("bad type for constant int: " ++ to_string typ)
          end

        | EXP_Float x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Float"
          | Some DTYPE_Float  => ret (UVALUE_Float x)
          | _                 => raise "bad type for constant float"
          end

        | EXP_Double x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Double"
          | Some DTYPE_Double => ret (UVALUE_Double x)
          | _                 => raise "bad type for constant double"
          end

        | EXP_Hex x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Hex"
          | Some DTYPE_Float  => ret (UVALUE_Float (Float32.of_double x))
          | Some DTYPE_Double => ret (UVALUE_Double x)
          | _                 => raise "bad type for constant hex float"
          end

        | EXP_Bool b =>
          match b with
          | true  => ret (UVALUE_I1 one)
          | false => ret (UVALUE_I1 zero)
          end

        | EXP_Null => ret (UVALUE_Addr A.null)

        | EXP_Zero_initializer =>
          match top with
          | None   => raise "denote_exp given untyped EXP_Zero_initializer"
          | Some t => lift_err ret (fmap (F :=err) dvalue_to_uvalue (dv_zero_initializer t))
          end

        | EXP_Cstring es =>
          vs <- map_monad eval_texp es ;;
          ret (UVALUE_Array vs)

        | EXP_Undef =>
          match top with
          | None   => raise "denote_exp given untyped EXP_Undef"
          | Some t => ret (UVALUE_Undef t)
          end

        (* Question: should we do any typechecking for aggregate types here? *)
        (* Option 1: do no typechecking: *)
        | EXP_Struct es =>
          vs <- map_monad eval_texp es ;;
          ret (UVALUE_Struct vs)

        | EXP_Array es =>
          vs <- map_monad eval_texp es ;;
          ret (UVALUE_Array vs)

        (* The semantics of operators is complicated by both uvalues and *)
        (*    undefined behaviors. *)
        (*    We denote each operands first, but the denotation of the operator itself *)
        (*    depends on whether it may raise UB, and how. *)
        (*  *)
        | OP_IBinop iop dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          ret (UVALUE_IBinop iop v1 v2)

        | OP_ICmp cmp dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          ret (UVALUE_ICmp cmp v1 v2)

        | OP_Conversion conv dt_from op dt_to =>
          v <- denote_exp (Some dt_from) op ;;
          ret (UVALUE_Conversion conv dt_from v dt_to)

        | OP_GetElementPtr dt1 (dt2, ptrval) idxs =>
          vptr <- denote_exp (Some dt2) ptrval ;;
          vs <- map_monad (fun '(dt, index) => denote_exp (Some dt) index) idxs ;;
          ret (UVALUE_GetElementPtr dt1 vptr vs)
        end.
  Arguments denote_exp _ : simpl nomatch.

  Definition denote_op (o:exp dtyp) : itree exp_E uvalue :=
    denote_exp None o.
  Arguments denote_op _ : simpl nomatch.

      (* An instruction has only side-effects, it therefore returns [unit] *)
      Definition denote_instr
                 (i: (instr_id * instr dtyp)): itree instr_E unit :=
        match i with
        (* Pure operations *)
        | (IId id, INSTR_Op op) =>
          dv <- translate exp_to_instr (denote_op op) ;;
          trigger (LocalWrite id dv)

        (* Allocation *)
        | (IId id, INSTR_Alloca dt _ _) =>
          dv <- trigger (Alloca dt);;
          trigger (LocalWrite id (dvalue_to_uvalue dv))

        (* Load *)
        | (IId id, INSTR_Load _ dt (du,ptr) _) =>
          ua <- translate exp_to_instr (denote_exp (Some du) ptr) ;;
          da <- concretize_or_pick ua True ;;
          if (@dvalue_eq_dec da DVALUE_Poison)
          then raiseUB "Load from poisoned address."
          else dv <- trigger (Load dt da);;
                trigger (LocalWrite id dv)

        (* Store *)
        | (IVoid _, INSTR_Store _ (dt, val) (DTYPE_Pointer, ptr) _) =>
          uv <- translate exp_to_instr (denote_exp (Some dt) val) ;;
          dv <- concretize_or_pick uv True ;;
          if (dvalue_has_dtyp_fun dv dt) then
          (ua <- translate exp_to_instr
                  (denote_exp (Some DTYPE_Pointer) ptr) ;;
            da <- pickUnique ua ;;
            if (@dvalue_eq_dec da DVALUE_Poison)
            then raiseUB "Store to poisoned address."
            else trigger (Store da dv))
          else
            raise "Ill-typed store instruction"

        | (_, INSTR_Store _ _ _ _) =>
            raise "ILL-FORMED itree ERROR: Store to non-void ID or
                    Ill-typed Store"

        (* Call *)
        | (pt, INSTR_Call (dt, f) args attrs) =>
          uvs <- map_monad (fun '(t, op) => (translate exp_to_instr (denote_exp (Some t) op))) args ;;
          fv <- translate exp_to_instr (denote_exp None f) ;;
          fv <- concretize_or_pick fv True ;;
          returned_value <- trigger (Call dt fv uvs attrs) ;;
          match pt with
          | IVoid _ => ret tt
          | IId id  => trigger (LocalWrite id returned_value)
          end

        | (IVoid _, INSTR_Comment _) => ret tt

        (* Currently unhandled itree instructions *)
        | (_, INSTR_Fence)
        | (_, INSTR_AtomicCmpXchg)
        | (_, INSTR_AtomicRMW)
        | (_, INSTR_VAArg)
        | (_, INSTR_LandingPad) => raise "Unsupported VIR instruction"

        (* Error states *)
        | (_, _) => raise "ID / Instr mismatch void/non-void"
        end.

      (* Computes the label to be returned by a switch terminator, after evaluation of values
         assuming already neither poison nor undef for the selector *)
      Fixpoint select_switch
               (value : dvalue) (default_dest : block_id)
               (switches : list (dvalue * block_id)) : err block_id :=
        match switches with
        | [] => ret default_dest
        | (v,id):: switches =>
          match value, v with
          | DVALUE_I1 i1, DVALUE_I1 i2    
          | DVALUE_I8 i1, DVALUE_I8 i2   
          | DVALUE_I32 i1, DVALUE_I32 i2
          | DVALUE_I64 i1, DVALUE_I64 i2
            => if cmp Ceq i1 i2
              then ret id
              else select_switch value default_dest switches
          | _,_ => failwith "Ill-typed switch."
          end
        end.

      Definition dvalue_is_poison (dv : dvalue) : bool :=
        match dv with
        | DVALUE_Poison => true
        | _ => false
        end.

      (* A [terminator] either returns from a function call, producing a [dvalue],
         or jumps to a new [block_id]. *)
      Definition denote_terminator (t: terminator dtyp): itree exp_E (block_id + uvalue) :=
        match t with

        | TERM_Ret (dt, op) =>
          dv <- denote_exp (Some dt) op ;;
          ret (inr dv)

        | TERM_Ret_void =>
          ret (inr UVALUE_None)

        | TERM_Br (dt,op) br1 br2 =>
          uv <- denote_exp (Some dt) op ;;
          dv <- concretize_or_pick uv True ;; 
          match dv with
          | DVALUE_I1 comparison_bit =>
            if equ comparison_bit one then
              ret (inl br1)
            else
              ret (inl br2)
          | DVALUE_Poison => raiseUB "Branching on poison."
          | _ => raise "Br got non-bool value"
          end

        | TERM_Br_1 br => ret (inl br)

        | TERM_Unreachable => raiseUB "IMPOSSIBLE: unreachable in reachable position" 

        (* Currently unhandled VIR terminators *)
        | TERM_Switch _ _ _
        | TERM_IndirectBr _ _
        | TERM_Resume _
        | TERM_Invoke _ _ _ _ => raise "Unsupport itree terminator"
        end.

      (* Denoting a list of instruction simply binds the trees together *)
      Definition denote_code (c: code dtyp): itree instr_E unit :=
        map_monad_ denote_instr c.

      Definition denote_phi (bid_from : block_id) (id_p : local_id * phi dtyp) : itree exp_E (local_id * uvalue) :=
        let '(id, Phi dt args) := id_p in
        match assoc bid_from args with
        | Some op =>
          uv <- denote_exp (Some dt) op ;;
          ret (id,uv)
        | None => raise ("jump: phi node doesn't include block ")
        end.

      Definition denote_phis (bid_from: block_id) (phis: list (local_id * phi dtyp)): itree instr_E unit :=
        dvs <- Util.map_monad
                (fun x => translate exp_to_instr (denote_phi bid_from x))
                phis;;
        Util.map_monad (fun '(id,dv) => trigger (LocalWrite id dv)) dvs ;;
        ret tt.

      (* A block ends with a terminator, it either jumps to another block,
         or returns a dynamic value *)
      Definition denote_block (b: block dtyp) (bid_from : block_id) : itree instr_E (block_id + uvalue) :=
        denote_phis bid_from (blk_phis b);;
        denote_code (blk_code b);;
        translate exp_to_instr (denote_terminator (blk_term b)).

      (* Our denotation currently contains two kinds of indirections: jumps to labels, internal to
         a cfg, and calls to functions, that jump from a cfg to another.
         In order to denote a single [cfg], we tie the first knot by linking together all the blocks
         contain in the [cfg].
         Note that contrary to calls, no events have been explicitely introduced for internal jumps.
         This is due to the _tail recursive_ nature of these jumps: they only occur as the last
         instruction of blocks. We hence can use a [loop] operator to do the linking, as opposed
         to the more general [mrec] operator that will be used to link internal calls.

         The idea here is simply to enter the body through the [init] [block_id] of the [cfg].
         As long as the computation returns a new label to jump to, we feed it back to the loop.
         If it ever returns a dynamic value, we exit the loop by returning the [dvalue].
       *)
      Definition denote_ocfg (bks: ocfg dtyp)
        : (block_id * block_id) -> itree instr_E ((block_id * block_id) + uvalue) :=
        iter (C := ktree _) (bif := sum)
             (fun '((bid_from,bid_src) : block_id * block_id) => 
                match find_block bks bid_src with
                | None => ret (inr (inl (bid_from,bid_src)))
                | Some block_src =>
                  bd <- denote_block block_src bid_from;;
                  match bd with
                  | inr dv => ret (inr (inr dv))
                  | inl bid_target => ret (inl (bid_src,bid_target))
                  end
                end).

     Definition denote_cfg (f: cfg dtyp) : itree instr_E uvalue :=
        r <- denote_ocfg (blks f) (init f,init f) ;;
        match r with
        | inl bid => raise ("Can't find block in denote_cfg " ++ to_string (snd bid))
        | inr uv  => ret uv
        end.

      Fixpoint combine_lists_err {A B:Type} (l1:list A) (l2:list B) : err (list (A * B)) :=
        match l1, l2 with
        | [], [] => ret []
        | x::xs, y::ys =>
          l <- combine_lists_err xs ys ;;
            ret ((x,y)::l)
        | _, _ =>
          (* YZ: This should be a failure, but we first need to have a proper
          story to handle main arguments since at the moment we expect exactly
          argc and argv, and feed default values to them *)
          (* failwith "combine_lists_err: different length lists" *)
          ret []
        end.

      (* The denotation of an itree function is a coq function that takes
         a list of uvalues and returns the appropriate semantics. *)
      Definition function_denotation : Type :=
        list uvalue -> itree L0' uvalue.

      Definition denote_function (df:definition dtyp (cfg dtyp)) : function_denotation :=
        fun (args : list uvalue) =>
          (* We match the arguments variables to the inputs *)
          bs <-
            (* Allow only full application of functions *)
            (if Nat.eqb (List.length (df_args df)) (List.length args) then
              ret (List.combine (df_args df) args)
             else raise ("Incorrect argument length for function")) ;;
          (* generate the corresponding writes to the local stack frame *)
          trigger MemPush ;;
          trigger (StackPush bs) ;;
          rv <- translate instr_to_L0' (denote_cfg (df_instrs df)) ;;
          trigger StackPop ;;
          trigger MemPop ;;
          ret rv.

      (* We now turn to the second knot to be tied: a top-level itree program is a set
         of mutually recursively defined functions, i.e. [cfg]s. We hence need to
         resolve this mutually recursive definition by interpreting away the call events.
         As mentionned above, calls are not tail recursive: we need a more general fixpoint
         operator than [loop], which [mrec] provides.
       *)
      (* A slight complication comes from the fact that not all call events will be interpreted
         away as such. Some of them correspond to external calls -- or to intrinsics -- that will
         be kept uninterpreted for now.
         Since the type of [mrec] forces us to get rid of the [CallE] family of events that we
         interpret, we therefore cast external calls into an isomorphic family of events
         that life in the "right" injection of the [_CFG_INTERNAL] effect
       *)

      Definition lookup_defn {B} := @assoc dvalue B _.

      Definition remove_tag : list fn_attr -> list fn_attr :=
        List.filter (fun attr =>
                      match attr with
                      | FNATTR_Internal
                      | FNATTR_External => false
                      | _ => true
                      end).

      Definition denote_mcfg
                 (fundefs:list (dvalue * definition dtyp (cfg dtyp))) (dt : dtyp)
                 (f_value : dvalue) (args : list uvalue) : itree L0 uvalue :=
        @mrec CallE (ExternalCallE +' _)
              (fun T call =>
                 match call with
                 | Call dt fv args attr =>
                   match (lookup_defn fv fundefs) with
                   | Some f_den => (* If the call is internal *)
                     denote_function (f_den) args
                   | None =>
                     dargs <- map_monad (fun uv => pickUnique uv) args ;;
                     trigger (ExternalCall dt fv (map dvalue_to_uvalue dargs) (remove_tag attr))
                   end
                 end)
              _ (Call dt f_value args []).

End Denotation.
