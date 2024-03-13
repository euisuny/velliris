(* begin hide *)
From Coq Require Import
     ZArith DecidableClass List String Bool.Bool.

Import BinInt.

Require Import Ceres.Ceres.

Require Import Integers Floats.

From Flocq.IEEE754 Require Import
     Bits
     BinarySingleNaN
     Binary.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv
     Structures.Monads
     Data.Monads.EitherMonad
     Structures.Functor
     Data.Nat
     Data.List.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.MemoryAddress.

Import EqvNotation.
Import MonadNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope N_scope.
(* end hide *)


(** * Dynamic values
    Definition of the dynamic values manipulated by VIR.
    They come in two flavors:
    - [dvalue] are the concrete notion of values computed.
    - [uvalue] (_under-defined values_) are an extension of [dvalue] as symbolic values:
      + a special [undef τ] value modeling LLVM's "undef"
      + delayed numerical operations.
 *)

#[global] Instance Eqv_nat : Eqv nat := (@eq nat).

(* Floating-point rounding mode *)
Definition FT_Rounding:mode := mode_NE.

(* Set up representations for for i1, i32, and i64 *)
Module Wordsize1.
  Definition wordsize := 1%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize1.

Module Wordsize8.
  Definition wordsize := 8%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize8.

Module Int1 := Make(Wordsize1).
Module Int8 := Make(Wordsize8).
Module Int32 := Integers.Int.
Module Int64 := Integers.Int64.

Definition int1 := Int1.int.
Definition int8 := Int8.int.
Definition int32 := Int32.int.
Definition int64 := Int64.int.

Definition inttyp (x:N) : Type :=
  match x with
  | 1 => int1
  | 8 => int8
  | 32 => int32
  | 64 => int64
  | _ => False
  end.

Inductive IX_supported : N -> Prop :=
| I1_Supported : IX_supported 1
| I8_Supported : IX_supported 8
| I32_Supported : IX_supported 32
| I64_Supported : IX_supported 64
.

(* TODO: This probably should live somewhere else... *)
#[global,refine] Instance Decidable_eq_N : forall (x y : N), Decidable (eq x y) := {
  Decidable_witness := N.eqb x y
}.
 apply N.eqb_eq.
Qed.

Lemma IX_supported_dec : forall (sz:N), {IX_supported sz} + {~IX_supported sz}.
Proof.
  intros sz.
  - decide (sz = 1)%N.
    + left. subst. constructor.
    + decide (sz = 8)%N.
      * left. subst. constructor.
      * decide (sz = 32).
        -- left. subst. constructor.
        -- decide (sz = 64).
           ++ left. subst. constructor.
           ++ right. intro X.
              inversion X; subst; contradiction.
Qed.

Lemma unsupported_cases : forall {X} (sz : N) (N : ~ IX_supported sz) (x64 x32 x8 x1 x : X),
    (if (sz =? 64) then x64
      else if (sz =? 32) then x32
          else if (sz =? 8) then x8
                else if (sz =? 1) then x1
                    else x) = x.
Proof.
  intros.
  destruct (sz =? 64) eqn: H.
  rewrite N.eqb_eq in H.
  destruct N. rewrite H. constructor.
  destruct (sz =? 32) eqn: H'.
  rewrite N.eqb_eq in H'.
  destruct N. rewrite H'. constructor.
  destruct (sz =? 8) eqn: H''.
  rewrite N.eqb_eq in H''.
  destruct N. rewrite H''. constructor.
  destruct (sz =? 1) eqn: H'''.
  rewrite N.eqb_eq in H'''.
  destruct N. rewrite H'''. constructor.
  reflexivity.
Qed.

Function unsupported_cases_match_ {X} (sz : N) (x64 x32 x8 x1 x : X) :=
    match sz with
    | 64 => x64
    | 32 => x32
    | 8 => x8
    | 1 => x1
    | _ => x
    end.

Lemma unsupported_cases_match : forall {X} (sz : N) (N : ~ IX_supported sz) (x64 x32 x8 x1 x : X),
    match sz with
    | 64 => x64
    | 32 => x32
    | 8 => x8
    | 1 => x1
    | _ => x
    end = x.
Proof.
  intros.
  change ((unsupported_cases_match_ sz x64 x32 x8 x1 x) = x).
  revert N.
  apply unsupported_cases_match__ind; intros.
  - assert False. apply N.  econstructor. inversion H.
  - assert False. apply N.  econstructor. inversion H.
  - assert False. apply N.  econstructor. inversion H.
  - assert False. apply N.  econstructor. inversion H.
  - reflexivity.
Qed.


Definition ll_float  := Floats.float32.
Definition ll_double := Floats.float.

Module DVALUE(A:Vellvm.Semantics.MemoryAddress.ADDRESS).

  (* The set of dynamic values manipulated by an LLVM program. *)
 Unset Elimination Schemes.
Inductive dvalue : Set :=
| DVALUE_Addr (a:A.addr)
| DVALUE_I1 (x:int1)
| DVALUE_I8 (x:int8)
| DVALUE_I32 (x:int32)
| DVALUE_I64 (x:int64)
| DVALUE_Double (x:ll_double)
| DVALUE_Float (x:ll_float)
| DVALUE_Poison
| DVALUE_None
| DVALUE_Struct        (fields: list dvalue)
| DVALUE_Array         (elts: list dvalue)
.
Set Elimination Schemes.

Section DvalueInd.
  Variable P : dvalue -> Prop.
  Hypothesis IH_Addr          : forall a, P (DVALUE_Addr a).
  Hypothesis IH_I1            : forall x, P (DVALUE_I1 x).
  Hypothesis IH_I8            : forall x, P (DVALUE_I8 x).
  Hypothesis IH_I32           : forall x, P (DVALUE_I32 x).
  Hypothesis IH_I64           : forall x, P (DVALUE_I64 x).
  Hypothesis IH_Double        : forall x, P (DVALUE_Double x).
  Hypothesis IH_Float         : forall x, P (DVALUE_Float x).
  Hypothesis IH_Poison        : P DVALUE_Poison.
  Hypothesis IH_None          : P DVALUE_None.
  Hypothesis IH_Struct        : forall (fields: list dvalue), (forall u, In u fields -> P u) -> P (DVALUE_Struct fields).
  Hypothesis IH_Array         : forall (elts: list dvalue), (forall e, In e elts -> P e) -> P (DVALUE_Array elts).

  Lemma dvalue_ind : forall (dv:dvalue), P dv.
    fix IH 1.
    remember P as P0 in IH.
    destruct dv; auto; subst.
    - apply IH_Struct.
      { revert fields.
        fix IHfields 1. intros [|u fields']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
      }
    - apply IH_Array.
      { revert elts.
        fix IHelts 1. intros [|u elts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
      }
  Qed.
End DvalueInd.


(* The set of dynamic values manipulated by an LLVM program. *)
Unset Elimination Schemes.
Inductive uvalue : Type :=
| UVALUE_Addr (a:A.addr)
| UVALUE_I1 (x:int1)
| UVALUE_I8 (x:int8)
| UVALUE_I32 (x:int32)
| UVALUE_I64 (x:int64)
| UVALUE_Double (x:ll_double)
| UVALUE_Float (x:ll_float)
| UVALUE_Undef (t:dtyp)
| UVALUE_Poison
| UVALUE_None
| UVALUE_Struct        (fields: list uvalue)
| UVALUE_Array         (elts: list uvalue)
| UVALUE_IBinop           (iop:ibinop) (v1:uvalue) (v2:uvalue)
| UVALUE_ICmp             (cmp:icmp)   (v1:uvalue) (v2:uvalue)
| UVALUE_FBinop           (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue)
| UVALUE_FCmp             (cmp:fcmp)   (v1:uvalue) (v2:uvalue)
| UVALUE_Conversion       (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp)
| UVALUE_GetElementPtr    (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)) (* TODO: do we ever need this? GEP raises an event? *)
| UVALUE_ExtractElement   (vec_typ : dtyp) (vec: uvalue) (idx: uvalue)
| UVALUE_InsertElement    (vec_typ : dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue)
| UVALUE_ShuffleVector    (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue)
| UVALUE_ExtractValue     (vec_typ : dtyp) (vec:uvalue) (idxs:list LLVMAst.int)
| UVALUE_InsertValue      (vec_typ : dtyp) (vec:uvalue) (elt:uvalue) (idxs:list LLVMAst.int)
| UVALUE_Select           (cnd:uvalue) (v1:uvalue) (v2:uvalue)
(* Extract the `idx` byte from a uvalue `uv`, which was stored with
  type `dt`. `idx` 0 is the least significant byte. `sid` is the "store
  id". *)
.
Set Elimination Schemes.

Section UvalueInd.
  Variable P : uvalue -> Prop.
  Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a).
  Hypothesis IH_I1             : forall x, P (UVALUE_I1 x).
  Hypothesis IH_I8             : forall x, P (UVALUE_I8 x).
  Hypothesis IH_I32            : forall x, P (UVALUE_I32 x).
  Hypothesis IH_I64            : forall x, P (UVALUE_I64 x).
  Hypothesis IH_Double         : forall x, P (UVALUE_Double x).
  Hypothesis IH_Float          : forall x, P (UVALUE_Float x).
  Hypothesis IH_Undef          : forall t, P (UVALUE_Undef t).
  Hypothesis IH_Poison         : P UVALUE_Poison.
  Hypothesis IH_None           : P UVALUE_None.
  Hypothesis IH_Struct         : forall (fields: list uvalue), (forall u, In u fields -> P u) -> P (UVALUE_Struct fields).
  Hypothesis IH_Array          : forall (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Array elts).
  Hypothesis IH_IBinop         : forall (iop:ibinop) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_IBinop iop v1 v2).
  Hypothesis IH_ICmp           : forall (cmp:icmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_ICmp cmp v1 v2).
  Hypothesis IH_FBinop         : forall (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FBinop fop fm v1 v2).
  Hypothesis IH_FCmp           : forall (cmp:fcmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FCmp cmp v1 v2).
  Hypothesis IH_Conversion     : forall (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp), P v -> P (UVALUE_Conversion conv t_from v t_to).
  Hypothesis IH_GetElementPtr  : forall (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)), P ptrval -> (forall idx, In idx idxs -> P idx) -> P (UVALUE_GetElementPtr t ptrval idxs).
  Hypothesis IH_ExtractElement : forall (t:dtyp) (vec: uvalue) (idx: uvalue), P vec -> P idx -> P (UVALUE_ExtractElement t vec idx).
  Hypothesis IH_InsertElement  : forall (t:dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue), P vec -> P elt -> P idx -> P (UVALUE_InsertElement t vec elt idx).
  Hypothesis IH_ShuffleVector  : forall (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue), P vec1 -> P vec2 -> P idxmask -> P (UVALUE_ShuffleVector vec1 vec2 idxmask).
  Hypothesis IH_ExtractValue   : forall (t:dtyp) (vec:uvalue) (idxs:list LLVMAst.int), P vec -> P (UVALUE_ExtractValue t vec idxs).
  Hypothesis IH_InsertValue    : forall (t:dtyp) (vec:uvalue) (elt:uvalue) (idxs:list LLVMAst.int), P vec -> P elt -> P (UVALUE_InsertValue t vec elt idxs).
  Hypothesis IH_Select         : forall (cnd:uvalue) (v1:uvalue) (v2:uvalue), P cnd -> P v1 -> P v2 -> P (UVALUE_Select cnd v1 v2).

  Lemma uvalue_ind : forall (uv:uvalue), P uv.
    fix IH 1.
    remember P as P0 in IH.
    destruct uv; auto; subst.
    - apply IH_Struct.
      { revert fields.
        fix IHfields 1. intros [|u fields']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
      }
    - apply IH_Array.
      { revert elts.
        fix IHelts 1. intros [|u elts']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
      }
    - apply IH_IBinop; auto.
    - apply IH_ICmp; auto.
    - apply IH_FBinop; auto.
    - apply IH_FCmp; auto.
    - apply IH_Conversion; auto.
    - apply IH_GetElementPtr. apply IH.
      { revert idxs.
        fix IHidxs 1. intros [|u idxs']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHidxs. apply Hin.
      }
    - apply IH_ExtractElement; auto.
    - apply IH_InsertElement; auto.
    - apply IH_ShuffleVector; auto.
    - apply IH_ExtractValue; auto.
    - apply IH_InsertValue; auto.
    - apply IH_Select; auto.
  Qed.
End UvalueInd.

(* Injection of [dvalue] into [uvalue] *)
Fixpoint dvalue_to_uvalue (dv : dvalue) : uvalue :=
  match dv with
  | DVALUE_Addr a => UVALUE_Addr a
  | DVALUE_I1 x => UVALUE_I1 x
  | DVALUE_I8 x => UVALUE_I8 x
  | DVALUE_I32 x => UVALUE_I32 x
  | DVALUE_I64 x => UVALUE_I64 x
  | DVALUE_Double x => UVALUE_Double x
  | DVALUE_Float x => UVALUE_Float x
  | DVALUE_Poison => UVALUE_Poison
  | DVALUE_None => UVALUE_None
  | DVALUE_Struct fields => UVALUE_Struct (map dvalue_to_uvalue fields)
  | DVALUE_Array elts => UVALUE_Array (map dvalue_to_uvalue elts)
  end.

(* Partial injection of [uvalue] into [dvalue] *)
Fixpoint uvalue_to_dvalue (uv : uvalue) : err dvalue :=
  match uv with
  | UVALUE_Addr a                          => ret (DVALUE_Addr a)
  | UVALUE_I1 x                            => ret (DVALUE_I1 x)
  | UVALUE_I8 x                            => ret (DVALUE_I8 x)
  | UVALUE_I32 x                           => ret (DVALUE_I32 x)
  | UVALUE_I64 x                           => ret (DVALUE_I64 x)
  | UVALUE_Double x                        => ret (DVALUE_Double x)
  | UVALUE_Float x                         => ret (DVALUE_Float x)
  | UVALUE_Undef t                         => failwith "Attempting to convert a non-defined uvalue to dvalue. The conversion should be guarded by is_concrete"
  | UVALUE_Poison                          => ret (DVALUE_Poison)
  | UVALUE_None                            => ret (DVALUE_None)

  | UVALUE_Struct fields                   =>
    fields' <- map_monad uvalue_to_dvalue fields ;;
    ret (DVALUE_Struct fields')


  | UVALUE_Array elts                      =>
    elts' <- map_monad uvalue_to_dvalue elts ;;
    ret (DVALUE_Array elts')

  | _ => failwith "Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen"
end.

Lemma uvalue_to_dvalue_of_dvalue_to_uvalue :
  forall (d : dvalue),
    uvalue_to_dvalue (dvalue_to_uvalue d) = inr d.
Proof.
  intros.
  induction d; auto.
  - cbn. induction fields. cbn. reflexivity.
    assert (forall u : dvalue,
               In u fields ->
               uvalue_to_dvalue (dvalue_to_uvalue u) = inr u).
    intros. apply H. apply in_cons; auto. specialize (IHfields H0).
    clear H0. rewrite map_cons. rewrite list_cons_app.
    rewrite map_monad_app. cbn.
    destruct (map_monad uvalue_to_dvalue (map dvalue_to_uvalue fields)) eqn: EQ.
    + discriminate IHfields.
    + rewrite H. cbn. inversion IHfields. reflexivity.
      constructor; auto.
  - cbn. induction elts. cbn. reflexivity.
    assert (forall u : dvalue,
               In u elts ->
               uvalue_to_dvalue (dvalue_to_uvalue u) = inr u).
    intros. apply H. apply in_cons; auto. specialize (IHelts H0).
    clear H0. rewrite map_cons. rewrite list_cons_app.
    rewrite map_monad_app. cbn.
    destruct (map_monad uvalue_to_dvalue (map dvalue_to_uvalue elts)) eqn: EQ.
    + discriminate IHelts.
    + rewrite H. cbn. inversion IHelts. reflexivity.
      constructor; auto.
Qed.


(* returns true iff the uvalue contains no occurrence of UVALUE_Undef. *)
Fixpoint is_concrete (uv : uvalue) : bool :=
  match uv with
  | UVALUE_Addr a => true
  | UVALUE_I1 x => true
  | UVALUE_I8 x => true
  | UVALUE_I32 x => true
  | UVALUE_I64 x => true
  | UVALUE_Double x => true
  | UVALUE_Float x => true
  | UVALUE_Undef t => false
  | UVALUE_Poison => true
  | UVALUE_None => true
  | UVALUE_Struct fields => forallb is_concrete fields
  | UVALUE_Array elts => forallb is_concrete elts
  | _ => false
  end.

(* If both operands are concrete, uvalue_to_dvalue them and run them through
   opd, else run the abstract ones through opu *)
Definition uvalue_to_dvalue_binop {A : Type}
           (opu : uvalue -> uvalue -> A) (opd : dvalue -> dvalue -> A) (uv1 uv2 : uvalue) : A :=
  let ma := dv1 <- uvalue_to_dvalue uv1 ;; dv2 <- uvalue_to_dvalue uv2 ;; ret (opd dv1 dv2)
  in match ma with
     | inl e => opu uv1 uv2
     | inr a => a
     end.

(* Like uvalue_to_dvalue_binop, but the second operand is already concrete *)
Definition uvalue_to_dvalue_binop2 {A : Type}
           (opu : uvalue -> uvalue -> A) (opd : dvalue -> dvalue -> A) (uv1 : uvalue) (dv2 : dvalue) : A :=
  let ma := dv1 <- uvalue_to_dvalue uv1 ;; ret (opd dv1 dv2)
  in match ma with
     | inl e => opu uv1 (dvalue_to_uvalue dv2)
     | inr a => a
     end.

Definition uvalue_to_dvalue_uop {A : Type}
           (opu : uvalue -> A) (opd : dvalue -> A) (uv : uvalue) : A :=
  let ma := dv <- uvalue_to_dvalue uv ;; ret (opd dv)
  in match ma with
     | inl e => opu uv
     | inr a => a
     end.

Section hiding_notation.
  #[local] Open Scope sexp_scope.

  Fixpoint serialize_dvalue' (dv:dvalue): sexp :=
    match dv with
    | DVALUE_Addr a => Atom "address" (* TODO: insist that memory models can print addresses? *)
    | DVALUE_I1 x => Atom "dvalue(i1)"
    | DVALUE_I8 x => Atom "dvalue(i8)"
    | DVALUE_I32 x => Atom "dvalue(i32)"
    | DVALUE_I64 x => Atom "dvalue(i64)"
    | DVALUE_Double x => Atom "dvalue(double)"
    | DVALUE_Float x => Atom "dvalue(float)"
    | DVALUE_Poison => Atom "poison"
    | DVALUE_None => Atom "none"
    | DVALUE_Struct fields
      => [Atom "{" ; to_sexp (List.map (fun x => [serialize_dvalue' x ; Atom ","]) fields) ; Atom "}"]
    | DVALUE_Array elts
      => [Atom "[" ; to_sexp (List.map (fun x => [serialize_dvalue' x ; Atom ","]) elts) ; Atom "]"]
    end.

  #[global] Instance serialize_dvalue : Serialize dvalue := serialize_dvalue'.

  Fixpoint serialize_uvalue' (pre post: string) (uv:uvalue): sexp :=
    match uv with
    | UVALUE_Addr a => Atom (pre ++ "address" ++ post)%string (* TODO: insist that memory models can print addresses? *)
    | UVALUE_I1 x => Atom (pre ++ "uvalue(i1)" ++ post)%string
    | UVALUE_I8 x => Atom (pre ++ "uvalue(i8)" ++ post)%string
    | UVALUE_I32 x => Atom (pre ++ "uvalue(i32)" ++ post)%string
    | UVALUE_I64 x => Atom (pre ++ "uvalue(i64)" ++ post)%string
    | UVALUE_Double x => Atom (pre ++ "uvalue(double)" ++ post)%string
    | UVALUE_Float x => Atom (pre ++ "uvalue(float)" ++ post)%string
    | UVALUE_Poison => Atom (pre ++ "poison" ++ post)%string
    | UVALUE_None => Atom (pre ++ "none" ++ post)%string
    | UVALUE_Struct fields
      => [Atom "{" ; to_sexp (List.map (serialize_uvalue' "" ",") fields) ; Atom "}"]
    | UVALUE_Array elts
      => [Atom "[" ; to_sexp (List.map (serialize_uvalue' "" ",") elts) ; Atom "]"]
    | UVALUE_Undef t => [Atom "undef(" ; to_sexp t ; Atom ")"]
    | UVALUE_IBinop iop v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp iop ; serialize_uvalue' "" ")" v2]
    | UVALUE_ICmp cmp v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp cmp; serialize_uvalue' "" ")" v2]
    | UVALUE_FBinop fop _ v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp fop; serialize_uvalue' "" ")" v2]
    | UVALUE_FCmp cmp v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp cmp; serialize_uvalue' "" ")" v2]
    | _ => Atom "TODO: show_uvalue"
    end.

  #[global] Instance serialize_uvalue : Serialize uvalue := serialize_uvalue' "" "".

End hiding_notation.

Ltac dec_dvalue :=
  match goal with
  | [ |- { ?X ?a = ?X ?b} + { ?X ?a <> ?X ?b} ] => idtac
  | [ |- { ?X ?a = ?Y ?b} + { ?X ?a <> ?Y ?b} ] => right; intros H; inversion H
  | [ |- { ?X = ?X } + { ?X <> ?X } ] => left; reflexivity
  | [ |- { ?X = ?Y } + { ?X <> ?Y } ] => right; intros H; inversion H
  end.

Section DecidableEquality.

  Fixpoint dvalue_eqb (d1 d2:dvalue) : bool :=
    let lsteq := list_eqb (Build_RelDec eq dvalue_eqb) in
    match d1, d2 with
    | DVALUE_Addr a1, DVALUE_Addr a2 =>
      if A.eq_dec a1 a2 then true else false
    | DVALUE_I1 x1, DVALUE_I1 x2 =>
      if Int1.eq_dec x1 x2 then true else false
    | DVALUE_I8 x1, DVALUE_I8 x2 =>
      if Int8.eq_dec x1 x2 then true else false
    | DVALUE_I32 x1, DVALUE_I32 x2 =>
      if Int32.eq_dec x1 x2 then true else false
    | DVALUE_I64 x1, DVALUE_I64 x2 =>
      if Int64.eq_dec x1 x2 then true else false
    | DVALUE_Double x1, DVALUE_Double x2 =>
      if Float.eq_dec x1 x2 then true else false
    | DVALUE_Float x1, DVALUE_Float x2 =>
      if Float32.eq_dec x1 x2 then true else false
    | DVALUE_Poison, DVALUE_Poison => true
    | DVALUE_None, DVALUE_None => true
    | DVALUE_Struct f1, DVALUE_Struct f2 =>
      lsteq f1 f2
    | DVALUE_Array f1, DVALUE_Array f2 =>
      lsteq f1 f2
    | _, _ => false
    end.

  Lemma dvalue_eq_dec : forall (d1 d2:dvalue), {d1 = d2} + {d1 <> d2}.
    refine (fix f d1 d2 :=
    let lsteq_dec := list_eq_dec f in
    match d1, d2 with
    | DVALUE_Addr a1, DVALUE_Addr a2 => _
    | DVALUE_I1 x1, DVALUE_I1 x2 => _
    | DVALUE_I8 x1, DVALUE_I8 x2 => _
    | DVALUE_I32 x1, DVALUE_I32 x2 => _
    | DVALUE_I64 x1, DVALUE_I64 x2 => _
    | DVALUE_Double x1, DVALUE_Double x2 => _
    | DVALUE_Float x1, DVALUE_Float x2 => _
    | DVALUE_Poison, DVALUE_Poison => _
    | DVALUE_None, DVALUE_None => _
    | DVALUE_Struct f1, DVALUE_Struct f2 => _
    | DVALUE_Array f1, DVALUE_Array f2 => _
    | _, _ => _
    end);  ltac:(dec_dvalue).
    - destruct (A.eq_dec a1 a2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int1.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int8.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int32.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Int64.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Float.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (Float32.eq_dec x1 x2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec f1 f2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec f1 f2).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
  Qed.

  #[global] Instance eq_dec_dvalue : RelDec (@eq dvalue) := RelDec_from_dec (@eq dvalue) (@dvalue_eq_dec).
  #[global] Instance eqv_dvalue : Eqv dvalue := (@eq dvalue).
  Hint Unfold eqv_dvalue : core.

	Definition dtyp_eq_dec : forall (t1 t2:dtyp), {t1 = t2} + {t1 <> t2}.
    refine (fix f t1 t2 :=
              let lsteq_dec := list_eq_dec f in
              match t1, t2 with
              | DTYPE_I n, DTYPE_I m => _
              | DTYPE_Pointer, DTYPE_Pointer => _
              | DTYPE_Void, DTYPE_Void => _
              | DTYPE_Half, DTYPE_Half => _
              | DTYPE_Float, DTYPE_Float => _
              | DTYPE_Double, DTYPE_Double => _
              | DTYPE_Fp128, DTYPE_Fp128 => _
              | DTYPE_X86_fp80, DTYPE_X86_fp80 => _
              | DTYPE_Ppc_fp128, DTYPE_Ppc_fp128 => _
              | DTYPE_Metadata, DTYPE_Metadata => _
              | DTYPE_X86_mmx, DTYPE_X86_mmx => _
              | DTYPE_Array n t, DTYPE_Array m t' => _
              | DTYPE_Struct l, DTYPE_Struct l' => _
              | DTYPE_Opaque, DTYPE_Opaque => _
              | _, _ => _
              end); try (ltac:(dec_dvalue); fail).
    - destruct (N.eq_dec n m).
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
    - destruct (N.eq_dec n m).
      * destruct (f t t').
      + left; subst; reflexivity.
      + right; intros H; inversion H. contradiction.
        * right; intros H; inversion H. contradiction.
    - destruct (lsteq_dec l l').
      * left; subst; reflexivity.
      * right; intros H; inversion H. contradiction.
  Defined.
  Arguments dtyp_eq_dec: clear implicits.

 Lemma ibinop_eq_dec : forall (op1 op2:ibinop), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Lemma fbinop_eq_dec : forall (op1 op2:fbinop), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Lemma icmp_eq_dec : forall (op1 op2:icmp), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Lemma fcmp_eq_dec : forall (op1 op2:fcmp), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Lemma fast_math_eq_dec : forall (op1 op2:fast_math), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Lemma conversion_type_eq_dec : forall (op1 op2:conversion_type), {op1 = op2} + {op1 <> op2}.
    intros.
    repeat decide equality.
  Qed.

  Arguments ibinop_eq_dec: clear implicits.
  Arguments fbinop_eq_dec: clear implicits.
  Arguments icmp_eq_dec: clear implicits.
  Arguments fcmp_eq_dec: clear implicits.
  Arguments fast_math_eq_dec: clear implicits.
  Arguments conversion_type_eq_dec: clear implicits.

  Ltac __abs := right; intros H; inversion H; contradiction.
  Ltac __eq := left; subst; reflexivity.

  Lemma uvalue_eq_dec : forall (u1 u2:uvalue), {u1 = u2} + {u1 <> u2}.
  Proof with (try (__eq || __abs)).
    refine (fix f u1 u2 :=
              let lsteq_dec := list_eq_dec f in
              match u1, u2 with
              | UVALUE_Addr a1, UVALUE_Addr a2 => _
              | UVALUE_I1 x1, UVALUE_I1 x2 => _
              | UVALUE_I8 x1, UVALUE_I8 x2 => _
              | UVALUE_I32 x1, UVALUE_I32 x2 => _
              | UVALUE_I64 x1, UVALUE_I64 x2 => _
              | UVALUE_Double x1, UVALUE_Double x2 => _
              | UVALUE_Float x1, UVALUE_Float x2 => _
              | UVALUE_Undef t1, UVALUE_Undef t2 => _
              | UVALUE_Poison, UVALUE_Poison => _
              | UVALUE_None, UVALUE_None => _
              | UVALUE_Struct f1, UVALUE_Struct f2 => _
              | UVALUE_Array f1, UVALUE_Array f2 => _
              | UVALUE_IBinop op uv1 uv2, UVALUE_IBinop op' uv1' uv2' => _
              | UVALUE_ICmp op uv1 uv2, UVALUE_ICmp op' uv1' uv2' => _
              | UVALUE_FBinop op fm uv1 uv2, UVALUE_FBinop op' fm' uv1' uv2' => _
              | UVALUE_FCmp op uv1 uv2, UVALUE_FCmp op' uv1' uv2' => _
              | UVALUE_Conversion ct tf u t, UVALUE_Conversion ct' tf' u' t' => _
              | UVALUE_GetElementPtr t u l, UVALUE_GetElementPtr t' u' l' => _
              | UVALUE_ExtractElement t u v, UVALUE_ExtractElement t' u' v' => _
              | UVALUE_InsertElement t u v x, UVALUE_InsertElement t' u' v' x' => _
              | UVALUE_ShuffleVector u v x, UVALUE_ShuffleVector u' v' x' => _
              | UVALUE_ExtractValue t u l, UVALUE_ExtractValue t' u' l' => _
              | UVALUE_InsertValue t u v l, UVALUE_InsertValue t' u' v' l' => _
              | UVALUE_Select u v w, UVALUE_Select u' v' w' => _
              | _, _ => _
              end); try (ltac:(dec_dvalue); fail).
    - destruct (A.eq_dec a1 a2)...
    - destruct (Int1.eq_dec x1 x2)...
    - destruct (Int8.eq_dec x1 x2)...
    - destruct (Int32.eq_dec x1 x2)...
    - destruct (Int64.eq_dec x1 x2)...
    - destruct (Float.eq_dec x1 x2)...
    - destruct (Float32.eq_dec x1 x2)...
    - destruct (dtyp_eq_dec t1 t2)...
    - destruct (lsteq_dec f1 f2)...
    - destruct (lsteq_dec f1 f2)...
    - destruct (ibinop_eq_dec op op')...
      destruct (f uv1 uv1')...
      destruct (f uv2 uv2')...
    - destruct (icmp_eq_dec op op')...
      destruct (f uv1 uv1')...
      destruct (f uv2 uv2')...
    - destruct (fbinop_eq_dec op op')...
      destruct (list_eq_dec fast_math_eq_dec fm fm')...
      destruct (f uv1 uv1')...
      destruct (f uv2 uv2')...
    - destruct (fcmp_eq_dec op op')...
      destruct (f uv1 uv1')...
      destruct (f uv2 uv2')...
    - destruct (conversion_type_eq_dec ct ct')...
      destruct (f u u')...
      destruct (dtyp_eq_dec tf tf')...
      destruct (dtyp_eq_dec t t')...
    - destruct (dtyp_eq_dec t t')...
      destruct (f u u')...
      destruct (lsteq_dec l l')...
    - destruct (dtyp_eq_dec t t')...
      destruct (f u u')...
      destruct (f v v')...
    - destruct (dtyp_eq_dec t t')...
      destruct (f u u')...
      destruct (f v v')...
      destruct (f x x')...
    - destruct (f u u')...
      destruct (f v v')...
      destruct (f x x')...
    - destruct (dtyp_eq_dec t t')...
      destruct (f u u')...
      destruct (list_eq_dec Z.eq_dec l l')...
    - destruct (dtyp_eq_dec t t')...
      destruct (f u u')...
      destruct (f v v')...
      destruct (list_eq_dec Z.eq_dec l l')...
    - destruct (f u u')...
      destruct (f v v')...
      destruct (f w w')...
  Defined.

  #[global] Instance eq_dec_uvalue : RelDec (@eq uvalue) := RelDec_from_dec (@eq uvalue) (@uvalue_eq_dec).
  #[global] Instance eqv_uvalue : Eqv uvalue := (@eq uvalue).
  Hint Unfold eqv_uvalue : core.
  #[global] Instance eq_dec_uvalue_correct: @RelDec.RelDec_Correct uvalue (@Logic.eq uvalue) _ := _.

End DecidableEquality.

Definition is_DVALUE_I1 (d:dvalue) : bool :=
  match d with
  | DVALUE_I1 _ => true
  | _ => false
  end.

Definition is_DVALUE_I8 (d:dvalue) : bool :=
  match d with
  | DVALUE_I8 _ => true
  | _ => false
  end.

Definition is_DVALUE_I32 (d:dvalue) : bool :=
  match d with
  | DVALUE_I32 _ => true
  | _ => false
  end.

Definition is_DVALUE_I64 (d:dvalue) : bool :=
  match d with
  | DVALUE_I64 _ => true
  | _ => false
  end.

Definition is_DVALUE_IX (d:dvalue) : bool :=
  is_DVALUE_I1 d || is_DVALUE_I8 d || is_DVALUE_I32 d || is_DVALUE_I64 d.


Class VInt I : Type :=
  {
    (* Comparisons *)
    equ : I -> I -> bool;
    cmp : comparison -> I -> I -> bool;
    cmpu : comparison -> I -> I -> bool;

    (* Constants *)
    bitwidth : nat;
    zero : I;
    one : I;

    (* Arithmetic *)
    add : I -> I -> I;
    add_carry : I -> I -> I -> I;
    add_overflow : I -> I -> I -> I;

    sub : I -> I -> I;
    sub_borrow : I -> I -> I -> I;
    sub_overflow : I -> I -> I -> I;

    mul : I -> I -> I;

    divu : I -> I -> I;
    divs : I -> I -> I;
    modu : I -> I -> I;
    mods : I -> I -> I;

    shl : I -> I -> I;
    shr : I -> I -> I;
    shru : I -> I -> I;

    negative : I -> I;

    (* Logic *)
    and : I -> I -> I;
    or : I -> I -> I;
    xor : I -> I -> I;

    (* Bounds *)
    min_signed : Z;
    max_signed : Z;

    (* Conversion *)
    to_dvalue : I -> dvalue;
    unsigned : I -> Z;
    signed : I -> Z;

    repr : Z -> I;
  }.


  #[global] Instance VInt1 : VInt Int1.int :=
  {
    (* Comparisons *)
    equ := Int1.eq;
    cmp := Int1.cmp;
    cmpu := Int1.cmpu;

    bitwidth := 1;

    (* Constants *)
    zero := Int1.zero;
    one := Int1.one;

    (* Arithmetic *)
    add := Int1.add;
    add_carry := Int1.add_carry;
    add_overflow := Int1.add_overflow;

    sub := Int1.sub;
    sub_borrow := Int1.sub_borrow;
    sub_overflow := Int1.sub_overflow;

    mul := Int1.mul;

    divu := Int1.divu;
    divs := Int1.divs;
    modu := Int1.modu;
    mods := Int1.mods;

    shl := Int1.shl;
    shr := Int1.shr;
    shru := Int1.shru;

    negative := Int1.negative;

    (* Logic *)
    and := Int1.and;
    or := Int1.or;
    xor := Int1.xor;

    (* Bounds *)
    min_signed := Int1.min_signed;
    max_signed := Int1.max_signed;

    (* Conversion *)
    to_dvalue := DVALUE_I1;
    unsigned := Int1.unsigned;
    signed := Int1.signed;

    repr := Int1.repr;
  }.


  #[global] Instance VInt8 : VInt Int8.int :=
  {
    (* Comparisons *)
    equ := Int8.eq;
    cmp := Int8.cmp;
    cmpu := Int8.cmpu;

    bitwidth := 8;

    (* Constants *)
    zero := Int8.zero;
    one := Int8.one;

    (* Arithmetic *)
    add := Int8.add;
    add_carry := Int8.add_carry;
    add_overflow := Int8.add_overflow;

    sub := Int8.sub;
    sub_borrow := Int8.sub_borrow;
    sub_overflow := Int8.sub_overflow;

    mul := Int8.mul;

    divu := Int8.divu;
    divs := Int8.divs;
    modu := Int8.modu;
    mods := Int8.mods;

    shl := Int8.shl;
    shr := Int8.shr;
    shru := Int8.shru;

    negative := Int8.negative;

    (* Logic *)
    and := Int8.and;
    or := Int8.or;
    xor := Int8.xor;

    (* Bounds *)
    min_signed := Int8.min_signed;
    max_signed := Int8.max_signed;

    (* Conversion *)
    to_dvalue := DVALUE_I8;
    unsigned := Int8.unsigned;
    signed := Int8.signed;

    repr := Int8.repr;
  }.


  #[global] Instance VInt32 : VInt Int32.int :=
  {
    (* Comparisons *)
    equ := Int32.eq;
    cmp := Int32.cmp;
    cmpu := Int32.cmpu;

    bitwidth := 32;

    (* Constants *)
    zero := Int32.zero;
    one := Int32.one;

    (* Arithmetic *)
    add := Int32.add;
    add_carry := Int32.add_carry;
    add_overflow := Int32.add_overflow;

    sub := Int32.sub;
    sub_borrow := Int32.sub_borrow;
    sub_overflow := Int32.sub_overflow;

    mul := Int32.mul;

    divu := Int32.divu;
    divs := Int32.divs;
    modu := Int32.modu;
    mods := Int32.mods;

    shl := Int32.shl;
    shr := Int32.shr;
    shru := Int32.shru;

    negative := Int32.negative;

    (* Logic *)
    and := Int32.and;
    or := Int32.or;
    xor := Int32.xor;

    (* Bounds *)
    min_signed := Int32.min_signed;
    max_signed := Int32.max_signed;

    (* Conversion *)
    to_dvalue := DVALUE_I32;
    unsigned := Int32.unsigned;
    signed := Int32.signed;

    repr := Int32.repr;
  }.

  #[global] Instance VInt64 : VInt Int64.int :=
  {
    (* Comparisons *)
    equ := Int64.eq;
    cmp := Int64.cmp;
    cmpu := Int64.cmpu;

    bitwidth := 64;

    (* Constants *)
    zero := Int64.zero;
    one := Int64.one;

    (* Arithmetic *)
    add := Int64.add;
    add_carry := Int64.add_carry;
    add_overflow := Int64.add_overflow;

    sub := Int64.sub;
    sub_borrow := Int64.sub_borrow;
    sub_overflow := Int64.sub_overflow;

    mul := Int64.mul;

    divu := Int64.divu;
    divs := Int64.divs;
    modu := Int64.modu;
    mods := Int64.mods;

    shl := Int64.shl;
    shr := Int64.shr;
    shru := Int64.shru;

    negative := Int64.negative;

    (* Logic *)
    and := Int64.and;
    or := Int64.or;
    xor := Int64.xor;

    (* Bounds *)
    min_signed := Int64.min_signed;
    max_signed := Int64.max_signed;

    (* Conversion *)
    to_dvalue := DVALUE_I64;
    unsigned := Int64.unsigned;
    signed := Int64.signed;

    repr := Int64.repr;
  }.

  (* Check if this is an instruction which can trigger UB with division by 0. *)
  Definition iop_is_div (iop : ibinop) : bool :=
    match iop with
    | UDiv _ => true
    | SDiv _ => true
    | URem   => true
    | SRem   => true
    | _      => false
    end.

  (* Check if this is an instruction which can trigger UB with division by 0. *)
  Definition fop_is_div (fop : fbinop) : bool :=
    match fop with
    | FDiv => true
    | FRem => true
    | _    => false
    end.

  Definition undef_i1  := UVALUE_Undef (DTYPE_I 1).
  Definition undef_i8  := UVALUE_Undef (DTYPE_I 8).
  Definition undef_i32 := UVALUE_Undef (DTYPE_I 32).
  Definition undef_i64 := UVALUE_Undef (DTYPE_I 64).
  Definition undef_int {Int} `{VInt Int}  := UVALUE_Undef (DTYPE_I (N.of_nat bitwidth)).

  Definition to_uvalue {Int} `{VInt Int} (i : Int) : uvalue := dvalue_to_uvalue (to_dvalue i).

  (* Arithmetic Operations ---------------------------------------------------- *)
  Section ARITHMETIC.

    (* Evaluate integer opererations to get a dvalue.

     These operations are between VInts, which are "vellvm"
     integers. This is a typeclass that wraps all of the integer
     operations that we use for integer types with different bitwidths.

     *)
    Definition eval_int_op {Int} `{VInt Int} (iop:ibinop) (x y: Int) : undef dvalue :=
      match iop with
      (* Following to cases are probably right since they use CompCert *)
      | Add nuw nsw =>
        ret (if orb (andb nuw (equ (add_carry x y zero) one))
                    (andb nsw (equ (add_overflow x y zero) one))
             then DVALUE_Poison else to_dvalue (add x y))

      | Sub nuw nsw =>
        ret (if orb (andb nuw (equ (sub_borrow x y zero) one))
                    (andb nsw (equ (sub_overflow x y zero) one))
            then DVALUE_Poison else to_dvalue (sub x y))

      | Mul nuw nsw =>
        (* I1 mul can't overflow, just based on the 4 possible multiplications. *)
        if (bitwidth ~=? 1)%nat then ret (to_dvalue (mul x y))
        else
          let res := mul x y in
          let res_s' := ((signed x) * (signed y))%Z in
          if orb (andb nuw ((unsigned x) * (unsigned y) >?
                        unsigned res))
              (andb nsw (orb (min_signed >? res_s')
                              (res_s' >? max_signed)))
        then ret DVALUE_Poison else ret (to_dvalue res)

      | Shl nuw nsw =>
        let bz := Z.of_nat bitwidth in
        let res := shl x y in
        let res_u := unsigned res in
        let res_u' := Z.shiftl (unsigned x) (unsigned y) in
        (* Unsigned shift x right by bitwidth - y. If shifted x != sign bit * (2^y - 1),
          then there is overflow. *)
        if (unsigned y) >=? bz then ret DVALUE_Poison
        else if orb (andb nuw (res_u' >? res_u))
                    (andb nsw (negb (Z.shiftr (unsigned x)
                                              (bz - unsigned y)
                                    =? (unsigned (negative res))
                                        * (Z.pow 2 (unsigned y) - 1))%Z))
            then ret DVALUE_Poison else ret (to_dvalue res)

      | UDiv ex =>
        if (unsigned y =? 0)%Z
        then failwith "Unsigned division by 0."
        else if andb ex (negb ((unsigned x) mod (unsigned y) =? 0))%Z
            then ret DVALUE_Poison
            else ret (to_dvalue (divu x y))

      | SDiv ex =>
        (* What does signed i1 mean? *)
        if (signed y =? 0)%Z
        then failwith "Signed division by 0."
        else if andb ex (negb ((signed x) mod (signed y) =? 0))%Z
            then ret DVALUE_Poison
            else ret (to_dvalue (divs x y))

      | LShr ex =>
        let bz := Z.of_nat bitwidth in
        if (unsigned y) >=? bz then ret DVALUE_Poison
        else if andb ex (negb ((unsigned x)
                                mod (Z.pow 2 (unsigned y)) =? 0))%Z
            then ret DVALUE_Poison else ret (to_dvalue (shru x y))

      | AShr ex =>
        let bz := Z.of_nat bitwidth in
        if (unsigned y) >=? bz then ret DVALUE_Poison
        else if andb ex (negb ((unsigned x)
                                mod (Z.pow 2 (unsigned y)) =? 0))%Z
            then ret DVALUE_Poison else ret (to_dvalue (shr x y))

      | URem =>
        if (unsigned y =? 0)%Z
        then failwith "Unsigned mod 0."
        else ret (to_dvalue (modu x y))

      | SRem =>
        if (signed y =? 0)%Z
        then failwith "Signed mod 0."
        else ret (to_dvalue (mods x y))

      | And =>
        ret (to_dvalue (and x y))

      | Or =>
        ret (to_dvalue (or x y))

      | Xor =>
        ret (to_dvalue (xor x y))
      end.
  Arguments eval_int_op _ _ _ : simpl nomatch.

  (* Evaluate the given iop on the given arguments according to the bitsize *)
  Definition integer_op (bits:N) (iop:ibinop) (x y:inttyp bits) : undef_or_err dvalue :=
    match bits, x, y with
    | 1, x, y  => lift (eval_int_op iop x y)
    | 8, x, y  => lift (eval_int_op iop x y)
    | 32, x, y => lift (eval_int_op iop x y)
    | 64, x, y => lift (eval_int_op iop x y)
    | _, _, _  => failwith "unsupported bitsize"
    end.
  Arguments integer_op _ _ _ _ : simpl nomatch.

  (* Convert written integer constant to corresponding integer with bitsize bits.
     Takes the integer modulo 2^bits. *)
  Definition coerce_integer_to_int (bits:N) (i:Z) : undef_or_err dvalue :=
    match bits with
    | 1  => ret (DVALUE_I1 (repr i))
    | 8  => ret (DVALUE_I8 (repr i))
    | 32 => ret (DVALUE_I32 (repr i))
    | 64 => ret (DVALUE_I64 (repr i))
    | _  => failwith "unsupported integer size"
    end.
  Arguments coerce_integer_to_int _ _ : simpl nomatch.

  (* Helper for looping 2 argument evaluation over vectors, producing a vector *)

  Definition vec_loop {A : Type} {M : Type -> Type} `{Monad M}
             (f : A -> A -> M A)
             (elts : list (A * A)) : M (list A) :=
    monad_fold_right (fun acc '(e1, e2) =>
                        val <- f e1 e2 ;;
                        ret (val :: acc)
                     ) elts [].


  (* Integer iop evaluation, called from eval_iop.
     Here the values must be integers. Helper defined
     in order to prevent eval_iop from being recursive. *)
  Definition eval_iop_integer_h iop v1 v2 : undef_or_err dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2    => lift (eval_int_op iop i1 i2)
    | DVALUE_I8 i1, DVALUE_I8 i2    => lift (eval_int_op iop i1 i2)
    | DVALUE_I32 i1, DVALUE_I32 i2  => lift (eval_int_op iop i1 i2)
    | DVALUE_I64 i1, DVALUE_I64 i2  => lift (eval_int_op iop i1 i2)
    | DVALUE_Poison, (DVALUE_I1 _ | DVALUE_I8 _ | DVALUE_I32 _ | DVALUE_I64 _) =>
        lift (ret DVALUE_Poison)
    | (DVALUE_I1 _ | DVALUE_I8 _ | DVALUE_I32 _ | DVALUE_I64 _),
        DVALUE_Poison              =>
      if iop_is_div iop
      then lift (raise "Division by poison.")
      else ret DVALUE_Poison
    | _, _                          => failwith "ill_typed-iop"
    end.
  Arguments eval_iop_integer_h _ _ _ : simpl nomatch.

  (* I split the definition between the vector and other evaluations because
     otherwise eval_iop should be recursive to allow for vector calculations,
     but coq can't find a fixpoint. *)
  (* Here is where we want to add the case distinction  for uvalues

       - this should check for "determined" uvalues and then use eval_iop_integer_h
         otherwise leave the op symbolic

       - this should use the inclusion of dvalue into uvalue in the case that
         eval_iop_integer_h is calle

   *)

  Definition eval_iop iop v1 v2 : undef_or_err dvalue :=
    match v1, v2 with
    | _, _ => eval_iop_integer_h iop v1 v2
    end.
  Arguments eval_iop _ _ _ : simpl nomatch.

  Definition default_dvalue_of_dtyp_i (sz : N) : err dvalue:=
    (if (sz =? 64) then ret (DVALUE_I64 (repr 0))
     else if (sz =? 32) then ret (DVALUE_I32 (repr 0))
          else if (sz =? 8) then ret (DVALUE_I8 (repr 0))
               else if (sz =? 1) then ret (DVALUE_I1 (repr 0))
                    else failwith
                           "Illegal size for generating default dvalue of DTYPE_I").

  (* Handler for PickE which concretizes everything to 0 *)
  (* If this succeeds the dvalue returned should agree with
     dvalue_has_dtyp for the sake of the dvalue_default lemma. *)
  Fixpoint default_dvalue_of_dtyp (dt : dtyp) : err dvalue :=
    match dt with
    | DTYPE_I sz => default_dvalue_of_dtyp_i sz
    | DTYPE_Pointer => ret (DVALUE_Addr A.null)
    | DTYPE_Void => ret DVALUE_None
    | DTYPE_Half => failwith "Unimplemented default type: half"
    | DTYPE_Float => ret (DVALUE_Float Float32.zero)
    | DTYPE_Double => ret (DVALUE_Double (Float32.to_double Float32.zero))
    | DTYPE_X86_fp80 => failwith "Unimplemented default type: x86_fp80"
    | DTYPE_Fp128 => failwith "Unimplemented default type: fp128"
    | DTYPE_Ppc_fp128 => failwith "Unimplemented default type: ppc_fp128"
    | DTYPE_Metadata => failwith "Unimplemented default type: metadata"
    | DTYPE_X86_mmx => failwith "Unimplemented default type: x86_mmx"
    | DTYPE_Opaque => failwith "Unimplemented default type: opaque"
    | DTYPE_Array sz t =>
        v <- default_dvalue_of_dtyp t ;;
        (ret (DVALUE_Array (repeat v (N.to_nat sz))))

    (* Matching valid Vector types... *)
    (* Currently commented out unsupported ones *)
    (* | DTYPE_Vector sz (DTYPE_Half) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     failwith ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    (* | DTYPE_Vector sz (DTYPE_X86_fp80) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     failwith ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    (* | DTYPE_Vector sz (DTYPE_Fp128) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     failwith ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    | DTYPE_Struct fields =>
        v <- @map_monad err _ dtyp dvalue default_dvalue_of_dtyp fields;;
        ret (DVALUE_Struct v)
    end.

  Definition eval_int_icmp {Int} `{VInt Int} icmp (x y : Int) : dvalue :=
    if match icmp with
       | Eq => cmp Ceq x y
       | Ne => cmp Cne x y
       | Ugt => cmpu Cgt x y
       | Uge => cmpu Cge x y
       | Ult => cmpu Clt x y
       | Ule => cmpu Cle x y
       | Sgt => cmp Cgt x y
       | Sge => cmp Cge x y
       | Slt => cmp Clt x y
       | Sle => cmp Cle x y
       end
    then DVALUE_I1 (Int1.one) else DVALUE_I1 (Int1.zero).
  Arguments eval_int_icmp _ _ _ : simpl nomatch.

  Definition eval_icmp icmp v1 v2 : undef_or_err dvalue :=
    match v1, v2 with
    | DVALUE_I1 i1, DVALUE_I1 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I8 i1, DVALUE_I8 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I32 i1, DVALUE_I32 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_I64 i1, DVALUE_I64 i2 => ret (eval_int_icmp icmp i1 i2)
    | DVALUE_Poison, DVALUE_Poison => ret DVALUE_Poison
    | DVALUE_Poison, _ => if is_DVALUE_IX v2 then ret DVALUE_Poison else failwith "ill_typed-iop"
    | _, DVALUE_Poison => if is_DVALUE_IX v1 then ret DVALUE_Poison else failwith "ill_typed-iop"
    | DVALUE_Addr a1, DVALUE_Addr a2 =>
      match icmp with
      | Eq => if A.eq_dec a1 a2 then ret (DVALUE_I1 (Int1.one)) else ret (DVALUE_I1 (Int1.zero))
      | Ne => if A.eq_dec a1 a2 then ret (DVALUE_I1 (Int1.zero)) else ret (DVALUE_I1 (Int1.one))
      | _ => failwith "non-equality pointer comparison"
      end
    | _, _ => failwith "ill_typed-icmp"
    end.
  Arguments eval_icmp _ _ _ : simpl nomatch.

  Definition double_op (fop:fbinop) (v1:ll_double) (v2:ll_double) : undef_or_err dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Double (b64_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Double (b64_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Double (b64_mult FT_Rounding v1 v2))
    | FDiv => if (Float.eq_dec v2 Float.zero)
              then lift (raise "Signed division by 0.")
              else ret (DVALUE_Double (b64_div FT_Rounding v1 v2))
    | FRem => failwith "unimplemented double operation"
    end.

  Definition float_op (fop:fbinop) (v1:ll_float) (v2:ll_float) : undef_or_err dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Float (b32_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Float (b32_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Float (b32_mult FT_Rounding v1 v2))
    | FDiv => if (Float32.eq_dec v2 Float32.zero)
              then lift (raise "Signed division by 0.")
              else ret (DVALUE_Float (b32_div FT_Rounding v1 v2))
    | FRem => failwith "unimplemented float operation"
    end.

  Definition eval_fop (fop:fbinop) (v1:dvalue) (v2:dvalue) : undef_or_err dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2   => float_op fop f1 f2
    | DVALUE_Double d1, DVALUE_Double d2 => double_op fop d1 d2
    | DVALUE_Poison, _                   => ret DVALUE_Poison
    | _, DVALUE_Poison                   =>
      if fop_is_div fop
      then lift (raise "Division by poison.")
      else ret DVALUE_Poison
    | _, _                               => failwith ("ill_typed-fop: " ++ (to_string fop) ++ " " ++ (to_string v1) ++ " " ++ (to_string v2))
    end.

  Definition not_nan32 (f:ll_float) : bool :=
    negb (Flocq.IEEE754.Binary.is_nan _ _ f).

  Definition ordered32 (f1 f2:ll_float) : bool :=
    andb (not_nan32 f1) (not_nan32 f2).

  Definition not_nan64 (f:ll_double) : bool :=
    negb (Flocq.IEEE754.Binary.is_nan _ _ f).

  Definition ordered64 (f1 f2:ll_double) : bool :=
    andb (not_nan64 f1) (not_nan64 f2).

  Definition float_cmp (fcmp:fcmp) (x:ll_float) (y:ll_float) : dvalue :=
    if match fcmp with
       | FFalse => false
       | FOeq => andb (ordered32 x y) (Float32.cmp Ceq x y)
       | FOgt => andb (ordered32 x y) (Float32.cmp Cgt x y)
       | FOge => andb (ordered32 x y) (Float32.cmp Cge x y)
       | FOlt => andb (ordered32 x y) (Float32.cmp Clt x y)
       | FOle => andb (ordered32 x y) (Float32.cmp Cle x y)
       | FOne => andb (ordered32 x y) (Float32.cmp Cne x y)
       | FOrd => ordered32 x y
       | FUno => negb (ordered32 x y)
       | FUeq => (Float32.cmp Ceq x y)
       | FUgt => (Float32.cmp Cgt x y)
       | FUge => (Float32.cmp Cge x y)
       | FUlt => (Float32.cmp Clt x y)
       | FUle => (Float32.cmp Cle x y)
       | FUne => (Float32.cmp Cne x y)
       | FTrue => true
       end
    then DVALUE_I1 Int1.one else DVALUE_I1 Int1.zero.
  Arguments float_cmp _ _ _ : simpl nomatch.

  Definition double_cmp (fcmp:fcmp) (x:ll_double) (y:ll_double) : dvalue :=
    if match fcmp with
       | FFalse => false
       | FOeq => andb (ordered64 x y) (Float.cmp Ceq x y)
       | FOgt => andb (ordered64 x y) (Float.cmp Cgt x y)
       | FOge => andb (ordered64 x y) (Float.cmp Cge x y)
       | FOlt => andb (ordered64 x y) (Float.cmp Clt x y)
       | FOle => andb (ordered64 x y) (Float.cmp Cle x y)
       | FOne => andb (ordered64 x y) (Float.cmp Cne x y)
       | FOrd => ordered64 x y
       | FUno => negb (ordered64 x y)
       | FUeq => (Float.cmp Ceq x y)
       | FUgt => (Float.cmp Cgt x y)
       | FUge => (Float.cmp Cge x y)
       | FUlt => (Float.cmp Clt x y)
       | FUle => (Float.cmp Cle x y)
       | FUne => (Float.cmp Cne x y)
       | FTrue => true
       end
    then DVALUE_I1 Int1.one else DVALUE_I1 Int1.zero.
    Arguments double_cmp _ _ _ : simpl nomatch.

  Definition eval_fcmp (fcmp:fcmp) (v1:dvalue) (v2:dvalue) : undef_or_err dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2 => ret (float_cmp fcmp f1 f2)
    | DVALUE_Double f1, DVALUE_Double f2 => ret (double_cmp fcmp f1 f2)
    | DVALUE_Poison, DVALUE_Poison => ret DVALUE_Poison
    | DVALUE_Poison, DVALUE_Double _ => ret DVALUE_Poison
    | DVALUE_Poison, DVALUE_Float _ => ret DVALUE_Poison
    | DVALUE_Double _, DVALUE_Poison => ret DVALUE_Poison
    | DVALUE_Float _, DVALUE_Poison => ret DVALUE_Poison
    | _, _ => failwith "ill_typed-fcmp"
    end.

  End ARITHMETIC.

  (* Same deal as above with the helper *)
  (* The pattern matching generates hundreds of subgoals, hence the factorization of the typeclass inference *)
  Definition eval_select (cnd : dvalue) (v1 v2 : uvalue) : undef_or_err uvalue :=
    let failwith_local := (@failwith _ undef_or_err (Monad_eitherT string Monad_err) (Exception_eitherT string Monad_err))
    in
    let ret_local := (@ret undef_or_err (Monad_eitherT string Monad_err) uvalue)
    in
    match v1, v2 with
    | UVALUE_Poison, _ => ret_local UVALUE_Poison
    | _, UVALUE_Poison => ret_local UVALUE_Poison
    | _, _ =>
      match cnd with
      | DVALUE_I1 i =>
        ret_local (if (Int1.unsigned i =? 1)%Z then v1 else v2)
      | DVALUE_Poison => ret_local UVALUE_Poison
      | _ => failwith_local "ill_typed select"
      end
    end.

  Arguments eval_select _ _ _ : simpl nomatch.

  (* Helper function for indexing into a structured datatype
     for extractvalue and insertvalue *)
  Definition index_into_str (v:uvalue) (idx:LLVMAst.int) : undef_or_err uvalue :=
    let fix loop elts i :=
        match elts with
        | [] => failwith "index out of bounds"
        | h :: tl =>
          if (idx =? 0)%Z then ret h else loop tl (i-1)%Z
        end in
    match v with
    | UVALUE_Struct f => loop f idx
    | UVALUE_Array e => loop e idx
    | _ => failwith "invalid aggregate data"
    end.
  Arguments index_into_str _ _ : simpl nomatch.

  (* Helper function for inserting into a structured datatype for insertvalue *)
  Definition insert_into_str (str:dvalue) (v:dvalue) (idx:LLVMAst.int) : undef_or_err dvalue :=
    let fix loop (acc elts:list dvalue) (i:LLVMAst.int) :=
        match elts with
        | [] => failwith "index out of bounds"
        | h :: tl =>
          (if idx =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list in
    match str with
    | DVALUE_Struct f =>
      v <- (loop [] f idx) ;;
      ret (DVALUE_Struct v)

    | DVALUE_Array e =>
      v <- (loop [] e idx) ;;
      ret (DVALUE_Array v)

    | _ => failwith "invalid aggregate data"
    end.
  Arguments insert_into_str _ _ _ : simpl nomatch.

(*  ------------------------------------------------------------------------- *)

  (* Interpretation of [uvalue] in terms of sets of [dvalue].
     Essentially used to implemenmt the handler for [pick], but also requuired to
     define some predicates passed as arguments to the [pick] events, hence why
     it's defined here.
   *)

  (* Poison not included because of concretize *)
  Unset Elimination Schemes.
  Inductive dvalue_has_dtyp : dvalue -> dtyp -> Prop :=
  | DVALUE_Addr_typ   : forall a, dvalue_has_dtyp (DVALUE_Addr a) DTYPE_Pointer
  | DVALUE_I1_typ     : forall x, dvalue_has_dtyp (DVALUE_I1 x) (DTYPE_I 1)
  | DVALUE_I8_typ     : forall x, dvalue_has_dtyp (DVALUE_I8 x) (DTYPE_I 8)
  | DVALUE_I32_typ    : forall x, dvalue_has_dtyp (DVALUE_I32 x) (DTYPE_I 32)
  | DVALUE_I64_typ    : forall x, dvalue_has_dtyp (DVALUE_I64 x) (DTYPE_I 64)
  | DVALUE_Double_typ : forall x, dvalue_has_dtyp (DVALUE_Double x) DTYPE_Double
  | DVALUE_Float_typ  : forall x, dvalue_has_dtyp (DVALUE_Float x) DTYPE_Float
  | DVALUE_None_typ   : dvalue_has_dtyp DVALUE_None DTYPE_Void
  | DVALUE_Struct_typ :
    forall fields dts,
      List.Forall2 dvalue_has_dtyp fields dts ->
      dvalue_has_dtyp (DVALUE_Struct fields) (DTYPE_Struct dts)

  (* Do we have to exclude mmx? "There are no arrays, vectors or constants of this type" *)
  | DVALUE_Array_typ :
      forall xs sz dt,
        Forall (fun x => dvalue_has_dtyp x dt) xs ->
        length xs = sz ->
        dvalue_has_dtyp (DVALUE_Array xs) (DTYPE_Array (N.of_nat sz) dt)
  .
  Set Elimination Schemes.

  Inductive uvalue_has_dtyp : uvalue -> dtyp -> Prop :=
  | UVALUE_Addr_typ   : forall a, uvalue_has_dtyp (UVALUE_Addr a) DTYPE_Pointer
  | UVALUE_I1_typ     : forall x, uvalue_has_dtyp (UVALUE_I1 x) (DTYPE_I 1)
  | UVALUE_I8_typ     : forall x, uvalue_has_dtyp (UVALUE_I8 x) (DTYPE_I 8)
  | UVALUE_I32_typ    : forall x, uvalue_has_dtyp (UVALUE_I32 x) (DTYPE_I 32)
  | UVALUE_I64_typ    : forall x, uvalue_has_dtyp (UVALUE_I64 x) (DTYPE_I 64)
  | UVALUE_IX_typ     : forall x, ~IX_supported x -> uvalue_has_dtyp UVALUE_None (DTYPE_I x)
  | UVALUE_Double_typ : forall x, uvalue_has_dtyp (UVALUE_Double x) DTYPE_Double
  | UVALUE_Float_typ  : forall x, uvalue_has_dtyp (UVALUE_Float x) DTYPE_Float
  | UVALUE_None_typ   : uvalue_has_dtyp UVALUE_None DTYPE_Void
  | UVALUE_Undef_typ  : forall τ, uvalue_has_dtyp (UVALUE_Undef τ) τ

  | UVALUE_Struct_Nil_typ  : uvalue_has_dtyp (UVALUE_Struct []) (DTYPE_Struct [])
  | UVALUE_Struct_Cons_typ :
      forall f dt fields dts,
        uvalue_has_dtyp f dt ->
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct dts) ->
        uvalue_has_dtyp (UVALUE_Struct (f :: fields)) (DTYPE_Struct (dt :: dts))

  (* Do we have to exclude mmx? "There are no arrays, vectors or constants of this type" *)
  | UVALUE_Array_typ :
      forall xs sz dt,
        Forall (fun x => uvalue_has_dtyp x dt) xs ->
        length xs = sz ->
        uvalue_has_dtyp (UVALUE_Array xs) (DTYPE_Array (N.of_nat sz) dt)

  | UVALUE_IBinop_typ :
      forall x y sz op,
      IX_supported sz ->
      uvalue_has_dtyp x (DTYPE_I sz) ->
      uvalue_has_dtyp y (DTYPE_I sz) ->
      uvalue_has_dtyp (UVALUE_IBinop op x y) (DTYPE_I sz)
  | UVALUE_ICmp_typ :
      forall x y sz op,
      IX_supported sz ->
      uvalue_has_dtyp x (DTYPE_I sz) ->
      uvalue_has_dtyp y (DTYPE_I sz) ->
      uvalue_has_dtyp (UVALUE_ICmp op x y) (DTYPE_I 1)
  | UVALUE_ICmp_pointer_typ :
      forall x y op,
      uvalue_has_dtyp x DTYPE_Pointer ->
      uvalue_has_dtyp y DTYPE_Pointer ->
      uvalue_has_dtyp (UVALUE_ICmp op x y) (DTYPE_I 1)
  | UVALUE_FBinop_Float_typ :
      forall x y op fms,
      uvalue_has_dtyp x DTYPE_Float ->
      uvalue_has_dtyp y DTYPE_Float ->
      uvalue_has_dtyp (UVALUE_FBinop op fms x y) DTYPE_Float
  | UVALUE_FBinop_Double_typ :
      forall x y op fms,
      uvalue_has_dtyp x DTYPE_Double ->
      uvalue_has_dtyp y DTYPE_Double ->
      uvalue_has_dtyp (UVALUE_FBinop op fms x y) DTYPE_Double
  | UVALUE_FCmp_Float_typ :
      forall x y op,
        uvalue_has_dtyp x DTYPE_Float ->
        uvalue_has_dtyp y DTYPE_Float ->
        uvalue_has_dtyp (UVALUE_FCmp op x y) (DTYPE_I 1)
  | UVALUE_FCmp_Double_typ :
      forall x y op,
        uvalue_has_dtyp x DTYPE_Double ->
        uvalue_has_dtyp y DTYPE_Double ->
        uvalue_has_dtyp (UVALUE_FCmp op x y) (DTYPE_I 1)
  | UVALUE_Conversion_trunc_int_typ :
      forall from_sz to_sz value,
        from_sz > to_sz ->
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        uvalue_has_dtyp (UVALUE_Conversion Trunc (DTYPE_I from_sz) value (DTYPE_I to_sz)) (DTYPE_I to_sz)
  | UVALUE_Conversion_zext_int_typ :
      forall from_sz to_sz value,
        from_sz < to_sz ->
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        uvalue_has_dtyp (UVALUE_Conversion Zext (DTYPE_I from_sz) value (DTYPE_I to_sz)) (DTYPE_I to_sz)
  | UVALUE_Conversion_sext_int_typ :
      forall from_sz to_sz value,
        from_sz < to_sz ->
        uvalue_has_dtyp value (DTYPE_I from_sz) ->
        uvalue_has_dtyp (UVALUE_Conversion Sext (DTYPE_I from_sz) value (DTYPE_I to_sz)) (DTYPE_I to_sz)
  | UVALUE_GetElementPtr_typ :
      forall dt uv idxs,
        uvalue_has_dtyp (UVALUE_GetElementPtr dt uv idxs) DTYPE_Pointer
  | UVALUE_ExtractValue_Struct_sing_typ :
      forall fields fts dt (idx : LLVMAst.int),
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (DTYPE_Struct fts) (UVALUE_Struct fields) [idx]) dt
  | UVALUE_ExtractValue_Struct_cons_typ :
      forall fields fts fld ft dt idx idxs,
        uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct fts) ->
        (0 <= idx)%Z ->
        Nth fts (Z.to_nat idx) ft ->
        Nth fields (Z.to_nat idx) fld ->
        uvalue_has_dtyp fld ft ->
        uvalue_has_dtyp (UVALUE_ExtractValue ft fld idxs) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (DTYPE_Struct fts) (UVALUE_Struct fields) (idx :: idxs)) dt
  | UVALUE_ExtractValue_Array_sing_typ :
      forall elements dt idx n,
        uvalue_has_dtyp (UVALUE_Array elements) (DTYPE_Array n dt) ->
        (0 <= idx <= Z.of_N n)%Z ->
        uvalue_has_dtyp (UVALUE_ExtractValue (DTYPE_Array n dt) (UVALUE_Array elements) [idx]) dt
  | UVALUE_ExtractValue_Array_cons_typ :
      forall elements elem et dt n idx idxs,
        uvalue_has_dtyp (UVALUE_Array elements) (DTYPE_Array n et) ->
        (0 <= idx <= Z.of_N n)%Z ->
        Nth elements (Z.to_nat idx) elem ->
        uvalue_has_dtyp elem et ->
        uvalue_has_dtyp (UVALUE_ExtractValue et elem idxs) dt ->
        uvalue_has_dtyp (UVALUE_ExtractValue (DTYPE_Array n et) (UVALUE_Array elements) (idx :: idxs)) dt
  | UVALUE_InsertValue_typ :
      forall struc idxs uv st dt,
        uvalue_has_dtyp (UVALUE_ExtractValue st struc idxs) dt ->
        uvalue_has_dtyp uv dt ->
        uvalue_has_dtyp struc st ->
        uvalue_has_dtyp (UVALUE_InsertValue st struc uv idxs) st
  | UVALUE_Select_i1 :
      forall cond x y t,
        uvalue_has_dtyp cond (DTYPE_I 1) ->
        uvalue_has_dtyp x t ->
        uvalue_has_dtyp y t ->
        uvalue_has_dtyp (UVALUE_Select cond x y) t.

  Section dvalue_has_dtyp_ind.
    Variable P : dvalue -> dtyp -> Prop.
    Hypothesis IH_Addr           : forall a, P (DVALUE_Addr a) DTYPE_Pointer.
    Hypothesis IH_I1             : forall x, P (DVALUE_I1 x) (DTYPE_I 1).
    Hypothesis IH_I8             : forall x, P (DVALUE_I8 x) (DTYPE_I 8).
    Hypothesis IH_I32            : forall x, P (DVALUE_I32 x) (DTYPE_I 32).
    Hypothesis IH_I64            : forall x, P (DVALUE_I64 x) (DTYPE_I 64).
    Hypothesis IH_Double         : forall x, P (DVALUE_Double x) DTYPE_Double.
    Hypothesis IH_Float          : forall x, P (DVALUE_Float x) DTYPE_Float.
    Hypothesis IH_None           : P DVALUE_None DTYPE_Void.
    Hypothesis IH_Struct :
      forall fields fts,
        List.Forall2 P fields fts ->
        P (DVALUE_Struct fields) (DTYPE_Struct fts).
    Hypothesis IH_Array : forall (xs : list dvalue) (sz : nat) (dt : dtyp)
                            (IH : forall x, In x xs -> P x dt)
                            (IHdtyp : forall x, In x xs -> dvalue_has_dtyp x dt),
        Datatypes.length xs = sz -> P (DVALUE_Array xs) (DTYPE_Array (N.of_nat sz) dt).

    Lemma dvalue_has_dtyp_ind : forall (dv:dvalue) (dt:dtyp) (TYP: dvalue_has_dtyp dv dt), P dv dt.
      fix IH 3.
      intros dv dt TYP.
      destruct TYP.
      - apply IH_Addr.
      - apply IH_I1.
      - apply IH_I8.
      - apply IH_I32.
      - apply IH_I64.
      - apply IH_Double.
      - apply IH_Float.
      - apply IH_None.
      - apply IH_Struct.
        revert fields dts H.
        fix IHL_A 3.
        intros fields dts H.
        destruct H.
        + constructor.
        + constructor.
          eauto.
          eauto.
      - rename H into Hforall.
        rename H0 into Hlen.
        refine (IH_Array _ _ Hlen).

        { generalize dependent sz.
          generalize dependent xs.
          fix IHxs 2.
          intros xs Hforall sz Hlen x H.
          destruct xs.
          + inversion H.
          + inversion H; subst.
            * inversion Hforall; subst; auto.
            * eapply IHxs. inversion Hforall; subst.
              all: try eassumption. reflexivity.
        }

        apply Forall_forall; auto.
    Qed.
  End dvalue_has_dtyp_ind.


  Fixpoint dvalue_has_dtyp_fun (dv:dvalue) (dt:dtyp) : bool :=
    let list_forallb2 :=
      fix go dvs dts :=
      match dvs, dts with
      | [], [] => true
      | dv::utl, dt::dttl => dvalue_has_dtyp_fun dv dt && go utl dttl
      | _,_ => false
      end
    in

    match dv with
    | DVALUE_Addr a =>
        if @dtyp_eq_dec dt DTYPE_Pointer then true else false 
        
    | DVALUE_I1 x =>
        if @dtyp_eq_dec dt (DTYPE_I 1) then true else false 
        
    | DVALUE_I8 x =>
        if @dtyp_eq_dec dt (DTYPE_I 8) then true else false
                                                       
    | DVALUE_I32 x => 
        if @dtyp_eq_dec dt (DTYPE_I 32) then true else false
                       
    | DVALUE_I64 x => 
        if @dtyp_eq_dec dt (DTYPE_I 64) then true else false
                       
    | DVALUE_Double x => 
        if @dtyp_eq_dec dt (DTYPE_Double) then true else false
                                                        
    | DVALUE_Float x =>
        if @dtyp_eq_dec dt (DTYPE_Float) then true else false        

    | DVALUE_Poison => false
               
    | DVALUE_None =>
        if @dtyp_eq_dec dt (DTYPE_Void) then true else false        
                      
    | DVALUE_Struct fields =>
        match dt with
        | DTYPE_Struct field_dts =>
            list_forallb2 fields field_dts
        | _ => false
        end

    | DVALUE_Array elts =>
        match dt with
        | DTYPE_Array sz dtt =>
            List.forallb (fun u => dvalue_has_dtyp_fun u dtt) elts &&
              (Nat.eqb (List.length elts) (N.to_nat sz))
        | _ => false
        end
    end.

  Ltac invert_bools :=
    repeat match goal with
      | [ H : false = true |- _ ] => inversion H
      | [ H : ((?X && ?Y) = true) |- _ ] => apply andb_true_iff in H; destruct H
      | [ H : ((?X || ?Y) = true) |- _ ] => apply orb_true_iff in H; destruct H
    end.

  Ltac break_match_hyp_inv :=
    match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
        match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
        end;
        inv H
    end.

  Lemma dvalue_has_dtyp_fun_sound :
    forall dv dt,
      dvalue_has_dtyp_fun dv dt = true -> dvalue_has_dtyp dv dt.
  Proof.
    induction dv; intros dtx HX;
      try solve [
          cbn in HX; 
          repeat break_match_hyp_inv;
          invert_bools;
          econstructor; eauto with dvalue
        ].

    - cbn in HX.
      repeat break_match_hyp_inv.
      intros. constructor.
      revert fields0 H1.
      induction fields; intros; cbn.
      { destruct fields0; invert_bools.
        constructor. }
      { destruct fields0; invert_bools.
        constructor.
        eapply H; auto; constructor; auto.
        eapply IHfields; eauto.
        intros; eapply H; auto.
        apply in_cons; auto. }
        
    - cbn in HX.
      repeat break_match_hyp_inv.
      apply andb_prop in H1. destruct H1.
      apply Nat.eqb_eq in H1; subst.
      assert (sz = N.of_nat (Datatypes.length elts)).
      { rewrite H1; rewrite Nnat.N2Nat.id; auto. }
      subst.
      apply DVALUE_Array_typ; auto.
      clear H1.
      induction elts.
      + constructor.
      + cbn in H0.
        invert_bools.
        constructor.
        eapply H; auto. left; auto.
        apply IHelts; auto.
        intros.
        eapply H. right; auto.
        assumption.

  Qed.

  Inductive concretize_u : uvalue -> undef_or_err dvalue -> Prop :=
  (* Concrete uvalue are contretized into their singleton *)
  | Pick_concrete             : forall uv (dv : dvalue), uvalue_to_dvalue uv = inr dv -> concretize_u uv (ret dv)
  | Pick_fail                 : forall uv v s, ~ (uvalue_to_dvalue uv = inr v)  -> concretize_u uv (lift (failwith s))
  (* Undef relates to all dvalue of the type *)
  | Concretize_Undef          : forall dt dv,
      dvalue_has_dtyp dv dt ->
      concretize_u (UVALUE_Undef dt) (ret dv)

  (* The other operations proceed non-deterministically *)
  | Concretize_IBinop : forall iop uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_IBinop iop uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    (eval_iop iop dv1 dv2))

  | Concretize_ICmp : forall cmp uv1 e1 uv2 e2 ,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_ICmp cmp uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    eval_icmp cmp dv1 dv2)

  | Concretize_FBinop : forall fop fm uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_FBinop fop fm uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    eval_fop fop dv1 dv2)

  | Concretize_FCmp : forall cmp uv1 e1 uv2 e2,
      concretize_u uv1 e1 ->
      concretize_u uv2 e2 ->
      concretize_u (UVALUE_FCmp cmp uv1 uv2)
                   (dv1 <- e1 ;;
                    dv2 <- e2 ;;
                    eval_fcmp cmp dv1 dv2)

  | Concretize_Struct_Nil     : concretize_u (UVALUE_Struct []) (ret (DVALUE_Struct []))
  | Concretize_Struct_Cons    : forall u e us es,
      concretize_u u e ->
      concretize_u (UVALUE_Struct us) es ->
      concretize_u (UVALUE_Struct (u :: us))
                   (d <- e ;;
                    vs <- es ;;
                    match vs with
                    | (DVALUE_Struct ds) => ret (DVALUE_Struct (d :: ds))
                    | _ => failwith "illegal Struct Cons"
                    end)

  | Concretize_Array_Nil :
      concretize_u (UVALUE_Array []) (ret (DVALUE_Array []))

  | Concretize_Array_Cons : forall u e us es,
      concretize_u u e ->
      concretize_u (UVALUE_Array us) es ->
      concretize_u (UVALUE_Array (u :: us))
                   (d <- e ;;
                    vs <- es ;;
                    match vs with
                    | (DVALUE_Array ds) => ret (DVALUE_Array (d :: ds))
                    | _ => failwith "illegal Array cons"
                    end)
  .

  Definition concretize (uv: uvalue) (dv : dvalue) := concretize_u uv (ret dv).

End DVALUE.
