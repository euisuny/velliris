(* begin hide *)
From Coq Require Import
     ZArith
     List
     String
     Setoid
     Morphisms
     Classes.RelationClasses.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv.

From Vellvm Require Import
     Utilities
     Syntax.LLVMAst.

Require Import Ceres.Ceres.

Set Implicit Arguments.
Set Contextual Implicit.
(* end hide *)

(** * Dynamic types
    LLVM types contain information unnecessary to the semantics of programs,
    and making them structurally annoying to reason about.
    We therefore pre-process them to convert them into so-called dynamic types,
    or [dtyp].
    These dynamic types differ from static ones in two aspects:
    - we have forget about the nature of the object pointer types point to
    - type variables have been resolved.
    The conversion from static types to dynamic types is defined in the module [TypToDtyp].
 *)

Unset Elimination Schemes.
Inductive dtyp : Set :=
| DTYPE_I (sz:N)
| DTYPE_Pointer
| DTYPE_Void
| DTYPE_Half
| DTYPE_Float
| DTYPE_Double
| DTYPE_X86_fp80
| DTYPE_Fp128
| DTYPE_Ppc_fp128
| DTYPE_Metadata
| DTYPE_X86_mmx
| DTYPE_Array (sz:N) (t:dtyp)
| DTYPE_Struct (fields:list dtyp)
| DTYPE_Opaque
.
Set Elimination Schemes.

Ltac dec_dtyp :=
  match goal with
  | [ |- { ?X ?a = ?X ?b} + { ?X ?a <> ?X ?b} ] => idtac
  | [ |- { ?X ?a = ?Y ?b} + { ?X ?a <> ?Y ?b} ] => right; intros H; inversion H
  | [ |- { ?X = ?X } + { ?X <> ?X } ] => left; reflexivity
  | [ |- { ?X = ?Y } + { ?X <> ?Y } ] => right; intros H; inversion H
  end.

Lemma dtyp_eq_dec : forall (t1 t2:dtyp), {t1 = t2} + {t1 <> t2}.
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
            end); try (ltac:(dec_dtyp); fail).
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

Definition dtyp_eqb (dt1 dt2 : dtyp) : bool
  := match @dtyp_eq_dec dt1 dt2 with
      | left x => true
      | right x => false
      end.

Definition vector_dtyp dt :=
  (exists n, dt = DTYPE_I n) \/ dt = DTYPE_Pointer \/ dt = DTYPE_Half \/ dt = DTYPE_Float \/
  dt = DTYPE_Double \/ dt = DTYPE_X86_fp80 \/ dt = DTYPE_Fp128 \/ dt = DTYPE_Ppc_fp128.

Section DtypInd.
  Variable P : dtyp -> Prop.
  Hypothesis IH_I             : forall a, P (DTYPE_I a).
  Hypothesis IH_Pointer       : P DTYPE_Pointer.
  Hypothesis IH_Void          : P DTYPE_Void.
  Hypothesis IH_Half          : P DTYPE_Half.
  Hypothesis IH_Float         : P DTYPE_Float.
  Hypothesis IH_Double        : P DTYPE_Double.
  Hypothesis IH_X86_fp80      : P DTYPE_X86_fp80.
  Hypothesis IH_Fp128         : P DTYPE_Fp128.
  Hypothesis IH_Ppc_fp128     : P DTYPE_Ppc_fp128.
  Hypothesis IH_Metadata      : P DTYPE_Metadata.
  Hypothesis IH_X86_mmx       : P DTYPE_X86_mmx.
  Hypothesis IH_Array         : forall sz t, P t -> P (DTYPE_Array sz t).
  Hypothesis IH_Struct        : forall (fields: list dtyp), (forall u, In u fields -> P u) -> P (DTYPE_Struct fields).
  Hypothesis IH_Opaque        : P DTYPE_Opaque.

  Lemma dtyp_ind : forall (dt:dtyp), P dt.
    fix IH 1.
    remember P as P0 in IH.
    destruct dt; auto; subst.
    - apply IH_Array. auto.
    - apply IH_Struct.
      { revert fields.
        fix IHfields 1. intros [|u fields']. intros. inversion H.
        intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
      }
  Qed.
End DtypInd.

Section WF_dtyp.

  Inductive well_formed_dtyp : dtyp -> Prop :=
  | Wf_I : forall sz, well_formed_dtyp (DTYPE_I sz)
  | Wf_Pointer : well_formed_dtyp DTYPE_Pointer
  | Wf_Void : well_formed_dtyp DTYPE_Void
  | Wf_Half : well_formed_dtyp DTYPE_Half
  | Wf_Float : well_formed_dtyp DTYPE_Float
  | Wf_Double : well_formed_dtyp DTYPE_Double
  | Wf_X86_fp80 : well_formed_dtyp DTYPE_X86_fp80
  | Wf_Fp128 : well_formed_dtyp DTYPE_Fp128
  | Wf_Ppc_fp128 : well_formed_dtyp DTYPE_Ppc_fp128
  | Wf_Metadata : well_formed_dtyp DTYPE_Metadata
  | Wf_X86_mmx : well_formed_dtyp DTYPE_X86_mmx
  | Wf_Opaque : well_formed_dtyp DTYPE_Opaque
  | Wf_Array : forall (sz : N),
      N.le 0 sz ->
      forall t, well_formed_dtyp t ->
           well_formed_dtyp (DTYPE_Array sz t)
  | Wf_Struct_nil :
      well_formed_dtyp (DTYPE_Struct nil)
  | Wf_Struct_cons :
      forall t, well_formed_dtyp t ->
           forall l, well_formed_dtyp (DTYPE_Struct l) ->
                well_formed_dtyp (DTYPE_Struct (t :: l))
  .

End WF_dtyp.

Fixpoint dtyp_measure (t : dtyp) : nat :=
  match t with
  | DTYPE_I sz => 0
  | DTYPE_Pointer => 0
  | DTYPE_Void => 0
  | DTYPE_Half => 0
  | DTYPE_Float => 0
  | DTYPE_Double => 0
  | DTYPE_X86_fp80 => 0
  | DTYPE_Fp128 => 0
  | DTYPE_Ppc_fp128 => 0
  | DTYPE_Metadata => 0
  | DTYPE_X86_mmx => 0
  | DTYPE_Array sz t => S (dtyp_measure t)
  | DTYPE_Struct fields => S (list_sum (map dtyp_measure fields))
  | DTYPE_Opaque => 0
  end.

Section hiding_notation.
  #[local] Open Scope sexp_scope.
  
  Fixpoint serialize_dtyp' (dt:dtyp): sexp :=
    match dt with
    | DTYPE_I sz     => Atom ("i" ++ to_string sz)%string
    | DTYPE_Pointer  => Atom "ptr"
    | DTYPE_Void     => Atom "dvoid"
    | DTYPE_Half     => Atom "half"
    | DTYPE_Float    => Atom "float"
    | DTYPE_Double   => Atom "double"
    | DTYPE_X86_fp80 => Atom "x86_fp80"
    | DTYPE_Fp128    => Atom "fp128"
    | DTYPE_Ppc_fp128 => Atom "ppc_fp128"
    | DTYPE_Metadata  => Atom "metadata"
    | DTYPE_X86_mmx   => Atom "x86_mmx"
    | DTYPE_Array sz t
      => [Atom ("[" ++ to_string sz) ; Atom "x" ; serialize_dtyp' t ; Atom "]"]%string
    | DTYPE_Struct fields
      => [Atom "{" ; to_sexp (List.map (fun x => [serialize_dtyp' x ; Atom ","]) fields) ; Atom "}"]
    | DTYPE_Opaque => Atom "opaque"
    end.

  #[global] Instance serialize_dtyp : Serialize dtyp := serialize_dtyp'.
End hiding_notation.
