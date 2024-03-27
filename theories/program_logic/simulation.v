(** Notational typeclasses for simulation relations. *)

From iris.bi Require Import bi.
From velliris.program_logic Require Import language.
From iris.prelude Require Import options.
Import bi.

From ITree Require Import ITree Eq.

(** Typeclass for the simulation relation so we can use the definitions with
   greatest+least fp (stuttering) or just greatest fp (no stuttering). *)
Class Sim (PROP: bi) (Λ : language):=
  sim : forall {R1 R2}, (R1 → R2 → PROP) → L2_expr Λ R1 → L2_expr Λ R2 → PROP.
(* We assume only one instance is ever in scope, hence no mode *)

(** Typeclass for the simulation relation so we can use the definitions with
   greatest+least fp (stuttering) or just greatest fp (no stuttering). *)
Class SimV (PROP : bi) (Λ : language) :=
  simV : forall {R1 R2}, (R1 → R2 → PROP) → expr Λ R1 → expr Λ R2 → PROP.
(* We assume only one instance is ever in scope, hence no mode *)

Class SimE (PROP : bi) (Λ : language) :=
  sim_expr : forall {R1 R2}, (expr Λ R1 → expr Λ R2 → PROP) → expr Λ R1 → expr Λ R2 → PROP.
(* We assume only one instance is ever in scope, hence no mode *)

(* FIXME what are good levels for et, es? *)

Notation "et '⪯' es ⦃ Φ ⦄" := (sim Φ et es) (at level 70, Φ at level 200,
  format "'[hv' et  '/' '⪯'  '/' es  '/' ⦃   Φ  ⦄ ']'") : bi_scope.
Notation "et '⪯' es {{ Φ }}" := (simV Φ et es) (at level 70, Φ at level 200,
  format "'[hv' et  '/' '⪯'  '/' es  '/' {{  '[ ' Φ  ']' }} ']'") : bi_scope.

(* FIXME: the notation with binder doesn't work; left-factoring seems to fail.
notation "et  '⪯'  es  {{  v_t  v_s ,  p  }}" := (sim et es (λ v_t v_s, p)) (at level 40, v_t, v_s at level 200, p at level 200) : bi_scope. *)

(* TODO: different symbols (no brackets) for expr thing *)
Notation "et '⪯' es [{ Φ }]" := (sim_expr Φ et es) (at level 70, Φ at level 200,
                                                     format "'[hv' et  '/' '⪯' '/' es  '/' [{  '[ ' Φ  ']' }] ']'") : bi_scope.
Notation "et '⪯' es [{ ( x ,  y  ) , Q }]" :=
  (sim_expr (fun e_t e_s => (∃ x y, ⌜e_t ≅ Ret x⌝ ∗ ⌜e_s ≅ Ret y⌝ ∗ Q)%I) et es)
    (at level 70, Q at level 200,
      format "'[hv' et  '/' '⪯'  '/' es  '/' [{  '[ ' ( x ,  y ) , '/' Q ']' }] ']'") : bi_scope.
