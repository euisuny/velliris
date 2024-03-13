From iris Require Import bi.bi.
From iris.proofmode Require Import proofmode.
From simuliris.simulation Require Import slsls simulation reduction.
From simuliris.vir Require Import vir heap spec.
From iris.prelude Require Import options.

(** Define (very basic) Hoare triple notations *)

Section fix_bi.

  Context `{!heapGS Σ, !heapbijGS Σ, !checkedoutGS Σ}.

  Definition hoareSim {R1 R2} P (e_t:_ R1) (e_s:_ R2) Φ : iProp Σ :=
    □ (P -∗ sim_expr Φ e_t e_s).
  Definition hoareTgt {R} P (e_t:_ R) Ψ : iProp Σ :=
    □ (P -∗ target_red (η := vir_handler) e_t Ψ).
  Definition hoareSrc {R} P (e_s:_ R) Ψ : iProp Σ :=
    □ (P -∗ source_red (η := vir_handler) e_s Ψ).
End fix_bi.

Notation "'{{{'  P  '}}}'  e_t  ⪯[  π  ] e_s   '{{{'  Φ  '}}}'" := (hoareSim P e_t e_s π Φ) (at level 10) : bi_scope.
Notation "'[{{'  P  '}}]'  e_t  '[{{'  Ψ  '}}]t'" := (hoareTgt P e_t Ψ) (at level 20) : bi_scope.
Notation "'[{{'  P  '}}]'  e_s  @  π  '[{{'  Ψ  '}}]s'" := (hoareSrc P e_s π Ψ) (at level 20) : bi_scope.
