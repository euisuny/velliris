From iris.prelude Require Import options.

From velliris.program_logic Require Export weakest_pre.
From velliris.utils Require Import tactics.

From ITree Require Import ITree Eq.Eqit.

From Paco Require Import paco.

From Coq Require Import Program.Equality.

From Equations Require Import Equations.

Section weak_bisim.

  Context {PROP : bi} `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context {Λ : language} {η : handlers Λ}.
  Context {si : simulirisGS PROP Λ}.
  Set Default Proof Using "Type*".

  (* FIX: Share NonExpansive/Proper instances with [slsls] *)
  Notation st_expr_rel' R1 R2 := (@st_exprO' Λ R1 -d> @st_exprO' Λ R2 -d> PROP).
  Notation st_expr_rel R1 R2 := (@st_exprO Λ R1 -d> @st_exprO Λ R2 -d> PROP).
  Notation expr_rel R1 R2 := (@exprO Λ R1 -d> @exprO Λ R2 -d> PROP).
  Notation expr_rel' R1 R2 := (@exprO' Λ R1 -d> @exprO' Λ R2 -d> PROP).

  Local Instance expr_rel_func_ne {R1 R2} (F: expr_rel R1 R2 -d> expr_rel R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance expr_rel'_func_ne {R1 R2} (F: expr_rel' R1 R2 -d> expr_rel' R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance st_expr_rel'_func_ne {R1 R2} (F: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance st_expr_rel_func_ne {R1 R2} (F: st_expr_rel R1 R2 -d> st_expr_rel R1 R2) `{Hne: !NonExpansive F}:
    (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) F).
  Proof.
    intros n Φ Φ' HΦ e_t e_t' ->%discrete_iff%leibniz_equiv e_s e_s' ->%discrete_iff%leibniz_equiv
          ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Local Instance sim_expr_stutter : SimE PROP Λ := (sim_expr_aux (η := η)).(unseal).

  (* IY: Why doesn't TC resolution figure this out from the instance in [slsls]?
   [Existing Instance sim_coindF_ne] does not work either *)
  Global Instance sim_coindF_ne {R1 R2} : NonExpansive (sim_coindF (R1 := R1) (R2 := R2)).
  Proof. solve_proper. Qed.

  Ltac lf_unfold := rewrite sim_indF_unfold /sim_expr_inner; auto.
  Ltac IHR_unfold F := rewrite /sim_expr_inner; cbn -[F] in *.

  Ltac eqitF_eqit :=
    match goal with
      [ H: eqitF eq _ _ _ _ ?t1 ?t2  |- _ ] =>
      assert (go t1 ≈ go t2) by (pstep; auto)
    end.

  Ltac observe_auto :=
    let EQ := fresh "EQ" in
    let EQ' := fresh "EQ'" in
    match goal with
    | [H : ?t = TauF ?t' |- _] =>
      assert (EQ: go t ≈ go t) by reflexivity;
      assert (EQ': go t ≈ Tau t'); [ pstep;red;cbn;rewrite <- H; punfold EQ | ]
    end.

  Ltac eqit_auto :=
    try iPureIntro; try eqitF_eqit; try observe_auto;
    repeat match goal with
    | |- context[ {| _observe := observe _ |} ] => setoid_rewrite <- itree_eta
    end;
    repeat match goal with
    | [H : ?t = _ |- context[ {| _observe := ?t |} ]] => rewrite H
    | [H : ?t2 = TauF ?t |- _ ≈ Tau ?t] => pstep; red; rewrite <- H; cbn
    | |- _ ≈ Tau _ => rewrite tau_eutt
    | |- Tau _ ≈ _ => rewrite tau_eutt
    | [H : ?t ≈ _ |- ?t ≈ _] => rewrite H
    end; auto; try reflexivity.

  Ltac base_case :=
    iDestruct "IHR" as ">[IHR | IHR]";
    [ iLeft; iApply ("Hcont" with "IHR"); iPureIntro; eqit_auto | ].

  Ltac apply_IH F t :=
    match goal with
      | |- context[F _ ?t2 _] =>
        unfold F;
        iAssert (⌜ {| _observe := t |} ≈ {| _observe := t2 |} ⌝)%I as "temp_EQ"; [ try eqit_auto | ];
        try (iSpecialize ("IHR" with "temp_EQ Hcont Hcont' Hcont''"); iClear "temp_EQ"; try lf_unfold)
    end.

  Ltac ind_case :=
    iDestruct "IHR" as ">[IHR | [IHR | [IHR | IHR] ]]";
    [ iLeft; iApply ("Hcont" with "IHR"); iPureIntro; try eqit_auto | .. ].

  Ltac ifalso :=
    let H := fresh "H" in
    iDestruct "IHR" as ">%H"; inv H.

  Existing Instance sim_coindF_proper.

  Lemma sim_coindF_TauL_inv {R1 R2} (Φ: st_expr_rel R1 R2) t1 t2:
    ⊢ <pers>(∀ x y, Φ x y -∗ ∀ x', ⌜x' ≈ x⌝ -∗ ∀ y', ⌜y' ≈ y⌝ -∗ Φ x' y') -∗
     sim_indF sim_coindF (fun x y => Φ (go x) (go y)) (observe (Tau t1)) t2 -∗
     sim_indF sim_coindF (fun x y => Φ (go x) (go y)) (observe t1) t2.
  Proof.
    iIntros "#Hmono H".
    pose (F := (λ (Ψ:st_expr_rel' R1 R2) (e_t:st_exprO' R1) e_s,
                ∀ Φ,
                  (∀ (e_t : st_exprO' R1) (e_s : st_exprO' R2),
                      Ψ e_t e_s -∗
                            ∀ e_t' e_t'', ⌜TauF e_t' = e_t⌝ -∗ ⌜observe e_t' = e_t''⌝ -∗
                               sim_indF sim_coindF Φ e_t'' e_s)%I -∗

                  (* Introduced these for NonExpansive proof obligation, is there a better way around this? *)
                   (∀ x y, sim_coindF Ψ x y -∗ sim_coindF Φ x y) -∗
                   (∀ x y, Ψ x y -∗ Φ x y) -∗
                  (∀ (e_t : st_exprO' R1) (e_s : st_exprO R2),
                      Ψ e_t (TauF e_s) -∗ sim_indF sim_coindF Φ e_t (observe e_s))%I -∗

                    (∀ e_t' e_t'', ⌜TauF e_t' = e_t⌝ -∗ ⌜observe e_t' = e_t''⌝ -∗
                         sim_indF (R1 := R1) (R2 := R2) sim_coindF Φ e_t'' e_s)
               )%I).
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ (observe e_t) e_s) -∗ F Ψ (observe e_t) e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "H"); try done. unfold F.
      iApply "Hgen"; [ | |  | | | ].
      2,3 : iIntros; eauto.
      3,4 : cbn; iPureIntro; reflexivity.
      { iIntros (e_t e_s) "HΦ %e_t' %ot %EQ %EQ'". subst.
        rewrite sim_indF_unfold; eauto. rewrite /sim_expr_inner.
        provide_case: BASE.
        iApply ("Hmono" with "[HΦ]"); try done.
        iPureIntro. by rewrite <- itree_eta, tau_eutt. }
      { iIntros (e_t e_s) "HΦ". 
        rewrite sim_indF_unfold; eauto. rewrite /sim_expr_inner.
        provide_case: BASE.
        iApply ("Hmono" with "[HΦ]"); try done.
        iPureIntro. by rewrite <- itree_eta, tau_eutt. } }

    iIntros (Ψ e_t e_s) "Hsim".
    iApply (sim_indF_strong_ind (η := η) with "[] Hsim"); clear Ψ e_t e_s.
    { solve_proper_prepare. repeat f_equiv; eauto; apply H. }

    iModIntro. iIntros (Ψ e_t e_s) "IHR".

    rewrite {2}/F. iClear "Hmono". clear t1 t2 Φ.
    iIntros "%Φ Hcont HΦ HΦ' Hcont' %e_t' %ot %EQ %EQ'". subst.

    rewrite (sim_indF_unfold (η := η)). rewrite /sim_expr_inner.
    iMod "IHR".
    iDestruct "IHR" as (c) "IHR".
    destruct c.
    { iSpecialize ("Hcont" with "IHR").
      iSpecialize ("Hcont" $! _ _ eq_refl eq_refl).
      rewrite sim_indF_unfold; by eauto. }
    { rewrite /stutter_l.
      iDestruct "IHR" as (??) "[_ IHR]"; inv H.
      setoid_rewrite <- sim_indF_unfold; [ | typeclasses eauto].
      do 2 rewrite -sim_coindF_unfold.
      iApply ("HΦ" with "IHR").  }
    { rewrite /stutter_r.
      iDestruct "IHR" as (??) "[IHR _]"; subst.
      iSpecialize ("IHR" with "Hcont HΦ HΦ' Hcont'").
      iSpecialize ("IHR" $! _ _ eq_refl eq_refl).
      by provide_case: STUTTER_R. }
    { rewrite /tau_step.
      iDestruct "IHR" as (????) "IHR"; inv H; subst.
      provide_case: STUTTER_R.
      iSpecialize ("HΦ" with "IHR").
      by rewrite sim_coindF_unfold. }
    { rewrite /vis_step.
      iDestruct "IHR" as (???????) "IHR"; inv H.  }
    { rewrite /source_ub. 
      iDestruct "IHR" as (???) "%H"; subst.
      by provide_case: SOURCE_UB.  }
    { rewrite /source_exc. 
      iDestruct "IHR" as (???) "%H"; subst.
      by provide_case: SOURCE_EXC.  }
  Qed.

  Lemma sim_coindF_TauR_inv {R1 R2} (Φ: st_expr_rel R1 R2) t1 t2:
    ⊢ <pers>(∀ x y, Φ x y -∗ ∀ x', ⌜x' ≈ x⌝ -∗ ∀ y', ⌜y' ≈ y⌝ -∗ Φ x' y') -∗
     sim_indF sim_coindF (fun x y => Φ (go x) (go y)) (observe t1) (TauF t2) -∗
     sim_indF sim_coindF (fun x y => Φ (go x) (go y)) (observe t1) (observe t2).
  Proof.
    iIntros "#Hmono H".
    pose (F := (λ (Ψ:st_expr_rel' R1 R2) (e_t:st_exprO' R1) (e_s:st_exprO' R2),
                ∀ Φ,
                  (∀ (e_t : st_exprO' R1) (e_s : st_exprO' R2),
                      Ψ e_t e_s -∗
                            ∀ e_s' e_s'', ⌜TauF e_s' = e_s⌝ -∗ ⌜observe e_s' = e_s''⌝ -∗
                               sim_indF sim_coindF Φ e_t e_s'')%I -∗

                  (* Introduced these for NonExpansive proof obligation, is there a better way around this? *)
                   (∀ x y, sim_coindF Ψ x y -∗ sim_coindF Φ x y) -∗
                   (∀ x y, Ψ x y -∗ Φ x y) -∗
                  (∀ (e_t : st_exprO R1) (e_s : st_exprO' R2),
                      Ψ (TauF e_t) e_s -∗ sim_indF sim_coindF Φ (observe e_t) e_s)%I -∗

                    (∀ e_s' e_s'', ⌜TauF e_s' = e_s⌝ -∗ ⌜observe e_s' = e_s''⌝ -∗
                         sim_indF (R1 := R1) (R2 := R2) sim_coindF Φ e_t e_s'')
               )%I).
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ (observe e_t) e_s) -∗ F Ψ (observe e_t) e_s)%I as "Hgen"; last first.
    { iSpecialize ("Hgen" with "H"); try done. unfold F.
      iApply "Hgen"; [ | |  | | | ].
      2,3 : iIntros; eauto.
      3,4 : cbn; iPureIntro; reflexivity.
      { iIntros (e_t e_s) "HΦ %e_t' %ot %EQ %EQ'". subst.
        rewrite sim_indF_unfold; eauto. rewrite /sim_expr_inner.
        provide_case: BASE.
        iApply ("Hmono" with "[HΦ]"); try done.
        iPureIntro. by rewrite <- itree_eta, tau_eutt. }
      { iIntros (e_t e_s) "HΦ". 
        rewrite sim_indF_unfold; eauto. rewrite /sim_expr_inner.
        provide_case: BASE.
        iApply ("Hmono" with "[HΦ]"); try done.
        iPureIntro. by rewrite <- itree_eta, tau_eutt. } }

    iIntros (Ψ e_t e_s) "Hsim".
    iApply (sim_indF_strong_ind (η := η) with "[] Hsim"); clear Ψ e_t e_s.
    { solve_proper_prepare. repeat f_equiv; eauto; apply H. }

    iModIntro. iIntros (Ψ e_t e_s) "IHR".

    rewrite {2}/F. iClear "Hmono". clear t1 t2 Φ.
    iIntros "%Φ Hcont HΦ HΦ' Hcont' %e_t' %ot %EQ %EQ'". subst.

    rewrite (sim_indF_unfold (η := η)). rewrite /sim_expr_inner.
    iMod "IHR".
    iDestruct "IHR" as (c) "IHR".
    destruct c.
    { iSpecialize ("Hcont" with "IHR").
      iSpecialize ("Hcont" $! _ _ eq_refl eq_refl).
      rewrite sim_indF_unfold; by eauto. }
    { rewrite /stutter_l.
      iDestruct "IHR" as (??) "[IHR _ ]"; subst.
      iSpecialize ("IHR" with "Hcont HΦ HΦ' Hcont'").
      iSpecialize ("IHR" $! _ _ eq_refl eq_refl).
      by provide_case: STUTTER_L. }
    { rewrite /stutter_r.
      iDestruct "IHR" as (??) "[_ IHR]"; inv H; subst.
      setoid_rewrite <- sim_indF_unfold; [ | typeclasses eauto].
      rewrite -!sim_coindF_unfold.
      iApply ("HΦ" with "IHR").  }
    { rewrite /tau_step.
      iDestruct "IHR" as (????) "IHR"; inv H0; subst.
      provide_case: STUTTER_L.
      iSpecialize ("HΦ" with "IHR").
      by rewrite sim_coindF_unfold. }
    { rewrite /vis_step.
      iDestruct "IHR" as (????????) "IHR"; inv H0.  }
    { rewrite /source_ub. 
      iDestruct "IHR" as (???) "%H"; subst.
      by provide_case: SOURCE_UB.  }
    { rewrite /source_exc. 
      iDestruct "IHR" as (???) "%H"; subst.
      by provide_case: SOURCE_EXC.  }
    Unshelve. all :eauto.
  Qed.

  Local Definition euttL_pred {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
      (<pers>(∀ x y, Φ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y') ∗
        ∃ e_t', ⌜go e_t ≈ go e_t'⌝ ∗ sim_coindF (fun e_t'' e_s'' => ∀ e_t''', ⌜go e_t''' ≈ go e_t''⌝ -∗ Φ e_t''' e_s'') e_t' e_s)%I.

  Local Definition euttL_rec {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
      (<pers>(∀ x y, Φ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y') ∗
        (∃ e_t', ⌜go e_t ≈ go e_t'⌝ ∗ sim_coindF (fun e_t'' e_s'' => ∀ e_t''', ⌜go e_t''' ≈ go e_t''⌝ -∗ Φ e_t''' e_s'') e_t' e_s) ∨ sim_coindF Φ e_t e_s)%I.

  Local Instance euttL_pred_ne {R1 R2}: NonExpansive (euttL_pred: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv; repeat intro; repeat f_equiv; try apply H.
  Qed.

  Local Instance euttL_rec_ne {R1 R2}: NonExpansive (euttL_rec: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv; auto;  repeat intro; repeat f_equiv; try apply H.
  Qed.

  Lemma sim_coindF_eutt_transL {R1 R2} (Φ : st_exprO R1 -d> st_exprO R2 -d> PROP) ot1 ot2 ot3:
    ⊢ ⌜Proper (eutt eq ==> eutt eq ==> equiv) Φ⌝ -∗
      ⌜go ot1 ≈ go ot2⌝ -∗
      sim_coindF (fun x y => Φ (go x) (go y)) ot2 ot3 -∗
      sim_coindF (fun x y => Φ (go x) (go y)) ot1 ot3.
  Proof.
    iIntros "%HΦ %EQ Hpre".

    (* Initialize greatest fixpoint *)
    iApply (sim_coindF_strong_coind euttL_pred); last first.
    { iSplitR.
      { iModIntro. iIntros. iApply HΦ; eauto. }
      iExists ot2. iSplitR; auto.
      iApply sim_coindF_bupd_mono; [ | done].
      iIntros (e_t e_s) "HΦ'".
      iModIntro. iIntros (e_t') "%Ht".
      iApply HΦ; eauto. reflexivity. }
    iModIntro.
    iIntros (Ψ t s) "IH".

    change (sim_indF _ Ψ t s) with (sim_indF euttL_rec Ψ t s).
    rewrite /euttL_pred.
    iDestruct "IH" as "[#HΨ [%e_tp [%Eqt H]]]".

    rewrite {1}sim_coindF_unfold.
    (* We introduce a functor [F] for inducting on the simulation that we have in our context. *)
    pose (F := (λ Ψ e_t e_s,
                ∀ Φ e_t'',
                  ⌜go e_t'' ≈ go e_t⌝ -∗
                  (* Ψ and Φ are logically equivalent *)
                    (<pers>(∀ x y, Ψ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y')) -∗
                    (<pers>(∀ x y, Φ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Ψ x' y')) -∗
                  (* Ψ and Φ are stable under [eutt] *)
                    (<pers>(∀ x y, Ψ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Ψ x' y')) -∗
                    (<pers>(∀ x y, Φ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y')) -∗
                  sim_indF (R1 := R1) (R2 := R2) euttL_rec Φ e_t'' e_s)%I).

    (* Assertion [Ω] *)
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗ F Ψ e_t e_s)%I as "Hgen"; last first.
    { iApply ("Hgen" with "H"); try done.
      { iModIntro.
        iIntros (e_t'' e_s'') "H". iIntros (e_t''') "Ht".
        iSpecialize ("H" with "Ht"). iIntros. iApply ("HΨ" with "H"); eauto. }
      { iModIntro.
        iIntros (e_t'' e_s'') "H". iIntros (e_t''') "%Ht %e_s''' %Hs %e_t'''' %Ht'".
        iSpecialize ("HΨ" with "H"). iApply "HΨ"; iPureIntro; try done. 
        by rewrite Ht' Ht. }
      { iModIntro.
        iIntros (e_t'' e_s'') "H". iIntros (e_t''') "%Ht %e_s''' %Hs %e_t'''' %Ht'".
        iSpecialize ("H" $! _ Ht).
        iApply ("HΨ" with "H"); iPureIntro; done.  } }

    iClear "HΨ".
    clear Ψ HΦ Φ Eqt t s e_tp ot1 ot2 ot3 e_tp EQ.
    iIntros (Ψ e_t e_s) "Hsim".

    (* Induction on [sim e_t e_s] *)
    iApply (sim_indF_ind with "[] Hsim"); clear Ψ e_t e_s.
    { solve_proper_prepare. clear -H. repeat f_equiv; apply H. }

    iModIntro. iIntros (Ψ t2 t3) "IHR".
    iIntros (Φ t1) "%Ht #Himpl #Himpl' #HΨ #HΦ".

    (* Set up [Ht] for induction later *)
    punfold Ht; red in Ht; cbn in Ht.

    rewrite sim_indF_unfold. rewrite /sim_expr_inner; iMod "IHR".
    change (
        |==>
          ∃ c : sim_case,
            match c with
            | BASE => Φ t1 t3
            | STUTTER_L => stutter_l
            | STUTTER_R => stutter_r
            | TAU_STEP => tau_step
            | VIS_STEP => vis_step t1 t3
            | SOURCE_UB => source_ub
            | SOURCE_EXC => source_exc
            end)%I
      with (sim_expr_inner euttL_rec (sim_indF euttL_rec) Φ t1 t3).
    rewrite -sim_indF_unfold; auto.

    iDestruct "IHR" as (c) "IHR".
    destruct c eqn: Hc.

    { (* Base case *)
      rewrite sim_indF_unfold; auto; rewrite /sim_expr_inner.
      provide_case: BASE.
      iApply ("Himpl" with "IHR"); iPureIntro; try done; by pstep. }

    { (* Left stutter case *)
      rewrite sim_indF_unfold; auto; rewrite /sim_expr_inner.
      iDestruct "IHR" as (??) "IHR"; subst.
      rewrite /F.
      assert (go t1 ≈ go t2) by (by pstep); clear Ht.
      assert ({| _observe := t1 |} ≈ {| _observe := observe t |}).
      { rewrite <- itree_eta, <- (tau_eutt t).
        rewrite H0; by rewrite H. }

      iSpecialize ("IHR" $! Φ _ H1 with "Himpl Himpl' HΨ HΦ").
      by rewrite sim_indF_unfold /sim_expr_inner. }

    { (* Right stutter case *)
      rewrite sim_indF_unfold; auto; rewrite /sim_expr_inner.
      iDestruct "IHR" as (??) "IHR"; subst.
      rewrite /F.
      provide_case: STUTTER_R.
      assert ({| _observe := t1 |} ≈ {| _observe := t2 |}) by (by pstep).

      iSpecialize ("IHR" $! Φ _ H0 with "Himpl Himpl' HΨ HΦ").
      by rewrite sim_indF_unfold /sim_expr_inner. }

    { (* Lock-step tau case *)
      iDestruct "IHR" as (????) "IHR"; subst.

      (* case analysis on whether or not t1 has [tau] on prefix
          case tau : t1 has Tau prefix -- use "IHR"
          case non-tau : t1 has non-tau prefix -- induction on Ht *)
      assert (DEC: (exists s1, t1 = TauF s1) \/ (forall s1, t1 <> TauF s1)).
      { destruct t1; eauto; right; red; intros; inv H. }

      destruct DEC.
      (* case tau *)
      { destruct H1 as (?&?); subst.
        rewrite sim_indF_unfold; auto; rewrite /sim_expr_inner.
        provide_case:TAU_STEP.
        iLeft. iSplitL ""; [ by iModIntro | ].
        iExists (observe t).
        iSplitL "".
        { iPureIntro.
          assert (Tau x ≈ go t2) by (by pstep).
          assert (Tau x ≈ Tau t).
          { rewrite H1; by rewrite H. }
          do 2 rewrite <- itree_eta.
          by do 2 rewrite tau_eutt in H2. }
        iApply sim_coindF_bupd_mono; [ | iApply "IHR"].
        iIntros (??) "HΨ'".
        iModIntro; iIntros; by iApply ("Himpl" with "HΨ'"). }

      (* case non-tau: resolve totally by induction *)
      { rename Ht into INL.
        inv INL; try (exfalso; eapply H1; eauto; fail); pclearbot; try inv H.
        remember (observe t) as ot eqn: Hot. clear Hot.

        iInduction REL as [] "IHL" forall "IHR"; subst; try (exfalso; eapply H1; eauto; fail).
        - iAssert (sim_coindF Ψ (RetF r2) (TauF s))%I with "[IHR]" as "H".
          { by iApply sim_coindF_tauR. }
          rewrite sim_coindF_unfold; auto; inversion H0; subst.
          iApply (sim_indF_mono sim_coindF euttL_rec); cycle 1.
          { iApply sim_indF_post_mono; [ | | done].
            { iModIntro.
              iIntros (??) "H %e_t %e_s Hc".
              iApply (sim_coindF_bupd_mono with "H Hc"). }
            iIntros (??) "H"; iModIntro; iApply ("Himpl" with "H"); done. }
          iModIntro. iIntros (???) "H".
          rewrite /euttL_rec. by iRight.
        - inversion H0. rewrite sim_indF_unfold; auto; rewrite /sim_expr_inner.
          provide_case:STUTTER_R.

          set (term' := itree' (L2 Λ) (state Λ * R1)).
          set (term := itree (L2 Λ) (state Λ * R1)).
          pose (F' := (λ Ψ (t2:term') t3,
                  ⌜forall s1 : itree (L2 Λ) (state Λ * R1), (VisF e k2 : term') <> TauF s1⌝ -∗ ⌜t2 = VisF e k2⌝ -∗
                   ∀ Φ t2', ⌜t2' = VisF e k1⌝ -∗
                  ⌜∀ v : u, paco2 (eqit_ eq true true id) bot2 (k1 v) (k2 v)⌝ -∗
                    (<pers>(∀ x y, Ψ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y')) -∗
                    (<pers>(∀ x y, Φ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y')) -∗
                    (<pers>(∀ x y, Ψ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Ψ x' y')) -∗
                  sim_indF (R1 := R1) (R2 := R2) euttL_rec Φ t2' t3)%I).
          iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗ F' Ψ e_t e_s)%I as "Hgen"; last first.
          { rewrite sim_coindF_unfold; auto. iApply ("Hgen" with ("IHR")); eauto.
            iPureIntro; intros; by pclearbot. }

          iClear "Himpl Himpl' HΨ HΦ". clear Ψ t3 Φ t s H0 H2.
          iIntros (Ψ e_t e_s) "Hsim".
          (* Induction on [sim e_t e_s] *)
          iApply (sim_indF_ind with "[] Hsim"); clear Ψ e_t e_s.
          { solve_proper_prepare. clear -H. repeat f_equiv; eauto; apply H.  }
          iModIntro. iIntros (Ψ t2 t3) "IHR".

          iIntros "%EQ %H" (Φ t2')  "%HΨ %H' #Hcont #Hcont' #Hcont''".
          subst.
          destruct t3.
          + rewrite /sim_expr_inner. rewrite sim_indF_unfold /sim_expr_inner; auto.
            iMod "IHR".
            iDestruct "IHR" as (?) "IHR".
            destruct c.
            { provide_case: BASE. iApply ("Hcont" with "IHR"); try done.
              iPureIntro; eapply eqit_Vis; eauto. }
            { iDestruct "IHR" as (??) "IHR". inv H. }
            { iDestruct "IHR" as (??) "IHR"; inv H. }
            { iDestruct "IHR" as (???) "IHR"; inv H. }
            { iDestruct "IHR" as (????????) "IHR". inv H0. }
            { iDestruct "IHR" as (???) "%H"; inv H. }
            { iDestruct "IHR" as (???) "%H"; inv H. }
          + rewrite /sim_expr_inner. rewrite sim_indF_unfold /sim_expr_inner; auto.
            iMod "IHR".
            iDestruct "IHR" as (?) "IHR".
            destruct c; cycle 2.
            { provide_case: STUTTER_R.
              iDestruct "IHR" as (??) "IHR"; inversion H.
              iApply "IHR"; try done. }
            { iDestruct "IHR" as (???) "IHR"; inv H. }
            { iDestruct "IHR" as (????????) "IHR". inv H0. }
            { iDestruct "IHR" as (???) "%H". inv H. }
            { iDestruct "IHR" as (???) "%H". inv H. }
            { provide_case: BASE. iApply ("Hcont" with "IHR"); try done.
              iPureIntro; eapply eqit_Vis; eauto. }
            { iDestruct "IHR" as (??) "IHR". inv H. }
          + rewrite /sim_expr_inner. rewrite sim_indF_unfold /sim_expr_inner; auto.
            iMod "IHR".
            iDestruct "IHR" as (?) "IHR".
            destruct c; cycle 4.
            { iDestruct "IHR" as (????????) "IHR".
              dependent destruction H.
              dependent destruction H0.
              provide_case: VIS_STEP.
              destruct e_t, e_s; cbn; try done.
              { destruct c, c0, p, p0. simp handle_call_events.
                iDestruct "IHR" as "[ Hinner | Hinner]";
                [iLeft | iRight];
                  iDestruct "Hinner" as (?) "(SI & H1 & H2)";
                  iExists _; iFrame;
                iIntros (??)"H"; iSpecialize ("H2" with "H");
                iLeft; iMod "H2"; iModIntro.

                { iSplitL ""; [ done | ].
                  iExists (observe (k_t (v_t.1, call_returns c v_t.2)));
                  iSplitL "".
                  { iPureIntro. rewrite -!itree_eta. eapply H'. }
                  iApply sim_coindF_bupd_mono; [ | iApply "H2"].
                  iIntros (??) "H". iModIntro.
                  iIntros (??). iApply ("Hcont" with "H"); done. }

                { iSplitL ""; [ done | ];
                  iExists (observe (k_t v_t));
                  iSplitL "".
                  { iPureIntro. rewrite -!itree_eta. eapply H'. }
                  iApply sim_coindF_bupd_mono; [ | iApply "H2"].
                  iIntros (??) "H". iModIntro.
                  iIntros (??). iApply ("Hcont" with "H"); done. } }
              { destruct s, s0; try done.
                destruct s, s0; try done. rewrite /handle_E.
                iDestruct "IHR" as (?) "IHR".
                destruct H as (?&?). destruct x; destruct H.
                iSplitL "".
                { iPureIntro; exists eq_refl; reflexivity. }
                { iIntros (??) "H"; iMod ("IHR" with "H") as "IHR".
                  iLeft. iModIntro.
                  iSplitL ""; [ done | ].
                  iExists (observe (k_t v_t)).
                  iSplitL "".
                  { iPureIntro. rewrite -!itree_eta. eapply H'. }
                  iApply sim_coindF_bupd_mono; [ | iApply "IHR"].
                  iIntros (??) "H". iModIntro.
                  iIntros (??). iApply ("Hcont" with "H"); done. } } }
            { iDestruct "IHR" as (???) "%H". dependent destruction H.
              by provide_case: SOURCE_UB. }
            { iDestruct "IHR" as (???) "%H". dependent destruction H.
              by provide_case: SOURCE_EXC. }
            { provide_case: BASE. iApply ("Hcont" with "IHR"); try done.
              iPureIntro; eapply eqit_Vis; eauto. }
            { iDestruct "IHR" as (??) "IHR"; inv H. }
            { iDestruct "IHR" as (??) "IHR"; inv H. }
            { iDestruct "IHR" as (???) "IHR". inv H. }
        - iSpecialize ("IHL" $! H1).
          iAssert (sim_coindF Ψ (observe t2) (observe s)) with "[IHR]" as "Ht".
          { iApply sim_coindF_bupd_mono; cycle 1.
            { setoid_rewrite sim_coindF_unfold at 3; auto.
            iApply (sim_coindF_TauL_inv (fun x y => Ψ (observe x) (observe y))); cycle 1.
            { cbn. setoid_rewrite sim_coindF_unfold at 2; auto. }
            { iModIntro. iIntros (??) "H %x' %Hx %y' %Hy".
              iApply ("HΨ" with "H"); rewrite -!itree_eta; done. } }
            cbn. by iIntros (??) "H". }
          iApply ("IHL" with "Ht"). } }

    { iDestruct "IHR" as (????????) "IHR".
      inversion H; inversion H0; subst; clear H H0.
      remember (VisF e_t k_t) as ot.

      iInduction Ht as [] "IHL" forall "IHR"; subst; try inv Heqot; cycle 1.
      { setoid_rewrite sim_indF_unfold at 2; auto; [ | typeclasses eauto].
        rewrite /sim_expr_inner.
        provide_case: STUTTER_L.
        by iApply "IHL". }
      { rewrite sim_indF_unfold; auto. rewrite /sim_expr_inner.
        provide_case: VIS_STEP.

        dependent destruction H1.
        destruct e_t, e_s; cbn; try done.
        { destruct c, c0, p, p0. simp handle_call_events.
          iDestruct "IHR" as "[ Hinner| Hinner]";
          [iLeft | iRight];
            iDestruct "Hinner" as (?) "(SI & H1 & H2)";
            iExists _; iFrame;
          iIntros (??) "H"; iSpecialize ("H2" with "H");
          iLeft; iMod "H2"; iModIntro.
          { iSplitL ""; [ done | ].
            iExists (observe (k_t (v_t.1, call_returns c v_t.2))).
            iSplitL "".
            { iPureIntro. rewrite -!itree_eta. pclearbot. eapply REL. }
            iApply sim_coindF_bupd_mono; [ | iApply "H2"].
            iIntros (??) "H". iModIntro.
            iIntros (??). iApply ("Himpl" with "H"); done. }
          { iSplitL ""; [ done | ]; iExists (observe (k_t v_t)).
            iSplitL "".
            { iPureIntro. rewrite -!itree_eta. pclearbot. eapply REL. }
            iApply sim_coindF_bupd_mono; [ | iApply "H2"].
            iIntros (??) "H". iModIntro.
            iIntros (??). iApply ("Himpl" with "H"); done. } }
        { destruct s, s0; try done.
          destruct s, s0; try done. rewrite /handle_E.
          iDestruct "IHR" as (?) "IHR".
          destruct H as (?&?). destruct x; destruct H.
          iSplitL "".
          { iPureIntro; exists eq_refl; reflexivity. }
          { iIntros (??) "H"; iMod ("IHR" with "H") as "IHR".
            iLeft. iModIntro.
            iSplitL ""; [ done | ].
            iExists (observe (k_t v_t)).
            iSplitL "".
            { iPureIntro. rewrite -!itree_eta. pclearbot. eapply REL. }
            iApply sim_coindF_bupd_mono; [ | iApply "IHR"].
            iIntros (??) "H". iModIntro.
            iIntros (??). iApply ("Himpl" with "H"); done. } } } }
    { iDestruct "IHR" as (???) "%H"; subst. inversion H.
      rewrite sim_indF_unfold; auto. rewrite /sim_expr_inner.
      by provide_case: SOURCE_UB. }
    { iDestruct "IHR" as (???) "%H"; subst. inversion H.
      rewrite sim_indF_unfold; auto. rewrite /sim_expr_inner.
      by provide_case: SOURCE_EXC. }
   Unshelve. all : auto.
  Qed.

  Local Definition euttR_pred {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
    (<pers>(∀ x y, Φ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y') ∗
      ∃ e_s', ⌜go e_s ≈ go e_s'⌝ ∗
        sim_coindF (fun e_t'' e_s'' => ∀ e_s''', ⌜go e_s''' ≈ go e_s''⌝ -∗ Φ e_t'' e_s''') e_t e_s')%I.

  Local Definition euttR_rec {R1 R2} :=
    fun (Φ:st_expr_rel' R1 R2) (e_t:st_expr' Λ R1) (e_s:st_expr' Λ R2) =>
    ((<pers>(∀ x y, Φ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y') ∗
      ∃ e_s', ⌜go e_s ≈ go e_s'⌝ ∗
               sim_coindF (fun e_t'' e_s'' => ∀ e_s''', ⌜go e_s''' ≈ go e_s''⌝ -∗ Φ e_t'' e_s''') e_t e_s') ∨
    sim_coindF Φ e_t e_s)%I.

  Local Instance euttR_pred_ne {R1 R2}: NonExpansive (euttR_pred: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv; repeat intro; repeat f_equiv; try apply H.
  Qed.

  Local Instance euttR_rec_ne {R1 R2}: NonExpansive (euttR_rec: st_expr_rel' R1 R2 -d> st_expr_rel' R1 R2).
  Proof.
    intros x y * H *. solve_proper_prepare. repeat f_equiv; auto;  repeat intro; repeat f_equiv; try apply H.
  Qed.

  Ltac apply_IH' F t :=
    match goal with
    | |- context [ F _ _ ?t2 ] =>
          unfold F; iAssert ⌜{| _observe := t |} ≈ {| _observe := t2 |}⌝%I as "temp_EQ"; [ try eqit_auto |  ];
          try (iSpecialize ("IHR" with "temp_EQ Hcont Hcont' Hcont''"); iClear "temp_EQ"; try lf_unfold)
    end.

  Lemma sim_coindF_eutt_transR {R1 R2} (Φ : st_expr_rel R1 R2) ot1 ot2 ot3:
    ⊢ ⌜Proper (eutt eq ==> eutt eq ==> equiv) Φ⌝ -∗
      ⌜go ot2 ≈ go ot3⌝ -∗
      sim_coindF (fun x y => Φ (go x) (go y)) ot1 ot2 -∗
      sim_coindF (fun x y => Φ (go x) (go y)) ot1 ot3.
  Proof.
    iIntros "%HΦ %EQ Hpre".

    (* Initialize greatest fixpoint *)
    iApply (sim_coindF_strong_coind euttR_pred); last first.
    { iSplitR.
      { iModIntro. iIntros. iApply HΦ; eauto. }
      iExists ot2. iSplitR; auto.
      iApply sim_coindF_bupd_mono; [ | done].
      iIntros (e_t e_s) "HΦ'".
      iModIntro. iIntros (e_t') "%Ht".
      iApply HΦ; eauto. reflexivity. }
    iModIntro.
    iIntros (Ψ t s) "IH".

    change (sim_indF _ Ψ t s) with (sim_indF euttR_rec Ψ t s).
    rewrite /euttR_pred.
    iDestruct "IH" as "[#HΨ [%e_sp [%Eqs H]]]".

    rewrite {1}sim_coindF_unfold.
    (* We introduce a functor [F] for inducting on the simulation that we have in our context. *)
    pose (F := (λ Ψ e_t e_s,
                ∀ Φ e_s'',
                  ⌜go e_s'' ≈ go e_s⌝ -∗
                    (<pers>(∀ x y, Ψ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y')) -∗
                    (<pers>(∀ x y, Ψ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Ψ x' y')) -∗
                    (<pers>(∀ x y, Φ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y')) -∗
                  sim_indF (R1 := R1) (R2 := R2) euttR_rec Φ e_t e_s'')%I).
    (* Assertion [Ω] *)
    iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗ F Ψ e_t e_s)%I as "Hgen"; last first.
    { iApply ("Hgen" with "H"); try done.
      { iModIntro.
        iIntros (e_t'' e_s'') "H". iIntros (e_t''') "%Ht %e_s''' Hs".
        iSpecialize ("H" with "Hs"). iIntros. iApply ("HΨ" with "H"); eauto. }
      { iModIntro.
        iIntros (e_t'' e_s'') "H". iIntros (e_t''') "%Ht %e_s''' Hs".
        iSpecialize ("H" with "Hs"). iIntros. iApply ("HΨ" with "H"); eauto. } }

    iClear "HΨ".
    clear Ψ HΦ Φ Eqs t s e_sp ot1 ot2 ot3 e_sp EQ.
    iIntros (Ψ e_t e_s) "Hsim".

    (* Induction on [sim e_t e_s] *)
    iApply (sim_indF_ind with "[] Hsim"); clear Ψ e_t e_s.
    { solve_proper_prepare. clear -H. repeat f_equiv; apply H. }

    iModIntro. iIntros (Ψ t2 t3) "IHR".
    iIntros (Φ t1) "%Ht #Himpl #HΨ #HΦ".

    (* Set up [Ht] for induction later *)
    punfold Ht; red in Ht; cbn in Ht.

    rewrite sim_indF_unfold /sim_expr_inner; iMod "IHR".
    change (
        |==>
          ∃ c : sim_case,
            match c with
            | BASE => Φ t2 t1
            | STUTTER_L => stutter_l
            | STUTTER_R => stutter_r
            | TAU_STEP => tau_step
            | VIS_STEP => vis_step t2 t1
            | SOURCE_UB => source_ub
            | SOURCE_EXC => source_exc
            end)%I
      with (sim_expr_inner euttR_rec (sim_indF euttR_rec) Φ t2 t1).
    rewrite -sim_indF_unfold; auto.

    iDestruct "IHR" as (c) "IHR".
    destruct c eqn: Hc.

    { (* Base case *)
      rewrite sim_indF_unfold; auto; rewrite /sim_expr_inner.
      provide_case: BASE.
      iApply ("Himpl" with "IHR"); iPureIntro; try done; by pstep. }

    { (* Left stutter case *)
      rewrite sim_indF_unfold; auto; rewrite /sim_expr_inner.
      iDestruct "IHR" as (??) "IHR"; subst.
      rewrite /F.
      provide_case: STUTTER_L.
      assert ({| _observe := t1 |} ≈ {| _observe := t3 |}) by (by pstep).

      iSpecialize ("IHR" $! Φ _ H0 with "Himpl HΨ HΦ").
      by rewrite sim_indF_unfold /sim_expr_inner. }

    { (* Right stutter case *)
      rewrite sim_indF_unfold; auto; rewrite /sim_expr_inner.
      iDestruct "IHR" as (??) "IHR"; subst.
      rewrite /F.
      assert ({| _observe := t1 |} ≈ {| _observe := observe s |}).
      { rewrite <- itree_eta, <- (tau_eutt s). inversion H; subst.
        by pstep. }

      iSpecialize ("IHR" $! Φ _ H0 with "Himpl HΨ HΦ").
      by rewrite sim_indF_unfold /sim_expr_inner. }

    { (* Lock-step tau case *)
      iDestruct "IHR" as (????) "IHR"; subst; inv H; inv H0.

      (* case analysis on whether or not t1 has [tau] on prefix
          case tau : t1 has Tau prefix -- use "IHR"
          case non-tau : t1 has non-tau prefix -- induction on Ht *)
      assert (DEC: (exists s1, t1 = TauF s1) \/ (forall s1, t1 <> TauF s1)).
      { destruct t1; eauto; right; red; intros; inv H. }

      destruct DEC.
      (* case tau *)
      { destruct H as (?&?); subst.
        rewrite sim_indF_unfold; auto; rewrite /sim_expr_inner.
        provide_case:TAU_STEP.
        iLeft. iSplitL ""; [ by iModIntro | ].
        iExists (observe s).
        iSplitL "".
        { iPureIntro.
          assert (Tau x ≈ Tau s).
          { by pstep. }
          rewrite !tau_eutt in H.
          by rewrite -!itree_eta. }
        iApply sim_coindF_bupd_mono; [ | iApply "IHR"].
        iIntros (??) "HΨ'".
        iModIntro; iIntros; by iApply ("Himpl" with "HΨ'"). }

      (* case non-tau: resolve totally by induction *)
      { rename Ht into INL.
        inv INL; try (exfalso; eapply H; eauto; fail); pclearbot; try inv H.
        remember (observe s) as ot eqn: Hot. clear Hot.

        iInduction REL as [] "IHL" forall "IHR"; subst;
           try (exfalso; eapply H; eauto; fail); pclearbot.
        - iAssert (sim_coindF Ψ (TauF t) (RetF r2))%I with "[IHR]" as "H".
          { by iApply sim_coindF_tauL. }
          rewrite sim_coindF_unfold; auto.
          iApply (sim_indF_mono sim_coindF euttR_rec); cycle 1.
          { iApply sim_indF_post_mono; [ | | done].
            { iModIntro.
              iIntros (??) "H %e_t %e_s Hc".
              iApply (sim_coindF_bupd_mono with "H Hc"). }
            iIntros (??) "H"; iModIntro; iApply ("Himpl" with "H"); done. }
          iModIntro. iIntros (???) "H".
          rewrite /euttR_rec. by iRight.

        - rewrite sim_indF_unfold; auto; rewrite /sim_expr_inner.
          provide_case:STUTTER_L.

          set (term' := itree' (L2 Λ) (state Λ * R2)).
          set (term := itree (L2 Λ) (state Λ * R2)).

          pose (F' := (λ Ψ t3 (t2:term'),
                  ⌜forall s1 : itree (L2 Λ) (state Λ * R2), (VisF e k1 : term') <> TauF s1⌝ -∗ ⌜t2 = VisF e k2⌝ -∗
                   ∀ Φ t2', ⌜t2' = VisF e k1⌝ -∗
                  ⌜∀ v : u, paco2 (eqit_ eq true true id) bot2 (k1 v) (k2 v)⌝ -∗
                    (<pers>(∀ x y, Ψ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y')) -∗
                    (<pers>(∀ x y, Φ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Φ x' y')) -∗
                    (<pers>(∀ x y, Ψ x y -∗ ∀ x', ⌜go x' ≈ go x⌝ -∗ ∀ y', ⌜go y' ≈ go y⌝ -∗ Ψ x' y')) -∗
                  sim_indF (R1 := R1) (R2 := R2) euttR_rec Φ t3 t2')%I).
          iAssert (∀ Ψ e_t e_s, (sim_indF sim_coindF Ψ e_t e_s) -∗ F' Ψ e_t e_s)%I as "Hgen"; last first.
          { rewrite sim_coindF_unfold; auto. iApply ("Hgen" with ("IHR")); eauto. }

          iClear "Himpl HΨ HΦ". clear Ψ Φ t s.
          iIntros (Ψ e_t e_s) "Hsim".
          (* Induction on [sim e_t e_s] *)
          iApply (sim_indF_ind with "[] Hsim"); clear Ψ e_t e_s.
          { solve_proper_prepare. clear -H0. repeat f_equiv; eauto; apply H0.  }
          iModIntro. iIntros (Ψ t2 t3) "IHR".

          iIntros "%EQ %HR" (Φ t2')  "%HΨ %H' #Hcont #Hcont' #Hcont''".
          subst.
          destruct t2.
          + rewrite /sim_expr_inner. rewrite sim_indF_unfold /sim_expr_inner; auto.
            iMod "IHR".
            iDestruct "IHR" as (?) "IHR".
            destruct c.
            { provide_case: BASE. iApply ("Hcont" with "IHR"); try done.
              iPureIntro; eapply eqit_Vis; eauto. }
            { iDestruct "IHR" as (??) "IHR". inv H0. }
            { iDestruct "IHR" as (??) "IHR"; inv H0. }
            { iDestruct "IHR" as (???) "IHR"; inv H0. }
            { iDestruct "IHR" as (????????) "IHR". inv H0. }
            { iDestruct "IHR" as (???) "%H0"; inv H0.
              dependent destruction H3.
              by provide_case: SOURCE_UB. }
            { iDestruct "IHR" as (???) "%H0"; inv H0.
              dependent destruction H3.
              by provide_case: SOURCE_EXC. }
          + rewrite /sim_expr_inner. rewrite sim_indF_unfold /sim_expr_inner; auto.
            iMod "IHR".
            iDestruct "IHR" as (?) "IHR".
            destruct c; cycle 2.
            { provide_case: STUTTER_R.
              iDestruct "IHR" as (??) "IHR"; inversion H0. }
            { iDestruct "IHR" as (????) "IHR"; inv H1. }
            { iDestruct "IHR" as (????????) "IHR". inv H0. }
            { iDestruct "IHR" as (???) "%H0". inv H0.
              dependent destruction H3.
              by provide_case: SOURCE_UB. }
            { iDestruct "IHR" as (???) "%H0". inv H0.
              dependent destruction H3.
              by provide_case: SOURCE_EXC. }
            { provide_case: BASE. iApply ("Hcont" with "IHR"); try done.
              iPureIntro; eapply eqit_Vis; eauto. }
            { iDestruct "IHR" as (??) "IHR".
              provide_case: STUTTER_L. inversion H0.
              iApply "IHR"; try done. }
          + rewrite /sim_expr_inner. rewrite sim_indF_unfold /sim_expr_inner; auto.
            iMod "IHR".
            iDestruct "IHR" as (?) "IHR".
            destruct c; cycle 4.
            { iDestruct "IHR" as (????????) "IHR".
              dependent destruction H1.
              provide_case: VIS_STEP.
              destruct e_t, e_s; cbn; try done.
              { destruct c, c0, p, p0. simp handle_call_events.
                iDestruct "IHR" as "[ Hinner | Hinner]";
                [iLeft | iRight];
                  iDestruct "Hinner" as (?) "(SI & H1 & H2)";
                  iExists _; iFrame;
                iIntros (??)"H"; iSpecialize ("H2" with "H");
                iLeft; iMod "H2"; iModIntro.
                { iSplitL ""; [ done | ].
                  iExists (observe (k_s (v_s.1, call_returns c0 v_s.2))).
                  iSplitL "".
                  { iPureIntro. rewrite -!itree_eta. eapply H'. }
                  iApply sim_coindF_bupd_mono; [ | iApply "H2"].
                  iIntros (??) "H". iModIntro.
                  iIntros (??). iApply ("Hcont" with "H"); done. }

                { iSplitL ""; [ done | ];
                  iExists (observe (k_s v_s)).
                  iSplitL "".
                  { iPureIntro. rewrite -!itree_eta. eapply H'. }
                  iApply sim_coindF_bupd_mono; [ | iApply "H2"].
                  iIntros (??) "H". iModIntro.
                  iIntros (??). iApply ("Hcont" with "H"); done. } }
              { destruct s, s0; try done.
                destruct s, s0; try done. rewrite /handle_E.
                iDestruct "IHR" as (?) "IHR".
                destruct H0 as (?&?). destruct x; destruct H0.
                iSplitL "".
                { iPureIntro; exists eq_refl; reflexivity. }
                { iIntros (??) "H"; iMod ("IHR" with "H") as "IHR".
                  iLeft. iModIntro.
                  iSplitL ""; [ done | ].
                  iExists (observe (k_s v_s)).
                  iSplitL "".
                  { iPureIntro. rewrite -!itree_eta. eapply H'. }
                  iApply sim_coindF_bupd_mono; [ | iApply "IHR"].
                  iIntros (??) "H". iModIntro.
                  iIntros (??). iApply ("Hcont" with "H"); done. } } }
            { iDestruct "IHR" as (???) "%H0". dependent destruction H0.
              by provide_case: SOURCE_UB. }
            { iDestruct "IHR" as (???) "%H0". dependent destruction H0.
              by provide_case: SOURCE_EXC. }
            { provide_case: BASE. iApply ("Hcont" with "IHR"); try done.
              iPureIntro; eapply eqit_Vis; eauto. }
            { iDestruct "IHR" as (??) "IHR"; inv H0. }
            { iDestruct "IHR" as (??) "IHR"; inv H0. }
            { iDestruct "IHR" as (???) "IHR". inv H0. }
        - iSpecialize ("IHL" $! H).
          iAssert (sim_coindF Ψ (observe t) (observe t2)) with "[IHR]" as "Ht".
          { iApply sim_coindF_bupd_mono; cycle 1.
            { setoid_rewrite sim_coindF_unfold at 3; auto.
            iApply (sim_coindF_TauR_inv (fun x y => Ψ (observe x) (observe y))); cycle 1.
            { cbn. setoid_rewrite sim_coindF_unfold at 2; auto. }
            { iModIntro. iIntros (??) "H %x' %Hx %y' %Hy".
              iApply ("HΨ" with "H"); rewrite -!itree_eta; done. } }
            cbn. by iIntros (??) "H". }
          iApply ("IHL" with "Ht"). } }

    { iDestruct "IHR" as (????????) "IHR".
      inversion H; inversion H0; subst; clear H H0.
      remember (VisF e_s k_s) as ot.

      iInduction Ht as [] "IHL" forall "IHR"; subst; try inv Heqot; cycle 1.
      { rewrite (sim_indF_unfold _ _ _ (TauF t1)).
        rewrite /sim_expr_inner.
        provide_case: STUTTER_R.
        by iApply "IHL". }
      { rewrite sim_indF_unfold; auto. rewrite /sim_expr_inner.
        provide_case: VIS_STEP.

        dependent destruction H1.
        destruct e_t, e_s; cbn; try done.
        { destruct c, c0, p, p0. simp handle_call_events.
          iDestruct "IHR" as "[ Hinner | Hinner]";
          [iLeft | iRight];
            iDestruct "Hinner" as (?) "(SI & H1 & H2)";
            iExists _; iFrame ;
          iIntros (??) "H"; iSpecialize ("H2" with "H");
          iLeft; iMod "H2"; iModIntro.
          { iSplitL ""; [ done | ].
            iExists (observe (k_s (v_s.1, call_returns c0 v_s.2))).
            iSplitL "".
            { iPureIntro. rewrite -!itree_eta. pclearbot. eapply REL. }
            iApply sim_coindF_bupd_mono; [ | iApply "H2"].
            iIntros (??) "H". iModIntro.
            iIntros (??). iApply ("Himpl" with "H"); done. }
          { iSplitL ""; [ done | ].
            iExists (observe (k_s v_s)).
            iSplitL "".
            { iPureIntro. rewrite -!itree_eta. pclearbot. eapply REL. }
            iApply sim_coindF_bupd_mono; [ | iApply "H2"].
            iIntros (??) "H". iModIntro.
            iIntros (??). iApply ("Himpl" with "H"); done. } }
        { destruct s, s0; try done.
          destruct s, s0; try done. rewrite /handle_E.
          iDestruct "IHR" as (?) "IHR".
          destruct H as (?&?). destruct x; destruct H.
          iSplitL "".
          { iPureIntro; exists eq_refl; reflexivity. }
          { iIntros (??) "H"; iMod ("IHR" with "H") as "IHR".
            iLeft. iModIntro.
            iSplitL ""; [ done | ].
            iExists (observe (k_s v_s)).
            iSplitL "".
            { iPureIntro. rewrite -!itree_eta. pclearbot. eapply REL. }
            iApply sim_coindF_bupd_mono; [ | iApply "IHR"].
            iIntros (??) "H". iModIntro.
            iIntros (??). iApply ("Himpl" with "H"); done. } } } }

    { iDestruct "IHR" as (???) "%H"; subst. inversion H; subst.
      rewrite sim_indF_unfold; auto.

      set (term' := itree' (L2 Λ) (state Λ * R2)).
      remember (VisF (inr1 (inl1 e)) k : term') as ot. clear H.

      iInduction Ht as [] "IHL"; subst; try inv Heqot.
      { dependent destruction H1.
        rewrite /sim_expr_inner. subst.
        by provide_case: SOURCE_UB. }
      { rewrite {2}/sim_expr_inner. provide_case: STUTTER_R.
        rewrite sim_indF_unfold; auto.
        by iApply "IHL". } }

    { iDestruct "IHR" as (???) "%H"; subst. inversion H; subst.
      rewrite sim_indF_unfold; auto.

      set (term' := itree' (L2 Λ) (state Λ * R2)).
      remember (VisF (inr1 (inr1 (inl1 e))) k : term') as ot. clear H.

      iInduction Ht as [] "IHL"; subst; try inv Heqot.
      { dependent destruction H1.
        rewrite /sim_expr_inner. subst.
        by provide_case: SOURCE_EXC. }
      { rewrite {2}/sim_expr_inner. provide_case: STUTTER_R.
        rewrite sim_indF_unfold; auto.
        by iApply "IHL". } }

    Unshelve. all : auto.
    exact (Vis e k2).
  Qed.

  Global Instance sim_coindF_eutt_Proper {R1 R2 : Type} Φ:
    Proper (eutt eq ==> eutt eq ==> equiv) Φ ->
    Proper (eutt eq ==> eutt eq ==> equiv)
           (fun e_t e_s => sim_coindF (PROP := PROP) (R1 := R1) (R2 := R2)
                          (fun x y => Φ (go x) (go y)) (observe e_t) (observe e_s)).
  Proof.
    intros Heq e_t e_t' Ht e_s e_s' Hs.
    iIntros. iSplit.
    { iIntros "Hpre".
      iApply sim_coindF_eutt_transR;
        [ iPureIntro ; eauto | iPureIntro ; setoid_rewrite <- itree_eta; apply Hs| ].
        by iApply sim_coindF_eutt_transL;
          [ iPureIntro ; eauto | iPureIntro ; setoid_rewrite <- itree_eta; symmetry; apply Ht| ]. }
    { iIntros "Hpre".
      iApply sim_coindF_eutt_transR;
        [ iPureIntro ; eauto | iPureIntro ; setoid_rewrite <- itree_eta; symmetry; apply Hs| ].
        by iApply sim_coindF_eutt_transL;
          [ iPureIntro ; eauto | iPureIntro ; setoid_rewrite <- itree_eta; apply Ht| ]. }
  Qed.

End weak_bisim.
