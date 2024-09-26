Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import Definitions.

Theorem sub_refl : forall A,
  sub A A.
Proof with auto using sub.
  induction A...
Qed.

Lemma sub_and : forall A B C,
  sub A (t_and B C) ->
  sub A B /\ sub A C.
Proof with auto using sub.
  intros * Hsub.
  dependent induction Hsub...
  - specialize (IHHsub B C) as [HsubB HsubC]...
  - specialize (IHHsub B C) as [HsubB HsubC]...
  - specialize (IHHsub1 B C) as [HsubB1 HsubC1]...
    specialize (IHHsub2 B C) as [HsubB2 HsubC2]...
Qed.

Lemma sub_or : forall A B C,
  sub (t_or A B) C ->
  sub A C /\ sub B C.
Proof with auto using sub.
  intros * Hsub.
  dependent induction Hsub...
  - specialize (IHHsub1 A B) as [HsubA1 HsubB1]...
    specialize (IHHsub2 A B) as [HsubA2 HsubB2]...
  - specialize (IHHsub A B) as [HsubA HsubB]...
  - specialize (IHHsub A B) as [HsubA HsubB]...
Qed.

Theorem sub_trans : forall B A C,
  sub A B -> sub B C -> sub A C.
Proof with eauto using sub.
  induction B.
  - (* t_top *)
    intros * HsubAB HsubBC.
    dependent induction HsubBC...
  - (* t_bot *)
    intros * HsubAB.
    dependent induction HsubAB...
  - (* t_null *)
    intros * HsubAB.
    dependent induction HsubAB...
  - (* t_int *)
    intros * HsubAB.
    dependent induction HsubAB...
  - (* t_arrow *)
    induction A; inversion 1...
    induction C; inversion 1...
  - (* t_rcd *)
    induction A; inversion 1...
    induction C; inversion 1...
  - (* t_and *)
    intros * HsubAB HsubBC.
    apply sub_and in HsubAB as [HsubAB1 HsubAB2].
    dependent induction HsubBC...
  - (* t_or *)
    intros * HsubAB HsubBC.
    apply sub_or in HsubBC as [HsubBC1 HsubBC2].
    dependent induction HsubAB...
Qed.

Lemma binds_ctxtrans : forall Gs As x,
  binds x As Gs ->
  binds x (trans As) (ctxtrans Gs). 
Proof with auto.
  intros * Hbinds.
  induction Gs...
  simpl. destruct a as [x' As'].
  inversion Hbinds; unfold binds; simpl.
  - injection H as Heq. subst...
  - right. apply IHGs...
Qed.

Lemma append_ctxtrans : forall Gs Gs',
  ctxtrans (Gs ++ Gs') = ctxtrans Gs ++ ctxtrans Gs'.
Proof with auto.
  induction Gs; intros; simpl...
  destruct a as [x As].
  rewrite IHGs...
Qed.

Lemma binds_weaken : forall {T} G F E x (A:T),
  binds x A (G ++ E) ->
  binds x A (G ++ F ++ E).
Proof with auto.
  intros * Hbinds.
  induction G; simpl in *.
  - apply in_or_app...
  - unfold binds in Hbinds.
    apply in_inv in Hbinds.
    destruct Hbinds.
    + destruct a as [y B].
      inversion H.
      left...
    + apply IHG in H.
      right...
Qed.

Scheme exp_mutind := Induction for exp Sort Prop
  with letin_mutind := Induction for letin Sort Prop.
Combined Scheme exp_letin_mutind from exp_mutind, letin_mutind.

Lemma typing_letbind_weaken :
(forall e G F E A,
  typing (G ++ E) e A ->
  typing (G ++ F ++ E) e A) /\
(forall letin G' G F E,
  letbind (G ++ E) letin G' ->
  exists D, G' = D ++ G ++ E /\
  letbind (G ++ F ++ E) letin (D ++ G ++ F ++ E)).
Proof with auto.
  apply exp_letin_mutind; intros * H; try dependent induction H;
                                      try solve [eapply Typ_Sub; eauto].
  (* typing_weaken *)
  - apply Typ_Top.
  - apply Typ_Null.
  - apply Typ_Int.
  - apply Typ_Var.
    apply binds_weaken...
  - intros * Htyping.
    dependent induction Htyping.
    + apply Typ_Abs.
      rewrite app_comm_cons.
      apply H...
    + eapply Typ_Sub; eauto.
  - intros * H' * Htyping.
    dependent induction Htyping.
    + apply Typ_App with (A := A)...
    + eapply Typ_Sub; eauto.
  - intros * Htyping.
    dependent induction Htyping.
    + apply Typ_Rcd...
    + eapply Typ_Sub; eauto.
  - intros * Htyping.
    dependent induction Htyping.
    + apply Typ_Prj...
    + eapply Typ_Sub; eauto.
  - intros * H' * Htyping.
    dependent induction Htyping.
    + apply Typ_Merge...
    + eapply Typ_Sub; eauto.
  - intros * H' * H'' * Htyping.
    dependent induction Htyping.
    + apply Typ_Switch; try rewrite app_comm_cons...
    + eapply Typ_Sub; eauto.
  - intros * H' * Htyping.
    dependent induction Htyping.
    + specialize (H _ _ F _ H0) as [D [Heq Hletbind]]. subst.
      apply Typ_Let with (G' := D ++ G ++ F ++ E)...
      rewrite app_assoc. apply H'. rewrite <- app_assoc...
    + eapply Typ_Sub; eauto.
  (* letbind_weaken *)
  - exists nil. split...
    apply LB_Id.
  - intros * H' * Hletbind. inversion Hletbind. subst.
    destruct (H G'0 G F E) as [D1 [Heq1 Hletbind1]]...
    destruct (H' G' (D1 ++ G) F E) as [D2 [Heq2 Hletbind2]].
    subst. rewrite <- app_assoc... subst.
    exists (D2 ++ D1). split.
    do 2 rewrite <- app_assoc...
    apply LB_Comp with (G' := D1 ++ G ++ F ++ E)...
    rewrite <- app_assoc in Hletbind2.
    rewrite <- app_assoc...
  - intros * Hletbind. inversion Hletbind. subst.
    exists (x ~ A). split...
    apply LB_Let.
    apply H...
Qed.

Lemma letbind_weaken : forall letin G' G F E,
  letbind (G ++ E) letin G' ->
  exists D, G' = D ++ G ++ E /\
  letbind (G ++ F ++ E) letin (D ++ G ++ F ++ E).
Proof.
  apply typing_letbind_weaken.
Qed.

Lemma typing_weaken : forall e G F E A,
  typing (G ++ E) e A ->
  typing (G ++ F ++ E) e A.
Proof.
  apply typing_letbind_weaken.
Qed.

Scheme elab_mutind := Induction for elab Sort Prop
  with pelab_mutind := Induction for pelab Sort Prop
  with pmatch_mutind := Induction for pmatch Sort Prop.
Combined Scheme elab_pelab_pmatch_mutind from elab_mutind, pelab_mutind, pmatch_mutind.

Lemma elab_pmatch_sound :
(forall Gs es As e,
  elab Gs es As e ->
  typing (ctxtrans Gs) e (trans As)) /\
(forall Gs x p P letin Es,
  pelab Gs x p P letin Es ->
  forall A,
  sub A (ptrans P) ->
  exists Fs,
  Es = Fs ++ Gs /\
  letbind (x ~ A ++ ctxtrans Gs)
    letin (ctxtrans Fs ++ x ~ A ++ ctxtrans Gs)) /\
(forall Gs P a e,
  pmatch Gs P a e ->
  typing (ctxtrans Gs) e (ptrans P)).
Proof with eauto.
  apply elab_pelab_pmatch_mutind; intros *.
  (* elab *)
  - apply Typ_Int.
  - intro Hbinds.
    apply Typ_Var.
    apply binds_ctxtrans...
  - intro Helab.
    apply Typ_Abs.
  - intros Helab1 Htyping1 Helab2 Htyping2.
    apply Typ_App with (A := trans As)...
  - intros Hpelab IH Helab Htyping.
    destruct (IH (ptrans P)) as [Fs [Heq Hlet]].
    apply sub_refl. subst.
    apply Typ_Abs. eapply Typ_Let...
    apply typing_weaken.
    rewrite append_ctxtrans in Htyping...
  - intros Helab Htyping Hpmatch.
    apply Typ_App...
  (* pelab *)
  - exists nil. split...
    apply LB_Id.
  - intros Hpelab IH * Hsub.
    specialize (IH A) as [Fs [Heq Hletbind]].
    simpl in Hsub. eapply sub_trans...
    apply Sub_AndL. apply sub_refl.
    subst. exists (l ~ As ++ Fs). split...
    apply LB_Comp with (G' := ctxtrans Fs
                  ++ x ~ A ++ ctxtrans Gs)... 
    simpl. apply LB_Let. apply Typ_Prj.
    eapply Typ_Sub with (A := A). apply Typ_Var.
    unfold binds. apply in_or_app. right. left...
    eapply sub_trans... simpl.
    apply Sub_AndR. apply sub_refl.
  - intros Hpelab IH Helab Htyping * Hsub.
    specialize (IH A) as [Fs [Heq Hletbind]].
    simpl in Hsub. eapply sub_trans...
    apply Sub_AndL. apply sub_refl.
    subst. exists (l ~ As ++ Fs). split...
    apply LB_Comp with (G' := ctxtrans Fs
                  ++ x ~ A ++ ctxtrans Gs)... 
    simpl. apply LB_Let.
    apply Typ_Switch. apply Typ_Prj.
    eapply Typ_Sub with (A := A). apply Typ_Var.
    unfold binds. apply in_or_app. right. left...
    eapply sub_trans... simpl.
    apply Sub_AndR. apply sub_refl.
    apply Typ_Var. left...
    rewrite append_ctxtrans in Htyping...
    assert (cons_app : forall {T} (t:T) G,
      t :: G = one t ++ G) by auto.
    do 2 rewrite cons_app...
    rewrite <- app_nil_l with (l := y ~ t_null).
    rewrite <- app_assoc.
    apply typing_weaken.
    rewrite app_assoc.
    apply typing_weaken...
  (* pmatch *)
  - apply Typ_Top.
  - simpl.
    intros Helab Htyping Hpmatch Htyping'.
    eapply Typ_Sub. apply Typ_Merge... apply Typ_Rcd...
    apply Sub_Top.
  - simpl.
    intros Hlookup Helab Htyping Hpmatch Htyping'.
    apply Typ_Merge... apply Typ_Rcd...
  - simpl.
    intros Hlookup Helab Htyping Hpmatch Htyping'.
    apply Typ_Merge... apply Typ_Rcd... eapply Typ_Sub...
    apply Sub_OrL. apply sub_refl.
  - simpl.
    intros Hlookdown Hpmatch Htyping.
    apply Typ_Merge... apply Typ_Rcd... eapply Typ_Sub.
    { apply Typ_Null. }
    { apply Sub_OrR. apply Sub_Null. }
Qed.

Theorem elab_sound : forall Gs es As e,
  elab Gs es As e ->
  typing (ctxtrans Gs) e (trans As).
Proof.
  apply elab_pmatch_sound.
Qed.
