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
  - pose proof IHHsub B C as [HsubB HsubC]...
  - pose proof IHHsub B C as [HsubB HsubC]...
  - pose proof IHHsub1 B C as [HsubB1 HsubC1]...
    pose proof IHHsub2 B C as [HsubB2 HsubC2]...
Qed.

Lemma sub_or : forall A B C,
  sub (t_or A B) C ->
  sub A C /\ sub B C.
Proof with auto using sub.
  intros * Hsub.
  dependent induction Hsub...
  - pose proof IHHsub1 A B as [HsubA1 HsubB1]...
    pose proof IHHsub2 A B as [HsubA2 HsubB2]...
  - pose proof IHHsub A B as [HsubA HsubB]...
  - pose proof IHHsub A B as [HsubA HsubB]...
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

Lemma pelab_letbind : forall Gs Es x p P letin A,
  pelab Gs x p P letin Es ->
  sub A (ptrans P) ->
  exists Fs,
  Es = Fs ++ Gs /\
  letbind (x ~ A ++ ctxtrans Gs)
    letin (ctxtrans Fs ++ x ~ A ++ ctxtrans Gs).
Proof with eauto.
  intros * Hpelab Hsub.
  induction Hpelab.
  - (* PEla-Empty *)
    exists nil. split...
    apply LB_Id.
  - (* PEla-Required *)
    destruct IHHpelab as [Fs [Heq Hletbind]].
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
  - (* PEla-Optional *)
    destruct IHHpelab as [Fs [Heq Hletbind]].
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
    apply Typ_Var. left... admit.
Admitted.

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

Lemma letbind_weaken : forall letin G' G F E,
  letbind (G ++ E) letin G' ->
  exists D, G' = D ++ G ++ E /\
  letbind (G ++ F ++ E) letin (D ++ G ++ F ++ E).
Proof with auto.
  induction letin; intros * Hletbind; inversion Hletbind; subst.
  - exists nil. split...
    apply LB_Id.
  - destruct (IHletin1 G'0 G F E) as [D1 [Heq1 Hletbind1]]...
    destruct (IHletin2 G' (D1 ++ G) F E) as [D2 [Heq2 Hletbind2]].
    subst. rewrite <- app_assoc... subst.
    exists (D2 ++ D1). split.
    do 2 rewrite <- app_assoc...
    apply LB_Comp with (G' := D1 ++ G ++ F ++ E)...
    rewrite <- app_assoc in Hletbind2.
    rewrite <- app_assoc...
  - exists (x ~ A). split...
    apply LB_Let.
Admitted.

Lemma typing_weaken : forall G F E e A,
  typing (G ++ E) e A ->
  typing (G ++ F ++ E) e A.
Proof with eauto.
  intros * Htyping. revert F.
  dependent induction Htyping; intros...
  - apply Typ_Top.
  - apply Typ_Int.
  - apply Typ_Var.
    apply binds_weaken...
  - apply Typ_Abs.
    rewrite app_comm_cons.
    apply IHHtyping...
  - eapply Typ_App...
  - apply Typ_Rcd...
  - apply Typ_Prj...
  - apply Typ_Merge...
  - apply Typ_Switch; try rewrite app_comm_cons...
  - pose proof letbind_weaken _ _ _ F _ H as [D [Heq Hletbind]]. subst.
    apply Typ_Let with (G' := D ++ G ++ F ++ E)...
    rewrite app_assoc. apply IHHtyping. rewrite app_assoc...
  - eapply Typ_Sub... 
Qed.

Lemma typing_napp : forall Gs G P PT a e,
  pmatch Gs P a e ->
  ctxtrans Gs = G ->
  ptrans P = PT ->
  typing G e PT.
Admitted.

Theorem elab_sound : forall Gs es As G e A,
  elab Gs es As e ->
  ctxtrans Gs = G ->
  trans As = A ->
  typing G e A.
Proof with eauto.
  intros Gs es. revert Gs.
  induction es; intros * Helab HGtrans Htrans;
                inversion Helab; subst.
  - (* Ela_Int *)
    apply Typ_Int.
  - (* Ela_Var *)
    apply Typ_Var.
    eapply binds_ctxtrans...
  - (* Ela_Abs *)
    apply Typ_Abs.
    eapply IHes...
  - (* Ela_App *)
    apply Typ_App with (A := trans As0).
    { eapply IHes1... }
    { eapply IHes2... }
  - (* Ela_NAbs *)
    pose proof pelab_letbind _ _ _ _ _ _
               (ptrans P) H1 as [Fs [Heq Hlet]].
    apply sub_refl. subst.
    apply Typ_Abs. eapply Typ_Let.
    + eapply Hlet...
    + apply typing_weaken.
      { eapply IHes...
        apply append_ctxtrans... }
  - (* Ela_NApp *)
    apply Typ_App with (A := ptrans P).
    { eapply IHes... }
    { eapply typing_napp... }
Qed.
