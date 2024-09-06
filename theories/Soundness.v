Require Import Metalib.Metatheory.

Require Import Definitions.

Lemma ctxtrans_cong_uniq : forall Gs G,
  ctxtrans Gs G ->
  uniq Gs ->
  uniq G.
Admitted.

Lemma ctxtrans_cong_binds : forall Gs G As A x,
  ctxtrans Gs G ->
  trans As A ->
  binds x As Gs ->
  binds x A G. 
Admitted.

Lemma ctxtrans_append : forall Gs Gs' G G',
  ctxtrans Gs G ->
  ctxtrans Gs' G' ->
  ctxtrans (Gs' ++ Gs) (G' ++ G).
Admitted.

Lemma ctxtrans_total : forall Gs,
  exists G, ctxtrans Gs G.
Admitted.

Lemma ptrans_determ : forall P A1 A2,
  ptrans P A1 ->
  ptrans P A2 ->
  A1 = A2.
Admitted.

Lemma ptrans_total : forall P,
  exists A, ptrans P A.
Admitted.

Lemma trans_determ : forall As A1 A2,
  trans As A1 ->
  trans As A2 ->
  A1 = A2.
Admitted.

Lemma trans_total : forall As,
  exists A, trans As A.
Admitted.

Lemma pelab_inc : forall Gs Es x p P letin,
  pelab Gs x p P letin Es ->
  exists Fs,
  Es = Fs ++ Gs.
Admitted.

Lemma pelab_letbind : forall Gs Gs' G G' x p P letin A,
  pelab Gs x p P letin (Gs' ++ Gs) ->
  ctxtrans Gs G ->
  ctxtrans Gs' G' ->
  letbind (x ~ A ++ G) letin (G' ++ x ~ A ++ G).
Admitted.

Lemma typing_weakening : forall G F E e A,
  typing (G ++ E) e A ->
  typing (G ++ F ++ E) e A.
Admitted.

Lemma typing_napp : forall Gs G P PT a e,
  pmatch Gs P a e ->
  ctxtrans Gs G ->
  ptrans P PT ->
  typing G e PT.
Admitted.

Theorem elab_sound : forall Gs es As G e A,
  elab Gs es As e ->
  ctxtrans Gs G ->
  trans As A ->
  typing G e A.
Proof.
  intros Gs es. revert Gs.
  induction es; intros * HElab HGTrans HTrans;
                inversion HElab; subst.
  - (* Ela_Int *)
    inversion HTrans. subst.
    apply Typ_Int.
    eauto using ctxtrans_cong_uniq.
  - (* Ela_Var *)
    apply Typ_Var.
    { eauto using ctxtrans_cong_binds. }
    { eauto using ctxtrans_cong_uniq. }
  - (* Ela_Abs *)
    inversion HTrans. subst.
    pose proof trans_determ _ _ _ H1 H6.
    pose proof trans_determ _ _ _ H4 H7.
    subst. clear HTrans H6 H7.
    apply Typ_Abs.
    eapply IHes; eauto.
  - (* Ela_App *)
    pose proof trans_total As0 as [A0 HTrans0].
    apply Typ_App with (A := A0).
    + (* typing e1 *)
      eapply IHes1; eauto.
    + (* typing e2 *)
      eapply IHes2; eauto.
  - (* Ela_NAbs *)
    inversion HTrans. subst.
    pose proof trans_determ _ _ _ H7 H8.
    pose proof ptrans_determ _ _ _ H4 H5.
    subst. clear HTrans H8 H5.
    pose proof pelab_inc _ _ _ _ _ _ H2 as [Fs Heq]. 
    pose proof ctxtrans_total Fs as [F HFTrans]. subst.
    apply Typ_Abs. eapply Typ_Let.
    { eapply pelab_letbind; eauto. }
    { apply typing_weakening.
      eapply IHes; eauto.
      apply ctxtrans_append; auto. }
  - (* Ela_NApp *)
    pose proof ptrans_total P as [PT HPTrans].
    apply Typ_App with (A := PT).
    + (* typing e0 *)
      eapply IHes; eauto.
    + (* typing e' *)
      eapply typing_napp; eauto.
Qed.
