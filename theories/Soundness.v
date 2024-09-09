Require Import List.

Require Import Definitions.

Lemma ctxtrans_cong_uniq : forall Gs G,
  ctxtrans Gs = G ->
  uniq Gs ->
  uniq G.
Admitted.

Lemma ctxtrans_cong_binds : forall Gs G As A x,
  ctxtrans Gs = G ->
  trans As = A ->
  binds x As Gs ->
  binds x A G. 
Admitted.

Lemma ctxtrans_append : forall Gs Gs' G G',
  ctxtrans Gs = G ->
  ctxtrans Gs' = G' ->
  ctxtrans (Gs' ++ Gs) = G' ++ G.
Admitted.

Lemma pelab_inc : forall Gs Es x p P letin,
  pelab Gs x p P letin Es ->
  exists Fs,
  Es = Fs ++ Gs.
Admitted.

Lemma pelab_letbind : forall Gs Gs' G G' x p P letin A,
  pelab Gs x p P letin (Gs' ++ Gs) ->
  ctxtrans Gs = G ->
  ctxtrans Gs' = G' ->
  letbind (x ~ A ++ G) letin (G' ++ x ~ A ++ G).
Admitted.

Lemma typing_weakening : forall G F E e A,
  typing (G ++ E) e A ->
  typing (G ++ F ++ E) e A.
Admitted.

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
                inversion Helab; subst; simpl.
  - (* Ela_Int *)
    apply Typ_Int.
    eapply ctxtrans_cong_uniq...
  - (* Ela_Var *)
    apply Typ_Var.
    { eapply ctxtrans_cong_binds... }
    { eapply ctxtrans_cong_uniq... }
  - (* Ela_Abs *)
    apply Typ_Abs.
    eapply IHes...
  - (* Ela_App *)
    apply Typ_App with (A := trans As0).
    { eapply IHes1... }
    { eapply IHes2... }
  - (* Ela_NAbs *)
    pose proof pelab_inc _ _ _ _ _ _ H2 as [Fs Heq]. subst.
    apply Typ_Abs. eapply Typ_Let.
    { eapply pelab_letbind... }
    { apply typing_weakening.
      eapply IHes...
      eapply ctxtrans_append... }
  - (* Ela_NApp *)
    apply Typ_App with (A := ptrans P).
    { eapply IHes... }
    { eapply typing_napp... }
Qed.
