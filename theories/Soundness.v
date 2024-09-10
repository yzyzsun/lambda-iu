Require Import List.

Require Import Definitions.

Lemma uniq_ctxtrans : forall Gs,
  uniq Gs ->
  uniq (ctxtrans Gs).
Admitted.

Lemma binds_ctxtrans : forall Gs As x,
  binds x As Gs ->
  binds x (trans As) (ctxtrans Gs). 
Admitted.

Lemma append_ctxtrans : forall Gs Gs',
  ctxtrans (Gs ++ Gs') = ctxtrans Gs ++ ctxtrans Gs'.
Admitted.

Lemma fresh_ctxtrans : forall Gs x,
  fresh x Gs ->
  fresh x (ctxtrans Gs).
Admitted.

Lemma fresh_uniq : forall G F x (A:typ),
  fresh x (F ++ G) ->
  uniq (F ++ x ~ A ++ G).
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

Lemma typing_weaken : forall G F E e A,
  typing (G ++ E) e A ->
  uniq (G ++ F ++ E) ->
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
                inversion Helab; subst.
  - (* Ela_Int *)
    apply Typ_Int.
    eapply uniq_ctxtrans...
  - (* Ela_Var *)
    apply Typ_Var.
    { eapply binds_ctxtrans... }
    { eapply uniq_ctxtrans... }
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
    + eapply pelab_letbind...
    + apply typing_weaken.
      { eapply IHes...
        eapply append_ctxtrans... }
      { apply fresh_uniq.
        rewrite <- append_ctxtrans.
        eapply fresh_ctxtrans... }
  - (* Ela_NApp *)
    apply Typ_App with (A := ptrans P).
    { eapply IHes... }
    { eapply typing_napp... }
Qed.
