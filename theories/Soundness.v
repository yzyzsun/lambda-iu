Require Import List.
Require Import PeanoNat.

Require Import Definitions.

Lemma cons_append : forall {T} (G : list T) t,
  t :: G = one t ++ G.
Proof. auto. Qed.

Lemma fresh_ctxtrans : forall Gs x,
  fresh x Gs ->
  fresh x (ctxtrans Gs).
Proof with auto.
  intros * Hfresh.
  induction Gs...
  simpl. destruct a as [y As].
  unfold fresh in *. simpl in *.
  tauto.
Qed.

Lemma uniq_ctxtrans : forall Gs,
  uniq Gs ->
  uniq (ctxtrans Gs).
Proof with auto.
  induction 1; simpl.
  - apply uniq_nil.
  - apply uniq_cons.
    { apply IHuniq. }
    { apply fresh_ctxtrans... }
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

Lemma append_dom : forall {A} (G : list (nat * A)) G',
  dom (G ++ G') = dom G ++ dom G'.
Proof with auto.
  induction G; intros; simpl...
  destruct a as [x As].
  rewrite IHG...
Qed.

Lemma fresh_append : forall {A} (G : list (nat * A)) G' x,
  fresh x G -> fresh x G' ->
  fresh x (G ++ G').
Proof with auto.
  intros * Hfresh Hfresh'.
  unfold fresh in *. 
  intro Hindom.
  rewrite append_dom in Hindom.
  apply in_app_or in Hindom as [Hindom | Hindom]...
Qed.

Lemma fresh_weaken : forall {A} (G : list (nat * A)) F E x,
  fresh x (G ++ F ++ E) ->
  fresh x F.
Proof with auto.
  intros * Hfresh.
  unfold fresh in *.
  intro Hindom. apply Hfresh.
  rewrite append_dom. rewrite append_dom.
  apply in_or_app. right.
  apply in_or_app...
Qed.

Lemma uniq_weaken : forall {A} (G : list (nat * A)) F E,
  uniq (G ++ F ++ E) ->
  uniq F.
Proof with eauto.
  induction G; simpl; intros * Huniq.
  - induction F...
    + apply uniq_nil.
    + destruct a as [x As].
      apply uniq_cons; inversion Huniq; subst...
      rewrite <- app_nil_l in H3.
      eapply fresh_weaken...
  - inversion Huniq. subst...
Qed.

Lemma fresh_uniq : forall G G' x (A:typ),
  fresh x (G ++ G') ->
  uniq (G ++ G') ->
  uniq (G ++ x ~ A ++ G').
Proof with eauto.
  intros * Hfresh Huniq.
  induction G; simpl in *.
  - apply uniq_cons...
  - destruct a as [y B].
    apply uniq_cons.
    + apply IHG...
      { rewrite cons_append in Hfresh.
        rewrite <- app_nil_r in Hfresh.
        rewrite <- app_assoc in Hfresh.
        eapply fresh_weaken... }
      { rewrite cons_append in Huniq.
        rewrite <- app_nil_r in Huniq.
        rewrite <- app_assoc in Huniq.
        eapply uniq_weaken... }
    + apply fresh_append.
      { inversion Huniq. subst.
        rewrite <- app_nil_l in H3.
        eapply fresh_weaken... }
      rewrite cons_append.
      apply fresh_append.
      { rewrite cons_append in Hfresh.
        rewrite <- app_nil_l in Hfresh.
        apply fresh_weaken in Hfresh.
        unfold fresh in *. simpl in *.
        intro Hor. apply Hfresh.
        left. destruct Hor... contradiction. }
      { inversion Huniq. subst.
        rewrite <- app_nil_r in H3.
        rewrite <- app_assoc in H3.
        eapply fresh_weaken... }
Qed.

Lemma pelab_inc : forall Gs Es x p P letin,
  pelab Gs x p P letin Es ->
  exists Fs, Es = Fs ++ Gs.
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
    pose proof pelab_inc _ _ _ _ _ _ H3 as [Fs Heq]. subst.
    apply Typ_Abs. eapply Typ_Let.
    + eapply pelab_letbind...
    + apply typing_weaken.
      { eapply IHes...
        eapply append_ctxtrans... }
      { apply fresh_uniq.
        rewrite <- append_ctxtrans.
        apply fresh_ctxtrans...
        rewrite <- append_ctxtrans.
        apply uniq_ctxtrans... }
  - (* Ela_NApp *)
    apply Typ_App with (A := ptrans P).
    { eapply IHes... }
    { eapply typing_napp... }
Qed.
