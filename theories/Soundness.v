Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import Definitions.

Lemma sub_refl : forall A,
  sub A A.
Proof with auto.
  induction A.
  - apply Sub_Top.
  - apply Sub_Bot.
  - apply Sub_Null.
  - apply Sub_Int.
  - apply Sub_Arrow...
  - apply Sub_Rcd...
  - apply Sub_And. apply Sub_AndL... apply Sub_AndR...
  - apply Sub_Or. apply Sub_OrL... apply Sub_OrR...
Qed.

Lemma sub_trans : forall A B C,
  sub A B -> sub B C -> sub A C.
Proof with eauto.
  intros * Hsub. revert C.
  induction Hsub; intros * Hsub'...
  - dependent induction Hsub'.
    + apply Sub_Top.
    + apply Sub_And...
    + apply Sub_OrL...
    + apply Sub_OrR...
  - apply Sub_Bot.
  - inversion Hsub'.
    + apply Sub_Top.
    + apply Sub_Arrow...
Admitted.

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

Lemma pelab_letbind : forall Gs Es x p P letin A,
  fresh x Es -> uniq Es ->
  pelab Gs x p P letin Es ->
  sub A (ptrans P) ->
  exists Fs,
  Es = Fs ++ Gs /\
  letbind (x ~ A ++ ctxtrans Gs)
    letin (ctxtrans Fs ++ x ~ A ++ ctxtrans Gs).
Proof with eauto.
  intros * Hfresh Huniq Hpelab Hsub.
  induction Hpelab.
  - (* PEla-Empty *)
    exists nil. split...
    apply LB_Id.
  - (* PEla-Required *)
    destruct IHHpelab as [Fs [Heq Hletbind]].
    { rewrite cons_append in Hfresh.
      rewrite <- app_nil_r in Hfresh.
      rewrite <- app_assoc in Hfresh.
      eapply fresh_weaken... }
    { rewrite cons_append in Huniq.
      rewrite <- app_nil_r in Huniq.
      rewrite <- app_assoc in Huniq.
      eapply uniq_weaken... }
    { simpl in Hsub. eapply sub_trans...
      apply Sub_AndL. apply sub_refl. }
    subst. exists (l ~ As ++ Fs). split...
    apply LB_Comp with (G' := ctxtrans Fs
                  ++ x ~ A ++ ctxtrans Gs)... 
    simpl. apply LB_Let. apply Typ_Prj.
    eapply Typ_Sub with (A := A). apply Typ_Var.
    unfold binds. apply in_or_app. right. left... 
    apply fresh_uniq.
    { rewrite <- append_ctxtrans.
      apply fresh_ctxtrans.
      rewrite cons_append in Hfresh.
      rewrite <- app_nil_r in Hfresh.
      rewrite <- app_assoc in Hfresh.
      eapply fresh_weaken... }
    { rewrite <- append_ctxtrans.
      apply uniq_ctxtrans.
      rewrite cons_append in Huniq.
      rewrite <- app_nil_r in Huniq.
      rewrite <- app_assoc in Huniq.
      eapply uniq_weaken... }
    eapply sub_trans... simpl.
    apply Sub_AndR. apply sub_refl.
  - (* PEla-Optional *)
    destruct IHHpelab as [Fs [Heq Hletbind]].
    { rewrite cons_append in Hfresh.
      rewrite <- app_nil_r in Hfresh.
      rewrite <- app_assoc in Hfresh.
      eapply fresh_weaken... }
    { rewrite cons_append in Huniq.
      rewrite <- app_nil_r in Huniq.
      rewrite <- app_assoc in Huniq.
      eapply uniq_weaken... }
    { simpl in Hsub. eapply sub_trans...
      apply Sub_AndL. apply sub_refl. }
    subst. exists (l ~ As ++ Fs). split...
    apply LB_Comp with (G' := ctxtrans Fs
                  ++ x ~ A ++ ctxtrans Gs)... 
    simpl. apply LB_Let.
    apply Typ_Switch. apply Typ_Prj.
    eapply Typ_Sub with (A := A). apply Typ_Var.
    unfold binds. apply in_or_app. right. left... 
    apply fresh_uniq.
    { rewrite <- append_ctxtrans.
      apply fresh_ctxtrans.
      rewrite cons_append in Hfresh.
      rewrite <- app_nil_r in Hfresh.
      rewrite <- app_assoc in Hfresh.
      eapply fresh_weaken... }
    { rewrite <- append_ctxtrans.
      apply uniq_ctxtrans.
      rewrite cons_append in Huniq.
      rewrite <- app_nil_r in Huniq.
      rewrite <- app_assoc in Huniq.
      eapply uniq_weaken... }
    eapply sub_trans... simpl.
    apply Sub_AndR. apply sub_refl.
    apply Typ_Var. left... admit.
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
    pose proof pelab_letbind _ _ _ _ _ _
               (ptrans P) H1 H2 H3 as [Fs [Heq Hlet]].
    apply sub_refl. subst.
    apply Typ_Abs. eapply Typ_Let.
    + eapply Hlet...
    + apply typing_weaken.
      { eapply IHes...
        apply append_ctxtrans... }
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
