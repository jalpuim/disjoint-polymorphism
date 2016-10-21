Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.EqualitiesFacts.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import SystemF.
Require Import Language.

Module MInfrastructure
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module MLanguage := MLanguage(VarTyp)(set).
Export MLanguage.

(** ok properties **)

Lemma ok_map : forall Gamma, ok Gamma -> ok (∥ Gamma ∥).
Proof.
  intros.
  induction H.
  simpl; auto.
  unfold conv_context, mapctx in *.
  unfold extend.
  rewrite map_app.
  simpl.
  apply Ok_push.
  assumption.
  simpl.
  change (map (fun p : var * TyEnvSource => (fst p, ptyp2styp_tyenv (snd p))) E) with (mapctx ptyp2styp_tyenv E).
  erewrite <- dom_map_id.
  assumption.
Qed.

Lemma in_persists :
  forall x ty Gamma, List.In (x, ty) Gamma -> List.In (x, ptyp2styp_tyenv ty) (∥ Gamma ∥).
Proof.
  intros.
  induction Gamma.
  simpl in *; assumption.
  simpl in *.
  inversion H.
  subst; simpl in *.
  auto.
  right; apply IHGamma; auto.
Qed.

Hint Resolve ok_map in_persists.

Module MDec := PairDecidableType(VarTypDecidable)(PTypDecidable).

Lemma ok_unique_type : forall {T : Type} (Gamma: context T) x A B,
  ok Gamma ->
  List.In (x, A) Gamma /\ List.In (x, B) Gamma ->
  sumbool (A = B) (not (A = B)) ->
  A = B.
Proof.
  intros.
  
  induction H.
  inversion H0.
  inversion H.

  assert (Ha := VarTyp.eq_dec x v).
  inversion Ha; inversion H1; subst.
  - reflexivity.
  - inversion H0.
    inversion H3; inversion H5.
    + inversion H6; inversion H7; subst; assumption.    
    + rewrite app_nil_l in H7; apply list_impl_m in H7; contradiction.
    + rewrite app_nil_l in H6; apply list_impl_m in H6; contradiction.
    + rewrite app_nil_l in H6; apply list_impl_m in H6; contradiction.
  - reflexivity.
  - inversion H0; clear H0.
    inversion H5; inversion H6.
    inversion H0; inversion H7; subst.
    exfalso; now apply H3.
    inversion H0; exfalso; now apply H3.
    inversion H7; exfalso; now apply H3.
    apply IHok.
    rewrite app_nil_l in *; split; auto.
Qed. 

(** WFEnv properties **)

Lemma wfenv_to_ok : forall Gamma, WFEnv Gamma -> ok Gamma.
Proof.
  intros; induction H; auto.
Qed.

Hint Resolve wfenv_to_ok.

Lemma wfenv_app_l : forall (E F : context TyEnvSource), WFEnv (E ++ F) -> WFEnv E.
Proof.
  intros E; induction E; intros; auto.
  inversion H;
  subst.
  eapply WFPushV; auto.
  now apply IHE with (F := F).
  not_in_L v.
  apply WFPushT; auto.
  now apply IHE with (F := F).
  not_in_L v.
Qed.  
  
Lemma wfenv_app_r : forall (E F : context TyEnvSource), WFEnv (E ++ F) -> WFEnv F.
Proof.
  intros E.
  induction E; intros.
  - rewrite app_nil_l in H.
    auto.
  - inversion H; subst;
    apply (IHE _ H2).    
Qed.

Lemma wfenv_remove : forall (E F G : context TyEnvSource),
                    WFEnv (E ++ G ++ F) -> WFEnv (E ++ F).
Proof.
  intros.
  induction E using env_ind.
  rewrite app_nil_l in *.
  now apply wfenv_app_r in H.
  unfold extend; rewrite <- app_assoc.
  destruct v.
  - inversion H; subst.
    apply WFPushV; auto.
    not_in_L x.
  - inversion H; subst.
    apply WFPushT; auto.
    not_in_L x.
Qed.


Lemma wfenv_extend_comm : forall (E F : context TyEnvSource) x v,
               WFEnv (F ++ E ++ (x, v) :: nil) ->
               WFEnv (F ++ (x, v) :: nil ++ E).
Proof.
  intros E F x v HWFEnv.  
  generalize dependent E.
  
  induction F using env_ind; intros.
  - unfold extend; simpl.
    rewrite app_nil_l in HWFEnv.
    destruct v.
    + apply WFPushV.
      now apply wfenv_app_l in HWFEnv.
      rewrite <- app_nil_l in HWFEnv.
      apply wfenv_remove in HWFEnv.
      simpl in *; now inversion HWFEnv.
      induction E.
      simpl in *; inversion HWFEnv.
      not_in_L x.
      simpl in *.
      destruct a; simpl in *.
      unfold not; intros H; apply MSetProperties.Dec.F.add_iff in H.
      destruct H.
      subst.
      inversion HWFEnv; subst.
      apply IHE; auto.
      not_in_L x.
      exfalso; apply H0.
      now apply MSetProperties.Dec.F.singleton_2.
      inversion HWFEnv; subst.
      apply IHE; auto.
      not_in_L x.
      exfalso; apply H0.
      now apply MSetProperties.Dec.F.singleton_2.
      inversion HWFEnv; subst; apply IHE; auto.
    + apply WFPushT.
      now apply wfenv_app_l in HWFEnv.
      induction E.
      simpl in *; inversion HWFEnv.
      not_in_L x.
      simpl in *.
      destruct a; simpl in *.
      unfold not; intros H; apply MSetProperties.Dec.F.add_iff in H.
      destruct H.
      subst.
      inversion HWFEnv; subst.
      apply IHE; auto.
      not_in_L x.
      exfalso; apply H0.
      now apply MSetProperties.Dec.F.singleton_2.
      inversion HWFEnv; subst.
      apply IHE; auto.
      not_in_L x.
      exfalso; apply H0.
      now apply MSetProperties.Dec.F.singleton_2.
      inversion HWFEnv; subst; apply IHE; auto.
  - destruct v0.
    unfold extend.
    simpl in *.
    inversion HWFEnv; subst.
    apply WFPushV.
    apply IHF; auto.
    not_in_L x0.
    not_in_L x0.
    unfold not; intros; apply H4; now apply MSetProperties.Dec.F.singleton_2.
    simpl in *.
    inversion HWFEnv; subst.
    apply WFPushT.
    apply IHF; auto.
    not_in_L x0.
    unfold not; intros; apply H3; now apply MSetProperties.Dec.F.singleton_2.
Qed.

Lemma wfenv_app_comm : forall (E F : context TyEnvSource), WFEnv (F ++ E) -> WFEnv (E ++ F).
Proof.
  intros.
  generalize dependent H.
  generalize dependent F.
  dependent induction E using (@env_ind).
  - intros.
    rewrite app_nil_r in H.
    now simpl.
  - intros.
    unfold extend in *.
    rewrite <- app_assoc.
    destruct v.
    apply WFPushV.
    apply IHE.
    apply wfenv_remove in H.
    assumption.
    apply wfenv_app_r in H.
    apply wfenv_app_l in H.
    now inversion H.
    not_in_L x.
    apply wfenv_app_r in H.
    now inversion H.
    rewrite app_assoc in H.
    apply IHE in H.
    apply wfenv_app_r in H.
    rewrite <- app_nil_l in H.
    apply wfenv_extend_comm in H.
    simpl in H; now inversion H.
    apply WFPushT.
    apply IHE.
    now apply wfenv_remove in H.    
    not_in_L x.
    unfold not; intros HH.
    apply wfenv_app_r in H.
    now inversion H.
    rewrite app_assoc in H.
    apply IHE in H.
    apply wfenv_app_r in H.
    rewrite <- app_nil_l in H.
    apply wfenv_extend_comm in H.
    simpl in H; now inversion H.
Qed.

Lemma wfenv_extend_comm' : forall (E F : context TyEnvSource) x v,
     WFEnv (F ++ (x, v) :: nil ++ E) ->
     WFEnv (F ++ E ++ (x, v) :: nil).
Proof.
  intros E F.
  generalize dependent E.
  induction F; intros.
  - simpl in *.
    inversion H; subst; apply wfenv_app_comm; now simpl.
  - simpl in *.
    inversion H; subst.
    apply WFPushV; auto.
    unfold not; intros HH.
    apply H4; rewrite dom_union; rewrite union_spec;
    simpl; rewrite add_spec.
    repeat (apply dom_union in HH;
            rewrite union_spec in HH;
            destruct HH as [HH | HH]); auto.
    simpl in HH; apply add_spec in HH.
    inversion HH.
    subst; auto.
    inversion H0.
    apply WFPushT; auto.
    unfold not; intros HH.
    apply H3; rewrite dom_union; rewrite union_spec;
    simpl; rewrite add_spec.
    repeat (apply dom_union in HH;
            rewrite union_spec in HH;
            destruct HH as [HH | HH]); auto.
    simpl in HH; apply add_spec in HH.
    inversion HH.
    subst; auto.
    inversion H0.    
Qed.
    
Lemma wfenv_middle_comm : forall E F G H,
              WFEnv (E ++ F ++ G ++ H) ->
              WFEnv (E ++ G ++ F ++ H).
Proof.
  intros E.
  induction E; intros.
  - simpl in *.
    apply wfenv_app_comm.
    rewrite <- app_assoc.
    induction F.
    + simpl in *; now apply wfenv_app_comm.
    + inversion H0; subst; simpl in *.
      inversion H0; subst.
      apply WFPushV.
      apply IHF; auto.
      not_in_L v.
      not_in_L v.
      simpl in H10; rewrite dom_union in H10;
      apply MSetProperties.Dec.F.union_1 in H10; destruct H10;
      [ auto | contradiction ].
      inversion H0; subst.
      apply WFPushT.
      apply IHF; auto.
      not_in_L v.
      simpl in H8; rewrite dom_union in H8;
      apply MSetProperties.Dec.F.union_1 in H8; destruct H8;
      [ auto | contradiction ].
  - destruct a; destruct t0; simpl in *.
    inversion H0; subst.
    apply WFPushV; auto.
    not_in_L v.
    simpl in H6; rewrite dom_union in H6.
    apply MSetProperties.Dec.F.union_1 in H6; destruct H6.
    contradiction.
    simpl in H6; rewrite dom_union in H6.
    apply MSetProperties.Dec.F.union_1 in H6; destruct H6; contradiction.
    inversion H0; subst.
    apply WFPushT; auto.
    not_in_L v.
    simpl in H5; rewrite dom_union in H5.
    apply MSetProperties.Dec.F.union_1 in H5; destruct H5.
    contradiction.
    simpl in H6; rewrite dom_union in H5.
    apply MSetProperties.Dec.F.union_1 in H5; destruct H5; contradiction.
Qed.


(** Free variable properties **)

(* fv_source distributes over the open_source operator *)

Lemma fv_source_distr :
  forall t1 t2 x n, In x (fv_source (open_rec_source n t2 t1)) ->
               In x (union (fv_source t1) (fv_source t2)).
Proof.
  intros.
  generalize dependent t2.
  generalize dependent n.
  induction t1; intros; simpl in *; rewrite union_spec in *; auto.
  - destruct (Nat.eqb n0 n); auto. 
  - rewrite <- union_spec.
    eapply IHt1.
    apply H.
  - rewrite union_spec.
    inversion H.
    rewrite or_comm at 1.
    rewrite <- or_assoc.
    left; rewrite or_comm; rewrite <- union_spec.
    eapply IHt1_1; apply H0.
    rewrite or_assoc.
    right; rewrite <- union_spec.
    eapply IHt1_2; apply H0.
  - rewrite union_spec.
    inversion H.
    rewrite or_comm at 1.
    rewrite <- or_assoc.
    left; rewrite or_comm; rewrite <- union_spec.
    eapply IHt1_1; apply H0.
    rewrite or_assoc.
    right; rewrite <- union_spec.
    eapply IHt1_2; apply H0.
  - rewrite <- union_spec.
    eapply IHt1; apply H.
  - destruct H.
    rewrite union_spec; auto.
    rewrite <- union_spec.
    repeat rewrite union_spec.
    rewrite or_assoc.
    right.
    rewrite <- union_spec.
    apply (IHt1 _ _ H).
  - rewrite union_spec.
    inversion H.
    assert (Ha : In x (union (fv_source t1) (fv_source t2))).
    eapply IHt1. apply H0.
    rewrite union_spec in Ha.
    inversion Ha. auto. auto. auto.
  - rewrite union_spec.
    inversion H.
    auto.
    assert (Ha : In x (union (fv_source t1) (fv_source t2))).
    eapply IHt1. apply H0.
    rewrite union_spec in Ha.
    inversion Ha. auto. auto.
  - rewrite union_spec.
    inversion H.
    assert (Ha : In x (union (fv_source t1) (fv_source t2))).
    eapply IHt1. apply H0.
    rewrite union_spec in Ha.
    inversion Ha. auto. auto. auto.
Qed.

(* fv_typ_source distributes over the open_typ_source operator *)
Lemma fv_open_rec_typ_source :
  forall t1 t2 x n, In x (fv_ptyp (open_rec_typ_source n t2 t1)) ->
               In x (union (fv_ptyp t1) (fv_ptyp t2)).
Proof.
  intros.
  generalize dependent t2.
  generalize dependent n.
  induction t1; intros; simpl in *; rewrite union_spec in *; auto.
  - rewrite union_spec.
    inversion H as [H1 | H1].
    apply IHt1_1 in H1; rewrite union_spec in H1; inversion H1; auto.
    apply IHt1_2 in H1; rewrite union_spec in H1; inversion H1; auto.
  - rewrite union_spec.
    inversion H as [H1 | H1].
    apply IHt1_1 in H1; rewrite union_spec in H1; inversion H1; auto.
    apply IHt1_2 in H1; rewrite union_spec in H1; inversion H1; auto.
  - destruct (Nat.eqb n0 n); auto. 
  - destruct H; rewrite union_spec in *.
    rewrite or_comm. rewrite <- or_assoc. left.
    rewrite or_comm; rewrite <- union_spec; eapply IHt1_1; apply H.
    rewrite or_assoc; right; rewrite <- union_spec; eapply IHt1_2; apply H.
  - rewrite union_spec.
    inversion H as [H1 | H1]; auto.
    apply IHt1 in H1; rewrite union_spec in H1; inversion H1; auto.
Qed.

(* fv_source distributes over the open_typ_term_source operator *)
Lemma fv_open_rec_typ_term_source :
  forall t1 t2 x n, In x (fv_source (open_rec_typ_term_source n t2 t1)) ->
               In x (union (fv_source t1) (fv_ptyp t2)).
Proof.
  intros.
  generalize dependent t2.
  generalize dependent n.
  induction t1; intros; simpl in *; try (now rewrite union_spec; auto).
  - eapply IHt1; apply H.
  - repeat rewrite union_spec. 
    rewrite union_spec in H.
    destruct H as [H | H].
    apply IHt1_1 in H; rewrite union_spec in H; inversion H; auto.
    apply IHt1_2 in H; rewrite union_spec in H; inversion H; auto.
  - repeat rewrite union_spec. 
    rewrite union_spec in H.
    destruct H as [H | H].
    apply IHt1_1 in H; rewrite union_spec in H; inversion H; auto.
    apply IHt1_2 in H; rewrite union_spec in H; inversion H; auto.
  - apply (IHt1 _ _ H).
  - repeat rewrite union_spec.
    rewrite union_spec in H.
    destruct H.
    auto.
    rewrite or_assoc.
    right.
    rewrite <- union_spec.
    apply (IHt1 _ _ H).
  - rewrite union_spec in H.
    repeat rewrite union_spec.
    inversion H.
    apply IHt1 in H0; rewrite union_spec in H0; inversion H0; auto.
    apply fv_open_rec_typ_source in H0.
    rewrite union_spec in H0.
    inversion H0; auto.
  - rewrite union_spec in H.
    repeat rewrite union_spec.
    inversion H; auto.
    apply IHt1 in H0; rewrite union_spec in H0; inversion H0; auto.
  - rewrite union_spec in H.
    repeat rewrite union_spec.
    inversion H; auto.
    apply IHt1 in H0; rewrite union_spec in H0; inversion H0; auto.
Qed.

(** Opening lemmas **)

(** "Ugly" lemma for open_rec_typ_source and open_rec_source **)
Lemma open_rec_typ_source_core :
  forall t j v i u,
    i <> j ->
    open_rec_typ_source j v t = open_rec_typ_source i u (open_rec_typ_source j v t) ->
    t = open_rec_typ_source i u t.
Proof.
  intro t; induction t; intros; simpl; auto.
  - simpl in H0; inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - simpl in H0; inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - simpl in *.
    case_eq (Nat.eqb j n); intros.
    case_eq (Nat.eqb i n); intros.
    exfalso. apply H. apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in H2. rewrite H1, H2.
    reflexivity.
    reflexivity.
    rewrite H1 in H0.
    apply H0.
  - simpl in H0; inversion H0.
    apply IHt1 in H2.
    apply IHt2 in H3.
    rewrite H2 at 1; rewrite H3 at 1.
    reflexivity.
    apply not_eq_S.
    apply H.
    apply H.
  - simpl in H0; inversion H0; erewrite <- IHt; eauto.
Qed.

Lemma open_rec_term_source_core :forall t j v i u, i <> j ->
  open_rec_source j v t = open_rec_source i u (open_rec_source j v t) ->
  t = open_rec_source i u t.
Proof.
  intro t; induction t; intros; simpl.
  - reflexivity.
  - reflexivity.
  - simpl in *.
    case_eq (Nat.eqb i n); intros.
    case_eq (Nat.eqb j n); intros.
    exfalso. apply H. apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in H2. rewrite H1, H2.
    reflexivity.
    rewrite H2 in H0.
    unfold open_rec_source in H0.
    rewrite H1 in H0.
    assumption.
    reflexivity.
  - reflexivity.
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply not_eq_S.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply H.
    apply H2. 
  - inversion H0; erewrite <- IHt; [ reflexivity | apply H | apply H2 ].
  - inversion H0; erewrite <- IHt; [ reflexivity | apply H | apply H2 ].
  - inversion H0; erewrite <- IHt; eauto.
  - inversion H0; erewrite <- IHt; eauto.
Qed.

Lemma open_rec_type_term_source_core :
  forall t j v i u,
    open_rec_typ_term_source j v t = open_rec_source i u (open_rec_typ_term_source j v t) ->
    t = open_rec_source i u t.
Proof.
  intro t; induction t; intros; simpl; auto.
  - simpl in *.
    inversion H.
    erewrite <- IHt.
    reflexivity.
    apply H1.
  - inversion H.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H2.
    apply H1.
  - inversion H.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H2. 
    apply H1.
  - inversion H.
    erewrite <- IHt.
    reflexivity.
    apply H1.
  - inversion H.
    erewrite <- IHt.
    reflexivity.
    apply H1.
  - inversion H; erewrite <- IHt; [ reflexivity | apply H1 ].
  - inversion H; erewrite <- IHt; [ reflexivity | apply H1 ].
  - inversion H; erewrite <- IHt; [ reflexivity | apply H1 ].  
Qed.

(** Opening a locally-closed term/type leaves it unchanged **)

Lemma open_rec_type_source : forall t u,
  PType  t -> forall k, t =  open_rec_typ_source k u t.
Proof.
  intros t u H.
  induction H; intros; simpl; auto.
  - rewrite <- IHPType1; rewrite <- IHPType2; reflexivity.
  - rewrite <- IHPType1; rewrite <- IHPType2; reflexivity.
  - pick_fresh x.
    assert (Ha1 : not (In x L)) by not_in_L x.
    apply H1 with (k := S k) in Ha1.
    apply open_rec_typ_source_core in Ha1.
    rewrite <- Ha1.
    rewrite <- IHPType; reflexivity.
    auto.
  - rewrite <- IHPType; reflexivity.
Qed.

Lemma open_rec_source_term : forall t u,
  PTerm t -> forall k, t =  open_rec_source k u t.
Proof.
  induction 1; intros; simpl; auto.
  - pick_fresh x.
    rewrite <- open_rec_term_source_core with (j := 0) (v := PFVar x).
    reflexivity.
    auto.
    simpl.
    unfold open_source in *.
    rewrite <- H0.
    reflexivity.
    not_in_L x.
  - rewrite <- IHPTerm1.
    rewrite <- IHPTerm2.
    reflexivity.
  - rewrite <- IHPTerm1.
    rewrite <- IHPTerm2.
    reflexivity.
  - rewrite <- IHPTerm.
    reflexivity.
  - pick_fresh x.
    assert (Ha : not (In x L)) by not_in_L x.
    apply H0 with (k := k) in Ha.
    simpl; apply f_equal.
    now apply open_rec_type_term_source_core in Ha.
  - simpl; rewrite <- IHPTerm; reflexivity.
  - simpl; rewrite <- IHPTerm; reflexivity.
  - simpl; rewrite <- IHPTerm; reflexivity.
Qed.

(* Substitution (at type-level) lemmas *)

Lemma subst_typ_source_fresh : forall x t u, 
  not (In x (fv_ptyp t)) -> subst_typ_source x u t = t.
Proof.
  intros; induction t0; simpl in *; auto.
  - rewrite IHt0_1; [ rewrite IHt0_2 | not_in_L x ]; [ reflexivity | not_in_L x ].
  - rewrite IHt0_1; [ rewrite IHt0_2 | not_in_L x ]; [ reflexivity | not_in_L x ].
  - case_eq (eqb v x); intros.
    exfalso; apply H; simpl; apply MSetProperties.Dec.F.singleton_2;
    now apply eqb_eq in H0.
    auto.
  - rewrite IHt0_1. rewrite IHt0_2. auto.
    not_in_L x.
    not_in_L x.
  - rewrite IHt0; auto; not_in_L x.
Qed.

Lemma subst_typ_source_open_source : forall x u t1 t2, PType u -> 
  subst_typ_source x u (open_typ_source t1 t2) = open_typ_source (subst_typ_source x u t1) (subst_typ_source x u t2).
Proof.
  intros. unfold open_typ_source. generalize 0.
  induction t1; intros; simpl; auto; try (apply f_equal; auto).
  - rewrite IHt1_1; rewrite IHt1_2; auto.
  - rewrite IHt1_1; rewrite IHt1_2; auto.
  - case_eq (Nat.eqb n0 n); intros; auto.
  - case_eq (eqb v x); intros; [ rewrite <- open_rec_type_source | ]; auto.
  - rewrite IHt1_1; rewrite IHt1_2; reflexivity.
Qed.

Lemma subst_typ_source_open_source_var :
  forall x y u t, y <> x -> PType u ->
             open_typ_source (subst_typ_source x u t) (PFVarT y) =
             subst_typ_source x u (open_typ_source t (PFVarT y)).
Proof.
  intros Neq Wu. intros. rewrite subst_typ_source_open_source; auto. simpl.
  case_eq (VarTyp.eqb Wu Neq); intros; auto.
  exfalso; apply H.
  now apply eqb_eq in H1.
Qed.

Lemma subst_typ_source_intro : forall x t u, 
  not (In x (fv_ptyp t)) -> PType u ->
  open_typ_source t u = subst_typ_source x u (open_typ_source t (PFVarT x)).
Proof.
  intros Fr Wu.
  intros.
  rewrite subst_typ_source_open_source.
  rewrite subst_typ_source_fresh.
  simpl.
  case_eq (eqb Fr Fr); intros; auto.
  apply EqFacts.eqb_neq in H1; exfalso; apply H1; reflexivity.
  auto. auto.
Qed.

  
(* Locally-closed types are stable by substitution *)
Lemma subst_source_lc : forall t z u,
  PType u -> PType t -> PType (subst_typ_source z u t).
Proof.
  induction 2; simpl; auto.
  - case_eq (VarTyp.eqb x z); intros; auto.
  - apply_fresh PType_ForAll as x; auto.
    rewrite subst_typ_source_open_source_var.
    apply H2.
    not_in_L x.
    not_in_L x.
    apply H.
Qed.

(* Properties of free variables and substitution *)

Lemma fv_subst_source :
  forall t z x u, In x (fv_ptyp (subst_typ_source z u t)) ->
             In x (union (fv_ptyp u) (fv_ptyp t)).
Proof.
  intro t; induction t; intros; simpl in *; try now inversion H.
  - repeat rewrite union_spec; rewrite union_spec in H; destruct H;
    [ apply IHt1 in H | apply IHt2 in H ]; rewrite union_spec in H; destruct H;
    auto.
  - repeat rewrite union_spec; rewrite union_spec in H; destruct H;
    [ apply IHt1 in H | apply IHt2 in H ]; rewrite union_spec in H; destruct H;
    auto.
  - rewrite union_spec; destruct (eqb v z); auto.
  - repeat rewrite union_spec; rewrite union_spec in H; destruct H;
    [ apply IHt1 in H | apply IHt2 in H ]; rewrite union_spec in H; destruct H;
    auto.
  - repeat rewrite union_spec; rewrite union_spec in H; destruct H; auto;
    apply IHt in H; rewrite union_spec in H; destruct H; auto.
Qed.  

(* Properties concerning environments *)

Lemma dom_subst_id : forall Gamma z u, dom (subst_env Gamma z u) = dom Gamma.
Proof.
  intros Gamma z u.
  induction Gamma using env_ind; auto.
  destruct v; simpl; now rewrite IHGamma.
Qed.

Hint Rewrite dom_subst_id.

Lemma codom_union : forall (E G : context TyEnvSource) (x : elt),
                      In x (codom (E ++ G)) <-> In x (union (codom E) (codom G)).
Proof.
  intros E G x; split.
  - intro HIn; induction E; simpl in *; auto.
    rewrite union_spec in HIn; destruct HIn.
    repeat rewrite union_spec; auto.
    repeat rewrite union_spec in *.
    rewrite or_assoc.
    right; now apply IHE.
  - intro HIn; induction E; simpl in *; auto.
    repeat rewrite union_spec in *.
    rewrite or_assoc in HIn.
    destruct HIn; auto.
Qed.

Hint Rewrite codom_union.

Lemma in_persists_subst_env :
  forall x A Gamma z u, 
    List.In (x, TyDis A) Gamma ->
    List.In (x, TyDis (subst_typ_source z u A)) (subst_env Gamma z u).
Proof.
  intros x A Gamma z u HIn.
  induction Gamma.
  - inversion HIn.
  - destruct a; destruct t0.
    inversion HIn.
    inversion H; subst.
    simpl; now left.
    simpl; right; now apply IHGamma.
    inversion HIn.
    inversion H.
    simpl; right; now apply IHGamma.
Qed.

Lemma subst_env_codom_fresh :
  forall Gamma z u,
    not (In z (codom Gamma)) ->
    subst_env Gamma z u = Gamma. 
Proof.
  intros Gamma z u HNotIn.
  induction Gamma; auto.
  - destruct a; destruct t0; simpl in *.
    rewrite subst_typ_source_fresh.
    apply f_equal.
    apply IHGamma.
    not_in_L z.
    not_in_L z.
    apply f_equal.
    apply IHGamma.
    not_in_L z.
Qed.

Lemma MapsTo_extend :
  forall Gamma x z d a,
    not (x = z) ->
    MapsTo Gamma z d ->
    MapsTo (extend x a Gamma) z d.
Proof.
  intros Gamma x z d a HNeq HMapsTo.
  unfold MapsTo; simpl; apply EqFacts.eqb_neq in HNeq; rewrite HNeq; auto.
Qed.

Lemma MapsTo_In_eq :
  forall Gamma z d A,
    WFEnv Gamma ->
    MapsTo Gamma z d ->
    List.In (z, TyDis A) Gamma ->
    A = d.
Proof.
  intros Gamma z d A HWFEnv HMapsTo HIn.
  induction Gamma.
  - inversion HMapsTo.
  - destruct a; destruct t0.
    inversion HWFEnv; subst.
    assert (Ha : sumbool (v = z) (not (v = z))) by apply VarTyp.eq_dec.
    destruct Ha.
    + subst.
      inversion HIn. inversion H; subst.
      inversion HMapsTo.
      assert (Heq : z = z) by auto.
      apply eqb_eq in Heq.
      rewrite Heq in H1; now inversion H1.
      apply list_impl_m in H.
      contradiction.
    + rewrite <- EqFacts.eqb_neq in n.
      unfold MapsTo in HMapsTo; simpl in HMapsTo.
      rewrite n in HMapsTo.
      apply IHGamma; auto.
      inversion HIn; auto.
      inversion H; subst; auto.
      rewrite EqFacts.eqb_neq in n; exfalso; now apply n.
    + inversion HWFEnv; subst.
      assert (Ha : sumbool (v = z) (not (v = z))) by apply VarTyp.eq_dec.
      destruct Ha.
      subst.
      inversion HIn.
      inversion H.
      apply list_impl_m in H; contradiction.
      rewrite <- EqFacts.eqb_neq in n.
      unfold MapsTo in HMapsTo; simpl in HMapsTo.
      rewrite n in HMapsTo.
      apply IHGamma; auto.
      inversion HIn; auto. now inversion H.
Qed.      

Lemma not_in_wfenv :
  forall Gamma z d,
    WFEnv Gamma ->
    List.In (z, TyDis d) Gamma ->
    ~ In z (fv_ptyp d).
Proof.
  intros Gamma z d HWFEnv HIn.
  induction HWFEnv.
  - simpl in HIn; exfalso; apply HIn.
  - destruct HIn; auto.
    inversion H1; now subst.
  - destruct HIn; auto.
    inversion H0.
Qed.

Lemma fv_ptyp_open_rec_typ_source :
  forall t1 t2 x n,
    In x (fv_ptyp t1) ->
    In x (fv_ptyp (open_rec_typ_source n t2 t1)).
Proof.
  intro t1; induction t1; intros; try (simpl in *; rewrite union_spec in *); auto;
  try now (destruct H; auto). inversion H.
Qed.

(** More properties on open **)

Lemma open_comm_open_typ_term :
  forall y x c n m, open_rec_typ_term n (STFVarT y) (open_rec m (STFVar elt x) c) =
               open_rec m (STFVar elt x) (open_rec_typ_term n (STFVarT y) c).
Proof.
  intros y x c.
  induction c; intros; simpl; auto.
  - case_eq (m =? n); intros; reflexivity.
  - apply f_equal; apply IHc.
  - rewrite IHc1; rewrite IHc2; reflexivity.
  - rewrite IHc1; rewrite IHc2; reflexivity.
  - rewrite IHc; reflexivity.
  - rewrite IHc; reflexivity.
  - apply f_equal; apply IHc.
  - rewrite IHc; reflexivity.
Qed.    

Lemma open_rec_typ_eq_source :
  forall ty n A, | open_rec_typ_source n A ty | = open_rec_typ n (| A |) (| ty |).
Proof.
  intro t.
  induction t; intros; simpl; auto.
  - rewrite IHt1; rewrite IHt2; auto.
  - rewrite IHt1; rewrite IHt2; auto.
  - case_eq (n0 =? n); intros; simpl; auto.
  - rewrite IHt2; auto.  
Qed.

Lemma type_source_gives_type_target :
  forall t, PType t -> STType (| t |).
Proof.
  intros t HPType.
  induction HPType; simpl; auto.
  - apply_fresh STType_ForAll as x.
    assert (Ha : not (In x L)) by not_in_L x.
    apply H0 in Ha.
    unfold open_typ_source in Ha; now rewrite open_rec_typ_eq_source in Ha.
Qed.

End MInfrastructure.