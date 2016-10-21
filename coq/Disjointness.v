Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import SystemF.
Require Import Coq.Program.Equality.
Require Export Subtyping.

Module MDisjointness
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).
  
Module MSubtyping := MSubtyping(VarTyp)(set).
Export MSubtyping.

(* Disjointness: Implementation *)

Definition hd (p : PTyp) : nat :=
  match p with
  | PInt       => 0
  | Fun t1 t2  => 1
  | ForAll d t => 2
  | Rec l t    => 3
  | Top        => 4
  | PBVarT n   => 5
  | PFVarT v   => 6 
  | And t1 t2  => 7
  end.

Definition OrthoAx (t1 t2 : PTyp) : Prop :=
  (hd t1 < 4 /\ hd t2 < 4 /\ not (hd t1 = hd t2)).

Inductive Ortho : context TyEnvSource -> PTyp -> PTyp -> Prop :=
  | OAnd1 : forall Gamma t1 t2 t3, Ortho Gamma t1 t3 -> Ortho Gamma t2 t3 -> Ortho Gamma (And t1 t2) t3
  | OAnd2 : forall Gamma t1 t2 t3, Ortho Gamma t1 t2 -> Ortho Gamma t1 t3 -> Ortho Gamma t1 (And t2 t3)
  | OFun  : forall Gamma t1 t2 t3 t4, Ortho Gamma t2 t4 -> Ortho Gamma (Fun t1 t2) (Fun t3 t4)
  | OForAll : forall L Gamma d1 d2 t1 t2,
                (forall x, not (In x L) -> Ortho (extend x (TyDis (And d1 d2)) Gamma)
                                           (open_typ_source t1 (PFVarT x))
                                           (open_typ_source t2 (PFVarT x))) ->
                PType (And d1 d2) ->
                Ortho Gamma (ForAll d1 t1) (ForAll d2 t2)
  | OVar : forall Gamma x ty A, List.In (x,TyDis A) Gamma ->
                       usub A ty ->
                       PType ty ->
                       Ortho Gamma (PFVarT x) ty
  | OVarSym : forall Gamma x ty A, List.In (x,TyDis A) Gamma ->
                          usub A ty ->
                          PType ty ->
                          Ortho Gamma ty (PFVarT x)
  | OTop1 : forall Gamma t, Ortho Gamma Top t
  | OTop2 : forall Gamma t, Ortho Gamma t Top
  | ORecNeq : forall Gamma l1 l2 t1 t2, l1 <> l2 -> Ortho Gamma (Rec l1 t1) (Rec l2 t2)
  | ORecEq : forall Gamma l t1 t2, Ortho Gamma t1 t2 -> Ortho Gamma (Rec l t1) (Rec l t2)
  | OAx : forall Gamma t1 t2, OrthoAx t1 t2 -> Ortho Gamma t1 t2.

Hint Constructors Ortho.

(* Disjointness: Specification *)

Definition OrthoS (A B : PTyp) := not (exists C, Sub A C /\ Sub B C).

Ltac orthoax_inv H :=
  let H' := fresh in
  let m := fresh in
  let H1 := fresh in
  let H2 := fresh in
  inversion H as [H' | m H1 H2 ]; orthoax_inv H1.

(* Solving goals by inversion, with the form OrthoAx t1 t2,
   where t1 is not part of OrthoAx *)
Ltac orthoax_inv_l :=
  match goal with
    | H: OrthoAx _ _ |- _ => let H1 := fresh in
                           destruct H as [H1 _]; orthoax_inv H1
  end.

(* Solving goals by inversion, with the form OrthoAx t1 t2,
   where t2 is not part of OrthoAx *)
Ltac orthoax_inv_r := 
  match goal with
    | H: OrthoAx _ _ |- _ => let H1 := fresh in
                           destruct H as [_ [H1 _]]; orthoax_inv H1
  end.

(** Ortho environment properties **)

Lemma ortho_weaken :
  forall G E F t1 t2, Ortho (E ++ G) t1 t2 ->
                 Ortho (E ++ F ++ G) t1 t2.
Proof.
  intros.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent E.
  dependent induction H; intros; eauto; subst.
  - apply_fresh OForAll as x.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    apply H0.
    not_in_L x.
    rewrite <- app_comm_cons.
    unfold extend; simpl; reflexivity.
    auto.
  - apply OVar with (A := A); auto.
    apply in_app_or in H; inversion H; apply in_or_app; auto.
    right; apply in_or_app; auto.
  - apply OVarSym with (A := A); auto.
    apply in_app_or in H; inversion H; apply in_or_app; auto.
    right; apply in_or_app; auto.
Qed.

Lemma ortho_strengthen : forall z U E F ty1 ty2,
  not (In z (union (fv_ptyp ty1) (fv_ptyp ty2))) ->
  Ortho (E ++ ((z,U) :: nil) ++ F) ty1 ty2 ->
  Ortho (E ++ F) ty1 ty2.
Proof.
  intros.
  remember (E ++ ((z,U) :: nil) ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; auto.
  - apply OAnd1; [ apply IHOrtho1 | apply IHOrtho2 ];
    simpl in H; not_in_L z; apply Heql.
  - apply OAnd2; [ apply IHOrtho1 | apply IHOrtho2 ];
    simpl in H; not_in_L z; apply Heql.
  - apply OFun;
    apply IHOrtho; simpl in H; not_in_L z; auto.
  - apply_fresh OForAll as x.
    subst; unfold extend; simpl.
    rewrite app_comm_cons.
    eapply H1.
    not_in_L x.
    unfold not; intro HH.
    apply MSetProperties.Dec.F.union_1 in HH.
    destruct HH as [HH | HH]; apply fv_open_rec_typ_source in HH.
    apply MSetProperties.Dec.F.union_1 in HH; simpl in HH; simpl in H.
    destruct HH as [HH | HH].
    apply H.
    apply MSetProperties.Dec.F.union_2.
    apply MSetProperties.Dec.F.union_3.
    assumption.
    not_in_L x.
    apply H16.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in HH.
    now symmetry.
    apply MSetProperties.Dec.F.union_1 in HH; simpl in HH; simpl in H.
    destruct HH as [HH | HH].
    apply H.
    apply MSetProperties.Dec.F.union_3.
    apply MSetProperties.Dec.F.union_3.
    assumption.
    not_in_L x.
    apply H16.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in HH.
    now symmetry.
    unfold extend; now simpl.
    auto.
  - subst.
    apply OVar with (A := A); auto.
    apply in_or_app.
    apply in_app_or in H0; destruct H0; auto.
    destruct H0; auto.
    inversion H0; subst; simpl in H.
    not_in_L x.
    exfalso; apply H3.
    now apply MSetProperties.Dec.F.singleton_2.
  - subst.
    apply OVarSym with (A := A); auto.
    apply in_or_app.
    apply in_app_or in H0; destruct H0; auto.
    destruct H0; auto.
    inversion H0; subst; simpl in H.
    not_in_L x.
    exfalso; apply H4.
    now apply MSetProperties.Dec.F.singleton_2.
  - subst.
    apply ORecEq.
    apply IHOrtho.
    simpl in *; not_in_L z.
    auto.
Qed.

Hint Resolve ortho_weaken ortho_strengthen.

Lemma ortho_extend_comm :
  forall F E x v ty1 ty2,
    Ortho (F ++ E ++ (x, v) :: nil) ty1 ty2 ->
    Ortho (F ++ (x, v) :: nil ++ E) ty1 ty2.
Proof.
  intros F E x v ty1 ty2 HOrtho.
  remember (F ++ E ++ (x, v) :: nil).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  dependent induction HOrtho; intros; subst; auto.
  - apply_fresh OForAll as x.
    unfold extend; simpl.
    change ((y, TyDis (And d1 d2)) :: F ++ (x, v) :: E) with
           (((y, TyDis (And d1 d2)) :: F) ++ ((x, v) :: nil) ++ E).
    apply H0.
    not_in_L y.
    unfold extend; now simpl.
    auto.
  - apply OVar with (A := A); auto.
    apply in_or_app; rewrite app_comm_cons.
    repeat (apply in_app_or in H; destruct H as [H | H]).
    auto.
    right; apply in_or_app; auto.
    right; apply in_or_app; auto.
  - apply OVarSym with (A := A); auto.
    apply in_or_app; rewrite app_comm_cons.
    repeat (apply in_app_or in H; destruct H as [H | H]).
    auto.
    right; apply in_or_app; auto.
    right; apply in_or_app; auto.
Qed.

Lemma ortho_extend_comm' :
  forall F E x v ty1 ty2,
    Ortho (F ++ (x, v) :: nil ++ E) ty1 ty2 ->
    Ortho (F ++ E ++ (x, v) :: nil) ty1 ty2.
Proof.
  intros F E x v ty1 ty2 HOrtho.
  remember (F ++ (x, v) :: nil ++ E).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  dependent induction HOrtho; intros; subst; auto.
  - apply_fresh OForAll as x.
    unfold extend; simpl.
    change ((y, TyDis (And d1 d2)) :: F ++ E ++ (x, v) :: nil) with
           (((y, TyDis (And d1 d2)) :: F) ++ E ++ (x, v) :: nil).
    apply H0.
    not_in_L y.
    unfold extend; now simpl.
    auto.
  - apply OVar with (A := A); auto.
    rewrite app_comm_cons in H.
    apply in_or_app.
    repeat (apply in_app_or in H; destruct H as [H | H]).
    auto.
    right; apply in_or_app; auto.
    right; apply in_or_app; auto.
  - apply OVarSym with (A := A); auto.
    rewrite app_comm_cons in H.
    apply in_or_app.
    repeat (apply in_app_or in H; destruct H as [H | H]).
    auto.
    right; apply in_or_app; auto.
    right; apply in_or_app; auto.
Qed.
    
Lemma ortho_app_comm :
  forall E F ty1 ty2, Ortho (F ++ E) ty1 ty2 -> Ortho (E ++ F) ty1 ty2.
Proof.
  intros E F ty1 ty2 HOrtho.
  remember (F ++ E).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  dependent induction HOrtho; intros; subst; auto.
  - apply_fresh OForAll as x.
    unfold extend; simpl.
    assert (Ha : not (In x L)) by not_in_L x.
    apply H0 with (F0 := extend x (TyDis (And d1 d2)) F) (E0 := E) in Ha.
    apply ortho_extend_comm' in Ha.
    change ((x, TyDis (And d1 d2)) :: E ++ F) with (nil ++ (x, TyDis (And d1 d2)) :: E ++ F).
    apply ortho_extend_comm with (E := E ++ F).
    simpl in *.
    rewrite <- app_assoc.
    apply Ha.
    unfold extend; now simpl.
    auto.
  - apply OVar with (A := A); auto.
    apply in_or_app.
    apply in_app_or in H; destruct H; auto.
  - apply OVarSym with (A := A); auto.
    apply in_or_app.
    apply in_app_or in H; destruct H; auto.
Qed.

Lemma ortho_middle_comm : forall H E F G ty1 ty2,
              Ortho (E ++ F ++ G ++ H) ty1 ty2 ->
              Ortho (E ++ G ++ F ++ H) ty1 ty2.
Proof.
  induction H; intros.
  - rewrite app_nil_r in *.
    rewrite app_assoc.
    apply ortho_app_comm.
    generalize dependent E.
    generalize dependent F.
    induction G; intros.
    + intros; rewrite app_nil_r in *; now apply ortho_app_comm.
    + intros.
      change (F ++ E ++ a :: G) with (F ++ E ++ (a :: nil) ++ G).
      destruct a.
      assert ((F ++ E ++ ((v, t0) :: nil) ++ G) = (F ++ (E ++ ((v, t0) :: nil)) ++ G))
             by now rewrite <- app_assoc.
      rewrite H0; clear H0.
      apply IHG.
      rewrite <- app_assoc.
      apply ortho_extend_comm.
      change (E ++ F ++ (v, t0) :: G) with (E ++ F ++ ((v, t0) :: nil) ++ G) in H.
      rewrite app_assoc in H.
      apply ortho_extend_comm' in H.
      now rewrite <- app_assoc in *.
  - change (E ++ G ++ F ++ a :: H) with (E ++ G ++ F ++ (a :: nil) ++ H).
    destruct a.
    assert ((E ++ G ++ F ++ ((v, t0) :: nil) ++ H) =
            (E ++ G ++ (F ++ ((v, t0) :: nil)) ++ H)) by
    now rewrite <- app_assoc.
    rewrite H1; clear H1.
    apply IHlist.
    rewrite <- app_assoc.
    rewrite app_assoc.
    apply ortho_extend_comm.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite app_assoc in H0.
    rewrite app_assoc in H0.
    change (((E ++ F) ++ G) ++ (v, t0) :: H) with
           (((E ++ F) ++ G) ++ ((v, t0) :: nil) ++ H).
    apply ortho_extend_comm' in H0.
    repeat rewrite <- app_assoc in H0.
    apply H0.
Qed.

Hint Resolve in_or_app.
Hint Resolve in_app_or.

Lemma ortho_env_comm :
  forall E F G H ty1 ty2, Ortho (E ++ F ++ G ++ H) ty1 ty2 ->
                     Ortho (E ++ G ++ F ++ H) ty1 ty2.
Proof.  
  intros.
  remember (E ++ F ++ G ++ H).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  generalize dependent G.
  dependent induction H0; intros; subst; auto.
  - apply_fresh OForAll as x.
    unfold extend; simpl; rewrite app_comm_cons; apply H1.
    not_in_L x.
    reflexivity.
    auto.
  - apply OVar with (A := A); auto.
    repeat (apply in_app_or in H0; destruct H0); auto 10.
  - apply OVarSym with (A := A); auto.
    repeat (apply in_app_or in H0; destruct H0); auto 10.
Qed.

Lemma ortho_weaken_sub :
  forall E G x t1 t2 d1 d2,
    ~ (In x (union (dom E) (dom G))) ->
    Ortho (E ++ extend x (TyDis d1) G) t1 t2 ->
    usub d2 d1  ->
    Ortho (E ++ extend x (TyDis d2) G) t1 t2.
Proof.
  intros E G x t1 t2 d1 d2 HNotIn HOrtho Husub.
  remember (E ++ extend x (TyDis d1) G) as Gamma.
  generalize dependent HeqGamma.
  generalize dependent E.
  induction HOrtho; intros; subst; eauto.
  - apply_fresh OForAll as x.
    assert (extend y (TyDis (And d0 d3)) (E ++ extend x (TyDis d2) G) =
            (extend y (TyDis (And d0 d3)) E) ++ extend x (TyDis d2) G) by
        (unfold extend; now simpl).
    rewrite H2.
    apply H0.
    not_in_L y.
    simpl.
    unfold not; intros; apply HNotIn.
    rewrite MSetProperties.union_add in H3.
    assert (Ha : x <> y).
    not_in_L y; unfold not; intros; subst; apply H16.
    now apply MSetProperties.Dec.F.singleton_iff.
    apply MSetProperties.Dec.F.add_iff in H3.
    destruct H3; auto.
    symmetry in H3; contradiction.
    now simpl.
    auto.
  - destruct (VarTyp.eq_dec x x0); subst.
    assert (Ha : A = d1).
    apply in_app_or in H.
    destruct H.
    not_in_L x0.
    exfalso; apply H2; now apply list_impl_m in H.
    not_in_L x0.
    apply in_app_or in H.
    destruct H.
    inversion H; now inversion H4.
    exfalso; apply H3; now apply list_impl_m in H.
    subst.
    apply OVar with (A := d2); auto.
    apply in_or_app.
    right.
    now left.
    apply usub_trans with (B := d1); auto.
    apply OVar with (A := A); auto.
    apply in_app_or in H.
    destruct H; auto.
    apply in_app_or in H.
    destruct H.
    simpl in H; destruct H.
    inversion H; subst; exfalso; now apply n.
    inversion H.
    apply in_or_app; right.
    apply in_or_app; auto.
  - destruct (VarTyp.eq_dec x x0); subst.
    assert (Ha : A = d1).
    apply in_app_or in H.
    destruct H.
    not_in_L x0.
    exfalso; apply H2; now apply list_impl_m in H.
    not_in_L x0.
    apply in_app_or in H.
    destruct H.
    inversion H; now inversion H4.
    exfalso; apply H3; now apply list_impl_m in H.
    subst.
    apply OVarSym with (A := d2); auto.
    apply in_or_app.
    right.
    now left.
    apply usub_trans with (B := d1); auto.
    apply OVarSym with (A := A); auto.
    apply in_app_or in H.
    destruct H; auto.
    apply in_app_or in H.
    destruct H.
    simpl in H; destruct H.
    inversion H; subst; exfalso; now apply n.
    inversion H.
    apply in_or_app; right.
    apply in_or_app; auto.
Qed.

Lemma ortho_weaken_sub_extend :
  forall Gamma x t1 t2 d1 d2, ~ In x (dom Gamma) ->
                     Ortho (extend x (TyDis d1) Gamma) t1 t2 ->
                     usub d2 d1 ->
                     Ortho (extend x (TyDis d2) Gamma) t1 t2.
Proof.
  intros Gamma x t1 t2 d1 d2 HNotIn HOrtho Husub.
  change (extend x (TyDis d2) Gamma) with (nil ++ extend x (TyDis d2) Gamma).
  apply ortho_weaken_sub with (d1 := d1); auto.
Qed.
  
Lemma Ortho_sym : forall Gamma t1 t2, Ortho Gamma t1 t2 -> Ortho Gamma t2 t1.
Proof.
  intros Gamma t1 t2 HOrtho.
  induction HOrtho; eauto.
  - inversion H1; subst.
    apply_fresh OForAll as x.
    apply ortho_weaken_sub_extend with (d1 := And d1 d2).
    not_in_L x.
    apply H0.
    not_in_L x.
    apply USAnd1.
    apply USAnd3; auto.
    apply usub_refl; auto.
    apply USAnd2.
    apply usub_refl; auto.
    auto.
    auto.
  - apply OAx; auto.
    destruct H as [H1 [H2 H3]].
    unfold OrthoAx; auto.
Qed.


Lemma Ortho_usub_trans :
  forall Gamma u ty d,
    PType ty ->
    Ortho Gamma u d ->
    usub d ty ->
    Ortho Gamma u ty.
Proof.
  intros Gamma u ty d HWFty HOrtho HSub.
  generalize dependent ty.
  induction HOrtho; intros; eauto;
  try now (dependent induction HSub; eauto; inversion HWFty; subst; auto).
  - dependent induction HSub; eauto.
    inversion HWFty; subst; auto.
    inversion HWFty; subst; auto.
    inversion H1; subst.
    apply_fresh OForAll as x.
    apply ortho_weaken_sub_extend with (d1 := And d1 d2).
    not_in_L x.
    apply H0.
    not_in_L x.
    apply H7.
    not_in_L x.
    apply H3.
    not_in_L x.
    apply USAnd1.
    apply USAnd2; auto.
    apply usub_refl; auto.
    apply USAnd3; auto.
    auto.
  - pose (usub_trans _ _ _ HWFty H0 HSub).
    apply OVar with (A := A) ; auto.
  - destruct t1; destruct t2;
    try (destruct H0 as [_ [_ H0]]; exfalso; now apply H0);
    try (now orthoax_inv_r H0); try (now orthoax_inv_l H0);
    try now (induction ty; inversion HSub; subst; inversion HWFty; auto).
Qed.

(* Properties concerning substitution and sub/ortho/wf *)

Lemma ortho_subst_not_in :
  forall Gamma z u t1 t2,
    not (In z (union (fv_ptyp t1) (fv_ptyp t2))) ->
    PType u ->
    Ortho Gamma t1 t2 ->
    Ortho (subst_env Gamma z u) t1 t2.
Proof.  
  intros Gamma z u t1 t2 HNotIn HWFu HOrtho.
  generalize dependent z.
  induction HOrtho; intros z HNotIn; simpl in HNotIn; auto.
  - apply OAnd1; [ apply IHHOrtho1 | apply IHHOrtho2 ]; auto; not_in_L z;
    now inversion HWFt1.
  - apply OAnd2; [ apply IHHOrtho1 | apply IHHOrtho2 ]; auto; not_in_L z;
    now inversion HWFt2.
  - apply OFun; apply IHHOrtho; auto; not_in_L z. 
  - assert (Ha : Ortho (subst_env Gamma z u) (ForAll (subst_typ_source z u d1) t1)
                       (ForAll (subst_typ_source z u d2) t2)).
    apply_fresh OForAll as x. apply H0. not_in_L x.
    unfold not; intros HH; rewrite union_spec in HH; destruct HH as [HH | HH];
    apply fv_open_rec_typ_source in HH; simpl in HH; rewrite union_spec in HH;
    destruct HH as [HH | HH]; try (now not_in_L z);
    not_in_L x; apply H11; apply MSetProperties.Dec.F.singleton_iff;
    apply MSetProperties.Dec.F.singleton_iff in HH; auto.
    apply PType_And.
    apply subst_source_lc; inversion H1; subst; auto.
    apply subst_source_lc; inversion H1; subst; auto.
    assert (Ha1 : d1 = subst_typ_source z u d1) by
        (rewrite subst_typ_source_fresh; auto; not_in_L z).
    assert (Ha2 : d2 = subst_typ_source z u d2) by
        (rewrite subst_typ_source_fresh; auto; not_in_L z).
    now rewrite Ha1, Ha2.
  - apply OVar with (A := subst_typ_source z u A); auto.
    apply in_persists_subst_env; auto.
    apply usub_subst_not_in; auto.
    not_in_L z.
  - apply OVarSym with (A := subst_typ_source z u A); auto.
    apply in_persists_subst_env; auto.
    apply usub_subst_not_in; auto.
    not_in_L z.
  - apply ORecEq.
    apply IHHOrtho.
    not_in_L z.
Qed.
  
Lemma ortho_subst :
  forall z u Gamma d t1 t2,
    not (In z (fv_ptyp u)) ->
    WFEnv (subst_env Gamma z u) ->
    WFEnv Gamma ->
    MapsTo Gamma z d -> 
    Ortho Gamma u d ->
    Ortho Gamma t1 t2 ->
    PType u ->
    PType t1 ->
    PType t2 ->
    Ortho (subst_env Gamma z u) (subst_typ_source z u t1) (subst_typ_source z u t2).
Proof.
  intros z u Gamma d t1 t2 HNotIn HWFEnvS HWFEnv HMapsTo HOrthoud HOrthot1t2 HWFu HWFt1 HWFt2.
  induction HOrthot1t2.
  - simpl; inversion HWFt1; auto.
  - simpl; inversion HWFt2; auto.
  - simpl; inversion HWFt1; inversion HWFt2; subst; auto.
  - simpl; inversion HWFt1; inversion HWFt2; subst.
    apply_fresh OForAll as x.
    repeat rewrite subst_typ_source_open_source_var.
    simpl in H0.
    apply H0.
    not_in_L x.
    apply WFPushV; auto.
    simpl.
    not_in_L x.
    apply fv_subst_source in H6; rewrite union_spec in H6; destruct H6; not_in_L x.
    apply fv_subst_source in H6; rewrite union_spec in H6; destruct H6; not_in_L x.
    rewrite dom_subst_id; not_in_L x.
    apply WFPushV; auto; not_in_L x.
    simpl in H6; rewrite union_spec in H6; destruct H6; not_in_L x.
    apply MapsTo_extend; auto.
    not_in_L x.
    rewrite <- app_nil_l with (l := (extend x (TyDis (And d1 d2)) Gamma)).
    apply ortho_weaken.
    now simpl.
    apply H5.
    not_in_L x.
    apply H9.
    not_in_L x.
    not_in_L x.
    assumption.
    not_in_L x.
    assumption.
    apply PType_And; apply subst_source_lc; auto.
  - assert (Ha : sumbool (x = z) (not (x = z))) by apply VarTyp.eq_dec.
    destruct Ha as [Ha | Ha].
    + assert (HWFEnv' : WFEnv Gamma) by assumption.
      assert (Ha1 : A = d) by (subst; eapply MapsTo_In_eq with (Gamma := Gamma); eauto).
      subst; simpl; rewrite EqFacts.eqb_refl.
      assert (Ha2 : not (In z (fv_ptyp d))) by
          (apply not_in_wfenv with (Gamma := Gamma); auto).
      apply Ortho_usub_trans with (d := subst_typ_source z u d).
      now apply subst_source_lc.
      rewrite subst_typ_source_fresh; auto.
      apply ortho_subst_not_in; auto.
      not_in_L z.
      apply usub_subst; auto.
    + simpl; apply EqFacts.eqb_neq in Ha; rewrite Ha.
      apply OVar with (A := subst_typ_source z u A); auto.
      apply in_persists_subst_env; auto.
      apply usub_subst; auto.
      now apply subst_source_lc.
  - assert (Ha : sumbool (x = z) (not (x = z))) by apply VarTyp.eq_dec.
    destruct Ha as [Ha | Ha].
    + assert (HWFEnv' : WFEnv Gamma) by assumption.
      assert (Ha1 : A = d) by (subst; eapply MapsTo_In_eq with (Gamma := Gamma); eauto).
      subst; simpl; rewrite EqFacts.eqb_refl.
      apply Ortho_sym.
      assert (Ha2 : not (In z (fv_ptyp d))) by
          (apply not_in_wfenv with (Gamma := Gamma); auto).
      apply Ortho_usub_trans with (d := subst_typ_source z u d).
      now apply subst_source_lc.
      rewrite subst_typ_source_fresh; auto.
      apply ortho_subst_not_in; auto.
      not_in_L z.
      apply usub_subst; auto.
    + simpl; apply EqFacts.eqb_neq in Ha; rewrite Ha.
      apply OVarSym with (A := subst_typ_source z u A); auto.
      apply in_persists_subst_env; auto.
      apply usub_subst; auto.
      now apply subst_source_lc.
  - simpl; apply OTop1.
  - simpl; apply OTop2.
  - simpl; inversion HWFt1; inversion HWFt2; subst; auto.
  - simpl; inversion HWFt1; inversion HWFt2; subst; auto.
  - apply OAx; auto.
    assert (Ha : OrthoAx t1 t2) by assumption.
    destruct t1; destruct t2; auto; simpl; try (now orthoax_inv_r H0);
    try now orthoax_inv_l H0.
Qed.

End MDisjointness.