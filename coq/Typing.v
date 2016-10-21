Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import SystemF.
Require Import Coq.Program.Equality.
Require Import Disjointness.

Module MTyping
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).
  
Module MDisjointness := MDisjointness(VarTyp)(set).
Export MDisjointness.

(* Well-formed types *)

Inductive WFTyp : context TyEnvSource -> PTyp -> Prop := 
  | WFInt : forall Gamma, WFEnv Gamma -> WFTyp Gamma PInt
  | WFFun : forall Gamma t1 t2, WFTyp Gamma t1 -> WFTyp Gamma t2 -> WFTyp Gamma (Fun t1 t2)
  | WFAnd : forall Gamma t1 t2, WFTyp Gamma t1 -> WFTyp Gamma t2 -> Ortho Gamma t1 t2 -> WFTyp Gamma (And t1 t2)
  | WFVar : forall Gamma x ty, List.In (x,TyDis ty) Gamma -> WFEnv Gamma -> WFTyp Gamma (PFVarT x)
  | WFForAll : forall L Gamma d t,
                 (forall x, not (In x L) -> WFTyp (extend x (TyDis d) Gamma) (open_typ_source t (PFVarT x))) ->
                 WFTyp Gamma d ->
                 WFTyp Gamma (ForAll d t)
  | WFTop : forall Gamma, WFEnv Gamma -> WFTyp Gamma Top
  | WFRec : forall Gamma l t, WFTyp Gamma t -> WFTyp Gamma (Rec l t).

Hint Constructors WFTyp.

Inductive Dir := Inf | Chk.

(* bidirection type-system (algorithmic): 

T |- e => t ~> E     (inference mode: infers the type of e producing target E) (use Inf)
T |- e <= t ~> E     (checking mode: checks the type of e producing target E) (use Chk)

Inspiration for the rules:

https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf

 *)

Inductive has_type_source_alg : context TyEnvSource -> PExp -> Dir -> PTyp -> (SExp var) -> Prop :=
  (* Inference rules *)
  | ATyTop : forall Gamma, WFEnv Gamma -> has_type_source_alg Gamma PUnit Inf Top (STUnit _)
  | ATyVar : forall Gamma x ty, WFEnv Gamma -> List.In (x,TermV ty) Gamma -> WFTyp Gamma ty ->
                      has_type_source_alg Gamma (PFVar x) Inf ty (STFVar _ x) 
  | ATyLit : forall Gamma x, WFEnv Gamma -> has_type_source_alg Gamma (PLit x) Inf PInt (STLit _ x)
  | ATyApp : forall Gamma A B t1 t2 E1 E2,
              has_type_source_alg Gamma t1 Inf (Fun A B) E1 ->
              has_type_source_alg Gamma t2 Chk A E2 ->
              has_type_source_alg Gamma (PApp t1 t2) Inf B (STApp _ E1 E2)
  | ATyMerge : forall Gamma A B t1 t2 E1 E2,
                has_type_source_alg Gamma t1 Inf A E1 ->
                has_type_source_alg Gamma t2 Inf B E2 ->
                Ortho Gamma A B ->
                has_type_source_alg Gamma (PMerge t1 t2) Inf (And A B) (STPair _ E1 E2)
  | ATyAnn : forall Gamma t1 A E, has_type_source_alg Gamma t1 Chk A E ->
                         has_type_source_alg Gamma (PAnn t1 A) Inf A E
  | ATyTApp : forall Gamma t A ty d E,
                WFTyp Gamma A ->
                has_type_source_alg Gamma t Inf (ForAll d ty) E ->
                Ortho Gamma A d -> 
                has_type_source_alg Gamma (PTApp t A) Inf (open_typ_source ty A) (STTApp _ E (|A|))
  | ATyRec : forall Gamma l t A E,
               has_type_source_alg Gamma t Inf A E ->
               has_type_source_alg Gamma (PRec l t) Inf (Rec l A) E
  | ATyProjR : forall Gamma l t A E,
                 has_type_source_alg Gamma t Inf (Rec l A) E ->
                 has_type_source_alg Gamma (PProjR t l) Inf A E
  (* Checking rules *)
  | ATyLam : forall L Gamma t A B E,
               (forall x, not (In x L) -> 
                     has_type_source_alg (extend x (TermV A) Gamma) (open_source t (PFVar x)) Chk B (open E (STFVar _ x))) ->
               WFTyp Gamma A ->
               has_type_source_alg Gamma (PLam t) Chk (Fun A B) (STLam _ E)
  | ATySub : forall Gamma t A B C E,
               has_type_source_alg Gamma t Inf A E ->
               sub A B C ->
               WFTyp Gamma B ->
               has_type_source_alg Gamma t Chk B (STApp _ C E)
  | ATyTLam : forall L Gamma t A d E,
               WFTyp Gamma d ->
               (forall x, not (In x L) -> 
                     has_type_source_alg (extend x (TyDis d) Gamma)
                                         (open_typ_term_source t (PFVarT x))
                                         Chk
                                         (open_typ_source A (PFVarT x))
                                         (open_typ_term E (STFVarT x))) ->
               has_type_source_alg Gamma (PTLam d t) Chk (ForAll d A) (STTLam _ E).

Hint Constructors has_type_source_alg.

(** Well-formedness of types **)

Lemma wf_gives_wfenv : forall Gamma ty, WFTyp Gamma ty -> WFEnv Gamma.
Proof.
  intros Gamma ty H; induction H; auto.
Qed.

Hint Resolve wf_gives_wfenv.

Lemma wf_weaken_source : forall G E F ty,
   WFTyp (E ++ G) ty -> 
   WFEnv (E ++ F ++ G) ->
   WFTyp (E ++ F ++ G) ty.
Proof.
  intros.
  generalize dependent H0.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent E.
  dependent induction H; intros; eauto.  
  - subst; apply WFAnd.
    apply IHWFTyp1; auto.
    apply IHWFTyp2; auto.
    apply ortho_weaken; auto.
  (* Var *)
  - subst.
    apply WFVar with (ty := ty).
    apply in_app_or in H.
    inversion H.
    apply in_or_app; left; assumption.
    apply in_or_app; right; apply in_or_app; right; assumption.  
    assumption.
  (* ForAll *)
  - apply_fresh WFForAll as x.
    intros.
    intros.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    apply H0.
    not_in_L x.
    unfold extend; simpl; reflexivity.
    rewrite <- app_comm_cons.
    apply WFPushV.
    apply H2.
    not_in_L x.
    not_in_L x.
    rewrite dom_union in H8.
    rewrite union_spec in H8.
    inversion H8; contradiction.
    subst.
    auto.
Qed.    
    
Lemma wf_strengthen_source : forall z U E F ty,
  not (In z (fv_ptyp ty)) ->
  WFTyp (E ++ ((z,U) :: nil) ++ F) ty ->
  WFTyp (E ++ F) ty.
Proof.
  intros.
  remember (E ++ ((z,U) :: nil) ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; auto.
  - apply WFInt.
    subst.
    now apply wfenv_remove in H0.
  - eapply WFFun.
    subst.
    apply IHWFTyp1; simpl in *; not_in_L z; reflexivity.
    subst.
    apply IHWFTyp2; simpl in *; not_in_L z; reflexivity.
  - eapply WFAnd.
    subst.
    apply IHWFTyp1; simpl in *; not_in_L z; reflexivity.
    subst.
    apply IHWFTyp2; simpl in *; not_in_L z; reflexivity.
    subst; eauto.
  - subst; eapply WFVar.
    apply in_or_app.
    repeat apply in_app_or in H0.
    inversion H0.
    left; apply H2.
    apply in_app_or in H2.
    inversion H2.
    inversion H3.
    inversion H4.
    subst.
    exfalso; apply H; simpl.
    left; reflexivity.
    inversion H4.
    auto.
    now apply wfenv_remove in H1.
  - subst.
    apply_fresh WFForAll as x.
    unfold extend in *; simpl in *; intros.
    rewrite app_comm_cons.
    eapply H1.
    not_in_L x.
    not_in_L z.
    apply fv_open_rec_typ_source in H.
    rewrite union_spec in H.
    inversion H.
    auto.
    assert (NeqXZ : not (In x (singleton z))) by (not_in_L x).
    simpl in H5.
    exfalso; apply NeqXZ.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in H5.
    symmetry; assumption.
    rewrite app_comm_cons.
    reflexivity.
    apply IHWFTyp.
    simpl in H; not_in_L z.
    reflexivity.
  - apply WFTop.
    subst.
    now apply wfenv_remove in H0.
  - eapply WFRec; subst; apply IHWFTyp; simpl in *; not_in_L z; reflexivity.
Qed.

Lemma wf_env_comm_source : forall E F G H ty,
              WFTyp (E ++ F ++ G ++ H) ty ->
              WFTyp (E ++ G ++ F ++ H) ty.
Proof.
  intros.
  remember (E ++ F ++ G ++ H).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  generalize dependent G.
  dependent induction H0; intros; subst; auto.
  - apply WFInt.
    now apply wfenv_middle_comm.
  - apply WFAnd; auto.
    now apply ortho_middle_comm.
  - eapply WFVar.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app; left; apply H2.
    apply in_or_app; right.
    apply in_app_or in H2.
    inversion H2.
    apply in_or_app.
    right; apply in_or_app; left.
    assumption.
    apply in_app_or in H3.
    inversion H3.
    apply in_or_app; auto.
    apply in_or_app; right; apply in_or_app; auto.
    now apply wfenv_middle_comm.
  - apply_fresh WFForAll as x.
    unfold extend.
    intros.
    simpl.
    rewrite app_comm_cons.
    apply H1.
    not_in_L x.
    unfold extend; now simpl.
    now apply IHWFTyp.
  - apply WFTop.
    now apply wfenv_middle_comm in H0.
Qed.

Lemma wf_env_comm_extend_source : forall Gamma x y v1 v2 ty,
              WFTyp (extend x v1 (extend y v2 Gamma)) ty ->
              WFTyp (extend y v2 (extend x v1 Gamma)) ty.
Proof.
  unfold extend.
  intros.
  rewrite <- app_nil_l with (l := ((x, v1) :: nil) ++ ((y, v2) :: nil) ++ Gamma) in H.
  apply wf_env_comm_source in H.
  now rewrite app_nil_l in H.
Qed. 
  
Lemma wf_weaken_extend_source_tydis : forall ty x v Gamma,
   WFTyp Gamma ty ->
   not (M.In x (union (dom Gamma) (fv_ptyp v))) ->                            
   WFTyp ((x,TyDis v) :: Gamma) ty.
Proof.
  intros.
  induction H; eauto.
  - apply WFInt.
    apply WFPushV; auto.
    not_in_L x.
    not_in_L x.
  - apply WFAnd; auto.
    rewrite <- app_nil_l with (l := ((x, TyDis v) :: Gamma)).
    change ((x, TyDis v) :: Gamma) with (((x, TyDis v) :: nil) ++ Gamma).
    apply ortho_weaken.
    now rewrite app_nil_l.
  - eapply WFVar.
    apply in_cons; apply H.
    apply WFPushV; auto.
    not_in_L x.
    not_in_L x.
  - apply_fresh WFForAll as x; cbn.
    unfold extend in H1.
    intros.
    apply wf_env_comm_extend_source.
    apply H1.
    not_in_L y.
    simpl; not_in_L x.
    apply MSetProperties.Dec.F.add_iff in H0.
    destruct H0.
    not_in_L y.
    not_in_L x.
    apply IHWFTyp.
    not_in_L x.
  - apply WFTop.
    apply WFPushV; auto.
    not_in_L x.
    not_in_L x.
Qed.

Lemma wf_weaken_extend_source_termv : forall ty x v Gamma,
   WFTyp Gamma ty ->
   not (M.In x (union (dom Gamma) (fv_ptyp v))) ->                            
   WFTyp ((x,TermV v) :: Gamma) ty.
Proof.
  intros.
  induction H; eauto.
  - apply WFInt.
    apply WFPushT; auto.
    not_in_L x.
  - apply WFAnd; auto.
    rewrite <- app_nil_l with (l := ((x, TermV v) :: Gamma)).
    change ((x, TermV v) :: Gamma) with (((x, TermV v) :: nil) ++ Gamma).
    apply ortho_weaken.
    now rewrite app_nil_l.
  - eapply WFVar.
    apply in_cons; apply H.
    apply WFPushT; auto.
    not_in_L x.
  - apply_fresh WFForAll as x; cbn.
    unfold extend in H1.
    intros.
    apply wf_env_comm_extend_source.
    apply H1.
    not_in_L y.
    simpl; not_in_L x.
    apply MSetProperties.Dec.F.add_iff in H0.
    destruct H0.
    not_in_L y.
    not_in_L x.
    apply IHWFTyp.
    not_in_L x.
  - apply WFTop.
    apply WFPushT; auto.
    not_in_L x.
Qed.

Lemma wf_gives_types_source : forall Gamma ty, WFTyp Gamma ty -> PType ty.
Proof.
  intros.
  induction H; auto.
  - apply_fresh PType_ForAll as x.
    auto.
    apply H0.
    not_in_L x.
Qed.

Hint Resolve wf_gives_types_source.

Lemma subst_source_wf_typ_not_in :
  forall Gamma z t u, WFEnv (subst_env Gamma z u) ->
             WFTyp Gamma u ->
             WFTyp Gamma t ->
             ~ In z (fv_ptyp t) ->
             WFTyp (subst_env Gamma z u) t.
Proof.
  intros Gamma z t u HWFEnv HWFu HWFt HNotIn.
  induction HWFt; auto.
  - simpl in HNotIn; apply WFFun; [ apply IHHWFt1 | apply IHHWFt2 ];
    auto; not_in_L z.
  - simpl in HNotIn; apply WFAnd.
    apply IHHWFt1; auto; not_in_L z.
    apply IHHWFt2; auto; not_in_L z.
    apply ortho_subst_not_in; eauto.
  - apply WFVar with (ty := subst_typ_source z u ty); auto.
    now apply in_persists_subst_env.
  - rewrite <- subst_typ_source_fresh with (x := z) (u := u) (t := d).
    apply_fresh WFForAll as x.
    apply H0.
    not_in_L x.
    simpl; apply WFPushV; auto.
    unfold not; intros HH; apply fv_subst_source in HH;
    rewrite union_spec in HH; destruct HH as [HH | HH]; not_in_L x.
    rewrite dom_subst_id; not_in_L x.
    apply wf_weaken_extend_source_tydis; auto.
    not_in_L x.
    unfold not; intros HH; apply fv_open_rec_typ_source in HH; simpl in *.
    rewrite union_spec in HH; destruct HH as [HH | HH].
    not_in_L z.
    not_in_L x.
    apply H8; apply MSetProperties.Dec.F.singleton_iff;
    apply MSetProperties.Dec.F.singleton_iff in HH; auto.
    rewrite subst_typ_source_fresh.
    apply IHHWFt; auto.
    not_in_L z; simpl; rewrite union_spec; auto.
    not_in_L z; simpl; rewrite union_spec; auto.
    not_in_L z; simpl; rewrite union_spec; auto.
  - simpl in HNotIn; apply WFRec; apply IHHWFt; auto; not_in_L z.
Qed.

Lemma subst_source_wf_typ :
  forall t z u Gamma d, not (In z (fv_ptyp u)) ->
               MapsTo Gamma z d ->
               WFEnv (subst_env Gamma z u) ->
               Ortho Gamma u d ->
               WFTyp Gamma u ->
               WFTyp Gamma t ->
               WFTyp (subst_env Gamma z u) (subst_typ_source z u t).
Proof.
  intros t z u Gamma d HNotIn HMapsTo HForAll HOrtho HWFu HWFt.
  induction HWFt; simpl; auto.
  - apply WFAnd; auto.
    eapply ortho_subst; eauto.
  - assert (Ha : sumbool (x = z) (not (x = z))) by apply VarTyp.eq_dec.
    destruct Ha as [Ha | Ha].
    + subst; rewrite EqFacts.eqb_refl; auto.
      apply subst_source_wf_typ_not_in; auto.
    + apply EqFacts.eqb_neq in Ha.
      rewrite Ha.
      apply WFVar with (ty := subst_typ_source z u ty); auto.
      apply in_persists_subst_env; auto.
  - assert (Ha : WFTyp (subst_env Gamma z u) (subst_typ_source z u d0)) by
        (apply IHHWFt; auto); clear IHHWFt.
    apply_fresh WFForAll as x.
    simpl in H0.
    rewrite subst_typ_source_open_source_var.
    apply H0.
    not_in_L x.
    eapply MapsTo_extend; auto.
    not_in_L x.
    apply WFPushV; auto.
    unfold not; intros HH; apply fv_subst_source in HH;
    rewrite union_spec in HH; destruct HH as [HH | HH]; not_in_L x.
    rewrite dom_subst_id; not_in_L x.
    rewrite <- app_nil_l with (l := (extend x (TyDis d0) Gamma)).
    apply ortho_weaken.
    now simpl.
    apply wf_weaken_extend_source_tydis.
    now apply wf_gives_wfenv in HWFt.
    not_in_L x.
    not_in_L x.
    now apply wf_gives_types_source in HWFu.
    auto.
Qed.

Hint Resolve wf_gives_wfenv wf_weaken_source wf_gives_types_source.
    
Definition body_wf_typ t d Gamma :=
  exists L, forall x, not (In x L) -> WFTyp Gamma d ->
            WFTyp (extend x (TyDis d) Gamma) (open_typ_source t (PFVarT x)).

Lemma forall_to_body_wf_typ : forall d t1 Gamma, 
  WFTyp Gamma (ForAll d t1) -> body_wf_typ t1 d Gamma.
Proof. intros. unfold body_wf_typ. inversion H; subst; eauto. Qed.

Lemma open_body_wf_type :
  forall t d u Gamma, body_wf_typ t d Gamma -> Ortho Gamma u d -> WFTyp Gamma d -> WFTyp Gamma u ->
             WFTyp Gamma (open_typ_source t u).
Proof.
  intros. destruct H. pick_fresh y.
  assert (Ha : not (In y x)) by not_in_L y.
  apply H in Ha; auto.
  rewrite <- app_nil_l with (l := Gamma).
  apply wf_strengthen_source with (z := y) (U := TyDis d).
  unfold not; intros HH.
  apply fv_open_rec_typ_source in HH.
  rewrite union_spec in HH.
  destruct HH; not_in_L y.
  rewrite subst_typ_source_intro with (x := y); eauto.
  change (nil ++ ((y, TyDis d) :: nil) ++ Gamma) with (nil ++ extend y (TyDis d) Gamma).
  assert (Ha1 : nil ++ (extend y (TyDis d) Gamma) =
                subst_env (nil ++ (extend y (TyDis d) Gamma)) y u).
  rewrite subst_env_codom_fresh. reflexivity.
  not_in_L y.
  simpl in H5; rewrite union_spec in H5; destruct H5; contradiction.
  rewrite Ha1.
  apply subst_source_wf_typ with (d := d); eauto.
  not_in_L y.
  unfold MapsTo; simpl; now rewrite EqFacts.eqb_refl.
  rewrite <- Ha1.
  now apply wf_gives_wfenv in Ha.
  apply ortho_weaken.
  auto.
  apply wf_weaken_extend_source_tydis; auto.
  not_in_L y.
  not_in_L y.
Qed.

Lemma WFTyp_to_WFType : forall Gamma ty, WFTyp Gamma ty -> WFType (∥ Gamma ∥) (| ty |).
Proof.
  intros Gamma ty H.
  induction H; simpl; auto.
  - apply wfenv_to_ok in H0.
    apply WFType_Var; auto.
    now apply in_persists in H.
  - apply_fresh WFType_ForAll as x.
    simpl in *.
    assert (Ha : not (In x L)) by (not_in_L x).
    apply H0 in Ha.
    unfold extend; simpl.
    unfold open_typ_source in Ha.
    now rewrite open_rec_typ_eq_source in Ha.
Qed.

Hint Resolve WFTyp_to_WFType.

End MTyping.