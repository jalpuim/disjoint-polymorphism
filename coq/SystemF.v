Require Import Coq.Arith.EqNat.
Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.PeanoNat.
Require Import MSetProperties.
Require Import Coq.Init.Specif.

Module SysF
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module EqFacts := BoolEqualityFacts(VarTyp).

Module M := MSetWeakList.Make(VarTyp).
Export M.
  
Module MSetProperties := WPropertiesOn(VarTyp)(M).

Definition var : Type := VarTyp.t.

Inductive STyp :=
  | STUnitT : STyp
  | STInt : STyp
  | STFun : STyp -> STyp -> STyp
  | STTuple : STyp -> STyp -> STyp
  | STFVarT : var -> STyp
  | STBVarT : nat -> STyp
  | STForAll : STyp -> STyp.

Inductive SExp (A : Type) :=
  | STFVar  : A -> SExp A
  | STBVar  : nat -> SExp A
  | STUnit  : SExp A
  | STLit   : nat -> SExp A
  | STLam   : SExp A -> SExp A
  | STApp   : SExp A -> SExp A -> SExp A
  | STPair  : SExp A -> SExp A -> SExp A
  | STProj1 : SExp A -> SExp A
  | STProj2 : SExp A -> SExp A
  | STTLam  : SExp A -> SExp A
  | STTApp  : SExp A -> STyp -> SExp A.

Definition Exp := forall A, SExp A.

Definition vars := M.t.

(** Definitions borrowed from STLC_Tutorial **)

(* Contexts *)
Definition context (A : Type) := list (var * A). 

Definition extend {A} (x : var) (a : A) (c : context A) : context A :=
  ((x,a) :: nil) ++ c.

Definition dom {A} (c : context A) : vars :=
  fold_right (fun el r => add (fst el) r) empty c.

(* Functions on contexts *)
Definition mapctx {A B} (f : A -> B) (c : context A) : context B :=
  map (fun p => (fst p, (f (snd p)))) c.

Lemma cons_to_push : forall {A} x v (E : context A),
  (x, v) :: E = extend x v E.
Proof. intros; unfold extend; simpl; reflexivity. Qed.

Lemma env_ind : forall {A} (P : context A -> Prop),
  (P nil) ->
  (forall E x v, P E -> P (extend x v E)) ->
  (forall E, P E).
Proof.
  unfold extend.
  induction E as [|(x,v)].
  assumption.
  pose (H0 _ x v IHE).
  now simpl in p.
Qed.

Lemma dom_map_id : forall (A B : Type) (E : context A) (f : A -> B),
  dom E = dom (mapctx f E).
Proof.
  unfold mapctx.
  intros.
  induction E.
  simpl; reflexivity.
  simpl in *.
  rewrite IHE.
  reflexivity.
Qed.

Lemma dom_union : forall (A : Type) (E G : context A) x,
  M.In x (dom (E ++ G)) <-> M.In x (M.union (dom E) (dom G)).
Proof.
  intros. generalize dependent G.
  induction E; intros.
  unfold dom at 2; simpl.
  unfold "<->".
  split; intros.
  apply MSetProperties.Dec.F.union_3.
  assumption.
  apply MSetProperties.Dec.F.union_1 in H.
  inversion H.
  inversion H0.
  assumption.
  simpl.
  destruct a.
  split; intros.
  simpl in *.
  assert (Ha : sumbool (VarTyp.eq v x) (not( VarTyp.eq v x))) by apply VarTyp.eq_dec.
  destruct Ha.
  apply MSetProperties.Dec.F.union_2.
  apply MSetProperties.Dec.F.add_iff.
  auto.
  rewrite (MSetProperties.Dec.F.add_neq_iff _ n) in H.
  assert (Ha : M.Equal (M.union (M.add v (dom E)) (dom G)) (M.add v (M.union (dom E) (dom G)))) by apply MSetProperties.union_add.
  apply Ha.
  apply IHE in H.
  unfold not in n.
  apply MSetProperties.Dec.F.add_2.
  assumption.
  simpl in *.
  apply MSetProperties.Dec.F.union_1 in H.
  destruct H.
  assert (Ha : sumbool (VarTyp.eq v x) (not( VarTyp.eq v x))) by apply VarTyp.eq_dec.
  destruct Ha.
  apply MSetProperties.Dec.F.add_iff; auto.
  rewrite (MSetProperties.Dec.F.add_neq_iff _ n) in H.
  apply MSetProperties.Dec.F.add_neq_iff; auto.
  apply IHE.
  apply MSetProperties.Dec.F.union_2; assumption.
  apply MSetProperties.Dec.F.add_iff.
  right.
  apply IHE.
  apply MSetProperties.Dec.F.union_3; assumption.
Qed.

Lemma list_impl_m : forall {A} Gamma x (v : A), List.In (x, v) Gamma -> M.In x (dom Gamma).
Proof.
  intros.
  induction Gamma.
  inversion H.
  simpl.
  destruct a.
  simpl in *.
  inversion H.
  apply MSetProperties.Dec.F.add_1.
  apply f_equal with (f := fst) in H0.
  simpl in H0.
  rewrite H0.
  reflexivity.
  apply MSetProperties.Dec.F.add_2.
  apply IHGamma; assumption.
Qed.

Ltac not_in_L x :=
  repeat rewrite dom_union; repeat rewrite M.union_spec;
  repeat match goal with
    | H: M.In x M.empty |- _ => inversion H
    | H:_ |- context [M.In x (dom nil)] => simpl
    | H:_ |- context [M.In x (dom ((?v, ?t) :: ?l))] => simpl; rewrite MSetProperties.Dec.F.add_iff
    | H: _ |- context [M.In ?v (dom ((x, ?t) :: ?l))] => simpl; rewrite MSetProperties.Dec.F.add_iff
    | H1: ~ ?l, H2: ?l |- _ => contradiction
    | H: ~ M.In ?y (M.singleton x) |- not (x = ?y) => rewrite MSetProperties.Dec.F.singleton_iff in H; assumption 
    | H: ~ M.In x (M.singleton ?y) |- not (x = ?y) => rewrite MSetProperties.Dec.F.singleton_iff in H; unfold not; intros; apply H; symmetry; assumption
    | H: ~ M.In x (M.add ?v M.empty) |- _ => rewrite <- MSetProperties.singleton_equal_add in H 
    | H: not (M.In x (dom ?l)) |- _ => rewrite dom_union in H; simpl in H
    | H: not (M.In x (M.union ?l1 ?l2)) |- _ =>
      rewrite M.union_spec in H
    | H: not (M.In x ?l3 \/ ?l) |- _ =>
      let l := fresh in
      let r := fresh in
      apply not_or_and in H; destruct H as [l r]
    | H: not (?l \/ M.In x ?l3) |- _ =>
      let l := fresh in
      let r := fresh in
      apply not_or_and in H; destruct H as [l r]
    | H: not (M.In x ?l1) |- not (M.In x ?l1) => assumption
    | H:_ |- ~ (x = ?v \/ M.In ?v ?l) => unfold not; intro HInv; inversion HInv as [HH | HH]
    | H:_ |- not (?A \/ ?B) => apply and_not_or; split
    | H1: ~ M.In x (M.singleton ?v), H2: ?v = x |- _ => exfalso; apply H1; apply MSetProperties.Dec.F.singleton_2; assumption
    | H1: ~ M.In x (M.singleton ?v), H2: x = ?v |- _ => exfalso; apply H1; apply MSetProperties.Dec.F.singleton_2; symmetry; assumption
    | H: not (M.In x ?l1) |- not (M.In x ?l2) =>
      unfold not; intros; apply H; repeat rewrite M.union_spec; auto 10 
  end.

(* Ok *)

Inductive ok {A} : context A -> Prop :=
  | Ok_nil : ok nil
  | Ok_push : forall (E : context A) (v : var) (ty : A),
                ok E -> not (In v (dom E)) -> ok (extend v ty E).        

Hint Constructors ok.

Lemma ok_app_l : forall {A} (E F : context A), ok (E ++ F) -> ok E.
Proof.
  intros A E; induction E; intros.
  apply Ok_nil.
  inversion H.
  subst.
  apply Ok_push.
  apply (IHE _ H2).
  not_in_L v.
Qed.  
  
Lemma ok_app_r : forall {A} (E F : context A), ok (E ++ F) -> ok F.
Proof.
  intros A E.
  induction E; intros.
  - rewrite app_nil_l in H.
    auto.
  - inversion H; subst.
    apply (IHE _ H2).
Qed.

Lemma ok_remove : forall {A} (E F G : context A), ok (E ++ G ++ F) -> ok (E ++ F).
Proof.
  intros.
  induction E using env_ind.
  rewrite app_nil_l in *.
  now apply ok_app_r in H.
  unfold extend; rewrite <- app_assoc.
  apply Ok_push.
  apply IHE.
  unfold extend in H; rewrite <- app_assoc in H.
  inversion H; subst.
  assumption.
  unfold extend in H.
  inversion H; subst.
  rewrite dom_union in *.
  rewrite union_spec in *.
  unfold not; intros.
  apply H4.
  inversion H0.
  auto.
  right.
  rewrite dom_union; rewrite union_spec.
  auto.
Qed.
  
Lemma ok_extend_comm : forall {A} (E F : context A) x v,
               ok (F ++ E ++ (x, v) :: nil) ->
               ok (F ++ (x, v) :: nil ++ E).
Proof.
  intros A E F x v HOk.  
  generalize dependent E.
  
  induction F using env_ind; intros.
  unfold extend; simpl.
  rewrite app_nil_l in HOk.
  apply Ok_push.
  now apply ok_app_l in HOk.
  induction E.
  unfold not; intros HInv; inversion HInv.
  simpl.
  rewrite <- app_comm_cons in HOk.
  inversion HOk; subst.
  apply IHE in H1.
  simpl in *.
  unfold not; intros H3; apply MSetProperties.Dec.F.add_iff in H3.
  inversion H3.
  rewrite H in H2.
  rewrite dom_union in H2.
  rewrite union_spec in H2.
  apply not_or_and in H2.
  inversion H2.
  simpl in H4.
  apply H4.
  apply MSetProperties.Dec.F.add_1.
  reflexivity.
  contradiction.
  unfold extend.
  rewrite <- app_assoc.
  apply Ok_push.
  apply IHF.
  inversion HOk.
  subst.
  assumption.
  rewrite dom_union.
  rewrite union_spec.
  unfold not; intros.
  inversion H.
  apply ok_app_l in HOk.
  inversion HOk.
  subst.
  contradiction.
  simpl in H0.
  apply MSetProperties.Dec.F.add_iff in H0.
  inversion H0.
  unfold extend in HOk.
  apply ok_remove in HOk.
  rewrite <- app_assoc in HOk.
  apply ok_remove in HOk.
  simpl in HOk.
  inversion HOk; subst.
  simpl in *.
  apply H6.
  apply MSetProperties.Dec.F.add_1.
  reflexivity.
  inversion HOk; subst.
  rewrite dom_union in H6; rewrite union_spec in H6.
  apply not_or_and in H6.
  inversion H6.
  rewrite dom_union in H3; rewrite union_spec in H3; apply not_or_and in H3.
  inversion H3.
  contradiction.
Qed.
  
Lemma ok_app_comm : forall {A} (E F : context A), ok (F ++ E) -> ok (E ++ F).
Proof.
  intros.
  generalize dependent H.
  generalize dependent F.
  dependent induction E using (@env_ind A).
  intros.
  rewrite app_nil_r in H.
  now simpl.
  intros.
  unfold extend in *.
  rewrite <- app_assoc.
  apply Ok_push.
  apply IHE.
  apply ok_remove in H.
  assumption.
  rewrite dom_union.
  rewrite union_spec.
  unfold not; intros.
  inversion H0.
  apply ok_app_r in H.
  inversion H; subst.
  contradiction.
  rewrite app_assoc in H.
  apply ok_app_l in H.
  rewrite <- app_nil_l in H.
  apply ok_extend_comm in H.
  rewrite app_nil_l in H.
  simpl in H.
  inversion H; subst.
  contradiction.
Qed.  
  
Definition ok_app_and {A} (E F : context A) (H : ok (E ++ F)) : ok E /\ ok F :=
  conj (ok_app_l _ _ H) (ok_app_r _ _ H).

Lemma ok_middle_comm :
  forall {A} (E : context A) F G H, ok (E ++ F ++ G ++ H) -> ok (E ++ G ++ F ++ H).
Proof.
  intros.
  induction E.
  generalize dependent F.
  induction H; intros.
  rewrite app_nil_l in *.
  rewrite app_nil_r in *.
  now apply ok_app_comm.
  rewrite app_nil_l.
  rewrite app_assoc.
  apply ok_app_comm.
  rewrite <- app_comm_cons.
  destruct a.
  apply Ok_push.
  apply ok_app_comm.
  rewrite <- app_assoc.
  rewrite app_nil_l in H0.
  rewrite app_assoc in H0.
  apply ok_app_comm in H0.
  rewrite <- app_comm_cons in H0.
  inversion H0; subst.
  apply IHlist.
  rewrite app_nil_l.
  apply ok_app_comm in H3.
  now rewrite <- app_assoc in H3.
  rewrite app_nil_l in H0.
  rewrite app_assoc in H0.
  apply ok_app_comm in H0.
  rewrite <- app_comm_cons in H0.
  inversion H0; subst.
  not_in_L v.
  rewrite dom_union in H2; rewrite union_spec in H2; inversion H2; contradiction.
  intros.
  rewrite <- app_comm_cons.
  destruct a.
  apply Ok_push.
  apply IHE.
  rewrite <- app_comm_cons in H0.
  inversion H0.
  assumption.
  rewrite <- app_comm_cons in H0.
  inversion H0.
  subst.
  not_in_L v.
  rewrite dom_union in H5; rewrite union_spec in H5; inversion H5.
  contradiction.
  rewrite dom_union in H7; rewrite union_spec in H7; inversion H7.
  contradiction.
  contradiction.
Qed.

(** Target language **)

Fixpoint fv_typ (sTyp : STyp) : vars :=
  match sTyp with
  | STUnitT       => empty
  | STInt         => empty
  | STFun t1 t2   => union (fv_typ t1) (fv_typ t2)
  | STTuple t1 t2 => union (fv_typ t1) (fv_typ t2)
  | STFVarT v     => singleton v 
  | STBVarT n     => empty
  | STForAll t    => fv_typ t
  end.

Fixpoint fv (sExp : SExp var) : vars :=
  match sExp with
    | STFVar _ v => singleton v
    | STBVar _ _ => empty
    | STUnit _ => empty
    | STLit _ _ => empty
    | STLam _ t => fv t
    | STApp _ t1 t2 => union (fv t1) (fv t2)
    | STPair _ t1 t2 => union (fv t1) (fv t2)
    | STProj1 _ t => fv t
    | STProj2 _ t => fv t
    | STTLam _ t => fv t
    | STTApp _ t ty => union (fv t) (fv_typ ty)      
  end.

Fixpoint open_rec_typ (k : nat) (u : STyp) (t : STyp) {struct t} : STyp :=
  match t with
  | STUnitT       => STUnitT
  | STInt         => STInt
  | STFun t1 t2   => STFun (open_rec_typ k u t1) (open_rec_typ k u t2)
  | STTuple t1 t2 => STTuple (open_rec_typ k u t1) (open_rec_typ k u t2) 
  | STFVarT x     => STFVarT x
  | STBVarT i     => if Nat.eqb k i then u else (STBVarT i)
  | STForAll t    => STForAll (open_rec_typ (S k) u t)
  end.

Fixpoint open_rec_typ_term (k : nat) (u : STyp) (t : SExp var) {struct t} :
  SExp var :=
  match t with
  | STBVar _ i => STBVar _ i
  | STFVar _ x => STFVar _ x
  | STUnit _ => STUnit _
  | STLit _ x => STLit _ x
  | STLam _ t1 => STLam _ (open_rec_typ_term k u t1)    
  | STApp _ t1 t2 => STApp _ (open_rec_typ_term k u t1) (open_rec_typ_term k u t2)
  | STPair _ t1 t2 => STPair _ (open_rec_typ_term k u t1) (open_rec_typ_term k u t2)
  | STProj1 _ t => STProj1 _ (open_rec_typ_term k u t)
  | STProj2 _ t => STProj2 _ (open_rec_typ_term k u t)
  | STTLam _ t => STTLam _ (open_rec_typ_term (S k) u t)
  | STTApp _ t ty => STTApp _ (open_rec_typ_term k u t) (open_rec_typ k u ty)
  end.

Fixpoint open_rec (k : nat) (u : SExp var) (t : SExp var) {struct t} : SExp var :=
  match t with
  | STBVar _ i => if Nat.eqb k i then u else (STBVar _ i)
  | STFVar _ x => STFVar _ x
  | STUnit _ => STUnit _
  | STLit _ x => STLit _ x
  | STLam _ t1 => STLam _ (open_rec (S k) u t1)    
  | STApp _ t1 t2 => STApp _ (open_rec k u t1) (open_rec k u t2)
  | STPair _ t1 t2 => STPair _ (open_rec k u t1) (open_rec k u t2)
  | STProj1 _ t => STProj1 _ (open_rec k u t)
  | STProj2 _ t => STProj2 _ (open_rec k u t)
  | STTLam _ t => STTLam _ (open_rec k u t)
  | STTApp _ t ty => STTApp _ (open_rec k u t) ty
  end.

Definition open (t : SExp var) u := open_rec 0 u t.
Definition open_typ (t : STyp) u := open_rec_typ 0 u t.
Definition open_typ_term (t : SExp var) u := open_rec_typ_term 0 u t.

Fixpoint subst (z : var) (u : SExp var) (t : SExp var) {struct t} : SExp var :=
  match t with
  | STBVar _ i     => STBVar _ i
  | STFVar _ x     => if VarTyp.eqb x z then u else (STFVar _ x)
  | STUnit _       => STUnit _
  | STLit _ n      => STLit _ n
  | STLam _ t      => STLam _ (subst z u t)
  | STApp _ t1 t2  => STApp _ (subst z u t1) (subst z u t2)
  | STPair _ t1 t2 => STPair _ (subst z u t1) (subst z u t2)
  | STProj1 _ t    => STProj1 _ (subst z u t)
  | STProj2 _ t    => STProj2 _ (subst z u t)
  | STTLam _ t     => STTLam _ (subst z u t)
  | STTApp _ t ty  => STTApp _ (subst z u t) ty
  end.

Fixpoint subst_typ (z : var) (u : STyp) (t : STyp) {struct t} : STyp :=
  match t with
  | STUnitT       => STUnitT
  | STInt         => STInt
  | STFun t1 t2   => STFun (subst_typ z u t1) (subst_typ z u t2)
  | STTuple t1 t2 => STTuple (subst_typ z u t1) (subst_typ z u t2)
  | STFVarT x     => if VarTyp.eqb x z then u else (STFVarT x)
  | STBVarT i     => STBVarT i
  | STForAll t    => STForAll (subst_typ z u t)
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).
Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^ x" := (open t (STFVar var x)).
Notation "t ^^ u" := (open t u) (at level 67).

Lemma fv_distr :
  forall t1 t2 x n, In x (fv (open_rec n t2 t1)) ->
               In x (union (fv t1) (fv t2)).
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
  - rewrite <- union_spec.
    apply (IHt1 _ _ H).
  - rewrite <- union_spec.
    apply (IHt1 _ _ H).
  - rewrite union_spec.
    inversion H.
    assert (Ha : In x (union (fv t1) (fv t2))).
    eapply IHt1. apply H0.
    rewrite union_spec in Ha.
    inversion Ha. auto. auto. auto.
Qed.

Lemma fv_open_rec_typ :
  forall t1 t2 x n, In x (fv_typ (open_rec_typ n t2 t1)) ->
               In x (union (fv_typ t1) (fv_typ t2)).
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
  - rewrite <- union_spec; eapply IHt1; apply H.
Qed.
    
Lemma fv_open_rec_typ_term :
  forall t1 t2 x n, In x (fv (open_rec_typ_term n t2 t1)) ->
               In x (union (fv t1) (fv_typ t2)).
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
  - apply (IHt1 _ _ H).
  - apply (IHt1 _ _ H).
  - rewrite union_spec in H.
    repeat rewrite union_spec.
    inversion H.
    apply IHt1 in H0; rewrite union_spec in H0; inversion H0; auto.
    apply fv_open_rec_typ in H0.
    rewrite union_spec in H0.
    inversion H0; auto.
Qed.

Inductive STType : STyp -> Prop :=
  | STType_Var : forall x, STType (STFVarT x)
  | STType_Unit : STType STUnitT
  | STType_Int : STType STInt
  | STType_Fun : forall t1 t2, STType t1 -> STType t2 -> STType (STFun t1 t2)
  | STType_Tuple : forall t1 t2, STType t1 -> STType t2 -> STType (STTuple t1 t2)
  | STType_ForAll : forall L t,
      (forall x, not (In x L) -> STType (open_typ t (STFVarT x))) ->
      STType (STForAll t).

Hint Constructors STType.

(* 
   Locally closed types and well-formed types (under an empty env.) are not isomorphic.
   For example, the type beta is locally closed but not well-formed.
   More concretely, the set of well-formed types is a subset of the locally closed set.
 *)

Inductive TyEnv (t : Type) : Type :=
  | TyVar : TyEnv t
  | TermVar : t -> TyEnv t.          

Inductive WFType : context (TyEnv STyp) -> STyp -> Prop :=
  | WFType_Var : forall x Gamma, ok Gamma -> List.In (x,TyVar _) Gamma -> WFType Gamma (STFVarT x)
  | WFType_Unit : forall Gamma, ok Gamma -> WFType Gamma STUnitT
  | WFType_Int : forall Gamma, ok Gamma -> WFType Gamma STInt
  | WFType_Fun : forall Gamma t1 t2, WFType Gamma t1 -> WFType Gamma t2 -> WFType Gamma (STFun t1 t2)
  | WFType_Tuple : forall Gamma t1 t2, WFType Gamma t1 -> WFType Gamma t2 -> WFType Gamma (STTuple t1 t2)
  | WFType_ForAll : forall L Gamma t,
      (forall x, not (In x L) -> WFType (extend x (TyVar _) Gamma) (open_typ t (STFVarT x))) ->
      WFType Gamma (STForAll t).

Hint Constructors WFType.

Inductive STTerm : SExp var -> Prop :=
  | STTerm_Var : forall x,
      STTerm (STFVar _ x)
  | STTerm_Unit : STTerm (STUnit _)
  | STTerm_Lit : forall n,
      STTerm (STLit _ n)
  | STTerm_Lam : forall L t1,
      (forall x, not (In x L) -> STTerm (open t1 (STFVar _ x))) ->
      STTerm (STLam _ t1)
  | STTerm_App : forall t1 t2,
      STTerm t1 -> 
      STTerm t2 -> 
      STTerm (STApp _ t1 t2)
  | STTerm_Pair : forall t1 t2,
      STTerm t1 ->
      STTerm t2 ->
      STTerm (STPair _ t1 t2)
  | STTerm_Proj1 : forall t,
      STTerm t ->
      STTerm (STProj1 _ t)
  | STTerm_Proj2 : forall t,
      STTerm t ->
      STTerm (STProj2 _ t)
  | STTerm_TLam : forall L t,
      (forall x, not (In x L) -> STTerm (open_typ_term t (STFVarT x))) ->
      STTerm (STTLam _ t)
  | STTerm_TApp : forall t ty,
      STTerm t ->
      STType ty ->
      STTerm (STTApp _ t ty).
      
Hint Constructors STTerm.

(* Tactics dealing with fresh variables, taken from STLC_Tutorial *)

Ltac gather_vars_with F :=
  let rec gather V :=
   (match goal with
    | H:?S
      |- _ =>
          let FH := constr:(F H) in
          match V with
          | empty => gather FH
          | context [FH] => fail 1
          | _ => gather (union FH V)
          end
    | _ => V
    end)
  in
  let L := gather (empty : vars) in
  eval simpl in L.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => singleton x) in
  (*let C := gather_vars_with (fun (x : context PTyp) => dom x) in *)
  let D := gather_vars_with (fun (x : context (TyEnv STyp)) => dom x) in
  let E := gather_vars_with (fun x : STyp => fv_typ x) in
  let F := gather_vars_with (fun (x : SExp var) => fv x) in
  constr:(union A (union B (union D (union E F )))).

Ltac beautify_fset V :=
  let rec go Acc E :=
   (match E with
    | union ?E1 ?E2 => let Acc1 := go Acc E1 in
                    go Acc1 E2
    | empty => Acc
    | ?E1 => match Acc with
             | empty => E1
             | _ => constr:(union Acc E1)
             end
    end)
  in
  go (empty : vars) V.

Parameter var_fresh : forall L : vars, (sig (A := var) (fun x => not (In x L))).
  
Ltac pick_fresh_gen L Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  destruct (var_fresh L) as (Y, Fr).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Ltac apply_fresh_base_simple lemma gather :=
  let L0 := gather in
  let L := beautify_fset L0 in
  first
  [ apply (lemma L) | eapply (lemma L) ].

Ltac intros_fresh x :=
  first
  [ let Fr := fresh "Fr" x in
    intros x Fr
  | let x2 :=
     (match goal with
      | |- ?T -> _ =>
            match T with
            | var => fresh "y"
            | vars => fresh "ys"
            | list var => fresh "ys"
            | _ => fresh "y"
            end
      end)
    in
    let Fr := fresh "Fr" x2 in
    intros x2 Fr ]. 

Fixpoint fresh (L : vars) (n : nat) (xs : list var) : Prop :=
  match xs with
  | nil => match n with
           | 0 => True
           | S _ => False
           end
  | (x :: xs')%list =>
      match n with
      | 0 => False
      | S n' => (not (In x L)) /\ fresh (union L (singleton x)) n' xs'
      end
  end.

Ltac apply_fresh_base lemma gather var_name :=
  apply_fresh_base_simple lemma gather;
   try
    match goal with
    | |- _ -> not (In _ _) -> _ => intros_fresh var_name
    | |- _ -> fresh _ _ _ -> _ => intros_fresh var_name
    end.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

(* Lemmas on types *)
Lemma open_rec_typ_core :forall t j v i u, i <> j ->
  open_rec_typ j v t = open_rec_typ i u (open_rec_typ j v t) -> t = open_rec_typ i u t.
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
    erewrite <- IHt.
    reflexivity.
    apply not_eq_S.
    apply H.
    apply H2.
Qed.

Lemma open_rec_type : forall t u,
  STType  t -> forall k, t =  open_rec_typ k u t.
Proof.
  intros t u H.
  induction H; intros; simpl; auto.
  - rewrite <- IHSTType1; rewrite <- IHSTType2; reflexivity.
  - rewrite <- IHSTType1; rewrite <- IHSTType2; reflexivity.
  - pick_fresh x.
    assert (Ha : not (In x L)) by not_in_L x.
    apply H0 with (k := S k) in Ha.
    apply open_rec_typ_core in Ha.
    rewrite <- Ha.
    reflexivity.
    auto.
Qed.
    
Lemma open_rec_term_core :forall t j v i u, i <> j ->
  { j ~> v }t = { i ~> u }({ j ~> v }t) -> t = { i ~> u }t.
Proof.
  intro t; induction t; intros; simpl; auto.
  - simpl in *.
    case_eq (Nat.eqb i n); intros.
    case_eq (Nat.eqb j n); intros.
    exfalso. apply H. apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in H2. rewrite H1, H2.
    reflexivity.
    rewrite H2 in H0.
    unfold open_rec in H0.
    rewrite H1 in H0.
    assumption.
    reflexivity.
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
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply H.
    apply H2.
  - inversion H0; erewrite <- IHt; [ reflexivity | apply H | apply H2 ].
  - inversion H0; erewrite <- IHt; [ reflexivity | apply H | apply H2 ].    
Qed.

Lemma open_rec_type_term_core :forall t j v i u,
  open_rec_typ_term j v t = { i ~> u }(open_rec_typ_term j v t) -> t = { i ~> u }t.
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
Qed.
  
(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_term : forall t u,
  STTerm  t -> forall k, t =  { k ~> u }t.
Proof.
  intros.
  generalize dependent k.
  induction H; intros; auto.
  - pick_fresh x.
    simpl.
    apply f_equal.
    erewrite <- open_rec_term_core with (j := 0) (v := STFVar _ x).
    reflexivity.
    auto.
    unfold open in H0.
    apply H0.    
    not_in_L x.
  - simpl; rewrite <- IHSTTerm1; rewrite <- IHSTTerm2; reflexivity.
  - simpl; rewrite <- IHSTTerm1; rewrite <- IHSTTerm2; reflexivity.
  - simpl; rewrite <- IHSTTerm; reflexivity.
  - simpl; rewrite <- IHSTTerm; reflexivity.
  - pick_fresh x.
    assert (Ha : not (In x L)) by not_in_L x.
    apply H0 with (k := k) in Ha.
    simpl; apply f_equal.
    now apply open_rec_type_term_core in Ha.
  - simpl; rewrite <- IHSTTerm; reflexivity.
Qed.

Hint Resolve open_rec_term.

Lemma open_rec_type_term_core2 :
  forall (t : SExp var) (j : nat) (v : STyp) (i : nat) (u : SExp var),
  open_rec_typ_term j v t = open_rec_typ_term j v ({i ~> u} t) ->
  t = {i ~> u} t.
Proof.
  intro t; induction t; intros; simpl in *; auto.
  - destruct (i =? n).
    destruct u; simpl in *; auto; now inversion H.
    reflexivity.
  - inversion H; apply IHt in H1; now rewrite <- H1.
  - inversion H; apply IHt1 in H1; apply IHt2 in H2; rewrite <- H1; rewrite <- H2;
    reflexivity.
  - inversion H; apply IHt1 in H1; apply IHt2 in H2; rewrite <- H1; rewrite <- H2;
    reflexivity.
  - inversion H; apply IHt in H1; now rewrite <- H1.
  - inversion H; apply IHt in H1; now rewrite <- H1.
  - inversion H; apply IHt in H1; now rewrite <- H1.
  - inversion H; apply IHt in H1; now rewrite <- H1.
Qed.

Lemma open_rec_type_term_core3 :
  forall t n m u x,
    {m ~> STFVar elt x} t = open_rec_typ_term n u ({m ~> STFVar elt x} t) ->
    t = open_rec_typ_term n u t.
Proof.
  intro t; induction t; intros; simpl in *; auto.
  - inversion H; apply IHt in H1; rewrite <- H1; auto.
  - inversion H; apply IHt1 in H1; apply IHt2 in H2;
    rewrite <- H1; rewrite <- H2; auto.
  - inversion H; apply IHt1 in H1; apply IHt2 in H2;
    rewrite <- H1; rewrite <- H2; auto.
  - inversion H; apply IHt in H1; rewrite <- H1; auto.
  - inversion H; apply IHt in H1; rewrite <- H1; auto.
  - inversion H; apply IHt in H1; rewrite <- H1; auto.
  - inversion H; apply IHt in H1; rewrite <- H1; rewrite <- H2; rewrite <- H2; auto.
Qed.

Lemma open_rec_typ_term_core4 : forall t j v i u, i <> j ->
  open_rec_typ_term j v t = open_rec_typ_term i u (open_rec_typ_term j v t) ->
  t = open_rec_typ_term i u t.
Proof.
  intro t; induction t; intros; simpl; auto.
  - simpl in H0; inversion H0.
    erewrite <- IHt; eauto.
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
  - simpl in H0; inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply H.
    apply H2.
  - simpl in H0; inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply H.
    apply H2.
  - simpl in H0; inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply not_eq_S.
    apply H.
    apply H2.
  - simpl in H0; inversion H0.
    erewrite <- IHt.
    apply open_rec_typ_core in H3.
    now rewrite <- H3.
    auto.
    apply H.
    apply H2.
Qed.

Lemma open_rec_typ_term_term :
  forall t u, STTerm t -> forall k, t = open_rec_typ_term k u t.
Proof.
  intros t u HT.
  induction HT; intros; simpl; auto.
  - unfold open in *.
    pick_fresh x.
    assert (Ha : ~ In x L) by not_in_L x.
    apply H0 with (k := k) in Ha.
    apply open_rec_type_term_core3 in Ha.
    now rewrite <- Ha.
  - rewrite <- IHHT1; rewrite <- IHHT2; auto.
  - rewrite <- IHHT1; rewrite <- IHHT2; auto.
  - rewrite <- IHHT; auto.
  - rewrite <- IHHT; auto.
  - pick_fresh x.
    assert (Ha : ~ In x L) by not_in_L x.
    apply H0 with (k := S k) in Ha.
    unfold open_typ_term in *.
    apply open_rec_typ_term_core4 in Ha.
    now rewrite <- Ha.
    auto.
  - rewrite <- IHHT; auto.
    rewrite <- open_rec_type; auto.
Qed.
 
Definition body_typ_term t :=
  exists L, forall x, ~ In x L -> STTerm (open_typ_term t (STFVarT x)).

Lemma term_abs_to_body_typ_term : forall t1, 
  STTerm (STTLam _ t1) -> body_typ_term t1.
Proof. intros. unfold body_typ_term. inversion H; subst. eauto. Qed.

Lemma body_typ_term_to_term_abs : forall t1, 
  body_typ_term t1 -> STTerm (STTLam _ t1).
Proof. intros. inversion H. eapply STTerm_TLam. apply H0. Qed.


Lemma open_app_eq : forall x E n F,
  not (In x (fv E)) ->
  not (In x (fv F)) ->
  (open_rec n (STFVar var x) E) = (open_rec n (STFVar var x) F) ->
  E = F.
Proof.
  intros x E.
  induction E; intros n' F HNotE HNotF HEqOpen.
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
    destruct (Nat.eqb n' n); auto.
    exfalso; apply HNotE.
    apply MSetProperties.Dec.F.singleton_2; inversion H0; reflexivity.
  - induction F; simpl in *; try (now (destruct (Nat.eqb n' n); inversion HEqOpen)).
    destruct (Nat.eqb n' n).
    exfalso; apply HNotF.
    apply MSetProperties.Dec.F.singleton_2; inversion HEqOpen; reflexivity. 
    inversion HEqOpen.
    case_eq (Nat.eqb n' n); intros.
    case_eq (Nat.eqb n' n0); intros.
    apply f_equal.
    apply beq_nat_true in H.
    apply beq_nat_true in H0.
    now subst.
    rewrite H in HEqOpen.
    rewrite H0 in HEqOpen.
    inversion HEqOpen.
    rewrite H in HEqOpen.
    case_eq (Nat.eqb n' n0); intros;
    rewrite H0 in HEqOpen; inversion HEqOpen.
    reflexivity.
  - induction F; simpl in *; try (now inversion HEqOpen).
    destruct (Nat.eqb n' n); [ inversion HEqOpen | auto ].
  - induction F; simpl in *; try (now inversion HEqOpen).
    destruct (Nat.eqb n' n0); [ inversion HEqOpen | auto ].
  - induction F; simpl in *; try (now inversion HEqOpen).
    destruct (Nat.eqb n' n); inversion HEqOpen.
    inversion HEqOpen.
    apply f_equal.
    now apply (IHE (S n')).
  - induction F; simpl in *; try (now inversion HEqOpen).  
    destruct (Nat.eqb n' n); inversion HEqOpen.
    rewrite IHE1 with (F := F1) (n := n'); try not_in_L x.
    rewrite IHE2 with (F := F2) (n := n'); try not_in_L x.
    reflexivity.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
  - induction F; simpl in *; try (now inversion HEqOpen).  
    destruct (Nat.eqb n' n); inversion HEqOpen.
    rewrite IHE1 with (F := F1) (n := n'); try not_in_L x.
    rewrite IHE2 with (F := F2) (n := n'); try not_in_L x.
    reflexivity.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
  - induction F; simpl in *; try (now inversion HEqOpen).  
    destruct (Nat.eqb n' n); inversion HEqOpen.
    apply f_equal.
    apply IHE with (n := n'); try not_in_L x.
    now inversion HEqOpen.
  - induction F; simpl in *; try (now inversion HEqOpen).  
    destruct (Nat.eqb n' n); inversion HEqOpen.
    apply f_equal.
    apply IHE with (n := n'); try not_in_L x.
    now inversion HEqOpen. 
  - induction F; simpl in *; try (now inversion HEqOpen).  
    destruct (Nat.eqb n' n); inversion HEqOpen.
    apply f_equal.
    apply IHE with (n := n'); try not_in_L x.
    now inversion HEqOpen.
  - induction F; simpl in *; try (now inversion HEqOpen).  
    destruct (Nat.eqb n' n); inversion HEqOpen.
    erewrite IHE.
    apply f_equal.
    now inversion HEqOpen.
    not_in_L x.
    not_in_L x.
    inversion HEqOpen.
    apply H0.
Qed.

Lemma open_typ_app_eq : forall x E n F,
  not (In x (fv_typ E)) ->
  not (In x (fv_typ F)) ->
  (open_rec_typ n (STFVarT x) E) = (open_rec_typ n (STFVarT x) F) ->
  E = F.
Proof.
  intros x E.
  induction E; intros n' F HNotE HNotF HEqOpen.
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
    destruct (Nat.eqb n' n); auto.
    inversion H0.
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
    destruct (Nat.eqb n' n); auto.
    inversion H0.
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
    rewrite IHE1 with (F := F1) (n := n'); try not_in_L x.
    rewrite IHE2 with (F := F2) (n := n'); try not_in_L x.
    reflexivity.
    simpl; rewrite union_spec; auto.
    auto.
    simpl; rewrite union_spec; auto.
    auto.
    destruct (Nat.eqb n' n); inversion H0.
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
    rewrite IHE1 with (F := F1) (n := n'); try not_in_L x.
    rewrite IHE2 with (F := F2) (n := n'); try not_in_L x.
    reflexivity.
    simpl; rewrite union_spec; auto.
    auto.
    simpl; rewrite union_spec; auto.
    auto.
    destruct (Nat.eqb n' n); inversion H0.
  - induction F; simpl in *; try (now (inversion HEqOpen)).
    destruct (Nat.eqb n' n).
    exfalso; apply HNotE.
    apply MSetProperties.Dec.F.singleton_2; inversion HEqOpen; reflexivity. 
    inversion HEqOpen.
  - induction F; simpl in *; try (now (destruct (Nat.eqb n' n); inversion HEqOpen)).
    destruct (Nat.eqb n' n).
    exfalso; apply HNotF.
    apply MSetProperties.Dec.F.singleton_2; inversion HEqOpen; reflexivity. 
    inversion HEqOpen.
    case_eq (Nat.eqb n' n); intros.
    case_eq (Nat.eqb n' n0); intros.
    apply f_equal.
    apply beq_nat_true in H.
    apply beq_nat_true in H0.
    now subst.
    rewrite H in HEqOpen.
    rewrite H0 in HEqOpen.
    inversion HEqOpen.
    rewrite H in HEqOpen.
    case_eq (Nat.eqb n' n0); intros;
    rewrite H0 in HEqOpen; inversion HEqOpen.
    reflexivity.
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
    destruct (Nat.eqb n' n); auto.
    inversion H0.
    inversion H0.
    erewrite IHE.
    reflexivity.
    auto.
    auto.
    apply H0.
Qed.    
    
Lemma open_typ_term_app_eq : forall x E n F,
  not (In x (fv E)) ->
  not (In x (fv F)) ->
  (open_rec_typ_term n (STFVarT x) E) = (open_rec_typ_term n (STFVarT x) F) ->
  E = F.
Proof.
  intros x E.
  induction E; intros n' F HNotE HNotF HEqOpen.
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
  - simpl in *.
    induction F; try (inversion HEqOpen; auto).
    erewrite IHE.
    reflexivity.
    not_in_L x.
    not_in_L x.
    apply H0.
  - destruct F; simpl in *; try (now inversion HEqOpen).  
    erewrite IHE1 with (F := F1) (n := n').
    erewrite IHE2 with (F := F2) (n := n').
    auto.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
  - destruct F; simpl in *; try (now inversion HEqOpen).  
    erewrite IHE1 with (F := F1) (n := n').
    erewrite IHE2 with (F := F2) (n := n').
    auto.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
  - destruct F; simpl in *; try (now inversion HEqOpen).  
    erewrite IHE with (F := F) (n := n').
    auto.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
  - destruct F; simpl in *; try (now inversion HEqOpen).  
    erewrite IHE with (F := F) (n := n').
    auto.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
  - destruct F; simpl in *; try (now inversion HEqOpen).  
    erewrite IHE with (F := F) (n := (S n')).
    auto.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
  - destruct F; simpl in *; try (now inversion HEqOpen).  
    erewrite IHE with (F := F) (n := n').
    inversion HEqOpen.
    apply open_typ_app_eq in H1.
    now subst.
    not_in_L x.
    not_in_L x.
    not_in_L x.
    not_in_L x.
    now inversion HEqOpen.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  not (In x (fv t)) ->  [x ~> u] t = t.
Proof.
  intros; induction t0; simpl in *; auto.
  - case_eq (eqb a x); intros.
    exfalso; apply H; simpl; apply MSetProperties.Dec.F.singleton_2;
    now apply eqb_eq in H0.
    auto.
  - rewrite IHt0; auto.
  - rewrite IHt0_1; [ rewrite IHt0_2 | not_in_L x ]; [ reflexivity | not_in_L x ].
  - rewrite IHt0_1; [ rewrite IHt0_2 | not_in_L x ]; [ reflexivity | not_in_L x ].
  - rewrite IHt0; [ reflexivity | not_in_L x ].
  - rewrite IHt0; [ reflexivity | not_in_L x ].
  - rewrite IHt0; [ reflexivity | not_in_L x ].
  - rewrite IHt0; [ reflexivity | not_in_L x ].
Qed.

Lemma subst_typ_fresh : forall x t u, 
  not (In x (fv_typ t)) -> subst_typ x u t = t.
Proof.
  intros; induction t0; simpl in *; auto.
  - rewrite IHt0_1; [ rewrite IHt0_2 | not_in_L x ]; [ reflexivity | not_in_L x ].
  - rewrite IHt0_1; [ rewrite IHt0_2 | not_in_L x ]; [ reflexivity | not_in_L x ].
  - case_eq (eqb v x); intros.
    exfalso; apply H; simpl; apply MSetProperties.Dec.F.singleton_2;
    now apply eqb_eq in H0.
    auto.
  - rewrite IHt0; auto.
Qed.
    
(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, STTerm u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; auto; try (apply f_equal; auto).
  - case_eq (eqb a x); intros; [ rewrite <- open_rec_term | ]; auto.
  - case_eq (Nat.eqb n0 n); intros; auto.
  - rewrite IHt1_1; rewrite IHt1_2; auto.
  - rewrite IHt1_1; rewrite IHt1_2; auto.
  - rewrite IHt1; auto.
Qed.

Lemma subst_typ_open : forall x u t1 t2, STType u -> 
  subst_typ x u (open_typ t1 t2) = open_typ (subst_typ x u t1) (subst_typ x u t2).
Proof.
  intros. unfold open_typ. generalize 0.
  induction t1; intros; simpl; auto; try (apply f_equal; auto).
  - rewrite IHt1_1; rewrite IHt1_2; auto.
  - rewrite IHt1_1; rewrite IHt1_2; auto.
  - case_eq (eqb v x); intros; [ rewrite <- open_rec_type | ]; auto.
  - case_eq (Nat.eqb n0 n); intros; auto.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall x y u t, y <> x -> STTerm u ->
  ([x ~> u]t) ^ y = [x ~> u] (t ^ y).
Proof.
  intros x y u t Neq Wu. rewrite subst_open; auto; simpl.
  case_eq (VarTyp.eqb y x); intros; auto.
  exfalso; apply Neq.
  now apply eqb_eq in H.
Qed.
  
Lemma subst_typ_open_var : forall x y u t, y <> x -> STType u ->
  open_typ (subst_typ x u t) (STFVarT y) = subst_typ x u (open_typ t (STFVarT y)).
Proof.
  intros Neq Wu. intros. rewrite subst_typ_open; auto. simpl.
  case_eq (VarTyp.eqb Wu Neq); intros; auto.
  exfalso; apply H.
  now apply eqb_eq in H1.
Qed.

(** Opening up an abstraction of body [t] with a term [u] is the same as opening
  up the abstraction with a fresh name [x] and then substituting [u] for [x]. *)

Lemma subst_intro : forall x t u, 
  not (In x (fv t)) -> STTerm u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  intros Fr Wu.
  intros.
  rewrite subst_open.
  rewrite subst_fresh.
  simpl.
  case_eq (eqb Fr Fr); intros; auto.
  apply EqFacts.eqb_neq in H1; exfalso; apply H1; reflexivity.
  auto. auto.
Qed.  

Lemma subst_typ_intro : forall x t u, 
  not (In x (fv_typ t)) -> STType u ->
  open_typ t u = subst_typ x u (open_typ t (STFVarT x)).
Proof.
  intros Fr Wu.
  intros.
  rewrite subst_typ_open.
  rewrite subst_typ_fresh.
  simpl.
  case_eq (eqb Fr Fr); intros; auto.
  apply EqFacts.eqb_neq in H1; exfalso; apply H1; reflexivity.
  auto. auto.
Qed.  

(* Typing rules *)

(* Typing rules of STLC, inspired by STLC_Tutorial *)
Inductive has_type_st : (context (TyEnv STyp)) -> (SExp var) -> STyp -> Prop :=
  | STTyVar : forall Gamma x ty, WFType Gamma ty ->
                ok Gamma -> List.In (x,TermVar _ ty) Gamma -> has_type_st Gamma (STFVar _ x) ty
  | STTyUnit : forall Gamma, ok Gamma -> has_type_st Gamma (STUnit _) STUnitT
  | STTyLit : forall Gamma x, ok Gamma -> has_type_st Gamma (STLit _ x) STInt       
  | STTyLam : forall L Gamma t A B,
                (forall x, not (In x L) -> 
                      has_type_st (extend x (TermVar _ A) Gamma) (open t (STFVar _ x)) B) ->
                WFType Gamma A ->
                has_type_st Gamma (STLam _ t) (STFun A B)
  | STTyApp : forall Gamma A B t1 t2, has_type_st Gamma t1 (STFun A B) ->
                             has_type_st Gamma t2 A -> has_type_st Gamma (STApp _ t1 t2) B
  | STTyPair : forall Gamma A B t1 t2, has_type_st Gamma t1 A ->
                              has_type_st Gamma t2 B ->
                              has_type_st Gamma (STPair _ t1 t2) (STTuple A B)
  | STTyProj1 : forall Gamma t A B, has_type_st Gamma t (STTuple A B) ->
                           has_type_st Gamma (STProj1 _ t) A
  | STTyProj2 : forall Gamma t A B, has_type_st Gamma t (STTuple A B) ->
                           has_type_st Gamma (STProj2 _ t) B
  | STTyTLam : forall L Gamma t A,
                 (forall x, not (In x L) ->
                       has_type_st (extend x (TyVar _) Gamma)
                                   (open_typ_term t (STFVarT x))
                                   (open_typ A (STFVarT x))) ->
                 has_type_st Gamma (STTLam _ t) (STForAll A) 
  | STTyTApp : forall Gamma t A ty, WFType Gamma A ->
                           has_type_st Gamma t (STForAll ty) ->
                           has_type_st Gamma (STTApp _ t A) (open_typ ty A).
                            
Hint Constructors has_type_st.

(* WF lemmas *)

Lemma wf_weaken : forall G E F ty,
   WFType (E ++ G) ty -> 
   ok (E ++ F ++ G) ->
   WFType (E ++ F ++ G) ty.
Proof.
  intros.
  generalize dependent H0.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent E.
  dependent induction H; intros; eauto.  
  (* Var *)
  - subst.
    apply WFType_Var.
    assumption.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app; left; assumption.
    apply in_or_app; right; apply in_or_app; right; assumption.  
  (* ForAll *)
  - apply_fresh WFType_ForAll as x.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    apply H0.
    not_in_L x.
    unfold extend; simpl; reflexivity.
    rewrite <- app_comm_cons.
    apply Ok_push.
    assumption.
    not_in_L x.
    rewrite dom_union in H6.
    rewrite union_spec in H6.
    inversion H6; contradiction. 
Qed.    

Lemma wf_strengthen : forall z U E F ty,
  not (In z (fv_typ ty)) ->
  WFType (E ++ ((z,U) :: nil) ++ F) ty ->
  WFType (E ++ F) ty.
Proof.
  intros.
  remember (E ++ ((z,U) :: nil) ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; auto.
  - subst; apply WFType_Var.
    now apply ok_remove in H0.
    apply in_or_app.
    repeat apply in_app_or in H1.
    inversion H1.
    auto.
    apply in_app_or in H2.
    inversion H2.
    inversion H3.
    inversion H4.
    subst.
    exfalso; apply H; simpl.
    left; reflexivity.
    inversion H4.
    auto.
  - apply WFType_Unit.
    subst.
    now apply ok_remove in H0.
  - apply WFType_Int.
    subst.
    now apply ok_remove in H0.
  - eapply WFType_Fun.
    subst.
    apply IHWFType1; simpl in *; not_in_L z; reflexivity.
    subst.
    apply IHWFType2; simpl in *; not_in_L z; reflexivity.
  - eapply WFType_Tuple.
    subst.
    apply IHWFType1; simpl in *; not_in_L z; reflexivity.
    subst.
    apply IHWFType2; simpl in *; not_in_L z; reflexivity.
  - subst.
    apply_fresh WFType_ForAll as x.
    unfold extend in *; simpl in *.
    rewrite app_comm_cons.
    apply H1.
    not_in_L x.
    not_in_L z.
    apply fv_open_rec_typ in H2.
    rewrite union_spec in H2.
    inversion H2.
    auto.
    assert (NeqXZ : not (In x (singleton z))) by (not_in_L x).
    simpl in H3.
    exfalso; apply NeqXZ.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in H3.
    symmetry; assumption.
    rewrite app_comm_cons.
    reflexivity.
Qed.

Lemma wf_env_comm : forall E F G H ty,
              WFType (E ++ F ++ G ++ H) ty ->
              WFType (E ++ G ++ F ++ H) ty.
Proof.
  intros.
  remember (E ++ F ++ G ++ H).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  generalize dependent G.
  dependent induction H0; intros; subst; auto.
  - apply WFType_Var.
    apply ok_app_comm.
    rewrite <- app_assoc.
    apply ok_app_comm.
    rewrite <- app_assoc.
    apply ok_app_comm.
    rewrite <- app_assoc.
    now apply ok_middle_comm.
    apply in_app_or in H1.
    inversion H1.
    apply in_or_app; auto.
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
  - apply WFType_Unit.
    now apply ok_middle_comm.
  - apply WFType_Int.
    now apply ok_middle_comm.
  - apply_fresh WFType_ForAll as x.
    unfold extend.
    rewrite app_assoc.
    apply H1.
    not_in_L x.
    unfold extend.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma wf_env_comm_extend : forall Gamma x y v1 v2 ty,
              WFType (extend x v1 (extend y v2 Gamma)) ty ->
              WFType (extend y v2 (extend x v1 Gamma)) ty.
Proof.
  unfold extend.
  intros.
  rewrite <- app_nil_l with (l := ((x, v1) :: nil) ++ ((y, v2) :: nil) ++ Gamma) in H.
  apply wf_env_comm in H.
  now rewrite app_nil_l in H.
Qed.  

Lemma wf_weaken_extend : forall ty x v Gamma,
   WFType Gamma ty ->
   not (M.In x (dom Gamma)) ->                            
   WFType ((x,v) :: Gamma) ty.
Proof.
  intros.
  induction H; eauto.
  - apply WFType_Var.
    apply Ok_push; assumption.
    apply in_cons; assumption.
  - apply WFType_Unit.
    apply Ok_push; assumption.
  - apply WFType_Int.
    apply Ok_push; assumption.
  - apply_fresh WFType_ForAll as x; cbn.
    unfold extend in H1.
    apply wf_env_comm_extend.
    apply H1.
    not_in_L y.
    not_in_L x.
    not_in_L y.
Qed.

Lemma wf_gives_types : forall Gamma ty, WFType Gamma ty -> STType ty.
Proof.
  intros.
  induction H; auto.
  - apply_fresh STType_ForAll as x.
    apply H0.
    not_in_L x.
Qed.

Lemma wf_gives_ok_env : forall Gamma ty, WFType Gamma ty -> ok Gamma.
Proof.
  induction 1; auto.
  pick_fresh x; assert (Ha : not (In x L)) by not_in_L x.
  apply H0 in Ha; unfold extend in Ha; apply ok_app_and in Ha.
  destruct Ha; auto.
Qed.
  
Hint Resolve wf_weaken wf_strengthen wf_weaken_extend wf_gives_types.

(* Typing lemmas *)

Lemma typing_weaken : forall G E F t T,
   has_type_st (E ++ G) t T -> 
   ok (E ++ F ++ G) ->
   has_type_st (E ++ F ++ G) t T.
Proof.
  intros.
  generalize dependent H0.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent E.
  dependent induction H; intros; eauto.
  (* STTyVar *)
  - subst.
    apply STTyVar; auto.
    apply in_app_or in H1.
    inversion H1.
    apply in_or_app; left; assumption.
    apply in_or_app; right; apply in_or_app; right; assumption.
  (* STTyLam *)
  - apply_fresh STTyLam as x.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    apply H0.
    not_in_L x.
    unfold extend; simpl; reflexivity.
    rewrite <- app_comm_cons.
    apply Ok_push.
    assumption.
    not_in_L x.
    rewrite dom_union in H9.
    rewrite union_spec in H9.
    inversion H9; contradiction.
    subst; apply wf_weaken; auto.
  (* STTyTLam *)
  - apply_fresh STTyTLam as x.
    intros.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    eapply H0.
    not_in_L x.
    unfold extend; simpl; reflexivity.
    rewrite <- app_comm_cons.
    apply Ok_push.
    assumption.
    not_in_L x.
    rewrite dom_union in H7.
    rewrite union_spec in H7.
    inversion H7; contradiction.
  (* STTyTApp *)
  - subst; apply STTyTApp; auto.
Qed. 
    
(*
Lemma typing_strengthen : forall z U E F t T,
  not (In z (fv t)) ->
  has_type_st (E ++ ((z,U) :: nil) ++ F) t T ->
  has_type_st (E ++ F) t T.
Proof.
  intros.
  remember (E ++ ((z,U) :: nil) ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; auto.
  - subst; apply STTyVar; auto.
    eapply wf_strengthen.
    eauto.
    now apply ok_remove in H0.
    apply in_or_app.
    repeat apply in_app_or in H1.
    inversion H1.
    auto.
    apply in_app_or in H2.
    inversion H2.
    inversion H3.
    inversion H4.
    subst.
    exfalso; apply H; simpl.
    left; reflexivity.
    inversion H4.
    auto.
  - apply STTyUnit.
    subst.
    now apply ok_remove in H0.
  - apply STTyLit.
    subst.
    now apply ok_remove in H0.
  - subst.
    apply_fresh STTyLam as x.
    unfold extend in *; simpl in *.
    rewrite app_comm_cons.
    apply H1.
    not_in_L x.
    not_in_L z.
    apply fv_distr in H2.
    rewrite union_spec in H2.
    inversion H2.
    auto.
    assert (NeqXZ : not (In x (singleton z))) by (not_in_L x).
    simpl in H3.
    exfalso; apply NeqXZ.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in H3.
    symmetry; assumption.
    rewrite app_comm_cons.
    reflexivity.
  - eapply STTyApp.
    subst.
    apply IHhas_type_st1; simpl in *; not_in_L z; reflexivity.
    subst.
    apply IHhas_type_st2; simpl in *; not_in_L z; reflexivity.
  - subst.
    apply STTyPair.
    apply IHhas_type_st1; simpl in *; not_in_L z; reflexivity.
    apply IHhas_type_st2; simpl in *; not_in_L z; reflexivity.
  - subst.
    eapply STTyProj1.
    apply IHhas_type_st.
    not_in_L z.
    reflexivity.
  - subst.
    eapply STTyProj2.
    apply IHhas_type_st.
    not_in_L z.
    reflexivity.
  - subst.
    apply_fresh STTyTLam as x.
    intros.
    unfold extend in *; simpl in *.
    rewrite app_comm_cons.
    apply H1.
    not_in_L x.
    unfold not; intros HH.
    apply fv_open_rec_typ_term in HH.
    not_in_L x.
    rewrite union_spec in HH; destruct HH as [ HH | HH ].
    contradiction.
    simpl in HH.
    apply H8.
    apply MSetProperties.Dec.F.singleton_1 in HH.
    apply MSetProperties.Dec.F.singleton_2.
    symmetry; auto.
    rewrite app_comm_cons.
    reflexivity.
  - subst.
    eapply STTyTApp.
    simpl in H.
    eapply wf_strengthen with (z := z).
    not_in_L z.
    apply H0.
    apply IHhas_type_st.
    not_in_L z.
    simpl; rewrite union_spec; auto.
    reflexivity.
Qed.
*)

Lemma has_type_env_comm : forall E F G H T t,
              has_type_st (E ++ F ++ G ++ H) t T ->
              has_type_st (E ++ G ++ F ++ H) t T.
Proof.
  intros.
  remember (E ++ F ++ G ++ H).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  generalize dependent G.
  dependent induction H0; intros; subst; auto.
  - apply STTyVar.
    now apply wf_env_comm.
    apply ok_app_comm.
    rewrite <- app_assoc.
    apply ok_app_comm.
    rewrite <- app_assoc.
    apply ok_app_comm.
    rewrite <- app_assoc.
    now apply ok_middle_comm.
    apply in_app_or in H2.
    inversion H2.
    apply in_or_app; auto.
    apply in_or_app; right.
    apply in_app_or in H3.
    inversion H3.
    apply in_or_app.
    right; apply in_or_app; left.
    assumption.
    apply in_app_or in H4.
    inversion H4.
    apply in_or_app; auto.
    apply in_or_app; right; apply in_or_app; auto.
  - apply STTyUnit.
    now apply ok_middle_comm.
  - apply STTyLit.
    now apply ok_middle_comm.
  - apply_fresh STTyLam as x.
    unfold extend.
    rewrite app_assoc.
    apply H1.
    not_in_L x.
    unfold extend.
    rewrite <- app_assoc.
    reflexivity.
    now apply wf_env_comm.
  - eapply STTyApp.
    apply IHhas_type_st1; reflexivity.
    apply IHhas_type_st2; reflexivity.
  - eapply STTyProj1; apply IHhas_type_st; reflexivity.
  - eapply STTyProj2; apply IHhas_type_st; reflexivity.
  - apply_fresh STTyTLam as x.
    unfold extend.
    rewrite app_assoc.
    apply H1.
    not_in_L x.
    unfold extend.
    rewrite <- app_assoc.
    reflexivity.
  - apply STTyTApp.
    apply wf_env_comm; auto.
    apply IHhas_type_st.
    reflexivity. 
Qed.
    
Lemma has_type_env_comm_extend : forall Gamma x y v1 v2 E t,
              has_type_st (extend x v1 (extend y v2 Gamma)) t E ->
              has_type_st (extend y v2 (extend x v1 Gamma)) t E.
Proof.
  unfold extend.
  intros.
  rewrite <- app_nil_l with (l := ((x, v1) :: nil) ++ ((y, v2) :: nil) ++ Gamma) in H.
  apply has_type_env_comm in H.
  now rewrite app_nil_l in H.
Qed.  

Lemma typing_weaken_extend : forall t T x v Gamma,
   has_type_st Gamma t T ->
   not (M.In x (dom Gamma)) ->                            
   has_type_st ((x,v) :: Gamma) t T.
Proof.
  intros.
  induction H; eauto.
  - apply STTyVar.
    now apply wf_weaken_extend.
    apply Ok_push; assumption.
    apply in_cons; assumption.
  - apply STTyUnit.
    apply Ok_push; assumption.
  - apply STTyLit.
    apply Ok_push; assumption.
  - apply_fresh STTyLam as x; cbn.
    unfold extend in H1.
    apply has_type_env_comm_extend.
    apply H1.
    not_in_L y.
    not_in_L x.
    not_in_L y.
    now apply wf_weaken_extend.
  - apply_fresh STTyTLam as x; cbn.
    apply has_type_env_comm_extend.
    apply H1.
    not_in_L y.
    not_in_L x.
    unfold extend in H2; simpl in H2.
    apply MSetProperties.FM.add_iff in H2; destruct H2.
    not_in_L y.
    assumption.
Qed.

Lemma typing_ok_env : forall Gamma E ty, has_type_st Gamma E ty -> ok Gamma.
Proof.
  intros.
  induction H; auto;
  pick_fresh x;
  assert (Ha: not (In x L)) by not_in_L x;
  pose (H0 _ Ha) as HInv;
  inversion HInv; auto.
Qed.


(* ****** *)

(* Inspired by STLC_Tutorial *)

(** The goal of this section is to set up the appropriate lemmas 
    for proving goals of the form [STType t] and [WFType Gamma t]. First, we defined a
    predicate capturing that a type [t] is the body of a locally
    closed abstraction. *)

(* TODO
   It is only necessary to prove WFType Gamma t, as STType t follows from it 
   (i.e. using wf_gives_types).
*)

Definition body_type t :=
  exists L, forall x, not (In x L) -> STType (open_typ t (STFVarT x)).

Definition body_wf_type t Gamma :=
  exists L, forall x, not (In x L) -> ok (extend x (TyVar _) Gamma) ->
            WFType (extend x (TyVar _) Gamma) (open_typ t (STFVarT x)).

(** We then show how to introduce and eliminate [body t]. *)

Lemma forall_to_body_type : forall t1, 
  STType (STForAll t1) -> body_type t1.
Proof. intros. unfold body_type. inversion H. subst. eauto. Qed.

Lemma body_type_to_forall : forall t1, 
  body_type t1 -> STType (STForAll t1).
Proof. intros. inversion H. apply_fresh STType_ForAll as x. apply H0. not_in_L y. Qed.

Lemma forall_to_body_wf_type : forall t1 Gamma, 
  WFType Gamma (STForAll t1) -> body_wf_type t1 Gamma.
Proof. intros. unfold body_wf_type. inversion H. subst. eauto. Qed.

Lemma body_wf_type_to_forall : forall t1, 
  body_type t1 -> STType (STForAll t1).
Proof. intros. inversion H. apply_fresh STType_ForAll as x. apply H0. not_in_L y. Qed.

Hint Resolve forall_to_body_type body_type_to_forall.
Hint Resolve forall_to_body_wf_type body_wf_type_to_forall.

(** We prove that terms are stable by substitution *)

Lemma subst_type : forall t z u,
  STType u -> STType t -> STType (subst_typ z u t).
Proof.
  induction 2; simpl; auto.
  - case_eq (VarTyp.eqb x z); intros; auto.
  - apply_fresh STType_ForAll as x.
    rewrite subst_typ_open_var.
    apply H1.
    not_in_L x.
    unfold not; intros; subst.
    not_in_L z.
    apply H6.
    apply MSetProperties.Dec.F.singleton_2.
    reflexivity.
    auto.
Qed.

Lemma subst_wf_type : forall t z u Gamma,
  WFType Gamma u -> WFType Gamma t -> WFType Gamma (subst_typ z u t).
Proof.
  induction 2; simpl; auto.
  - case_eq (VarTyp.eqb x z); intros; auto.
  - apply_fresh WFType_ForAll as x.
    rewrite subst_typ_open_var.
    apply H1.
    not_in_L x.
    rewrite <- app_nil_l with (l := (extend x (TyVar STyp) Gamma)).
    apply wf_weaken; rewrite app_nil_l; auto.
    apply Ok_push.
    now apply wf_gives_ok_env in H.
    not_in_L x.
    unfold not; intros; subst.
    not_in_L z.
    apply H7.
    apply MSetProperties.Dec.F.singleton_2.
    reflexivity.
    now apply wf_gives_types with (Gamma := Gamma).
Qed.
  
Hint Resolve subst_type subst_wf_type.

(** We prove that opening a body_type with a term gives a type *)

Lemma open_body_type : forall t u,
  body_type t -> STType u -> STType (open_typ t u).
Proof.
  intros. destruct H. pick_fresh y.
  rewrite subst_typ_intro with (x := y).
  apply subst_type; auto.
  apply H.
  not_in_L y.
  not_in_L y.
  auto.
Qed.  

Lemma open_body_wf_type : forall t u Gamma,
  body_wf_type t Gamma -> WFType Gamma u -> WFType Gamma (open_typ t u).
Proof.
  intros. destruct H. pick_fresh y.

  assert (Ha : not (In y x)) by not_in_L y.
  apply H in Ha.
  rewrite <- app_nil_l with (l := Gamma).
  apply wf_strengthen with (z := y) (U := TyVar STyp).
  unfold not; intros HH.
  apply fv_open_rec_typ in HH.
  rewrite union_spec in HH.
  destruct HH; not_in_L y.
  rewrite app_nil_l.
  rewrite subst_typ_intro with (x := y).
  apply subst_wf_type.
  apply wf_weaken_extend; auto.
  not_in_L y.
  unfold extend in H; apply H.
  not_in_L y.
  apply Ok_push.
  now apply wf_gives_ok_env in H0.
  not_in_L y.
  not_in_L y.
  now apply wf_gives_types in H0.
  apply Ok_push.
  now apply wf_gives_ok_env in H0.
  not_in_L y.
Qed.  

Hint Resolve open_body_type open_body_wf_type.

(* ****** *)

Lemma typing_gives_types : forall Gamma E ty, has_type_st Gamma E ty -> STType ty.
Proof.
  intros.
  induction H; auto.
  - now apply wf_gives_types with (Gamma := Gamma).
  - apply STType_Fun.
    now apply wf_gives_types in H1.
    pick_fresh x.
    apply H0 with (x := x).
    not_in_L x.
  - now inversion IHhas_type_st1.
  - now inversion IHhas_type_st.
  - now inversion IHhas_type_st.
  - apply_fresh STType_ForAll as x.
    apply H0.
    not_in_L x.
  - apply open_body_type.
    auto.
    now apply wf_gives_types in H.
Qed.

Lemma typing_gives_wf_types : forall Gamma E ty, has_type_st Gamma E ty -> WFType Gamma ty.
Proof.
  intros.
  induction H; auto.
  - apply WFType_Fun; auto.
    pick_fresh x.
    assert (Ha : not (In x L)).
    not_in_L x.
    apply H0 in Ha.
    rewrite <- app_nil_l with (l := (extend x (TermVar STyp A) Gamma)) in Ha;
    apply wf_strengthen in Ha.
    now rewrite <- app_nil_l with (l := Gamma).
    not_in_L x.
  - now inversion IHhas_type_st1. 
  - now inversion IHhas_type_st.    
  - now inversion IHhas_type_st. 
  - apply_fresh WFType_ForAll as x.
    apply H0.
    not_in_L x.
Qed.

Lemma typing_gives_terms : forall Gamma E ty, has_type_st Gamma E ty -> STTerm E.
Proof.
  intros.
  induction H; auto.
  - apply_fresh STTerm_Lam as x.
    apply H0.
    not_in_L x.
  - apply_fresh STTerm_TLam as x.
    apply H0.
    not_in_L x.
  - apply STTerm_TApp.
    auto.
    now apply wf_gives_types in H.
Qed.

End SysF.