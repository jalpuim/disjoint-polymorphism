Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import SystemF.
Require Import Infrastructure.

Module MSubtyping
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module MInfrastructure := MInfrastructure(VarTyp)(set).
Export MInfrastructure.

(* Notes:

The syntax is encoded using Charguéraud's Locally nameless representation:

http://www.chargueraud.org/softs/ln/

 *)

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2)
  | AVar : forall v, Atomic (PFVarT v)
  | AForAll : forall d t, Atomic (ForAll d t)
  | ARec : forall l t, Atomic (Rec l t).
(*  | ATop : Atomic Top. *)

Hint Constructors Atomic.
Hint Constructors STType.

(* Subtyping relation *)

Inductive usub : PTyp -> PTyp -> Prop :=
  | USInt : usub PInt PInt
  | USFun : forall o1 o2 o3 o4, usub o3 o1 -> usub o2 o4 -> usub (Fun o1 o2) (Fun  o3 o4) 
  | USAnd1 : forall t t1 t2, usub t t1 -> usub t t2 -> usub t (And  t1 t2) 
  | USAnd2 : forall t t1 t2 , usub t1 t -> PType t2 -> usub (And t1 t2) t 
  | USAnd3 : forall t t1 t2, usub t2 t -> PType t1 -> usub (And t1 t2) t
  | USVar   : forall v, usub (PFVarT v) (PFVarT v) 
  | USForAll : forall L d1 d2 t1 t2,
                 (forall x, not (In x L) -> usub (open_typ_source t1 (PFVarT x))
                                           (open_typ_source t2 (PFVarT x))) ->
                 usub d2 d1 ->
                 usub (ForAll d1 t1) (ForAll d2 t2)
  | USTop : forall t, PType t -> usub t Top
  | USRec : forall l t1 t2, usub t1 t2 -> usub (Rec l t1) (Rec l t2).

Inductive and_coercion (e : SExp var) : PTyp -> sum (SExp var) (SExp var) -> Prop :=
  | ACInt : and_coercion e PInt (inr e)
  | ACFunL : forall A B e1, and_coercion e B (inl e1) ->
                       and_coercion e (Fun A B) (inl (STLam _ e1))
  | ACFunR : forall A B, and_coercion e B (inr e) ->
                    and_coercion e (Fun A B) (inr e)
  | ACAndL : forall A B e1 e2, and_coercion e A (inl e1) ->
                          and_coercion e B (inl e2) ->
                          and_coercion e (And A B) (inl (STPair _ e1 e2))
  | ACAndR1 : forall A B, and_coercion e A (inr e) ->
                     and_coercion e (And A B) (inr e)
  | ACAndR2 : forall A B, and_coercion e B (inr e) ->
                     and_coercion e (And A B) (inr e)
  | ACVar : forall x, and_coercion e (PFVarT x) (inr e)
  | ACForAllL : forall L A d e1,
                  (forall x, not (In x L) ->
                        and_coercion e (open_typ_source A (PFVarT x)) (inl e1)) ->
                  and_coercion e (ForAll d A) (inl (STTLam _ e1))
  | ACForAllR : forall L A d,
                  (forall x, not (In x L) ->
                        and_coercion e (open_typ_source A (PFVarT x)) (inr e)) ->
                  and_coercion e (ForAll d A) (inr e)
  | ACTop : and_coercion e Top (inl (STUnit _))
  | ACRec : forall l t r, and_coercion e t r ->
                     and_coercion e (Rec l t) r.

Hint Constructors and_coercion.

(* Some properties about and_coercion *)

Definition join_sum : forall {A}, A + A -> A.
  intros A H; destruct H as [a | a]; exact a.
Defined.

Lemma ac_inr_inv : forall t e e', and_coercion e t (inr e') -> and_coercion e t (inr e).
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Hint Resolve ac_inr_inv.

Lemma ac_inr_inv_eq : forall t e e', and_coercion e t (inr e') -> e = e'.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Lemma ac_subst :
  forall t, PType t ->
       forall e c y x,
         x <> y ->
         and_coercion e t c ->
         and_coercion e (subst_typ_source y (PFVarT x) t) c.
Proof.
  intros t Ht.
  induction Ht; intros; eauto.
  - destruct c. inversion H0.
    simpl in *; apply ac_inr_inv_eq in H0; subst.
    destruct (eqb x y); auto.
  - simpl in *.
    destruct c.
    inversion H0; subst.
    apply ACFunL; auto.
    assert (Ha : and_coercion e (Fun t1 t2) (inr s)) by assumption.
    apply ac_inr_inv_eq in Ha; subst.
    inversion H0; subst; auto.
  - simpl in *; destruct c.
    inversion H0; subst.
    apply ACAndL; auto.
    assert (Ha : and_coercion e (And t1 t2) (inr s)) by assumption.
    apply ac_inr_inv_eq in Ha; subst.
    inversion H0; subst; eauto.
  - simpl in *.
    destruct c.
    inversion H2; subst.
    eapply ACForAllL with (L := union L0 (union L (singleton y))); intros z H3.
    rewrite subst_typ_source_open_source_var.
    apply H0.
    not_in_L z.
    assumption.
    apply H4.
    not_in_L z.
    not_in_L z.
    auto.
    assert (Ha : and_coercion e (ForAll d t0) (inr s)) by assumption.
    apply ac_inr_inv_eq in H2; subst.
    inversion Ha; subst.
    eapply ACForAllR with (L := union L0 (union L (singleton y))); intros z H4.
    rewrite subst_typ_source_open_source_var.
    apply H0.
    not_in_L z.    
    assumption.
    apply H3.
    not_in_L z.
    not_in_L z.
    auto.
  - inversion H0; subst; simpl; auto.
Qed.    
    
Lemma ac_rename :
  forall L t e c, forall y, PType (open_typ_source t (PFVarT y)) ->
    ~ In y (union L (fv_ptyp t)) -> and_coercion e (open_typ_source t (PFVarT y)) c ->
    (forall x : elt, ~ In x L -> and_coercion e (open_typ_source t (PFVarT x)) c).
Proof.
  intros.
  destruct (VarTyp.eq_dec x y).
  subst; auto.
  rewrite subst_typ_source_intro with (x := y); auto.
  apply ac_subst; auto.
  not_in_L y.
Qed.
  
Lemma ac_ex : forall L e t,
  (forall x, ~ In x L -> PType (open_typ_source t (PFVarT x))) ->
  (forall x, ~ In x L -> exists c, and_coercion e (open_typ_source t (PFVarT x)) c) ->
  exists c, forall x, ~ In x L -> and_coercion e (open_typ_source t (PFVarT x)) c.
Proof.
  intros L e t H0 H.
  pick_fresh x.
  assert (Ha : ~ In x L) by not_in_L x.
  apply H in Ha.
  destruct Ha as [c HAC].
  exists c.
  intros.
  apply ac_rename with (y := x) (L := L); auto.
  apply H0.
  not_in_L x.
  not_in_L x.
Qed.

Lemma ac_ptype : forall t e, PType t -> exists x, and_coercion e t x.
Proof.
  intros t e Ht.
  induction Ht; eauto.
  - destruct IHHt1, IHHt2.
    destruct x, x0; eauto; apply ac_inr_inv in H0; eauto.
  - destruct IHHt1, IHHt2.
    destruct x, x0; eauto.
  - apply (ac_ex _ _ _ H) in H0.
    destruct IHHt.
    destruct H0.
    destruct x0.
    eexists.
    eapply ACForAllL with (L := L).
    intros.
    apply H0.
    auto.
    eexists.
    eapply ACForAllR with (L := L).
    intros.
    apply H0 in H2.
    now apply ac_inr_inv in H2.
  - destruct IHHt; eauto.
Qed.

(* and_coercion lemmas *)

Lemma ac_inl_term : forall e t r, and_coercion e t (inl r) -> STTerm r.
Proof.
  intros.
  dependent induction H; auto.
  - apply_fresh STTerm_Lam as x.
    unfold open; rewrite <- open_rec_term; auto.
  - pick_fresh x.
    assert (Ha : ~ In x L) by not_in_L x.
    apply H0 in Ha.
    apply body_typ_term_to_term_abs.
    unfold body_typ_term.
    exists (fv e1).
    intros; unfold open_typ_term; rewrite <- open_rec_typ_term_term; auto.
Qed.

Lemma ac_inr_term : forall e t r, STTerm e -> and_coercion e t (inr r) -> STTerm r.
Proof. intros; apply ac_inr_inv_eq in H0; now subst. Qed.
  
Lemma and_coercion_proj1_term :
  forall t0 (c : SExp var) c',
    PType t0 ->
    STTerm c ->
    and_coercion ((STApp _ c (STProj1 _ (STBVar _ 0)))) t0 c' ->
    STTerm (STLam _ (join_sum c')).
Proof.
  intros.
  apply_fresh STTerm_Lam as x; unfold open; simpl.
  destruct c'; simpl.
  apply ac_inl_term in H1.
  rewrite <- open_rec_term; auto.
  apply ac_inr_inv_eq in H1.
  rewrite <- H1.
  simpl.
  apply STTerm_App; auto.
  rewrite <- open_rec_term; auto.
Qed.

Lemma and_coercion_proj2_term :
  forall t0 (c : SExp var) c',
    PType t0 ->
    STTerm c ->
    and_coercion ((STApp _ c (STProj2 _ (STBVar _ 0)))) t0 c' ->
    STTerm (STLam _ (join_sum c')).
Proof.
  intros.
  apply_fresh STTerm_Lam as x; unfold open; simpl.
  destruct c'; simpl.
  apply ac_inl_term in H1.
  rewrite <- open_rec_term; auto.
  apply ac_inr_inv_eq in H1.
  rewrite <- H1.
  simpl.
  apply STTerm_App; auto.
  rewrite <- open_rec_term; auto.
Qed.

Lemma same_coercion :
  forall A, PType A ->
       forall e c1 c2, and_coercion e A c1 -> and_coercion e A c2 -> c1 = c2.
Proof.
  intros A HPT.
  induction HPT; intros.
  - now inversion H; inversion H0.
  - now inversion H; inversion H0.
  - inversion H; inversion H0; subst; eauto.
    + apply f_equal.
      now apply (IHHPT2 _ _ _ H4) in H8; inversion H8.
    + now apply (IHHPT2 _ _ _ H4) in H8; inversion H8.
    + now apply (IHHPT2 _ _ _ H4) in H8; inversion H8.
  - inversion H; inversion H0; subst; eauto.
    + apply f_equal.
      apply (IHHPT1 _ _ _ H3) in H8.
      apply (IHHPT2 _ _ _ H5) in H10.
      inversion H8; inversion H10; now subst.
    + apply (IHHPT1 _ _ _ H3) in H9; inversion H9.
    + apply (IHHPT2 _ _ _ H5) in H9; inversion H9.
    + apply (IHHPT1 _ _ _ H4) in H7; inversion H7.
    + apply (IHHPT2 _ _ _ H4) in H9; inversion H9.
  - inversion H1; inversion H2; subst; eauto.
    + pick_fresh x.
      assert (Ha : @inl _ (SExp var) e1 = inl e0).
      eapply H0 with (x := x).
      not_in_L x.
      apply H6; not_in_L x.
      apply H10; not_in_L x.
      inversion Ha; now subst.
    + pick_fresh x.
      assert (Ha : inl e1 = inr e).
      eapply H0 with (x := x).
      not_in_L x.
      apply H6; not_in_L x.
      apply H10; not_in_L x.
      inversion Ha.
    + pick_fresh x.
      assert (Ha : inl e1 = inr e).
      eapply H0 with (x := x).
      not_in_L x.
      apply H10; not_in_L x.
      apply H6; not_in_L x.
      inversion Ha.
  - inversion H; inversion H0; subst; auto;
    apply (IHHTL _ _ _ H4) in H8; now inversion H8.
  - inversion H; inversion H0; subst; eauto.
Qed.


Fixpoint and_coercion' (t : PTyp) (e : SExp var) {struct t} : sum (SExp var) (SExp var).
refine(
  match t with
    | PInt => inr e
    | Fun _ B => match (and_coercion' B e) with
                  | inl l => inl (STLam _ l)
                  | inr r => inr r
                 end 
    | And A B => match (and_coercion' A e, and_coercion' B e) with
                  | (inl l1, inl l2) =>
                    inl (STPair _ l1 l2)
                  | _ => inr e
                end
    | PBVarT _  => inr e
    | PFVarT _ => inr e
    | ForAll d A => match and_coercion' A e with
                     | inl l => inl (STTLam _ l)
                     | inr e => inr e
                   end
    | Top    => inl (STUnit _)
    | Rec l t => and_coercion' t e
  end).
Defined.
(*
pick_fresh x.
destruct (and_coercion (open_typ_source A (PFVarT x)) e).
apply (inl (STTLam _ s)).
apply (inr s).
Admitted. *)

Inductive sub : PTyp -> PTyp -> (SExp var) -> Prop :=
  | SInt : sub PInt PInt (STLam _ (STBVar _ 0))
  | SFun : forall o1 o2 o3 o4 c1 c2,
             sub o3 o1 c1 ->
             sub o2 o4 c2 -> 
             sub (Fun o1 o2) (Fun o3 o4) (STLam _ (STLam _ (STApp _ c2 (STApp _ (STBVar _ 1) (STApp _ c1 (STBVar _ 0))))))
  | SAnd1 : forall t t1 t2 c1 c2,
              sub t t1 c1 ->
              sub t t2 c2 -> 
              sub t (And t1 t2) (STLam _ (STPair _ (STApp _ c1 (STBVar _ 0)) (STApp _ c2 (STBVar _ 0))))
  | SAnd2 : forall t t1 t2 c ac,
              sub t1 t c ->
              Atomic t ->
              PType t2 ->
              and_coercion ((STApp _ c (STProj1 _ (STBVar _ 0)))) t ac -> 
              sub (And t1 t2) t (STLam _ (join_sum ac))
              (*
              sub (And t1 t2) t (STLam _ (join_sum (and_coercion' t ((STApp _ c (STProj1 _ (STBVar _ 0))))))) *)
  | SAnd3 : forall t t1 t2 c ac,
              sub t2 t c ->
              Atomic t ->
              PType t1 ->
              (* sub (And t1 t2) t (STLam _ (join_sum (and_coercion' t ((STApp _ c (STProj2 _ (STBVar _ 0))))))) *)
              and_coercion ((STApp _ c (STProj2 _ (STBVar _ 0)))) t ac -> 
              sub (And t1 t2) t (STLam _ (join_sum ac))
  | SVar : forall v, sub (PFVarT v) (PFVarT v) (STLam _ (STBVar _ 0))
  | SForAll : forall L d1 d2 t1 t2 c c',
                (forall x, not (In x L) -> sub (open_typ_source t1 (PFVarT x))
                                         (open_typ_source t2 (PFVarT x))
                                         (open_typ_term c (STFVarT x))) ->
                sub d2 d1 c' ->
                sub (ForAll d1 t1) (ForAll d2 t2)
                    (STLam _ (STTLam _ (STApp _ c (STTApp _ (STBVar _ 0) (STBVarT 0)))))
  | STop : forall t, PType t -> sub t Top (STLam _ (STUnit _))
  | SRec : forall l t1 t2 c, sub t1 t2 c -> sub (Rec l t1) (Rec l t2) c.

Hint Constructors Atomic sub usub.

Definition Sub (t1 t2 : PTyp) : Prop := exists (e:SExp var), sub t1 t2 e.

Lemma sub_lc : forall t1 t2, Sub t1 t2 -> PType t1 /\ PType t2.
Proof.
  intros t1 t2 HSub.
  destruct HSub.
  induction H; eauto.
  - destruct IHsub1, IHsub2; auto.
  - destruct IHsub1, IHsub2; auto.
  - destruct IHsub; auto.
  - destruct IHsub; auto.
  - destruct IHsub; split.
    apply_fresh PType_ForAll as x; auto.
    assert (Ha : ~ In x L) by not_in_L x.
    apply H0 in Ha; now destruct Ha.
    apply_fresh PType_ForAll as x; auto.
    assert (Ha : ~ In x L) by not_in_L x.
    apply H0 in Ha; now destruct Ha.
  - destruct IHsub; auto.
Qed.

Hint Resolve sub_lc.

(* Smart constructors for Sub *)

Definition stop : forall t, PType t -> Sub t Top.
unfold Sub; eauto.
Defined.

Definition sint : Sub PInt PInt.
unfold Sub. exists (STLam _ (STBVar _ 0)). 
exact SInt.
Defined.

Definition sfun : forall o1 o2 o3 o4, Sub o3 o1 -> Sub o2 o4 -> Sub (Fun o1 o2) (Fun  o3 o4).
unfold Sub; intros. destruct H. destruct H0.
exists (STLam _ ( 
       STLam _ (STApp _ x0 (STApp _ (STBVar _ 1) (STApp _ x (STBVar _ 0)))))).
apply SFun. auto. auto.
Defined.

Definition sand1 : forall t t1 t2, Sub t t1 -> Sub t t2 -> Sub t (And t1 t2).
unfold Sub. intros. destruct H. destruct H0.
exists (STLam _ (
       STPair _ (STApp _ x (STBVar _ 0)) (STApp _ x0 (STBVar _ 0)))).
apply SAnd1. auto. auto.
Defined.

Definition sand2_atomic :
  forall t t1 t2, Sub t1 t -> Atomic t -> PType t2 -> Sub (And t1 t2) t.
  unfold Sub; intros t t1 t2 H H1 H0.
  destruct H; destruct t; try (now inversion H1); eauto.
  - assert (Ha : Sub t1 (Fun t3 t4)) by (unfold Sub; eauto).
    apply sub_lc in Ha; destruct Ha.
    eapply ac_ptype in H3.
    destruct H3; eauto.
  - assert (Ha : Sub t1 (ForAll t3 t4)) by (unfold Sub; eauto).
    apply sub_lc in Ha; destruct Ha.
    eapply ac_ptype in H3.
    destruct H3; eauto.
  - assert (Ha : Sub t1 (Rec v t0)) by (unfold Sub; eauto).
    apply sub_lc in Ha; destruct Ha.
    eapply ac_ptype in H3.
    destruct H3; eauto.
Defined.

Definition sand2 : forall t t1 t2, Sub t1 t -> PType t2 -> Sub (And t1 t2) t.
  intro t.
  induction t; intros.
  (* Case PInt *)
  - apply sand2_atomic; auto.
  (* Case Fun *)
  - apply sand2_atomic; auto.
  (* Case And *)
  - unfold Sub. unfold Sub in H. destruct H. inversion H.
    assert (Sub (And t0 t3) t1). apply IHt1.
    unfold Sub. exists c1; auto. auto.
    assert (Sub (And t0 t3) t2). apply IHt2.
    unfold Sub. exists c2. auto. auto.
    unfold Sub in H7. destruct H7.
    unfold Sub in H8. destruct H8.
    exists (STLam _ (STPair _ (STApp _ x0 (STBVar _ 0)) (STApp _ x1 (STBVar _ 0)))).
    apply SAnd1. auto. auto.
    inversion H2.
    inversion H2.
  (* Case BVar *)
  - inversion H. inversion H1; inversion H3.
  (* Case FVar *)
  - apply sand2_atomic; auto.
  (* Case ForAll *)
  - apply sand2_atomic; auto; apply AForAll.
  (* Case Top *)
  - apply stop; auto.
    apply PType_And; auto.
    apply sub_lc in H; now destruct H.
  (* Case Rec *)
  - apply sand2_atomic; auto.
Defined.

Definition sand3_atomic :
  forall t t1 t2, Sub t2 t -> Atomic t -> PType t1 -> Sub (And t1 t2) t.
  unfold Sub; intros t t1 t2 H H1 H0.
  destruct t; try (now inversion H1); destruct H; eauto.
  - assert (Ha : Sub t2 (Fun t3 t4)) by (unfold Sub; eauto).
    apply sub_lc in Ha; destruct Ha.
    eapply ac_ptype in H3.
    destruct H3; eauto.
  - assert (Ha : Sub t2 (ForAll t3 t4)) by (unfold Sub; eauto).
    apply sub_lc in Ha; destruct Ha.
    eapply ac_ptype in H3.
    destruct H3; eauto.
  - assert (Ha : Sub t2 (Rec v t0)) by (unfold Sub; eauto).
    apply sub_lc in Ha; destruct Ha.
    eapply ac_ptype in H3.
    destruct H3; eauto. 
Defined.

Definition sand3 : forall t t1 t2, Sub t2 t -> PType t1 -> Sub (And t1 t2) t.
  intros t; induction t; intros.
  (* Case PInt *)
  - apply sand3_atomic; auto.
  (* Case Fun *)
  - apply sand3_atomic; auto.
  (* Case And *)
  - unfold Sub. unfold Sub in H. destruct H. inversion H.
    assert (Sub (And t0 t3) t1). apply IHt1.
    unfold Sub. exists c1. auto. auto.
    assert (Sub (And t0 t3) t2). apply IHt2.
    unfold Sub. exists c2. auto. auto.
    unfold Sub in H7. destruct H7.
    unfold Sub in H8. destruct H8.
    exists (STLam _ (STPair _ (STApp _ x0 (STBVar _ 0)) (STApp _ x1 (STBVar _ 0)))).
    apply SAnd1. auto. auto.
    inversion H2.
    inversion H2.
  (* Case BVar *)
  - inversion H; inversion H1; inversion H3.
  (* Case FVar *)
  - apply sand3_atomic; auto.
  (* Case ForAll *)
  - apply sand3_atomic; auto; apply AForAll.
  (* Case Top *)
  - apply stop; auto.
    apply PType_And; auto.
    apply sub_lc in H; now destruct H.
  (* Case Rec *)
  - apply sand3_atomic; auto.
Qed.

Definition svar : forall v, Sub (PFVarT v) (PFVarT v).
  intros.
  unfold Sub.
  exists (STLam _ (STBVar _ 0)).
  apply SVar.
Defined.

(*
Definition sforall : forall L t1 t2 c,
                (forall x, not (In x L) -> sub (open_ptyp t1 (PFVar x))
                                         (open_ptyp t2 (PFVar x))
                                         (open_typ_term c (STFVarT x))) ->
                Sub (ForAll t1) (ForAll t2).
  intros.
  unfold Sub.
  eexists.
  eapply SForAll.
  intros.
  
  pick_fresh.
 *)

Definition srec : forall l t1 t2, Sub t1 t2 -> Sub (Rec l t1) (Rec l t2).
  intros l t1 t2 HSub; unfold Sub in *; destruct HSub; eauto.
Qed.

Hint Constructors sub.
Hint Resolve stop sint sfun sand1 sand2 sand3 svar srec.

Lemma coercions_produce_terms :
  forall E A B, sub A B E -> STTerm E.
Proof.
  intros.
  induction H.
  (* Case SInt *)
  - apply_fresh STTerm_Lam as x; cbn; auto.
  (* Case SFun *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply_fresh STTerm_Lam as y; cbn.
    apply STTerm_App.
    repeat rewrite <- open_rec_term; assumption.
    apply STTerm_App.
    apply STTerm_Var.
    apply STTerm_App; [ repeat rewrite <- open_rec_term; auto | apply STTerm_Var ].
  (* Case SAnd1 *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply STTerm_Pair.
    apply STTerm_App; repeat rewrite <- open_rec_term; auto.
    rewrite <- open_rec_term; auto.
  (* Case SAnd2 *)
  - apply and_coercion_proj1_term with (t0 := t0) (c := c); auto.
    assert (Ha : Sub t1 t0) by (unfold Sub; eauto).
    now apply sub_lc in Ha as [Ha1 Ha2].
  (* Case SAnd3 *)
  - apply and_coercion_proj2_term with (t0 := t0) (c := c); auto.
    assert (Ha : Sub t2 t0) by (unfold Sub; eauto).
    now apply sub_lc in Ha as [Ha1 Ha2].
  (* Case SVar *)
  - apply_fresh STTerm_Lam as x; cbn; auto.
  (* Case SForAll *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply_fresh STTerm_TLam as y; cbn.
    apply STTerm_App; auto.
    assert (Ha : not (In y L)) by (not_in_L y).
    apply H0 in Ha.
    rewrite open_comm_open_typ_term.
    rewrite <- open_rec_term; auto.
  (* Case STop *)
  - apply_fresh STTerm_Lam as x; cbn; auto.
  (* Case SRec *)
  - auto.
Qed.
    

Lemma sub_inv :
  forall t1 t2 e x n,
    sub (open_rec_typ_source n (PFVarT x) t1) (open_rec_typ_source n (PFVarT x) t2) e ->
    exists e', e = open_rec_typ_term n (STFVarT x) e'.
Proof.
  intros t1 t2 e x n H.
  unfold open.
  inversion H; intros.
  - exists (STLam var (STBVar var 0)); now simpl.
  - exists (STLam var
       (STLam var
          (STApp var c2
                 (STApp var (STBVar var 1) (STApp var c1 (STBVar var 0)))))).
    unfold open_typ_term; simpl.
    apply coercions_produce_terms in H2; apply coercions_produce_terms in H3.
    repeat rewrite <- open_rec_typ_term_term; auto.
  - exists (STLam var
       (STPair var (STApp var c1 (STBVar var 0))
               (STApp var c2 (STBVar var 0)))).
    simpl.
    unfold open_typ_term; simpl.
    apply coercions_produce_terms in H1; apply coercions_produce_terms in H3.
    repeat rewrite <- open_rec_typ_term_term; auto.
  - exists (STLam var (join_sum ac)).
    unfold open_typ_term; simpl.      
    destruct ac; simpl.
    apply ac_inl_term in H4.
    rewrite <- open_rec_typ_term_term; auto.
    apply ac_inr_inv_eq in H4.
    subst; simpl.
    apply coercions_produce_terms in H1.
    rewrite <- open_rec_typ_term_term; auto.
  - exists (STLam var (join_sum ac)).
    unfold open_typ_term; simpl.
    destruct ac; simpl.
    apply ac_inl_term in H4.
    rewrite <- open_rec_typ_term_term; auto.
    apply ac_inr_inv_eq in H4.
    subst; simpl.
    apply coercions_produce_terms in H1.
    rewrite <- open_rec_typ_term_term; auto.
  - exists (STLam var (STBVar var 0)); now simpl.
  - exists (STLam var
             (STTLam var (STApp var c (STTApp var (STBVar var 0) (STBVarT 0))))).
    rewrite <- open_rec_typ_term_term.
    auto.
    rewrite <- H4 in H.
    apply coercions_produce_terms in H.
    apply H.
 - exists (STLam var (STUnit var)); now simpl.
 - exists e.
   subst.
   apply coercions_produce_terms in H2.
   rewrite <- open_rec_typ_term_term; auto.
Qed.           

(** Interlude: substitution of types in term **)

Fixpoint subst_typ_term (z : var) (u : STyp) (t : SExp var) {struct t} : SExp var :=
  match t with
  | STBVar _ i     => STBVar _ i
  | STFVar _ x     => STFVar _ x
  | STUnit _       => STUnit _
  | STLit _ n      => STLit _ n
  | STLam _ t      => STLam _ (subst_typ_term z u t)
  | STApp _ t1 t2  => STApp _ (subst_typ_term z u t1) (subst_typ_term z u t2)
  | STPair _ t1 t2 => STPair _ (subst_typ_term z u t1) (subst_typ_term z u t2)
  | STProj1 _ t    => STProj1 _ (subst_typ_term z u t)
  | STProj2 _ t    => STProj2 _ (subst_typ_term z u t)
  | STTLam _ t     => STTLam _ (subst_typ_term z u t)
  | STTApp _ t ty  => STTApp _ (subst_typ_term z u t) (subst_typ z u ty)
  end.

Lemma subst_typ_term_fresh :
  forall x t u, not (In x (fv t)) ->  subst_typ_term x u t = t.
Proof.
  intros; induction t0; simpl in *; auto.
  - rewrite IHt0; auto.
  - rewrite IHt0_1; [ rewrite IHt0_2 | not_in_L x ]; [ reflexivity | not_in_L x ].
  - rewrite IHt0_1; [ rewrite IHt0_2 | not_in_L x ]; [ reflexivity | not_in_L x ].
  - rewrite IHt0; [ reflexivity | not_in_L x ].
  - rewrite IHt0; [ reflexivity | not_in_L x ].
  - rewrite IHt0; [ reflexivity | not_in_L x ].
  - rewrite IHt0; [ | not_in_L x ].
    rewrite subst_typ_fresh; auto; not_in_L x.
Qed.

Lemma subst_typ_open' : forall x u t1 t2, STType u -> forall n, 
  subst_typ x u (open_rec_typ n t1 t2) = open_rec_typ n (subst_typ x u t1) (subst_typ x u t2).
Proof.
  intros x u t1 t2.
  induction t2; intros; simpl; auto; try (apply f_equal; auto).
  - rewrite IHt2_1; auto; rewrite IHt2_2; auto.
  - rewrite IHt2_1; auto; rewrite IHt2_2; auto.
  - case_eq (eqb v x); intros; [ rewrite <- open_rec_type | ]; auto.
  - case_eq (Nat.eqb n0 n); intros; auto.
Qed.

Lemma subst_typ_term_open : forall x u t1 t2, STType u -> 
  subst_typ_term x u (open_typ_term t1 t2) = open_typ_term (subst_typ_term x u t1) (subst_typ x u t2).
Proof.
  intros. unfold open_typ_term. generalize 0.
  induction t1; intros; simpl; auto; try (apply f_equal; auto).
  - rewrite IHt1_1; rewrite IHt1_2; auto.
  - rewrite IHt1_1; rewrite IHt1_2; auto.
  - rewrite IHt1.
    rewrite <- subst_typ_open'; auto.
Qed.

Lemma subst_typ_open_var :
  forall x y u t,
    y <> x -> STType u ->
    open_typ_term (subst_typ_term x u t) (STFVarT y) =
    subst_typ_term x u (open_typ_term t (STFVarT y)).
Proof.
  intros Neq Wu. intros. rewrite subst_typ_term_open; auto. simpl.
  case_eq (VarTyp.eqb Wu Neq); intros; auto.
  exfalso; apply H.
  now apply eqb_eq in H1.
Qed.

Lemma subst_typ_term_intro : forall x t u, 
  not (In x (fv t)) -> STType u ->
  open_typ_term t u = subst_typ_term x u (open_typ_term t (STFVarT x)).
Proof.
  intros Fr Wu.
  intros.
  rewrite subst_typ_term_open.
  rewrite subst_typ_term_fresh.
  simpl.
  case_eq (eqb Fr Fr); intros; auto.
  apply EqFacts.eqb_neq in H1; exfalso; apply H1; reflexivity.
  auto. auto.
Qed.  

Lemma sub_ex : forall L t1 t2,
  (forall x, ~ In x L -> PType (open_typ_source t1 (PFVarT x))) ->
  (forall x, ~ In x L -> PType (open_typ_source t2 (PFVarT x))) ->              
  (forall x, ~ In x L -> exists c, sub (open_typ_source t1 (PFVarT x))
                            (open_typ_source t2 (PFVarT x))
                            (open_typ_term c (STFVarT x))) ->
  exists c, forall x, ~ In x L -> sub (open_typ_source t1 (PFVarT x))
                           (open_typ_source t2 (PFVarT x))
                           (open_typ_term c (STFVarT x)).
Proof.
  intros L t1 t2 H1 H2 H.
  pick_fresh x.
  assert (Ha : ~ In x L) by not_in_L x.
  apply H in Ha.
  destruct Ha as [c HAC].
  exists c.
  intros.
  (* this should follow naturally from hypothesis HAC *)
  (* we could try using a renaming lemma, but then "x" would have to be fresh in "c" *)
  admit.
Admitted.

Lemma sound_sub : forall t1 t2, usub t1 t2 -> Sub t1 t2.
  intros; induction H; auto.
  - destruct IHusub as [c Hsub].
    unfold Sub in *.
    assert (Ha : forall x : elt,
       ~ In x L ->
       exists e : SExp var,
         sub (open_typ_source t1 (PFVarT x)) (open_typ_source t2 (PFVarT x))
             (open_typ_term e (STFVarT x))).
    intros.
    apply H0 in H2.
    destruct H2.
    assert (H3 : sub (open_typ_source t1 (PFVarT x)) (open_typ_source t2 (PFVarT x)) x0) by assumption.
    apply sub_inv in H2.
    destruct H2; subst.
    eauto.
    clear H0.
    apply sub_ex in Ha.
    destruct Ha.
    eexists.
    apply_fresh SForAll as x; auto.
    apply H0.
    not_in_L y.
    eauto.
    intros.
    apply Ha in H0; destruct H0.
    assert (HSub : Sub (open_typ_source t1 (PFVarT x)) (open_typ_source t2 (PFVarT x))).
    unfold Sub; eauto.
    apply sub_lc in HSub; now destruct HSub.
    intros.
    apply Ha in H0; destruct H0.
    assert (HSub : Sub (open_typ_source t1 (PFVarT x)) (open_typ_source t2 (PFVarT x))).
    unfold Sub; eauto.
    apply sub_lc in HSub; now destruct HSub.
Qed.

Lemma complete_sub : forall t1 t2, Sub t1 t2 -> usub t1 t2.
Proof.
  intros; destruct H; induction H; auto.
  - apply_fresh USForAll as x.
    apply H0.
    not_in_L x.
    auto.
Qed.  

(* Properties about sub *)

Lemma usub_refl : forall t, PType t -> usub t t.
Proof.
  intros t HWFt; induction HWFt; auto.
  - apply_fresh USForAll as x.
    apply H0.
    not_in_L x.
    auto.
Qed.

Lemma usub_and_l : forall t1 t2 t3, usub t1 (And t2 t3) -> usub t1 t2.
Proof.
  intros t1 t2 t3 Husub.
  apply complete_sub.
  apply sound_sub in Husub as [c Hsub].
  inversion Hsub; subst.
  exists c1; auto. inversion H0. inversion H0.
Qed.

Lemma usub_and_r : forall t1 t2 t3, usub t1 (And t2 t3) -> usub t1 t3.
Proof.
  intros t1 t2 t3 Husub.
  apply complete_sub.
  apply sound_sub in Husub as [c Hsub].
  inversion Hsub; subst.
  exists c2; auto. inversion H0. inversion H0.
Qed.

Lemma usub_lc : forall t1 t2, usub t1 t2 -> PType t1 /\ PType t2.
Proof.
  intros.
  apply sound_sub in H.
  now apply sub_lc in H.
Qed.
  
Lemma usub_trans_mid :
  forall A B C D, usub A B -> usub B C -> usub C D -> usub A D.
Proof.
  intros A B C D HusubAB HusubBC HusubCD.
  generalize dependent A.
  generalize dependent D.
  induction HusubBC; intros; auto.
  - dependent induction HusubAB; subst; auto.
  - dependent induction HusubAB; subst; auto.
    dependent induction HusubCD; subst; auto.
    apply USAnd1.
    apply IHHusubCD1; auto.
    intros; auto.
    subst.
    apply usub_and_l with (t3 := t2); eauto.
    intros; auto.
    subst.
    apply usub_and_l with (t3 := t2); eauto.
    apply IHHusubCD2; auto.
    intros; auto.
    subst.
    apply usub_and_r with (t2 := t1); eauto.
    intros; auto.
    subst.
    apply usub_and_r with (t2 := t1); eauto.    
    apply usub_lc in HusubAB1; apply usub_lc in HusubAB2.
    apply USTop; destruct HusubAB1; destruct HusubAB2; auto.
  - dependent induction HusubCD; subst; auto.
    apply usub_lc in HusubAB; apply USTop; destruct HusubAB; auto.
  - dependent induction HusubAB; subst; auto.
  - dependent induction HusubAB; subst; auto.
  - dependent induction HusubCD; subst; auto.
    apply usub_lc in HusubAB; apply USTop; destruct HusubAB; auto. 
  - dependent induction HusubCD; subst; auto.
    dependent induction HusubAB; subst; auto.
    apply_fresh USForAll as x.
    apply H0 with (x := x).
    not_in_L x.
    apply H1.
    not_in_L x.
    apply H3.
    not_in_L x.
    auto.
    apply usub_lc in HusubAB; apply USTop; destruct HusubAB; auto.
  - dependent induction HusubCD; subst; auto.
    apply usub_lc in HusubAB; apply USTop; destruct HusubAB; auto.
  - dependent induction HusubCD; subst; auto.
    apply usub_lc in HusubAB; destruct HusubAB; auto.
    dependent induction HusubAB; subst; auto.
Qed.

Lemma usub_trans :
  forall B A C, PType C -> usub A B -> usub B C -> usub A C.
Proof.
  intros B A C HWFC HusubAB HusubBC.
  assert (HusubCC : usub C C).
  eapply usub_refl; apply HWFC.
  eapply usub_trans_mid.
  apply HusubAB.
  apply HusubBC.
  apply HusubCC.
Qed.

Lemma usub_subst :
  forall A B z u,
    usub A B ->
    PType u ->
    usub (subst_typ_source z u A) (subst_typ_source z u B).
Proof.
  intros A B z u HSub HWFu.
  induction HSub; intros; simpl; eauto.
  - apply USAnd2; auto; now apply subst_source_lc.
  - apply USAnd3; auto; now apply subst_source_lc.
  - destruct eqb; auto.
    eapply usub_refl; apply HWFu.
  - apply_fresh USForAll as x.
    repeat rewrite subst_typ_source_open_source_var; auto.
    apply H0; auto.
    not_in_L x.
    not_in_L x.
    not_in_L x.
    auto.
  - apply USTop.
    apply subst_source_lc; auto.
Qed.

Lemma usub_subst_not_in :
  forall A B u z,
    not (In z (fv_ptyp B)) ->
    usub A B ->
    PType u ->
    usub (subst_typ_source z u A) B.
Proof.
  intros A ty u z HNotIn HSub HWFu.
  erewrite <- subst_typ_source_fresh with (t := ty).
  eapply usub_subst; eauto.
  auto.
Qed.

End MSubtyping.