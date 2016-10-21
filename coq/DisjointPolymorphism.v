Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import SystemF.
Require Import Extended.

(* Notes:

The syntax is encoded using Charguéraud's Locally nameless representation:

http://www.chargueraud.org/softs/ln/

We annotate the Coq theorems with the corresponding lemmas/theorems in the paper. 
The reader can just look for:

Lemma 4

for example, to look for the proof of lemma 4 in the paper.
This top-level Coq script only re-states the lemmas/theorems formulated in the paper,
which have been proven in other sub-scripts.

All lemmas and theorems are complete: there are no uses of admit or Admitted,
with the exceptions of "sound_sub" due to a technical limitation.

*)

Module MDisjointPolymorphism
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module MExtended := MExtended(VarTyp)(set).
Export MExtended.

(* Lemma 2: Subtyping reflexivity *)

Lemma subyping_reflexivity : forall A, PType A -> Sub A A.
Proof. intros; apply sound_sub; now apply usub_refl. Qed.

(* Lemma 3: Subtyping transitivity *)

Lemma subtyping_transitivity : forall B A C : PTyp, PType C -> Sub A B -> Sub B C -> Sub A C.
Proof.
  intros B A C HPT HS1 HS2. apply complete_sub in HS1. apply complete_sub in HS2.
  apply sound_sub; eapply usub_trans; eauto.
Qed.

(* Lemma 4: Covariance of disjointness *)

Lemma covariance_disjointness :
  forall Gamma A B C, PType C -> Ortho Gamma A B -> Sub B C -> Ortho Gamma A C.
Proof.
  intros Gamma A B C HT HO HS; apply complete_sub in HS; eapply Ortho_usub_trans; eauto.
Qed.

(* Lemma 5: Disjointness is stable under substitution *)

Lemma disjointness_stable_substitution :
  forall a C Gamma D A B,
    not (In a (fv_ptyp C)) ->
    WFEnv (subst_env Gamma a C) ->
    WFEnv Gamma ->
    MapsTo Gamma a D -> 
    Ortho Gamma C D ->
    Ortho Gamma A B ->
    PType C ->
    PType A ->
    PType B ->
    Ortho (subst_env Gamma a C) (subst_typ_source a C A) (subst_typ_source a C B).
Proof. apply ortho_subst. Qed.

(* Lemma 6: Types are stable under substitution *)

Lemma types_stable_substitution :
  forall A a B Gamma C, not (In a (fv_ptyp B)) ->
               MapsTo Gamma a C ->
               WFEnv (subst_env Gamma a B) ->
               Ortho Gamma B C ->
               WFTyp Gamma B ->
               WFTyp Gamma A ->
               WFTyp (subst_env Gamma a B) (subst_typ_source a B A).
Proof. apply subst_source_wf_typ. Qed.

(* Lemma 7: Well-formed typing *)

Lemma wellformed_typing :
  forall Gamma e A E dir, has_type_source_alg Gamma e dir A E -> WFTyp Gamma A.
Proof. apply typing_wf_source_alg. Qed.  

(* Lemma 8: Subtyping rules produce type-correct coercions *)

Lemma subtype_correct_coercions :
  forall Gamma A1 A2 E, sub A1 A2 E ->
               WFEnv Gamma ->
               WFTyp Gamma A1 ->
               WFTyp Gamma A2 ->
               has_type_st (∥ Gamma ∥) E (STFun (|A1|) (|A2|)) .
Proof. apply type_correct_coercions. Qed.

(* Lemma 9: Unique subtyping contributor *)

Lemma unique_subtyping_contributor :
  forall Gamma A1 A2 B, WFTyp Gamma A1 ->
               WFTyp Gamma A2 ->
               ~ TopLike B ->
               Ortho Gamma A1 A2 ->
               Sub (And A1 A2) B ->
               not (Sub A1 B /\ Sub A2 B).
Proof. apply uniquesub. Qed.

(* Lemma 10: Unique coercion *)

Lemma unique_coercion :
  forall A B E1 E2 Gamma, WFTyp Gamma A ->
                 WFTyp Gamma B ->
                 sub A B E1 ->
                 sub A B E2 -> E1 = E2.
Proof. intros; eapply sub_coherent; [ apply H | apply H0 | | ]; eauto. Qed.

(* Theorem 1: Type preservation *)

Lemma type_preservation :
  forall e ty dir E (Gamma : context TyEnvSource) (H : has_type_source_alg Gamma e dir ty E),
  has_type_st (∥ Gamma ∥) E (|ty|).
Proof. apply type_preservation. Qed.

(* Theorem 3: Uniqueness of type-inference *)

Lemma uniqueness_type_inference :
  forall Gamma e A1 A2 E1 E2, has_type_source_alg Gamma e Inf A1 E1 ->
                     has_type_source_alg Gamma e Inf A2 E2 ->
                     A1 = A2.
Proof. intros; eapply typ_inf_unique; eauto. Qed.

(* Theorem 4: Unique elaboration *)

Lemma unique_elaboration :
  forall Gamma e d A E1 E2, has_type_source_alg Gamma e d A E1 ->
                   has_type_source_alg Gamma e d A E2 ->
                   E1 = E2.
Proof. intros; eapply typ_coherence; eauto. Qed.

End MDisjointPolymorphism.