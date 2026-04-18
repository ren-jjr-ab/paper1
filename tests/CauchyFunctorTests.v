(* ========================================== *)
(*  CauchyTestSuite                             *)
(*                                              *)
(*  Apply the framework's Equalizer,            *)
(*  Coequalizer, and Factorization constructions*)
(*  to CauchyReal.                              *)
(*                                              *)
(*  CauchyReal's interact advances external     *)
(*  time on every non-self step. This makes     *)
(*  preserves_interact severely restrictive:    *)
(*  any morphism that identifies two distinct   *)
(*  entities must land on a self-interacting    *)
(*  target, i.e., the morphism is essentially   *)
(*  constant on the collapsed fibres. The two   *)
(*  extremes (const and id) bracket what the    *)
(*  time-tracked framework permits.             *)
(*                                              *)
(*  Cross-system factorization is already       *)
(*  covered by RationalCauchyFactorization;     *)
(*  this file records the intra-CauchyReal      *)
(*  brackets.                                   *)
(* ========================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistencePullback.
Require Import ExistencePushout.
Require Import ExistenceEqualizer.
Require Import ExistenceCoequalizer.
Require Import ExistenceFactorization.
Require CauchyReal.
From Stdlib Require Import QArith.


(* ================================================ *)
(*  MODULE ALIASES + WITNESSES                       *)
(* ================================================ *)

Module CR := CauchyReal.CauchyReal.

Definition zero_ent : CR.Entity := CR.REnt (CR.CTConst 0) 0.
Definition invsucc_ent : CR.Entity := CR.REnt CR.CTInvSucc 0.

Theorem zero_ne_invsucc : zero_ent <> invsucc_ent.
Proof. intros H. inversion H. Qed.


(* ================================================ *)
(*  MORPHISMS                                        *)
(* ================================================ *)

Module CauchyId := ExistencePullback.IdentityInto CR.

Module ConstZero <: MorphismInto CR CR.

  Definition phi : CR.Entity -> CR.Entity := fun _ => zero_ent.

  Theorem preserves_interact :
    forall a b : CR.Entity,
      phi (CR.interact a b) = CR.interact (phi a) (phi b).
  Proof.
    intros a b. unfold phi.
    rewrite CR.interact_self. reflexivity.
  Qed.

End ConstZero.


(* ================================================ *)
(*  EQUALIZER                                        *)
(*                                                   *)
(*  F = id, G = const zero_ent.                      *)
(*  on_equalizer(a) ⟺ a = zero_ent.                 *)
(* ================================================ *)

Module CauchyEq :=
  ExistenceEqualizer.Equalizer
    CR CR CauchyId ConstZero.

Theorem equalizer_zero : CauchyEq.on_equalizer zero_ent.
Proof.
  unfold CauchyEq.on_equalizer, CauchyId.phi, ConstZero.phi.
  reflexivity.
Qed.

Theorem not_equalizer_invsucc : ~ CauchyEq.on_equalizer invsucc_ent.
Proof.
  unfold CauchyEq.on_equalizer, CauchyId.phi, ConstZero.phi.
  intros Heq. apply zero_ne_invsucc. symmetry. exact Heq.
Qed.

Theorem equalizer_preserved_zero :
  CauchyEq.on_equalizer (CR.interact zero_ent zero_ent).
Proof.
  apply CauchyEq.interact_preserves_equalizer;
    exact equalizer_zero.
Qed.

(* Observational equalizer. *)

Module CauchyEqObs :=
  ExistenceEqualizer.ObservationalEqualizer
    CR CR CauchyId ConstZero.

Theorem zero_observational :
  CauchyEqObs.on_equalizer_observational zero_ent.
Proof.
  apply CauchyEqObs.on_equalizer_is_observational.
  exact equalizer_zero.
Qed.


(* ================================================ *)
(*  COEQUALIZER                                      *)
(*                                                   *)
(*  Universal collapse onto zero_ent.                *)
(* ================================================ *)

Module CauchyCoeq :=
  ExistenceCoequalizer.Universal
    CR CR CauchyId ConstZero
    CR ConstZero.

Theorem cauchy_cls_anything_eq_zero :
  forall a : CR.Entity,
    CauchyCoeq.C.cls a = CauchyCoeq.C.cls zero_ent.
Proof.
  intros a. apply CauchyCoeq.C.cls_correct.
  exact (CauchyCoeq.C.e_identify a).
Qed.

Theorem cauchy_coequalizer_is_singleton :
  forall a b : CR.Entity,
    CauchyCoeq.C.cls a = CauchyCoeq.C.cls b.
Proof.
  intros a b.
  rewrite (cauchy_cls_anything_eq_zero a).
  rewrite (cauchy_cls_anything_eq_zero b).
  reflexivity.
Qed.

(* Zero and invsucc (the natural convention_eq pair
   at the paper level) collapse in the Coequalizer. *)

Theorem cauchy_cls_zero_eq_invsucc :
  CauchyCoeq.C.cls zero_ent = CauchyCoeq.C.cls invsucc_ent.
Proof. apply cauchy_coequalizer_is_singleton. Qed.

Theorem cauchy_q_preserves_interact :
  forall a b : CR.Entity,
    CauchyCoeq.C.q (CR.interact a b) =
    CauchyCoeq.C.interact (CauchyCoeq.C.q a) (CauchyCoeq.C.q b).
Proof. exact CauchyCoeq.C.q_preserves_interact. Qed.

(* Universal factoring: R = const_zero coequalizes F, G
   trivially. *)

Module CauchyCoeqR <: CauchyCoeq.CoequalizingRmorphism.
  Theorem r_coequalizes :
    forall a : CR.Entity,
      ConstZero.phi (CauchyId.phi a) =
      ConstZero.phi (ConstZero.phi a).
  Proof.
    intros a. unfold ConstZero.phi, CauchyId.phi. reflexivity.
  Qed.
End CauchyCoeqR.

Module CauchyFactor := CauchyCoeq.Factor CauchyCoeqR.

Theorem cauchy_r_star_constantly_zero :
  forall e : CauchyCoeq.C.Entity,
    CauchyFactor.r_star e = zero_ent.
Proof.
  intros e.
  destruct (CauchyCoeq.C.cls_surjective e) as [w Hw].
  subst e.
  rewrite CauchyFactor.r_star_factors.
  unfold ConstZero.phi. reflexivity.
Qed.


(* ================================================ *)
(*  FACTORIZATION                                    *)
(*                                                   *)
(*  ConstFact (phi = const zero_ent): universal      *)
(*  kernel. IdFact (phi = id): trivial kernel + iso. *)
(* ================================================ *)

Module CauchyConstFact :=
  ExistenceFactorization.Factorization CR CR ConstZero.

Theorem cauchy_const_ker_universal :
  forall a b : CR.Entity, CauchyConstFact.ker a b.
Proof. intros a b. unfold CauchyConstFact.ker. reflexivity. Qed.

Theorem cauchy_const_cls_collapses :
  forall a b : CR.Entity,
    CauchyConstFact.cls a = CauchyConstFact.cls b.
Proof.
  intros a b. apply CauchyConstFact.cls_correct.
  apply cauchy_const_ker_universal.
Qed.

Theorem cauchy_const_phi_hat_constant :
  forall x : CauchyConstFact.Entity,
    CauchyConstFact.phi_hat x = zero_ent.
Proof.
  intros x.
  destruct (CauchyConstFact.cls_surjective x) as [a Ha].
  subst x. rewrite CauchyConstFact.phi_hat_spec.
  unfold ConstZero.phi. reflexivity.
Qed.


Module CauchyIdFact :=
  ExistenceFactorization.Factorization CR CR CauchyId.

Theorem cauchy_id_ker_is_equality :
  forall a b : CR.Entity,
    CauchyIdFact.ker a b <-> a = b.
Proof.
  intros a b. unfold CauchyIdFact.ker, CauchyId.phi.
  split; intros H; exact H.
Qed.

Theorem cauchy_id_cls_injective :
  forall a b : CR.Entity,
    CauchyIdFact.cls a = CauchyIdFact.cls b -> a = b.
Proof.
  apply CauchyIdFact.injective_phi_makes_cls_injective.
  intros a b H. unfold CauchyId.phi in H. exact H.
Qed.

Theorem cauchy_id_phi_surjective :
  forall b : CR.Entity, exists a : CR.Entity, CauchyId.phi a = b.
Proof. intros b. exists b. unfold CauchyId.phi. reflexivity. Qed.

Theorem cauchy_id_phi_hat_is_iso :
  (forall x y,
    CauchyIdFact.phi_hat (CauchyIdFact.interact x y) =
    CR.interact (CauchyIdFact.phi_hat x) (CauchyIdFact.phi_hat y)) /\
  (forall b, exists x, CauchyIdFact.phi_hat x = b) /\
  (forall x y, CauchyIdFact.phi_hat x = CauchyIdFact.phi_hat y -> x = y).
Proof.
  apply CauchyIdFact.phi_hat_is_iso_if_phi_surjective.
  exact cauchy_id_phi_surjective.
Qed.

Theorem cauchy_id_cls_zero_ne_invsucc :
  CauchyIdFact.cls zero_ent <> CauchyIdFact.cls invsucc_ent.
Proof.
  intros Heq. apply zero_ne_invsucc.
  apply cauchy_id_cls_injective. exact Heq.
Qed.
