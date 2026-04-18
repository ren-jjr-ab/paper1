(* ========================================== *)
(*  FactorizationTest                           *)
(*                                              *)
(*  Intra-system factorization on                *)
(*  LatticeComputable — demonstrates the         *)
(*  framework's epi-mono factorization at both   *)
(*  extremes:                                    *)
(*                                              *)
(*    [collapse]  phi = const_pair_2_4           *)
(*       kernel is universal (everything ~       *)
(*       everything), quotient is a singleton,   *)
(*       phi_hat is constant.                    *)
(*                                              *)
(*    [identity]  phi = id                       *)
(*       kernel is trivial (a ~ b iff a = b),    *)
(*       quotient is bijective with D1, phi_hat  *)
(*       is an isomorphism.                      *)
(*                                              *)
(*  RationalCauchyFactorization already          *)
(*  demonstrates the cross-system middle case    *)
(*  (quotient non-trivial, embedding non-        *)
(*  surjective). The two extremes here bracket   *)
(*  that example from both sides, verifying the  *)
(*  framework handles the full spectrum.         *)
(* ========================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistencePullback.
Require Import ExistencePushout.
Require Import ExistenceFactorization.
Require Import LatticeModel.


(* ================================================ *)
(*  MORPHISMS                                        *)
(* ================================================ *)

Module LatId := ExistencePullback.IdentityInto LatticeComputable.

Module ConstPair24 <: MorphismInto LatticeComputable LatticeComputable.

  Definition phi
    : LatticeComputable.Entity -> LatticeComputable.Entity :=
    fun _ => pair_2_4.

  Theorem preserves_interact :
    forall a b : LatticeComputable.Entity,
      phi (LatticeComputable.interact a b) =
      LatticeComputable.interact (phi a) (phi b).
  Proof.
    intros a b. unfold phi.
    rewrite LatticeComputable.interact_self. reflexivity.
  Qed.

End ConstPair24.


(* ================================================ *)
(*  EXTREME 1 — UNIVERSAL COLLAPSE (const phi)       *)
(*                                                   *)
(*  Kernel identifies every pair; the quotient is   *)
(*  a singleton. phi_hat is constantly pair_2_4.    *)
(* ================================================ *)

Module ConstFact :=
  ExistenceFactorization.Factorization
    LatticeComputable LatticeComputable ConstPair24.

(* Kernel is universal: every two entities are
   ker-related because const maps both to pair_2_4. *)

Theorem const_ker_universal :
  forall a b : LatticeComputable.Entity, ConstFact.ker a b.
Proof. intros a b. unfold ConstFact.ker. reflexivity. Qed.

(* Every cls-image collapses. *)

Theorem const_cls_collapses :
  forall a b : LatticeComputable.Entity,
    ConstFact.cls a = ConstFact.cls b.
Proof.
  intros a b. apply ConstFact.cls_correct.
  apply const_ker_universal.
Qed.

(* phi_hat is constant: every quotient element maps to pair_2_4. *)

Theorem const_phi_hat_constant :
  forall x : ConstFact.Entity, ConstFact.phi_hat x = pair_2_4.
Proof.
  intros x. destruct (ConstFact.cls_surjective x) as [a Ha].
  subst x. rewrite ConstFact.phi_hat_spec.
  unfold ConstPair24.phi. reflexivity.
Qed.

(* Factorization triangle commutes concretely. *)

Theorem const_factorization_concrete :
  forall a : LatticeComputable.Entity,
    ConstPair24.phi a = ConstFact.phi_hat (ConstFact.cls a).
Proof. exact ConstFact.factorization. Qed.

(* phi_hat is vacuously injective on the singleton. *)

Theorem const_phi_hat_injective_concrete :
  forall x y : ConstFact.Entity,
    ConstFact.phi_hat x = ConstFact.phi_hat y -> x = y.
Proof. exact ConstFact.phi_hat_injective. Qed.

(* Distinct pairs in LatticeComputable collapse in the
   quotient — made explicit. *)

Theorem const_cls_pair24_eq_pair42 :
  ConstFact.cls pair_2_4 = ConstFact.cls pair_4_2.
Proof. apply const_cls_collapses. Qed.


(* ================================================ *)
(*  EXTREME 2 — TRIVIAL KERNEL (identity phi)        *)
(*                                                   *)
(*  Kernel is equality; the quotient is in          *)
(*  bijection with D1; phi_hat is an iso.           *)
(* ================================================ *)

Module IdFact :=
  ExistenceFactorization.Factorization
    LatticeComputable LatticeComputable LatId.

(* Kernel degenerates to equality. *)

Theorem id_ker_is_equality :
  forall a b : LatticeComputable.Entity,
    IdFact.ker a b <-> a = b.
Proof.
  intros a b. unfold IdFact.ker, LatId.phi.
  split; intros H; exact H.
Qed.

(* cls is injective when phi is injective. *)

Theorem id_cls_injective :
  forall a b : LatticeComputable.Entity,
    IdFact.cls a = IdFact.cls b -> a = b.
Proof.
  apply IdFact.injective_phi_makes_cls_injective.
  intros a b H. unfold LatId.phi in H. exact H.
Qed.

(* phi_hat (cls a) = a — the quotient embeds into D1. *)

Theorem id_phi_hat_recovers :
  forall a : LatticeComputable.Entity,
    IdFact.phi_hat (IdFact.cls a) = a.
Proof.
  intros a. rewrite IdFact.phi_hat_spec. unfold LatId.phi. reflexivity.
Qed.

(* phi = id is surjective on LatticeComputable. *)

Theorem id_phi_surjective :
  forall b : LatticeComputable.Entity,
    exists a : LatticeComputable.Entity, LatId.phi a = b.
Proof.
  intros b. exists b. unfold LatId.phi. reflexivity.
Qed.

(* phi_hat is iso: preserves_interact + surjective + injective. *)

Theorem id_phi_hat_is_iso :
  (forall x y,
    IdFact.phi_hat (IdFact.interact x y) =
    LatticeComputable.interact (IdFact.phi_hat x) (IdFact.phi_hat y)) /\
  (forall b, exists x, IdFact.phi_hat x = b) /\
  (forall x y, IdFact.phi_hat x = IdFact.phi_hat y -> x = y).
Proof.
  apply IdFact.phi_hat_is_iso_if_phi_surjective.
  exact id_phi_surjective.
Qed.

(* Distinct pairs in LatticeComputable remain distinct
   in the quotient — the opposite of the ConstFact case. *)

Theorem id_cls_pair24_ne_pair42 :
  IdFact.cls pair_2_4 <> IdFact.cls pair_4_2.
Proof.
  intros Heq.
  apply pair_2_4_distinct_from_pair_4_2.
  apply id_cls_injective. exact Heq.
Qed.


(* ================================================ *)
(*  BRACKET                                          *)
(*                                                   *)
(*  The two extremes together with                   *)
(*  RationalCauchyFactorization (middle case) cover  *)
(*  the full spectrum of framework factorization:    *)
(*                                                   *)
(*    ConstFact  : kernel = universal, quotient = 1  *)
(*    Rat→Cau    : kernel non-trivial, image ⊂ target*)
(*    IdFact     : kernel = equality, quotient ≅ D1  *)
(* ================================================ *)
