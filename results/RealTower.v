(* ============================================== *)
(*  RealTower                                       *)
(*                                                  *)
(*  The number-system tower                          *)
(*                                                  *)
(*     ℚ  →  ℝ_Cauchy  ≅  ℝ_Dedekind                *)
(*     RR     CR           DR                       *)
(*                                                  *)
(*  assembled from existing framework morphisms:   *)
(*                                                  *)
(*    RationalToCauchyMorphism.phi : RR → CR        *)
(*    DedekindCauchyIsomorphism.psi : CR → DR       *)
(*                                                  *)
(*  Integers appear naturally at the ℚ level as     *)
(*  rational numbers with denominator 1. The        *)
(*  framework does not need a separate integer      *)
(*  instance to include ℤ in the tower — z ↦ z/1    *)
(*  is the canonical embedding, and its image       *)
(*  flows through the morphism chain unchanged.     *)
(*                                                  *)
(*  This file chains the existing morphisms and     *)
(*  demonstrates that a single integer (z = 3) has  *)
(*  a concrete entity at every layer.               *)
(* ============================================== *)

Require Existence.
Require ExistenceMorphism.
Require ExternalTime.
Require RationalRep.
Require CauchyReal.
Require DedekindReal.
Require RationalToCauchyMorphism.
Require DedekindCauchyIsomorphism.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.


Module RR := RationalRep.RationalRep.
Module CR := CauchyReal.CauchyReal.
Module DR := DedekindReal.DedekindReal.


(* =========================================== *)
(*  COMPOSITION MORPHISM: ℚ → ℝ_Dedekind        *)
(* =========================================== *)

Definition phi_RR_to_DR (r : RR.Entity) : DR.Entity :=
  DedekindCauchyIsomorphism.psi (RationalToCauchyMorphism.phi r).

Theorem phi_RR_to_DR_preserves_interact :
  forall a b : RR.Entity,
    phi_RR_to_DR (RR.interact a b) =
    DR.interact (phi_RR_to_DR a) (phi_RR_to_DR b).
Proof.
  intros a b. unfold phi_RR_to_DR.
  rewrite RationalToCauchyMorphism.phi_preserves_interact.
  rewrite DedekindCauchyIsomorphism.psi_preserves_interact.
  reflexivity.
Qed.


(* =========================================== *)
(*  INTEGER WITNESS AT EACH LEVEL              *)
(*                                             *)
(*  z = 3 as an integer. At each layer of the  *)
(*  tower this becomes a concrete entity.      *)
(* =========================================== *)

Definition int_three_as_rational : RR.Entity := RR.REnt (3 # 1) 0.

Definition int_three_as_cauchy : CR.Entity :=
  RationalToCauchyMorphism.phi int_three_as_rational.

Definition int_three_as_dedekind : DR.Entity :=
  phi_RR_to_DR int_three_as_rational.

(* Expose the concrete form at each layer. *)

Example three_rational_form :
  int_three_as_rational = RR.REnt (3 # 1) 0.
Proof. reflexivity. Qed.

Example three_cauchy_form :
  int_three_as_cauchy = CR.REnt (CR.CTConst (3 # 1)) 0.
Proof. reflexivity. Qed.

Example three_dedekind_form :
  int_three_as_dedekind = DR.DREnt (DR.DConst (3 # 1)) 0.
Proof. reflexivity. Qed.


(* =========================================== *)
(*  TRACE THROUGH COMPOSITION                  *)
(*                                             *)
(*  The composition ψ ∘ φ maps every rational  *)
(*  REnt q t to DR.DREnt (DConst q) t via the  *)
(*  Cauchy intermediate.                       *)
(* =========================================== *)

Theorem rational_to_dedekind_shape :
  forall (q : Q) (t : nat),
    phi_RR_to_DR (RR.REnt q t) = DR.DREnt (DR.DConst q) t.
Proof. reflexivity. Qed.

Theorem rational_to_dedekind_CMark :
  forall (t : nat),
    phi_RR_to_DR (RR.CMark t) = DR.DEval 0 t.
Proof. reflexivity. Qed.


(* =========================================== *)
(*  INTERACTION PRESERVATION AT INTEGERS        *)
(*                                             *)
(*  Two integers interacting at RR correspond  *)
(*  to their Dedekind images interacting.      *)
(* =========================================== *)

Theorem integer_interaction_preserved :
  forall (z1 z2 : Z) (t1 t2 : nat),
    phi_RR_to_DR (RR.interact (RR.REnt (z1 # 1) t1) (RR.REnt (z2 # 1) t2)) =
    DR.interact (phi_RR_to_DR (RR.REnt (z1 # 1) t1))
                 (phi_RR_to_DR (RR.REnt (z2 # 1) t2)).
Proof. intros. apply phi_RR_to_DR_preserves_interact. Qed.


(* =========================================== *)
(*  TOWER COMMUTES                             *)
(*                                             *)
(*  The three-step chain φ_{RR→DR} =           *)
(*  ψ ∘ φ_{RR→CR} is literal by definition —   *)
(*  no proof beyond reflexivity.               *)
(* =========================================== *)

Theorem tower_commutes :
  forall r : RR.Entity,
    phi_RR_to_DR r =
    DedekindCauchyIsomorphism.psi (RationalToCauchyMorphism.phi r).
Proof. reflexivity. Qed.


(* =========================================== *)
(*  DEDEKIND → CAUCHY (reverse leg)            *)
(*                                             *)
(*  DR ≅ CR gives us the reverse direction     *)
(*  for free. Any Dedekind entity transports   *)
(*  to Cauchy and back.                        *)
(* =========================================== *)

Definition dedekind_to_cauchy (d : DR.Entity) : CR.Entity :=
  DedekindCauchyIsomorphism.phi d.

Theorem dedekind_cauchy_roundtrip :
  forall d : DR.Entity,
    DedekindCauchyIsomorphism.psi (dedekind_to_cauchy d) = d.
Proof.
  intros d. unfold dedekind_to_cauchy.
  apply DedekindCauchyIsomorphism.psi_phi_id.
Qed.

Theorem cauchy_dedekind_roundtrip :
  forall c : CR.Entity,
    dedekind_to_cauchy (DedekindCauchyIsomorphism.psi c) = c.
Proof.
  intros c. unfold dedekind_to_cauchy.
  apply DedekindCauchyIsomorphism.phi_psi_id.
Qed.


(* =========================================== *)
(*  CONCRETE ROUNDTRIPS AT A SPECIFIC INTEGER   *)
(* =========================================== *)

Example three_roundtrip :
  dedekind_to_cauchy int_three_as_dedekind = int_three_as_cauchy.
Proof.
  unfold dedekind_to_cauchy, int_three_as_dedekind, phi_RR_to_DR, int_three_as_cauchy.
  rewrite DedekindCauchyIsomorphism.phi_psi_id.
  reflexivity.
Qed.
