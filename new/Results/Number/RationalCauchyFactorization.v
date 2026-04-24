(* ============================================== *)
(*  RationalCauchyFactorization                     *)
(*                                                  *)
(*  PART A — Categorical factorization:             *)
(*                                                  *)
(*    RR ─diag_phi─> Pullback ─inj1∘fst─> Pushout   *)
(*                                              │   *)
(*                                             rho  *)
(*                                              ↓   *)
(*                                              CR  *)
(*                                                  *)
(*    Composition equals phi. All four framework    *)
(*    constructions participate in ONE theorem.     *)
(*                                                  *)
(*  PART B — Five-fold witness:                     *)
(*                                                  *)
(*    "1/2 and 2/4 are paper_projection" — same     *)
(*    fact, proved five ways, each through a        *)
(*    different framework structure. All converge   *)
(*    on the same classical identity.               *)
(* ============================================== *)

Require Existence.
Require Morphism.
Require Pullback.
Require Product.
Require Pushout.
Require RationalRep.
Require Cauchy.
Require RationalRepTest.
Require RationalToCauchyMorphism.
Require RationalCauchyProduct.
Require RationalCauchyPullback.
Require RationalCauchyPushout.
From Stdlib Require Import QArith.


(* =========================================== *)
(*  ALIASES                                    *)
(* =========================================== *)

Module RR := RationalRep.RationalRep.
Module CR := Cauchy.CauchyReal.

Module Prod := RationalCauchyProduct.Prod.
Module Pull := RationalCauchyPullback.Pull.
Module Push := RationalCauchyPushout.Push.
Module Rho  := RationalCauchyPushout.Rho.

Definition phi := RationalToCauchyMorphism.phi.
Definition diag_phi := RationalCauchyProduct.diag_phi.


(* =========================================== *)
(*  PART A — CATEGORICAL FACTORIZATION         *)
(* =========================================== *)

(* Arrow: Pullback element → Pushout class.    *)
(* Defined on every product element. Restricted *)
(* to pullback elements, it agrees with the     *)
(* second coordinate's inj2 (base id).          *)

Definition pullback_to_pushout
  (p : RR.Entity * CR.Entity) : Push.Entity :=
  Push.inj1 (fst p).

Theorem pullback_to_pushout_commutes :
  forall p : RR.Entity * CR.Entity,
    Pull.on_pullback p ->
    pullback_to_pushout p = Push.inj2 (snd p).
Proof.
  intros [r c] Hmem.
  unfold Pull.on_pullback in Hmem. simpl in Hmem.
  unfold pullback_to_pushout. simpl.
  unfold RationalCauchyPullback.PhiInto.phi,
         RationalCauchyPullback.IdCR.phi in Hmem.
  rewrite <- Hmem.
  pose proof (Push.base_identification r) as Hb.
  unfold RationalCauchyPushout.IdRR.phi,
         RationalCauchyPushout.PhiInto.phi in Hb.
  exact Hb.
Qed.

Theorem diag_phi_lands_on_pullback :
  forall r : RR.Entity, Pull.on_pullback (diag_phi r).
Proof. exact RationalCauchyPullback.diag_phi_image_in_pullback. Qed.

(* The main factorization theorem. *)

Theorem phi_factors_via_pullback_pushout :
  forall r : RR.Entity,
    Rho.rho (pullback_to_pushout (diag_phi r)) = phi r.
Proof.
  intro r.
  unfold pullback_to_pushout, diag_phi.
  unfold RationalCauchyProduct.UP.pair_morphism. simpl.
  apply Rho.rho_on_inj1.
Qed.

(* Both routes (via inj1, via inj2) agree on
   pullback elements — the factorization is
   independent of projection choice. *)

Theorem factorization_via_inj2 :
  forall r : RR.Entity,
    Rho.rho (Push.inj2 (snd (diag_phi r))) = phi r.
Proof.
  intro r.
  rewrite <- (pullback_to_pushout_commutes
                (diag_phi r)
                (diag_phi_lands_on_pullback r)).
  apply phi_factors_via_pullback_pushout.
Qed.


(* =========================================== *)
(*  PART B — FIVE-FOLD WITNESS                 *)
(*                                             *)
(*  The fact: 1/2 and 2/4 are distinct         *)
(*  rationals (syntactically) but agree at a   *)
(*  witness viewpoint — paper_projection.      *)
(*                                             *)
(*  Proved five ways.                          *)
(* =========================================== *)

(* Path 1 — RationalRep DIRECT                *)
(* Qred canonicalization at CMark 0 witness.  *)

Check RationalRepTest.halves_1_2_and_2_4_paper_projection.
(* : (exists c, RationalRep.interact half_1_2 c =
                RationalRep.interact half_2_4 c)
     /\ half_1_2 <> half_2_4 *)


(* Path 2 — CauchyReal via phi LIFT           *)
(* Framework morphism_carries_agreement lifts *)
(* Path 1's witness through phi.              *)

Check RationalToCauchyMorphism.halves_paper_projection_in_cauchyreal.


(* Path 3 — Product via diag_phi              *)
(* Coordinate-wise interact, witness          *)
(* diag_phi (CMark 0) = (CMark 0, CEval 0 0). *)

Check RationalCauchyProduct.halves_paper_projection_in_product.


(* Path 4 — Pullback CLOSURE                  *)
(* interact_preserves_pullback keeps the      *)
(* phi graph stable under joint dynamics.     *)

Check RationalCauchyPullback.halves_trip_stays_on_pullback.


(* Path 5 — Pushout via inj1 + interact       *)
(* NEW: In the pushout, the inj1 images of    *)
(* 1/2 and 2/4 become interact-equal under    *)
(* CMark 0 viewpoint — Qred-collapsed inside  *)
(* the quotient.                              *)

Example halves_paper_projection_in_pushout :
  Push.interact (Push.inj1 RationalRepTest.half_1_2)
                (Push.inj1 (RR.CMark 0)) =
  Push.interact (Push.inj1 RationalRepTest.half_2_4)
                (Push.inj1 (RR.CMark 0)).
Proof.
  rewrite <- !Push.inj1_preserves_interact.
  reflexivity.
Qed.


(* =========================================== *)
(*  STRUCTURAL NOTE                            *)
(*                                             *)
(*  All five paths establish the same fact.    *)
(*  Path 1 is the source of truth; Paths 2-5   *)
(*  obtain it via framework machinery only —   *)
(*  no Qred_complete re-invocation, no new     *)
(*  ε-δ reasoning. Each arrow in the           *)
(*  categorical diagram (morphism, product     *)
(*  pair, pullback embedding, pushout          *)
(*  injection) preserves the fact.             *)
(*                                             *)
(*  This is the framework's internal           *)
(*  consistency: no matter which structural    *)
(*  tool a reader chooses, the verdict on      *)
(*  rational equivalence is invariant.         *)
(* =========================================== *)
