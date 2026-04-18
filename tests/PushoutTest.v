(* ========================================== *)
(*  PushoutTest                                *)
(*                                             *)
(*  Apply ExistencePushout.Construction to a   *)
(*  concrete span and instantiate its          *)
(*  universal property.                        *)
(*                                             *)
(*  Span chosen:                               *)
(*    Base = D1 = D2 = LatticeComputable       *)
(*    F1 = F2 = identity.                      *)
(*                                             *)
(*  This is the diagonal span. Base            *)
(*  identification collapses Gen1 b and Gen2 b *)
(*  for every b, so the pushout is             *)
(*  isomorphic to LatticeComputable itself.    *)
(*                                             *)
(*  Universal instantiation:                   *)
(*    D3   = LatticeComputable                 *)
(*    Psi1 = Psi2 = identity                   *)
(*                                             *)
(*  The cocone agreement for this choice is    *)
(*  trivially provable, discharging the only   *)
(*  place where user proof is required to      *)
(*  activate the universal property. The       *)
(*  resulting factoring arrow rho is proved    *)
(*  to behave as expected on the two           *)
(*  injections and to preserve interact.       *)
(* ========================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistencePullback.
Require Import ExistencePushout.
Require Import LatticeModel.


(* ================================================ *)
(*  IDENTITY MORPHISM ON LATTICE                     *)
(* ================================================ *)

Module LatId := ExistencePullback.IdentityInto LatticeComputable.


(* ================================================ *)
(*  PUSHOUT OF THE DIAGONAL SPAN                     *)
(* ================================================ *)

Module LatPushout :=
  ExistencePushout.Construction
    LatticeComputable LatticeComputable LatticeComputable
    LatId LatId.


(* ================================================ *)
(*  BASE IDENTIFICATION — diagonal                   *)
(* ================================================ *)

Theorem diagonal_base_identification :
  forall b : LatticeComputable.Entity,
    LatPushout.inj1 b = LatPushout.inj2 b.
Proof.
  intros b. exact (LatPushout.base_identification b).
Qed.


(* ================================================ *)
(*  COCONE AGREEMENT — Theorem, not Axiom            *)
(*                                                   *)
(*  With Psi1 = Psi2 = identity and F1 = F2 =        *)
(*  identity, the agreement is b = b.                *)
(* ================================================ *)

Module LatCocone <: LatPushout.CoconeAgreement
                       LatticeComputable LatId LatId.
  Theorem agreement :
    forall b : LatticeComputable.Entity,
      LatId.phi (LatId.phi b) = LatId.phi (LatId.phi b).
  Proof. intros b. reflexivity. Qed.
End LatCocone.


(* ================================================ *)
(*  UNIVERSAL INSTANTIATION                          *)
(* ================================================ *)

Module LatUniversal :=
  LatPushout.Universal
    LatticeComputable LatId LatId LatCocone.


(* ================================================ *)
(*  FACTORING ARROW — concrete behavior              *)
(* ================================================ *)

Theorem rho_identity_on_inj1 :
  forall a : LatticeComputable.Entity,
    LatUniversal.rho (LatPushout.inj1 a) = a.
Proof. intros a. exact (LatUniversal.rho_on_inj1 a). Qed.

Theorem rho_identity_on_inj2 :
  forall a : LatticeComputable.Entity,
    LatUniversal.rho (LatPushout.inj2 a) = a.
Proof. intros a. exact (LatUniversal.rho_on_inj2 a). Qed.

Theorem rho_preserves_lattice_interact :
  forall a b : LatPushout.Entity,
    LatUniversal.rho (LatPushout.interact a b) =
    LatticeComputable.interact
      (LatUniversal.rho a) (LatUniversal.rho b).
Proof.
  intros a b. exact (LatUniversal.rho_preserves_interact a b).
Qed.


(* ================================================ *)
(*  CROSS-INJECTION: inj1 and inj2 factor the same   *)
(*                                                   *)
(*  Because base identification forces inj1 b =      *)
(*  inj2 b pointwise, rho sends either injection of  *)
(*  the same b to the same target — the universal    *)
(*  arrow collapses the two legs consistently.       *)
(* ================================================ *)

Theorem rho_same_on_both_legs :
  forall b : LatticeComputable.Entity,
    LatUniversal.rho (LatPushout.inj1 b) =
    LatUniversal.rho (LatPushout.inj2 b).
Proof.
  intros b.
  rewrite rho_identity_on_inj1.
  rewrite rho_identity_on_inj2.
  reflexivity.
Qed.
