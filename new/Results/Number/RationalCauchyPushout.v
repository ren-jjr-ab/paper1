(* ============================================== *)
(*  RationalCauchyPushout                           *)
(*                                                  *)
(*  Pushout of the span                             *)
(*                                                  *)
(*         RR                                        *)
(*        /  \                                       *)
(*      id   phi                                     *)
(*      v     v                                      *)
(*     RR     CR                                     *)
(*                                                  *)
(*  glues RR onto CR via phi. In the quotient,       *)
(*  every rational representation r is identified   *)
(*  with its Cauchy embedding phi r.                *)
(*                                                  *)
(*  Uses framework's Construction functor, which    *)
(*  relies on one meta-axiom (quotient_exists in     *)
(*  ExistencePushout).                              *)
(*                                                  *)
(*  Universal property: for any target cocone       *)
(*  (D3, psi1, psi2) compatible with (F1, F2), a    *)
(*  unique rho : Pushout → D3 factors through the   *)
(*  injections.                                     *)
(*                                                  *)
(*  Natural cocone: D3 = CR, psi1 = phi, psi2 = id. *)
(*  The resulting rho "collapses" the pushout       *)
(*  back into CR — every class is represented by    *)
(*  its Cauchy value.                               *)
(* ============================================== *)

Require Existence.
Require Morphism.
Require Pullback.
Require Pushout.
Require RationalRep.
Require Cauchy.
Require RationalRepTest.
Require RationalToCauchyMorphism.
From Stdlib Require Import QArith.


(* =========================================== *)
(*  ALIASES + MORPHISM WRAPPERS                *)
(* =========================================== *)

Module RR := RationalRep.RationalRep.
Module CR := Cauchy.CauchyReal.

Module IdRR := Pullback.IdentityInto RR.
Module IdCR := Pullback.IdentityInto CR.

Module PhiInto <: Pullback.MorphismInto RR CR.
  Definition phi : RR.Entity -> CR.Entity :=
    RationalToCauchyMorphism.phi.
  Theorem preserves_interact :
    forall a b : RR.Entity,
      phi (RR.interact a b) = CR.interact (phi a) (phi b).
  Proof. exact RationalToCauchyMorphism.phi_preserves_interact. Qed.
End PhiInto.


(* =========================================== *)
(*  PUSHOUT CONSTRUCTION                       *)
(*                                             *)
(*  Span: Base = RR, F1 = id (RR → RR),        *)
(*        F2 = phi (RR → CR).                  *)
(*  Identifies each r ∈ RR with phi r ∈ CR     *)
(*  via the base.                              *)
(* =========================================== *)

Module Push :=
  Pushout.Construction RR RR CR IdRR PhiInto.


(* =========================================== *)
(*  BASE IDENTIFICATION                         *)
(*                                             *)
(*  For every rational r, inj1 r = inj2 (phi r) *)
(*  in the pushout. Rational and its Cauchy    *)
(*  embedding collapse to the same class.      *)
(* =========================================== *)

Theorem base_id_halves :
  Push.inj1 RationalRepTest.half_1_2 =
  Push.inj2 (PhiInto.phi RationalRepTest.half_1_2).
Proof. apply Push.base_identification. Qed.

Theorem base_id_any_rational :
  forall r : RR.Entity,
    Push.inj1 r = Push.inj2 (RationalToCauchyMorphism.phi r).
Proof.
  intro r. apply (Push.base_identification r).
Qed.


(* =========================================== *)
(*  HALVES COLLAPSE IN PUSHOUT                 *)
(*                                             *)
(*  In RR we have 1/2 ≠ 2/4 syntactically.     *)
(*  Both phi-embed to (CTConst (1#2)) after    *)
(*  canonicalization at CEval 0 0. In the      *)
(*  pushout, following the base identification *)
(*  chain:                                     *)
(*                                             *)
(*    inj1 (1/2) = inj2 (phi (1/2))            *)
(*    inj1 (2/4) = inj2 (phi (2/4))            *)
(*                                             *)
(*  Classes agree IF phi (1/2) = phi (2/4) in  *)
(*  CR, which does NOT hold pointwise (CTConst *)
(*  (1#2) vs CTConst (2#4)). So without        *)
(*  passing through CEval, the classes DIFFER. *)
(*                                             *)
(*  After applying CEval: interact             *)
(*  (inj2 (CTConst (1#2))) with inj2 (CEval    *)
(*  0 0) collapses both to inj2 (CTConst       *)
(*  (1#2) at time 1).                          *)
(* =========================================== *)


(* =========================================== *)
(*  UNIVERSAL PROPERTY                          *)
(*                                             *)
(*  Target D3 = CR.                            *)
(*  Psi1 : D1 = RR → CR = phi.                 *)
(*  Psi2 : D2 = CR → CR = id.                  *)
(*                                             *)
(*  Agreement: ∀b ∈ Base = RR,                 *)
(*    Psi1 (F1 b) = Psi2 (F2 b)                *)
(*  = phi (id b) = id (phi b)                  *)
(*  = phi b = phi b.                           *)
(*                                             *)
(*  Trivial by reflexivity.                    *)
(* =========================================== *)

Module PsiAgreement <: Push.CoconeAgreement CR PhiInto IdCR.
  Theorem agreement :
    forall b : RR.Entity,
      PhiInto.phi (IdRR.phi b) = IdCR.phi (PhiInto.phi b).
  Proof. intros. reflexivity. Qed.
End PsiAgreement.

Module Rho := Push.Universal CR PhiInto IdCR PsiAgreement.


(* =========================================== *)
(*  FACTORING ARROW rho : Pushout → CR         *)
(* =========================================== *)

Example rho_on_rational_half :
  Rho.rho (Push.inj1 RationalRepTest.half_1_2) =
  RationalToCauchyMorphism.phi RationalRepTest.half_1_2.
Proof. apply Rho.rho_on_inj1. Qed.

Example rho_on_cauchy_identity :
  forall c : CR.Entity, Rho.rho (Push.inj2 c) = c.
Proof. apply Rho.rho_on_inj2. Qed.

Theorem rho_preserves_interact :
  forall a b : Push.Entity,
    Rho.rho (Push.interact a b) = CR.interact (Rho.rho a) (Rho.rho b).
Proof. apply Rho.rho_preserves_interact. Qed.


(* =========================================== *)
(*  STRUCTURAL CONSEQUENCE                     *)
(*                                             *)
(*  rho factors consistently: rho of inj1      *)
(*  equals rho of inj2 composed with phi.      *)
(*  This is the commutativity of the pushout   *)
(*  square under the universal arrow.          *)
(* =========================================== *)

Theorem rho_factors_consistently :
  forall r : RR.Entity,
    Rho.rho (Push.inj1 r) =
    Rho.rho (Push.inj2 (RationalToCauchyMorphism.phi r)).
Proof.
  intro r.
  pose proof (Push.base_identification r) as Hbase.
  unfold IdRR.phi, PhiInto.phi in Hbase.
  rewrite Hbase. reflexivity.
Qed.


(* =========================================== *)
(*  INTERACT INSIDE THE PUSHOUT                *)
(*                                             *)
(*  inj1 and inj2 both preserve interact.      *)
(*  Combined with base_identification,         *)
(*  rational dynamics "agree with" Cauchy      *)
(*  dynamics at each RR point.                 *)
(* =========================================== *)

Theorem inj1_preserves :
  forall a b : RR.Entity,
    Push.inj1 (RR.interact a b) =
    Push.interact (Push.inj1 a) (Push.inj1 b).
Proof. exact Push.inj1_preserves_interact. Qed.

Theorem inj2_preserves :
  forall a b : CR.Entity,
    Push.inj2 (CR.interact a b) =
    Push.interact (Push.inj2 a) (Push.inj2 b).
Proof. exact Push.inj2_preserves_interact. Qed.


(* =========================================== *)
(*  HALVES UNIFY AFTER CEval (rho level)       *)
(*                                             *)
(*  In CR, halves_paper_projection_in_         *)
(*  cauchyreal gives agreement at some CEval.  *)
(*  Under rho (which collapses pushout to CR), *)
(*  the image of both halves agrees at that    *)
(*  same viewpoint.                            *)
(* =========================================== *)

Example halves_rho_images_paper_project :
  (exists c : CR.Entity,
     CR.interact (Rho.rho (Push.inj1 RationalRepTest.half_1_2)) c =
     CR.interact (Rho.rho (Push.inj1 RationalRepTest.half_2_4)) c).
Proof.
  exists (CR.CEval 0 0).
  rewrite !Rho.rho_on_inj1.
  reflexivity.
Qed.
