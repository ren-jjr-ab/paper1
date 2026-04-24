(* ============================================== *)
(*  RationalCauchyProduct                           *)
(*                                                  *)
(*  RationalRep × CauchyReal as a joint instance.   *)
(*                                                  *)
(*  Product's interact is coordinate-wise.          *)
(*  Product's collapse requires BOTH           *)
(*  coordinates — which is uninhabited here         *)
(*  because RationalRep.collapse is False.     *)
(*                                                  *)
(*  Using the morphism phi : RationalRep →          *)
(*  CauchyReal (from RationalToCauchyMorphism),     *)
(*  the universal property of the product gives     *)
(*  a "diagonal" morphism                           *)
(*                                                  *)
(*    diag_phi : RR → RR × CR                       *)
(*    diag_phi r := (r, phi r)                      *)
(*                                                  *)
(*  pair_morphism from UniversalPair functor.       *)
(*                                                  *)
(*  Verifies:                                       *)
(*  - Product functor applies.                      *)
(*  - Projections recover coordinates.              *)
(*  - RR's rational paper_projection lifts to       *)
(*    the product with explicit joint witness.      *)
(*  - Product collapse is uninhabited.         *)
(* ============================================== *)

Require Existence.
Require ExistenceProduct.
Require ExistenceMorphism.
Require RationalRep.
Require CauchyReal.
Require RationalRepTest.
Require RationalToCauchyMorphism.
From Stdlib Require Import QArith.


(* =========================================== *)
(*  ALIASES + PRODUCT + PROJECTIONS            *)
(* =========================================== *)

Module RR := RationalRep.RationalRep.
Module CR := CauchyReal.CauchyReal.

Module Prod := ExistenceProduct.Make RR CR.
Module Proj := ExistenceProduct.Projections RR CR.
Module UP   := ExistenceProduct.UniversalPair RR RR CR.

Definition phi := RationalToCauchyMorphism.phi.


(* =========================================== *)
(*  COMPUTE — coordinate-wise interact         *)
(* =========================================== *)

Compute Prod.interact
  (RR.REnt (1#2) 0, CR.REnt (CR.CTConst (1#2)) 0)
  (RR.CMark 0,      CR.CEval 0 0).
(* = (RR.REnt (1#2) 1, CR.REnt (CR.CTConst (1#2)) 1) *)

Compute Prod.interact
  (RR.REnt (2#4) 0, CR.REnt (CR.CTConst (2#4)) 0)
  (RR.CMark 0,      CR.CEval 0 0).
(* = (RR.REnt (1#2) 1, CR.REnt (CR.CTConst (1#2)) 1)
     — both coords canonicalize via Qred *)


(* =========================================== *)
(*  PRODUCT collapse IS UNINHABITED       *)
(*                                             *)
(*  Product.collapse requires BOTH        *)
(*  coordinates to be collapse. Since     *)
(*  RationalRep.collapse = False, no      *)
(*  product pair satisfies it.                 *)
(* =========================================== *)

Theorem product_no_convention_eq :
  forall a b : Prod.Entity, ~ Prod.collapse a b.
Proof.
  intros [a1 a2] [b1 b2] [Hconv _]. exact Hconv.
Qed.


(* =========================================== *)
(*  DIAGONAL MORPHISM                          *)
(*                                             *)
(*  Universal property: id : RR → RR and       *)
(*  phi : RR → CR give the pair                *)
(*    diag_phi r := (r, phi r) : RR → RR × CR  *)
(* =========================================== *)

Definition diag_phi : RR.Entity -> Prod.Entity :=
  UP.pair_morphism (fun x => x) phi.

Theorem diag_phi_preserves_interact :
  UP.M.preserves_interact diag_phi.
Proof.
  apply UP.pair_preserves_interact.
  - intros a b. reflexivity.
  - exact RationalToCauchyMorphism.phi_preserves_interact.
Qed.


(* =========================================== *)
(*  PROJECTIONS RECOVER COORDINATES            *)
(* =========================================== *)

Example diag_phi_pi1 :
  forall r : RR.Entity, Proj.pi1 (diag_phi r) = r.
Proof. reflexivity. Qed.

Example diag_phi_pi2 :
  forall r : RR.Entity, Proj.pi2 (diag_phi r) = phi r.
Proof. reflexivity. Qed.


(* =========================================== *)
(*  STRUCTURAL IDENTITY OF DIAGONAL POINTS     *)
(* =========================================== *)

Example diag_phi_CMark_0 :
  diag_phi (RR.CMark 0) = (RR.CMark 0, CR.CEval 0 0).
Proof. reflexivity. Qed.

Example diag_phi_half_1_2 :
  diag_phi RationalRepTest.half_1_2 =
  (RR.REnt (1#2) 0, CR.REnt (CR.CTConst (1#2)) 0).
Proof. reflexivity. Qed.


(* =========================================== *)
(*  PRODUCT COMPUTE via diag_phi                *)
(* =========================================== *)

Compute Prod.interact
  (diag_phi (RR.REnt (1#2) 0))
  (diag_phi (RR.CMark 0)).
(* = (RR.REnt (1#2) 1, CR.REnt (CR.CTConst (1#2)) 1) *)

Compute Prod.interact
  (diag_phi (RR.REnt (2#4) 0))
  (diag_phi (RR.CMark 0)).
(* Same concrete term as above *)


(* =========================================== *)
(*  PAPER_PROJECTION LIFTS TO PRODUCT          *)
(*                                             *)
(*  Rational halves (RR) paper_projection      *)
(*  AND its phi image (CR) paper_projection    *)
(*  together give a joint paper_projection in  *)
(*  the product — with explicit witness        *)
(*  diag_phi (RR.CMark 0) = (CMark 0, CEval 0  *)
(*  0).                                         *)
(* =========================================== *)

Example halves_agree_in_product_via_diag :
  Prod.interact (diag_phi RationalRepTest.half_1_2)
                (diag_phi (RR.CMark 0)) =
  Prod.interact (diag_phi RationalRepTest.half_2_4)
                (diag_phi (RR.CMark 0)).
Proof. reflexivity. Qed.

Theorem halves_paper_projection_in_product :
  (exists c : Prod.Entity,
     Prod.interact (diag_phi RationalRepTest.half_1_2) c =
     Prod.interact (diag_phi RationalRepTest.half_2_4) c)
  /\ diag_phi RationalRepTest.half_1_2 <>
     diag_phi RationalRepTest.half_2_4.
Proof.
  split.
  - exists (diag_phi (RR.CMark 0)). reflexivity.
  - intro H. inversion H.
Qed.


(* =========================================== *)
(*  WITNESS IS A DIAGONAL POINT                *)
(*                                             *)
(*  The joint paper_projection witness is      *)
(*  itself on the diagonal — no extra          *)
(*  structure needed beyond the natural phi    *)
(*  embedding.                                 *)
(* =========================================== *)

Example witness_lies_on_diagonal :
  exists r : RR.Entity,
    diag_phi r = (RR.CMark 0, CR.CEval 0 0).
Proof. exists (RR.CMark 0). reflexivity. Qed.
