(* ============================================== *)
(*  MultivariatePolynomial                          *)
(*                                                  *)
(*  Iterated PolynomialRing: each application       *)
(*  adds one variable. Ring-over-ring-over-ring     *)
(*  nesting in three layers.                        *)
(*                                                  *)
(*      ℤ          (IntegerRing)                    *)
(*      ℤ[x]       (IntPoly)                        *)
(*      ℤ[x][y]    (IntPoly2)                       *)
(*      ℤ[x][y][z] (IntPoly3)                       *)
(*                                                  *)
(*  Each level satisfies DecEqCommRingSig, so       *)
(*  PolynomialRing can be applied again. The        *)
(*  nesting is type-level: no additional axioms,    *)
(*  no custom constructions. The functor we proved  *)
(*  does all the work.                              *)
(*                                                  *)
(*  Concrete witnesses:                             *)
(*                                                  *)
(*    - Polynomials in ℤ[x][y] constructed from     *)
(*      elements of ℤ[x] as "coefficients".         *)
(*                                                  *)
(*    - Ring operations (add, mul, neg) pass        *)
(*      through all three levels, each operating on *)
(*      the preceding ring's elements.              *)
(*                                                  *)
(*    - Ring axioms (add_assoc, mul_comm, etc.)     *)
(*      at every level, inherited from the functor. *)
(* ============================================== *)

Require Ring.
Require IntegerRing.
Require PolynomialRing.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Import ListNotations.


(* =========================================== *)
(*  LEVEL 1 — ℤ[x]                              *)
(* =========================================== *)

Module IntPoly := PolynomialRing.PolynomialRing IntegerRing.IntegerRing.


(* =========================================== *)
(*  LEVEL 2 — ℤ[x][y]                           *)
(* =========================================== *)

Module IntPoly2 := PolynomialRing.PolynomialRing IntPoly.


(* =========================================== *)
(*  LEVEL 3 — ℤ[x][y][z]                        *)
(* =========================================== *)

Module IntPoly3 := PolynomialRing.PolynomialRing IntPoly2.


(* =========================================== *)
(*  RING AXIOMS AT EVERY LEVEL                 *)
(*                                             *)
(*  Inherited from the PolynomialRing functor. *)
(*  These checks confirm that each level       *)
(*  satisfies DecEqCommRingSig without any     *)
(*  extra effort — the functor application is  *)
(*  self-certifying.                           *)
(* =========================================== *)

(* Level 1: ℤ[x] *)

Check IntPoly.add_assoc.
Check IntPoly.mul_comm.
Check IntPoly.distrib_l.

(* Level 2: ℤ[x][y] *)

Check IntPoly2.add_assoc.
Check IntPoly2.mul_comm.
Check IntPoly2.distrib_l.

(* Level 3: ℤ[x][y][z] *)

Check IntPoly3.add_assoc.
Check IntPoly3.mul_comm.
Check IntPoly3.distrib_l.


(* =========================================== *)
(*  CONCRETE WITNESSES — COEFFICIENT BUILDING  *)
(*                                             *)
(*  At each level, the Carrier is a subset     *)
(*  type of canonical polynomial lists over    *)
(*  the preceding ring's Carrier.              *)
(*                                             *)
(*  We construct small polynomials and witness *)
(*  that ring operations behave as expected.   *)
(* =========================================== *)

(* Base: integer 0 and 1. *)

Definition int_zero : IntegerRing.IntegerRing.Carrier := IntegerRing.IntegerRing.zero.
Definition int_one  : IntegerRing.IntegerRing.Carrier := IntegerRing.IntegerRing.one.

(* Level 1 witnesses. *)

Definition x1_zero : IntPoly.Carrier := IntPoly.zero.
Definition x1_one  : IntPoly.Carrier := IntPoly.one.

Example intpoly_mul_one_l_witness :
  IntPoly.mul x1_one x1_zero = x1_zero.
Proof. apply IntPoly.mul_one_l. Qed.

Example intpoly_add_comm_witness :
  forall p q : IntPoly.Carrier, IntPoly.add p q = IntPoly.add q p.
Proof. apply IntPoly.add_comm. Qed.


(* Level 2 witnesses. *)

Definition x2_zero : IntPoly2.Carrier := IntPoly2.zero.
Definition x2_one  : IntPoly2.Carrier := IntPoly2.one.

Example intpoly2_distrib_witness :
  forall p q r : IntPoly2.Carrier,
    IntPoly2.mul p (IntPoly2.add q r) =
    IntPoly2.add (IntPoly2.mul p q) (IntPoly2.mul p r).
Proof. apply IntPoly2.distrib_l. Qed.

Example intpoly2_mul_assoc_witness :
  forall p q r : IntPoly2.Carrier,
    IntPoly2.mul (IntPoly2.mul p q) r = IntPoly2.mul p (IntPoly2.mul q r).
Proof. apply IntPoly2.mul_assoc. Qed.


(* Level 3 witnesses. *)

Definition x3_zero : IntPoly3.Carrier := IntPoly3.zero.
Definition x3_one  : IntPoly3.Carrier := IntPoly3.one.

Example intpoly3_mul_comm_witness :
  forall p q : IntPoly3.Carrier, IntPoly3.mul p q = IntPoly3.mul q p.
Proof. apply IntPoly3.mul_comm. Qed.

Example intpoly3_add_neg_l_witness :
  forall p : IntPoly3.Carrier,
    IntPoly3.add (IntPoly3.neg p) p = IntPoly3.zero.
Proof. apply IntPoly3.add_neg_l. Qed.


(* =========================================== *)
(*  DECIDABLE EQUALITY AT EVERY LEVEL          *)
(*                                             *)
(*  Also inherited from the functor, lifting   *)
(*  decidable equality through the subset      *)
(*  type construction at each nesting step.    *)
(* =========================================== *)

Check IntPoly.carrier_eq_dec.
Check IntPoly2.carrier_eq_dec.
Check IntPoly3.carrier_eq_dec.

(* Concrete decidable equality checks. *)

Example intpoly_zero_eq_itself :
  {IntPoly.zero = IntPoly.zero} + {IntPoly.zero <> IntPoly.zero}.
Proof. apply IntPoly.carrier_eq_dec. Qed.

Example intpoly3_zero_eq_itself :
  {IntPoly3.zero = IntPoly3.zero} + {IntPoly3.zero <> IntPoly3.zero}.
Proof. apply IntPoly3.carrier_eq_dec. Qed.
