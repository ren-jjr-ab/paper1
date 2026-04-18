(* ============================================== *)
(*  BoolPolyAsEntity                                *)
(*                                                  *)
(*  The polynomial ring with Boolean-set            *)
(*  coefficients, promoted into the framework via   *)
(*  RingAsEntity. The literal                       *)
(*                                                  *)
(*      {{0,1},{2}} + {{0},{1,2}}·x²                *)
(*                                                  *)
(*  from BooleanSetPolynomial now inhabits an       *)
(*  ExistenceSig: the marker universe is attached   *)
(*  by the functor, and the ring's own operations   *)
(*  (set-XOR coefficients, polynomial add/mul) stay *)
(*  untouched.                                      *)
(*                                                  *)
(*  Stack height at this point:                     *)
(*                                                  *)
(*    FinSetRing(3)  — Boolean ring on subsets of   *)
(*                     {0,1,2}                      *)
(*    FinSetRing(8)  — subsets of that powerset     *)
(*                     (sets of sets)               *)
(*    PolynomialRing — polynomials with             *)
(*                     set-of-sets coefficients     *)
(*    RingAsEntity   — framework Entity lifting     *)
(*                                                  *)
(*  Four functor applications, one concrete Entity  *)
(*  that simultaneously satisfies every axiom       *)
(*  layer each step committed to.                   *)
(* ============================================== *)

Require RingAsEntity.
Require BooleanSetPolynomial.


(* =========================================== *)
(*  ENTITY FROM THE COMPOSED RING               *)
(* =========================================== *)

Module BoolPolyEntity :=
  RingAsEntity.RingAsEntity BooleanSetPolynomial.FinSet8Poly.


(* =========================================== *)
(*  THE POLYNOMIAL AS AN ENTITY                 *)
(*                                              *)
(*  {{0,1},{2}} + {{0},{1,2}}·x² lifted into    *)
(*  the REnt branch of the marker-augmented     *)
(*  Entity.                                     *)
(* =========================================== *)

Definition the_polynomial_as_entity : BoolPolyEntity.Entity :=
  BoolPolyEntity.REnt BooleanSetPolynomial.the_polynomial.


(* =========================================== *)
(*  WITNESSES                                   *)
(* =========================================== *)

(* Self-interact returns the polynomial entity unchanged. *)

Example poly_entity_self :
  BoolPolyEntity.interact the_polynomial_as_entity the_polynomial_as_entity
    = the_polynomial_as_entity.
Proof. apply BoolPolyEntity.interact_self. Qed.

(* The polynomial has a marker partner: Mark 0 shifts the entity    *)
(* entirely out of the REnt branch into the marker universe.        *)

Example poly_entity_with_marker :
  BoolPolyEntity.interact the_polynomial_as_entity (BoolPolyEntity.Mark 0)
    = BoolPolyEntity.Mark 1.
Proof. reflexivity. Qed.

(* The Boolean character survives every step of the composition.    *)
(* Polynomial + polynomial (coefficient-wise XOR) is zero; this is  *)
(* BooleanSetPolynomial.the_polynomial_add_self restated here as a  *)
(* witness available at the ring level.                              *)

Example poly_self_add_is_zero :
  BooleanSetPolynomial.FinSet8Poly.add
    BooleanSetPolynomial.the_polynomial
    BooleanSetPolynomial.the_polynomial
  = BooleanSetPolynomial.FinSet8Poly.zero.
Proof. apply BooleanSetPolynomial.the_polynomial_add_self. Qed.

(* REnt and Mark branches stay distinct as entities: the framework  *)
(* existence axiom is directly witnessed.                            *)

Example poly_ent_distinct_from_marker :
  the_polynomial_as_entity <> BoolPolyEntity.Mark 42.
Proof. intros H. inversion H. Qed.

(* interact_with: the polynomial is not terminal — a marker moves   *)
(* it. Direct application of the framework axiom.                    *)

Example poly_ent_has_partner :
  exists b : BoolPolyEntity.Entity,
    BoolPolyEntity.interact the_polynomial_as_entity b
    <> the_polynomial_as_entity.
Proof. apply BoolPolyEntity.interact_with. Qed.
