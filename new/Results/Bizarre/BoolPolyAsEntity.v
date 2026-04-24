(* ============================================== *)
(*  BoolPolyAsEntity                                *)
(*                                                  *)
(*  The polynomial ring with Boolean-set            *)
(*  coefficients, promoted into the framework via   *)
(*  RingAsWitnessed. The literal                    *)
(*                                                  *)
(*      {{0,1},{2}} + {{0},{1,2}}·x²                *)
(*                                                  *)
(*  from BooleanSetPolynomial now inhabits a        *)
(*  WitnessedSig: the observer iteration is         *)
(*  attached by the functor, and the ring's own     *)
(*  operations stay untouched.                      *)
(*                                                  *)
(*  Stack height:                                   *)
(*    FinSetRing(3)     — Boolean ring on subsets   *)
(*                         of {0,1,2}               *)
(*    FinSetRing(8)     — subsets of that powerset  *)
(*    PolynomialRing    — polynomials with          *)
(*                        set-of-sets coefficients  *)
(*    RingAsWitnessed   — framework Entity lifting  *)
(*                                                  *)
(*  No markers: motion is supplied by the observer  *)
(*  iteration, not by an auxiliary Mark branch.    *)
(* ============================================== *)

Require Import RingAsWitnessed.
Require Import BooleanSetPolynomial.


Module BoolPolyEntity := RingAsWitnessed.Make BooleanSetPolynomial.FinSet8Poly.


Definition the_polynomial_as_entity : BoolPolyEntity.Entity :=
  (BoolPolyEntity.EConst BooleanSetPolynomial.the_polynomial, 0%nat).


(* =========================================== *)
(*  WITNESSES                                   *)
(* =========================================== *)

(* Self-interact returns the entity unchanged. *)
Example poly_entity_self :
  BoolPolyEntity.interact the_polynomial_as_entity the_polynomial_as_entity
    = the_polynomial_as_entity.
Proof. apply BoolPolyEntity.interact_self. Qed.

(* The Boolean character survives every step. *)
Example poly_self_add_is_zero :
  BooleanSetPolynomial.FinSet8Poly.add
    BooleanSetPolynomial.the_polynomial
    BooleanSetPolynomial.the_polynomial
  = BooleanSetPolynomial.FinSet8Poly.zero.
Proof. apply BooleanSetPolynomial.the_polynomial_add_self. Qed.

(* The polynomial has a non-self partner via observer iteration. *)
Example poly_ent_has_partner :
  exists b : BoolPolyEntity.Entity,
    BoolPolyEntity.interact the_polynomial_as_entity b
    <> the_polynomial_as_entity.
Proof. apply BoolPolyEntity.interact_with. Qed.

(* Two observer tags give distinct entities at the same polynomial. *)
Example poly_ent_distinct_by_iter :
  the_polynomial_as_entity
  <> (BoolPolyEntity.EConst BooleanSetPolynomial.the_polynomial, 42%nat).
Proof. intro H. inversion H. Qed.
