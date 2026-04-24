(* =========================================== *)
(*  Mod7 as a WitnessedSig instance via         *)
(*  RingAsWitnessed — the same functor that    *)
(*  produced Z. Demonstrates extensibility:    *)
(*  any ring enters the framework through one  *)
(*  bridge.                                     *)
(* =========================================== *)

Require Import RingAsWitnessed.
Require Import ModularRing.


Module Mod7W := RingAsWitnessed.Make ModularRing.Mod7Ring.
