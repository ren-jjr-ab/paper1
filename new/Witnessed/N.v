(* =========================================== *)
(*  N as a WitnessedSig instance via the        *)
(*  SemiringAsWitnessed functor.                 *)
(* =========================================== *)

Require Import SemiringAsWitnessed.
Require Import NatSemiring.


Module N := SemiringAsWitnessed.Make NatSemiring.NatSemiring.
