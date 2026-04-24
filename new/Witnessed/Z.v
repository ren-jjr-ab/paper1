(* =========================================== *)
(*  Z as a WitnessedSig instance via the        *)
(*  RingAsWitnessed functor.                     *)
(*                                              *)
(*  The bridge is a single functor application: *)
(*  any ring instance produces a Witnessed      *)
(*  instance, and ℤ is no exception.            *)
(* =========================================== *)

Require Import RingAsWitnessed.
Require Import IntegerRing.


Module IntegerW := RingAsWitnessed.Make IntegerRing.IntegerRing.
