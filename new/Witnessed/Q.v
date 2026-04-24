(* =========================================== *)
(*  Q as a WitnessedSig instance via the        *)
(*  FieldAsWitnessed functor.                    *)
(* =========================================== *)

Require Import FieldAsWitnessed.
Require Import RationalField.


Module Q := FieldAsWitnessed.Make RationalField.RationalField.
