(* ============================================== *)
(*  NatSet                                          *)
(*                                                  *)
(*  Concrete SymbolicSet instantiation for          *)
(*  Elem = nat. Serves as the canonical Set         *)
(*  instance in the framework.                      *)
(* ============================================== *)

Require Import Existence.
Require Import Witnessed.
Require Import ElemSig.
Require SymbolicSet.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.


Module NatElem <: ElemSig.
  Definition Elem := nat.
  Definition elem_eq_dec := Nat.eq_dec.
  Definition witness : nat := 0.
End NatElem.

Module NS := SymbolicSet.Make NatElem.
Export NS.

(* Static verification that NS satisfies the
   WitnessedSig interface. *)

Module NatSet_is_Witnessed : WitnessedSig := NS.
