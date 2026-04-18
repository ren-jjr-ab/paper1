(* ============================================== *)
(*  NatSetSet                                       *)
(*                                                  *)
(*  Second-level SymbolicSet: Elem = NatSet.NS.Entity. *)
(*  The resulting instance's entities are sets of   *)
(*  NatSet entities — literal "set of sets" in the  *)
(*  framework.                                      *)
(*                                                  *)
(*  Nesting is obtained without any set-theoretic   *)
(*  axioms beyond the framework's own five plus     *)
(*  ElemSig's decidability witness. The functor     *)
(*  closes under itself: NatSet.NS.Entity satisfies    *)
(*  ElemSig (decidable equality + witness), so      *)
(*  SymbolicSet.Make can be applied again.          *)
(* ============================================== *)

Require Import Existence.
Require Import ExternalTime.
Require Import ElemSig.
Require SymbolicSet.
Require Import NatSet.


Module NatSetElem <: ElemSig.
  Definition Elem : Type := NatSet.NS.Entity.
  Definition elem_eq_dec : forall x y : Elem, {x = y} + {x <> y} :=
    NatSet.NS.entity_eq_dec.
  Definition witness : Elem := NatSet.NS.SREnt NatSet.NS.SEmpty 0.
End NatSetElem.

Module NSS := SymbolicSet.Make NatSetElem.
Export NSS.

Module NatSetSet_is_ExternalTime : ExternalTimeSig := NSS.
