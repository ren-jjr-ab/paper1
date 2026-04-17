(* ============================================== *)
(*  SemilatticeInstances                            *)
(*                                                  *)
(*  Concrete LatticeTimed instances built from     *)
(*  idempotent binary operations.                  *)
(*                                                  *)
(*    NatMax    (nat, Nat.max)                     *)
(*    NatMin    (nat, Nat.min)                     *)
(*    BoolAnd   (bool, andb)                       *)
(*    BoolOr    (bool, orb)                        *)
(*                                                  *)
(*  Each instance supplies only the three           *)
(*  LatticeSpec obligations — op_idempotent,        *)
(*  eq_dec, exists_distinct — and receives a full   *)
(*  TimedExistenceSig (hence ExistenceSig)          *)
(*  instance from the LatticeTimed functor.         *)
(*                                                  *)
(*  Absorbing-element semi-lattices (NatMin's 0,    *)
(*  BoolAnd's false, BoolOr's true) fit the         *)
(*  framework naturally via the time coord of the   *)
(*  paired entity — the framework's interact_with   *)
(*  is satisfied through time movement even when    *)
(*  the lattice value is stuck at an absorbing      *)
(*  element.                                        *)
(* ============================================== *)

Require Import Existence.
Require Import ExternalTime.
Require Import LatticeExternalTimed.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.


(* ================================================ *)
(*  NATMAX                                           *)
(* ================================================ *)

Module NatMaxSpec <: LatticeSpec.
  Definition T : Type := nat.
  Definition op : T -> T -> T := Nat.max.
  Theorem op_idempotent : forall a : T, op a a = a.
  Proof. intros a. unfold op. apply Nat.max_id. Qed.
  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof. exact Nat.eq_dec. Qed.
  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists 0, 1. discriminate. Qed.
End NatMaxSpec.

Module NatMax := LatticeExternalTimed.Make NatMaxSpec.


(* ================================================ *)
(*  NATMIN                                           *)
(*                                                   *)
(*  Bottom 0 is absorbing in the value coord; the    *)
(*  time coord rescues framework fit.                *)
(* ================================================ *)

Module NatMinSpec <: LatticeSpec.
  Definition T : Type := nat.
  Definition op : T -> T -> T := Nat.min.
  Theorem op_idempotent : forall a : T, op a a = a.
  Proof. intros a. unfold op. apply Nat.min_id. Qed.
  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof. exact Nat.eq_dec. Qed.
  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists 0, 1. discriminate. Qed.
End NatMinSpec.

Module NatMin := LatticeExternalTimed.Make NatMinSpec.


(* ================================================ *)
(*  BOOLAND                                          *)
(*                                                   *)
(*  false is absorbing; time coord rescues.          *)
(* ================================================ *)

Module BoolAndSpec <: LatticeSpec.
  Definition T : Type := bool.
  Definition op : T -> T -> T := andb.
  Theorem op_idempotent : forall a : T, op a a = a.
  Proof. intros a. unfold op. destruct a; reflexivity. Qed.
  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof. exact bool_dec. Qed.
  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists true, false. discriminate. Qed.
End BoolAndSpec.

Module BoolAnd := LatticeExternalTimed.Make BoolAndSpec.


(* ================================================ *)
(*  BOOLOR                                           *)
(*                                                   *)
(*  true is absorbing; time coord rescues.           *)
(* ================================================ *)

Module BoolOrSpec <: LatticeSpec.
  Definition T : Type := bool.
  Definition op : T -> T -> T := orb.
  Theorem op_idempotent : forall a : T, op a a = a.
  Proof. intros a. unfold op. destruct a; reflexivity. Qed.
  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof. exact bool_dec. Qed.
  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists true, false. discriminate. Qed.
End BoolOrSpec.

Module BoolOr := LatticeExternalTimed.Make BoolOrSpec.
