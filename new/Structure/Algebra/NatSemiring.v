(* ============================================== *)
(*  NatSemiring                                     *)
(*                                                  *)
(*  ℕ as a DecEqCommSemiring. Addition and          *)
(*  multiplication are Nat.add and Nat.mul;         *)
(*  zero and one are 0 and 1. Equality on nat is    *)
(*  decidable.                                      *)
(* ============================================== *)

Require Import Semiring.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.


Module NatSemiring <: DecEqCommSemiringSig.

  Definition Carrier : Type := nat.

  Definition zero : Carrier := 0.
  Definition one  : Carrier := 1.
  Definition add  : Carrier -> Carrier -> Carrier := Nat.add.
  Definition mul  : Carrier -> Carrier -> Carrier := Nat.mul.

  Definition carrier_eq_dec :
    forall a b : Carrier, {a = b} + {a <> b} := Nat.eq_dec.

  Theorem add_assoc  : forall a b c, add (add a b) c = add a (add b c).
  Proof. intros. unfold add. symmetry. apply Nat.add_assoc. Qed.

  Theorem add_comm   : forall a b, add a b = add b a.
  Proof. intros. unfold add. apply Nat.add_comm. Qed.

  Theorem add_zero_l : forall a, add zero a = a.
  Proof. intros. unfold add, zero. apply Nat.add_0_l. Qed.

  Theorem mul_assoc  : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. intros. unfold mul. symmetry. apply Nat.mul_assoc. Qed.

  Theorem mul_one_l  : forall a, mul one a = a.
  Proof. intros. unfold mul, one. apply Nat.mul_1_l. Qed.

  Theorem mul_one_r  : forall a, mul a one = a.
  Proof. intros. unfold mul, one. apply Nat.mul_1_r. Qed.

  Theorem mul_zero_l : forall a, mul zero a = zero.
  Proof. intros. unfold mul, zero. apply Nat.mul_0_l. Qed.

  Theorem mul_zero_r : forall a, mul a zero = zero.
  Proof. intros. unfold mul, zero. apply Nat.mul_0_r. Qed.

  Theorem distrib_l : forall a b c,
    mul a (add b c) = add (mul a b) (mul a c).
  Proof. intros. unfold mul, add. apply Nat.mul_add_distr_l. Qed.

  Theorem distrib_r : forall a b c,
    mul (add a b) c = add (mul a c) (mul b c).
  Proof. intros. unfold mul, add. apply Nat.mul_add_distr_r. Qed.

  Theorem mul_comm : forall a b, mul a b = mul b a.
  Proof. intros. unfold mul. apply Nat.mul_comm. Qed.

End NatSemiring.
