(* ============================================== *)
(*  IntegerRing                                     *)
(*                                                  *)
(*  ℤ as a DecEqCommRing. Operations and axioms    *)
(*  delegate to Coq's ZArith library.               *)
(* ============================================== *)

Require Import Ring.
From Stdlib Require Import ZArith.


Module IntegerRing <: DecEqCommRingSig.

  Definition Carrier : Type := Z.

  Definition zero : Carrier := 0%Z.
  Definition one  : Carrier := 1%Z.
  Definition add  : Carrier -> Carrier -> Carrier := Z.add.
  Definition mul  : Carrier -> Carrier -> Carrier := Z.mul.
  Definition neg  : Carrier -> Carrier := Z.opp.

  Definition carrier_eq_dec :
    forall a b : Carrier, {a = b} + {a <> b} := Z.eq_dec.

  Theorem add_assoc  : forall a b c, add (add a b) c = add a (add b c).
  Proof. intros. unfold add. symmetry. apply Z.add_assoc. Qed.

  Theorem add_comm   : forall a b, add a b = add b a.
  Proof. intros. unfold add. apply Z.add_comm. Qed.

  Theorem add_zero_l : forall a, add zero a = a.
  Proof. intros. unfold add, zero. apply Z.add_0_l. Qed.

  Theorem add_neg_l  : forall a, add (neg a) a = zero.
  Proof. intros. unfold add, neg, zero. apply Z.add_opp_diag_l. Qed.

  Theorem mul_assoc  : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. intros. unfold mul. symmetry. apply Z.mul_assoc. Qed.

  Theorem mul_one_l  : forall a, mul one a = a.
  Proof. intros. unfold mul, one. apply Z.mul_1_l. Qed.

  Theorem mul_one_r  : forall a, mul a one = a.
  Proof. intros. unfold mul, one. apply Z.mul_1_r. Qed.

  Theorem mul_zero_l : forall a, mul zero a = zero.
  Proof. intros. unfold mul, zero. apply Z.mul_0_l. Qed.

  Theorem mul_zero_r : forall a, mul a zero = zero.
  Proof. intros. unfold mul, zero. apply Z.mul_0_r. Qed.

  Theorem distrib_l : forall a b c,
    mul a (add b c) = add (mul a b) (mul a c).
  Proof. intros. unfold mul, add. apply Z.mul_add_distr_l. Qed.

  Theorem distrib_r : forall a b c,
    mul (add a b) c = add (mul a c) (mul b c).
  Proof. intros. unfold mul, add. apply Z.mul_add_distr_r. Qed.

  Theorem mul_comm : forall a b, mul a b = mul b a.
  Proof. intros. unfold mul. apply Z.mul_comm. Qed.

End IntegerRing.
