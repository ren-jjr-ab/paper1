(* ============================================== *)
(*  RationalField                                   *)
(*                                                  *)
(*  ℚ as a DecEqField. Carrier is Qc (canonical   *)
(*  rationals) so that Leibniz equality coincides  *)
(*  with rational equivalence. Operations delegate *)
(*  to Coq's Qcanon library.                        *)
(* ============================================== *)

Require Import Field.
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qcanon.


Module RationalField <: DecEqFieldSig.

  Definition Carrier : Type := Qc.

  Definition zero : Carrier := 0%Qc.
  Definition one  : Carrier := 1%Qc.
  Definition add  : Carrier -> Carrier -> Carrier := Qcplus.
  Definition mul  : Carrier -> Carrier -> Carrier := Qcmult.
  Definition neg  : Carrier -> Carrier := Qcopp.
  Definition inv  : Carrier -> Carrier := Qcinv.

  Definition carrier_eq_dec :
    forall a b : Carrier, {a = b} + {a <> b} := Qc_eq_dec.

  Theorem add_assoc  : forall a b c, add (add a b) c = add a (add b c).
  Proof. intros. unfold add. symmetry. apply Qcplus_assoc. Qed.

  Theorem add_comm   : forall a b, add a b = add b a.
  Proof. intros. unfold add. apply Qcplus_comm. Qed.

  Theorem add_zero_l : forall a, add zero a = a.
  Proof. intros. unfold add, zero. apply Qcplus_0_l. Qed.

  Theorem add_neg_l  : forall a, add (neg a) a = zero.
  Proof.
    intros. unfold add, neg, zero.
    rewrite Qcplus_comm. apply Qcplus_opp_r.
  Qed.

  Theorem mul_assoc  : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof. intros. unfold mul. symmetry. apply Qcmult_assoc. Qed.

  Theorem mul_one_l  : forall a, mul one a = a.
  Proof. intros. unfold mul, one. apply Qcmult_1_l. Qed.

  Theorem mul_one_r  : forall a, mul a one = a.
  Proof. intros. unfold mul, one. apply Qcmult_1_r. Qed.

  Theorem mul_zero_l : forall a, mul zero a = zero.
  Proof. intros. unfold mul, zero. apply Qcmult_0_l. Qed.

  Theorem mul_zero_r : forall a, mul a zero = zero.
  Proof. intros. unfold mul, zero. apply Qcmult_0_r. Qed.

  Theorem distrib_l : forall a b c,
    mul a (add b c) = add (mul a b) (mul a c).
  Proof. intros. unfold mul, add. apply Qcmult_plus_distr_r. Qed.

  Theorem distrib_r : forall a b c,
    mul (add a b) c = add (mul a c) (mul b c).
  Proof. intros. unfold mul, add. apply Qcmult_plus_distr_l. Qed.

  Theorem mul_comm : forall a b, mul a b = mul b a.
  Proof. intros. unfold mul. apply Qcmult_comm. Qed.

  Theorem mul_inv_r :
    forall a, a <> zero -> mul a (inv a) = one.
  Proof. intros. unfold mul, inv, one, zero in *. apply Qcmult_inv_r. exact H. Qed.

  Theorem one_neq_zero : one <> zero.
  Proof. unfold one, zero. intro H. inversion H. Qed.

End RationalField.
