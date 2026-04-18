(* ============================================== *)
(*  Ring                                            *)
(*                                                  *)
(*  Axiomatization of a (commutative) ring,          *)
(*  independent of ExistenceSig.                    *)
(*                                                  *)
(*  Two module types:                               *)
(*    RingSig       — not-necessarily-commutative   *)
(*                    ring. 9 axioms: additive      *)
(*                    abelian group (4) +           *)
(*                    multiplicative monoid (3) +   *)
(*                    distributivity (2).           *)
(*    CommRingSig   — commutative ring. Adds 1      *)
(*                    axiom (mul_comm) to RingSig.  *)
(*                                                  *)
(*  RingTheory exposes the standard derived         *)
(*  identities that every ring satisfies.           *)
(*                                                  *)
(*  Ring lives alongside ExistenceSig, not under    *)
(*  it: a single concrete Entity may inhabit both,  *)
(*  but neither depends on the other at the         *)
(*  signature level. The framework's interact       *)
(*  axis and a ring's algebraic axis are parallel   *)
(*  languages over the same Carrier.                *)
(* ============================================== *)


Module Type RingSig.

  Parameter Carrier : Type.

  Parameter zero : Carrier.
  Parameter one  : Carrier.
  Parameter add  : Carrier -> Carrier -> Carrier.
  Parameter mul  : Carrier -> Carrier -> Carrier.
  Parameter neg  : Carrier -> Carrier.

  (* Additive abelian group. *)
  Axiom add_assoc  : forall a b c, add (add a b) c = add a (add b c).
  Axiom add_comm   : forall a b,   add a b = add b a.
  Axiom add_zero_l : forall a,     add zero a = a.
  Axiom add_neg_l  : forall a,     add (neg a) a = zero.

  (* Multiplicative monoid. *)
  Axiom mul_assoc  : forall a b c, mul (mul a b) c = mul a (mul b c).
  Axiom mul_one_l  : forall a,     mul one a = a.
  Axiom mul_one_r  : forall a,     mul a one = a.

  (* Distributivity. *)
  Axiom distrib_l  : forall a b c,
    mul a (add b c) = add (mul a b) (mul a c).
  Axiom distrib_r  : forall a b c,
    mul (add a b) c = add (mul a c) (mul b c).

End RingSig.


Module Type CommRingSig.
  Include RingSig.

  (* Commutative extension. *)
  Axiom mul_comm : forall a b, mul a b = mul b a.
End CommRingSig.


(* ================================================ *)
(*  DECIDABLE-EQUALITY COMMUTATIVE RING              *)
(*                                                   *)
(*  Strengthens CommRingSig with decidable Leibniz   *)
(*  equality on the carrier. This is what the       *)
(*  PolynomialRing functor requires to normalize    *)
(*  polynomials (strip trailing zeros).              *)
(* ================================================ *)

Module Type DecEqCommRingSig.
  Include CommRingSig.
  Parameter carrier_eq_dec : forall a b : Carrier, {a = b} + {a <> b}.
End DecEqCommRingSig.


(* ================================================ *)
(*  DERIVED RING IDENTITIES                          *)
(* ================================================ *)

Module RingTheory (R : RingSig).

  Import R.

  (* Additive identity on the right. *)

  Theorem add_zero_r : forall a, add a zero = a.
  Proof.
    intros a. rewrite add_comm. apply add_zero_l.
  Qed.

  (* Additive inverse on the right. *)

  Theorem add_neg_r : forall a, add a (neg a) = zero.
  Proof.
    intros a. rewrite add_comm. apply add_neg_l.
  Qed.

  (* Cancellation of addition. *)

  Theorem add_cancel_l :
    forall a b c, add a b = add a c -> b = c.
  Proof.
    intros a b c H.
    assert (H' : add (neg a) (add a b) = add (neg a) (add a c)).
    { rewrite H. reflexivity. }
    rewrite <- add_assoc in H'. rewrite <- add_assoc in H'.
    rewrite add_neg_l in H'.
    rewrite add_zero_l in H'. rewrite add_zero_l in H'.
    exact H'.
  Qed.

  (* Zero absorbs under multiplication (left). *)

  Theorem mul_zero_l : forall a, mul zero a = zero.
  Proof.
    intros a.
    assert (H : mul zero a = add (mul zero a) (mul zero a)).
    { rewrite <- distrib_r. rewrite add_zero_l. reflexivity. }
    apply (add_cancel_l (mul zero a)).
    rewrite add_zero_r. symmetry. exact H.
  Qed.

  (* Zero absorbs under multiplication (right). *)

  Theorem mul_zero_r : forall a, mul a zero = zero.
  Proof.
    intros a.
    assert (H : mul a zero = add (mul a zero) (mul a zero)).
    { rewrite <- distrib_l. rewrite add_zero_l. reflexivity. }
    apply (add_cancel_l (mul a zero)).
    rewrite add_zero_r. symmetry. exact H.
  Qed.

  (* Negation commutes with multiplication (left). *)

  Theorem mul_neg_l : forall a b, mul (neg a) b = neg (mul a b).
  Proof.
    intros a b.
    apply (add_cancel_l (mul a b)).
    rewrite add_neg_r.
    rewrite <- distrib_r.
    rewrite add_neg_r.
    apply mul_zero_l.
  Qed.

  (* Negation is an involution. *)

  Theorem neg_involutive : forall a, neg (neg a) = a.
  Proof.
    intros a.
    apply (add_cancel_l (neg a)).
    rewrite add_neg_r. rewrite add_neg_l. reflexivity.
  Qed.

End RingTheory.
