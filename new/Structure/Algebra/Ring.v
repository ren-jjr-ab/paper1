(* ============================================== *)
(*  Ring                                            *)
(*                                                  *)
(*  Commutative ring axiomatization, extending     *)
(*  the semiring hierarchy with an additive        *)
(*  inverse (neg) and the cancellation axiom.      *)
(*                                                  *)
(*  Three module types layered:                     *)
(*    RingSig              — semiring + neg +      *)
(*                           add_neg_l.            *)
(*    CommRingSig          — adds mul_comm.        *)
(*    DecEqCommRingSig     — adds decidable        *)
(*                           Leibniz equality.     *)
(*                                                  *)
(*  RingTheory exposes standard derived ring       *)
(*  identities.                                     *)
(*                                                  *)
(*  Ring is independent of ExistenceSig; the       *)
(*  bridge lives in RingAsExistence.                *)
(* ============================================== *)

Require Import Semiring.


Module Type RingSig.
  Include SemiringSig.

  Parameter neg : Carrier -> Carrier.
  Axiom add_neg_l : forall a, add (neg a) a = zero.
End RingSig.


Module Type CommRingSig.
  Include RingSig.

  Axiom mul_comm : forall a b, mul a b = mul b a.
End CommRingSig.


Module Type DecEqCommRingSig.
  Include CommRingSig.

  Parameter carrier_eq_dec :
    forall a b : Carrier, {a = b} + {a <> b}.
End DecEqCommRingSig.


(* ================================================ *)
(*  DERIVED RING IDENTITIES                          *)
(* ================================================ *)

Module RingTheory (R : RingSig).

  Import R.

  Theorem add_zero_r : forall a, add a zero = a.
  Proof.
    intros a. rewrite add_comm. apply add_zero_l.
  Qed.

  Theorem add_neg_r : forall a, add a (neg a) = zero.
  Proof.
    intros a. rewrite add_comm. apply add_neg_l.
  Qed.

  Theorem add_cancel_l :
    forall a b c, add a b = add a c -> b = c.
  Proof.
    intros a b c H.
    assert (H' : add (neg a) (add a b) = add (neg a) (add a c))
      by (rewrite H; reflexivity).
    rewrite <- add_assoc in H'. rewrite <- add_assoc in H'.
    rewrite add_neg_l in H'.
    rewrite add_zero_l in H'. rewrite add_zero_l in H'.
    exact H'.
  Qed.

  Theorem neg_involutive : forall a, neg (neg a) = a.
  Proof.
    intros a.
    apply (add_cancel_l (neg a)).
    rewrite add_neg_r. rewrite add_neg_l. reflexivity.
  Qed.

End RingTheory.
