(* ============================================== *)
(*  Semiring                                        *)
(*                                                  *)
(*  Commutative semiring axiomatization,            *)
(*  independent of ExistenceSig.                    *)
(*                                                  *)
(*  Three module types layered:                     *)
(*    SemiringSig           — additive commutative  *)
(*                            monoid (3) +          *)
(*                            multiplicative monoid *)
(*                            (3) + distributivity  *)
(*                            (2) + zero absorption *)
(*                            (2).                  *)
(*    CommSemiringSig       — adds mul_comm (1).    *)
(*    DecEqCommSemiringSig  — adds decidable        *)
(*                            Leibniz equality on   *)
(*                            the carrier.          *)
(*                                                  *)
(*  SemiringTheory exposes derived identities       *)
(*  every semiring satisfies.                       *)
(*                                                  *)
(*  Unlike Ring, a semiring has no additive         *)
(*  inverse, so mul_zero_l and mul_zero_r are       *)
(*  themselves axioms — they cannot be derived      *)
(*  from the remaining ring-style identities.       *)
(* ============================================== *)


Module Type SemiringSig.

  Parameter Carrier : Type.

  Parameter zero : Carrier.
  Parameter one  : Carrier.
  Parameter add  : Carrier -> Carrier -> Carrier.
  Parameter mul  : Carrier -> Carrier -> Carrier.

  (* Additive commutative monoid. *)
  Axiom add_assoc  : forall a b c, add (add a b) c = add a (add b c).
  Axiom add_comm   : forall a b,   add a b = add b a.
  Axiom add_zero_l : forall a,     add zero a = a.

  (* Multiplicative monoid. *)
  Axiom mul_assoc  : forall a b c, mul (mul a b) c = mul a (mul b c).
  Axiom mul_one_l  : forall a,     mul one a = a.
  Axiom mul_one_r  : forall a,     mul a one = a.

  (* Zero absorption. Not derivable without additive inverses. *)
  Axiom mul_zero_l : forall a, mul zero a = zero.
  Axiom mul_zero_r : forall a, mul a zero = zero.

  (* Distributivity. *)
  Axiom distrib_l  : forall a b c,
    mul a (add b c) = add (mul a b) (mul a c).
  Axiom distrib_r  : forall a b c,
    mul (add a b) c = add (mul a c) (mul b c).

End SemiringSig.


Module Type CommSemiringSig.
  Include SemiringSig.

  Axiom mul_comm : forall a b, mul a b = mul b a.
End CommSemiringSig.


Module Type DecEqCommSemiringSig.
  Include CommSemiringSig.

  Parameter carrier_eq_dec :
    forall a b : Carrier, {a = b} + {a <> b}.
End DecEqCommSemiringSig.


(* ================================================ *)
(*  DERIVED SEMIRING IDENTITIES                      *)
(* ================================================ *)

Module SemiringTheory (S : SemiringSig).

  Import S.

  (* Additive identity on the right. *)
  Theorem add_zero_r : forall a, add a zero = a.
  Proof.
    intros a. rewrite add_comm. apply add_zero_l.
  Qed.

End SemiringTheory.
