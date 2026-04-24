(* ============================================== *)
(*  Field                                           *)
(*                                                  *)
(*  A commutative ring in which every non-zero     *)
(*  carrier has a multiplicative inverse.           *)
(*                                                  *)
(*  Three module types layered:                     *)
(*    FieldSig              — ring + inv +         *)
(*                            mul_inv_r.            *)
(*    DecEqFieldSig         — adds decidable       *)
(*                            Leibniz equality.    *)
(*                                                  *)
(*  inv is total: inv 0 is left unspecified by     *)
(*  the axiom, mirroring the usual convention.     *)
(* ============================================== *)

Require Import Ring.


Module Type FieldSig.
  Include CommRingSig.

  Parameter inv : Carrier -> Carrier.

  Axiom mul_inv_r :
    forall a, a <> zero -> mul a (inv a) = one.

  (* Non-triviality: one and zero are distinct. Trivial ring
     collapses the field structure. *)
  Axiom one_neq_zero : one <> zero.
End FieldSig.


Module Type DecEqFieldSig.
  Include FieldSig.

  Parameter carrier_eq_dec :
    forall a b : Carrier, {a = b} + {a <> b}.
End DecEqFieldSig.
