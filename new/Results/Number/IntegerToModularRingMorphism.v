(* ============================================== *)
(*  IntegerToModularRingMorphism                    *)
(*                                                  *)
(*  The canonical ring homomorphism                 *)
(*                                                  *)
(*    phi : ℤ → ℤ/7ℤ                                *)
(*    phi(z) = z mod 7                              *)
(*                                                  *)
(*  Implemented via Mod7Ring.canonicalize, which    *)
(*  is exactly Z.modulo 7 wrapped into the          *)
(*  canonical subset type.                          *)
(*                                                  *)
(*  Preservation of add/mul/one reduces to Coq's    *)
(*  standard modular arithmetic lemmas (Z.add_mod,  *)
(*  Z.mul_mod).                                     *)
(* ============================================== *)

Require Import Ring.
Require Import RingMorphism.
Require IntegerRing.
Require ModularRing.
From Stdlib Require Import ZArith.


Module IntegerToMod7 <:
  RingMorphism IntegerRing.IntegerRing ModularRing.Mod7Ring.

  Definition phi (z : IntegerRing.IntegerRing.Carrier)
    : ModularRing.Mod7Ring.Carrier :=
    ModularRing.Mod7Ring.canonicalize z.

  Theorem preserves_add :
    forall a b : IntegerRing.IntegerRing.Carrier,
      phi (IntegerRing.IntegerRing.add a b) =
      ModularRing.Mod7Ring.add (phi a) (phi b).
  Proof.
    intros a b.
    apply ModularRing.Mod7Ring.sig_eq_by_value. simpl.
    apply Z.add_mod. apply ModularRing.Mod7Ring.n_nonzero.
  Qed.

  Theorem preserves_mul :
    forall a b : IntegerRing.IntegerRing.Carrier,
      phi (IntegerRing.IntegerRing.mul a b) =
      ModularRing.Mod7Ring.mul (phi a) (phi b).
  Proof.
    intros a b.
    apply ModularRing.Mod7Ring.sig_eq_by_value. simpl.
    apply Z.mul_mod. apply ModularRing.Mod7Ring.n_nonzero.
  Qed.

  Theorem preserves_one :
    phi IntegerRing.IntegerRing.one = ModularRing.Mod7Ring.one.
  Proof. reflexivity. Qed.

End IntegerToMod7.


(* ================================================ *)
(*  CONCRETE RESIDUE WITNESSES                       *)
(* ================================================ *)

Example phi_0 : proj1_sig (IntegerToMod7.phi 0%Z) = 0%Z.
Proof. reflexivity. Qed.

Example phi_7 : proj1_sig (IntegerToMod7.phi 7%Z) = 0%Z.
Proof. reflexivity. Qed.

Example phi_14 : proj1_sig (IntegerToMod7.phi 14%Z) = 0%Z.
Proof. reflexivity. Qed.

Example phi_neg1 : proj1_sig (IntegerToMod7.phi (-1)%Z) = 6%Z.
Proof. reflexivity. Qed.

Example phi_100 : proj1_sig (IntegerToMod7.phi 100%Z) = 2%Z.
Proof. reflexivity. Qed.


(* ================================================ *)
(*  DERIVED: preserves_zero, preserves_neg          *)
(* ================================================ *)

Module IntegerToMod7_Theory :=
  RingMorphismTheory
    IntegerRing.IntegerRing
    ModularRing.Mod7Ring
    IntegerToMod7.
