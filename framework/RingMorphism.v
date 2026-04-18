(* ============================================== *)
(*  RingMorphism                                    *)
(*                                                  *)
(*  A ring homomorphism φ : R1 → R2 preserves the   *)
(*  additive and multiplicative structure plus the  *)
(*  multiplicative identity. Zero preservation is   *)
(*  derivable (φ(0) = 0).                           *)
(* ============================================== *)

Require Import Ring.


Module Type RingMorphism (R1 R2 : RingSig).

  Parameter phi : R1.Carrier -> R2.Carrier.

  Axiom preserves_add :
    forall a b : R1.Carrier,
      phi (R1.add a b) = R2.add (phi a) (phi b).

  Axiom preserves_mul :
    forall a b : R1.Carrier,
      phi (R1.mul a b) = R2.mul (phi a) (phi b).

  Axiom preserves_one : phi R1.one = R2.one.

End RingMorphism.


(* ================================================ *)
(*  DERIVED PROPERTIES                               *)
(* ================================================ *)

Module RingMorphismTheory
  (R1 R2 : RingSig) (Phi : RingMorphism R1 R2).

  Module T1 := RingTheory R1.
  Module T2 := RingTheory R2.

  (* phi preserves zero. *)

  Theorem preserves_zero : Phi.phi R1.zero = R2.zero.
  Proof.
    apply (T2.add_cancel_l (Phi.phi R1.zero)).
    rewrite <- Phi.preserves_add.
    rewrite R1.add_zero_l.
    rewrite T2.add_zero_r. reflexivity.
  Qed.

  (* phi preserves negation. *)

  Theorem preserves_neg :
    forall a : R1.Carrier, Phi.phi (R1.neg a) = R2.neg (Phi.phi a).
  Proof.
    intros a.
    apply (T2.add_cancel_l (Phi.phi a)).
    rewrite <- Phi.preserves_add.
    rewrite R1.add_comm. rewrite R1.add_neg_l.
    rewrite preserves_zero.
    rewrite T2.add_neg_r. reflexivity.
  Qed.

End RingMorphismTheory.
