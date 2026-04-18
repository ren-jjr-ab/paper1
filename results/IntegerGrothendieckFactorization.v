(* ============================================== *)
(*  IntegerGrothendieckFactorization                *)
(*                                                  *)
(*  Realize the Grothendieck construction           *)
(*                                                  *)
(*      ℤ = ℕ² / ~    (a, b) ~ (c, d)               *)
(*                      iff  a + d = b + c          *)
(*                                                  *)
(*  as a framework Factorization.                   *)
(*                                                  *)
(*     phi : NatPair → Integer                      *)
(*     phi (d, (a, b)) = (d, a - b) in ℤ            *)
(*                                                  *)
(*  Properties proved here:                         *)
(*                                                  *)
(*   - phi preserves_interact (trivially, because   *)
(*     interact on both instances is pure           *)
(*     dim-dispatch and phi preserves dim).         *)
(*                                                  *)
(*   - phi is non-injective with explicit           *)
(*     witnesses: (0, (1, 0)) and (0, (2, 1)) both  *)
(*     map to (0, +1). The kernel relation agrees   *)
(*     with Grothendieck's a + d = b + c.           *)
(*                                                  *)
(*   - phi is surjective onto Integer.              *)
(*                                                  *)
(*   - The Factorization's phi_hat is therefore    *)
(*     an isomorphism: NatPair/ker ≅ Integer. This  *)
(*     is the framework statement of ℤ = ℕ² / ~.   *)
(*                                                  *)
(*  Contrast with the intra-RR / intra-CR case:     *)
(*  there, external_time advance forced all         *)
(*  non-injective preserves_interact morphisms to   *)
(*  be essentially constant. Here, by using the     *)
(*  pure-projection regime, we obtain a natural     *)
(*  partial quotient that coincides with a          *)
(*  textbook algebraic construction.                *)
(* ============================================== *)

Require Existence.
Require ExistenceMorphism.
Require ExistencePullback.
Require ExistencePushout.
Require ExistenceFactorization.
Require IntegerGrothendieck.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module NP := IntegerGrothendieck.NatPair.
Module IZ := IntegerGrothendieck.Integer.


(* ================================================ *)
(*  THE MORPHISM                                     *)
(* ================================================ *)

Module PhiNPIZ <: ExistencePullback.MorphismInto NP IZ.

  Definition phi (x : NP.Entity) : IZ.Entity :=
    let '(d, (a, b)) := x in
    (d, (Z.of_nat a - Z.of_nat b)%Z).

  Theorem preserves_interact :
    forall a b : NP.Entity,
      phi (NP.interact a b) = IZ.interact (phi a) (phi b).
  Proof.
    intros [da [aa ab]] [db [ba bb]].
    unfold phi, NP.interact, IZ.interact. simpl.
    destruct (Nat.eq_dec da db) as [Hd | Hd]; reflexivity.
  Qed.

End PhiNPIZ.


(* ================================================ *)
(*  NON-INJECTIVE WITNESSES                          *)
(* ================================================ *)

Example phi_collapses_1_0_and_2_1 :
  PhiNPIZ.phi (0%nat, (1%nat, 0%nat)) =
  PhiNPIZ.phi (0%nat, (2%nat, 1%nat)).
Proof. unfold PhiNPIZ.phi. simpl. reflexivity. Qed.

Example phi_collapses_3_1_and_5_3 :
  PhiNPIZ.phi (0%nat, (3%nat, 1%nat)) =
  PhiNPIZ.phi (0%nat, (5%nat, 3%nat)).
Proof. unfold PhiNPIZ.phi. simpl. reflexivity. Qed.

Example phi_collapses_0_2_and_1_3 :
  PhiNPIZ.phi (0%nat, (0%nat, 2%nat)) =
  PhiNPIZ.phi (0%nat, (1%nat, 3%nat)).
Proof. unfold PhiNPIZ.phi. simpl. reflexivity. Qed.

(* Pairs with different dims do not collapse. *)

Example phi_separates_different_dims :
  PhiNPIZ.phi (0%nat, (1%nat, 0%nat)) <>
  PhiNPIZ.phi (1%nat, (1%nat, 0%nat)).
Proof. intros H. inversion H. Qed.

(* Pairs at same dim with different Grothendieck values
   do not collapse. *)

Example phi_separates_0_and_1 :
  PhiNPIZ.phi (0%nat, (1%nat, 1%nat)) <>
  PhiNPIZ.phi (0%nat, (2%nat, 1%nat)).
Proof. intros H. inversion H. Qed.


(* ================================================ *)
(*  KERNEL AGREES WITH GROTHENDIECK RELATION         *)
(* ================================================ *)

Module Fact :=
  ExistenceFactorization.Factorization NP IZ PhiNPIZ.

(* ker at same dim iff a + d = b + c (Grothendieck). *)

Theorem ker_same_dim_iff_grothendieck :
  forall (d : nat) (a b c d' : nat),
    Fact.ker (d, (a, b)) (d, (c, d')) <->
    (a + d' = b + c)%nat.
Proof.
  intros d a b c d'. unfold Fact.ker, PhiNPIZ.phi.
  split.
  - intros H. inversion H as [Hz]. lia.
  - intros Heq. f_equal. lia.
Qed.

(* Kernel rejects different dims. *)

Theorem ker_different_dims :
  forall (d1 d2 : nat) (p1 p2 : nat * nat),
    d1 <> d2 -> ~ Fact.ker (d1, p1) (d2, p2).
Proof.
  intros d1 d2 [a b] [c d'] Hne Hker.
  unfold Fact.ker, PhiNPIZ.phi in Hker.
  inversion Hker. contradiction.
Qed.


(* ================================================ *)
(*  PHI IS SURJECTIVE                                *)
(*                                                   *)
(*  Every (d, z) ∈ Integer is phi of some pair:     *)
(*    z ≥ 0: (d, (z, 0))                            *)
(*    z < 0: (d, (0, -z))                           *)
(* ================================================ *)

Theorem phi_surjective :
  forall b : IZ.Entity, exists a : NP.Entity, PhiNPIZ.phi a = b.
Proof.
  intros [d z]. unfold PhiNPIZ.phi.
  destruct z as [ | p | p ].
  - exists (d, (0%nat, 0%nat)). simpl. reflexivity.
  - exists (d, (Pos.to_nat p, 0%nat)). simpl.
    f_equal. rewrite positive_nat_Z. lia.
  - exists (d, (0%nat, Pos.to_nat p)). simpl.
    f_equal. rewrite positive_nat_Z. lia.
Qed.


(* ================================================ *)
(*  PHI_HAT IS AN ISOMORPHISM                        *)
(*                                                   *)
(*  NatPair/ker ≅ Integer via phi_hat.              *)
(* ================================================ *)

Theorem phi_hat_is_iso :
  (forall x y,
    Fact.phi_hat (Fact.interact x y) =
    IZ.interact (Fact.phi_hat x) (Fact.phi_hat y)) /\
  (forall b, exists x, Fact.phi_hat x = b) /\
  (forall x y, Fact.phi_hat x = Fact.phi_hat y -> x = y).
Proof.
  apply Fact.phi_hat_is_iso_if_phi_surjective.
  exact phi_surjective.
Qed.

(* The factorization triangle commutes. *)

Theorem grothendieck_factorization :
  forall a : NP.Entity,
    PhiNPIZ.phi a = Fact.phi_hat (Fact.cls a).
Proof. exact Fact.factorization. Qed.


(* ================================================ *)
(*  EXPLICIT QUOTIENT MEMBERSHIPS                    *)
(*                                                   *)
(*  The collapses above promoted from phi-equality   *)
(*  to cls-equality in the quotient.                 *)
(* ================================================ *)

Theorem cls_1_0_eq_cls_2_1 :
  Fact.cls (0%nat, (1%nat, 0%nat)) = Fact.cls (0%nat, (2%nat, 1%nat)).
Proof.
  apply Fact.cls_correct. exact phi_collapses_1_0_and_2_1.
Qed.

Theorem cls_3_1_eq_cls_5_3 :
  Fact.cls (0%nat, (3%nat, 1%nat)) = Fact.cls (0%nat, (5%nat, 3%nat)).
Proof.
  apply Fact.cls_correct. exact phi_collapses_3_1_and_5_3.
Qed.

Theorem cls_different_dims_distinct :
  Fact.cls (0%nat, (1%nat, 0%nat)) <> Fact.cls (1%nat, (1%nat, 0%nat)).
Proof.
  intros H. apply Fact.cls_correct in H.
  unfold Fact.ker, PhiNPIZ.phi in H.
  inversion H.
Qed.
