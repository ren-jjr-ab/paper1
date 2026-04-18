(* ============================================== *)
(*  IntegerGrothendieck                             *)
(*                                                  *)
(*  Two ExistenceSig instances used together to     *)
(*  realize the Grothendieck construction           *)
(*                                                  *)
(*      ℤ = ℕ² / ~    where                         *)
(*      (a, b) ~ (c, d)  iff  a + d = b + c         *)
(*                                                  *)
(*  as a framework kernel quotient.                 *)
(*                                                  *)
(*  NatPair carries entities (d, (a, b)) where a    *)
(*  and b are natural numbers and d is a dimension  *)
(*  label. Integer carries entities (d, z) where z  *)
(*  is a Coq integer.                               *)
(*                                                  *)
(*  Interact on both is dim-dispatched: at the      *)
(*  self dim interact is identity; at a foreign     *)
(*  dim interact moves the payload into the new    *)
(*  dim coordinate. This is the "pure projection"  *)
(*  regime — no cost accumulation, no external      *)
(*  time advance — which leaves room for a non-    *)
(*  trivial preserves_interact morphism whose      *)
(*  kernel is exactly the Grothendieck relation.   *)
(*                                                  *)
(*  The cross-instance morphism and the            *)
(*  Factorization demo live in                      *)
(*  results/IntegerGrothendieckFactorization.v.    *)
(* ============================================== *)

Require Import Existence.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.


(* ================================================ *)
(*  NATPAIR — entities (d, (a, b))                   *)
(* ================================================ *)

Module NatPair <: ExistenceSig.

  Definition Entity : Type := (nat * (nat * nat))%type.

  Definition interact (x y : Entity) : Entity :=
    if Nat.eq_dec (fst x) (fst y) then x
    else (fst y, snd x).

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a. unfold interact.
    destruct (Nat.eq_dec (fst a) (fst a)) as [_ | H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof.
    intros a b c.
    destruct (interact a c) as [d1 p1] eqn:E1.
    destruct (interact b c) as [d2 p2] eqn:E2.
    destruct (Nat.eq_dec d1 d2) as [Hd | Hd];
      destruct p1 as [a1 b1]; destruct p2 as [a2 b2];
      destruct (Nat.eq_dec a1 a2) as [Ha | Ha];
      destruct (Nat.eq_dec b1 b2) as [Hb | Hb].
    all: try (left; subst; reflexivity).
    all: right; intros H; inversion H; contradiction.
  Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (0, (0, 0)), (0, (1, 0)).
    intros H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intros [d p]. exists (S d, p).
    unfold interact. simpl.
    destruct (Nat.eq_dec d (S d)) as [Habs | _].
    - lia.
    - intros H. inversion H. lia.
  Qed.

  Definition convention_eq : Entity -> Entity -> Prop := fun _ _ => False.

  Theorem convention_not_derivable :
    forall a b : Entity,
      convention_eq a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof. intros a b H. destruct H. Qed.

End NatPair.


(* ================================================ *)
(*  INTEGER — entities (d, z : Z)                    *)
(* ================================================ *)

Module Integer <: ExistenceSig.

  Definition Entity : Type := (nat * Z)%type.

  Definition interact (x y : Entity) : Entity :=
    if Nat.eq_dec (fst x) (fst y) then x
    else (fst y, snd x).

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a. unfold interact.
    destruct (Nat.eq_dec (fst a) (fst a)) as [_ | H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof.
    intros a b c.
    destruct (interact a c) as [d1 z1] eqn:E1.
    destruct (interact b c) as [d2 z2] eqn:E2.
    destruct (Nat.eq_dec d1 d2) as [Hd | Hd];
      destruct (Z.eq_dec z1 z2) as [Hz | Hz].
    - left. subst. reflexivity.
    - right. intros H. inversion H. contradiction.
    - right. intros H. inversion H. contradiction.
    - right. intros H. inversion H. contradiction.
  Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (0%nat, 0%Z), (0%nat, 1%Z).
    intros H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intros [d z]. exists (S d, z).
    unfold interact. simpl.
    destruct (Nat.eq_dec d (S d)) as [Habs | _].
    - lia.
    - intros H. inversion H. lia.
  Qed.

  Definition convention_eq : Entity -> Entity -> Prop := fun _ _ => False.

  Theorem convention_not_derivable :
    forall a b : Entity,
      convention_eq a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof. intros a b H. destruct H. Qed.

End Integer.
