(* ============================================== *)
(*  LatticeExternalTimed — lattice-like op lifted  *)
(*                          to ExternalTimeSig     *)
(*                                                  *)
(*  Given an idempotent binary operation on a       *)
(*  type T with decidable equality and at least     *)
(*  two distinct values (LatticeSpec), produces an  *)
(*  ExternalTimeSig instance whose Entity is T      *)
(*  paired with an explicit time counter.           *)
(*                                                  *)
(*  Interaction semantics:                          *)
(*    self     → identity (no event).               *)
(*    non-self → apply op on value coord and        *)
(*               advance external_time by one.      *)
(*                                                  *)
(*  Every ExistenceSig axiom plus                   *)
(*  external_time_advances_on_nonself derives from  *)
(*  the three LatticeSpec obligations. No           *)
(*  absorbing-element concern: bottom value         *)
(*  entities still have movers through the          *)
(*  external_time coord.                            *)
(* ============================================== *)

Require Import Existence.
Require Import ExternalTime.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module Type LatticeSpec.
  Parameter T : Type.
  Parameter op : T -> T -> T.
  Axiom op_idempotent : forall a : T, op a a = a.
  Axiom eq_dec : forall a b : T, {a = b} + {a <> b}.
  Axiom exists_distinct : exists a b : T, a <> b.
End LatticeSpec.


Module Make (L : LatticeSpec) <: ExternalTimeSig.

  Definition Entity : Type := (L.T * nat)%type.

  Definition entity_eq_dec (a b : Entity) : {a = b} + {a <> b}.
  Proof.
    destruct a as [v1 t1]. destruct b as [v2 t2].
    destruct (L.eq_dec v1 v2) as [Hv | Hv].
    - destruct (Nat.eq_dec t1 t2) as [Ht | Ht].
      + left. subst. reflexivity.
      + right. intro H. injection H as _ Ht_eq. exact (Ht Ht_eq).
    - right. intro H. injection H as Hv_eq _. exact (Hv Hv_eq).
  Defined.

  Definition interact (a b : Entity) : Entity :=
    match entity_eq_dec a b with
    | left _  => a
    | right _ => (L.op (fst a) (fst b),
                  S (Nat.max (snd a) (snd b)))
    end.

  Definition convention_eq (_ _ : Entity) : Prop := False.

  Definition external_time (a : Entity) : nat := snd a.

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intro a. unfold interact.
    destruct (entity_eq_dec a a) as [Heq | Hne].
    - reflexivity.
    - exfalso. apply Hne. reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} +
      {interact a c <> interact b c}.
  Proof.
    intros a b c. apply entity_eq_dec.
  Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    destruct L.exists_distinct as [v1 [v2 Hne]].
    exists (v1, 0), (v2, 0).
    intro H. apply (f_equal fst) in H. simpl in H. exact (Hne H).
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b : Entity, interact a b <> a.
  Proof.
    intros [v t]. exists (v, S t). unfold interact.
    destruct (entity_eq_dec (v, t) (v, S t)) as [Heq | Hne].
    - apply (f_equal snd) in Heq. simpl in Heq. lia.
    - simpl. intro H.
      apply (f_equal snd) in H. simpl in H.
      assert (Hmax : Nat.max t (S t) = S t) by lia.
      rewrite Hmax in H. lia.
  Qed.

  Theorem convention_not_derivable :
    forall a b : Entity,
      convention_eq a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof.
    intros a b H. destruct H.
  Qed.

  Theorem external_time_advances_on_nonself :
    forall a c : Entity,
      interact a c <> a ->
      external_time (interact a c) > external_time a.
  Proof.
    intros a c Hne.
    unfold interact in Hne. unfold interact.
    destruct (entity_eq_dec a c) as [Heq | Hne_ac].
    - exfalso. apply Hne. reflexivity.
    - unfold external_time. simpl. lia.
  Qed.

End Make.
