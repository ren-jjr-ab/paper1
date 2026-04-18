(* ============================================== *)
(*  PureMarkerEntity                                *)
(*                                                  *)
(*  Existence without data — the minimal            *)
(*  inhabitant of ExistenceSig whose Entity has no  *)
(*  carrier-structured content at all. Just         *)
(*  viewpoints indexed by nat, with interact        *)
(*  advancing the index.                            *)
(*                                                  *)
(*  Entity := nat                                   *)
(*                                                  *)
(*    interact m n = m                  (if m = n)  *)
(*    interact m n = S (max m n)        (if m ≠ n)  *)
(*                                                  *)
(*    convention_eq m n = False                     *)
(*                                                  *)
(*  This inhabits ExistenceSig with zero reference  *)
(*  to any algebraic, set-theoretic, or             *)
(*  computational structure. The five axioms are    *)
(*  satisfied by pure viewpoint dynamics.           *)
(*                                                  *)
(*  Conceptual observation — why bother:            *)
(*                                                  *)
(*  The RingAsEntity functor packs every ring R     *)
(*  into                                            *)
(*                                                  *)
(*    Entity = REnt R.Carrier | Mark nat            *)
(*                                                  *)
(*  The Mark branch is closed under interact        *)
(*  (marker pairs stay markers, REnt–Mark produces  *)
(*  a marker too) and its internal dynamics never   *)
(*  touch R. So *every* Ring-as-Entity carries a    *)
(*  copy of the same Ring-independent marker        *)
(*  universe — and that universe is itself an       *)
(*  Existence. PureMarkerEntity is the standalone   *)
(*  extraction of that universe.                    *)
(*                                                  *)
(*  Framework reading: Entity = "data + viewpoint"  *)
(*  in every instance we have built. Pure markers   *)
(*  are the degenerate case data = ∅ — viewpoints   *)
(*  interacting with themselves. Minimal, but not   *)
(*  empty: the five axioms still hold.              *)
(* ============================================== *)

Require Import Existence.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module PureMarkerEntity <: ExistenceSig.

  Definition Entity : Type := nat.

  Definition interact (a b : Entity) : Entity :=
    match Nat.eq_dec a b with
    | left  _ => a
    | right _ => S (Nat.max a b)
    end.

  Definition convention_eq (_ _ : Entity) : Prop := False.


  (* ------------------------------------------- *)
  (*  AXIOM PROOFS                               *)
  (* ------------------------------------------- *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a. unfold interact.
    destruct (Nat.eq_dec a a) as [_ | H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply Nat.eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof. exists 0, 1. lia. Qed.

  Theorem interact_with :
    forall a : Entity, exists b : Entity, interact a b <> a.
  Proof.
    intros a. exists (S a). unfold interact.
    destruct (Nat.eq_dec a (S a)) as [Heq | _].
    - lia.
    - assert (Hmax : Nat.max a (S a) = S a) by lia.
      rewrite Hmax. intros H. lia.
  Qed.

  Theorem convention_not_derivable :
    forall a b : Entity,
      convention_eq a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof. intros a b []. Qed.

End PureMarkerEntity.


(* =========================================== *)
(*  CONCRETE WITNESSES                          *)
(* =========================================== *)

Example marker_zero_one :
  PureMarkerEntity.interact 0 1 = 2.
Proof. reflexivity. Qed.

Example marker_three_five :
  PureMarkerEntity.interact 3 5 = 6.
Proof. reflexivity. Qed.

Example marker_self :
  PureMarkerEntity.interact 7 7 = 7.
Proof. apply PureMarkerEntity.interact_self. Qed.

(* Markers strictly advance on every non-self interaction: there is   *)
(* no terminal marker.                                                *)

Example no_terminal_marker :
  forall a : PureMarkerEntity.Entity,
    exists b, PureMarkerEntity.interact a b <> a.
Proof. apply PureMarkerEntity.interact_with. Qed.
