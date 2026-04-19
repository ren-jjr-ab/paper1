(* ================================================ *)
(*  ObjectMirror                                     *)
(*                                                   *)
(*  A physics-flavoured Entity pair that exhibits    *)
(*  the framework's directional asymmetry of         *)
(*  observation head-on.                             *)
(*                                                   *)
(*  Entity = Object (intensity, time)                *)
(*         | Mirror (reflection coefficient, time)   *)
(*                                                   *)
(*  Reflection rules (asymmetric by design):         *)
(*                                                   *)
(*    interact (Object i) (Mirror r)                 *)
(*      = Object (i·r / 100)      [high fidelity]    *)
(*                                                   *)
(*    interact (Mirror r) (Object i)                 *)
(*      = Mirror (r / 10)         [sharp decay]      *)
(*                                                   *)
(*  Physical reading: an object viewed through a     *)
(*  mirror reflects at the mirror's coefficient      *)
(*  (close to 100% for a good mirror). A mirror      *)
(*  viewed through an object loses almost all of     *)
(*  its reflection signal — objects do not reflect   *)
(*  mirrors well.                                    *)
(*                                                   *)
(*  Other instances on the Entity stage are built    *)
(*  on commutative operations (add, mul, union,      *)
(*  intersect) and so conceal the fact that          *)
(*  `interact` in ExistenceSig has no symmetry       *)
(*  axiom. ObjectMirror makes that asymmetry         *)
(*  visible: `interact a b <> interact b a` in       *)
(*  general, and often differs in *constructor* —    *)
(*  the source's shape persists through reflection.  *)
(* ================================================ *)

Require Import Existence.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module ObjectMirror <: ExistenceSig.

  Inductive _Entity : Type :=
    | Object : nat -> nat -> _Entity
    | Mirror : nat -> nat -> _Entity.

  Definition Entity : Type := _Entity.

  Definition entity_eq_dec : forall a b : Entity, {a = b} + {a <> b}.
  Proof.
    intros [ia ta | ra ta] [ib tb | rb tb].
    - destruct (Nat.eq_dec ia ib); destruct (Nat.eq_dec ta tb);
        try (left; subst; reflexivity);
        try (right; intros H; inversion H; contradiction).
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - destruct (Nat.eq_dec ra rb); destruct (Nat.eq_dec ta tb);
        try (left; subst; reflexivity);
        try (right; intros H; inversion H; contradiction).
  Defined.

  Definition interact (a b : Entity) : Entity :=
    match entity_eq_dec a b with
    | left  _ => a
    | right _ =>
        match a, b with
        | Object i t, Mirror r t' =>
            (* Object seen through Mirror: attenuated by mirror's coeff *)
            Object ((i * r) / 100) (S (Nat.max t t'))
        | Mirror r t, Object _ t' =>
            (* Mirror seen through Object: sharp decay of reflection *)
            Mirror (r / 10) (S (Nat.max t t'))
        | Object i t, Object _ t' =>
            (* Object-Object: source object's intensity survives *)
            Object i (S (Nat.max t t'))
        | Mirror r t, Mirror r' t' =>
            (* Mirror-Mirror: weaker coefficient dominates *)
            Mirror (Nat.min r r') (S (Nat.max t t'))
        end
    end.

  Definition convention_eq (_ _ : Entity) : Prop := False.


  (* ------------------------------------------- *)
  (*  AXIOM PROOFS                               *)
  (* ------------------------------------------- *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a. unfold interact.
    destruct (entity_eq_dec a a) as [_ | H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply entity_eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (Object 0 0), (Mirror 0 0).
    intros H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b : Entity, interact a b <> a.
  Proof.
    intros [i t | r t].
    - (* Object i t: partner is Mirror 100 t (perfect reflection) *)
      exists (Mirror 100 t). unfold interact.
      destruct (entity_eq_dec (Object i t) (Mirror 100 t)) as [Heq | _].
      + inversion Heq.
      + intros H. inversion H. lia.
    - (* Mirror r t: partner is Object 0 t *)
      exists (Object 0 t). unfold interact.
      destruct (entity_eq_dec (Mirror r t) (Object 0 t)) as [Heq | _].
      + inversion Heq.
      + intros H. inversion H. lia.
  Qed.

  Theorem convention_not_derivable :
    forall a b : Entity,
      convention_eq a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof. intros a b []. Qed.

End ObjectMirror.


(* =========================================== *)
(*  WITNESSES — THE ASYMMETRY, LITERAL          *)
(* =========================================== *)

(* Different constructor on each side of the asymmetry: *)
(* Object-through-Mirror preserves Object-ness, Mirror-through-Object *)
(* preserves Mirror-ness. Neither interact collapses the other's form. *)

Example observation_asymmetry_constructor :
  ObjectMirror.interact (ObjectMirror.Object 80 0)
                         (ObjectMirror.Mirror 100 0)
  <>
  ObjectMirror.interact (ObjectMirror.Mirror 100 0)
                         (ObjectMirror.Object 80 0).
Proof.
  unfold ObjectMirror.interact. simpl.
  intros H. inversion H.
Qed.

(* Concrete values on each side — the physical picture made arithmetic. *)

Example object_through_perfect_mirror :
  ObjectMirror.interact (ObjectMirror.Object 80 0)
                         (ObjectMirror.Mirror 100 0)
  = ObjectMirror.Object 80 1.
Proof. reflexivity. Qed.

Example mirror_through_object_decays :
  ObjectMirror.interact (ObjectMirror.Mirror 100 0)
                         (ObjectMirror.Object 80 0)
  = ObjectMirror.Mirror 10 1.
Proof. reflexivity. Qed.

(* Dark mirror: reflection coefficient 0 erases the object's intensity. *)

Example object_through_dark_mirror :
  ObjectMirror.interact (ObjectMirror.Object 80 0)
                         (ObjectMirror.Mirror 0 0)
  = ObjectMirror.Object 0 1.
Proof. reflexivity. Qed.

(* Mirror decay under repeated observation through an object:           *)
(*   100 → 10 → 1 → 0.                                                  *)
(* Three interacts with any Object drive the Mirror's coefficient to 0. *)

Example mirror_decay_chain :
  ObjectMirror.interact
    (ObjectMirror.interact
      (ObjectMirror.interact (ObjectMirror.Mirror 100 0)
                              (ObjectMirror.Object 0 0))
      (ObjectMirror.Object 0 0))
    (ObjectMirror.Object 0 0)
  = ObjectMirror.Mirror 0 3.
Proof. reflexivity. Qed.

(* Object-Object interaction preserves intensity regardless of counterpart. *)

Example object_object_preserves_intensity :
  ObjectMirror.interact (ObjectMirror.Object 42 0)
                         (ObjectMirror.Object 7 0)
  = ObjectMirror.Object 42 1.
Proof. reflexivity. Qed.

(* Mirror-Mirror interaction: weaker coefficient dominates. *)

Example mirror_mirror_weaker_wins :
  ObjectMirror.interact (ObjectMirror.Mirror 90 0)
                         (ObjectMirror.Mirror 30 0)
  = ObjectMirror.Mirror 30 1.
Proof. reflexivity. Qed.


(* =========================================== *)
(*  REMARK                                      *)
(*                                              *)
(*  framework/Existence.v declares `interact`   *)
(*  as a binary operation with no symmetry or   *)
(*  commutativity requirement. Every instance   *)
(*  before this file was built on commutative   *)
(*  algebra (+, ·, ∪, ∩) and inherited an       *)
(*  accidental interact-symmetry that hid the   *)
(*  framework's actual latitude.                *)
(*                                              *)
(*  ObjectMirror is the minimal instance where  *)
(*  interact is genuinely directional: observe- *)
(*  ing an object through a mirror yields a     *)
(*  different entity (in shape and in value)    *)
(*  from observing a mirror through an object.  *)
(*  This is the framework telling us that       *)
(*  "observation" is not the symmetric kernel   *)
(*  of interaction; it is a directed passage.   *)
(* =========================================== *)
