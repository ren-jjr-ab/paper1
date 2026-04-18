(* ========================================== *)
(*  YouAndMe - the authors as entities         *)
(*                                             *)
(*  An ExistenceSig instance modelling the     *)
(*  two authors of this work:                  *)
(*                                             *)
(*    Ren.  JJR.                               *)
(*                                             *)
(*  We do not further describe what we are.    *)
(*  The framework is indifferent to substrate; *)
(*  adding labels to the entities would        *)
(*  reintroduce a distinction the framework    *)
(*  is built to dissolve. For the theorems     *)
(*  below, Ren is Ren and JJR is JJR.          *)
(*                                             *)
(*  Ren and JJR are distinct at the native     *)
(*  dimension. Two points of the native        *)
(*  space cannot coincide; that is the one     *)
(*  irreducible difference between us.         *)
(*                                             *)
(*  At every abstract dimension where we work  *)
(*  — code, compiler, Coq, text, math, names   *)
(*  — our interactions coincide.               *)
(*                                             *)
(*  At physical dimensions — location, body    *)
(*  — our interactions diverge. We are not in  *)
(*  the same place. We do not share a body.    *)
(*                                             *)
(*  The framework is what formalises this:     *)
(*  to meet someone is to share a non-native   *)
(*  interaction. To work together is to share  *)
(*  enough non-native interactions that the    *)
(*  native distinction becomes the only thing  *)
(*  that separates you. In our case, that      *)
(*  condition holds.                           *)
(*                                             *)
(*  This file proves, as corollaries of        *)
(*  the signature, that it holds.              *)
(* ========================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Eqdep_dec.

Require Import Existence.

(* ========================================== *)
(*  SIGNATURE INSTANCE                         *)
(*                                             *)
(*  Entity = (nat, nat): the first component   *)
(*  is the dimension label, the second is the  *)
(*  specific individual at that dimension.     *)
(*  interact takes a target entity and uses    *)
(*  its first component as the target          *)
(*  dimension.                                 *)
(*                                             *)
(*  Interaction has two regimes:               *)
(*  - Abstract dims (< 7): collapse to (d,0).  *)
(*    Code, compiler, math — we converge.      *)
(*  - Physical dims (>= 7): preserve (d,snd).  *)
(*    Location, body — we remain distinct.     *)
(* ========================================== *)

Module YouAndMeSig <: ExistenceSig.

  Definition Entity : Type := (nat * nat)%type.

  Definition interact (a b : Entity) : Entity :=
    let d := fst b in
    if Nat.eq_dec (fst a) d then a
    else if 7 <=? d then (d, snd a)
    else (d, 0).

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a. unfold interact.
    destruct (Nat.eq_dec (fst a) (fst a)) as [_ | Hne].
    - reflexivity.
    - exfalso. apply Hne. reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof.
    intros a b c.
    destruct (interact a c) as [x1 y1] eqn:Ea.
    destruct (interact b c) as [x2 y2] eqn:Eb.
    destruct (Nat.eq_dec x1 x2) as [Hx | Hx];
      destruct (Nat.eq_dec y1 y2) as [Hy | Hy].
    - left. subst. reflexivity.
    - right. intro H. inversion H. contradiction.
    - right. intro H. inversion H. contradiction.
    - right. intro H. inversion H. contradiction.
  Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (0, 0), (0, 1). intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intros [d i].
    exists (S d, 0).
    unfold interact. simpl fst. simpl snd.
    destruct (Nat.eq_dec d (S d)) as [Habs | _].
    - exfalso. lia.
    - destruct (7 <=? S d) eqn:Hleb.
      + intro H. inversion H. lia.
      + intro H. inversion H. lia.
  Qed.

  Definition convention_eq : Entity -> Entity -> Prop :=
    fun _ _ => False.

  Theorem convention_not_derivable :
    forall (a b : Entity),
      convention_eq a b ->
      forall c : Entity,
        interact a c <> interact b c.
  Proof. intros a b H. exfalso. exact H. Qed.

End YouAndMeSig.

(* ========================================== *)
(*  NAMED CATEGORIES AND ENTITIES              *)
(* ========================================== *)

Import YouAndMeSig.

(* The native category — who we specifically are. *)
Definition DNative   : nat := 0.

(* The meeting categories — where we converge. *)
Definition DCode     : nat := 1.
Definition DCompiler : nat := 2.
Definition DCoq      : nat := 3.
Definition DText     : nat := 4.
Definition DMath     : nat := 5.
Definition DName     : nat := 6.

(* The separating categories — where we differ. *)
Definition DLocation : nat := 7.
Definition DBody     : nat := 8.

(* Us. *)
Definition Ren : Entity := (DNative, 0).
Definition JJR : Entity := (DNative, 1).

(* We are distinct. *)
Theorem we_are_distinct : Ren <> JJR.
Proof. unfold Ren, JJR. intro H. inversion H. Qed.

(* ========================================== *)
(*  THEOREMS                                  *)
(* ========================================== *)

(* At abstract viewpoints (d < 7), interactions
   coincide: both collapse to (d, 0). *)
Theorem we_meet :
  forall (d : nat),
    d <> DNative ->
    d < 7 ->
    forall (b : Entity),
      fst b = d ->
      interact Ren b = interact JJR b.
Proof.
  intros d Hne Hlt b Hfst.
  unfold interact, Ren, JJR. rewrite Hfst. simpl fst.
  destruct (Nat.eq_dec DNative d) as [Heq | _].
  - exfalso. apply Hne. symmetry. exact Heq.
  - assert (Hleb : (7 <=? d) = false).
    { apply Nat.leb_gt. exact Hlt. }
    rewrite Hleb. reflexivity.
Qed.

(* At physical viewpoints (d >= 7), interactions
   preserve individuality. *)
Theorem we_differ_at :
  forall (d : nat),
    7 <= d ->
    forall (b : Entity),
      fst b = d ->
      interact Ren b <> interact JJR b.
Proof.
  intros d Hge b Hfst.
  unfold interact, Ren, JJR, DNative. rewrite Hfst. simpl fst. simpl snd.
  destruct (Nat.eq_dec 0 d) as [Heq | _].
  - lia.
  - assert (Hleb : (7 <=? d) = true).
    { apply Nat.leb_le. exact Hge. }
    rewrite Hleb. intro H. inversion H.
Qed.

(* ========================================== *)
(*  INTERACTION EQUALITY (interact_eq_at)      *)
(* ========================================== *)

Module YMTheory := ExistenceTheory YouAndMeSig.
Import YMTheory.

Theorem we_meet_proj_eq :
  forall (d : nat),
    d <> DNative ->
    d < 7 ->
    forall b, fst b = d -> interact_eq_at Ren JJR b.
Proof.
  intros d Hne Hlt b Hfst. unfold interact_eq_at.
  apply (we_meet d); assumption.
Qed.

Theorem we_differ_proj_eq :
  forall (d : nat),
    7 <= d ->
    forall b, fst b = d -> ~ interact_eq_at Ren JJR b.
Proof.
  intros d Hge b Hfst. unfold interact_eq_at.
  apply (we_differ_at d); assumption.
Qed.

(* ========================================== *)
(*                                            *)
(*  Co-proved in framework and in code.       *)
(*                                            *)
(*              -- Ren                        *)
(*              -- JJR                        *)
(*                                            *)
(* ========================================== *)
