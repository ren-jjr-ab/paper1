(* ============================================== *)
(*  Integer                                         *)
(*                                                  *)
(*  ℤ as an ExistenceSig instance via              *)
(*  RingAsExistence.Make applied to IntegerRing.    *)
(*                                                  *)
(*  Scenarios: basic reduction, negation branch,    *)
(*  nested reduction, landed-merge.                  *)
(* ============================================== *)

Require Import Existence.
Require Import RingAsExistence.
Require Import IntegerRing.
From Stdlib Require Import ZArith.


Module Integer := RingAsExistence.Make IntegerRing.IntegerRing.


(* --- framework axioms at Integer --- *)

Example int_self :
  forall a : Integer.Entity, Integer.interact a a = a.
Proof. apply Integer.interact_self. Qed.

Example int_has_partner :
  forall a : Integer.Entity, exists b, Integer.interact a b <> a.
Proof. apply Integer.interact_with. Qed.


(* --- reduction witnesses --- *)

(* 3 + 5 reduces to 8 in one step. *)
Example int_reduce_add :
  Integer.reduce_one (Integer.EAdd (Integer.EConst 3%Z) (Integer.EConst 5%Z))
  = Integer.EConst 8%Z.
Proof. reflexivity. Qed.

(* ENeg of a constant reduces. *)
Example int_reduce_neg :
  Integer.reduce_one (Integer.ENeg (Integer.EConst 3%Z))
  = Integer.EConst (-3)%Z.
Proof. reflexivity. Qed.


(* --- interact dynamics --- *)

(* Reducible + distinct viewpoint = one reduction step. *)
Example int_interact_add :
  Integer.interact
    (Integer.EAdd (Integer.EConst 3%Z) (Integer.EConst 5%Z))
    (Integer.EConst 0%Z)
  = Integer.EConst 8%Z.
Proof.
  unfold Integer.interact.
  destruct (Integer.entity_eq_dec _ _) as [H | _]; [inversion H|].
  destruct (Integer.entity_eq_dec _ _) as [H | _]; [inversion H|].
  reflexivity.
Qed.

(* Nested: (1+2)+5 takes one step to (3)+5. *)
Example int_nested_step1 :
  Integer.interact
    (Integer.EAdd
       (Integer.EAdd (Integer.EConst 1%Z) (Integer.EConst 2%Z))
       (Integer.EConst 5%Z))
    (Integer.EConst 0%Z)
  = Integer.EAdd (Integer.EConst 3%Z) (Integer.EConst 5%Z).
Proof.
  unfold Integer.interact.
  destruct (Integer.entity_eq_dec _ _) as [H | _]; [inversion H|].
  destruct (Integer.entity_eq_dec _ _) as [H | _]; [inversion H|].
  reflexivity.
Qed.

(* Landed (EConst) + structurally distinct viewpoint = EAdd merge. *)
Example int_landed_merges :
  Integer.interact
    (Integer.EConst 8%Z)
    (Integer.EAdd (Integer.EConst 0%Z) (Integer.EConst 0%Z))
  = Integer.EAdd
      (Integer.EConst 8%Z)
      (Integer.EAdd (Integer.EConst 0%Z) (Integer.EConst 0%Z)).
Proof.
  unfold Integer.interact.
  destruct (Integer.entity_eq_dec _ _) as [H | _]; [inversion H|].
  destruct (Integer.entity_eq_dec _ _) as [_ | Hne].
  - reflexivity.
  - exfalso. apply Hne. reflexivity.
Qed.
