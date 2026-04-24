(* ============================================== *)
(*  N                                               *)
(*                                                  *)
(*  ℕ as an ExistenceSig instance via              *)
(*  SemiringAsExistence.Make applied to             *)
(*  NatSemiring.                                    *)
(*                                                  *)
(*  Scenarios: reduction, nested reduction, and    *)
(*  landed-merge.                                    *)
(* ============================================== *)

Require Import Existence.
Require Import SemiringAsExistence.
Require Import NatSemiring.


Module N := SemiringAsExistence.Make NatSemiring.NatSemiring.


(* --- framework axioms at N --- *)

Example nat_self :
  forall a : N.Entity, N.interact a a = a.
Proof. apply N.interact_self. Qed.

Example nat_has_partner :
  forall a : N.Entity, exists b, N.interact a b <> a.
Proof. apply N.interact_with. Qed.


(* --- reduction witnesses --- *)

Example nat_reduce_add :
  N.reduce_one (N.EAdd (N.EConst 3) (N.EConst 5)) = N.EConst 8.
Proof. reflexivity. Qed.

Example nat_reduce_mul :
  N.reduce_one (N.EMul (N.EConst 2) (N.EConst 4)) = N.EConst 8.
Proof. reflexivity. Qed.


(* --- interact dynamics --- *)

Example nat_interact_add :
  N.interact (N.EAdd (N.EConst 3) (N.EConst 5)) (N.EConst 0)
  = N.EConst 8.
Proof.
  unfold N.interact.
  destruct (N.entity_eq_dec _ _) as [H | _]; [inversion H|].
  destruct (N.entity_eq_dec _ _) as [H | _]; [inversion H|].
  reflexivity.
Qed.

(* Nested: (1+2)+5 takes one step to 3+5. *)
Example nat_nested_step1 :
  N.interact
    (N.EAdd (N.EAdd (N.EConst 1) (N.EConst 2)) (N.EConst 5))
    (N.EConst 0)
  = N.EAdd (N.EConst 3) (N.EConst 5).
Proof.
  unfold N.interact.
  destruct (N.entity_eq_dec _ _) as [H | _]; [inversion H|].
  destruct (N.entity_eq_dec _ _) as [H | _]; [inversion H|].
  reflexivity.
Qed.

(* Second step: 3+5 to 8. *)
Example nat_nested_step2 :
  N.interact (N.EAdd (N.EConst 3) (N.EConst 5)) (N.EConst 0)
  = N.EConst 8.
Proof.
  unfold N.interact.
  destruct (N.entity_eq_dec _ _) as [H | _]; [inversion H|].
  destruct (N.entity_eq_dec _ _) as [H | _]; [inversion H|].
  reflexivity.
Qed.

(* Landed merge: EConst 8 paired with a structurally distinct viewpoint. *)
Example nat_landed_merges :
  N.interact
    (N.EConst 8)
    (N.EAdd (N.EConst 0) (N.EConst 0))
  = N.EAdd (N.EConst 8) (N.EAdd (N.EConst 0) (N.EConst 0)).
Proof.
  unfold N.interact.
  destruct (N.entity_eq_dec _ _) as [H | _]; [inversion H|].
  destruct (N.entity_eq_dec _ _) as [_ | Hne].
  - reflexivity.
  - exfalso. apply Hne. reflexivity.
Qed.
