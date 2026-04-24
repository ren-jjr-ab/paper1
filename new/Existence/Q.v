(* ============================================== *)
(*  Q                                               *)
(*                                                  *)
(*  ℚ as an ExistenceSig instance via              *)
(*  FieldAsExistence.Make applied to RationalField. *)
(*                                                  *)
(*  Scenarios exercise the two interact branches    *)
(*  (reduction and landed-merge) and the inverse    *)
(*  contraction unique to fields.                   *)
(* ============================================== *)

Require Import Existence.
Require Import FieldAsExistence.
Require Import RationalField.
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qcanon.


Module Q := FieldAsExistence.Make RationalField.RationalField.


(* --- framework axioms at Q --- *)

Example q_self :
  forall a : Q.Entity, Q.interact a a = a.
Proof. apply Q.interact_self. Qed.

Example q_has_partner :
  forall a : Q.Entity, exists b, Q.interact a b <> a.
Proof. apply Q.interact_with. Qed.

Example q_existence : exists a b : Q.Entity, a <> b.
Proof. apply Q.existence. Qed.


(* --- reduction witnesses --- *)

(* Addition of two constants contracts to their sum. *)
Example q_reduce_add :
  Q.reduce_one (Q.EAdd (Q.EConst 1%Qc) (Q.EConst 1%Qc))
  = Q.EConst (1 + 1)%Qc.
Proof. reflexivity. Qed.

(* Multiplication contracts. *)
Example q_reduce_mul :
  Q.reduce_one (Q.EMul (Q.EConst (Q2Qc 2)) (Q.EConst (Q2Qc 3)))
  = Q.EConst (Q2Qc 2 * Q2Qc 3)%Qc.
Proof. reflexivity. Qed.

(* Negation contracts. *)
Example q_reduce_neg :
  Q.reduce_one (Q.ENeg (Q.EConst 1%Qc)) = Q.EConst (Qcopp 1%Qc).
Proof. reflexivity. Qed.

(* Inversion contracts (the field-specific operator). *)
Example q_reduce_inv :
  Q.reduce_one (Q.EInv (Q.EConst (Q2Qc 2)))
  = Q.EConst (Qcinv (Q2Qc 2)).
Proof. reflexivity. Qed.


(* --- interact dynamics --- *)

(* Reducible entity + distinct viewpoint = one reduction step. *)
Example q_interact_reduces :
  Q.interact
    (Q.EAdd (Q.EConst 1%Qc) (Q.EConst 1%Qc))
    (Q.EConst 0%Qc)
  = Q.EConst (1 + 1)%Qc.
Proof.
  unfold Q.interact.
  destruct (Q.entity_eq_dec _ _) as [Heq | _]; [inversion Heq|].
  destruct (Q.entity_eq_dec _ _) as [Heq' | _]; [inversion Heq'|].
  reflexivity.
Qed.

(* Landed (EConst) entity + distinct viewpoint = EAdd-merge.
   We pick a structurally distinct viewpoint so entity_eq_dec
   separates them without needing numeric distinctness. *)
Example q_interact_landed_merges :
  Q.interact
    (Q.EConst 0%Qc)
    (Q.EAdd (Q.EConst 0%Qc) (Q.EConst 0%Qc))
  = Q.EAdd (Q.EConst 0%Qc) (Q.EAdd (Q.EConst 0%Qc) (Q.EConst 0%Qc)).
Proof.
  unfold Q.interact.
  destruct (Q.entity_eq_dec _ _) as [Heq | _]; [inversion Heq|].
  destruct (Q.entity_eq_dec _ _) as [_ | Hne].
  - reflexivity.
  - exfalso. apply Hne. reflexivity.
Qed.
