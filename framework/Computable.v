(* ============================================== *)
(*  Computable — quantitative extension           *)
(*                                                *)
(*  Extends ExistenceSig with three               *)
(*  quantitative primitives:                      *)
(*                                                *)
(*    info_size     current capacity              *)
(*    storage_cost  accumulated holding cost      *)
(*    flip_cost     accumulated work cost         *)
(*                                                *)
(*  Two axioms:                                   *)
(*    storage_pays_capacity                       *)
(*    flip_pays_work                              *)
(*                                                *)
(*  No info_monotone — info_size may grow or      *)
(*  shrink under interaction; growth is charged   *)
(*  to flip_cost.                                 *)
(* ============================================== *)

Require Import Existence.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.

Module Type ComputableExistenceSig.
  Include ExistenceSig.

  (* ============================================= *)
  (*  NEW PRIMITIVES                               *)
  (* ============================================= *)

  (* Current capacity — number of distinguishable
     states this entity carries. Finite by
     convention. *)
  Parameter info_size : Entity -> nat.

  (* Accumulated holding cost — the integral of
     info_size across the interaction chain that led
     to this entity. *)
  Parameter storage_cost : Entity -> nat.

  (* Accumulated work cost — the operator count
     across the interaction chain, each non-identity
     step paying at least one unit. *)
  Parameter flip_cost : Entity -> nat.

  (* ============================================= *)
  (*  AXIOMS                                       *)
  (* ============================================= *)

  (* ----- storage_pays_capacity -----
     Each non-identity interaction step advances
     storage_cost by the source's info_size. *)
  Axiom storage_pays_capacity :
    forall (a c : Entity),
      interact a c <> a ->
      storage_cost (interact a c) = storage_cost a + info_size a.

  (* ----- flip_pays_work -----
     Each non-identity interaction pays at least one
     flip token. If info_size grows by k >= 1, it
     pays k; otherwise it pays the minimum of one. *)
  Axiom flip_pays_work :
    forall (a c : Entity),
      interact a c <> a ->
      flip_cost (interact a c) =
        flip_cost a +
        Nat.max 1 (info_size (interact a c) - info_size a).

End ComputableExistenceSig.


(* ============================================== *)
(*  THEORY FUNCTOR                                *)
(* ============================================== *)

Module ComputableExistenceTheory (C : ComputableExistenceSig).
  Module DT := ExistenceTheory C.
  Import C DT.

  (* At the self-viewpoint, interaction is identity
     (interact_self) so both costs are preserved. *)
  Lemma storage_preserved_at_self :
    forall (a : Entity),
      storage_cost (interact a a) = storage_cost a.
  Proof.
    intros a. rewrite interact_self. reflexivity.
  Qed.

  Lemma flip_preserved_at_self :
    forall (a : Entity),
      flip_cost (interact a a) = flip_cost a.
  Proof.
    intros a. rewrite interact_self. reflexivity.
  Qed.

  (* Non-identity interaction that does NOT grow
     info_size: flip advances by exactly one. *)
  Lemma flip_shrink_is_unit :
    forall (a c : Entity),
      interact a c <> a ->
      info_size (interact a c) <= info_size a ->
      flip_cost (interact a c) = flip_cost a + 1.
  Proof.
    intros a c Hne Hshrink.
    rewrite (flip_pays_work a c Hne).
    assert (Hzero : info_size (interact a c) - info_size a = 0).
    { apply Nat.sub_0_le. exact Hshrink. }
    rewrite Hzero. reflexivity.
  Qed.

  (* Non-identity interaction that grows info_size by
     k > 0: flip advances by exactly k. *)
  Lemma flip_grow_pays_growth :
    forall (a c : Entity),
      interact a c <> a ->
      info_size a < info_size (interact a c) ->
      flip_cost (interact a c) =
        flip_cost a + (info_size (interact a c) - info_size a).
  Proof.
    intros a c Hne Hgrow.
    rewrite (flip_pays_work a c Hne).
    assert (Hdiff_ge_one :
      1 <= info_size (interact a c) - info_size a).
    { apply Nat.le_add_le_sub_r. simpl. exact Hgrow. }
    assert (Hmax :
      Nat.max 1 (info_size (interact a c) - info_size a) =
      info_size (interact a c) - info_size a).
    { apply Nat.max_r. exact Hdiff_ge_one. }
    rewrite Hmax. reflexivity.
  Qed.

  (* For any non-identity interaction, storage does
     not decrease and flip strictly advances. No free
     lunch on the work axis. *)
  Lemma both_costs_advance :
    forall (a c : Entity),
      interact a c <> a ->
      storage_cost a <= storage_cost (interact a c) /\
      flip_cost a < flip_cost (interact a c).
  Proof.
    intros a c Hne. split.
    - rewrite (storage_pays_capacity a c Hne). apply Nat.le_add_r.
    - rewrite (flip_pays_work a c Hne).
      apply Nat.lt_add_pos_r.
      apply Nat.lt_le_trans with 1.
      + apply Nat.lt_0_1.
      + apply Nat.le_max_l.
  Qed.

End ComputableExistenceTheory.
