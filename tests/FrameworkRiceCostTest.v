(* ================================================ *)
(*  FrameworkRiceCostTest                            *)
(*                                                   *)
(*  Apply FrameworkRiceCost.Make to                  *)
(*  LatticeComputable using the pair_2_4 /           *)
(*  pair_4_2 collapse witness, plus the two          *)
(*  non-identity facts the cost layer requires.      *)
(*                                                   *)
(*  Instance side: the two non-identity axioms       *)
(*  discharge by reflexivity-after-rewriting, since  *)
(*  pair_2_4 and collapse_target are literally       *)
(*  different constructors in LatticeModel's Entity  *)
(*  inductive (pair_2_4 is an LENormal with          *)
(*  vals = [2;4] and category 2; collapse_target is  *)
(*  an LENormal at category 1 with vals = [2]).      *)
(* ================================================ *)

Require Import Existence.
Require Import Materialized.
Require Import FrameworkRiceCost.
Require Import LatticeModel.

From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Module LatticeWithCollapseComputable <: MaterializedExistenceWithCollapse.
  Include LatticeComputable.

  Definition is_frozen (a : Entity) : Prop :=
    exists b, a = LatticeModel.freeze b.

  Definition collapse_a      : Entity := pair_2_4.
  Definition collapse_a'     : Entity := pair_4_2.
  Definition collapse_target : Entity := LENormal 1 [2] 6 1.
  Definition collapse_via    : Entity := dim_as_entity 1.

  Theorem collapse_distinct : collapse_a <> collapse_a'.
  Proof. exact pair_2_4_distinct_from_pair_4_2. Qed.

  Theorem collapse_a_not_frozen : ~ is_frozen collapse_a.
  Proof.
    intros [b Hb].
    unfold collapse_a, pair_2_4, is_frozen,
           LatticeModel.freeze, lat_freeze in Hb.
    inversion Hb.
  Qed.

  Theorem collapse_a'_not_frozen : ~ is_frozen collapse_a'.
  Proof.
    intros [b Hb].
    unfold collapse_a', pair_4_2, is_frozen,
           LatticeModel.freeze, lat_freeze in Hb.
    inversion Hb.
  Qed.

  Theorem collapse_interacts_a :
    interact collapse_a collapse_via = collapse_target.
  Proof.
    unfold collapse_a, collapse_via, collapse_target,
           pair_2_4, dim_as_entity.
    reflexivity.
  Qed.

  Theorem collapse_interacts_a' :
    interact collapse_a' collapse_via = collapse_target.
  Proof.
    unfold collapse_a', collapse_via, collapse_target,
           pair_4_2, dim_as_entity.
    reflexivity.
  Qed.

  Theorem collapse_nontrivial_a :
    interact collapse_a collapse_via <> collapse_a.
  Proof.
    rewrite collapse_interacts_a.
    unfold collapse_target, collapse_a, pair_2_4.
    intro H. inversion H.
  Qed.

  Theorem collapse_nontrivial_a' :
    interact collapse_a' collapse_via <> collapse_a'.
  Proof.
    rewrite collapse_interacts_a'.
    unfold collapse_target, collapse_a', pair_4_2.
    intro H. inversion H.
  Qed.

End LatticeWithCollapseComputable.

(* ================================================ *)
(*  Apply the functor                                *)
(* ================================================ *)

Module LatticeRiceCost :=
  FrameworkRiceCost.Make LatticeWithCollapseComputable.

(* ================================================ *)
(*  Concrete cost results for LatticeComputable      *)
(* ================================================ *)

Import LatticeComputable.

Theorem lattice_collapse_flip_cost_a :
  flip_cost LatticeWithCollapseComputable.collapse_a <
  flip_cost LatticeWithCollapseComputable.collapse_target.
Proof. exact LatticeRiceCost.collapse_flip_cost_a. Qed.

Theorem lattice_collapse_flip_cost_a' :
  flip_cost LatticeWithCollapseComputable.collapse_a' <
  flip_cost LatticeWithCollapseComputable.collapse_target.
Proof. exact LatticeRiceCost.collapse_flip_cost_a'. Qed.

Theorem lattice_collapse_flip_cost_max :
  Nat.max
    (flip_cost LatticeWithCollapseComputable.collapse_a)
    (flip_cost LatticeWithCollapseComputable.collapse_a') <
  flip_cost LatticeWithCollapseComputable.collapse_target.
Proof. exact LatticeRiceCost.collapse_flip_cost_max. Qed.
