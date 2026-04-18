(* ================================================ *)
(*  FrameworkRiceTest                                *)
(*                                                   *)
(*  Apply the FrameworkRice.Make functor to          *)
(*  LatticeComputable by supplying the gcd-merge     *)
(*  collapse witness:                                *)
(*                                                   *)
(*    pair_2_4 and pair_4_2 are distinct,            *)
(*    both are non-frozen, and their interactions    *)
(*    with the (1, _) viewpoint yield the same       *)
(*    scalar entity.                                 *)
(* ================================================ *)

Require Import Existence.
Require Import FrameworkRice.
Require Import LatticeModel.

From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

(* ================================================ *)
(*  LatticeWithCollapse — LatticeComputable plus    *)
(*  the collapse witness required by FrameworkRice. *)
(* ================================================ *)

Module LatticeWithCollapse <: ExistenceWithCollapse.

  Include LatticeComputable.

  Definition is_frozen (a : Entity) : Prop :=
    exists b, a = LatticeModel.freeze b.

  (* Two distinct non-frozen pair entities with the
     same info_size whose gcd merge collapses them
     to a common result. *)
  Definition collapse_a      : Entity := pair_2_4.
  Definition collapse_a'     : Entity := pair_4_2.

  (* The merged scalar at the (1, _) viewpoint, given
     as a literal entity so the category reduces
     definitionally. *)
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
    unfold collapse_a, collapse_via, collapse_target, pair_2_4, dim_as_entity.
    reflexivity.
  Qed.

  Theorem collapse_interacts_a' :
    interact collapse_a' collapse_via = collapse_target.
  Proof.
    unfold collapse_a', collapse_via, collapse_target, pair_4_2, dim_as_entity.
    reflexivity.
  Qed.

End LatticeWithCollapse.

(* ================================================ *)
(*  Apply FrameworkRice.Make                        *)
(* ================================================ *)

Module LatticeRice := FrameworkRice.Make LatticeWithCollapse.

(* ================================================ *)
(*  Re-expose the theorems as concrete per-instance *)
(*  results about LatticeComputable.                *)
(* ================================================ *)

Theorem rice_instance_has_loss_Lattice :
  exists (a a' : LatticeWithCollapse.Entity) (c target : LatticeWithCollapse.Entity),
    a <> a' /\
    ~ LatticeWithCollapse.is_frozen a /\
    ~ LatticeWithCollapse.is_frozen a' /\
    LatticeWithCollapse.interact a c = target /\
    LatticeWithCollapse.interact a' c = target.
Proof. exact LatticeRice.rice_instance_has_loss. Qed.

Theorem rice_no_universal_decoder_Lattice :
  ~ (exists (decode : LatticeWithCollapse.Entity ->
                       LatticeWithCollapse.Entity),
       forall (a c : LatticeWithCollapse.Entity),
         decode (LatticeWithCollapse.interact a c) = a).
Proof. exact LatticeRice.rice_no_universal_decoder. Qed.
