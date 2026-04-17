(* ========================================== *)
(*  MorphismTest                               *)
(*                                             *)
(*  Sanity check: apply the ExistenceMorphism  *)
(*  functors to LatticeComputable and verify   *)
(*  two canonical morphisms exist.             *)
(*                                             *)
(*    Identity   — fully injective morphism    *)
(*                 from Lattice to itself.     *)
(*                 All relations transport     *)
(*                 unchanged.                  *)
(*                                             *)
(*    Constant   — maximal non-injective       *)
(*                 morphism. Every entity      *)
(*                 collapses to a single       *)
(*                 fixed point. Non-injective  *)
(*                 witness for the Make        *)
(*                 functor's lemmas.           *)
(*                                             *)
(*  These two bracket the "morphism spectrum": *)
(*  identity preserves every distinction;      *)
(*  constant erases every distinction. Every   *)
(*  other morphism sits between.               *)
(* ========================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import LatticeModel.


(* ================================================ *)
(*  IDENTITY                                         *)
(* ================================================ *)

Module LatIdentity := ExistenceMorphism.Identity LatticeComputable.

Module LatSelf :=
  ExistenceMorphism.Make LatticeComputable LatticeComputable.

Theorem lat_id_preserves_interact :
  LatSelf.preserves_interact LatIdentity.id.
Proof.
  intros a b. unfold LatIdentity.id. reflexivity.
Qed.

Theorem lat_id_injective :
  LatSelf.injective LatIdentity.id.
Proof.
  intros a b Heq. unfold LatIdentity.id in Heq. exact Heq.
Qed.


(* ================================================ *)
(*  CONSTANT MORPHISM                                *)
(*                                                   *)
(*  Choose any fixed point — every entity is a       *)
(*  self-fixed point by interact_self, so any        *)
(*  Lattice entity works. We pick pair_2_4.          *)
(* ================================================ *)

Definition lat_const
  : LatticeComputable.Entity -> LatticeComputable.Entity :=
  fun _ => pair_2_4.

Theorem lat_const_preserves_interact :
  LatSelf.preserves_interact lat_const.
Proof.
  intros a b. unfold lat_const.
  rewrite LatticeComputable.interact_self.
  reflexivity.
Qed.

Theorem lat_const_not_injective :
  ~ LatSelf.injective lat_const.
Proof.
  intros Hinj.
  apply pair_2_4_distinct_from_pair_4_2.
  apply Hinj. unfold lat_const. reflexivity.
Qed.

(* ================================================ *)
(*  CONSTANT COLLAPSES EVERY PROJECTION TO EQUIV     *)
(*                                                   *)
(*  Source paper_projection is characterized by      *)
(*  "distinct a, b with agreement at some c".        *)
(*  The constant morphism sends a and b both to      *)
(*  pair_2_4, so the image is paper_equiv by         *)
(*  reflexivity — the distinction is lost.           *)
(*                                                   *)
(*  morphism_preserves_paper_equiv is the generic    *)
(*  fact that any function lifts equality; here we   *)
(*  witness it with the constant-equality case.      *)
(* ================================================ *)

Theorem lat_const_collapses :
  forall a b : LatticeComputable.Entity,
    lat_const a = lat_const b.
Proof.
  intros a b. unfold lat_const. reflexivity.
Qed.
