(* ========================================== *)
(*  PullbackTest                               *)
(*                                             *)
(*  A concrete meeting between two views of    *)
(*  LatticeComputable via two different        *)
(*  morphisms into the same base.              *)
(*                                             *)
(*    D1   = LatticeComputable                 *)
(*    D2   = LatticeComputable                 *)
(*    Base = LatticeComputable                 *)
(*    F1   = identity                          *)
(*    F2   = constant to pair_2_4              *)
(*                                             *)
(*  The meeting predicate then reads:          *)
(*    on_pullback (a, b)  iff  a = pair_2_4    *)
(*  That is, D1 and D2 meet on the slice       *)
(*  where the first coordinate is pair_2_4 —   *)
(*  the constant target chooses a viewpoint    *)
(*  and the identity witnesses which D1        *)
(*  entities reach it.                         *)
(*                                             *)
(*  The general interact_preserves_pullback    *)
(*  theorem guarantees this slice is           *)
(*  interact-closed: two meetings interact to  *)
(*  another meeting. Verified concretely       *)
(*  below.                                     *)
(* ========================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistenceProduct.
Require Import ExistencePullback.
Require Import LatticeModel.


(* ================================================ *)
(*  CONSTANT MORPHISM TO pair_2_4                    *)
(* ================================================ *)

Module ConstPair24 <: MorphismInto LatticeComputable LatticeComputable.

  Definition phi
    : LatticeComputable.Entity -> LatticeComputable.Entity :=
    fun _ => pair_2_4.

  Theorem preserves_interact :
    forall a b : LatticeComputable.Entity,
      phi (LatticeComputable.interact a b) =
      LatticeComputable.interact (phi a) (phi b).
  Proof.
    intros a b. unfold phi.
    rewrite LatticeComputable.interact_self.
    reflexivity.
  Qed.

End ConstPair24.


(* ================================================ *)
(*  IDENTITY ON LATTICE                              *)
(* ================================================ *)

Module LatId := ExistencePullback.IdentityInto LatticeComputable.


(* ================================================ *)
(*  PULLBACK                                         *)
(*                                                   *)
(*    D1 = D2 = Base = LatticeComputable             *)
(*    F1 = id, F2 = const_pair_2_4                   *)
(* ================================================ *)

Module LatLatMeeting :=
  ExistencePullback.Pullback
    LatticeComputable LatticeComputable LatticeComputable
    LatId ConstPair24.


(* ================================================ *)
(*  CONCRETE MEETINGS                                *)
(* ================================================ *)

Theorem meeting_pair24_pair42 :
  LatLatMeeting.on_pullback (pair_2_4, pair_4_2).
Proof.
  unfold LatLatMeeting.on_pullback,
         LatId.phi, ConstPair24.phi. simpl. reflexivity.
Qed.

Theorem meeting_pair24_pair24 :
  LatLatMeeting.on_pullback (pair_2_4, pair_2_4).
Proof.
  unfold LatLatMeeting.on_pullback,
         LatId.phi, ConstPair24.phi. simpl. reflexivity.
Qed.

(* Non-meeting: first coord is pair_4_2, not the slice. *)

Theorem not_meeting_pair42_any :
  ~ LatLatMeeting.on_pullback (pair_4_2, pair_2_4).
Proof.
  unfold LatLatMeeting.on_pullback,
         LatId.phi, ConstPair24.phi. simpl.
  intros Heq. apply pair_2_4_distinct_from_pair_4_2.
  symmetry. exact Heq.
Qed.


(* ================================================ *)
(*  STABILITY UNDER JOINT INTERACT                   *)
(*                                                   *)
(*  Two meetings interact to a meeting — derived     *)
(*  from the generic theorem and instantiated at     *)
(*  the two concrete witnesses above.                *)
(* ================================================ *)

Theorem meeting_preserved_concrete :
  LatLatMeeting.on_pullback
    (LatLatMeeting.P.interact
       (pair_2_4, pair_4_2)
       (pair_2_4, pair_2_4)).
Proof.
  apply LatLatMeeting.interact_preserves_pullback.
  - exact meeting_pair24_pair42.
  - exact meeting_pair24_pair24.
Qed.
