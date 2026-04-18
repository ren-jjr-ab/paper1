(* ========================================== *)
(*  PullbackLatHashTest                        *)
(*                                             *)
(*  A genuine meeting between two different    *)
(*  instances: LatticeComputable and           *)
(*  HashComputable. Both are ComputableExist-  *)
(*  enceSig instances with entirely different  *)
(*  entity structures (lattice pairs vs hash   *)
(*  stages).                                   *)
(*                                             *)
(*  Common substrate: LatticeComputable itself *)
(*  serves as the base. The two morphisms are  *)
(*                                             *)
(*    F1 = identity   : Lat -> Lat             *)
(*    F2 = constant   : Hash -> Lat            *)
(*                       (every hash entity to *)
(*                        pair_2_4)            *)
(*                                             *)
(*  Meeting condition:                         *)
(*    on_pullback (a, b)  iff  a = pair_2_4    *)
(*                                             *)
(*  Reading: the meeting slice is "the Lattice *)
(*  side pinned at pair_2_4 joined with an     *)
(*  arbitrary Hash entity". Every hash entity  *)
(*  agrees with pair_2_4 through the constant  *)
(*  encoding, so the pullback fills out the    *)
(*  full Hash fiber above pair_2_4.            *)
(*                                             *)
(*  The general Pullback theorem makes this    *)
(*  slice stable under joint interact — the    *)
(*  concrete case is verified for an arbitrary *)
(*  Hash entity below.                         *)
(* ========================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistenceProduct.
Require Import ExistencePullback.
Require Import LatticeModel.
Require Import HashModel.


(* ================================================ *)
(*  CONSTANT MORPHISM: HashComputable -> Lattice     *)
(* ================================================ *)

Module HashToLatConst <: MorphismInto HashComputable LatticeComputable.

  Definition phi
    : HashComputable.Entity -> LatticeComputable.Entity :=
    fun _ => pair_2_4.

  Theorem preserves_interact :
    forall a b : HashComputable.Entity,
      phi (HashComputable.interact a b) =
      LatticeComputable.interact (phi a) (phi b).
  Proof.
    intros a b. unfold phi.
    rewrite LatticeComputable.interact_self. reflexivity.
  Qed.

End HashToLatConst.


(* ================================================ *)
(*  IDENTITY ON LATTICE                              *)
(* ================================================ *)

Module LatId := ExistencePullback.IdentityInto LatticeComputable.


(* ================================================ *)
(*  PULLBACK                                         *)
(* ================================================ *)

Module LatHashMeeting :=
  ExistencePullback.Pullback
    LatticeComputable HashComputable LatticeComputable
    LatId HashToLatConst.


(* ================================================ *)
(*  THE MEETING SLICE                                *)
(*                                                   *)
(*  Every hash entity meets pair_2_4 on the Lattice  *)
(*  side. The slice is fully populated.              *)
(* ================================================ *)

Theorem meeting_any_hash :
  forall h : HashComputable.Entity,
    LatHashMeeting.on_pullback (pair_2_4, h).
Proof.
  intros h.
  unfold LatHashMeeting.on_pullback,
         LatId.phi, HashToLatConst.phi.
  simpl. reflexivity.
Qed.

Theorem non_meeting_pair42 :
  forall h : HashComputable.Entity,
    ~ LatHashMeeting.on_pullback (pair_4_2, h).
Proof.
  intros h.
  unfold LatHashMeeting.on_pullback,
         LatId.phi, HashToLatConst.phi. simpl.
  intros Heq. apply pair_2_4_distinct_from_pair_4_2.
  symmetry. exact Heq.
Qed.


(* ================================================ *)
(*  JOINT STABILITY                                  *)
(*                                                   *)
(*  Two Lattice-Hash meetings, joint-interacted,    *)
(*  remain a meeting. The Hash side may move         *)
(*  arbitrarily under HashComputable.interact; the   *)
(*  Lattice side stays at pair_2_4 since interact    *)
(*  of pair_2_4 with itself is pair_2_4.             *)
(* ================================================ *)

Theorem meeting_preserved :
  forall h1 h2 : HashComputable.Entity,
    LatHashMeeting.on_pullback
      (LatHashMeeting.P.interact
         (pair_2_4, h1) (pair_2_4, h2)).
Proof.
  intros h1 h2.
  apply LatHashMeeting.interact_preserves_pullback.
  - apply meeting_any_hash.
  - apply meeting_any_hash.
Qed.
