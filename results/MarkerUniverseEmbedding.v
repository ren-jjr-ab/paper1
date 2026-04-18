(* ============================================== *)
(*  MarkerUniverseEmbedding                         *)
(*                                                  *)
(*  Every RingAsEntity R contains a canonical copy  *)
(*  of PureMarkerEntity as an interact-preserving   *)
(*  sub-Entity. The embedding is                    *)
(*                                                  *)
(*    iota : nat → RingAsEntity(R).Entity           *)
(*    iota n = Mark n                               *)
(*                                                  *)
(*  It is injective (markers stay markers, never    *)
(*  collapse onto REnt x) and preserves interact    *)
(*  by construction: RingAsEntity.interact          *)
(*  on Mark–Mark pairs matches PureMarkerEntity's   *)
(*  interact verbatim.                              *)
(*                                                  *)
(*  The consequence: one and the same pure-         *)
(*  viewpoint Existence sits inside Ring-as-Entity  *)
(*  for every choice of ring R. The marker universe *)
(*  is ring-independent — its dynamics never look   *)
(*  at R, never produce REnt outputs, and never     *)
(*  consume ring data. Across all rings, markers    *)
(*  behave identically.                             *)
(* ============================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import Ring.
Require PureMarkerEntity.
Require RingAsEntity.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


(* =========================================== *)
(*  EMBEDDING FUNCTOR                           *)
(*                                              *)
(*  For any ring R, marker indices map to the   *)
(*  Mark branch of RingAsEntity(R), and that    *)
(*  map preserves interact.                     *)
(* =========================================== *)

Module MarkerEmbedding (R : DecEqCommRingSig).

  Module RE := RingAsEntity.RingAsEntity R.
  Module PME := PureMarkerEntity.PureMarkerEntity.

  Definition iota (n : PME.Entity) : RE.Entity := RE.Mark n.

  Theorem iota_injective :
    forall m n : PME.Entity, iota m = iota n -> m = n.
  Proof.
    intros m n H. unfold iota in H. inversion H. reflexivity.
  Qed.

  Theorem iota_preserves_interact :
    forall m n : PME.Entity,
      iota (PME.interact m n) = RE.interact (iota m) (iota n).
  Proof.
    intros m n. unfold iota, PME.interact, RE.interact.
    destruct (Nat.eq_dec m n) as [Heq | Hne]; reflexivity.
  Qed.

  (* The embedding never lands in REnt — markers stay markers. *)

  Theorem iota_image_is_marker :
    forall n : PME.Entity,
      exists k, iota n = RE.Mark k.
  Proof. intros n. exists n. reflexivity. Qed.

  (* Self-interact is preserved automatically from preserves_interact,
     but restating here for visibility. *)

  Theorem iota_preserves_self :
    forall n : PME.Entity,
      iota (PME.interact n n) = RE.interact (iota n) (iota n).
  Proof. intros. apply iota_preserves_interact. Qed.

End MarkerEmbedding.


(* =========================================== *)
(*  INSTANTIATIONS ACROSS RINGS                 *)
(*                                              *)
(*  The same PureMarkerEntity embeds into every *)
(*  Ring-Entity uniformly. Listing a few to     *)
(*  make the point concrete.                    *)
(* =========================================== *)

Module IntegerMarker   := MarkerEmbedding IntegerRing.IntegerRing.
Module Mod7Marker      := MarkerEmbedding ModularRing.Mod7Ring.
Module FinSet3Marker   := MarkerEmbedding FinSetRing.FinSet3.
Module F2Marker        := MarkerEmbedding RingAsEntity.F2.
Module TrivialMarker   := MarkerEmbedding RingAsEntity.TrivialRing.


(* =========================================== *)
(*  CONCRETE WITNESSES                          *)
(*                                              *)
(*  iota's image and interact-preservation      *)
(*  computed at specific indices.               *)
(* =========================================== *)

(* The embedding produces the same Mark in the target. *)

Example iota_into_integer :
  IntegerMarker.iota 3 = IntegerMarker.RE.Mark 3.
Proof. reflexivity. Qed.

Example iota_into_f2 :
  F2Marker.iota 5 = F2Marker.RE.Mark 5.
Proof. reflexivity. Qed.

(* interact on markers matches the universe dynamics in every ring. *)

Example interact_commutes_integer :
  IntegerMarker.iota (PureMarkerEntity.PureMarkerEntity.interact 3 5) =
  IntegerMarker.RE.interact (IntegerMarker.iota 3) (IntegerMarker.iota 5).
Proof. apply IntegerMarker.iota_preserves_interact. Qed.

Example interact_commutes_trivial :
  TrivialMarker.iota (PureMarkerEntity.PureMarkerEntity.interact 3 5) =
  TrivialMarker.RE.interact (TrivialMarker.iota 3) (TrivialMarker.iota 5).
Proof. apply TrivialMarker.iota_preserves_interact. Qed.


(* =========================================== *)
(*  CROSS-RING MARKER AGREEMENT                 *)
(*                                              *)
(*  The same pair of marker indices, embedded   *)
(*  into two different ring-entities, produces  *)
(*  "the same" marker result (up to the target  *)
(*  type) because the marker dynamics is        *)
(*  ring-independent. We expose this by         *)
(*  computing each side to its nat index.       *)
(* =========================================== *)

Definition mark_index_integer (e : IntegerMarker.RE.Entity) : option nat :=
  match e with
  | IntegerMarker.RE.Mark n => Some n
  | IntegerMarker.RE.REnt _ => None
  end.

Definition mark_index_f2 (e : F2Marker.RE.Entity) : option nat :=
  match e with
  | F2Marker.RE.Mark n => Some n
  | F2Marker.RE.REnt _ => None
  end.

Example same_interaction_in_integer :
  mark_index_integer
    (IntegerMarker.RE.interact (IntegerMarker.iota 3) (IntegerMarker.iota 5))
  = Some 6.
Proof. reflexivity. Qed.

Example same_interaction_in_f2 :
  mark_index_f2
    (F2Marker.RE.interact (F2Marker.iota 3) (F2Marker.iota 5))
  = Some 6.
Proof. reflexivity. Qed.

(* Same marker index (6) produced in both rings — the marker universe *)
(* is ring-independent, demonstrated across a rich ring and F_2.      *)


(* =========================================== *)
(*  REMARK                                      *)
(*                                              *)
(*  Framework position: Entity in ExistenceSig  *)
(*  is declared without shape constraint. What  *)
(*  our instances do — RationalRep's CMark,     *)
(*  CauchyReal's CEval, SymbolicSet's SQuery,   *)
(*  now RingAsEntity's Mark — is pair an        *)
(*  algebraic data layer with a viewpoint layer *)
(*  that supplies motion. The viewpoint layer   *)
(*  is *never* reducible to the algebraic data, *)
(*  and in Ring-Entity that asymmetry is laid   *)
(*  bare: the pure marker universe is a free    *)
(*  Existence standing beside any ring.         *)
(*                                              *)
(*  "Entity = data + viewpoint" is not a        *)
(*  convention we chose. It is what the five    *)
(*  axioms force, and pure markers are the      *)
(*  viewpoint half in isolation.                *)
(* =========================================== *)
