(* ============================================== *)
(*  ExternalTime — explicit event-counter extension *)
(*                                                  *)
(*  Existence already carries an internal time      *)
(*  axis: interact_with asserts that every entity   *)
(*  has some partner moving it, so time flows at    *)
(*  the framework level. That time is abstract —    *)
(*  no counter, no position.                        *)
(*                                                  *)
(*  ExternalTime layers an explicit counter on top. *)
(*  Each instance attaches an external_time field   *)
(*  to entities and commits to a single behavioral  *)
(*  axiom: non-self interact advances this counter. *)
(*                                                  *)
(*  Shape mirrors Computable. Include ExistenceSig  *)
(*  unchanged, add primitive + behavioral axiom.    *)
(*                                                  *)
(*  Use case: instances whose value coord can stall *)
(*  (e.g., semi-lattices with absorbing elements).  *)
(*  The external counter is a stall-free coord, so  *)
(*  interact_with is satisfied through counter      *)
(*  movement even when the value coord is stuck.    *)
(* ============================================== *)

Require Import Existence.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module Type ExternalTimeSig.
  Include ExistenceSig.

  (* ============================================= *)
  (*  NEW PRIMITIVE                                *)
  (* ============================================= *)

  (* Explicit event counter on entities.
     external_time a records the number of
     non-self interact events that led to a. *)
  Parameter external_time : Entity -> nat.

  (* ============================================= *)
  (*  AXIOM                                        *)
  (* ============================================= *)

  (* Non-self interact is an event: the result's
     external_time strictly exceeds the source's.
     Self-interact preserves external_time via
     interact_self (identity). *)
  Axiom external_time_advances_on_nonself :
    forall (a c : Entity),
      interact a c <> a ->
      external_time (interact a c) > external_time a.

End ExternalTimeSig.


(* ================================================ *)
(*  THEORY FUNCTOR                                   *)
(* ================================================ *)

Module ExternalTimeTheory (T : ExternalTimeSig).

  Import T.

  (* Every entity has a partner that advances its
     external_time — direct consequence of
     interact_with plus the ExternalTime axiom. *)
  Theorem exists_external_time_advancing_partner :
    forall a, exists b, external_time (interact a b) > external_time a.
  Proof.
    intros a. destruct (interact_with a) as [b Hne].
    exists b. apply external_time_advances_on_nonself. exact Hne.
  Qed.

  (* Self-interact preserves external_time.
     Immediate from interact_self. *)
  Lemma self_interact_preserves_external_time :
    forall a, external_time (interact a a) = external_time a.
  Proof.
    intros a. rewrite interact_self. reflexivity.
  Qed.

End ExternalTimeTheory.
