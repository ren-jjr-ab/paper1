(* ============================================== *)
(*  Witnessed — explicit event-counter extension    *)
(*                                                  *)
(*  Existence already carries an internal time      *)
(*  axis: interact_with asserts that every entity   *)
(*  has some partner moving it, so time flows at    *)
(*  the framework level. That time is abstract —    *)
(*  no counter, no position.                        *)
(*                                                  *)
(*  Witnessed layers an explicit counter on top.    *)
(*  Each instance attaches a witness_time field     *)
(*  to entities and commits to a single behavioral  *)
(*  axiom: non-self interact advances this counter. *)
(*                                                  *)
(*  Shape mirrors Materialized. Include             *)
(*  ExistenceSig unchanged, add primitive +         *)
(*  behavioral axiom.                               *)
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
From Stdlib Require Import List.
Import ListNotations.


Module Type WitnessedSig.
  Include ExistenceSig.

  (* ============================================= *)
  (*  NEW PRIMITIVE                                *)
  (* ============================================= *)

  (* Explicit event counter on entities.
     witness_time a records the number of
     non-self interact events that led to a. *)
  Parameter witness_time : Entity -> nat.

  (* ============================================= *)
  (*  AXIOM                                        *)
  (* ============================================= *)

  (* Non-self interact is an event: the result's
     witness_time strictly exceeds the source's.
     Self-interact preserves witness_time via
     interact_self (identity). *)
  Axiom witness_advances_on_nonself :
    forall (a c : Entity),
      interact a c <> a ->
      witness_time (interact a c) > witness_time a.

End WitnessedSig.


(* ================================================ *)
(*  THEORY FUNCTOR                                   *)
(* ================================================ *)

Module WitnessedTheory (T : WitnessedSig).

  Import T.

  (* Every entity has a partner that advances its
     witness_time — direct consequence of
     interact_with plus the Witnessed axiom. *)
  Theorem exists_witness_time_advancing_partner :
    forall a, exists b, witness_time (interact a b) > witness_time a.
  Proof.
    intros a. destruct (interact_with a) as [b Hne].
    exists b. apply witness_advances_on_nonself. exact Hne.
  Qed.

  (* Self-interact preserves witness_time.
     Immediate from interact_self. *)
  Lemma self_interact_preserves_witness_time :
    forall a, witness_time (interact a a) = witness_time a.
  Proof.
    intros a. rewrite interact_self. reflexivity.
  Qed.

  (* ============================================= *)
  (*  CHAIN-BASED TIME MONOTONICITY                *)
  (*                                               *)
  (*  Under a non-self chain, witness_time       *)
  (*  advances by at least the chain length.       *)
  (*  This is the explicit counter version of     *)
  (*  the framework's interact_with axiom,        *)
  (*  giving a lower bound on elapsed events.     *)
  (* ============================================= *)

  Fixpoint apply_chain (chain : list Entity) (a : Entity) : Entity :=
    match chain with
    | [] => a
    | c :: rest => apply_chain rest (interact a c)
    end.

  Fixpoint all_non_self (a : Entity) (chain : list Entity) : Prop :=
    match chain with
    | [] => True
    | c :: rest =>
        interact a c <> a /\ all_non_self (interact a c) rest
    end.

  (* Witness time strictly exceeds starting time by
     at least the length of any non-self chain. *)

  Theorem witness_time_advances_on_chain :
    forall (chain : list Entity) (a : Entity),
      all_non_self a chain ->
      witness_time (apply_chain chain a) >= witness_time a + length chain.
  Proof.
    intros chain. induction chain as [| c rest IH].
    - intros a _. simpl. lia.
    - intros a [Hne Hrest]. simpl.
      specialize (IH (interact a c) Hrest).
      pose proof (witness_advances_on_nonself a c Hne) as Hstep.
      lia.
  Qed.

  (* Non-empty non-self chain strictly advances time. *)

  Theorem witness_time_strictly_advances_nonempty_chain :
    forall (chain : list Entity) (a : Entity),
      all_non_self a chain ->
      length chain > 0 ->
      witness_time (apply_chain chain a) > witness_time a.
  Proof.
    intros chain a Hall Hlen.
    pose proof (witness_time_advances_on_chain chain a Hall) as H.
    lia.
  Qed.

End WitnessedTheory.


(* ================================================ *)
(*  TIMED MORPHISM                                   *)
(*                                                   *)
(*  A morphism between WitnessedSig instances    *)
(*  that preserves (or shifts) the witness_time    *)
(*  counter. Useful for reasoning about time-       *)
(*  respecting translations between axiom systems.  *)
(* ================================================ *)

Module TimedMorphism (T1 T2 : WitnessedSig).

  Definition preserves_interact (phi : T1.Entity -> T2.Entity) : Prop :=
    forall a b : T1.Entity,
      phi (T1.interact a b) = T2.interact (phi a) (phi b).

  (* Witness time is preserved exactly. *)

  Definition preserves_witness_time (phi : T1.Entity -> T2.Entity) : Prop :=
    forall a : T1.Entity,
      T2.witness_time (phi a) = T1.witness_time a.

  (* Witness time is shifted by a constant delta. *)

  Definition shifts_witness_time
    (phi : T1.Entity -> T2.Entity) (delta : nat) : Prop :=
    forall a : T1.Entity,
      T2.witness_time (phi a) = T1.witness_time a + delta.

  (* Timed morphism: interact + exact time preservation. *)

  Definition timed_morphism (phi : T1.Entity -> T2.Entity) : Prop :=
    preserves_interact phi /\ preserves_witness_time phi.

  (* Exact preservation is shifting by zero. *)

  Theorem preserves_is_shift_zero :
    forall phi,
      preserves_witness_time phi -> shifts_witness_time phi 0.
  Proof.
    intros phi H a. rewrite H. lia.
  Qed.

  Theorem shift_zero_is_preserves :
    forall phi,
      shifts_witness_time phi 0 -> preserves_witness_time phi.
  Proof.
    intros phi H a. rewrite H. lia.
  Qed.

End TimedMorphism.


(* ================================================ *)
(*  TIMED COMPOSITION                                *)
(* ================================================ *)

Module TimedCompose (T1 T2 T3 : WitnessedSig).

  Definition compose
    (psi : T2.Entity -> T3.Entity)
    (phi : T1.Entity -> T2.Entity) : T1.Entity -> T3.Entity :=
    fun x => psi (phi x).

  Theorem compose_preserves_interact :
    forall psi phi,
      (forall a b,
        phi (T1.interact a b) = T2.interact (phi a) (phi b)) ->
      (forall a b,
        psi (T2.interact a b) = T3.interact (psi a) (psi b)) ->
      forall a b,
        compose psi phi (T1.interact a b) =
        T3.interact (compose psi phi a) (compose psi phi b).
  Proof.
    intros psi phi Hphi Hpsi a b.
    unfold compose. rewrite Hphi. apply Hpsi.
  Qed.

  Theorem compose_preserves_witness_time :
    forall psi phi,
      (forall a, T2.witness_time (phi a) = T1.witness_time a) ->
      (forall a, T3.witness_time (psi a) = T2.witness_time a) ->
      forall a, T3.witness_time (compose psi phi a) = T1.witness_time a.
  Proof.
    intros psi phi Hphi Hpsi a. unfold compose.
    rewrite Hpsi. apply Hphi.
  Qed.

  (* Shifts compose additively. *)

  Theorem compose_shifts_witness_time :
    forall psi phi k1 k2,
      (forall a, T2.witness_time (phi a) = T1.witness_time a + k1) ->
      (forall a, T3.witness_time (psi a) = T2.witness_time a + k2) ->
      forall a, T3.witness_time (compose psi phi a) =
                T1.witness_time a + (k1 + k2).
  Proof.
    intros psi phi k1 k2 Hphi Hpsi a. unfold compose.
    rewrite Hpsi. rewrite Hphi. lia.
  Qed.

  Theorem compose_of_timed_morphisms :
    forall psi phi,
      (forall a b,
        phi (T1.interact a b) = T2.interact (phi a) (phi b)) ->
      (forall a, T2.witness_time (phi a) = T1.witness_time a) ->
      (forall a b,
        psi (T2.interact a b) = T3.interact (psi a) (psi b)) ->
      (forall a, T3.witness_time (psi a) = T2.witness_time a) ->
      (forall a b,
        compose psi phi (T1.interact a b) =
        T3.interact (compose psi phi a) (compose psi phi b)) /\
      (forall a, T3.witness_time (compose psi phi a) =
                 T1.witness_time a).
  Proof.
    intros psi phi Hi1 Ht1 Hi2 Ht2.
    split.
    - apply compose_preserves_interact; assumption.
    - apply compose_preserves_witness_time; assumption.
  Qed.

End TimedCompose.
