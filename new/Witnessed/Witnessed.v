(* =========================================== *)
(*  Witnessed — Existence under external time. *)
(*                                             *)
(*  Adds a witness function that records the   *)
(*  iteration/time coordinate of each entity.  *)
(*  Any non-self interact strictly advances    *)
(*  this coordinate, so motion is externally   *)
(*  observable even when an entity's internal  *)
(*  representation holds still.                *)
(* =========================================== *)

Require Import Existence.
Require Import Theory.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Lia.


Module Type WitnessedSig.
  Include ExistenceSig.

  Parameter witness_time : Entity -> nat.

  Axiom witness_advances_on_nonself :
    forall (a c : Entity),
      interact a c <> a ->
      witness_time (interact a c) > witness_time a.

End WitnessedSig.


Module WitnessedTheory (T : WitnessedSig).

  Import T.

  Theorem exists_witness_time_advancing_partner :
    forall a, exists b, witness_time (interact a b) > witness_time a.
  Proof.
    intros a. destruct (interact_with a) as [b Hne].
    exists b. apply witness_advances_on_nonself. exact Hne.
  Qed.

  Lemma self_interact_preserves_witness_time :
    forall a, witness_time (interact a a) = witness_time a.
  Proof.
    intros a. rewrite interact_self. reflexivity.
  Qed.

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
