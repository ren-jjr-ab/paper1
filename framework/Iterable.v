(* ============================================== *)
(*  Iterable — termination structure              *)
(*                                                *)
(*  Extends ComputableExistenceSig with one       *)
(*  primitive:                                    *)
(*                                                *)
(*    remaining : Entity -> option nat            *)
(*                                                *)
(*  Two axioms:                                   *)
(*    project_decrements_remaining                *)
(*    done_stays_done                             *)
(*                                                *)
(*  Some n — iterator has n steps remaining.      *)
(*  None — looping, with no finite commitment.    *)
(* ============================================== *)

Require Import Existence.
Require Import Computable.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Module Type IterableComputableSig.
  Include ComputableExistenceSig.

  (* ============================================= *)
  (*  NEW PRIMITIVE                                *)
  (* ============================================= *)

  Parameter remaining : Entity -> option nat.

  (* ============================================= *)
  (*  AXIOMS                                       *)
  (* ============================================= *)

  (* ----- project_decrements_remaining -----
     For iterators committed to a finite count, every
     non-identity interaction drops the count by one:
     Some n becomes Some (n-1). Looping iterators
     (None) are untouched. *)
  Axiom project_decrements_remaining :
    forall (a c : Entity) (n : nat),
      interact a c <> a ->
      remaining a = Some n ->
      remaining (interact a c) = Some (n - 1).

  (* ----- done_stays_done -----
     Once remaining reaches Some 0 the iterator is
     exhausted: further interactions leave the count
     at Some 0. The entity itself may still change
     (is_terminal_impossible forbids total fixity),
     but the remaining counter has stabilized. *)
  Axiom done_stays_done :
    forall (a c : Entity),
      remaining a = Some 0 ->
      remaining (interact a c) = Some 0.

End IterableComputableSig.


Module IterableTheory (I : IterableComputableSig).
  Module CT := ComputableExistenceTheory I.
  Import I CT.

  Lemma done_preserved :
    forall (a c : Entity),
      remaining a = Some 0 ->
      remaining (interact a c) = Some 0.
  Proof. exact done_stays_done. Qed.

  (* ============================================= *)
  (*  CHAIN OF INTERACTIONS                        *)
  (*                                               *)
  (*  A chain is a list of viewpoints; apply_chain *)
  (*  folds interact over the chain. The framework *)
  (*  time axis — viewpoint sequence — emerges     *)
  (*  here as an explicit list for reasoning about *)
  (*  multi-step behavior.                         *)
  (* ============================================= *)

  Fixpoint apply_chain (chain : list Entity) (a : Entity) : Entity :=
    match chain with
    | [] => a
    | c :: rest => apply_chain rest (interact a c)
    end.

  Lemma apply_chain_nil :
    forall a, apply_chain [] a = a.
  Proof. intros. simpl. reflexivity. Qed.

  Lemma apply_chain_cons :
    forall c rest a,
      apply_chain (c :: rest) a = apply_chain rest (interact a c).
  Proof. intros. simpl. reflexivity. Qed.

  (* done_stays_done extends to arbitrary chains:
     once remaining hits Some 0, no chain of
     interactions can bring it back. *)

  Theorem done_stays_done_chain :
    forall (chain : list Entity) (a : Entity),
      remaining a = Some 0 ->
      remaining (apply_chain chain a) = Some 0.
  Proof.
    intros chain. induction chain as [| c rest IH].
    - intros a H. simpl. exact H.
    - intros a H. simpl. apply IH. apply done_stays_done. exact H.
  Qed.

  (* From Some n a non-self chain of length n drives
     the iterator to Some 0. The chain exists because
     interact_with supplies a non-self partner at each
     step, and project_decrements_remaining decrements
     the count deterministically. *)

  Theorem some_n_reaches_done :
    forall (n : nat) (a : Entity),
      remaining a = Some n ->
      exists chain : list Entity,
        length chain = n /\
        remaining (apply_chain chain a) = Some 0.
  Proof.
    induction n as [| k IH]; intros a H.
    - exists []. split; [reflexivity | simpl; exact H].
    - destruct (interact_with a) as [c Hne].
      assert (Hrem : remaining (interact a c) = Some (S k - 1)).
      { apply (project_decrements_remaining a c (S k) Hne H). }
      replace (S k - 1) with k in Hrem by lia.
      destruct (IH (interact a c) Hrem) as [chain' [Hlen Hdone]].
      exists (c :: chain').
      split.
      + simpl. rewrite Hlen. reflexivity.
      + simpl. exact Hdone.
  Qed.

End IterableTheory.


(* ================================================ *)
(*  ITERABLE MORPHISM                                *)
(*                                                   *)
(*  A morphism between IterableComputableSig        *)
(*  instances that preserves the termination         *)
(*  structure — specifically, the remaining         *)
(*  counter.                                         *)
(* ================================================ *)

Module IterableMorphism (I1 I2 : IterableComputableSig).

  Definition preserves_interact (phi : I1.Entity -> I2.Entity) : Prop :=
    forall a b : I1.Entity,
      phi (I1.interact a b) = I2.interact (phi a) (phi b).

  Definition preserves_remaining (phi : I1.Entity -> I2.Entity) : Prop :=
    forall a : I1.Entity,
      I2.remaining (phi a) = I1.remaining a.

  Definition iterable_morphism (phi : I1.Entity -> I2.Entity) : Prop :=
    preserves_interact phi /\ preserves_remaining phi.

  (* A morphism preserving remaining carries "done"
     status across instances. *)

  Theorem preserves_remaining_carries_done :
    forall phi,
      preserves_remaining phi ->
      forall a, I1.remaining a = Some 0 ->
                I2.remaining (phi a) = Some 0.
  Proof.
    intros phi Hpres a Hdone.
    rewrite Hpres. exact Hdone.
  Qed.

  (* Looping status is carried as well. *)

  Theorem preserves_remaining_carries_looping :
    forall phi,
      preserves_remaining phi ->
      forall a, I1.remaining a = None ->
                I2.remaining (phi a) = None.
  Proof.
    intros phi Hpres a Hloop.
    rewrite Hpres. exact Hloop.
  Qed.

End IterableMorphism.


(* ================================================ *)
(*  ITERABLE COMPOSITION                             *)
(* ================================================ *)

Module IterableCompose (I1 I2 I3 : IterableComputableSig).

  Definition compose
    (psi : I2.Entity -> I3.Entity)
    (phi : I1.Entity -> I2.Entity) : I1.Entity -> I3.Entity :=
    fun x => psi (phi x).

  Theorem compose_preserves_interact :
    forall psi phi,
      (forall a b,
        phi (I1.interact a b) = I2.interact (phi a) (phi b)) ->
      (forall a b,
        psi (I2.interact a b) = I3.interact (psi a) (psi b)) ->
      forall a b,
        compose psi phi (I1.interact a b) =
        I3.interact (compose psi phi a) (compose psi phi b).
  Proof.
    intros psi phi Hphi Hpsi a b.
    unfold compose. rewrite Hphi. apply Hpsi.
  Qed.

  Theorem compose_preserves_remaining :
    forall psi phi,
      (forall a, I2.remaining (phi a) = I1.remaining a) ->
      (forall a, I3.remaining (psi a) = I2.remaining a) ->
      forall a, I3.remaining (compose psi phi a) = I1.remaining a.
  Proof.
    intros psi phi Hphi Hpsi a. unfold compose.
    rewrite Hpsi. apply Hphi.
  Qed.

  Theorem compose_of_iterable_morphisms :
    forall psi phi,
      (forall a b,
        phi (I1.interact a b) = I2.interact (phi a) (phi b)) ->
      (forall a, I2.remaining (phi a) = I1.remaining a) ->
      (forall a b,
        psi (I2.interact a b) = I3.interact (psi a) (psi b)) ->
      (forall a, I3.remaining (psi a) = I2.remaining a) ->
      (forall a b,
        compose psi phi (I1.interact a b) =
        I3.interact (compose psi phi a) (compose psi phi b)) /\
      (forall a, I3.remaining (compose psi phi a) = I1.remaining a).
  Proof.
    intros psi phi Hi1 Hr1 Hi2 Hr2.
    split.
    - apply compose_preserves_interact; assumption.
    - apply compose_preserves_remaining; assumption.
  Qed.

End IterableCompose.
