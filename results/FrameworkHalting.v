(* ================================================ *)
(*  FrameworkHalting.v                               *)
(*                                                   *)
(*  Halting, stated in the framework's own           *)
(*  vocabulary, at the Iterable layer.               *)
(*                                                   *)
(*  The Iterable layer exposes remaining as          *)
(*  option nat. Some n means the instance has        *)
(*  committed to a finite step budget; None means    *)
(*  the instance refuses to commit. That split is    *)
(*  exactly the halts / diverges split of            *)
(*  computability theory, recovered here as plain    *)
(*  predicates on entities.                          *)
(*                                                   *)
(*  Once the Iterable layer is in place no extra     *)
(*  axiom is needed: halts and diverges are purely   *)
(*  definitional, and the two basic classical        *)
(*  properties (mutual exclusion and exhaustiveness) *)
(*  fall out of option nat's case analysis.          *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Require Import Existence.
Require Import Computable.
Require Import Iterable.

Module Make (I : IterableComputableSig).
  Import I.

  (* ============================================= *)
  (*  HALTING PREDICATES                           *)
  (* ============================================= *)

  (* halts a : a is committed to some specific
     finite step budget. *)
  Definition halts (a : Entity) : Prop :=
    exists n : nat, remaining a = Some n.

  (* diverges a : a refuses to commit to any
     finite step count. *)
  Definition diverges (a : Entity) : Prop :=
    remaining a = None.

  (* done a : a halts and the committed count is
     zero — the iterator is exhausted. *)
  Definition done (a : Entity) : Prop :=
    remaining a = Some 0.

  (* ============================================= *)
  (*  BASIC PROPERTIES                             *)
  (* ============================================= *)

  Theorem halts_or_diverges :
    forall a, halts a \/ diverges a.
  Proof.
    intro a.
    unfold halts, diverges.
    destruct (remaining a) as [n|] eqn:Hr.
    - left. exists n. reflexivity.
    - right. reflexivity.
  Qed.

  Theorem not_halts_and_diverges :
    forall a, halts a -> diverges a -> False.
  Proof.
    intros a Hh Hd.
    destruct Hh as [n Hn].
    unfold diverges in Hd.
    rewrite Hn in Hd. discriminate.
  Qed.

  Theorem done_implies_halts :
    forall a, done a -> halts a.
  Proof.
    intros a Hd. exists 0. exact Hd.
  Qed.

  Theorem not_done_and_diverges :
    forall a, done a -> diverges a -> False.
  Proof.
    intros a Hdone Hdiv.
    apply (not_halts_and_diverges a).
    - apply done_implies_halts. exact Hdone.
    - exact Hdiv.
  Qed.

  (* ============================================= *)
  (*  DONE PRESERVATION                            *)
  (*                                               *)
  (*  Done entities stay done under interaction.   *)
  (*  This is exactly the done_stays_done axiom    *)
  (*  from the Iterable layer, re-stated as a      *)
  (*  property of the done predicate.              *)
  (*                                               *)
  (*  The more general halts preservation — that   *)
  (*  any non-zero committed count yields another  *)
  (*  committed count after interaction — cannot   *)
  (*  be proved at this layer without entity       *)
  (*  equality decidability: the case split        *)
  (*  "interact a c = a vs interact a c <> a" has  *)
  (*  no framework-level decider. Instances can    *)
  (*  supply one; the abstract functor cannot.     *)
  (* ============================================= *)

  Theorem done_preserved_by_interact :
    forall (a c : Entity),
      done a -> done (interact a c).
  Proof.
    intros a c Hd.
    unfold done in *.
    apply done_stays_done. exact Hd.
  Qed.

End Make.
