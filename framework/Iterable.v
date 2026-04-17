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

End IterableTheory.
