(* ========================================== *)
(*  FrameworkIrreversibility                   *)
(*                                             *)
(*  Interaction induces a reachability         *)
(*  relation on entities: b is reachable from  *)
(*  a when some chain of non-identity          *)
(*  interactions takes a to b. The Materialized  *)
(*  layer's flip_pays_work axiom makes every   *)
(*  such step strictly advance flip_cost.      *)
(*  Chaining the advances forces flip_cost to  *)
(*  be strictly monotonic along every proper   *)
(*  reachability chain.                        *)
(*                                             *)
(*  Consequences:                              *)
(*                                             *)
(*    - Reachability is antisymmetric:         *)
(*      if a reaches b, b does not reach a.    *)
(*    - No interaction cycle: no sequence of   *)
(*      non-identity steps returns an entity   *)
(*      to itself.                             *)
(*                                             *)
(*  This is the arrow of time for the          *)
(*  framework: flip_cost orders reachable      *)
(*  states, and interaction cannot walk back.  *)
(*                                             *)
(*  No new axiom. Everything follows from      *)
(*  flip_pays_work via both_costs_advance.     *)
(* ========================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Require Import Existence.
Require Import Theory.
Require Import Materialized.

Module Make (C : MaterializedExistenceSig).

  Import C.
  Module DT := ExistenceTheory C.
  Module CT := MaterializedExistenceTheory C.
  Import DT CT.

  (* ============================================= *)
  (*  ONE-STEP REACHABILITY                        *)
  (*                                               *)
  (*  b is reached from a in one non-identity      *)
  (*  step iff some viewpoint c takes a to b and   *)
  (*  b is distinct from a.                        *)
  (* ============================================= *)

  Definition reaches_in_one (a b : Entity) : Prop :=
    exists c : Entity, interact a c = b /\ b <> a.

  Theorem reaches_in_one_advances_flip :
    forall a b, reaches_in_one a b -> flip_cost a < flip_cost b.
  Proof.
    intros a b [c [Hint Hne]].
    assert (Hne_int : interact a c <> a).
    { rewrite Hint. exact Hne. }
    pose proof (both_costs_advance a c Hne_int) as [_ Hf].
    rewrite Hint in Hf. exact Hf.
  Qed.

  (* ============================================= *)
  (*  MULTI-STEP REACHABILITY                      *)
  (*                                               *)
  (*  Inductive chain of non-identity steps.       *)
  (*  reach_one is the base case, reach_step       *)
  (*  appends one further non-identity step.       *)
  (* ============================================= *)

  Inductive reaches : Entity -> Entity -> Prop :=
    | reach_one  : forall a b,
        reaches_in_one a b -> reaches a b
    | reach_step : forall a b c,
        reaches a b -> reaches_in_one b c -> reaches a c.

  Theorem reaches_advances_flip :
    forall a b, reaches a b -> flip_cost a < flip_cost b.
  Proof.
    intros a b H.
    induction H as [x y Hone | x y z Hr IH Hone].
    - apply reaches_in_one_advances_flip. exact Hone.
    - apply reaches_in_one_advances_flip in Hone. lia.
  Qed.

  Theorem reaches_distinct :
    forall a b, reaches a b -> a <> b.
  Proof.
    intros a b H Heq. subst b.
    apply reaches_advances_flip in H. lia.
  Qed.

  Theorem reaches_transitive :
    forall a b c, reaches a b -> reaches b c -> reaches a c.
  Proof.
    intros a b c H1 H2.
    revert a H1.
    induction H2 as [x y Hone | x y z Hr IH Hone]; intros a H1.
    - exact (reach_step a x y H1 Hone).
    - apply (reach_step a y z).
      + apply IH. exact H1.
      + exact Hone.
  Qed.

  (* ============================================= *)
  (*  NO CYCLE                                     *)
  (*                                               *)
  (*  Reachability does not return — if a reaches  *)
  (*  b, b cannot reach a. The flip_cost ordering  *)
  (*  rules out any back-walk.                     *)
  (* ============================================= *)

  Theorem no_interaction_cycle :
    forall a b, reaches a b -> reaches b a -> False.
  Proof.
    intros a b H1 H2.
    apply reaches_advances_flip in H1.
    apply reaches_advances_flip in H2.
    lia.
  Qed.

  Theorem reaches_antisymmetric :
    forall a b, reaches a b -> ~ reaches b a.
  Proof.
    intros a b H1 H2. exact (no_interaction_cycle a b H1 H2).
  Qed.

  Theorem reaches_irreflexive :
    forall a, ~ reaches a a.
  Proof.
    intros a H. exact (reaches_distinct a a H eq_refl).
  Qed.

  (* Arrow of time: reaches_advances_flip says
     reachability agrees with the flip_cost order.
     Every interaction chain that moves the entity
     lands at a strictly later flip-cost. The
     framework has a direction built into it. *)

End Make.
