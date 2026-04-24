(* ========================================== *)
(*  FrameworkRiceCost                          *)
(*                                             *)
(*  Quantitative companion to FrameworkRice.   *)
(*  FrameworkRice proves the existence-layer   *)
(*  result: no universal decoder exists when   *)
(*  two distinct non-frozen entities collapse  *)
(*  onto a common target.                      *)
(*                                             *)
(*  This file adds the Materialized-layer        *)
(*  statement: collapse is not only            *)
(*  non-invertible but strictly costly. When   *)
(*  the collapse is non-trivial on both sides  *)
(*  (neither source is a fixed point of        *)
(*  collapse_via):                             *)
(*                                             *)
(*    flip_cost collapse_a                     *)
(*      < flip_cost collapse_target            *)
(*    flip_cost collapse_a'                    *)
(*      < flip_cost collapse_target            *)
(*                                             *)
(*  and therefore                              *)
(*                                             *)
(*    Nat.max (flip_cost collapse_a)           *)
(*            (flip_cost collapse_a')          *)
(*        < flip_cost collapse_target          *)
(*                                             *)
(*  FrameworkRice says no decoder exists;      *)
(*  here that becomes an explicit flip-budget  *)
(*  gap: every collapse pays strictly more     *)
(*  work than either source carried.           *)
(*                                             *)
(*  Instances opt in by supplying a collapse   *)
(*  witness plus two non-identity axioms at    *)
(*  the Materialized layer.                      *)
(* ========================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Require Import Existence.
Require Import Theory.
Require Import Materialized.

(* ================================================ *)
(*  MODULE TYPE                                      *)
(*                                                   *)
(*  Same shape as ExistenceWithCollapse, promoted    *)
(*  to MaterializedExistenceSig, plus two              *)
(*  non-identity axioms needed to apply              *)
(*  flip_pays_work constructively. Framework has no  *)
(*  general entity-equality decider, so the          *)
(*  non-identity fact is taken as an instance        *)
(*  commitment rather than derived.                  *)
(* ================================================ *)

Module Type MaterializedExistenceWithCollapse.
  Include MaterializedExistenceSig.

  Parameter is_frozen : Entity -> Prop.

  Parameter collapse_a      : Entity.
  Parameter collapse_a'     : Entity.
  Parameter collapse_target : Entity.
  Parameter collapse_via    : Entity.

  Axiom collapse_distinct : collapse_a <> collapse_a'.

  Axiom collapse_a_not_frozen  : ~ is_frozen collapse_a.
  Axiom collapse_a'_not_frozen : ~ is_frozen collapse_a'.

  Axiom collapse_interacts_a :
    interact collapse_a collapse_via = collapse_target.
  Axiom collapse_interacts_a' :
    interact collapse_a' collapse_via = collapse_target.

  (* Non-identity commitments: neither source is
     fixed by collapse_via. Equivalent to saying
     collapse_target is distinct from each source. *)
  Axiom collapse_nontrivial_a :
    interact collapse_a  collapse_via <> collapse_a.
  Axiom collapse_nontrivial_a' :
    interact collapse_a' collapse_via <> collapse_a'.

End MaterializedExistenceWithCollapse.


(* ================================================ *)
(*  FUNCTOR                                          *)
(* ================================================ *)

Module Make (D : MaterializedExistenceWithCollapse).

  Import D.
  Module DT := ExistenceTheory D.
  Module CT := MaterializedExistenceTheory D.
  Import DT CT.

  (* ============================================= *)
  (*  TARGET STRICTLY EXCEEDS EACH SOURCE          *)
  (*                                               *)
  (*  Both non-identity commitments feed straight  *)
  (*  into both_costs_advance, which gives the     *)
  (*  strict increase on flip_cost per step.       *)
  (* ============================================= *)

  Theorem collapse_flip_cost_a :
    flip_cost collapse_a < flip_cost collapse_target.
  Proof.
    pose proof (both_costs_advance collapse_a collapse_via
                  collapse_nontrivial_a) as [_ Hf].
    rewrite collapse_interacts_a in Hf. exact Hf.
  Qed.

  Theorem collapse_flip_cost_a' :
    flip_cost collapse_a' < flip_cost collapse_target.
  Proof.
    pose proof (both_costs_advance collapse_a' collapse_via
                  collapse_nontrivial_a') as [_ Hf].
    rewrite collapse_interacts_a' in Hf. exact Hf.
  Qed.

  (* ============================================= *)
  (*  MAX-FORM LOWER BOUND                         *)
  (*                                               *)
  (*  The target's flip_cost strictly dominates    *)
  (*  BOTH sources — so the target exceeds even    *)
  (*  the maximum. Qualitative Rice: no decoder.   *)
  (*  Quantitative Rice: the target lies above     *)
  (*  both sources in the flip-cost ordering.      *)
  (* ============================================= *)

  Theorem collapse_flip_cost_max :
    Nat.max (flip_cost collapse_a) (flip_cost collapse_a') <
    flip_cost collapse_target.
  Proof.
    pose proof collapse_flip_cost_a  as Ha.
    pose proof collapse_flip_cost_a' as Hb.
    lia.
  Qed.

  (* ============================================= *)
  (*  STORAGE LOWER BOUND                          *)
  (*                                               *)
  (*  Cost monotonicity on storage is weaker —     *)
  (*  equal, not strict, since a source carrying   *)
  (*  info_size 0 pays 0 for storage. Still        *)
  (*  worth stating: collapse never decreases      *)
  (*  storage.                                     *)
  (* ============================================= *)

  Theorem collapse_storage_cost_a :
    storage_cost collapse_a <= storage_cost collapse_target.
  Proof.
    pose proof (both_costs_advance collapse_a collapse_via
                  collapse_nontrivial_a) as [Hs _].
    rewrite collapse_interacts_a in Hs. exact Hs.
  Qed.

  Theorem collapse_storage_cost_a' :
    storage_cost collapse_a' <= storage_cost collapse_target.
  Proof.
    pose proof (both_costs_advance collapse_a' collapse_via
                  collapse_nontrivial_a') as [Hs _].
    rewrite collapse_interacts_a' in Hs. exact Hs.
  Qed.

End Make.
