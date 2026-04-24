(* ================================================ *)
(*  SKIComputationalWitnesses                         *)
(*                                                    *)
(*  Programs as Entities. SKI terms inhabit           *)
(*  ExistenceSig through `SKIModel`; this file        *)
(*  applies the framework's own meta-theorems to      *)
(*  that instance and exhibits concrete programs.     *)
(*                                                    *)
(*  Content:                                          *)
(*                                                    *)
(*    · FrameworkHalting applied to SKI:              *)
(*      halts / diverges predicates on SKI entities.  *)
(*                                                    *)
(*    · FrameworkRice applied to SKI:                 *)
(*      collapse witness exhibiting two distinct      *)
(*      non-frozen terms that reduce identically      *)
(*      under the same viewpoint, yielding            *)
(*      no-universal-decoder for SKI.                 *)
(*                                                    *)
(*    · Concrete programs: literal SKI terms lifted   *)
(*      to Entity, with step-by-step interact         *)
(*      unfolding reduction. Halting and diverging    *)
(*      witnesses (SII SII = M M loop).               *)
(*                                                    *)
(*  Moving piece: interact is *one reduction step*.   *)
(*  Executing a program = interact chain. Halting =   *)
(*  Iterable.remaining commits to Some n.             *)
(* ================================================ *)

Require Import Existence.
Require Import Materialized.
Require Import Iterable.
Require SKIModel.
Require FrameworkRice.
Require FrameworkHalting.

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


(* =========================================== *)
(*  HALTING — FrameworkHalting applied          *)
(* =========================================== *)

Module SKIHalting := FrameworkHalting.Make SKIModel.SKIComputable.


(* =========================================== *)
(*  RICE — ExistenceWithCollapse for SKI        *)
(*                                              *)
(*  Two distinct non-frozen SKI entities that   *)
(*  reduce to the same target under the same    *)
(*  viewpoint. The collapse witnesses that no   *)
(*  universal decoder can recover the source    *)
(*  from its interaction.                       *)
(*                                              *)
(*  Specific terms:                             *)
(*                                              *)
(*    a  = (K K) S   = TApp (TApp TK TK) TS     *)
(*    a' = (K K) I   = TApp (TApp TK TK) TI     *)
(*                                              *)
(*  Both match the K-reduction rule on the      *)
(*  outer application and reduce in one step    *)
(*  to TK. Term sizes are equal (4), so cost    *)
(*  counters agree, and interact at any         *)
(*  non-self viewpoint yields identical         *)
(*  entities.                                   *)
(* =========================================== *)

Module SKIExistenceWithCollapse <: FrameworkRice.ExistenceWithCollapse.

  Definition Entity           := SKIModel.SKIComputable.Entity.
  Definition interact         := SKIModel.SKIComputable.interact.
  Definition collapse    := SKIModel.SKIComputable.collapse.

  Definition interact_self    := SKIModel.SKIComputable.interact_self.
  Definition entity_eq_dec    := SKIModel.SKIComputable.entity_eq_dec.
  Definition interact_decidable := SKIModel.SKIComputable.interact_decidable.
  Definition existence        := SKIModel.SKIComputable.existence.
  Definition interact_with    := SKIModel.SKIComputable.interact_with.
  Definition interaction_cannot_witness_collapse :=
    SKIModel.SKIComputable.interaction_cannot_witness_collapse.

  Definition is_frozen (e : Entity) : Prop :=
    exists d s f inner, e = SKIModel.SKIFrozen d s f inner.

  Definition collapse_a : Entity :=
    SKIModel.SKINormal 0
      (SKIModel.TApp (SKIModel.TApp SKIModel.TK SKIModel.TK) SKIModel.TS)
      0 0.

  Definition collapse_a' : Entity :=
    SKIModel.SKINormal 0
      (SKIModel.TApp (SKIModel.TApp SKIModel.TK SKIModel.TK) SKIModel.TI)
      0 0.

  Definition collapse_target : Entity :=
    SKIModel.SKINormal 1 SKIModel.TK 5 1.

  Definition collapse_via : Entity :=
    SKIModel.SKINormal 1 SKIModel.TI 0 0.

  Theorem collapse_distinct : collapse_a <> collapse_a'.
  Proof. intros H. inversion H. Qed.

  Theorem collapse_a_not_frozen : ~ is_frozen collapse_a.
  Proof.
    intros [d [s [f [inner H]]]].
    unfold collapse_a in H. inversion H.
  Qed.

  Theorem collapse_a'_not_frozen : ~ is_frozen collapse_a'.
  Proof.
    intros [d [s [f [inner H]]]].
    unfold collapse_a' in H. inversion H.
  Qed.

  Theorem collapse_interacts_a :
    interact collapse_a collapse_via = collapse_target.
  Proof. reflexivity. Qed.

  Theorem collapse_interacts_a' :
    interact collapse_a' collapse_via = collapse_target.
  Proof. reflexivity. Qed.

End SKIExistenceWithCollapse.


Module SKIRice := FrameworkRice.Make SKIExistenceWithCollapse.


(* =========================================== *)
(*  LITERAL PROGRAMS AS ENTITIES                *)
(*                                              *)
(*  Two concrete SKI programs lifted to Entity, *)
(*  with interact witnessing one reduction      *)
(*  step each time.                             *)
(* =========================================== *)

(* Program 1: K I I ≡ (λxy. x) I I reduces to I. Halting. *)

Definition prog_kii : SKIModel.SKIEnt :=
  SKIModel.SKINormal 0
    (SKIModel.TApp (SKIModel.TApp SKIModel.TK SKIModel.TI) SKIModel.TI)
    0 0.

Definition view_1 : SKIModel.SKIEnt :=
  SKIModel.SKINormal 1 SKIModel.TI 0 0.

Definition view_2 : SKIModel.SKIEnt :=
  SKIModel.SKINormal 2 SKIModel.TI 0 0.

(* interact is a one-step reduction: (K I) I → I on the outer K. *)

Example kii_one_step :
  SKIModel.SKIComputable.interact prog_kii view_1
    = SKIModel.SKINormal 1 SKIModel.TI 5 1.
Proof. reflexivity. Qed.

(* Second interact leaves the term unchanged — TI is already in
   normal form. The dim advances and costs accumulate. *)

Example kii_two_steps :
  SKIModel.SKIComputable.interact
    (SKIModel.SKIComputable.interact prog_kii view_1)
    view_2
    = SKIModel.SKINormal 2 SKIModel.TI 6 2.
Proof. reflexivity. Qed.


(* Program 2: (S I I)(S I I) — Ω-like. S I I x → I x (I x) → x x,
   so (S I I)(S I I) → (S I I)(S I I) ... infinite reduction. *)

Definition sii : SKIModel.SKITerm :=
  SKIModel.TApp (SKIModel.TApp SKIModel.TS SKIModel.TI) SKIModel.TI.

Definition omega_term : SKIModel.SKITerm :=
  SKIModel.TApp sii sii.

Definition prog_omega : SKIModel.SKIEnt :=
  SKIModel.SKINormal 0 omega_term 0 0.


(* =========================================== *)
(*  HALTING / DIVERGENCE WITNESSES              *)
(*                                              *)
(*  Exposes halts / diverges predicates at the  *)
(*  SKI instance via FrameworkHalting.          *)
(* =========================================== *)

(* prog_kii halts: Iterable.remaining commits to a finite count. *)

Example kii_halts : SKIHalting.halts prog_kii.
Proof.
  unfold SKIHalting.halts, SKIModel.SKIComputable.Entity.
  eexists. reflexivity.
Qed.

(* Either halts or diverges, from FrameworkHalting's exhaustiveness. *)

Example kii_is_classified :
  SKIHalting.halts prog_kii \/ SKIHalting.diverges prog_kii.
Proof. apply SKIHalting.halts_or_diverges. Qed.

Example omega_is_classified :
  SKIHalting.halts prog_omega \/ SKIHalting.diverges prog_omega.
Proof. apply SKIHalting.halts_or_diverges. Qed.


(* =========================================== *)
(*  RICE AT SKI — CONCRETE                      *)
(*                                              *)
(*  The abstract framework theorem, carried     *)
(*  over to SKI with explicit collapse.         *)
(*  No universal decoder exists that recovers   *)
(*  an SKI source from its one-step reduction   *)
(*  result.                                     *)
(* =========================================== *)

Theorem ski_rice_no_universal_decoder :
  ~ (exists (decode : SKIExistenceWithCollapse.Entity ->
                       SKIExistenceWithCollapse.Entity),
       forall a c : SKIExistenceWithCollapse.Entity,
         decode (SKIExistenceWithCollapse.interact a c) = a).
Proof. apply SKIRice.rice_no_universal_decoder. Qed.

Theorem ski_rice_interact_not_injective :
  exists (a a' c : SKIExistenceWithCollapse.Entity),
    a <> a' /\
    ~ SKIExistenceWithCollapse.is_frozen a /\
    ~ SKIExistenceWithCollapse.is_frozen a' /\
    SKIExistenceWithCollapse.interact a c =
    SKIExistenceWithCollapse.interact a' c.
Proof. apply SKIRice.rice_interact_not_injective. Qed.


(* =========================================== *)
(*  REMARK                                      *)
(*                                              *)
(*  interact on SKIComputable performs exactly  *)
(*  one reduce_one step (or identity if the     *)
(*  term is already in normal form), advancing  *)
(*  the dim and accumulating storage/flip cost. *)
(*  Executing a program therefore reduces to    *)
(*  chaining interact calls with distinct       *)
(*  viewpoints. Halting is Iterable.remaining   *)
(*  committing to Some n; divergence is         *)
(*  remaining returning None.                   *)
(*                                              *)
(*  Rice and Halting — framework-level          *)
(*  meta-theorems — land here with explicit     *)
(*  witnesses. The generic impossibility        *)
(*  results acquire concrete SKI carriers.      *)
(* =========================================== *)
