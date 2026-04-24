(* ================================================ *)
(*  SKIWitnesses                                      *)
(*                                                    *)
(*  SKI as a concrete carrier for the framework      *)
(*  meta-theorems. SKI itself (Existence/Bizarre/    *)
(*  SKI.v) provides the ExistenceSig instance; this  *)
(*  file applies Rice and the constructive halting   *)
(*  theorems to it with explicit term witnesses.     *)
(*                                                    *)
(*  Two concepts share the name "collapse":          *)
(*                                                    *)
(*    · Framework collapse (Existence.v):            *)
(*      a relation between entities, meaning no      *)
(*      viewpoint can witness a distinction. SKI     *)
(*      has no such pairs — for any a <> b, the      *)
(*      viewpoint c = a already separates them       *)
(*      (interact a a = a, interact b a <> a). So    *)
(*      SKI.collapse is False, and                   *)
(*      interaction_cannot_witness_collapse holds    *)
(*      vacuously.                                    *)
(*                                                    *)
(*    · Rice-level collapse (this file): two         *)
(*      distinct non-frozen entities that reach the  *)
(*      same target through some specific viewpoint. *)
(*      SKI exhibits this: (K K) S and (K K) I are   *)
(*      both reducible, both reduce in one step to K.*)
(*      At any viewpoint c distinct from both, the   *)
(*      interactions produce K on both sides.        *)
(*                                                    *)
(*  Rice's ExistenceWithCollapse captures the second *)
(*  notion only. It is opt-in: an instance supplies  *)
(*  is_frozen and four entity witnesses. For SKI,    *)
(*  is_frozen := halted — halted terms t, when       *)
(*  interacted with c <> t, yield TApp t c, which    *)
(*  carries t injectively and therefore cannot merge *)
(*  with another halted term's interaction result.   *)
(*  The Rice impossibility is a statement about the  *)
(*  non-halted subset.                               *)
(* ================================================ *)

Require Import Existence.
Require Import Theory.
Require Import SKI.
Require Import Rice.
Require Import FrameworkHalting.


(* ================================================ *)
(*  RICE AT SKI                                      *)
(*                                                    *)
(*  Opt into ExistenceWithCollapse.                  *)
(*                                                    *)
(*    is_frozen := halted                            *)
(*    a      = (K K) S                               *)
(*    a'     = (K K) I                               *)
(*    target = K                                     *)
(*    via    = I                                     *)
(*                                                    *)
(*  Both a and a' match the K-reduction rule on the  *)
(*  outer TApp and reduce_one to TK. Neither is      *)
(*  halted. With via = TI, distinct from both a and  *)
(*  a', interact walks to reduce_one on both sides.  *)
(* ================================================ *)

Module SKIWithCollapse <: ExistenceWithCollapse.
  Include SKI.

  Definition is_frozen : Entity -> Prop := halted.

  Definition collapse_a      : Entity :=
    TApp (TApp TK TK) TS.

  Definition collapse_a'     : Entity :=
    TApp (TApp TK TK) TI.

  Definition collapse_target : Entity := TK.

  Definition collapse_via    : Entity := TI.

  Theorem collapse_distinct : collapse_a <> collapse_a'.
  Proof. intros H. inversion H. Qed.

  Theorem collapse_a_not_frozen : ~ is_frozen collapse_a.
  Proof.
    unfold is_frozen, halted, collapse_a. simpl.
    intros H. inversion H.
  Qed.

  Theorem collapse_a'_not_frozen : ~ is_frozen collapse_a'.
  Proof.
    unfold is_frozen, halted, collapse_a'. simpl.
    intros H. inversion H.
  Qed.

  Theorem collapse_interacts_a :
    interact collapse_a collapse_via = collapse_target.
  Proof. reflexivity. Qed.

  Theorem collapse_interacts_a' :
    interact collapse_a' collapse_via = collapse_target.
  Proof. reflexivity. Qed.

End SKIWithCollapse.


Module SKIRice := Make SKIWithCollapse.


(* Rice's four impossibility layers, re-exposed with SKI types. *)

Theorem ski_rice_instance_has_loss :
  exists (a a' c target : SKITerm),
    a <> a' /\
    ~ halted a /\
    ~ halted a' /\
    SKI.interact a c = target /\
    SKI.interact a' c = target.
Proof. exact SKIRice.rice_instance_has_loss. Qed.

Theorem ski_rice_interact_not_injective :
  exists (a a' c : SKITerm),
    a <> a' /\
    ~ halted a /\
    ~ halted a' /\
    SKI.interact a c = SKI.interact a' c.
Proof. exact SKIRice.rice_interact_not_injective. Qed.

Theorem ski_rice_no_universal_decoder :
  ~ (exists (decode : SKITerm -> SKITerm),
       forall (a c : SKITerm),
         decode (SKI.interact a c) = a).
Proof. exact SKIRice.rice_no_universal_decoder. Qed.

Theorem ski_rice_every_decoder_has_counterexample :
  forall (decode : SKITerm -> SKITerm),
    (forall (a c : SKITerm), decode (SKI.interact a c) = a) ->
    False.
Proof. exact SKIRice.rice_every_decoder_has_counterexample. Qed.


(* ================================================ *)
(*  LITERAL PROGRAMS AS ENTITIES                    *)
(*                                                    *)
(*  interact is one reduce_one step (or TApp merge   *)
(*  when the term is already halted). Chaining       *)
(*  interact with fresh viewpoints walks the         *)
(*  reduction. Halting means reduce_n n lands on a   *)
(*  halted term for some n.                          *)
(* ================================================ *)

(* Program 1: (K I) I — one K-reduction to I, halts. *)

Definition prog_kii : SKITerm :=
  TApp (TApp TK TI) TI.

Example kii_reduce_once : reduce_one prog_kii = TI.
Proof. reflexivity. Qed.

Example kii_halted_after_one :
  halted (reduce_n 1 prog_kii).
Proof. simpl. unfold halted. reflexivity. Qed.

Example kii_halts : halts prog_kii.
Proof. exists 1. simpl. unfold halted. reflexivity. Qed.

(* Viewpoint TS is distinct from prog_kii, so interact advances
   one reduction step, yielding TI. *)
Example kii_interact_step :
  SKI.interact prog_kii TS = TI.
Proof. reflexivity. Qed.


(* Program 2: (S I I)(S I I) — Ω-like. Reduces in one step to
   a term containing two further SII redexes, and the reduction
   trace does not shrink. A formal divergence proof needs a
   progress invariant and is not produced here — we only record
   the single-step reduction. The absence of a halts/diverges
   classification at this level is exactly what SKI's
   Turing-completeness forces: no constructive decider exists. *)

Definition sii : SKITerm :=
  TApp (TApp TS TI) TI.

Definition omega_term : SKITerm :=
  TApp sii sii.

Example omega_one_step :
  reduce_one omega_term =
    TApp (TApp TI sii) (TApp TI sii).
Proof. reflexivity. Qed.


(* ================================================ *)
(*  CONSTRUCTIVE HALTING WITNESSES                   *)
(*                                                    *)
(*  FrameworkHalting exposes the constructive        *)
(*  theorems. halted is decidable; halted is         *)
(*  preserved under further reduction; halts and     *)
(*  diverges are mutually exclusive. The classical   *)
(*  halts \/ diverges dichotomy is deliberately      *)
(*  absent (it would require LEM on halts).          *)
(* ================================================ *)

Example kii_halted_decidable :
  {halted prog_kii} + {~ halted prog_kii}.
Proof. apply halted_decidable. Qed.

Example kii_reduced_stays_halted :
  forall n, halted (reduce_n n (reduce_n 1 prog_kii)).
Proof.
  intros n. apply halted_preserved_under_reduce_n.
  simpl. unfold halted. reflexivity.
Qed.

Example kii_cannot_both_halt_and_diverge :
  halts prog_kii -> diverges prog_kii -> False.
Proof. apply not_halts_and_diverges. Qed.
