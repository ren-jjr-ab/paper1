(* ========================================== *)
(*  FrameworkRice                              *)
(*                                             *)
(*  Rice-style impossibility on the Existence  *)
(*  layer, parameterized by an instance-level  *)
(*  is_frozen predicate and a non-frozen       *)
(*  collapse witness.                          *)
(*                                             *)
(*  Classical Rice: non-trivial semantic       *)
(*  properties of programs are undecidable.    *)
(*                                             *)
(*  Framework analog: IF an instance exhibits  *)
(*  a collapse on non-frozen entities (two     *)
(*  distinct non-frozen sources reaching the   *)
(*  same target through some viewpoint),       *)
(*  THEN no universal decoder function can     *)
(*  exist that recovers the source from its    *)
(*  interaction.                               *)
(*                                             *)
(*  Why non-frozen specifically: freeze is     *)
(*  the framework's single escape from         *)
(*  interaction collapse. Frozen entities are  *)
(*  structurally prevented from merging        *)
(*  (freeze_preserves_existence at the         *)
(*  instance level). So the Rice-style         *)
(*  impossibility is a claim about what        *)
(*  happens when you don't freeze — the        *)
(*  non-frozen subset of entities.             *)
(*                                             *)
(*  Instances where every distinct pair is     *)
(*  frozen (or where no non-frozen pair        *)
(*  collapses) can still satisfy decoder       *)
(*  existence on their own subset. The         *)
(*  impossibility is structural: it names the  *)
(*  boundary between frozen and non-frozen     *)
(*  as the boundary of decodability.           *)
(*                                             *)
(*  The is_frozen predicate and the collapse   *)
(*  witnesses are Parameters: instances opt in *)
(*  by supplying them. Instances without a     *)
(*  non-frozen collapse cannot apply the       *)
(*  functor; the Rice result does not apply    *)
(*  to them.                                   *)
(* ========================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Require Import Existence.
Require Import Theory.

(* ================================================ *)
(*  MODULE TYPE FOR INSTANCES WITH NON-FROZEN       *)
(*  COLLAPSE                                        *)
(*                                                  *)
(*  Extends ExistenceSig with the is_frozen         *)
(*  predicate and an explicit witness: two          *)
(*  distinct non-frozen entities that reach the     *)
(*  same target through some viewpoint.             *)
(* ================================================ *)

Module Type ExistenceWithCollapse.
  Include ExistenceSig.

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

End ExistenceWithCollapse.

(* ================================================ *)
(*  FRAMEWORK RICE FUNCTOR                          *)
(* ================================================ *)

Module Make (D : ExistenceWithCollapse).

  Import D.
  Module DT := ExistenceTheory D.
  Import DT.

  (* ====== Rice layer 1: the instance has a loss ====== *)

  Theorem rice_instance_has_loss :
    exists (a a' : Entity) (c target : Entity),
      a <> a' /\
      ~ is_frozen a /\
      ~ is_frozen a' /\
      interact a c = target /\
      interact a' c = target.
  Proof.
    exists collapse_a, collapse_a', collapse_via, collapse_target.
    split; [exact collapse_distinct |].
    split; [exact collapse_a_not_frozen |].
    split; [exact collapse_a'_not_frozen |].
    split; [exact collapse_interacts_a | exact collapse_interacts_a'].
  Qed.

  (* ====== Rice layer 2: interact is not injective on non-frozen ====== *)

  Theorem rice_interact_not_injective :
    exists (a a' c : Entity),
      a <> a' /\
      ~ is_frozen a /\
      ~ is_frozen a' /\
      interact a c = interact a' c.
  Proof.
    exists collapse_a, collapse_a', collapse_via.
    split; [exact collapse_distinct |].
    split; [exact collapse_a_not_frozen |].
    split; [exact collapse_a'_not_frozen |].
    rewrite collapse_interacts_a. rewrite collapse_interacts_a'. reflexivity.
  Qed.

  (* ====== Rice layer 3: no universal decoder ====== *)

  Theorem rice_no_universal_decoder :
    ~ (exists (decode : Entity -> Entity),
         forall (a c : Entity),
           decode (interact a c) = a).
  Proof.
    intros [decode Hdecode].
    pose proof (Hdecode collapse_a collapse_via) as Da.
    pose proof (Hdecode collapse_a' collapse_via) as Da'.
    rewrite collapse_interacts_a in Da.
    rewrite collapse_interacts_a' in Da'.
    apply collapse_distinct. rewrite <- Da. exact Da'.
  Qed.

  (* ====== Rice layer 4: every attempted decoder fails ====== *)

  Theorem rice_every_decoder_has_counterexample :
    forall (decode : Entity -> Entity),
      (forall (a c : Entity), decode (interact a c) = a) ->
      False.
  Proof.
    intros decode Hdecode.
    apply rice_no_universal_decoder.
    exists decode. exact Hdecode.
  Qed.

End Make.
