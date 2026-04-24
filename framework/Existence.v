(* =========================================== *)
(*  Existence — Entity-only, parallel          *)
(*                                             *)
(*  Three primitives, five axioms. Entity is   *)
(*  the sole type. interact is a binary        *)
(*  operation on entities. collapse is a       *)
(*  binary relation that records equalities    *)
(*  no interaction can witness.                *)
(*                                             *)
(*  No hierarchy, no dimension, no layering —  *)
(*  entities are parallel, and any roles       *)
(*  (freeze, taint, etc.) are played by        *)
(*  particular entities in an instance, not    *)
(*  by framework primitives.                   *)
(*                                             *)
(*  Signature:                                 *)
(*    Entity        : Type                     *)
(*    interact      : Entity -> Entity         *)
(*                    -> Entity                *)
(*    collapse      : Entity -> Entity         *)
(*                    -> Prop                  *)
(*                                             *)
(*  Axioms:                                    *)
(*    interact_self                            *)
(*      interact a a = a                       *)
(*    entity_eq_dec                            *)
(*      {a = b} + {a <> b}                     *)
(*    existence                                *)
(*      exists a b, a <> b                     *)
(*    interact_with                            *)
(*      forall a, exists b, interact a b <> a  *)
(*    interaction_cannot_witness_collapse      *)
(*      collapse a b ->                        *)
(*      forall c, interact a c <> interact b c *)
(*                                             *)
(*  Meta-level: we use propositional equality  *)
(*  as Leibniz identity (Coq's built-in `eq`). *)
(*  This is a meta-theorem of the host type    *)
(*  system, not a framework axiom — the        *)
(*  framework operates inside whatever logical *)
(*  context provides it.                       *)
(*                                             *)
(*  Derived theory (ExistenceTheory):          *)
(*    interact_eq_at, preserves_at, dichotomy, *)
(*    interact_decidable (from entity_eq_dec), *)
(*    interaction_reflects_diff,               *)
(*    is_terminal, is_terminal_impossible,     *)
(*    viewpoint_has_fixed_point,               *)
(*    collapse_distinct_entities,              *)
(*    collapse_irreflexive,                    *)
(*    observationally_equivalent,              *)
(*    observational_equivalence_reflexive,     *)
(*    observational_equivalence_excludes_      *)
(*      collapse.                              *)
(*                                             *)
(*  Extensions:                                *)
(*    framework/Materialized.v                 *)
(*      info_size, storage_cost, flip_cost     *)
(*    framework/Iterable.v                     *)
(*      remaining                              *)
(* =========================================== *)

Module Type ExistenceSig.

  Parameter Entity : Type.

  (* Binary operation on entities. interact a b is
     the result of a interacting with b. No
     precondition — every pair is a valid
     application. The meaning of an interaction at a
     pair where no natural relation exists is
     instance-determined. *)
  Parameter interact : Entity -> Entity -> Entity.

  (* Binary relation on entities. collapse a b
     asserts a user-level equivalence that no
     interaction is required to witness — two
     entities can be declared equal by collapse
     while remaining distinguishable under every
     viewpoint. *)
  Parameter collapse : Entity -> Entity -> Prop.

  (* ============================================= *)
  (*  AXIOMS                                       *)
  (* ============================================= *)

  (* Interacting with itself returns the entity
     unchanged. *)
  Axiom interact_self : forall a : Entity, interact a a = a.

  (* Entity equality is decidable. *)
  Axiom entity_eq_dec :
    forall a b : Entity, {a = b} + {a <> b}.

  (* At least two entities exist — there is some
     difference for the framework to carry. *)
  Axiom existence : exists a b : Entity, a <> b.

  (* No entity is static under all interactions:
     every entity is moved by some partner. This
     replaces any dedicated "time" axis — time is
     whatever viewpoint an instance identifies as
     the one whose interactions advance the state. *)
  Axiom interact_with :
    forall a : Entity, exists b, interact a b <> a.

  (* Collapse is not derivable from interaction. If
     two entities are related by collapse, their
     interactions disagree at every viewpoint — so
     no interaction-derived equality can ever bridge
     them from inside the framework. *)
  Axiom interaction_cannot_witness_collapse :
    forall (a b : Entity),
      collapse a b ->
      forall c : Entity,
        interact a c <> interact b c.

End ExistenceSig.


(* =========================================== *)
(*  THEORY FUNCTOR                             *)
(* =========================================== *)

Module ExistenceTheory (D : ExistenceSig).

  Import D.

  (* ================================================ *)
  (*  INTERACTION DECIDABILITY                        *)
  (*                                                  *)
  (*  Derived from entity_eq_dec: if entities are     *)
  (*  decidably equal, so are their interaction       *)
  (*  results at any common viewpoint.                *)
  (* ================================================ *)

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply entity_eq_dec. Qed.

  (* ================================================ *)
  (*  INTERACTION EQUALITY AT A VIEWPOINT             *)
  (*                                                  *)
  (*  "=" in the paper: a and b interact to the same  *)
  (*  result through viewpoint c.                     *)
  (* ================================================ *)

  Definition interact_eq_at (a b c : Entity) : Prop :=
    interact a c = interact b c.

  Theorem interact_eq_at_refl : forall a c, interact_eq_at a a c.
  Proof. intros. unfold interact_eq_at. reflexivity. Qed.

  Theorem interact_eq_at_sym :
    forall a b c, interact_eq_at a b c -> interact_eq_at b a c.
  Proof.
    intros a b c H. unfold interact_eq_at in *. symmetry. exact H.
  Qed.

  Theorem interact_eq_at_trans :
    forall a b c d,
      interact_eq_at a b d -> interact_eq_at b c d -> interact_eq_at a c d.
  Proof.
    intros a b c d H1 H2. unfold interact_eq_at in *.
    rewrite H1. exact H2.
  Qed.

  (* ================================================ *)
  (*  PROPERTY PRESERVATION AT A VIEWPOINT            *)
  (*                                                  *)
  (*  A property P is "preserved at c" iff entities   *)
  (*  that interact to the same result at c agree     *)
  (*  on P.                                           *)
  (* ================================================ *)

  Definition preserves_at
    (P : Entity -> Prop) (c : Entity) : Prop :=
    forall (a b : Entity),
      interact_eq_at a b c -> (P a <-> P b).

  (* ================================================ *)
  (*  DICHOTOMY                                       *)
  (*                                                  *)
  (*  At any viewpoint, two entities either interact  *)
  (*  to the same result or to different results.     *)
  (* ================================================ *)

  Theorem dichotomy :
    forall a b c,
      {interact_eq_at a b c} + {~ interact_eq_at a b c}.
  Proof.
    intros a b c. unfold interact_eq_at. apply interact_decidable.
  Qed.

  (* ================================================ *)
  (*  INTERACTION REFLECTS DIFFERENCE                 *)
  (* ================================================ *)

  Theorem interaction_reflects_diff :
    forall a b c,
      interact a c <> interact b c -> a <> b.
  Proof.
    intros a b c Hne Heq. apply Hne. rewrite Heq. reflexivity.
  Qed.

  (* ================================================ *)
  (*  TERMINAL ENTITIES ARE IMPOSSIBLE                *)
  (*                                                  *)
  (*  is_terminal a — a stays itself under every      *)
  (*  viewpoint. interact_with rules this out: no     *)
  (*  entity is fixed by every interaction.           *)
  (* ================================================ *)

  Definition is_terminal (a : Entity) : Prop :=
    forall b, interact a b = a.

  Theorem is_terminal_impossible :
    forall a, ~ is_terminal a.
  Proof.
    intros a Hterm.
    destruct (interact_with a) as [b Hne].
    apply Hne. apply Hterm.
  Qed.

  (* ================================================ *)
  (*  VIEWPOINT FIXED POINTS                          *)
  (*                                                  *)
  (*  The dual of is_terminal_impossible. Every       *)
  (*  viewpoint c fixes at least one entity — c       *)
  (*  itself, by interact_self. Combined with         *)
  (*  is_terminal_impossible, the fixed set of any    *)
  (*  viewpoint is non-empty but never exhaustive.    *)
  (* ================================================ *)

  Theorem viewpoint_has_fixed_point :
    forall c, exists a, interact a c = a.
  Proof.
    intro c. exists c. apply interact_self.
  Qed.

  (* ================================================ *)
  (*  COLLAPSE FORCES DISTINCTNESS                    *)
  (*                                                  *)
  (*  interaction_cannot_witness_collapse, read       *)
  (*  through the self-viewpoint, forces collapse     *)
  (*  pairs to be distinct — and therefore collapse   *)
  (*  itself to be irreflexive. ≡ is reflexive; ≈ is  *)
  (*  irreflexive. That is the first sign of their    *)
  (*  antipodal position.                             *)
  (* ================================================ *)

  Theorem collapse_distinct_entities :
    forall a b, collapse a b -> a <> b.
  Proof.
    intros a b Hconv Heq.
    subst b.
    apply (interaction_cannot_witness_collapse a a Hconv a).
    reflexivity.
  Qed.

  Theorem collapse_irreflexive :
    forall a, ~ collapse a a.
  Proof.
    intros a H.
    apply (collapse_distinct_entities a a H). reflexivity.
  Qed.

  (* ================================================ *)
  (*  OBSERVATIONAL EQUIVALENCE vs COLLAPSE           *)
  (*                                                  *)
  (*  Two entities are observationally equivalent     *)
  (*  when they agree at every viewpoint. Collapse    *)
  (*  denies exactly what observational equivalence   *)
  (*  grants: no pair can satisfy both.               *)
  (* ================================================ *)

  Definition observationally_equivalent (a b : Entity) : Prop :=
    forall c, interact a c = interact b c.

  Theorem observational_equivalence_reflexive :
    forall a, observationally_equivalent a a.
  Proof.
    intros a c. reflexivity.
  Qed.

  Theorem observational_equivalence_excludes_collapse :
    forall a b,
      observationally_equivalent a b -> ~ collapse a b.
  Proof.
    intros a b Hobs Hconv.
    apply (interaction_cannot_witness_collapse a b Hconv a).
    apply Hobs.
  Qed.

End ExistenceTheory.
