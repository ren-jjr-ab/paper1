(* =========================================== *)
(*  Existence — Entity-only, parallel          *)
(*                                             *)
(*  Three primitives, five axioms. Entity is   *)
(*  the sole type. interact is a binary        *)
(*  operation on entities. convention_eq is a  *)
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
(*    convention_eq : Entity -> Entity         *)
(*                    -> Prop                  *)
(*                                             *)
(*  Axioms:                                    *)
(*    interact_self                            *)
(*      interact a a = a                       *)
(*    interact_decidable                       *)
(*      {interact a c = interact b c}          *)
(*       + {interact a c <> interact b c}      *)
(*    existence                                *)
(*      exists a b, a <> b                     *)
(*    interact_with                            *)
(*      forall a, exists b, interact a b <> a  *)
(*    convention_not_derivable                 *)
(*      convention_eq a b ->                   *)
(*      forall c, interact a c <> interact b c *)
(*                                             *)
(*  Derived theory (ExistenceTheory):          *)
(*    interact_eq_at, preserves_at, dichotomy, *)
(*    interaction_reflects_diff,               *)
(*    is_terminal, is_terminal_impossible,     *)
(*    viewpoint_has_fixed_point,               *)
(*    convention_eq_distinct,                  *)
(*    convention_eq_irreflexive,               *)
(*    observationally_equivalent,              *)
(*    observational_equivalence_reflexive,     *)
(*    observational_equivalence_excludes_      *)
(*      convention.                            *)
(*                                             *)
(*  Extensions:                                *)
(*    framework/Computable.v                   *)
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

  (* Binary relation on entities. convention_eq a b
     asserts a user-level equivalence that no
     interaction is required to witness — two
     entities can be declared equal by convention
     while remaining distinguishable under every
     viewpoint. *)
  Parameter convention_eq : Entity -> Entity -> Prop.

  (* ============================================= *)
  (*  AXIOMS                                       *)
  (* ============================================= *)

  (* Interacting with itself returns the entity
     unchanged. *)
  Axiom interact_self : forall a : Entity, interact a a = a.

  (* Interaction equality at a common viewpoint is
     decidable. *)
  Axiom interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.

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

  (* Convention is not derivable from interaction. If
     two entities are related by convention, their
     interactions disagree at every viewpoint — so
     no interaction-derived equality can ever bridge
     them from inside the framework. *)
  Axiom convention_not_derivable :
    forall (a b : Entity),
      convention_eq a b ->
      forall c : Entity,
        interact a c <> interact b c.

End ExistenceSig.


(* =========================================== *)
(*  THEORY FUNCTOR                             *)
(* =========================================== *)

Module ExistenceTheory (D : ExistenceSig).

  Import D.

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
  (*  CONVENTION FORCES DISTINCTNESS                  *)
  (*                                                  *)
  (*  convention_not_derivable, read through the      *)
  (*  self-viewpoint, forces convention-equal pairs   *)
  (*  to be distinct — and therefore convention_eq    *)
  (*  itself to be irreflexive. ≡ is reflexive; ≈ is  *)
  (*  irreflexive. That is the first sign of their    *)
  (*  antipodal position.                             *)
  (* ================================================ *)

  Theorem convention_eq_distinct :
    forall a b, convention_eq a b -> a <> b.
  Proof.
    intros a b Hconv Heq.
    subst b.
    apply (convention_not_derivable a a Hconv a).
    reflexivity.
  Qed.

  Theorem convention_eq_irreflexive :
    forall a, ~ convention_eq a a.
  Proof.
    intros a H.
    apply (convention_eq_distinct a a H). reflexivity.
  Qed.

  (* ================================================ *)
  (*  OBSERVATIONAL EQUIVALENCE vs CONVENTION         *)
  (*                                                  *)
  (*  Two entities are observationally equivalent     *)
  (*  when they agree at every viewpoint. Convention  *)
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

  Theorem observational_equivalence_excludes_convention :
    forall a b,
      observationally_equivalent a b -> ~ convention_eq a b.
  Proof.
    intros a b Hobs Hconv.
    apply (convention_not_derivable a b Hconv a).
    apply Hobs.
  Qed.

End ExistenceTheory.
