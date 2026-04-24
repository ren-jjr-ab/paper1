(* Derived theorems from ExistenceSig — ported from framework/Existence.v *)

Require Import Existence.

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
