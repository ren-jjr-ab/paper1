(* Derived theorems from ExistenceSig.

   Ported from new/Existence/Theory.v with one structural
   change: the prior `is_terminal_impossible` is removed.

   Under the modified framework, "terminal" entities
   (those satisfying `forall b, interact a b = a`) are
   precisely the frozen entities defined in Existence.v.
   The new `interact_with` is a dichotomy: every entity
   is either frozen or has a moving partner. The
   constructive replacement for the prior impossibility
   theorem is `nonfrozen_has_partner` below — frozen
   entities exist by design (lattice top, lazy infinity,
   etc.); only non-frozen entities are required to move. *)

Require Import Existence.

Module ExistenceTheory (D : ExistenceSig).

  Import D.

  (* ================================================ *)
  (*  INTERACTION DECIDABILITY                        *)
  (* ================================================ *)

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply entity_eq_dec. Qed.

  (* ================================================ *)
  (*  INTERACTION EQUALITY AT A VIEWPOINT             *)
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
  (* ================================================ *)

  Definition preserves_at
    (P : Entity -> Prop) (c : Entity) : Prop :=
    forall (a b : Entity),
      interact_eq_at a b c -> (P a <-> P b).

  (* ================================================ *)
  (*  DICHOTOMY                                       *)
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
  (*  FROZEN ENTITIES                                 *)
  (*                                                  *)
  (*  An entity is frozen iff it absorbs every        *)
  (*  interaction. This is the framework's native     *)
  (*  expression of stuck/terminal state — lattice    *)
  (*  top, lazy-infinity carriers, etc. The prior     *)
  (*  `is_terminal_impossible` theorem is gone:       *)
  (*  the "terminal" entities of the old definition   *)
  (*  are precisely these frozen entities, and the    *)
  (*  new framework allows them by design.            *)
  (* ================================================ *)

  Definition frozen (a : Entity) : Prop :=
    forall b : Entity, interact a b = a.

  (* Constructive form of the dynamic side of
     interact_with's dichotomy. Frozen entities are
     exempt from motion; non-frozen ones always have
     a partner that distinguishes them from their
     self-image. *)

  Theorem nonfrozen_has_partner :
    forall a, ~ frozen a -> exists b, interact a b <> a.
  Proof.
    intros a Hnf.
    destruct (interact_with a) as [Hf | Hp].
    - exfalso. apply Hnf. exact Hf.
    - exact Hp.
  Qed.

  (* ================================================ *)
  (*  VIEWPOINT FIXED POINTS                          *)
  (*                                                  *)
  (*  Every viewpoint c fixes at least one entity —   *)
  (*  c itself, by interact_self.                     *)
  (* ================================================ *)

  Theorem viewpoint_has_fixed_point :
    forall c, exists a, interact a c = a.
  Proof.
    intro c. exists c. apply interact_self.
  Qed.

  (* ================================================ *)
  (*  COLLAPSE FORCES DISTINCTNESS                    *)
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
