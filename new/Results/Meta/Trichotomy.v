(* ========================================== *)
(*  Trichotomy                                 *)
(*                                             *)
(*  The three paper relations ≡, =, ≈ capture  *)
(*  the distinct ways two entities may be      *)
(*  related:                                   *)
(*                                             *)
(*    paper_equiv       (≡) the same entity    *)
(*    paper_projection  (=) distinct entities  *)
(*                          whose interactions *)
(*                          coincide at some   *)
(*                          witness            *)
(*    paper_convention  (≈) equated by         *)
(*                          convention, not    *)
(*                          derivable from     *)
(*                          any interaction    *)
(*                                             *)
(*  These three are pairwise disjoint: no pair *)
(*  of entities inhabits two of them at once.  *)
(*                                             *)
(*    ≡ excludes = because = requires a ≠ b.   *)
(*    ≡ excludes ≈ because a ≡ b reduces ≈ to  *)
(*      a ≈ a, which convention must refute    *)
(*      by interact a a ≠ interact a a —       *)
(*      absurd.                                *)
(*    = excludes ≈ because convention denies   *)
(*      every interaction agreement, while =   *)
(*      supplies one.                          *)
(*                                             *)
(*  Beyond pairwise disjointness, ≡ and ≈ sit  *)
(*  at opposite ends of a spectrum that asks   *)
(*  how much interaction can reveal agreement: *)
(*                                             *)
(*    ≡  ⇒  ∀c, interact a c = interact b c    *)
(*    ≈  ⇒  ∀c, interact a c ≠ interact b c    *)
(*                                             *)
(*  Same quantifier, opposite verdict. ≡ is    *)
(*  reflexive, ≈ is irreflexive.               *)
(*                                             *)
(*  Wrapped as a functor over ExistenceSig.    *)
(*  Adds no framework axioms.                  *)
(* ========================================== *)

Require Import Existence.
Require Import Theory.

Module Make (D : ExistenceSig).

  Import D.
  Module DT := ExistenceTheory D.
  Import DT.

  (* ================================================ *)
  (*  PAPER-LEVEL TRICHOTOMY                          *)
  (* ================================================ *)

  Definition paper_equiv (a b : Entity) : Prop :=
    a = b.

  Definition paper_projection (a b : Entity) : Prop :=
    (exists c : Entity, interact a c = interact b c) /\
    a <> b.

  Definition paper_convention (a b : Entity) : Prop :=
    collapse a b.

  (* ================================================ *)
  (*  PAIRWISE DISJOINTNESS                           *)
  (* ================================================ *)

  Theorem paper_equiv_excludes_projection :
    forall a b, ~ (paper_equiv a b /\ paper_projection a b).
  Proof.
    intros a b [Heq [_ Hneq]].
    apply Hneq. exact Heq.
  Qed.

  Theorem paper_equiv_excludes_convention :
    forall a b, ~ (paper_equiv a b /\ paper_convention a b).
  Proof.
    intros a b [Heq Hconv].
    unfold paper_equiv in Heq. subst b.
    unfold paper_convention in Hconv.
    apply (interaction_cannot_witness_collapse a a Hconv a).
    reflexivity.
  Qed.

  Theorem paper_projection_excludes_convention :
    forall a b, ~ (paper_projection a b /\ paper_convention a b).
  Proof.
    intros a b [[[c Hpeq] _] Hconv].
    unfold paper_convention in Hconv.
    exact (interaction_cannot_witness_collapse a b Hconv c Hpeq).
  Qed.

  Theorem paper_trichotomy_pairwise_disjoint :
    forall a b,
      (~ (paper_equiv a b /\ paper_projection a b)) /\
      (~ (paper_equiv a b /\ paper_convention a b)) /\
      (~ (paper_projection a b /\ paper_convention a b)).
  Proof.
    intros a b.
    split; [apply paper_equiv_excludes_projection |].
    split; [apply paper_equiv_excludes_convention |].
    apply paper_projection_excludes_convention.
  Qed.

  (* ================================================ *)
  (*  ANTIPODE STRUCTURE OF ≡ AND ≈                    *)
  (*                                                   *)
  (*  The two outer relations of the trichotomy make   *)
  (*  exactly opposite statements about every          *)
  (*  viewpoint:                                       *)
  (*                                                   *)
  (*    ≡ is preserved by every interaction.           *)
  (*    ≈ is destroyed by every interaction.           *)
  (*                                                   *)
  (*  Both quantify universally over c, but one gives  *)
  (*  = at every c, and the other ≠ at every c.        *)
  (*  = (paper_projection) sits in the middle,         *)
  (*  asserting agreement at at least one c.           *)
  (* ================================================ *)

  Theorem paper_equiv_congruent_under_interact :
    forall a b c,
      paper_equiv a b -> interact a c = interact b c.
  Proof.
    intros a b c Heq.
    unfold paper_equiv in Heq. subst b.
    reflexivity.
  Qed.

  Theorem paper_convention_separates_everywhere :
    forall a b c,
      paper_convention a b -> interact a c <> interact b c.
  Proof.
    intros a b c Hconv.
    unfold paper_convention in Hconv.
    exact (interaction_cannot_witness_collapse a b Hconv c).
  Qed.

  (* Reflexive / irreflexive witnesses — ≡ holds at
     the diagonal, ≈ is forbidden there. *)

  Theorem paper_equiv_reflexive :
    forall a, paper_equiv a a.
  Proof.
    intro a. unfold paper_equiv. reflexivity.
  Qed.

  Theorem paper_convention_irreflexive :
    forall a, ~ paper_convention a a.
  Proof.
    intros a Hconv.
    apply (paper_convention_separates_everywhere a a a Hconv).
    reflexivity.
  Qed.

End Make.
