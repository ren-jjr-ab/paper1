(* ========================================== *)
(*  ExistenceProduct                           *)
(*                                             *)
(*  Categorical product of two ExistenceSig    *)
(*  instances. Given D1 and D2, the product    *)
(*  has:                                       *)
(*                                             *)
(*    Entity        := D1.Entity * D2.Entity   *)
(*    interact      coordinate-wise            *)
(*    collapse both coordinates convention*)
(*                                             *)
(*  Each of the five ExistenceSig axioms       *)
(*  discharges from the corresponding D1 / D2  *)
(*  axioms, coordinate-wise.                   *)
(*                                             *)
(*  The projections pi1 and pi2 are morphisms  *)
(*  that carry the product back to each        *)
(*  factor. Combined with the pairing of two   *)
(*  morphisms from any other instance, this    *)
(*  is the usual universal property of the     *)
(*  categorical product.                       *)
(*                                             *)
(*  Purpose: supply a "common substrate" for   *)
(*  two axiom systems to sit inside jointly.   *)
(*  Further constructions (pullback, etc.) use *)
(*  this as the basic joint instance.          *)
(* ========================================== *)

Require Import Existence.
Require Import Morphism.


Module Make (D1 D2 : ExistenceSig) <: ExistenceSig.

  Definition Entity : Type := (D1.Entity * D2.Entity)%type.

  Definition interact (a b : Entity) : Entity :=
    (D1.interact (fst a) (fst b), D2.interact (snd a) (snd b)).

  Definition collapse (a b : Entity) : Prop :=
    D1.collapse (fst a) (fst b) /\
    D2.collapse (snd a) (snd b).

  (* ============================================= *)
  (*  AXIOMS (all coordinate-wise)                 *)
  (* ============================================= *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros [a1 a2]. unfold interact. simpl.
    rewrite D1.interact_self. rewrite D2.interact_self.
    reflexivity.
  Qed.

  Theorem entity_eq_dec :
    forall a b : Entity, {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].
    destruct (D1.entity_eq_dec a1 b1) as [H1 | H1];
    destruct (D2.entity_eq_dec a2 b2) as [H2 | H2].
    - left. subst. reflexivity.
    - right. intros Heq. apply (f_equal snd) in Heq. simpl in Heq. exact (H2 Heq).
    - right. intros Heq. apply (f_equal fst) in Heq. simpl in Heq. exact (H1 Heq).
    - right. intros Heq. apply (f_equal fst) in Heq. simpl in Heq. exact (H1 Heq).
  Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    destruct D1.existence as [a1 [b1 Hne]].
    destruct D2.existence as [a2 _].
    exists (a1, a2), (b1, a2).
    intros Heq.
    apply (f_equal fst) in Heq. simpl in Heq. exact (Hne Heq).
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b : Entity, interact a b <> a.
  Proof.
    intros [a1 a2].
    destruct (D1.interact_with a1) as [b1 Hne].
    exists (b1, a2). unfold interact. simpl.
    intros Heq.
    apply (f_equal fst) in Heq. simpl in Heq. exact (Hne Heq).
  Qed.

  Theorem interaction_cannot_witness_collapse :
    forall a b : Entity, collapse a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof.
    intros [a1 a2] [b1 b2] [Hconv1 _] [c1 c2].
    unfold interact.
    intros Heq.
    apply (f_equal fst) in Heq. simpl in Heq.
    exact (D1.interaction_cannot_witness_collapse a1 b1 Hconv1 c1 Heq).
  Qed.

End Make.


(* ================================================ *)
(*  PROJECTIONS AS MORPHISMS                         *)
(* ================================================ *)

Module Projections (D1 D2 : ExistenceSig).

  Module P := Make D1 D2.
  Module M1 := Morphism.Make P D1.
  Module M2 := Morphism.Make P D2.

  Definition pi1 : P.Entity -> D1.Entity := fun p => fst p.
  Definition pi2 : P.Entity -> D2.Entity := fun p => snd p.

  Theorem pi1_preserves_interact : M1.preserves_interact pi1.
  Proof.
    intros [a1 a2] [b1 b2]. unfold pi1, P.interact. simpl. reflexivity.
  Qed.

  Theorem pi2_preserves_interact : M2.preserves_interact pi2.
  Proof.
    intros [a1 a2] [b1 b2]. unfold pi2, P.interact. simpl. reflexivity.
  Qed.

  (* Convention preservation for projections: product's
     collapse is a conjunction, so each projection
     extracts one conjunct automatically. *)

  Theorem pi1_preserves_convention : M1.preserves_convention pi1.
  Proof.
    intros [a1 a2] [b1 b2] [Hconv _]. unfold pi1. simpl. exact Hconv.
  Qed.

  Theorem pi2_preserves_convention : M2.preserves_convention pi2.
  Proof.
    intros [a1 a2] [b1 b2] [_ Hconv]. unfold pi2. simpl. exact Hconv.
  Qed.

  Theorem pi1_full_morphism : M1.full_morphism pi1.
  Proof.
    split;
      [apply pi1_preserves_interact | apply pi1_preserves_convention].
  Qed.

  Theorem pi2_full_morphism : M2.full_morphism pi2.
  Proof.
    split;
      [apply pi2_preserves_interact | apply pi2_preserves_convention].
  Qed.

End Projections.


(* ================================================ *)
(*  UNIVERSAL PAIRING                                *)
(*                                                   *)
(*  If D has morphisms phi1 : D -> D1 and            *)
(*  phi2 : D -> D2, then the pair function           *)
(*     x |-> (phi1 x, phi2 x)                        *)
(*  is a morphism D -> (D1 x D2).                    *)
(*                                                   *)
(*  This is the universal property of the product —  *)
(*  any pair of out-maps factors through the product *)
(*  uniquely.                                        *)
(* ================================================ *)

Module UniversalPair (D D1 D2 : ExistenceSig).

  Module P := Make D1 D2.
  Module M  := Morphism.Make D P.
  Module M1 := Morphism.Make D D1.
  Module M2 := Morphism.Make D D2.

  Definition pi1 : P.Entity -> D1.Entity := fun p => fst p.
  Definition pi2 : P.Entity -> D2.Entity := fun p => snd p.

  Definition pair_morphism
    (phi1 : D.Entity -> D1.Entity)
    (phi2 : D.Entity -> D2.Entity)
    (x : D.Entity) : P.Entity :=
    (phi1 x, phi2 x).

  Theorem pair_preserves_interact :
    forall phi1 phi2,
      M1.preserves_interact phi1 ->
      M2.preserves_interact phi2 ->
      M.preserves_interact (pair_morphism phi1 phi2).
  Proof.
    intros phi1 phi2 Hphi1 Hphi2 a b.
    unfold pair_morphism, P.interact. simpl.
    rewrite Hphi1. rewrite Hphi2. reflexivity.
  Qed.

  (* Convention preservation lifts coordinate-wise. Both
     components must preserve convention for the pair to. *)

  Theorem pair_preserves_convention :
    forall phi1 phi2,
      M1.preserves_convention phi1 ->
      M2.preserves_convention phi2 ->
      M.preserves_convention (pair_morphism phi1 phi2).
  Proof.
    intros phi1 phi2 Hphi1 Hphi2 a b Hconv.
    unfold pair_morphism, P.collapse. simpl.
    split.
    - apply Hphi1. exact Hconv.
    - apply Hphi2. exact Hconv.
  Qed.

  (* Full morphism version of universal pairing. *)

  Theorem pair_full_morphism :
    forall phi1 phi2,
      M1.full_morphism phi1 ->
      M2.full_morphism phi2 ->
      M.full_morphism (pair_morphism phi1 phi2).
  Proof.
    intros phi1 phi2 [Hi1 Hc1] [Hi2 Hc2].
    split.
    - apply pair_preserves_interact; assumption.
    - apply pair_preserves_convention; assumption.
  Qed.


  (* ============================================= *)
  (*  UNIVERSAL PROPERTY — FACTORING + UNIQUENESS  *)
  (*                                               *)
  (*  Classical statement of the categorical       *)
  (*  product's universal property, split into     *)
  (*  existence (pair_morphism factors) and        *)
  (*  uniqueness (any other factoring agrees       *)
  (*  pointwise with pair_morphism).               *)
  (* ============================================= *)

  (* Factoring: pair_morphism satisfies the projection
     equations by construction. *)

  Theorem pair_factors_pi1 :
    forall phi1 phi2 x,
      pi1 (pair_morphism phi1 phi2 x) = phi1 x.
  Proof. intros. reflexivity. Qed.

  Theorem pair_factors_pi2 :
    forall phi1 phi2 x,
      pi2 (pair_morphism phi1 phi2 x) = phi2 x.
  Proof. intros. reflexivity. Qed.

  (* Existence: a factoring morphism exists. *)

  Theorem product_universal_existence :
    forall phi1 phi2,
      M1.preserves_interact phi1 ->
      M2.preserves_interact phi2 ->
      exists h : D.Entity -> P.Entity,
        M.preserves_interact h /\
        (forall x, pi1 (h x) = phi1 x) /\
        (forall x, pi2 (h x) = phi2 x).
  Proof.
    intros phi1 phi2 Hphi1 Hphi2.
    exists (pair_morphism phi1 phi2).
    split; [apply pair_preserves_interact; assumption |].
    split; intro x; reflexivity.
  Qed.

  (* Uniqueness: any two factorings agree pointwise.
     Stated without function extensionality. *)

  Theorem product_universal_uniqueness :
    forall phi1 phi2 (h h' : D.Entity -> P.Entity),
      (forall x, pi1 (h x) = phi1 x) ->
      (forall x, pi2 (h x) = phi2 x) ->
      (forall x, pi1 (h' x) = phi1 x) ->
      (forall x, pi2 (h' x) = phi2 x) ->
      forall x, h x = h' x.
  Proof.
    intros phi1 phi2 h h' H1 H2 H1' H2' x.
    destruct (h x) as [h1 h2] eqn:Eh.
    destruct (h' x) as [h1' h2'] eqn:Eh'.
    specialize (H1 x). unfold pi1 in H1. rewrite Eh in H1.
    specialize (H2 x). unfold pi2 in H2. rewrite Eh in H2.
    specialize (H1' x). unfold pi1 in H1'. rewrite Eh' in H1'.
    specialize (H2' x). unfold pi2 in H2'. rewrite Eh' in H2'.
    simpl in *. subst. reflexivity.
  Qed.

  (* Combined: existence + uniqueness in one statement.
     The factoring morphism is unique up to pointwise
     agreement. *)

  Theorem product_universal :
    forall phi1 phi2,
      M1.preserves_interact phi1 ->
      M2.preserves_interact phi2 ->
      exists h : D.Entity -> P.Entity,
        M.preserves_interact h /\
        (forall x, pi1 (h x) = phi1 x) /\
        (forall x, pi2 (h x) = phi2 x) /\
        (forall h' : D.Entity -> P.Entity,
          (forall x, pi1 (h' x) = phi1 x) ->
          (forall x, pi2 (h' x) = phi2 x) ->
          forall x, h x = h' x).
  Proof.
    intros phi1 phi2 Hphi1 Hphi2.
    exists (pair_morphism phi1 phi2).
    split; [apply pair_preserves_interact; assumption |].
    split; [intro x; reflexivity |].
    split; [intro x; reflexivity |].
    intros h' H1' H2' x.
    apply (product_universal_uniqueness phi1 phi2
             (pair_morphism phi1 phi2) h').
    - intro. apply pair_factors_pi1.
    - intro. apply pair_factors_pi2.
    - exact H1'.
    - exact H2'.
  Qed.

  (* ============================================= *)
  (*  OBSERVATIONAL UNIVERSAL PROPERTY             *)
  (*                                               *)
  (*  Observational morphism preservation is       *)
  (*  coordinate-wise: if each component is        *)
  (*  observational, so is the pair. The pair's    *)
  (*  observational agreement at any P-viewpoint   *)
  (*  splits into two viewpoint-equalities in D1   *)
  (*  and D2 respectively.                         *)
  (*                                               *)
  (*  This is the strengthening the framework      *)
  (*  allows: instead of requiring strict          *)
  (*  preserves_interact at each component, the    *)
  (*  pair morphism is already universal at the    *)
  (*  observational level.                         *)
  (* ============================================= *)

  Theorem pair_observational_morphism :
    forall phi1 phi2,
      M1.observational_morphism phi1 ->
      M2.observational_morphism phi2 ->
      M.observational_morphism (pair_morphism phi1 phi2).
  Proof.
    intros phi1 phi2 Hobs1 Hobs2 a b [c1 c2].
    unfold pair_morphism, P.interact. simpl.
    f_equal.
    - apply (Hobs1 a b c1).
    - apply (Hobs2 a b c2).
  Qed.

  Theorem product_observational_universal :
    forall phi1 phi2,
      M1.observational_morphism phi1 ->
      M2.observational_morphism phi2 ->
      exists h : D.Entity -> P.Entity,
        M.observational_morphism h /\
        (forall x, pi1 (h x) = phi1 x) /\
        (forall x, pi2 (h x) = phi2 x) /\
        (forall h' : D.Entity -> P.Entity,
          (forall x, pi1 (h' x) = phi1 x) ->
          (forall x, pi2 (h' x) = phi2 x) ->
          forall x, h x = h' x).
  Proof.
    intros phi1 phi2 Hphi1 Hphi2.
    exists (pair_morphism phi1 phi2).
    split; [apply pair_observational_morphism; assumption |].
    split; [intro x; reflexivity |].
    split; [intro x; reflexivity |].
    intros h' H1' H2' x.
    apply (product_universal_uniqueness phi1 phi2
             (pair_morphism phi1 phi2) h').
    - intro. apply pair_factors_pi1.
    - intro. apply pair_factors_pi2.
    - exact H1'.
    - exact H2'.
  Qed.

End UniversalPair.
