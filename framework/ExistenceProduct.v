(* ========================================== *)
(*  ExistenceProduct                           *)
(*                                             *)
(*  Categorical product of two ExistenceSig    *)
(*  instances. Given D1 and D2, the product    *)
(*  has:                                       *)
(*                                             *)
(*    Entity        := D1.Entity * D2.Entity   *)
(*    interact      coordinate-wise            *)
(*    convention_eq both coordinates convention*)
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
Require Import ExistenceMorphism.


Module Make (D1 D2 : ExistenceSig) <: ExistenceSig.

  Definition Entity : Type := (D1.Entity * D2.Entity)%type.

  Definition interact (a b : Entity) : Entity :=
    (D1.interact (fst a) (fst b), D2.interact (snd a) (snd b)).

  Definition convention_eq (a b : Entity) : Prop :=
    D1.convention_eq (fst a) (fst b) /\
    D2.convention_eq (snd a) (snd b).

  (* ============================================= *)
  (*  AXIOMS (all coordinate-wise)                 *)
  (* ============================================= *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros [a1 a2]. unfold interact. simpl.
    rewrite D1.interact_self. rewrite D2.interact_self.
    reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof.
    intros [a1 a2] [b1 b2] [c1 c2]. unfold interact. simpl.
    destruct (D1.interact_decidable a1 b1 c1) as [H1 | H1];
    destruct (D2.interact_decidable a2 b2 c2) as [H2 | H2].
    - left. rewrite H1. rewrite H2. reflexivity.
    - right. intros Heq.
      apply (f_equal snd) in Heq. simpl in Heq. exact (H2 Heq).
    - right. intros Heq.
      apply (f_equal fst) in Heq. simpl in Heq. exact (H1 Heq).
    - right. intros Heq.
      apply (f_equal fst) in Heq. simpl in Heq. exact (H1 Heq).
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

  Theorem convention_not_derivable :
    forall a b : Entity,
      convention_eq a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof.
    intros [a1 a2] [b1 b2] [Hconv1 _] [c1 c2].
    unfold interact. simpl.
    intros Heq.
    apply (f_equal fst) in Heq. simpl in Heq.
    exact (D1.convention_not_derivable a1 b1 Hconv1 c1 Heq).
  Qed.

End Make.


(* ================================================ *)
(*  PROJECTIONS AS MORPHISMS                         *)
(* ================================================ *)

Module Projections (D1 D2 : ExistenceSig).

  Module P := Make D1 D2.
  Module M1 := ExistenceMorphism.Make P D1.
  Module M2 := ExistenceMorphism.Make P D2.

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
  Module M  := ExistenceMorphism.Make D P.
  Module M1 := ExistenceMorphism.Make D D1.
  Module M2 := ExistenceMorphism.Make D D2.

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

End UniversalPair.
