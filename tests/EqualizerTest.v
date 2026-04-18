(* ========================================== *)
(*  EqualizerTest                               *)
(*                                              *)
(*  A concrete equalizer of two morphisms       *)
(*  F, G : LatticeComputable -> LatticeComputable*)
(*                                              *)
(*    F = id                                    *)
(*    G = const_pair_2_4                        *)
(*                                              *)
(*  The equalizing predicate reads:             *)
(*    on_equalizer a  iff  a = pair_2_4         *)
(*  i.e., the subspace of D1 where F and G      *)
(*  agree is exactly the singleton {pair_2_4}.  *)
(*                                              *)
(*  Dual observation: PullbackTest carves out   *)
(*  the same slice in D1 x D2 (pairs whose      *)
(*  first coord is pair_2_4). Equalizer is the  *)
(*  D1-projection of that subspace — the same   *)
(*  witness from a different categorical        *)
(*  angle.                                      *)
(*                                              *)
(*  The general interact_preserves_equalizer    *)
(*  theorem guarantees the slice is             *)
(*  interact-closed; verified concretely below. *)
(* ========================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistencePullback.
Require Import ExistenceEqualizer.
Require Import LatticeModel.


(* ================================================ *)
(*  IDENTITY ON LATTICE                              *)
(* ================================================ *)

Module LatId := ExistencePullback.IdentityInto LatticeComputable.


(* ================================================ *)
(*  CONSTANT MORPHISM TO pair_2_4                    *)
(* ================================================ *)

Module ConstPair24 <: MorphismInto LatticeComputable LatticeComputable.

  Definition phi
    : LatticeComputable.Entity -> LatticeComputable.Entity :=
    fun _ => pair_2_4.

  Theorem preserves_interact :
    forall a b : LatticeComputable.Entity,
      phi (LatticeComputable.interact a b) =
      LatticeComputable.interact (phi a) (phi b).
  Proof.
    intros a b. unfold phi.
    rewrite LatticeComputable.interact_self.
    reflexivity.
  Qed.

End ConstPair24.


(* ================================================ *)
(*  EQUALIZER                                        *)
(*                                                   *)
(*    D1 = D2 = LatticeComputable                    *)
(*    F  = id, G = const_pair_2_4                    *)
(* ================================================ *)

Module LatEq :=
  ExistenceEqualizer.Equalizer
    LatticeComputable LatticeComputable
    LatId ConstPair24.


(* ================================================ *)
(*  CONCRETE EQUALIZER MEMBERSHIP                    *)
(* ================================================ *)

(* pair_2_4 is on the equalizer: id(pair_2_4) = pair_2_4 = const(pair_2_4). *)

Theorem equalizer_pair24 : LatEq.on_equalizer pair_2_4.
Proof.
  unfold LatEq.on_equalizer, LatId.phi, ConstPair24.phi.
  reflexivity.
Qed.

(* pair_4_2 is NOT on the equalizer: id(pair_4_2) = pair_4_2 ≠ pair_2_4. *)

Theorem not_equalizer_pair42 : ~ LatEq.on_equalizer pair_4_2.
Proof.
  unfold LatEq.on_equalizer, LatId.phi, ConstPair24.phi.
  intros Heq. apply pair_2_4_distinct_from_pair_4_2.
  symmetry. exact Heq.
Qed.


(* ================================================ *)
(*  STABILITY UNDER INTERACT                         *)
(*                                                   *)
(*  Two equalizer points interact to an equalizer    *)
(*  point — derived from the generic theorem and     *)
(*  instantiated at pair_2_4.                        *)
(* ================================================ *)

Theorem equalizer_preserved_concrete :
  LatEq.on_equalizer
    (LatticeComputable.interact pair_2_4 pair_2_4).
Proof.
  apply LatEq.interact_preserves_equalizer.
  - exact equalizer_pair24.
  - exact equalizer_pair24.
Qed.

(* Direct corollary via self-interact. *)

Theorem equalizer_self_pair24 :
  LatEq.on_equalizer
    (LatticeComputable.interact pair_2_4 pair_2_4).
Proof.
  apply LatEq.self_on_equalizer. exact equalizer_pair24.
Qed.


(* ================================================ *)
(*  UNIVERSAL PROPERTY — CONCRETE CONE               *)
(*                                                   *)
(*  Instantiate the universal property with a third  *)
(*  instance X = LatticeComputable and cone           *)
(*  h = const_pair_2_4. Then F ∘ h and G ∘ h both   *)
(*  point at pair_2_4, and h is guaranteed to land   *)
(*  inside the equalizer.                            *)
(* ================================================ *)

Module LatEqU :=
  ExistenceEqualizer.EqualizerUniversal
    LatticeComputable LatticeComputable LatticeComputable
    LatId ConstPair24.

(* The cone: h sends every entity to pair_2_4. *)

Definition h : LatticeComputable.Entity -> LatticeComputable.Entity :=
  ConstPair24.phi.

Theorem h_preserves_interact :
  forall a b,
    h (LatticeComputable.interact a b) =
    LatticeComputable.interact (h a) (h b).
Proof. exact ConstPair24.preserves_interact. Qed.

Theorem h_makes_F_G_agree :
  forall x, LatId.phi (h x) = ConstPair24.phi (h x).
Proof.
  intros x. unfold LatId.phi, ConstPair24.phi. reflexivity.
Qed.

Theorem h_lands_on_equalizer :
  forall x, LatEqU.Eq.on_equalizer (h x).
Proof.
  apply LatEqU.equalizer_universal_existence.
  - exact h_preserves_interact.
  - exact h_makes_F_G_agree.
Qed.


(* ================================================ *)
(*  OBSERVATIONAL EQUALIZER                          *)
(*                                                   *)
(*  Strict equalizer ⊆ observational equalizer.      *)
(*  The strict witness pair_2_4 is observational     *)
(*  too.                                             *)
(* ================================================ *)

Module LatEqObs :=
  ExistenceEqualizer.ObservationalEqualizer
    LatticeComputable LatticeComputable
    LatId ConstPair24.

Theorem pair24_observational :
  LatEqObs.on_equalizer_observational pair_2_4.
Proof.
  apply LatEqObs.on_equalizer_is_observational.
  exact equalizer_pair24.
Qed.
