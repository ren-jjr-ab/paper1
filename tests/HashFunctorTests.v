(* ========================================== *)
(*  HashTestSuite                               *)
(*                                              *)
(*  Apply the framework's Equalizer,            *)
(*  Coequalizer, and Factorization constructions*)
(*  to the FxHash-style instance HashComputable.*)
(*                                              *)
(*  HashComputable tracks storage_cost and      *)
(*  flip_cost, which makes preserves_interact   *)
(*  very restrictive — the natural non-trivial  *)
(*  collapses in this instance (e.g. stage-1   *)
(*  hash collisions like fx_stage1_collapses)   *)
(*  are interact_eq_at statements, not          *)
(*  kernel-equalities of a framework morphism. *)
(*  This suite therefore demonstrates the       *)
(*  framework mechanics at both extremes —      *)
(*  universal collapse via const, trivial       *)
(*  factor via id — mirroring the Lattice       *)
(*  bracket.                                    *)
(*                                              *)
(*  Sections:                                   *)
(*    1. Morphisms (id, const fx_raw_a)         *)
(*    2. Equalizer tests                        *)
(*    3. Coequalizer tests                      *)
(*    4. Factorization tests                    *)
(* ========================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistencePullback.
Require Import ExistencePushout.
Require Import ExistenceEqualizer.
Require Import ExistenceCoequalizer.
Require Import ExistenceFactorization.
Require Import HashModel.


(* ================================================ *)
(*  1. MORPHISMS                                     *)
(* ================================================ *)

Module HashId := ExistencePullback.IdentityInto HashComputable.

Module ConstFxRawA <: MorphismInto HashComputable HashComputable.

  Definition phi
    : HashComputable.Entity -> HashComputable.Entity :=
    fun _ => fx_raw_a.

  Theorem preserves_interact :
    forall a b : HashComputable.Entity,
      phi (HashComputable.interact a b) =
      HashComputable.interact (phi a) (phi b).
  Proof.
    intros a b. unfold phi.
    rewrite HashComputable.interact_self. reflexivity.
  Qed.

End ConstFxRawA.


(* ================================================ *)
(*  2. EQUALIZER                                     *)
(*                                                   *)
(*  F = id, G = const fx_raw_a.                      *)
(*  on_equalizer(a) ⟺ a = fx_raw_a.                 *)
(* ================================================ *)

Module HashEq :=
  ExistenceEqualizer.Equalizer
    HashComputable HashComputable HashId ConstFxRawA.

Theorem equalizer_fx_raw_a : HashEq.on_equalizer fx_raw_a.
Proof.
  unfold HashEq.on_equalizer, HashId.phi, ConstFxRawA.phi.
  reflexivity.
Qed.

Theorem not_equalizer_fx_raw_b : ~ HashEq.on_equalizer fx_raw_b.
Proof.
  unfold HashEq.on_equalizer, HashId.phi, ConstFxRawA.phi.
  intros Heq. apply fx_raw_distinct. symmetry. exact Heq.
Qed.

Theorem equalizer_preserved_fx_raw_a :
  HashEq.on_equalizer
    (HashComputable.interact fx_raw_a fx_raw_a).
Proof.
  apply HashEq.interact_preserves_equalizer;
    exact equalizer_fx_raw_a.
Qed.

(* Universal property — cone h = const fx_raw_a. *)

Module HashEqU :=
  ExistenceEqualizer.EqualizerUniversal
    HashComputable HashComputable HashComputable
    HashId ConstFxRawA.

Definition eq_cone : HashComputable.Entity -> HashComputable.Entity :=
  ConstFxRawA.phi.

Theorem eq_cone_preserves_interact :
  forall a b,
    eq_cone (HashComputable.interact a b) =
    HashComputable.interact (eq_cone a) (eq_cone b).
Proof. exact ConstFxRawA.preserves_interact. Qed.

Theorem eq_cone_makes_F_G_agree :
  forall x, HashId.phi (eq_cone x) = ConstFxRawA.phi (eq_cone x).
Proof.
  intros x. unfold HashId.phi, ConstFxRawA.phi. reflexivity.
Qed.

Theorem eq_cone_lands_on_equalizer :
  forall x, HashEqU.Eq.on_equalizer (eq_cone x).
Proof.
  apply HashEqU.equalizer_universal_existence.
  - exact eq_cone_preserves_interact.
  - exact eq_cone_makes_F_G_agree.
Qed.

(* Observational equalizer. *)

Module HashEqObs :=
  ExistenceEqualizer.ObservationalEqualizer
    HashComputable HashComputable HashId ConstFxRawA.

Theorem fx_raw_a_observational :
  HashEqObs.on_equalizer_observational fx_raw_a.
Proof.
  apply HashEqObs.on_equalizer_is_observational.
  exact equalizer_fx_raw_a.
Qed.


(* ================================================ *)
(*  3. COEQUALIZER                                   *)
(*                                                   *)
(*  Same F, G. Coequalizer forces every a ~          *)
(*  fx_raw_a, collapsing HashComputable to a         *)
(*  singleton.                                       *)
(* ================================================ *)

Module HashCoeq :=
  ExistenceCoequalizer.Universal
    HashComputable HashComputable HashId ConstFxRawA
    HashComputable ConstFxRawA.

Theorem hash_cls_anything_eq_fx_raw_a :
  forall a : HashComputable.Entity,
    HashCoeq.C.cls a = HashCoeq.C.cls fx_raw_a.
Proof.
  intros a. apply HashCoeq.C.cls_correct.
  exact (HashCoeq.C.e_identify a).
Qed.

Theorem hash_coequalizer_is_singleton :
  forall a b : HashComputable.Entity,
    HashCoeq.C.cls a = HashCoeq.C.cls b.
Proof.
  intros a b.
  rewrite (hash_cls_anything_eq_fx_raw_a a).
  rewrite (hash_cls_anything_eq_fx_raw_a b).
  reflexivity.
Qed.

(* Note: this is stronger than the stage-1 hash
   collision (fx_stage1_collapses) — Coequalizer
   collapses every pair, not just equal-size raws. *)

Theorem hash_cls_raw_a_eq_raw_b :
  HashCoeq.C.cls fx_raw_a = HashCoeq.C.cls fx_raw_b.
Proof. apply hash_coequalizer_is_singleton. Qed.

Theorem hash_q_preserves_interact :
  forall a b : HashComputable.Entity,
    HashCoeq.C.q (HashComputable.interact a b) =
    HashCoeq.C.interact (HashCoeq.C.q a) (HashCoeq.C.q b).
Proof. exact HashCoeq.C.q_preserves_interact. Qed.

Theorem hash_q_coequalizes :
  forall a : HashComputable.Entity,
    HashCoeq.C.q (HashId.phi a) = HashCoeq.C.q (ConstFxRawA.phi a).
Proof. exact HashCoeq.C.q_coequalizes. Qed.

(* Universal factoring: R = const_fx_raw_a coequalizes F, G
   trivially. r_star sends every class to fx_raw_a. *)

Module HashCoeqR <: HashCoeq.CoequalizingRmorphism.
  Theorem r_coequalizes :
    forall a : HashComputable.Entity,
      ConstFxRawA.phi (HashId.phi a) =
      ConstFxRawA.phi (ConstFxRawA.phi a).
  Proof.
    intros a. unfold ConstFxRawA.phi, HashId.phi. reflexivity.
  Qed.
End HashCoeqR.

Module HashFactor := HashCoeq.Factor HashCoeqR.

Theorem hash_r_star_factors :
  forall a : HashComputable.Entity,
    HashFactor.r_star (HashCoeq.C.q a) = ConstFxRawA.phi a.
Proof. exact HashFactor.r_star_factors. Qed.

Theorem hash_r_star_constantly_fx_raw_a :
  forall e : HashCoeq.C.Entity,
    HashFactor.r_star e = fx_raw_a.
Proof.
  intros e.
  destruct (HashCoeq.C.cls_surjective e) as [w Hw].
  subst e.
  rewrite hash_r_star_factors.
  unfold ConstFxRawA.phi. reflexivity.
Qed.


(* ================================================ *)
(*  4. FACTORIZATION                                 *)
(*                                                   *)
(*  ConstFact (phi = const fx_raw_a): universal      *)
(*  kernel. IdFact (phi = id): trivial kernel + iso. *)
(* ================================================ *)

Module HashConstFact :=
  ExistenceFactorization.Factorization
    HashComputable HashComputable ConstFxRawA.

Theorem hash_const_ker_universal :
  forall a b : HashComputable.Entity, HashConstFact.ker a b.
Proof. intros a b. unfold HashConstFact.ker. reflexivity. Qed.

Theorem hash_const_cls_collapses :
  forall a b : HashComputable.Entity,
    HashConstFact.cls a = HashConstFact.cls b.
Proof.
  intros a b. apply HashConstFact.cls_correct.
  apply hash_const_ker_universal.
Qed.

Theorem hash_const_phi_hat_constant :
  forall x : HashConstFact.Entity,
    HashConstFact.phi_hat x = fx_raw_a.
Proof.
  intros x.
  destruct (HashConstFact.cls_surjective x) as [a Ha].
  subst x. rewrite HashConstFact.phi_hat_spec.
  unfold ConstFxRawA.phi. reflexivity.
Qed.

Theorem hash_const_cls_raw_a_eq_raw_b :
  HashConstFact.cls fx_raw_a = HashConstFact.cls fx_raw_b.
Proof. apply hash_const_cls_collapses. Qed.


Module HashIdFact :=
  ExistenceFactorization.Factorization
    HashComputable HashComputable HashId.

Theorem hash_id_ker_is_equality :
  forall a b : HashComputable.Entity,
    HashIdFact.ker a b <-> a = b.
Proof.
  intros a b. unfold HashIdFact.ker, HashId.phi.
  split; intros H; exact H.
Qed.

Theorem hash_id_cls_injective :
  forall a b : HashComputable.Entity,
    HashIdFact.cls a = HashIdFact.cls b -> a = b.
Proof.
  apply HashIdFact.injective_phi_makes_cls_injective.
  intros a b H. unfold HashId.phi in H. exact H.
Qed.

Theorem hash_id_phi_surjective :
  forall b : HashComputable.Entity,
    exists a : HashComputable.Entity, HashId.phi a = b.
Proof. intros b. exists b. unfold HashId.phi. reflexivity. Qed.

Theorem hash_id_phi_hat_is_iso :
  (forall x y,
    HashIdFact.phi_hat (HashIdFact.interact x y) =
    HashComputable.interact (HashIdFact.phi_hat x) (HashIdFact.phi_hat y)) /\
  (forall b, exists x, HashIdFact.phi_hat x = b) /\
  (forall x y, HashIdFact.phi_hat x = HashIdFact.phi_hat y -> x = y).
Proof.
  apply HashIdFact.phi_hat_is_iso_if_phi_surjective.
  exact hash_id_phi_surjective.
Qed.

(* Distinct raws stay distinct in the identity quotient
   — the opposite of the ConstFact case. *)

Theorem hash_id_cls_raw_a_ne_raw_b :
  HashIdFact.cls fx_raw_a <> HashIdFact.cls fx_raw_b.
Proof.
  intros Heq. apply fx_raw_distinct.
  apply hash_id_cls_injective. exact Heq.
Qed.
