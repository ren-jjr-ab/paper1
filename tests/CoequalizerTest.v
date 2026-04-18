(* ========================================== *)
(*  CoequalizerTest                             *)
(*                                              *)
(*  Apply ExistenceCoequalizer.Universal to a   *)
(*  concrete parallel pair and instantiate its  *)
(*  universal property.                         *)
(*                                              *)
(*  Pair chosen (dual of EqualizerTest):        *)
(*    D1 = D2 = LatticeComputable               *)
(*    F = id, G = const_pair_2_4                *)
(*                                              *)
(*  Coequalizing forces F(a) = G(a) in the      *)
(*  target, i.e., a ~ pair_2_4 for every a.     *)
(*  By transitivity the entire LatticeComputable*)
(*  collapses into a single equivalence class.  *)
(*  This is Coequalizer at its most aggressive  *)
(*  — the whole target becomes a singleton      *)
(*  when the parallel pair forces every source  *)
(*  point to a single anchor.                   *)
(*                                              *)
(*  Universal instantiation:                    *)
(*    D3 = LatticeComputable                    *)
(*    R  = const_pair_2_4                       *)
(*  The coequalizing condition reads            *)
(*    R(id a) = R(const a)                      *)
(*     pair_2_4 = pair_2_4                      *)
(*  and is trivially discharged. The resulting  *)
(*  r_star sends every coequalizer class back   *)
(*  to pair_2_4 in LatticeComputable.           *)
(* ========================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistencePullback.
Require Import ExistencePushout.
Require Import ExistenceCoequalizer.
Require Import LatticeModel.


(* ================================================ *)
(*  IDENTITY AND CONST MORPHISMS ON LATTICE          *)
(* ================================================ *)

Module LatId := ExistencePullback.IdentityInto LatticeComputable.

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
    rewrite LatticeComputable.interact_self. reflexivity.
  Qed.

End ConstPair24.


(* ================================================ *)
(*  COEQUALIZER + UNIVERSAL                          *)
(*                                                   *)
(*  Universal internally builds its own              *)
(*  Construction (as LatCoeq.C). We use that         *)
(*  instance throughout so the Construction and      *)
(*  Factor operations share namespace.               *)
(* ================================================ *)

Module LatCoeq :=
  ExistenceCoequalizer.Universal
    LatticeComputable LatticeComputable LatId ConstPair24
    LatticeComputable ConstPair24.


(* ================================================ *)
(*  COLLAPSE OBSERVATIONS                            *)
(*                                                   *)
(*  For any a, e_identify supplies equiv a pair_2_4  *)
(*  (since F = id, G = const pair_2_4). By           *)
(*  transitivity the quotient collapses to a         *)
(*  single class.                                    *)
(* ================================================ *)

(* Any entity lands in the class of pair_2_4. *)

Theorem cls_anything_eq_pair24 :
  forall a : LatticeComputable.Entity,
    LatCoeq.C.cls a = LatCoeq.C.cls pair_2_4.
Proof.
  intros a. apply LatCoeq.C.cls_correct.
  exact (LatCoeq.C.e_identify a).
Qed.

(* Specialised: pair_4_2 and pair_2_4 collapse, even
   though they are distinct in LatticeComputable. *)

Theorem cls_pair42_eq_cls_pair24 :
  LatCoeq.C.cls pair_4_2 = LatCoeq.C.cls pair_2_4.
Proof. exact (cls_anything_eq_pair24 pair_4_2). Qed.

(* Full collapse: every two entities are equal in the
   coequalizer. *)

Theorem coequalizer_is_singleton :
  forall a b : LatticeComputable.Entity,
    LatCoeq.C.cls a = LatCoeq.C.cls b.
Proof.
  intros a b.
  rewrite (cls_anything_eq_pair24 a).
  rewrite (cls_anything_eq_pair24 b).
  reflexivity.
Qed.


(* ================================================ *)
(*  QUOTIENT MAP PROPERTIES                          *)
(* ================================================ *)

Theorem q_preserves_interact_concrete :
  forall a b : LatticeComputable.Entity,
    LatCoeq.C.q (LatticeComputable.interact a b) =
    LatCoeq.C.interact (LatCoeq.C.q a) (LatCoeq.C.q b).
Proof. exact LatCoeq.C.q_preserves_interact. Qed.

Theorem q_coequalizes_concrete :
  forall a : LatticeComputable.Entity,
    LatCoeq.C.q (LatId.phi a) = LatCoeq.C.q (ConstPair24.phi a).
Proof. exact LatCoeq.C.q_coequalizes. Qed.


(* ================================================ *)
(*  UNIVERSAL PROPERTY — concrete factoring          *)
(*                                                   *)
(*  R = const_pair_2_4 coequalizes F and G           *)
(*  trivially (both sides collapse to pair_2_4).     *)
(* ================================================ *)

Module LatCoeqR <: LatCoeq.CoequalizingRmorphism.
  Theorem r_coequalizes :
    forall a : LatticeComputable.Entity,
      ConstPair24.phi (LatId.phi a) =
      ConstPair24.phi (ConstPair24.phi a).
  Proof.
    intros a. unfold ConstPair24.phi, LatId.phi. reflexivity.
  Qed.
End LatCoeqR.

Module LatFactor := LatCoeq.Factor LatCoeqR.

(* r_star agrees with R on every class representative. *)

Theorem r_star_factors_concrete :
  forall a : LatticeComputable.Entity,
    LatFactor.r_star (LatCoeq.C.q a) = ConstPair24.phi a.
Proof. exact LatFactor.r_star_factors. Qed.

(* r_star preserves interact. *)

Theorem r_star_preserves_interact_concrete :
  forall a b : LatCoeq.C.Entity,
    LatFactor.r_star (LatCoeq.C.interact a b) =
    LatticeComputable.interact
      (LatFactor.r_star a) (LatFactor.r_star b).
Proof. exact LatFactor.r_star_preserves_interact. Qed.

(* Uniqueness of r_star: any morphism r' that factors
   like r_star and preserves interact agrees with it. *)

Theorem r_star_unique_concrete :
  forall r' : LatCoeq.C.Entity -> LatticeComputable.Entity,
    (forall a b,
      r' (LatCoeq.C.interact a b) =
      LatticeComputable.interact (r' a) (r' b)) ->
    (forall a, r' (LatCoeq.C.q a) = ConstPair24.phi a) ->
    forall e, r' e = LatFactor.r_star e.
Proof. exact LatFactor.r_star_unique. Qed.


(* ================================================ *)
(*  CONCRETE CORNER: r_star everywhere equals        *)
(*  pair_2_4                                         *)
(*                                                   *)
(*  Because R = const_pair_2_4 and r_star factors    *)
(*  through q, every coequalizer element maps to     *)
(*  pair_2_4.                                        *)
(* ================================================ *)

Theorem r_star_constantly_pair24 :
  forall e : LatCoeq.C.Entity, LatFactor.r_star e = pair_2_4.
Proof.
  intros e.
  destruct (LatCoeq.C.cls_surjective e) as [w Hw].
  subst e.
  rewrite r_star_factors_concrete.
  unfold ConstPair24.phi. reflexivity.
Qed.
