(* ============================================== *)
(*  RationalRepTest                                 *)
(*                                                  *)
(*  Verify that RationalRep is actually usable:     *)
(*                                                  *)
(*  1. ExistenceTheory applies — framework's        *)
(*     derived theorems (dichotomy, observational   *)
(*     equivalence, collapse_irreflexive,      *)
(*     etc.) become available for RationalRep.      *)
(*                                                  *)
(*  2. WitnessedTheory applies — time advance    *)
(*     theorems available.                          *)
(*                                                  *)
(*  3. The general rational_equivalent_paper_       *)
(*     projection theorem specializes to concrete   *)
(*     rational pairs (1/2 vs 2/4, 3/6 vs 1/2,      *)
(*     etc.) without further proof work — just      *)
(*     instantiation.                               *)
(* ============================================== *)

Require Import Existence.
Require Import Theory.
Require Import Witnessed.
Require Import RationalRep.
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.


(* =================================================== *)
(*  1. Framework theory functors apply.                *)
(* =================================================== *)

Module RR_Theory    := ExistenceTheory     RationalRep_is_Witnessed.
Module RR_ExtTime   := WitnessedTheory  RationalRep_is_Witnessed.

(* Check: derived theorems are accessible. *)

Check RR_Theory.is_terminal_impossible.
Check RR_Theory.viewpoint_has_fixed_point.
Check RR_Theory.collapse_irreflexive.
Check RR_Theory.observational_equivalence_excludes_collapse.
Check RR_ExtTime.exists_witness_time_advancing_partner.
Check RR_ExtTime.self_interact_preserves_witness_time.


(* =================================================== *)
(*  2. General theorem specializes.                    *)
(* =================================================== *)

Definition half_1_2 : RationalRep.Entity :=
  RationalRep.REnt (1 # 2) 0.

Definition half_2_4 : RationalRep.Entity :=
  RationalRep.REnt (2 # 4) 0.

Definition half_3_6 : RationalRep.Entity :=
  RationalRep.REnt (3 # 6) 0.

Lemma half_1_2_eq_2_4 : ((1 # 2) == (2 # 4))%Q.
Proof. reflexivity. Qed.

Lemma half_1_2_distinct_2_4 : (1 # 2 : Q) <> (2 # 4 : Q).
Proof. intro H. inversion H. Qed.

Lemma half_1_2_eq_3_6 : ((1 # 2) == (3 # 6))%Q.
Proof. reflexivity. Qed.

Lemma half_1_2_distinct_3_6 : (1 # 2 : Q) <> (3 # 6 : Q).
Proof. intro H. inversion H. Qed.

Lemma half_2_4_eq_3_6 : ((2 # 4) == (3 # 6))%Q.
Proof. reflexivity. Qed.

Lemma half_2_4_distinct_3_6 : (2 # 4 : Q) <> (3 # 6 : Q).
Proof. intro H. inversion H. Qed.


(* Apply general theorem — three concrete pair
   proofs from one generic result. *)

Theorem halves_1_2_and_2_4_paper_projection :
  (exists c : RationalRep.Entity,
     RationalRep.interact half_1_2 c = RationalRep.interact half_2_4 c)
  /\ half_1_2 <> half_2_4.
Proof.
  apply RationalRep.rational_equivalent_paper_projection.
  - exact half_1_2_eq_2_4.
  - exact half_1_2_distinct_2_4.
Qed.

Theorem halves_1_2_and_3_6_paper_projection :
  (exists c : RationalRep.Entity,
     RationalRep.interact half_1_2 c = RationalRep.interact half_3_6 c)
  /\ half_1_2 <> half_3_6.
Proof.
  apply RationalRep.rational_equivalent_paper_projection.
  - exact half_1_2_eq_3_6.
  - exact half_1_2_distinct_3_6.
Qed.

Theorem halves_2_4_and_3_6_paper_projection :
  (exists c : RationalRep.Entity,
     RationalRep.interact half_2_4 c = RationalRep.interact half_3_6 c)
  /\ half_2_4 <> half_3_6.
Proof.
  apply RationalRep.rational_equivalent_paper_projection.
  - exact half_2_4_eq_3_6.
  - exact half_2_4_distinct_3_6.
Qed.


(* =================================================== *)
(*  3. Non-half pair: e.g., 1/3 vs 2/6.                *)
(* =================================================== *)

Definition third_1_3 : RationalRep.Entity :=
  RationalRep.REnt (1 # 3) 0.

Definition third_2_6 : RationalRep.Entity :=
  RationalRep.REnt (2 # 6) 0.

Lemma third_1_3_eq_2_6 : ((1 # 3) == (2 # 6))%Q.
Proof. reflexivity. Qed.

Lemma third_1_3_distinct_2_6 : (1 # 3 : Q) <> (2 # 6 : Q).
Proof. intro H. inversion H. Qed.

Theorem thirds_1_3_and_2_6_paper_projection :
  (exists c : RationalRep.Entity,
     RationalRep.interact third_1_3 c = RationalRep.interact third_2_6 c)
  /\ third_1_3 <> third_2_6.
Proof.
  apply RationalRep.rational_equivalent_paper_projection.
  - exact third_1_3_eq_2_6.
  - exact third_1_3_distinct_2_6.
Qed.


(* =================================================== *)
(*  4. Observational inequivalence.                    *)
(*                                                     *)
(*  Different rationals (e.g., 1/2 vs 1/3) are NOT    *)
(*  rational-equivalent, so the general theorem       *)
(*  does not apply. Framework should keep them        *)
(*  distinguishable.                                  *)
(* =================================================== *)

Definition half : RationalRep.Entity := half_1_2.
Definition third : RationalRep.Entity := third_1_3.

(* At canonical viewpoint, different rationals
   produce different interact outputs. *)

Theorem half_and_third_canonical_distinct :
  RationalRep.interact half (RationalRep.CMark 0) <>
  RationalRep.interact third (RationalRep.CMark 0).
Proof.
  unfold RationalRep.interact, half, third, half_1_2, third_1_3.
  destruct (RationalRep.entity_eq_dec
              (RationalRep.REnt (1 # 2) 0) (RationalRep.CMark 0))
    as [H1 | _].
  - inversion H1.
  - destruct (RationalRep.entity_eq_dec
                (RationalRep.REnt (1 # 3) 0) (RationalRep.CMark 0))
      as [H2 | _].
    + inversion H2.
    + simpl. intro H. inversion H.
Qed.
