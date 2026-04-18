(* ============================================== *)
(*  CauchyRealTest                                  *)
(*                                                  *)
(*  Verify both equalities are live in CauchyReal:  *)
(*                                                  *)
(*  1. Functors (ExistenceTheory, ExternalTime      *)
(*     Theory) apply.                               *)
(*                                                  *)
(*  2. = case (paper_projection) — pointwise        *)
(*     equal, syntactically distinct terms          *)
(*     collapse at CEval.                           *)
(*                                                  *)
(*  3. ≈ case (convention_eq) — cauchy-equivalent   *)
(*     pointwise-distinct pair with concrete        *)
(*     ε-δ proof, no external axioms.               *)
(* ============================================== *)

Require Import Existence.
Require Import ExternalTime.
Require Import CauchyReal.
From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import PArith.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module CR_Theory  := ExistenceTheory     CauchyReal_is_ExternalTime.
Module CR_ExtTime := ExternalTimeTheory  CauchyReal_is_ExternalTime.

Check CR_Theory.is_terminal_impossible.
Check CR_Theory.convention_eq_irreflexive.
Check CR_Theory.observational_equivalence_excludes_convention.
Check CR_ExtTime.exists_external_time_advancing_partner.


(* ===================================================== *)
(*  ε-δ SUPPORT LEMMAS                                   *)
(* ===================================================== *)

Lemma pos_of_succ_nat_le :
  forall k n : nat, (k <= n)%nat ->
    (Pos.of_succ_nat k <= Pos.of_succ_nat n)%positive.
Proof.
  intros k n Hle.
  apply Pos2Nat.inj_le.
  rewrite !SuccNat2Pos.id_succ.
  lia.
Qed.

Lemma Qle_inv_succ_nat :
  forall k n : nat, (k <= n)%nat ->
    (1 # Pos.of_succ_nat n <= 1 # Pos.of_succ_nat k)%Q.
Proof.
  intros k n Hle.
  unfold Qle. simpl.
  apply Pos2Z.pos_le_pos.
  apply pos_of_succ_nat_le. exact Hle.
Qed.


(* ===================================================== *)
(*  =  CASE                                              *)
(*                                                       *)
(*  CTConst 1 and CTScale 1 (CTConst 1) —                *)
(*  denote gives 1 and 1 · 1 = 1 pointwise; same         *)
(*  Qeq everywhere. Syntactically distinct. Finite       *)
(*  witness at CEval 0 0 (Qred collapses both to         *)
(*  CTConst (Qred 1)).                                   *)
(* ===================================================== *)

Definition const_1 : CauchyReal.CauchyTerm :=
  CauchyReal.CTConst 1.

Definition scale_1_const_1 : CauchyReal.CauchyTerm :=
  CauchyReal.CTScale 1 const_1.

Lemma const_scale_distinct :
  const_1 <> scale_1_const_1.
Proof. intro H. inversion H. Qed.

Lemma const_scale_pointwise_equal :
  CauchyReal.pointwise_equal const_1 scale_1_const_1.
Proof.
  intros n. unfold const_1, scale_1_const_1.
  simpl. ring.
Qed.

Theorem const_scale_paper_projection :
  (exists c : CauchyReal.Entity,
     CauchyReal.interact (CauchyReal.REnt const_1 0%nat) c =
     CauchyReal.interact (CauchyReal.REnt scale_1_const_1 0%nat) c)
  /\ CauchyReal.REnt const_1 0%nat <>
     CauchyReal.REnt scale_1_const_1 0%nat.
Proof.
  apply CauchyReal.pointwise_equal_paper_projection.
  - exact const_scale_distinct.
  - exact const_scale_pointwise_equal.
Qed.


(* ===================================================== *)
(*  ≈  CASE                                              *)
(*                                                       *)
(*  CTConst 1 and CTSum (CTConst 1) CTInvSucc.           *)
(*  denote difference is 1/(n+1) at index n —            *)
(*  pointwise_distinct (always > 0) and                  *)
(*  cauchy_equivalent (ε-δ: N = k).                      *)
(* ===================================================== *)

Definition one_plus_invsucc : CauchyReal.CauchyTerm :=
  CauchyReal.CTSum const_1 CauchyReal.CTInvSucc.

Lemma const_sum_distinct :
  const_1 <> one_plus_invsucc.
Proof. intro H. inversion H. Qed.

Lemma const_sum_pointwise_distinct :
  CauchyReal.pointwise_distinct const_1 one_plus_invsucc.
Proof.
  intros n.
  unfold const_1, one_plus_invsucc.
  simpl.
  unfold Qeq. simpl.
  intro H.
  (* H : 1 * Zpos (1 * Pos.of_succ_nat n) =
         (1 * Zpos (Pos.of_succ_nat n) + 1 * 1) * 1    *)
  (* i.e. Zpos (Pos.of_succ_nat n) = Zpos (Pos.of_succ_nat n) + 1 *)
  lia.
Qed.

Lemma const_sum_cauchy_equivalent :
  CauchyReal.cauchy_equivalent const_1 one_plus_invsucc.
Proof.
  intros k. exists k. intros n Hn.
  unfold const_1, one_plus_invsucc.
  cbn [CauchyReal.denote].
  set (x := (1 # Pos.of_succ_nat n)%Q).
  assert (Hdiff : ((1 - (1 + x)) == - x)%Q) by ring.
  rewrite Hdiff.
  rewrite Qabs_opp.
  assert (Hnn : (0 <= x)%Q).
  { subst x. unfold Qle. simpl. lia. }
  rewrite Qabs_pos; [| exact Hnn].
  subst x.
  apply Qle_inv_succ_nat. exact Hn.
Qed.

Theorem const_sum_convention_eq :
  CauchyReal.convention_eq
    (CauchyReal.REnt const_1 0%nat)
    (CauchyReal.REnt one_plus_invsucc 0%nat).
Proof.
  apply CauchyReal.cauchy_pointwise_distinct_convention.
  - exact const_sum_distinct.
  - exact const_sum_cauchy_equivalent.
  - exact const_sum_pointwise_distinct.
Qed.

(* Framework consequence: no viewpoint bridges them. *)

Theorem const_sum_no_viewpoint_bridges :
  forall c : CauchyReal.Entity,
    CauchyReal.interact (CauchyReal.REnt const_1 0%nat) c <>
    CauchyReal.interact (CauchyReal.REnt one_plus_invsucc 0%nat) c.
Proof.
  apply CauchyReal.convention_not_derivable.
  exact const_sum_convention_eq.
Qed.
