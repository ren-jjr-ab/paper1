(* ============================================== *)
(*  NatSetExtensionality                            *)
(*                                                  *)
(*  Set-theoretic paper projection (framework's =   *)
(*  axis) witnessed on NatSet. Classical set        *)
(*  extensionality — two sets with the same         *)
(*  members are equal — becomes a framework         *)
(*  paper projection: syntactically distinct        *)
(*  SetExpr values that agree at every SQuery       *)
(*  viewpoint.                                      *)
(*                                                  *)
(*  Theorems:                                       *)
(*                                                  *)
(*  - ext_eq_paper_projection — the general bridge  *)
(*    from extensional equality to framework =.     *)
(*                                                  *)
(*  - Concrete witnesses: permutation, multiplicity,*)
(*    set-operation laws, complement duality.       *)
(* ============================================== *)

Require Import Existence.
Require Import ExternalTime.
Require Import ElemSig.
Require SymbolicSet.
Require Import NatSet.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.

Import NatSet.


(* ================================================ *)
(*  GENERAL BRIDGE — ext_eq IMPLIES PAPER PROJECTION*)
(* ================================================ *)

Theorem ext_eq_paper_projection :
  forall (s1 s2 : SetExpr) (t : nat),
    s1 <> s2 ->
    ext_eq s1 s2 ->
    (exists c : Entity, interact (SREnt s1 t) c = interact (SREnt s2 t) c)
    /\ SREnt s1 t <> SREnt s2 t.
Proof.
  intros s1 s2 t Hne Hee.
  split.
  - exists (SQuery NatElem.witness 0).
    unfold interact.
    destruct (entity_eq_dec (SREnt s1 t) (SQuery NatElem.witness 0)) as [Hc | _].
    { inversion Hc. }
    destruct (entity_eq_dec (SREnt s2 t) (SQuery NatElem.witness 0)) as [Hc | _].
    { inversion Hc. }
    rewrite (Hee NatElem.witness). reflexivity.
  - intros H. inversion H. contradiction.
Qed.


(* ================================================ *)
(*  WITNESS 1 — PERMUTATION {1, 2} = {2, 1}          *)
(* ================================================ *)

Definition set_1_2 : SetExpr := SInsert 1 (SInsert 2 SEmpty).
Definition set_2_1 : SetExpr := SInsert 2 (SInsert 1 SEmpty).

Theorem set_1_2_ne_set_2_1 : set_1_2 <> set_2_1.
Proof. intros H. inversion H. Qed.

Theorem set_1_2_ext_eq_set_2_1 : ext_eq set_1_2 set_2_1.
Proof.
  intros x. unfold set_1_2, set_2_1, member_bool.
  destruct (NatElem.elem_eq_dec x 1) as [H1 | H1];
    destruct (NatElem.elem_eq_dec x 2) as [H2 | H2];
    reflexivity.
Qed.

Theorem set_1_2_eq_set_2_1_paper_projection :
  (exists c : Entity,
     interact (SREnt set_1_2 0) c = interact (SREnt set_2_1 0) c)
  /\ SREnt set_1_2 0 <> SREnt set_2_1 0.
Proof.
  apply ext_eq_paper_projection.
  - exact set_1_2_ne_set_2_1.
  - exact set_1_2_ext_eq_set_2_1.
Qed.


(* ================================================ *)
(*  WITNESS 2 — MULTIPLICITY {1, 1, 2} = {1, 2}      *)
(* ================================================ *)

Definition set_1_1_2 : SetExpr := SInsert 1 (SInsert 1 (SInsert 2 SEmpty)).

Theorem set_1_1_2_ne_set_1_2 : set_1_1_2 <> set_1_2.
Proof. intros H. inversion H. Qed.

Theorem set_1_1_2_ext_eq_set_1_2 : ext_eq set_1_1_2 set_1_2.
Proof.
  intros x. unfold set_1_1_2, set_1_2, member_bool.
  destruct (NatElem.elem_eq_dec x 1); destruct (NatElem.elem_eq_dec x 2);
    reflexivity.
Qed.

Theorem multiplicity_paper_projection :
  (exists c : Entity,
     interact (SREnt set_1_1_2 0) c = interact (SREnt set_1_2 0) c)
  /\ SREnt set_1_1_2 0 <> SREnt set_1_2 0.
Proof.
  apply ext_eq_paper_projection.
  - exact set_1_1_2_ne_set_1_2.
  - exact set_1_1_2_ext_eq_set_1_2.
Qed.


(* ================================================ *)
(*  WITNESS 3 — UNION IDEMPOTENCE A ∪ A = A          *)
(* ================================================ *)

Theorem union_idempotent_ext_eq :
  forall s : SetExpr, ext_eq (SUnion s s) s.
Proof.
  intros s x. unfold member_bool at 1. fold member_bool.
  apply orb_diag.
Qed.

Theorem union_self_ne :
  SUnion set_1_2 set_1_2 <> set_1_2.
Proof. intros H. inversion H. Qed.

Theorem union_idempotent_paper_projection :
  (exists c : Entity,
     interact (SREnt (SUnion set_1_2 set_1_2) 0) c =
     interact (SREnt set_1_2 0) c)
  /\ SREnt (SUnion set_1_2 set_1_2) 0 <> SREnt set_1_2 0.
Proof.
  apply ext_eq_paper_projection.
  - exact union_self_ne.
  - apply union_idempotent_ext_eq.
Qed.


(* ================================================ *)
(*  WITNESS 4 — UNION COMMUTATIVITY                  *)
(* ================================================ *)

Theorem union_commutative_ext_eq :
  forall a b : SetExpr, ext_eq (SUnion a b) (SUnion b a).
Proof.
  intros a b x. unfold member_bool at 1 2. fold member_bool.
  apply orb_comm.
Qed.

Theorem union_a_b_ne_b_a :
  SUnion (SInsert 1 SEmpty) (SInsert 2 SEmpty) <>
  SUnion (SInsert 2 SEmpty) (SInsert 1 SEmpty).
Proof. intros H. inversion H. Qed.

Theorem union_commutative_paper_projection :
  (exists c : Entity,
     interact (SREnt (SUnion (SInsert 1 SEmpty) (SInsert 2 SEmpty)) 0) c =
     interact (SREnt (SUnion (SInsert 2 SEmpty) (SInsert 1 SEmpty)) 0) c)
  /\ SREnt (SUnion (SInsert 1 SEmpty) (SInsert 2 SEmpty)) 0 <>
     SREnt (SUnion (SInsert 2 SEmpty) (SInsert 1 SEmpty)) 0.
Proof.
  apply ext_eq_paper_projection.
  - exact union_a_b_ne_b_a.
  - apply union_commutative_ext_eq.
Qed.


(* ================================================ *)
(*  WITNESS 5 — INTERSECT IDEMPOTENCE                *)
(* ================================================ *)

Theorem intersect_idempotent_ext_eq :
  forall s : SetExpr, ext_eq (SIntersect s s) s.
Proof.
  intros s x. unfold member_bool at 1. fold member_bool.
  apply andb_diag.
Qed.

Theorem intersect_idempotent_paper_projection :
  (exists c : Entity,
     interact (SREnt (SIntersect set_1_2 set_1_2) 0) c =
     interact (SREnt set_1_2 0) c)
  /\ SREnt (SIntersect set_1_2 set_1_2) 0 <> SREnt set_1_2 0.
Proof.
  apply ext_eq_paper_projection.
  - intros H. inversion H.
  - apply intersect_idempotent_ext_eq.
Qed.


(* ================================================ *)
(*  WITNESS 6 — COMPLEMENT DUALITY                   *)
(*                                                   *)
(*  SComplement SAll agrees with SEmpty at every    *)
(*  viewpoint. Two "different" representations of   *)
(*  the empty set are paper-projection equal.       *)
(* ================================================ *)

Theorem complement_all_ext_eq_empty :
  ext_eq (SComplement SAll) SEmpty.
Proof. intros x. unfold member_bool. reflexivity. Qed.

Theorem complement_empty_ext_eq_all :
  ext_eq (SComplement SEmpty) SAll.
Proof. intros x. unfold member_bool. reflexivity. Qed.

Theorem complement_all_paper_projection :
  (exists c : Entity,
     interact (SREnt (SComplement SAll) 0) c =
     interact (SREnt SEmpty 0) c)
  /\ SREnt (SComplement SAll) 0 <> SREnt SEmpty 0.
Proof.
  apply ext_eq_paper_projection.
  - intros H. inversion H.
  - apply complement_all_ext_eq_empty.
Qed.

Theorem complement_empty_paper_projection :
  (exists c : Entity,
     interact (SREnt (SComplement SEmpty) 0) c =
     interact (SREnt SAll 0) c)
  /\ SREnt (SComplement SEmpty) 0 <> SREnt SAll 0.
Proof.
  apply ext_eq_paper_projection.
  - intros H. inversion H.
  - apply complement_empty_ext_eq_all.
Qed.


(* ================================================ *)
(*  WITNESS 7 — DOUBLE COMPLEMENT (INVOLUTION)       *)
(*                                                   *)
(*  ¬¬A = A at every viewpoint.                      *)
(* ================================================ *)

Theorem double_complement_ext_eq :
  forall s : SetExpr, ext_eq (SComplement (SComplement s)) s.
Proof.
  intros s x. unfold member_bool at 1. fold member_bool.
  apply negb_involutive.
Qed.

Theorem double_complement_paper_projection :
  (exists c : Entity,
     interact (SREnt (SComplement (SComplement set_1_2)) 0) c =
     interact (SREnt set_1_2 0) c)
  /\ SREnt (SComplement (SComplement set_1_2)) 0 <> SREnt set_1_2 0.
Proof.
  apply ext_eq_paper_projection.
  - intros H. inversion H.
  - apply double_complement_ext_eq.
Qed.


(* ================================================ *)
(*  SYNTACTIC DISTINCTNESS (≡)                       *)
(*                                                   *)
(*  All of the above are Leibniz-distinct at the    *)
(*  SetExpr level despite being paper-projection    *)
(*  equal. The framework's three-axis equality      *)
(*  separates "same representation" from "same      *)
(*  members".                                        *)
(* ================================================ *)

Theorem three_axis_separation_at_set_level :
  (* ≡ : syntactically distinct *)
  set_1_2 <> set_2_1 /\
  (* = : paper-projection equal (via ext_eq) *)
  ext_eq set_1_2 set_2_1 /\
  (* ≈ : convention vacuous in Sprint 1 *)
  ~ convention_eq (SREnt set_1_2 0) (SREnt set_2_1 0).
Proof.
  repeat split.
  - exact set_1_2_ne_set_2_1.
  - exact set_1_2_ext_eq_set_2_1.
  - intros H. destruct H.
Qed.
