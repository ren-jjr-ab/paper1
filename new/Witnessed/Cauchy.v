(* ============================================== *)
(*  CauchyReal                                      *)
(*                                                  *)
(*  Cauchy sequences over Q as framework entities,  *)
(*  carrying BOTH = (paper_projection) and ≈        *)
(*  (collapse) equalities in one instance.     *)
(*                                                  *)
(*  - ≡ : syntactic identity on CauchyTerm.         *)
(*  - = : pointwise-equal (valuewise at every       *)
(*        index) but syntactically distinct —       *)
(*        finite witness at a CEval viewpoint       *)
(*        collapses them to the same CTConst.       *)
(*  - ≈ : cauchy-equivalent (same real limit via    *)
(*        ε-δ) but pointwise-distinct at every      *)
(*        index — no finite viewpoint can witness   *)
(*        agreement. collapse pays the         *)
(*        unsound/incomplete cost to declare equal  *)
(*        what time's flow cannot.                  *)
(*                                                  *)
(*  CauchyTerm grammar — structural, no limit       *)
(*  parameter:                                      *)
(*    CTConst q    s(n) = q                         *)
(*    CTInvSucc    s(n) = 1/(n+1)                   *)
(*    CTSum a b    s(n) = a(n) + b(n)               *)
(*    CTNeg a      s(n) = -a(n)                     *)
(*    CTScale q a  s(n) = q · a(n)                  *)
(*                                                  *)
(*  Entity:                                         *)
(*    REnt  s t    sequence at external time t      *)
(*    CEval n t    "evaluate at index n" viewpoint  *)
(*                                                  *)
(*  Interact:                                       *)
(*    self                     → identity           *)
(*    REnt s _, CEval n _      → REnt (CTConst      *)
(*                                 (Qred (s n))) t' *)
(*    REnt s _, REnt _ _       → REnt s t' (source  *)
(*                                 preserving)      *)
(*    CEval n _, _             → CEval n t'         *)
(*                                                  *)
(*  cauchy_equivalent is concrete ε-δ on denote —   *)
(*  no external axioms (no Classical, no FunExt).   *)
(* ============================================== *)

Require Import Existence.
Require Import Witnessed.
From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import PArith.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module CauchyReal <: WitnessedSig.

  (* =========================================== *)
  (*  CAUCHY TERM GRAMMAR                        *)
  (*                                             *)
  (*  Structural, decidable. Denote determines   *)
  (*  values; limit is NOT a parameter.          *)
  (* =========================================== *)

  Inductive _CauchyTerm : Type :=
    | CTConst   : Q -> _CauchyTerm
    | CTInvSucc : _CauchyTerm
    | CTSum     : _CauchyTerm -> _CauchyTerm -> _CauchyTerm
    | CTNeg     : _CauchyTerm -> _CauchyTerm
    | CTScale   : Q -> _CauchyTerm -> _CauchyTerm
    | CTMul     : _CauchyTerm -> _CauchyTerm -> _CauchyTerm.

  Definition CauchyTerm : Type := _CauchyTerm.

  Fixpoint denote (t : CauchyTerm) (n : nat) : Q :=
    match t with
    | CTConst q    => q
    | CTInvSucc    => 1 # Pos.of_succ_nat n
    | CTSum a b    => denote a n + denote b n
    | CTNeg a      => - denote a n
    | CTScale q a  => q * denote a n
    | CTMul a b    => denote a n * denote b n
    end.

  (* =========================================== *)
  (*  ε-δ CAUCHY EQUIVALENCE                     *)
  (*                                             *)
  (*  All concrete. No external axioms.          *)
  (* =========================================== *)

  Definition cauchy_equivalent (s1 s2 : CauchyTerm) : Prop :=
    forall k : nat,
      exists N : nat,
        forall n : nat, (n >= N)%nat ->
          (Qabs (denote s1 n - denote s2 n) <= 1 # Pos.of_succ_nat k)%Q.

  Definition pointwise_equal (s1 s2 : CauchyTerm) : Prop :=
    forall n : nat, (denote s1 n == denote s2 n)%Q.

  Definition pointwise_distinct (s1 s2 : CauchyTerm) : Prop :=
    forall n : nat, ~ (denote s1 n == denote s2 n)%Q.

  (* =========================================== *)
  (*  ENTITY                                     *)
  (* =========================================== *)

  Inductive _Entity : Type :=
    | REnt  : CauchyTerm -> nat -> _Entity
    | CEval : nat -> nat -> _Entity.

  Definition Entity : Type := _Entity.

  Definition tm_of (e : Entity) : nat :=
    match e with
    | REnt _ t  => t
    | CEval _ t => t
    end.

  (* =========================================== *)
  (*  DECIDABLE EQUALITY                         *)
  (* =========================================== *)

  Definition Q_leibniz_eq_dec (q1 q2 : Q) : {q1 = q2} + {q1 <> q2}.
  Proof.
    destruct q1 as [n1 d1]. destruct q2 as [n2 d2].
    destruct (Z.eq_dec n1 n2) as [Hn | Hn].
    - destruct (Pos.eq_dec d1 d2) as [Hd | Hd].
      + left. subst. reflexivity.
      + right. intro H. inversion H. contradiction.
    - right. intro H. inversion H. contradiction.
  Defined.

  Fixpoint term_eq_dec (t1 t2 : CauchyTerm) : {t1 = t2} + {t1 <> t2}.
  Proof.
    destruct t1 as [q1 | | a1 b1 | a1 | q1 a1 | a1 b1];
      destruct t2 as [q2 | | a2 b2 | a2 | q2 a2 | a2 b2];
      try (right; intro H; inversion H; fail).
    - destruct (Q_leibniz_eq_dec q1 q2) as [Hq | Hq].
      + left. subst. reflexivity.
      + right. intro H. inversion H. contradiction.
    - left. reflexivity.
    - destruct (term_eq_dec a1 a2) as [Ha | Ha].
      + destruct (term_eq_dec b1 b2) as [Hb | Hb].
        * left. subst. reflexivity.
        * right. intro H. inversion H. contradiction.
      + right. intro H. inversion H. contradiction.
    - destruct (term_eq_dec a1 a2) as [Ha | Ha].
      + left. subst. reflexivity.
      + right. intro H. inversion H. contradiction.
    - destruct (Q_leibniz_eq_dec q1 q2) as [Hq | Hq].
      + destruct (term_eq_dec a1 a2) as [Ha | Ha].
        * left. subst. reflexivity.
        * right. intro H. inversion H. contradiction.
      + right. intro H. inversion H. contradiction.
    - destruct (term_eq_dec a1 a2) as [Ha | Ha].
      + destruct (term_eq_dec b1 b2) as [Hb | Hb].
        * left. subst. reflexivity.
        * right. intro H. inversion H. contradiction.
      + right. intro H. inversion H. contradiction.
  Defined.

  Definition entity_eq_dec (a b : Entity) : {a = b} + {a <> b}.
  Proof.
    destruct a as [s1 t1 | n1 t1]; destruct b as [s2 t2 | n2 t2].
    - destruct (term_eq_dec s1 s2) as [Hs | Hs].
      + destruct (Nat.eq_dec t1 t2) as [Ht | Ht].
        * left. subst. reflexivity.
        * right. intro H. inversion H. contradiction.
      + right. intro H. inversion H. contradiction.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - destruct (Nat.eq_dec n1 n2) as [Hn | Hn].
      + destruct (Nat.eq_dec t1 t2) as [Ht | Ht].
        * left. subst. reflexivity.
        * right. intro H. inversion H. contradiction.
      + right. intro H. inversion H. contradiction.
  Defined.

  (* =========================================== *)
  (*  INTERACT / CONVENTION / EXTERNAL TIME      *)
  (* =========================================== *)

  Definition interact (a b : Entity) : Entity :=
    match entity_eq_dec a b with
    | left _ => a
    | right _ =>
        let new_t := S (Nat.max (tm_of a) (tm_of b)) in
        match a, b with
        | REnt s _, CEval n _ =>
            REnt (CTConst (Qred (denote s n))) new_t
        | REnt s _, REnt _ _ =>
            REnt s new_t
        | CEval n _, _ =>
            CEval n new_t
        end
    end.

  Definition collapse (a b : Entity) : Prop :=
    match a, b with
    | REnt s1 _, REnt s2 _ =>
        s1 <> s2 /\
        cauchy_equivalent s1 s2 /\
        pointwise_distinct s1 s2
    | _, _ => False
    end.

  Definition witness_time (a : Entity) : nat := tm_of a.

  (* =========================================== *)
  (*  AXIOM PROOFS                               *)
  (* =========================================== *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intro a. unfold interact.
    destruct (entity_eq_dec a a) as [_ | H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply entity_eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (REnt (CTConst 0) 0), (CEval 0 0).
    intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b : Entity, interact a b <> a.
  Proof.
    intros [s t | n t].
    - exists (REnt s (S t)).
      unfold interact.
      destruct (entity_eq_dec (REnt s t) (REnt s (S t))) as [Heq | _].
      + exfalso. inversion Heq. lia.
      + simpl. intro H. inversion H. lia.
    - exists (CEval n (S t)).
      unfold interact.
      destruct (entity_eq_dec (CEval n t) (CEval n (S t))) as [Heq | _].
      + exfalso. inversion Heq. lia.
      + simpl. intro H. inversion H. lia.
  Qed.

  (* =========================================== *)
  (*  CONVENTION_NOT_DERIVABLE                   *)
  (*                                             *)
  (*  For REnt s1 t1, REnt s2 t2 with distinct   *)
  (*  specs and pointwise_distinct values, every *)
  (*  viewpoint disagreement holds:              *)
  (*                                             *)
  (*  - REnt c: source-preserve → distinct by    *)
  (*    s1 ≠ s2.                                 *)
  (*  - CEval n c: both collapse to              *)
  (*    REnt (CTConst (Qred (denote _ n))) _ ;   *)
  (*    Qred (denote s1 n) ≠ Qred (denote s2 n)  *)
  (*    by pointwise_distinct (via Qred_correct  *)
  (*    contrapositive).                         *)
  (* =========================================== *)

  Lemma Qred_inj_Qeq :
    forall q1 q2 : Q, Qred q1 = Qred q2 -> (q1 == q2)%Q.
  Proof.
    intros q1 q2 H.
    rewrite <- (Qred_correct q1).
    rewrite <- (Qred_correct q2).
    rewrite H. reflexivity.
  Qed.

  Theorem interaction_cannot_witness_collapse :
    forall a b : Entity,
      collapse a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof.
    intros a b Hconv c.
    destruct a as [s1 t1 | n1 t1];
      destruct b as [s2 t2 | n2 t2];
      try (simpl in Hconv; contradiction).
    simpl in Hconv. destruct Hconv as [Hne [_ Hpd]].
    unfold interact.
    destruct (entity_eq_dec (REnt s1 t1) c) as [Ha | Ha];
      destruct (entity_eq_dec (REnt s2 t2) c) as [Hb | Hb].
    - (* both self: forces REnt s1 t1 = REnt s2 t2, contradiction *)
      subst c. congruence.
    - (* c = REnt s1 t1 (= a); b ≠ c *)
      subst c. intro H. apply Hne. congruence.
    - (* c = REnt s2 t2 (= b); a ≠ c *)
      subst c. intro H. apply Hne. congruence.
    - (* a ≠ c, b ≠ c *)
      destruct c as [sc tc | nc tc].
      + (* c = REnt sc tc: source-preserve both *)
        intro H. apply Hne. congruence.
      + (* c = CEval nc tc: both collapse to CTConst (Qred (denote _ nc)) *)
        intro H. inversion H as [Hq].
        apply (Hpd nc).
        apply Qred_inj_Qeq.
        exact Hq.
  Qed.

  Theorem witness_advances_on_nonself :
    forall a c : Entity,
      interact a c <> a ->
      (witness_time (interact a c) > witness_time a)%nat.
  Proof.
    intros a c Hne.
    unfold interact in Hne. unfold interact.
    destruct (entity_eq_dec a c) as [_ | _].
    - exfalso. apply Hne. reflexivity.
    - unfold witness_time.
      destruct a as [sa ta | na ta]; destruct c as [sc tc | nc tc]; simpl; lia.
  Qed.

  (* =========================================== *)
  (*  GENERAL PAPER_PROJECTION (=) THEOREM       *)
  (*                                             *)
  (*  Pointwise-equal but syntactically distinct *)
  (*  terms collapse at any CEval viewpoint via  *)
  (*  Qred. Witness at CEval 0 0.                *)
  (* =========================================== *)

  Theorem pointwise_equal_paper_projection :
    forall (s1 s2 : CauchyTerm) (t : nat),
      s1 <> s2 ->
      pointwise_equal s1 s2 ->
      (exists c : Entity,
         interact (REnt s1 t) c = interact (REnt s2 t) c)
      /\ REnt s1 t <> REnt s2 t.
  Proof.
    intros s1 s2 t Hne Hpe.
    split.
    - exists (CEval 0%nat 0%nat).
      unfold interact.
      destruct (entity_eq_dec (REnt s1 t) (CEval 0%nat 0%nat)) as [Hc1 | _];
        [inversion Hc1 |].
      destruct (entity_eq_dec (REnt s2 t) (CEval 0%nat 0%nat)) as [Hc2 | _];
        [inversion Hc2 |].
      simpl.
      rewrite (Qred_complete (denote s1 0%nat) (denote s2 0%nat) (Hpe 0%nat)).
      reflexivity.
    - intro H. inversion H. contradiction.
  Qed.

  (* =========================================== *)
  (*  GENERAL CONVENTION (≈) THEOREM             *)
  (*                                             *)
  (*  cauchy_equivalent + pointwise_distinct +   *)
  (*  syntactic distinctness → collapse.    *)
  (* =========================================== *)

  Theorem cauchy_pointwise_distinct_convention :
    forall (s1 s2 : CauchyTerm) (t1 t2 : nat),
      s1 <> s2 ->
      cauchy_equivalent s1 s2 ->
      pointwise_distinct s1 s2 ->
      collapse (REnt s1 t1) (REnt s2 t2).
  Proof.
    intros. simpl. repeat split; assumption.
  Qed.

End CauchyReal.


(* Signature check. *)
Module CauchyReal_is_Witnessed : WitnessedSig := CauchyReal.
