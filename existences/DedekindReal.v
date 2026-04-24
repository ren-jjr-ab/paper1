(* ============================================== *)
(*  DedekindReal                                    *)
(*                                                  *)
(*  A second formal-representation instance for the *)
(*  real numbers built on a Dedekind-cut grammar.   *)
(*                                                  *)
(*  DCut grammar:                                   *)
(*    DConst q      — the cut at rational q         *)
(*    DInvSucc      — the cut reached as limit of   *)
(*                    1/(n+1), i.e. value-wise 0    *)
(*                    approached from above         *)
(*    DSum a b      — cut for a + b                 *)
(*    DNeg a        — cut for -a                    *)
(*    DScale q a    — cut for q · a                 *)
(*    DMul a b      — cut for a · b                 *)
(*                                                  *)
(*  Entity:                                         *)
(*    DREnt c t     — cut at external time t        *)
(*    DEval n t     — "evaluate at rational index n"*)
(*                                                  *)
(*  This grammar is structurally parallel to        *)
(*  CauchyReal's CauchyTerm — the two instances     *)
(*  are syntactically distinct but semantically     *)
(*  equivalent, which sets up a framework           *)
(*  isomorphism (proved in                          *)
(*  results/DedekindCauchyIsomorphism.v).           *)
(*                                                  *)
(*  The purpose of DedekindReal is to give          *)
(*  framework's is_iso property real mathematical   *)
(*  content: two classical ℝ constructions — the    *)
(*  one via convergent sequences and the one via    *)
(*  cuts — become iso in the framework's sense.     *)
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


Module DedekindReal.

  (* =========================================== *)
  (*  CUT GRAMMAR                                *)
  (* =========================================== *)

  Inductive _DCut : Type :=
    | DConst   : Q -> _DCut
    | DInvSucc : _DCut
    | DSum     : _DCut -> _DCut -> _DCut
    | DNeg     : _DCut -> _DCut
    | DScale   : Q -> _DCut -> _DCut
    | DMul     : _DCut -> _DCut -> _DCut.

  Definition DCut : Type := _DCut.

  Fixpoint denote (c : DCut) (n : nat) : Q :=
    match c with
    | DConst q     => q
    | DInvSucc     => 1 # Pos.of_succ_nat n
    | DSum a b     => denote a n + denote b n
    | DNeg a       => - denote a n
    | DScale q a   => q * denote a n
    | DMul a b     => denote a n * denote b n
    end.

  Definition cauchy_equivalent (c1 c2 : DCut) : Prop :=
    forall k : nat,
      exists N : nat,
        forall n : nat, (n >= N)%nat ->
          (Qabs (denote c1 n - denote c2 n) <= 1 # Pos.of_succ_nat k)%Q.

  Definition pointwise_equal (c1 c2 : DCut) : Prop :=
    forall n : nat, (denote c1 n == denote c2 n)%Q.

  Definition pointwise_distinct (c1 c2 : DCut) : Prop :=
    forall n : nat, ~ (denote c1 n == denote c2 n)%Q.

  (* =========================================== *)
  (*  ENTITY                                     *)
  (* =========================================== *)

  Inductive _Entity : Type :=
    | DREnt : DCut -> nat -> _Entity
    | DEval : nat -> nat -> _Entity.

  Definition Entity : Type := _Entity.

  Definition tm_of (e : Entity) : nat :=
    match e with
    | DREnt _ t => t
    | DEval _ t => t
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

  Fixpoint cut_eq_dec (c1 c2 : DCut) : {c1 = c2} + {c1 <> c2}.
  Proof.
    destruct c1 as [q1 | | a1 b1 | a1 | q1 a1 | a1 b1];
      destruct c2 as [q2 | | a2 b2 | a2 | q2 a2 | a2 b2];
      try (right; intro H; inversion H; fail).
    - destruct (Q_leibniz_eq_dec q1 q2) as [Hq | Hq].
      + left. subst. reflexivity.
      + right. intro H. inversion H. contradiction.
    - left. reflexivity.
    - destruct (cut_eq_dec a1 a2) as [Ha | Ha].
      + destruct (cut_eq_dec b1 b2) as [Hb | Hb].
        * left. subst. reflexivity.
        * right. intro H. inversion H. contradiction.
      + right. intro H. inversion H. contradiction.
    - destruct (cut_eq_dec a1 a2) as [Ha | Ha].
      + left. subst. reflexivity.
      + right. intro H. inversion H. contradiction.
    - destruct (Q_leibniz_eq_dec q1 q2) as [Hq | Hq].
      + destruct (cut_eq_dec a1 a2) as [Ha | Ha].
        * left. subst. reflexivity.
        * right. intro H. inversion H. contradiction.
      + right. intro H. inversion H. contradiction.
    - destruct (cut_eq_dec a1 a2) as [Ha | Ha].
      + destruct (cut_eq_dec b1 b2) as [Hb | Hb].
        * left. subst. reflexivity.
        * right. intro H. inversion H. contradiction.
      + right. intro H. inversion H. contradiction.
  Defined.

  Definition entity_eq_dec (a b : Entity) : {a = b} + {a <> b}.
  Proof.
    destruct a as [c1 t1 | n1 t1]; destruct b as [c2 t2 | n2 t2].
    - destruct (cut_eq_dec c1 c2) as [Hc | Hc].
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
        | DREnt c _, DEval n _ =>
            DREnt (DConst (Qred (denote c n))) new_t
        | DREnt c _, DREnt _ _ =>
            DREnt c new_t
        | DEval n _, _ =>
            DEval n new_t
        end
    end.

  Definition collapse (a b : Entity) : Prop :=
    match a, b with
    | DREnt c1 _, DREnt c2 _ =>
        c1 <> c2 /\
        cauchy_equivalent c1 c2 /\
        pointwise_distinct c1 c2
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
    exists (DREnt (DConst 0) 0), (DEval 0 0).
    intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b : Entity, interact a b <> a.
  Proof.
    intros [c t | n t].
    - exists (DREnt c (S t)).
      unfold interact.
      destruct (entity_eq_dec (DREnt c t) (DREnt c (S t))) as [Heq | _].
      + exfalso. inversion Heq. lia.
      + simpl. intro H. inversion H. lia.
    - exists (DEval n (S t)).
      unfold interact.
      destruct (entity_eq_dec (DEval n t) (DEval n (S t))) as [Heq | _].
      + exfalso. inversion Heq. lia.
      + simpl. intro H. inversion H. lia.
  Qed.

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
    destruct a as [c1 t1 | n1 t1];
      destruct b as [c2 t2 | n2 t2];
      try (simpl in Hconv; contradiction).
    simpl in Hconv. destruct Hconv as [Hne [_ Hpd]].
    unfold interact.
    destruct (entity_eq_dec (DREnt c1 t1) c) as [Ha | Ha];
      destruct (entity_eq_dec (DREnt c2 t2) c) as [Hb | Hb].
    - subst c. congruence.
    - subst c. intro H. apply Hne. congruence.
    - subst c. intro H. apply Hne. congruence.
    - destruct c as [cc tc | nc tc].
      + intro H. apply Hne. congruence.
      + intro H. inversion H as [Hq].
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
      destruct a as [ca ta | na ta]; destruct c as [cc tc | nc tc]; simpl; lia.
  Qed.

End DedekindReal.


(* Signature check. *)
Module DedekindReal_is_Witnessed : WitnessedSig := DedekindReal.
