(* ============================================== *)
(*  RationalRep                                     *)
(*                                                  *)
(*  Rational representations as framework           *)
(*  entities. Entity is an inductive type with      *)
(*  two constructors:                               *)
(*                                                  *)
(*    REnt q t   — representation q : Q at time t   *)
(*    CMark t    — canonicalization viewpoint       *)
(*                                                  *)
(*  Rational equivalence (cross-multiplication)     *)
(*  is paper_projection: through the CMark          *)
(*  viewpoint, distinct representations of the      *)
(*  same rational collapse to the same canonical    *)
(*  form via Qred.                                  *)
(* ============================================== *)

Require Import Existence.
Require Import ExternalTime.
From Stdlib Require Import ZArith.
From Stdlib Require Import PArith.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import QArith.


Module RationalRep.

  Inductive _Entity : Type :=
    | REnt  : Q -> nat -> _Entity
    | CMark : nat -> _Entity.

  Definition Entity : Type := _Entity.

  Definition tm_of (e : Entity) : nat :=
    match e with
    | REnt _ t => t
    | CMark t  => t
    end.

  (* =========================================== *)
  (*  Leibniz equality on Q                      *)
  (* =========================================== *)

  Definition Q_eq_dec_leibniz (q1 q2 : Q) : {q1 = q2} + {q1 <> q2}.
  Proof.
    destruct q1 as [n1 d1]. destruct q2 as [n2 d2].
    destruct (Z.eq_dec n1 n2) as [Hn | Hn].
    - destruct (Pos.eq_dec d1 d2) as [Hd | Hd].
      + left. subst. reflexivity.
      + right. intro H. inversion H. contradiction.
    - right. intro H. inversion H. contradiction.
  Defined.

  Definition entity_eq_dec (a b : Entity) : {a = b} + {a <> b}.
  Proof.
    destruct a as [qa ta | tca]; destruct b as [qb tb | tcb].
    - destruct (Q_eq_dec_leibniz qa qb) as [Hq | Hq].
      + destruct (Nat.eq_dec ta tb) as [Ht | Ht].
        * left. subst. reflexivity.
        * right. intro H. inversion H. contradiction.
      + right. intro H. inversion H. contradiction.
    - right. intro H. inversion H.
    - right. intro H. inversion H.
    - destruct (Nat.eq_dec tca tcb) as [Ht | Ht].
      + left. subst. reflexivity.
      + right. intro H. inversion H. contradiction.
  Defined.

  (* =========================================== *)
  (*  INTERACT                                   *)
  (* =========================================== *)

  Definition interact (a b : Entity) : Entity :=
    match entity_eq_dec a b with
    | left _ => a
    | right _ =>
        let new_t := S (Nat.max (tm_of a) (tm_of b)) in
        match b with
        | CMark _ =>
            match a with
            | REnt q _ => REnt (Qred q) new_t
            | CMark _  => CMark new_t
            end
        | REnt _ _ =>
            match a with
            | REnt q _ => REnt q new_t
            | CMark _  => CMark new_t
            end
        end
    end.

  Definition convention_eq (_ _ : Entity) : Prop := False.

  Definition external_time (a : Entity) : nat := tm_of a.

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
    exists (REnt (0 # 1) 0), (CMark 0).
    intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b : Entity, interact a b <> a.
  Proof.
    intros [q t | t].
    - exists (REnt q (S t)).
      unfold interact.
      destruct (entity_eq_dec (REnt q t) (REnt q (S t))) as [Heq | _].
      + exfalso. inversion Heq. lia.
      + simpl. intro H. inversion H. lia.
    - exists (CMark (S t)).
      unfold interact.
      destruct (entity_eq_dec (CMark t) (CMark (S t))) as [Heq | _].
      + exfalso. inversion Heq. lia.
      + simpl. intro H. inversion H. lia.
  Qed.

  Theorem convention_not_derivable :
    forall a b : Entity,
      convention_eq a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof. intros a b H. destruct H. Qed.

  Theorem external_time_advances_on_nonself :
    forall a c : Entity,
      interact a c <> a ->
      (external_time (interact a c) > external_time a)%nat.
  Proof.
    intros a c Hne.
    unfold interact in Hne. unfold interact.
    destruct (entity_eq_dec a c) as [_ | _].
    - exfalso. apply Hne. reflexivity.
    - unfold external_time.
      destruct c as [qc tc | tc]; destruct a as [qa ta | ta]; simpl; lia.
  Qed.

  (* =========================================== *)
  (*  GENERAL PAPER_PROJECTION THEOREM           *)
  (* =========================================== *)

  Theorem rational_equivalent_paper_projection :
    forall (q1 q2 : Q) (t : nat),
      (q1 == q2)%Q ->
      q1 <> q2 ->
      (exists c : Entity,
         interact (REnt q1 t) c = interact (REnt q2 t) c)
      /\ REnt q1 t <> REnt q2 t.
  Proof.
    intros q1 q2 t Heq Hne.
    split.
    - exists (CMark 0).
      unfold interact.
      destruct (entity_eq_dec (REnt q1 t) (CMark 0)) as [Hc1 | _].
      + inversion Hc1.
      + destruct (entity_eq_dec (REnt q2 t) (CMark 0)) as [Hc2 | _].
        * inversion Hc2.
        * simpl.
          rewrite (Qred_complete q1 q2 Heq).
          reflexivity.
    - intro H. inversion H. contradiction.
  Qed.

End RationalRep.


(* Static verification that RationalRep satisfies the
   ExternalTimeSig interface. *)

Module RationalRep_is_ExternalTime : ExternalTimeSig := RationalRep.
