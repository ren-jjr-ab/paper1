(* ============================================== *)
(*  FinSetRing                                      *)
(*                                                  *)
(*  A Boolean ring built from finite subsets of     *)
(*  a bounded universe {0, 1, ..., n-1}. Each set   *)
(*  is represented by its characteristic vector:    *)
(*  a bool list of length n whose i-th bit is true  *)
(*  iff i is in the set.                            *)
(*                                                  *)
(*  The ring operations:                            *)
(*                                                  *)
(*    add  = symmetric difference (pointwise XOR)   *)
(*    mul  = intersection          (pointwise AND)  *)
(*    neg  = identity              (a + a = ∅)      *)
(*    zero = ∅                     (const false)    *)
(*    one  = U                     (const true)     *)
(*                                                  *)
(*  This is the classical Boolean ring viewed       *)
(*  through the characteristic-function bijection   *)
(*  P(U) ≅ 2^U. Ring axioms follow from the         *)
(*  pointwise Boolean-algebra identities on         *)
(*  individual bits.                                *)
(*                                                  *)
(*  Unusual property of a Boolean ring:             *)
(*                                                  *)
(*    a + a = 0   (self-inverse under sym-diff)     *)
(*    a * a = a   (intersection is idempotent)      *)
(*                                                  *)
(*  Both derivable from the ring axioms as          *)
(*  RT lemmas — they fall out of the Carrier shape. *)
(* ============================================== *)

Require Import Ring.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.


Module Type UniverseSize.
  Parameter n : nat.
End UniverseSize.


Module FinSetRing (U : UniverseSize) <: DecEqCommRingSig.


  (* =========================================== *)
  (*  CARRIER — characteristic vector             *)
  (* =========================================== *)

  Definition Carrier : Type := { l : list bool | length l = U.n }.

  Lemma length_proof_unique :
    forall (l : list bool) (h1 h2 : length l = U.n), h1 = h2.
  Proof. intros. apply UIP_dec. exact Nat.eq_dec. Qed.

  Lemma sig_eq_by_value :
    forall x y : Carrier, proj1_sig x = proj1_sig y -> x = y.
  Proof.
    intros [xv xp] [yv yp] Hv. simpl in Hv. subst yv.
    f_equal. apply length_proof_unique.
  Qed.


  (* =========================================== *)
  (*  REPEAT — constant lists                     *)
  (* =========================================== *)

  Fixpoint repeat_bool (b : bool) (k : nat) : list bool :=
    match k with
    | 0 => []
    | S k' => b :: repeat_bool b k'
    end.

  Lemma repeat_bool_length : forall b k, length (repeat_bool b k) = k.
  Proof. intros b. induction k; simpl; [reflexivity | f_equal; exact IHk]. Qed.


  (* =========================================== *)
  (*  POINTWISE OPERATIONS ON LISTS               *)
  (* =========================================== *)

  Fixpoint xor_list (l1 l2 : list bool) : list bool :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | b1 :: r1, b2 :: r2 => xorb b1 b2 :: xor_list r1 r2
    end.

  Fixpoint and_list (l1 l2 : list bool) : list bool :=
    match l1, l2 with
    | [], _ => []
    | _, [] => []
    | b1 :: r1, b2 :: r2 => andb b1 b2 :: and_list r1 r2
    end.

  (* Length preservation for pointwise ops on equal-length lists. *)

  Lemma xor_list_length :
    forall l1 l2, length l1 = length l2 ->
      length (xor_list l1 l2) = length l1.
  Proof.
    induction l1 as [| b1 r1 IH]; intros [| b2 r2] H; simpl in *.
    - reflexivity.
    - discriminate.
    - discriminate.
    - f_equal. apply IH. lia.
  Qed.

  Lemma and_list_length :
    forall l1 l2, length l1 = length l2 ->
      length (and_list l1 l2) = length l1.
  Proof.
    induction l1 as [| b1 r1 IH]; intros [| b2 r2] H; simpl in *.
    - reflexivity.
    - discriminate.
    - discriminate.
    - f_equal. apply IH. lia.
  Qed.


  (* =========================================== *)
  (*  CONSTANTS AND OPERATIONS ON CARRIER         *)
  (* =========================================== *)

  Definition zero : Carrier.
  Proof.
    exists (repeat_bool false U.n). apply repeat_bool_length.
  Defined.

  Definition one : Carrier.
  Proof.
    exists (repeat_bool true U.n). apply repeat_bool_length.
  Defined.

  Definition add (x y : Carrier) : Carrier.
  Proof.
    exists (xor_list (proj1_sig x) (proj1_sig y)).
    destruct x as [lx Hx]. destruct y as [ly Hy]. simpl.
    rewrite xor_list_length; [exact Hx | rewrite Hx, Hy; reflexivity].
  Defined.

  Definition mul (x y : Carrier) : Carrier.
  Proof.
    exists (and_list (proj1_sig x) (proj1_sig y)).
    destruct x as [lx Hx]. destruct y as [ly Hy]. simpl.
    rewrite and_list_length; [exact Hx | rewrite Hx, Hy; reflexivity].
  Defined.

  Definition neg (x : Carrier) : Carrier := x.  (* self-inverse *)


  (* =========================================== *)
  (*  RAW-LEVEL LEMMAS                            *)
  (* =========================================== *)

  Lemma xor_list_assoc :
    forall l1 l2 l3, xor_list (xor_list l1 l2) l3 = xor_list l1 (xor_list l2 l3).
  Proof.
    induction l1 as [| b1 r1 IH]; intros [| b2 r2] [| b3 r3]; simpl;
      try reflexivity.
    f_equal.
    - destruct b1, b2, b3; reflexivity.
    - apply IH.
  Qed.

  Lemma xor_list_comm :
    forall l1 l2, length l1 = length l2 ->
      xor_list l1 l2 = xor_list l2 l1.
  Proof.
    induction l1 as [| b1 r1 IH]; intros [| b2 r2] H; simpl in *;
      try lia; try reflexivity.
    f_equal.
    - destruct b1, b2; reflexivity.
    - apply IH. lia.
  Qed.

  Lemma xor_list_zero_l :
    forall l, xor_list (repeat_bool false (length l)) l = l.
  Proof.
    induction l as [| b r IH]; simpl.
    - reflexivity.
    - rewrite IH. destruct b; reflexivity.
  Qed.

  Lemma xor_list_self :
    forall l, xor_list l l = repeat_bool false (length l).
  Proof.
    induction l as [| b r IH]; simpl.
    - reflexivity.
    - rewrite IH. destruct b; reflexivity.
  Qed.

  Lemma and_list_assoc :
    forall l1 l2 l3, and_list (and_list l1 l2) l3 = and_list l1 (and_list l2 l3).
  Proof.
    induction l1 as [| b1 r1 IH]; intros [| b2 r2] [| b3 r3]; simpl;
      try reflexivity.
    f_equal.
    - destruct b1, b2, b3; reflexivity.
    - apply IH.
  Qed.

  Lemma and_list_comm :
    forall l1 l2, length l1 = length l2 ->
      and_list l1 l2 = and_list l2 l1.
  Proof.
    induction l1 as [| b1 r1 IH]; intros [| b2 r2] H; simpl in *;
      try lia; try reflexivity.
    f_equal.
    - destruct b1, b2; reflexivity.
    - apply IH. lia.
  Qed.

  Lemma and_list_one_l :
    forall l, and_list (repeat_bool true (length l)) l = l.
  Proof.
    induction l as [| b r IH]; simpl.
    - reflexivity.
    - rewrite IH. destruct b; reflexivity.
  Qed.

  Lemma and_list_one_r :
    forall l, and_list l (repeat_bool true (length l)) = l.
  Proof.
    induction l as [| b r IH]; simpl.
    - reflexivity.
    - rewrite IH. destruct b; reflexivity.
  Qed.

  Lemma and_xor_distr_l :
    forall l1 l2 l3,
      length l2 = length l3 ->
      and_list l1 (xor_list l2 l3) =
      xor_list (and_list l1 l2) (and_list l1 l3).
  Proof.
    induction l1 as [| b1 r1 IH]; intros [| b2 r2] [| b3 r3] H; simpl in *;
      try lia; try reflexivity.
    f_equal.
    - destruct b1, b2, b3; reflexivity.
    - apply IH. lia.
  Qed.

  Lemma and_xor_distr_r :
    forall l1 l2 l3,
      length l1 = length l2 ->
      and_list (xor_list l1 l2) l3 =
      xor_list (and_list l1 l3) (and_list l2 l3).
  Proof.
    induction l1 as [| b1 r1 IH]; intros [| b2 r2] [| b3 r3] H; simpl in *;
      try lia; try reflexivity.
    f_equal.
    - destruct b1, b2, b3; reflexivity.
    - apply IH. lia.
  Qed.


  (* =========================================== *)
  (*  RING AXIOMS                                 *)
  (* =========================================== *)

  Theorem add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof.
    intros a b c. apply sig_eq_by_value. simpl.
    apply xor_list_assoc.
  Qed.

  Theorem add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b. apply sig_eq_by_value. simpl.
    destruct a as [la Ha]. destruct b as [lb Hb]. simpl.
    apply xor_list_comm. rewrite Ha, Hb. reflexivity.
  Qed.

  Theorem add_zero_l : forall a, add zero a = a.
  Proof.
    intros a. apply sig_eq_by_value. simpl.
    destruct a as [la Ha]. simpl.
    rewrite <- Ha. apply xor_list_zero_l.
  Qed.

  Theorem add_neg_l : forall a, add (neg a) a = zero.
  Proof.
    intros a. apply sig_eq_by_value. simpl.
    destruct a as [la Ha]. simpl.
    rewrite xor_list_self. rewrite Ha. reflexivity.
  Qed.

  Theorem mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof.
    intros a b c. apply sig_eq_by_value. simpl.
    apply and_list_assoc.
  Qed.

  Theorem mul_one_l : forall a, mul one a = a.
  Proof.
    intros a. apply sig_eq_by_value. simpl.
    destruct a as [la Ha]. simpl.
    rewrite <- Ha. apply and_list_one_l.
  Qed.

  Theorem mul_one_r : forall a, mul a one = a.
  Proof.
    intros a. apply sig_eq_by_value. simpl.
    destruct a as [la Ha]. simpl.
    rewrite <- Ha. apply and_list_one_r.
  Qed.

  Theorem distrib_l : forall a b c,
    mul a (add b c) = add (mul a b) (mul a c).
  Proof.
    intros a b c. apply sig_eq_by_value. simpl.
    destruct a as [la Ha]. destruct b as [lb Hb]. destruct c as [lc Hc]. simpl.
    apply and_xor_distr_l. rewrite Hb, Hc. reflexivity.
  Qed.

  Theorem distrib_r : forall a b c,
    mul (add a b) c = add (mul a c) (mul b c).
  Proof.
    intros a b c. apply sig_eq_by_value. simpl.
    destruct a as [la Ha]. destruct b as [lb Hb]. destruct c as [lc Hc]. simpl.
    apply and_xor_distr_r. rewrite Ha, Hb. reflexivity.
  Qed.

  Theorem mul_comm : forall a b, mul a b = mul b a.
  Proof.
    intros a b. apply sig_eq_by_value. simpl.
    destruct a as [la Ha]. destruct b as [lb Hb]. simpl.
    apply and_list_comm. rewrite Ha, Hb. reflexivity.
  Qed.


  (* =========================================== *)
  (*  DECIDABLE EQUALITY                          *)
  (* =========================================== *)

  Definition carrier_eq_dec : forall a b : Carrier, {a = b} + {a <> b}.
  Proof.
    intros a b.
    destruct (list_eq_dec Bool.bool_dec (proj1_sig a) (proj1_sig b))
      as [Heq | Hne].
    - left. apply sig_eq_by_value. exact Heq.
    - right. intros H. apply Hne. rewrite H. reflexivity.
  Defined.

End FinSetRing.


(* =========================================== *)
(*  CONCRETE INSTANTIATION — universe of 3      *)
(* =========================================== *)

Module FinSet3Size <: UniverseSize.
  Definition n : nat := 3.
End FinSet3Size.

Module FinSet3 := FinSetRing FinSet3Size.


(* =========================================== *)
(*  BOOLEAN RING PROPERTIES (derived)           *)
(*                                              *)
(*  Boolean ring characterizations:             *)
(*    a + a = 0   (every element self-inverse)  *)
(*    a * a = a   (intersection idempotent)     *)
(*                                              *)
(*  Both are direct consequences of the         *)
(*  construction — provable from Ring axioms    *)
(*  and the specific definitions of add/mul.    *)
(* =========================================== *)

Theorem finset3_add_self :
  forall a : FinSet3.Carrier, FinSet3.add a a = FinSet3.zero.
Proof.
  intros a. apply FinSet3.add_neg_l.
Qed.

Theorem finset3_mul_idempotent :
  forall a : FinSet3.Carrier, FinSet3.mul a a = a.
Proof.
  intros a. apply FinSet3.sig_eq_by_value. simpl.
  destruct a as [la Ha]. simpl.
  clear Ha. induction la as [| b r IH]; simpl.
  - reflexivity.
  - f_equal; [destruct b; reflexivity | exact IH].
Qed.
