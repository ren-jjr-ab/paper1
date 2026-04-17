(* ================================================ *)
(*  RealIterator.v                                   *)
(*                                                   *)
(*  A growing-approximation object. An "uncountable  *)
(*  infinite set" is read here as a sequential       *)
(*  refinement process that never terminates.        *)
(*                                                   *)
(*  Structure:                                       *)
(*    ri_prec : current precision (number of digits, *)
(*              elements, or refinement terms)       *)
(*    ri_stor : accumulated storage cost             *)
(*    ri_flip : accumulated flip cost                *)
(*                                                   *)
(*  The information size of the object equals        *)
(*  ri_prec. Each step increments ri_prec by one,    *)
(*  pays storage equal to the old precision          *)
(*  (storage_pays_capacity on the source), and pays  *)
(*  flip one (flip_pays_work with growth 1, so       *)
(*  max 1 1 = 1).                                    *)
(*                                                   *)
(*  remaining is identically None: this instance     *)
(*  refuses to commit to a finite step count, which  *)
(*  is how we read "no finite termination" at this   *)
(*  level.                                           *)
(*                                                   *)
(*  The point of the file is to attach concrete      *)
(*  numbers to the cost of treating such an object   *)
(*  as "just one thing": every step the observer     *)
(*  takes toward it pays a growing storage charge,   *)
(*  and the total after n steps is quadratic in n.   *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Record RIEnt := {
  ri_prec : nat;
  ri_stor : nat;
  ri_flip : nat
}.

(* One refinement step. The cost update matches the
   standard Computable-level formulas: storage gains
   the information size of the source, and flip
   gains max 1 growth. Here growth is always 1
   (precision increments by one each step), so flip
   simply increments by 1. The information size of
   the source is ri_prec e. *)
Definition ri_step (e : RIEnt) : RIEnt :=
  {| ri_prec := S (ri_prec e);
     ri_stor := ri_stor e + ri_prec e;
     ri_flip := ri_flip e + 1 |}.

Fixpoint ri_walk (n : nat) (e : RIEnt) : RIEnt :=
  match n with
  | 0   => e
  | S k => ri_walk k (ri_step e)
  end.

Definition ri_start : RIEnt :=
  {| ri_prec := 0; ri_stor := 0; ri_flip := 0 |}.

(* The remaining field for this instance: identically
   None. No finite step count is ever committed to. *)
Definition ri_remaining (_ : RIEnt) : option nat := None.

(* ================================================ *)
(*  COST TABLE                                       *)
(*                                                   *)
(*  After n refinement steps starting from           *)
(*  ri_start:                                        *)
(*                                                   *)
(*     n  | precision | storage     | flip           *)
(*     1  |     1     |       0     |   1            *)
(*     2  |     2     |       1     |   2            *)
(*     5  |     5     |      10     |   5            *)
(*     10 |    10     |      45     |  10            *)
(*     50 |    50     |    1225     |  50            *)
(*    100 |   100     |    4950     | 100            *)
(*    200 |   200     |   19900     | 200            *)
(*                                                   *)
(*  storage grows as n (n - 1) / 2, quadratic.       *)
(*  flip grows as n, linear.                         *)
(*  ri_remaining stays None throughout; the          *)
(*  framework never sees a "done" state.             *)
(* ================================================ *)

Example ri_1_cost :
  let e := ri_walk 1 ri_start in
  (ri_prec e, ri_stor e, ri_flip e) = (1, 0, 1).
Proof. reflexivity. Qed.

Example ri_2_cost :
  let e := ri_walk 2 ri_start in
  (ri_prec e, ri_stor e, ri_flip e) = (2, 1, 2).
Proof. reflexivity. Qed.

Example ri_5_cost :
  let e := ri_walk 5 ri_start in
  (ri_prec e, ri_stor e, ri_flip e) = (5, 10, 5).
Proof. reflexivity. Qed.

Example ri_10_cost :
  let e := ri_walk 10 ri_start in
  (ri_prec e, ri_stor e, ri_flip e) = (10, 45, 10).
Proof. reflexivity. Qed.

Example ri_50_cost :
  let e := ri_walk 50 ri_start in
  (ri_prec e, ri_stor e, ri_flip e) = (50, 1225, 50).
Proof. reflexivity. Qed.

Example ri_100_cost :
  let e := ri_walk 100 ri_start in
  (ri_prec e, ri_stor e, ri_flip e) = (100, 4950, 100).
Proof. reflexivity. Qed.

Example ri_200_cost :
  let e := ri_walk 200 ri_start in
  (ri_prec e, ri_stor e, ri_flip e) = (200, 19900, 200).
Proof. reflexivity. Qed.

(* ================================================ *)
(*  LINEAR OBSERVABLES                               *)
(*                                                   *)
(*  Precision and flip both grow linearly in the     *)
(*  number of steps. The quadratic closed form for   *)
(*  storage is proved separately in the next         *)
(*  section.                                         *)
(* ================================================ *)

Lemma ri_walk_prec :
  forall n e, ri_prec (ri_walk n e) = ri_prec e + n.
Proof.
  induction n as [|k IH]; intros e; simpl.
  - lia.
  - rewrite IH. simpl. lia.
Qed.

Lemma ri_walk_flip :
  forall n e, ri_flip (ri_walk n e) = ri_flip e + n.
Proof.
  induction n as [|k IH]; intros e; simpl.
  - lia.
  - rewrite IH. simpl. lia.
Qed.

Theorem ri_flip_from_start :
  forall n, ri_flip (ri_walk n ri_start) = n.
Proof.
  intro n. rewrite ri_walk_flip. simpl. reflexivity.
Qed.

(* ================================================ *)
(*  QUADRATIC STORAGE — CLOSED FORM                  *)
(*                                                   *)
(*  2 * storage = n * (n - 1) after n steps from     *)
(*  ri_start. Stated this way to avoid integer       *)
(*  division in the theorem statement.               *)
(* ================================================ *)

Lemma ri_walk_succ :
  forall n e, ri_walk (S n) e = ri_step (ri_walk n e).
Proof.
  induction n as [|k IH]; intros e.
  - reflexivity.
  - exact (IH (ri_step e)).
Qed.

Theorem ri_storage_closed_form :
  forall n, 2 * ri_stor (ri_walk n ri_start) = n * (n - 1).
Proof.
  induction n as [|k IH].
  - reflexivity.
  - assert (Heq : ri_walk (S k) ri_start = ri_step (ri_walk k ri_start))
      by apply ri_walk_succ.
    rewrite Heq.
    unfold ri_step. simpl.
    rewrite (ri_walk_prec k ri_start). simpl.
    nia.
Qed.

(* ================================================ *)
(*  COMPARISON WITH BOUNDED ITERATION                *)
(*                                                   *)
(*  CounterMachine with limit = n pays the same      *)
(*  quadratic storage (n (n-1) / 2) and linear flip  *)
(*  (n) to walk from precision 0 to precision n.     *)
(*  The difference is not the cost curve but the     *)
(*  remaining field:                                 *)
(*                                                   *)
(*    CounterMachine: remaining init = Some n,       *)
(*                    remaining final = Some 0.      *)
(*    RealIterator : remaining init = None,          *)
(*                    remaining final = None.        *)
(*                                                   *)
(*  Both pay the same storage to walk n steps. Only  *)
(*  the Counter reaches a "done" state, since it     *)
(*  has explicitly committed to a finite limit. The  *)
(*  RealIterator stays in None throughout, so        *)
(*  framework-level theorems that require Some 0     *)
(*  (like sat_flip_exponential) do not apply here.   *)
(*                                                   *)
(*  Trade-off of refusing to bound the iteration:    *)
(*    - same instantaneous cost curve                *)
(*    - no handle on termination                     *)
(*    - no framework result can bind the iterator    *)
(*      to a finite total                            *)
(* ================================================ *)
