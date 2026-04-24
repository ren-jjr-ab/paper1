(* ================================================ *)
(*  FrameworkHalting                                 *)
(*                                                   *)
(*  Constructive halting theorems for SKI.          *)
(*                                                   *)
(*  What we prove here are the theorems that hold   *)
(*  in pure constructive Coq without LEM, without   *)
(*  fuel-based approximations, without any          *)
(*  additional axiom. SKI is Turing-complete so     *)
(*  halting is undecidable in general; therefore    *)
(*  the classical dichotomy                          *)
(*                                                   *)
(*      forall t, halts t \/ diverges t              *)
(*                                                   *)
(*  is not a theorem of this file — a constructive  *)
(*  proof would be a halting decider, which cannot  *)
(*  exist. We do NOT state it with a LEM section    *)
(*  either; the undecidability stays implicit in    *)
(*  the absence of that theorem.                    *)
(*                                                   *)
(*  Likewise, there is no done_preserved_by_interact*)
(*  because SKI's framework interact advances a     *)
(*  normal term t into TApp t b, which can          *)
(*  re-introduce a redex (e.g. TApp (TApp TK TS) TI *)
(*  reduces to TS). Such a preservation theorem is  *)
(*  false of SKI, so it is not stated here.         *)
(* ================================================ *)

Require Import Existence.
Require Import SKI.


Theorem halted_decidable :
  forall t : SKITerm, {halted t} + {~ halted t}.
Proof. exact halted_dec. Qed.

Theorem halted_implies_halts :
  forall t : SKITerm, halted t -> halts t.
Proof.
  intros t H. exists 0. simpl. exact H.
Qed.

Theorem not_halts_and_diverges :
  forall t : SKITerm, halts t -> diverges t -> False.
Proof.
  intros t Hh Hd. unfold diverges in Hd. apply Hd. exact Hh.
Qed.

Lemma reduce_one_halted_fixes :
  forall t : SKITerm, halted t -> reduce_one t = t.
Proof. intros t H. exact H. Qed.

Theorem halted_preserved_under_reduce_n :
  forall (t : SKITerm) (n : nat),
    halted t -> halted (reduce_n n t).
Proof.
  intros t n Hh.
  induction n as [| n' IH]; simpl.
  - exact Hh.
  - rewrite Hh. exact IH.
Qed.
