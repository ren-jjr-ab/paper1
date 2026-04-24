(* ============================================== *)
(*  SKI — combinator calculus as an Existence-only *)
(*        instance.                                 *)
(*                                                  *)
(*  Entity := SKITerm.                              *)
(*  β-rules:                                        *)
(*    I x       → x                                 *)
(*    K x y     → x                                 *)
(*    S x y z   → (x z) (y z)                       *)
(*                                                  *)
(*  reduce_one: leftmost-outermost single step;     *)
(*              self if no redex.                   *)
(*                                                  *)
(*  interact a b :                                  *)
(*    a = b                 → a (self)              *)
(*    a reducible           → reduce_one a          *)
(*    a normal (no redex)   → TApp a b              *)
(*                                                  *)
(*  Halting is read off entity structure: a term    *)
(*  is normal iff no redex. No external iteration   *)
(*  counter, no Materialized layer — Existence      *)
(*  alone.                                          *)
(*                                                  *)
(*  collapse := False. SKI does not carry a         *)
(*  non-trivial eternal-parallel relation at this   *)
(*  layer: every pair of distinct terms is either   *)
(*  separated by reduction dynamics or merges via   *)
(*  the App-merge branch.                           *)
(* ============================================== *)

Require Import Existence.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Inductive SKITerm : Type :=
  | TS   : SKITerm
  | TK   : SKITerm
  | TI   : SKITerm
  | TApp : SKITerm -> SKITerm -> SKITerm.

Fixpoint term_size (t : SKITerm) : nat :=
  match t with
  | TS | TK | TI => 1
  | TApp l r     => S (term_size l + term_size r)
  end.

Lemma term_size_pos : forall t, term_size t >= 1.
Proof. destruct t; simpl; lia. Qed.

Definition ski_eq_dec : forall a b : SKITerm, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Fixpoint reduce_one (t : SKITerm) : SKITerm :=
  match t with
  | TApp (TApp (TApp TS x) y) z => TApp (TApp x z) (TApp y z)
  | TApp (TApp TK x) _          => x
  | TApp TI x                   => x
  | TApp l r                    =>
      let l' := reduce_one l in
      if ski_eq_dec l' l then
        let r' := reduce_one r in
        if ski_eq_dec r' r then t else TApp l r'
      else TApp l' r
  | _ => t
  end.

(* ============================================== *)
(*  MODULE SKI : ExistenceSig                      *)
(* ============================================== *)

Module SKI <: ExistenceSig.

  Definition Entity : Type := SKITerm.

  Definition entity_eq_dec : forall a b : Entity, {a = b} + {a <> b} := ski_eq_dec.

  Definition interact (a b : Entity) : Entity :=
    match entity_eq_dec a b with
    | left  _ => a
    | right _ =>
        let a' := reduce_one a in
        match entity_eq_dec a' a with
        | left  _ => TApp a b
        | right _ => a'
        end
    end.

  Definition collapse (_ _ : Entity) : Prop := False.

  (* ------------------------------------------- *)
  (*  AXIOMS                                     *)
  (* ------------------------------------------- *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intro a. unfold interact.
    destruct (entity_eq_dec a a) as [_ | H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
  Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof. exists TS, TK. intro H. inversion H. Qed.

  Lemma app_left_not_self :
    forall a b : SKITerm, TApp a b <> a.
  Proof.
    intros a b H.
    assert (Hsize : term_size (TApp a b) = term_size a) by (rewrite H; reflexivity).
    simpl in Hsize.
    pose proof (term_size_pos b). lia.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intro a.
    exists (TApp a a).
    unfold interact.
    destruct (entity_eq_dec a (TApp a a)) as [Heq | Hne].
    - exfalso. apply (app_left_not_self a a). symmetry. exact Heq.
    - destruct (entity_eq_dec (reduce_one a) a) as [Hnorm | Hred].
      + (* normal form: result is TApp a (TApp a a) ≠ a *)
        apply (app_left_not_self a (TApp a a)).
      + (* reducible: reduce_one a ≠ a *)
        exact Hred.
  Qed.

  Theorem interaction_cannot_witness_collapse :
    forall a b : Entity, collapse a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof. intros a b H. exfalso. exact H. Qed.

End SKI.


(* ============================================== *)
(*  INTERNAL HALTING — Prop-level, no fuel         *)
(*                                                  *)
(*  halted t : term is in normal form (reduce_one  *)
(*             fixes it). Decidable via syntactic  *)
(*             term equality.                       *)
(*                                                  *)
(*  halts t  : there exists some number of         *)
(*             reduction steps after which t       *)
(*             reaches a halted state.             *)
(*                                                  *)
(*  diverges t : no such step count exists.        *)
(*                                                  *)
(*  The generic dichotomy  halts t \/ diverges t   *)
(*  is LEM on halts t and is NOT provable here —    *)
(*  SKI is Turing-complete, so a constructive      *)
(*  decider for halting would solve the halting    *)
(*  problem. We do not introduce LEM, do not use   *)
(*  a fuel approximation, and do not state the     *)
(*  classical disjunction. The constructive        *)
(*  theorems about halted and halts that do hold   *)
(*  are proved in Results/Bizarre/FrameworkHalting.*)
(* ============================================== *)

Definition halted (t : SKITerm) : Prop := reduce_one t = t.

Fixpoint reduce_n (n : nat) (t : SKITerm) : SKITerm :=
  match n with
  | 0   => t
  | S k => reduce_n k (reduce_one t)
  end.

Definition halts (t : SKITerm) : Prop :=
  exists n : nat, halted (reduce_n n t).

Definition diverges (t : SKITerm) : Prop := ~ halts t.

Lemma halted_dec : forall t, {halted t} + {~ halted t}.
Proof. intro t. unfold halted. apply ski_eq_dec. Defined.

Example halted_S : halted TS.
Proof. reflexivity. Qed.

Example halted_K : halted TK.
Proof. reflexivity. Qed.

Example halted_I : halted TI.
Proof. reflexivity. Qed.

Example halts_I_applied_S : halts (TApp TI TS).
Proof. exists 1. unfold halts, reduce_n, halted. reflexivity. Qed.

Example reducible_I_applied :
  reduce_one (TApp TI TS) = TS.
Proof. reflexivity. Qed.

Example reducible_K_applied :
  reduce_one (TApp (TApp TK TS) TK) = TS.
Proof. reflexivity. Qed.

Example reducible_S_applied :
  reduce_one (TApp (TApp (TApp TS TK) TI) TK) = TApp (TApp TK TK) (TApp TI TK).
Proof. reflexivity. Qed.
