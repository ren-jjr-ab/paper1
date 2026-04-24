(* ============================================== *)
(*  RingAsExistence                                 *)
(*                                                  *)
(*  Functor: DecEqCommRingSig -> ExistenceSig.     *)
(*                                                  *)
(*  Entity := Expr over (EConst | EAdd | EMul |    *)
(*                       ENeg).                     *)
(*                                                  *)
(*  reduce_one: leftmost-outermost one-step          *)
(*  reduction. EAdd/EMul of two EConsts contract;   *)
(*  ENeg of an EConst contracts via R.neg.          *)
(*                                                  *)
(*  interact a b :                                   *)
(*    a = b                 → a (self)              *)
(*    a reducible           → reduce_one a          *)
(*    a normal (EConst _)   → EAdd a b              *)
(*                                                  *)
(*  collapse := False. DecEqCommRingSig does not    *)
(*  assume one <> zero, so existence uses           *)
(*  structurally distinct exprs (EConst R.zero vs   *)
(*  EAdd (EConst R.zero) (EConst R.zero)) rather    *)
(*  than a value-level distinctness.                *)
(*                                                  *)
(*  eval is kept as an internal helper; reduction   *)
(*  preserves eval.                                  *)
(* ============================================== *)

Require Import Existence.
Require Import Ring.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module Make (R : DecEqCommRingSig) <: ExistenceSig.

  Inductive Expr : Type :=
  | EConst : R.Carrier -> Expr
  | EAdd   : Expr -> Expr -> Expr
  | EMul   : Expr -> Expr -> Expr
  | ENeg   : Expr -> Expr.

  Definition Entity : Type := Expr.

  Definition entity_eq_dec :
    forall a b : Entity, {a = b} + {a <> b}.
  Proof.
    decide equality; apply R.carrier_eq_dec.
  Defined.

  (* --- internal helpers --- *)

  Fixpoint size (e : Expr) : nat :=
    match e with
    | EConst _  => 1
    | EAdd a b  => S (size a + size b)
    | EMul a b  => S (size a + size b)
    | ENeg a    => S (size a)
    end.

  Lemma size_pos : forall e, size e >= 1.
  Proof. destruct e; simpl; lia. Qed.

  Fixpoint eval (e : Expr) : R.Carrier :=
    match e with
    | EConst n  => n
    | EAdd a b  => R.add (eval a) (eval b)
    | EMul a b  => R.mul (eval a) (eval b)
    | ENeg a    => R.neg (eval a)
    end.

  Fixpoint reduce_one (e : Expr) : Expr :=
    match e with
    | EConst _ => e
    | EAdd (EConst a) (EConst b) => EConst (R.add a b)
    | EAdd a b =>
        match a with
        | EConst _ => EAdd a (reduce_one b)
        | _        => EAdd (reduce_one a) b
        end
    | EMul (EConst a) (EConst b) => EConst (R.mul a b)
    | EMul a b =>
        match a with
        | EConst _ => EMul a (reduce_one b)
        | _        => EMul (reduce_one a) b
        end
    | ENeg (EConst a) => EConst (R.neg a)
    | ENeg a          => ENeg (reduce_one a)
    end.

  Lemma reduce_one_preserves_eval :
    forall e, eval (reduce_one e) = eval e.
  Proof.
    induction e; simpl.
    - reflexivity.
    - destruct e1; simpl in *.
      + destruct e2; simpl in *; try reflexivity.
        * rewrite IHe2. reflexivity.
        * rewrite IHe2. reflexivity.
        * rewrite IHe2. reflexivity.
      + rewrite IHe1. reflexivity.
      + rewrite IHe1. reflexivity.
      + rewrite IHe1. reflexivity.
    - destruct e1; simpl in *.
      + destruct e2; simpl in *; try reflexivity.
        * rewrite IHe2. reflexivity.
        * rewrite IHe2. reflexivity.
        * rewrite IHe2. reflexivity.
      + rewrite IHe1. reflexivity.
      + rewrite IHe1. reflexivity.
      + rewrite IHe1. reflexivity.
    - destruct e; simpl in *; try reflexivity.
      + rewrite IHe. reflexivity.
      + rewrite IHe. reflexivity.
      + rewrite IHe. reflexivity.
  Qed.

  (* --- ExistenceSig fields --- *)

  Definition interact (a b : Entity) : Entity :=
    match entity_eq_dec a b with
    | left _  => a
    | right _ =>
        let a' := reduce_one a in
        match entity_eq_dec a' a with
        | left _  => EAdd a b
        | right _ => a'
        end
    end.

  Definition collapse (_ _ : Entity) : Prop := False.

  (* --- Axioms --- *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intro a. unfold interact.
    destruct (entity_eq_dec a a) as [_ | H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
  Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (EConst R.zero), (EAdd (EConst R.zero) (EConst R.zero)).
    intro H. inversion H.
  Qed.

  Lemma eadd_left_not_self :
    forall a b : Expr, EAdd a b <> a.
  Proof.
    intros a b H.
    assert (Hsize : size (EAdd a b) = size a) by (rewrite H; reflexivity).
    simpl in Hsize.
    pose proof (size_pos b). lia.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intro a.
    exists (EAdd a a).
    unfold interact.
    destruct (entity_eq_dec a (EAdd a a)) as [Heq | Hne].
    - exfalso. apply (eadd_left_not_self a a). symmetry. exact Heq.
    - destruct (entity_eq_dec (reduce_one a) a) as [Hlanded | Hred].
      + apply (eadd_left_not_self a (EAdd a a)).
      + exact Hred.
  Qed.

  Theorem interaction_cannot_witness_collapse :
    forall a b : Entity, collapse a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof. intros a b H. exfalso. exact H. Qed.

End Make.
