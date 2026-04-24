(* ============================================== *)
(*  SemiringAsWitnessed                             *)
(*                                                  *)
(*  Functor: DecEqCommSemiringSig -> WitnessedSig. *)
(*                                                  *)
(*  Entity := Expr × observer_tag.                 *)
(*  Expr ::= EConst c | EAdd e1 e2 | EMul e1 e2.   *)
(*                                                  *)
(*  Same pattern as RingAsWitnessed but without    *)
(*  the ENeg node — semirings have no additive     *)
(*  inverse.                                        *)
(* ============================================== *)

Require Import Existence.
Require Import Witnessed.
Require Import Semiring.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module Make (S : DecEqCommSemiringSig) <: WitnessedSig.

  Inductive Expr : Type :=
  | EConst : S.Carrier -> Expr
  | EAdd   : Expr -> Expr -> Expr
  | EMul   : Expr -> Expr -> Expr.

  Fixpoint eval (e : Expr) : S.Carrier :=
    match e with
    | EConst c  => c
    | EAdd a b  => S.add (eval a) (eval b)
    | EMul a b  => S.mul (eval a) (eval b)
    end.

  Fixpoint expr_eq_dec (e f : Expr) : {e = f} + {e <> f}.
  Proof.
    decide equality; apply S.carrier_eq_dec.
  Defined.

  Definition Entity : Type := (Expr * nat)%type.

  Definition entity_eq_dec :
    forall a b : Entity, {a = b} + {a <> b}.
  Proof.
    intros [ea ta] [eb tb].
    destruct (expr_eq_dec ea eb) as [He | He].
    - destruct (Nat.eq_dec ta tb) as [Ht | Ht].
      + left. subst. reflexivity.
      + right. intro H. inversion H. contradiction.
    - right. intro H. inversion H. contradiction.
  Defined.

  Definition interact (a b : Entity) : Entity :=
    match entity_eq_dec a b with
    | left _  => a
    | right _ => (fst a, S (Nat.max (snd a) (snd b)))
    end.

  Definition collapse (a b : Entity) : Prop :=
    fst a <> fst b /\ eval (fst a) = eval (fst b).

  Definition witness_time (a : Entity) : nat := snd a.

  (* --- AXIOM PROOFS --- *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intro a. unfold interact.
    destruct (entity_eq_dec a a) as [_ | H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
  Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (EConst S.zero, 0%nat), (EAdd (EConst S.zero) (EConst S.zero), 0%nat).
    intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intro a. exists (fst a, S (snd a)).
    unfold interact.
    destruct (entity_eq_dec a (fst a, S (snd a))) as [Heq | Hne].
    - apply (f_equal snd) in Heq. simpl in Heq. lia.
    - intro H. apply (f_equal snd) in H. simpl in H. lia.
  Qed.

  Theorem interaction_cannot_witness_collapse :
    forall a b : Entity, collapse a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof.
    intros a b [Hstate Hval] c.
    unfold interact.
    destruct (entity_eq_dec a c) as [Hac | Hac];
    destruct (entity_eq_dec b c) as [Hbc | Hbc].
    - exfalso. apply Hstate. rewrite Hac, Hbc. reflexivity.
    - subst c. intro H. apply Hstate.
      apply (f_equal fst) in H. simpl in H. exact H.
    - subst c. intro H. apply Hstate.
      apply (f_equal fst) in H. simpl in H. exact H.
    - intro H. apply Hstate.
      apply (f_equal fst) in H. simpl in H. exact H.
  Qed.

  Theorem witness_advances_on_nonself :
    forall (a c : Entity),
      interact a c <> a ->
      witness_time (interact a c) > witness_time a.
  Proof.
    intros a c Hne. unfold interact, witness_time in *.
    destruct (entity_eq_dec a c) as [_ | _].
    - exfalso. apply Hne. reflexivity.
    - simpl. lia.
  Qed.

End Make.
