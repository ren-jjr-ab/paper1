(* ============================================== *)
(*  FieldAsWitnessed                                *)
(*                                                  *)
(*  Functor: DecEqFieldSig -> WitnessedSig.       *)
(*                                                  *)
(*  Entity := Expr × observer_tag.                 *)
(*  Expr ::= EConst c | EAdd | EMul | ENeg | EInv. *)
(*                                                  *)
(*  EInv extends the ring expression grammar with  *)
(*  a formal inverse. eval delegates to the        *)
(*  field's inv, whose behavior on zero is left    *)
(*  to the field's own convention.                 *)
(* ============================================== *)

Require Import Existence.
Require Import Witnessed.
Require Import Field.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module Make (F : DecEqFieldSig) <: WitnessedSig.

  Inductive Expr : Type :=
  | EConst : F.Carrier -> Expr
  | EAdd   : Expr -> Expr -> Expr
  | EMul   : Expr -> Expr -> Expr
  | ENeg   : Expr -> Expr
  | EInv   : Expr -> Expr.

  Fixpoint eval (e : Expr) : F.Carrier :=
    match e with
    | EConst c  => c
    | EAdd a b  => F.add (eval a) (eval b)
    | EMul a b  => F.mul (eval a) (eval b)
    | ENeg a    => F.neg (eval a)
    | EInv a    => F.inv (eval a)
    end.

  Fixpoint expr_eq_dec (e f : Expr) : {e = f} + {e <> f}.
  Proof.
    decide equality; apply F.carrier_eq_dec.
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
    exists (EConst F.zero, 0%nat), (EConst F.one, 0%nat).
    intro H. inversion H as [H1].
    apply F.one_neq_zero. symmetry. exact H1.
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
