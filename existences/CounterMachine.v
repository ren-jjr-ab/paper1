(* ================================================ *)
(*  CounterMachine.v                                 *)
(*                                                   *)
(*  The simplest possible Iterable instance: a       *)
(*  counter that must tick from 0 to a declared      *)
(*  limit, one step per interaction, no shortcuts.   *)
(*                                                   *)
(*  Purpose: exhibit a concrete model where the      *)
(*  framework forces an exact step count structurally*)
(*  rather than by convention. For limit = 2^k,      *)
(*  every complete chain has flip_cost >= 2^k by     *)
(*  sat_flip_exponential from SATLowerBound — and    *)
(*  here the 2^k is fixed by the data definition     *)
(*  itself, leaving no room to shortcut it.          *)
(*                                                   *)
(*  This is not SAT. A SAT entity can claim that its *)
(*  remaining work is small; the counter cannot. The *)
(*  only honest reading of (count, limit) is         *)
(*  remaining = limit - count.                       *)
(*                                                   *)
(*  Structure follows HashModel — Inductive with     *)
(*  Normal / Frozen constructors.                    *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Eqdep_dec.

Require Import Existence.
Require Import Computable.
Require Import Iterable.

(* ================================================ *)
(*  RAW ENTITY                                       *)
(* ================================================ *)

(* CMNormal dim count limit storage flip
     dim     — current category
     count   — ticks taken so far
     limit   — target count
     storage — accumulated storage cost
     flip    — accumulated flip cost
   CMFrozen dim storage flip inner   — frozen wrapper *)
Inductive CMEnt : Type :=
  | CMNormal  : nat -> nat -> nat -> nat -> nat -> CMEnt
  | CMFrozen  : nat -> nat -> nat -> CMEnt -> CMEnt.

Fixpoint cm_dim (x : CMEnt) : nat :=
  match x with
  | CMNormal d _ _ _ _ => d
  | CMFrozen d _ _ _   => d
  end.

Fixpoint cm_info (x : CMEnt) : nat :=
  match x with
  | CMNormal _ c l _ _ => l - c
  | CMFrozen _ _ _ e   => cm_info e
  end.

Fixpoint cm_stor (x : CMEnt) : nat :=
  match x with
  | CMNormal _ _ _ s _ => s
  | CMFrozen _ s _ _   => s
  end.

Fixpoint cm_flip (x : CMEnt) : nat :=
  match x with
  | CMNormal _ _ _ _ f => f
  | CMFrozen _ _ f _   => f
  end.

(* Frozen entities are "done" from the iterator
   perspective — no further iteration is possible. *)
Fixpoint cm_remaining_nat (x : CMEnt) : nat :=
  match x with
  | CMNormal _ c l _ _ => l - c
  | CMFrozen _ _ _ _   => 0
  end.

Definition dim_as_entity (d : nat) : CMEnt := CMNormal d 0 0 0 0.

(* ================================================ *)
(*  ONE TICK PER INTERACTION                         *)
(* ================================================ *)

(* cm_step advances count by exactly 1 (clipped at
   limit), pays info_size of source to storage, pays
   1 to flip, and relabels category to target. One
   tick per step regardless of target mirrors
   HashModel's h_step. *)
Definition cm_step (e : CMEnt) (d : nat) : CMEnt :=
  match e with
  | CMNormal _ c l s f =>
      let new_c := if Nat.ltb c l then S c else c in
      CMNormal d new_c l (s + (l - c)) (f + 1)
  | CMFrozen _ s f inner =>
      CMFrozen d (s + cm_info inner) (f + 1) inner
  end.

Fixpoint cm_project_at (x : CMEnt) (d : nat) : CMEnt :=
  match x with
  | CMNormal src_d _ _ _ _ =>
      if Nat.eq_dec src_d d then x else cm_step x d
  | CMFrozen src_d _ _ _ =>
      if Nat.eq_dec src_d d then x else cm_step x d
  end.

Lemma cm_project_at_dim : forall x d, cm_dim (cm_project_at x d) = d.
Proof.
  induction x as [d0 c l s f | d0 s f inner IH]; intro d; simpl.
  - destruct (Nat.eq_dec d0 d); simpl; congruence.
  - destruct (Nat.eq_dec d0 d); simpl; congruence.
Qed.

Lemma cm_project_at_self : forall x, cm_project_at x (cm_dim x) = x.
Proof.
  induction x as [d c l s f | d s f inner IH]; simpl.
  - destruct (Nat.eq_dec d d); [reflexivity | contradiction].
  - destruct (Nat.eq_dec d d); [reflexivity | contradiction].
Qed.

(* ================================================ *)
(*  FREEZE (instance-internal)                       *)
(* ================================================ *)

Definition cm_freeze (e : CMEnt) : CMEnt := CMFrozen (cm_dim e) 0 0 e.

Lemma cm_freeze_injective :
  forall a b, cm_freeze a = cm_freeze b -> a = b.
Proof. intros a b H. unfold cm_freeze in H. inversion H. reflexivity. Qed.

(* ================================================ *)
(*  INSTANCE                                         *)
(* ================================================ *)

Module CounterMachine <: IterableComputableSig.

  Definition Entity : Type := CMEnt.

  Definition interact (a b : Entity) : Entity :=
    cm_project_at a (cm_dim b).

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof. intros. unfold interact. apply cm_project_at_self. Qed.

  Fixpoint cm_eq_dec (a b : CMEnt) : {a = b} + {a <> b}.
  Proof.
    refine (
      match a, b with
      | CMNormal d1 c1 l1 s1 f1, CMNormal d2 c2 l2 s2 f2 => _
      | CMFrozen d1 s1 f1 e1, CMFrozen d2 s2 f2 e2 => _
      | _, _ => right _
      end); try (intro H; inversion H).
    - destruct (Nat.eq_dec d1 d2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec c1 c2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec l1 l2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec s1 s2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec f1 f2); [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
    - destruct (Nat.eq_dec d1 d2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec s1 s2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec f1 f2); [| right; intro H; inversion H; contradiction].
      destruct (cm_eq_dec e1 e2); [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
  Defined.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply cm_eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (CMNormal 0 0 0 0 0), (CMNormal 1 0 0 0 0).
    intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intros a. exists (dim_as_entity (S (cm_dim a))).
    unfold interact, dim_as_entity. simpl cm_dim.
    intro H.
    assert (Hd : cm_dim (cm_project_at a (S (cm_dim a))) = S (cm_dim a)).
    { apply cm_project_at_dim. }
    rewrite H in Hd. lia.
  Qed.

  Definition convention_eq : Entity -> Entity -> Prop :=
    fun _ _ => False.

  Theorem convention_not_derivable :
    forall a b, convention_eq a b ->
    forall c, interact a c <> interact b c.
  Proof. intros a b H. exfalso. exact H. Qed.

  (* ---- Computable layer ---- *)

  Definition info_size (e : Entity) : nat := cm_info e.
  Definition storage_cost (e : Entity) : nat := cm_stor e.
  Definition flip_cost (e : Entity) : nat := cm_flip e.

  (* Direct computation: for a non-identity cm_step on either
     a Normal or a Frozen entity, storage pays info_size exactly
     and flip pays exactly 1 (info never grows here). *)
  Lemma cm_step_normal_stor_flip :
    forall d0 c l s f d,
      cm_stor (cm_step (CMNormal d0 c l s f) d) =
        cm_stor (CMNormal d0 c l s f) + cm_info (CMNormal d0 c l s f) /\
      cm_flip (cm_step (CMNormal d0 c l s f) d) =
        cm_flip (CMNormal d0 c l s f) + 1 /\
      cm_info (cm_step (CMNormal d0 c l s f) d) <=
        cm_info (CMNormal d0 c l s f).
  Proof.
    intros. unfold cm_step.
    destruct (c <? l) eqn:Hltb.
    - apply Nat.ltb_lt in Hltb. simpl. repeat split; try reflexivity; lia.
    - apply Nat.ltb_ge in Hltb. simpl. repeat split; try reflexivity; lia.
  Qed.

  Lemma cm_step_frozen_stor_flip :
    forall d0 s f inner d,
      cm_stor (cm_step (CMFrozen d0 s f inner) d) =
        cm_stor (CMFrozen d0 s f inner) + cm_info (CMFrozen d0 s f inner) /\
      cm_flip (cm_step (CMFrozen d0 s f inner) d) =
        cm_flip (CMFrozen d0 s f inner) + 1 /\
      cm_info (cm_step (CMFrozen d0 s f inner) d) <=
        cm_info (CMFrozen d0 s f inner).
  Proof.
    intros. simpl. repeat split; try reflexivity; lia.
  Qed.

  Lemma cm_project_at_normal_non_id :
    forall d0 c l s f d,
      d0 <> d ->
      cm_project_at (CMNormal d0 c l s f) d = cm_step (CMNormal d0 c l s f) d.
  Proof.
    intros. simpl. destruct (Nat.eq_dec d0 d); [contradiction | reflexivity].
  Qed.

  Lemma cm_project_at_frozen_non_id :
    forall d0 s f inner d,
      d0 <> d ->
      cm_project_at (CMFrozen d0 s f inner) d = cm_step (CMFrozen d0 s f inner) d.
  Proof.
    intros. simpl. destruct (Nat.eq_dec d0 d); [contradiction | reflexivity].
  Qed.

  Lemma cm_project_at_change :
    forall x d,
      cm_project_at x d <> x ->
      cm_stor (cm_project_at x d) = cm_stor x + cm_info x /\
      cm_flip (cm_project_at x d) =
        cm_flip x + Nat.max 1 (cm_info (cm_project_at x d) - cm_info x).
  Proof.
    induction x as [d0 c l s f | d0 s f inner IH]; intros d Hne.
    - assert (Hd : d0 <> d).
      { intro Heq. apply Hne. simpl. destruct (Nat.eq_dec d0 d); [reflexivity | contradiction]. }
      rewrite (cm_project_at_normal_non_id d0 c l s f d Hd).
      pose proof (cm_step_normal_stor_flip d0 c l s f d) as [Hs [Hf Hle]].
      split; [exact Hs |].
      rewrite Hf. f_equal.
      assert (He : cm_info (cm_step (CMNormal d0 c l s f) d) -
                   cm_info (CMNormal d0 c l s f) = 0) by lia.
      rewrite He. reflexivity.
    - assert (Hd : d0 <> d).
      { intro Heq. apply Hne. simpl. destruct (Nat.eq_dec d0 d); [reflexivity | contradiction]. }
      rewrite (cm_project_at_frozen_non_id d0 s f inner d Hd).
      pose proof (cm_step_frozen_stor_flip d0 s f inner d) as [Hs [Hf Hle]].
      split; [exact Hs |].
      rewrite Hf. f_equal.
      assert (He : cm_info (cm_step (CMFrozen d0 s f inner) d) -
                   cm_info (CMFrozen d0 s f inner) = 0) by lia.
      rewrite He. reflexivity.
  Qed.

  Theorem storage_pays_capacity :
    forall (a c : Entity),
      interact a c <> a ->
      storage_cost (interact a c) = storage_cost a + info_size a.
  Proof.
    intros a c Hne. unfold storage_cost, info_size, interact.
    apply (proj1 (cm_project_at_change a (cm_dim c) Hne)).
  Qed.

  Theorem flip_pays_work :
    forall (a c : Entity),
      interact a c <> a ->
      flip_cost (interact a c) =
        flip_cost a + Nat.max 1 (info_size (interact a c) - info_size a).
  Proof.
    intros a c Hne. unfold flip_cost, info_size, interact.
    apply (proj2 (cm_project_at_change a (cm_dim c) Hne)).
  Qed.

  (* ---- Iterable layer ---- *)

  Definition remaining (e : Entity) : option nat := Some (cm_remaining_nat e).

  Lemma cm_remaining_after_step :
    forall x d,
      cm_project_at x d <> x ->
      cm_remaining_nat (cm_project_at x d) = cm_remaining_nat x - 1.
  Proof.
    induction x as [d0 c l s f | d0 s f inner IH]; intros d Hne.
    - assert (Hd : d0 <> d).
      { intro Heq. apply Hne. simpl. destruct (Nat.eq_dec d0 d); [reflexivity | contradiction]. }
      rewrite (cm_project_at_normal_non_id d0 c l s f d Hd).
      unfold cm_step, cm_remaining_nat.
      destruct (c <? l) eqn:Hltb.
      + apply Nat.ltb_lt in Hltb. lia.
      + apply Nat.ltb_ge in Hltb. lia.
    - assert (Hd : d0 <> d).
      { intro Heq. apply Hne. simpl. destruct (Nat.eq_dec d0 d); [reflexivity | contradiction]. }
      rewrite (cm_project_at_frozen_non_id d0 s f inner d Hd).
      simpl. lia.
  Qed.

  Theorem project_decrements_remaining :
    forall (a c : Entity) (n : nat),
      interact a c <> a ->
      remaining a = Some n ->
      remaining (interact a c) = Some (n - 1).
  Proof.
    intros a c n Hne Hrem.
    unfold remaining, interact in *.
    pose proof (cm_remaining_after_step a (cm_dim c) Hne) as Hdec.
    inversion Hrem as [Heq]. rewrite Hdec. rewrite Heq. reflexivity.
  Qed.

  Theorem done_stays_done :
    forall (a c : Entity),
      remaining a = Some 0 ->
      remaining (interact a c) = Some 0.
  Proof.
    intros a c Hrem.
    unfold remaining, interact in *.
    assert (Heq : cm_remaining_nat a = 0).
    { injection Hrem. intro. exact H. }
    f_equal.
    destruct (cm_eq_dec (cm_project_at a (cm_dim c)) a) as [He | He].
    - rewrite He. exact Heq.
    - pose proof (cm_remaining_after_step a (cm_dim c) He) as Hdec.
      rewrite Hdec, Heq. reflexivity.
  Qed.

End CounterMachine.

(* ================================================ *)
(*  INSTANCE-INTERNAL FREEZE                         *)
(* ================================================ *)

Module CMCT := ComputableExistenceTheory CounterMachine.
Import CounterMachine CMCT.

Definition freeze (e : Entity) : Entity := cm_freeze e.

Definition is_frozen (a : Entity) : Prop :=
  exists b, a = freeze b.

Theorem freeze_injective :
  forall a b, freeze a = freeze b -> a = b.
Proof. exact cm_freeze_injective. Qed.

Theorem freeze_preserves_existence :
  forall (a b c : Entity),
    is_frozen a ->
    is_frozen b ->
    interact a c = interact b c ->
    a = b.
Proof.
  intros a b c Hfa Hfb Hproj.
  destruct Hfa as [a' Ha]. destruct Hfb as [b' Hb].
  unfold freeze, cm_freeze in Ha, Hb. subst a b.
  unfold interact in Hproj. simpl in Hproj.
  destruct (Nat.eq_dec (cm_dim a') (cm_dim c)) as [Hea | Hea];
    destruct (Nat.eq_dec (cm_dim b') (cm_dim c)) as [Heb | Heb];
    inversion Hproj; try congruence.
Qed.
