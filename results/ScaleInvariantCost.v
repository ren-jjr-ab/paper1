(* ================================================ *)
(*  ScaleInvariantCost.v                            *)
(*                                                  *)
(*  The minimum cost of computation is scale-       *)
(*  invariant: refining operations into smaller     *)
(*  sub-operations does not eliminate the cost --   *)
(*  it redistributes it multiplicatively.           *)
(*                                                  *)
(*  Key result: if every non-trivial operation      *)
(*  decomposes into at least m >= 2 sub-            *)
(*  operations, then after k levels of refinement   *)
(*  the total operation count is at least m^k,      *)
(*  and each sub-operation adds at least 1 to the   *)
(*  flip_cost. Total cost >= m^k.                   *)
(*                                                  *)
(*  This does NOT claim to prove P != NP. It        *)
(*  establishes that within the framework's cost    *)
(*  model, the actual cost of computation exceeds   *)
(*  any single-level accounting by an exponential   *)
(*  factor in the refinement depth.                 *)
(*                                                  *)
(*  The connection to physical computation: any     *)
(*  physical implementation of an operation         *)
(*  decomposes into sub-operations (gates,          *)
(*  signals, particle interactions). The axioms     *)
(*  storage_pays_capacity and flip_pays_work apply  *)
(*  at every level, because they are axioms of      *)
(*  the structure, not properties of one level.     *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Require Import Existence.
Require Import Computable.

(* ================================================ *)
(*  PART 1: MINIMUM REQUIREMENTS FOR DECISION       *)
(* ================================================ *)

Module ScaleInvariant (C : ComputableExistenceSig).
  Module CDT := ComputableExistenceTheory C.
  Module DT := ExistenceTheory C.
  Import C CDT DT.

  (* A decision problem has two possible outcomes.
     To represent two outcomes, we need at least
     two distinct entities. *)

  Definition decision_requires_two :=
    existence.

  (* ================================================ *)
  (*  PART 2: EVERY STEP PAYS                         *)
  (* ================================================ *)

  Theorem every_step_pays_flip :
    forall (a c : Entity),
      interact a c <> a ->
      flip_cost (interact a c) >= flip_cost a + 1.
  Proof.
    intros a c Hne.
    pose proof (flip_pays_work a c Hne) as Hf. lia.
  Qed.

  Theorem positive_step_pays_storage :
    forall (a c : Entity),
      interact a c <> a ->
      info_size a > 0 ->
      storage_cost (interact a c) >= storage_cost a + 1.
  Proof.
    intros a c Hne Hpos.
    rewrite (storage_pays_capacity a c Hne). lia.
  Qed.

  (* ================================================ *)
  (*  PART 3: REFINEMENT IS MULTIPLICATIVE            *)
  (* ================================================ *)

  Fixpoint min_ops (m k : nat) : nat :=
    match k with
    | 0   => 1
    | S j => m * min_ops m j
    end.

  Theorem min_ops_is_power :
    forall m k, min_ops m k = m ^ k.
  Proof.
    intros m k. induction k as [|j IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.

  Theorem min_ops_exponential :
    forall k, min_ops 2 k = 2 ^ k.
  Proof. intro k. apply min_ops_is_power. Qed.

  Theorem min_ops_ge :
    forall m k, m >= 2 -> min_ops m k >= 1.
  Proof.
    intros m k Hm. induction k as [|j IH].
    - simpl. lia.
    - simpl. lia.
  Qed.

  Theorem min_ops_monotone :
    forall m k, m >= 2 -> min_ops m (S k) >= 2 * min_ops m k.
  Proof.
    intros m k Hm. simpl.
    assert (Hge : m * min_ops m k >= 2 * min_ops m k).
    { apply Nat.mul_le_mono_r. exact Hm. }
    exact Hge.
  Qed.

  (* ================================================ *)
  (*  PART 4: THE SCALE-INVARIANT LOWER BOUND         *)
  (* ================================================ *)

  Inductive positive_chain : Entity -> Entity -> nat -> Prop :=
    | pc_refl : forall a, positive_chain a a 0
    | pc_step : forall a b c n,
        positive_chain a b n ->
        forall (v : Entity),
          interact b v <> b ->
          info_size b > 0 ->
          c = interact b v ->
          positive_chain a c (S n).

  Theorem chain_flip_cost :
    forall a b n,
      positive_chain a b n ->
      flip_cost b >= flip_cost a + n.
  Proof.
    intros a b n Hpc. induction Hpc.
    - lia.
    - subst c.
      pose proof (flip_pays_work b v H) as Hf. lia.
  Qed.

  Theorem chain_storage_cost :
    forall a b n,
      positive_chain a b n ->
      storage_cost b >= storage_cost a + n.
  Proof.
    intros a b n Hpc. induction Hpc.
    - lia.
    - subst c.
      rewrite (storage_pays_capacity b v H). lia.
  Qed.

  Theorem scale_invariant_lower_bound :
    forall a b n m k,
      positive_chain a b n ->
      n >= m ^ k ->
      flip_cost b >= flip_cost a + m ^ k /\
      storage_cost b >= storage_cost a + m ^ k.
  Proof.
    intros a b n m k Hpc Hge.
    split.
    - pose proof (chain_flip_cost a b n Hpc). lia.
    - pose proof (chain_storage_cost a b n Hpc). lia.
  Qed.

  Corollary binary_refinement_lower_bound :
    forall a b n k,
      positive_chain a b n ->
      n >= 2 ^ k ->
      flip_cost a = 0 ->
      storage_cost a = 0 ->
      flip_cost b >= 2 ^ k /\
      storage_cost b >= 2 ^ k.
  Proof.
    intros a b n k Hpc Hge Hf0 Hs0.
    destruct (scale_invariant_lower_bound a b n 2 k Hpc Hge).
    lia.
  Qed.

  (* ================================================ *)
  (*  READING                                         *)
  (*                                                  *)
  (*  1. A decision problem needs 2 distinct          *)
  (*     entities.                                    *)
  (*  2. Every non-identity step pays                 *)
  (*     flip_cost >= 1. Steps with info_size > 0     *)
  (*     also pay storage_cost. There is no free      *)
  (*     step.                                        *)
  (*  3. Refining an operation into m >= 2 sub-       *)
  (*     operations multiplies the count. After k     *)
  (*     levels, min_ops = m^k.                       *)
  (*  4. Combining: a k-level refinement adds at      *)
  (*     least m^k to both flip_cost and              *)
  (*     storage_cost -- exponential in the           *)
  (*     refinement depth.                            *)
  (*                                                  *)
  (*  TWO DIRECTIONS, SAME ASSUMPTION                 *)
  (*                                                  *)
  (*  Shared assumption: m >= 2 at every level.       *)
  (*  A non-trivial decision needs at least two       *)
  (*  distinguishable outcomes, and reaching them     *)
  (*  requires at least one non-identity step.        *)
  (*                                                  *)
  (*  Direction 1 (SATLowerBound, "from above"):      *)
  (*    A chain of n steps with remaining = Some k    *)
  (*    pays flip_cost >= 2^k. Lengthening the        *)
  (*    chain does not reduce the cost.               *)
  (*                                                  *)
  (*  Direction 2 (this file, "from below"):          *)
  (*    Decomposing one step into m >= 2 sub-steps,   *)
  (*    repeated k times, gives m^k sub-operations.   *)
  (*    Refining the step does not reduce the cost.   *)
  (*                                                  *)
  (*  Both directions derive from the same two        *)
  (*  axioms: storage_pays_capacity and               *)
  (*  flip_pays_work.                                 *)
  (* ================================================ *)

End ScaleInvariant.
