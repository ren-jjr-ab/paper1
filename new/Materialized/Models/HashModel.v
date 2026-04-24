(* ================================================ *)
(*  HashModel.v                                      *)
(*                                                   *)
(*  FxHash-style evaluator as a                      *)
(*  MaterializedExistenceSig instance.                 *)
(*                                                   *)
(*  This file does not model 64-bit FxHash           *)
(*  bit-by-bit. It captures only what the framework  *)
(*  needs to see: a multi-stage hash has a token     *)
(*  budget, and its internal merges show up as       *)
(*  info_size drops paired with storage and flip     *)
(*  cost increments.                                 *)
(*                                                   *)
(*  Stages are encoded as the first nat field of     *)
(*  each entity constructor:                         *)
(*                                                   *)
(*    0  raw input (state + word)                    *)
(*    1  after XOR rotate                            *)
(*    2  after multiply-widen (doubled)              *)
(*    3  after truncation (halved)                   *)
(*    4  final collapsed digest                      *)
(*                                                   *)
(*  Each stage carries a symbolic "shape" list       *)
(*  (list nat) plus the accumulated storage_cost     *)
(*  and flip_cost. The HFrozen wrapper plays the     *)
(*  same role as LEFrozen in LatticeModel:           *)
(*  it is the instance-internal freeze.              *)
(*                                                   *)
(*  Witnesses:                                       *)
(*                                                   *)
(*    - Two distinct raw inputs with the same        *)
(*      info_size collapse to the same entity at     *)
(*      stage 1 (many-to-one hash collision).        *)
(*    - Each non-identity interact step pays the     *)
(*      source info_size into storage_cost, so a     *)
(*      chain of stages accumulates total source     *)
(*      info.                                        *)
(*    - Freezing a raw input blocks the stage-1      *)
(*      collapse: freeze_preserves_existence holds   *)
(*      here exactly as in the lattice instance.     *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Eqdep_dec.
From Stdlib Require Import List.
Import ListNotations.

Require Import Existence.
Require Import Theory.
Require Import Materialized.

(* ================================================ *)
(*  ENTITY                                           *)
(* ================================================ *)

(* Stage code: nat 0..4 select the FxHash stage.
   The first field of each constructor is the stage
   number, which is what interact dispatches on. *)
Inductive HEnt : Type :=
  | HNormal  : nat -> list nat -> nat -> nat -> HEnt
    (* stage shape stor flip *)
  | HFrozen  : nat -> nat -> nat -> HEnt -> HEnt.
    (* dim stor flip inner *)

(* ================================================ *)
(*  OBSERVERS                                        *)
(* ================================================ *)

Fixpoint h_dim (x : HEnt) : nat :=
  match x with
  | HNormal d _ _ _ => d
  | HFrozen d _ _ _ => d
  end.

Fixpoint h_info (x : HEnt) : nat :=
  match x with
  | HNormal _ vs _ _ => fold_right Nat.add 0 vs
  | HFrozen _ _ _ e => h_info e
  end.

Fixpoint h_stor (x : HEnt) : nat :=
  match x with
  | HNormal _ _ s _ => s
  | HFrozen _ s _ _ => s
  end.

Fixpoint h_flip (x : HEnt) : nat :=
  match x with
  | HNormal _ _ _ f => f
  | HFrozen _ _ f _ => f
  end.

Definition dim_as_entity (d : nat) : HEnt := HNormal d [] 0 0.

(* ================================================ *)
(*  FX STAGE TRANSITIONS                             *)
(*                                                   *)
(*  Symbolic transitions between the five FxHash     *)
(*  stages. The exact numeric values do not matter;  *)
(*  what matters is that the transitions are lossy   *)
(*  in specific places, and that info_size evolves   *)
(*  in a way the Materialized axioms can account for.  *)
(*                                                   *)
(*  h_next_vals collapses the shape the same way at  *)
(*  every stage: the current shape is summed into a  *)
(*  single nat mod 64. This is a uniform stand-in    *)
(*  for the per-stage bit operations of real FxHash. *)
(* ================================================ *)

Definition h_next_vals (vs : list nat) : list nat :=
  [fold_right Nat.add 0 vs mod 64].

Definition h_step (e : HEnt) (d : nat) : HEnt :=
  match e with
  | HNormal _ vs s f =>
    let new_vals := h_next_vals vs in
    let old_info := fold_right Nat.add 0 vs in
    let new_info := fold_right Nat.add 0 new_vals in
    HNormal d new_vals (s + old_info)
            (f + Nat.max 1 (new_info - old_info))
  | HFrozen _ s f inner =>
    HFrozen d (s + h_info inner) (f + 1) inner
  end.

Fixpoint h_project_at (x : HEnt) (d : nat) : HEnt :=
  match x with
  | HNormal src_d vs s f =>
    if Nat.eq_dec src_d d then x
    else h_step x d
  | HFrozen src_d s f inner =>
    if Nat.eq_dec src_d d then x
    else h_step x d
  end.

Lemma h_project_at_dim : forall x d, h_dim (h_project_at x d) = d.
Proof.
  induction x as [da vs s f | da s f inner IHinner]; intros d; simpl.
  - destruct (Nat.eq_dec da d); simpl; congruence.
  - destruct (Nat.eq_dec da d); simpl; congruence.
Qed.

Lemma h_project_at_self : forall x, h_project_at x (h_dim x) = x.
Proof.
  induction x as [da vs s f | da s f inner IHinner]; simpl.
  - destruct (Nat.eq_dec da da); [reflexivity | exfalso; apply n; reflexivity].
  - destruct (Nat.eq_dec da da); [reflexivity | exfalso; apply n; reflexivity].
Qed.

(* ================================================ *)
(*  FREEZE (instance-internal)                       *)
(* ================================================ *)

Definition h_freeze (e : HEnt) : HEnt :=
  HFrozen (h_dim e) 0 0 e.

Lemma h_freeze_injective :
  forall a b, h_freeze a = h_freeze b -> a = b.
Proof.
  intros a b H. unfold h_freeze in H. inversion H. reflexivity.
Qed.

(* ================================================ *)
(*  SIGNATURE INSTANCE                               *)
(* ================================================ *)

Module HashComputable <: MaterializedExistenceSig.

  Definition Entity : Type := HEnt.

  Definition interact (a b : Entity) : Entity :=
    h_project_at a (h_dim b).

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a. unfold interact. apply h_project_at_self.
  Qed.

  Fixpoint h_eq_dec (a b : HEnt) : {a = b} + {a <> b}.
  Proof.
    refine (
      match a, b with
      | HNormal da vsa sa fa, HNormal db vsb sb fb => _
      | HFrozen da sa fa ea, HFrozen db sb fb eb => _
      | _, _ => right _
      end); try (intro H; inversion H).
    - destruct (Nat.eq_dec da db) as [Hd|Hd];
        [| right; intro H; inversion H; contradiction].
      destruct (list_eq_dec Nat.eq_dec vsa vsb) as [Hv|Hv];
        [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec sa sb) as [Hs|Hs];
        [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec fa fb) as [Hf|Hf];
        [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
    - destruct (Nat.eq_dec da db) as [Hd|Hd];
        [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec sa sb) as [Hs|Hs];
        [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec fa fb) as [Hf|Hf];
        [| right; intro H; inversion H; contradiction].
      destruct (h_eq_dec ea eb) as [He|He];
        [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
  Defined.

  Definition entity_eq_dec :
    forall a b : Entity, {a = b} + {a <> b} := h_eq_dec.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply entity_eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (HNormal 0 nil 0 0), (HNormal 1 nil 0 0).
    intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intros a. exists (dim_as_entity (S (h_dim a))).
    unfold interact, dim_as_entity. simpl h_dim.
    intro H.
    assert (Hd : h_dim (h_project_at a (S (h_dim a))) = S (h_dim a)).
    { apply h_project_at_dim. }
    rewrite H in Hd. lia.
  Qed.

  Definition collapse : Entity -> Entity -> Prop :=
    fun _ _ => False.

  Theorem interaction_cannot_witness_collapse :
    forall (a b : Entity),
      collapse a b ->
      forall c : Entity,
        interact a c <> interact b c.
  Proof. intros a b H. exfalso. exact H. Qed.

  (* ---- Materialized layer ---- *)

  Definition info_size (e : Entity) : nat := h_info e.
  Definition storage_cost (e : Entity) : nat := h_stor e.
  Definition flip_cost (e : Entity) : nat := h_flip e.

  Lemma h_project_at_change :
    forall x d,
      h_project_at x d <> x ->
      h_stor (h_project_at x d) = h_stor x + h_info x /\
      h_flip (h_project_at x d) =
        h_flip x + Nat.max 1 (h_info (h_project_at x d) - h_info x).
  Proof.
    induction x as [da vs s f | da s f inner IHinner];
    intros d Hne; simpl in *.
    - destruct (Nat.eq_dec da d) as [Hd|Hd].
      + exfalso. apply Hne. reflexivity.
      + simpl. split; reflexivity.
    - destruct (Nat.eq_dec da d) as [Hd|Hd].
      + exfalso. apply Hne. reflexivity.
      + simpl. split.
        * reflexivity.
        * assert (Hsub : h_info inner - h_info inner = 0) by lia.
          rewrite Hsub. reflexivity.
  Qed.

  Theorem storage_pays_capacity :
    forall (a c : Entity),
      interact a c <> a ->
      storage_cost (interact a c) = storage_cost a + info_size a.
  Proof.
    intros a c Hne. unfold storage_cost, info_size, interact.
    apply (proj1 (h_project_at_change a (h_dim c) Hne)).
  Qed.

  Theorem flip_pays_work :
    forall (a c : Entity),
      interact a c <> a ->
      flip_cost (interact a c) =
        flip_cost a + Nat.max 1 (info_size (interact a c) - info_size a).
  Proof.
    intros a c Hne. unfold flip_cost, info_size, interact.
    apply (proj2 (h_project_at_change a (h_dim c) Hne)).
  Qed.

End HashComputable.

(* ================================================ *)
(*  INSTANCE-INTERNAL FREEZE                         *)
(* ================================================ *)

Module HCT := MaterializedExistenceTheory HashComputable.
Import HashComputable HCT.

Definition freeze (e : Entity) : Entity := h_freeze e.

Definition is_frozen (a : Entity) : Prop :=
  exists b, a = freeze b.

Theorem freeze_injective :
  forall a b, freeze a = freeze b -> a = b.
Proof. exact h_freeze_injective. Qed.

Theorem freeze_preserves_existence :
  forall (a b c : Entity),
    is_frozen a ->
    is_frozen b ->
    interact a c = interact b c ->
    a = b.
Proof.
  intros a b c Hfa Hfb Hproj.
  destruct Hfa as [a' Ha]. destruct Hfb as [b' Hb].
  unfold freeze, h_freeze in Ha, Hb. subst a b.
  unfold interact in Hproj. simpl in Hproj.
  destruct (Nat.eq_dec (h_dim a') (h_dim c)) as [Hea | Hea];
    destruct (Nat.eq_dec (h_dim b') (h_dim c)) as [Heb | Heb];
    inversion Hproj; try congruence.
Qed.

(* ================================================ *)
(*  FxHash WITNESSES                                 *)
(* ================================================ *)

(* Raw input at stage 0 with a small shape. *)
Definition fx_raw_a : Entity := HNormal 0 [5; 7] 0 0.
Definition fx_raw_b : Entity := HNormal 0 [4; 8] 0 0.

Example fx_raw_a_info : info_size fx_raw_a = 12.
Proof. reflexivity. Qed.

Example fx_raw_b_info : info_size fx_raw_b = 12.
Proof. reflexivity. Qed.

Example fx_raw_distinct : fx_raw_a <> fx_raw_b.
Proof. intro H. inversion H. Qed.

(* Two distinct raw inputs with the same info_size
   collapse to the same entity under the stage-1 hash. *)
Example fx_stage1_collapses :
  interact fx_raw_a (dim_as_entity 1) =
  interact fx_raw_b (dim_as_entity 1).
Proof. compute. reflexivity. Qed.

(* The merged entity at stage 1 has info_size = (12 mod 64) = 12.
   There is no info_size reduction in this particular example:
   the mod-64 sum happens to preserve the value. *)
Example fx_stage1_result_info :
  info_size (interact fx_raw_a (dim_as_entity 1)) = 12.
Proof. reflexivity. Qed.

(* Storage cost: stage1 paid source info_size = 12. *)
Example fx_stage1_storage :
  storage_cost (interact fx_raw_a (dim_as_entity 1)) = 12.
Proof. reflexivity. Qed.

(* Flip cost: stage1 paid minimum 1 (no growth). *)
Example fx_stage1_flip :
  flip_cost (interact fx_raw_a (dim_as_entity 1)) = 1.
Proof. reflexivity. Qed.

(* ================================================ *)
(*  Multi-stage chain: track cumulative cost         *)
(*                                                   *)
(*  Run a raw input through stages 1 and 2 and       *)
(*  observe how storage_cost accumulates across      *)
(*  interact steps.                                  *)
(* ================================================ *)

Definition fx_big_raw : Entity := HNormal 0 [100; 100] 0 0.

Example fx_big_raw_info : info_size fx_big_raw = 200.
Proof. reflexivity. Qed.

(* Stage 0 -> 1: source info_size 200 is paid into storage_cost.
   New info_size = 200 mod 64 = 8. *)
Definition fx_big_stage1 : Entity :=
  interact fx_big_raw (dim_as_entity 1).

Example fx_big_stage1_info : info_size fx_big_stage1 = 8.
Proof. reflexivity. Qed.

Example fx_big_stage1_stor : storage_cost fx_big_stage1 = 200.
Proof. reflexivity. Qed.

Example fx_big_stage1_flip : flip_cost fx_big_stage1 = 1.
Proof. reflexivity. Qed.

(* Stage 1 -> 2: source info_size 8 is paid into storage_cost.
   New info_size = 8 mod 64 = 8 (no change). *)
Definition fx_big_stage2 : Entity :=
  interact fx_big_stage1 (dim_as_entity 2).

Example fx_big_stage2_stor : storage_cost fx_big_stage2 = 208.
Proof. reflexivity. Qed.

Example fx_big_stage2_flip : flip_cost fx_big_stage2 = 2.
Proof. reflexivity. Qed.

(* Cumulative storage_cost grows by source info_size at each
   stage, and flip_cost grows by 1 per non-identity step. *)

(* ================================================ *)
(*  Freeze blocks the fx_stage1 collapse             *)
(* ================================================ *)

Definition frozen_fx_raw_a : Entity := freeze fx_raw_a.
Definition frozen_fx_raw_b : Entity := freeze fx_raw_b.

Example frozen_fx_raws_stay_distinct :
  interact frozen_fx_raw_a (dim_as_entity 1) <>
  interact frozen_fx_raw_b (dim_as_entity 1).
Proof.
  unfold interact, frozen_fx_raw_a, frozen_fx_raw_b, freeze, h_freeze,
         fx_raw_a, fx_raw_b.
  simpl. intro H. inversion H.
Qed.

(* ================================================ *)
(*  FX_STEP TOKEN COST (bit-level witness)           *)
(*                                                   *)
(*  A single FxHash step on 64-bit state breaks      *)
(*  down into four atomic operations:                *)
(*                                                   *)
(*    token_rotl     64 = 64                         *)
(*    token_xor      64 = 64                         *)
(*    token_mul_w    64 = 49152   (quadratic)        *)
(*    token_trunc    64 = 64                         *)
(*                                                   *)
(*  sum: fx_step_cost 64 = 49344                     *)
(*                                                   *)
(*  This records the real per-step cost of FxHash    *)
(*  against the framework's token budget. It is      *)
(*  independent of the interact function defined     *)
(*  above: the cost comes from the underlying        *)
(*  bit-level operations, not from the symbolic      *)
(*  shape transitions.                               *)
(* ================================================ *)

Definition token_rotl     (n : nat) : nat := n.
Definition token_xor      (n : nat) : nat := n.
Definition token_mul_wide (n : nat) : nat := 12 * n * n.
Definition token_trunc    (n : nat) : nat := n.

Definition fx_step_cost (n : nat) : nat :=
  token_rotl n + token_xor n + token_mul_wide n + token_trunc n.

Example fx_step_cost_64 : fx_step_cost 64 = 49344.
Proof. reflexivity. Qed.

Example fx_step_cost_32 : fx_step_cost 32 = 12384.
Proof. reflexivity. Qed.

(* At n=64, fx_step_cost is dominated by multiply-widen:
   mul_wide accounts for 49152 of the 49344 total. *)
Example mul_wide_is_49152 :
  token_mul_wide 64 = 49152.
Proof. reflexivity. Qed.

Example fx_step_cost_64_breakdown :
  fx_step_cost 64 = token_rotl 64 + token_xor 64 + token_mul_wide 64 + token_trunc 64.
Proof. reflexivity. Qed.

(* ================================================ *)
(*  INTERACTION EQUALITY (interact_eq_at)            *)
(*                                                   *)
(*  Two distinct raw inputs with equal info_size     *)
(*  collapse to the same entity at stage 1.          *)
(*  In the framework's three-way split this is =     *)
(*  (not ≡): fx_raw_a and fx_raw_b remain distinct   *)
(*  as entities, but they are interact_eq_at the     *)
(*  stage-1 observer.                                *)
(* ================================================ *)

Example fx_raw_interact_eq_at :
  HCT.DT.interact_eq_at fx_raw_a fx_raw_b (dim_as_entity 1).
Proof. exact fx_stage1_collapses. Qed.

(* ================================================ *)
(*  FX CHAIN: n hash steps on 64-bit state           *)
(*                                                   *)
(*  Running fx_step n times on a 64-bit state costs  *)
(*  exactly n * fx_step_cost 64 tokens.              *)
(* ================================================ *)

Fixpoint fx_chain_cost (n : nat) : nat :=
  match n with
  | O => 0
  | S k => fx_step_cost 64 + fx_chain_cost k
  end.

Example fx_chain_cost_0 : fx_chain_cost 0 = 0.
Proof. reflexivity. Qed.

(* Make fx_step_cost opaque to the tactics below so that
   simpl and lia do not try to expand the (large) value
   of fx_step_cost 64 into its unary representation. *)
Opaque fx_step_cost.

Theorem fx_chain_cost_linear :
  forall n, fx_chain_cost n = n * fx_step_cost 64.
Proof.
  induction n as [| k IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

(* Running 1 step costs exactly fx_step_cost 64 tokens. *)
Theorem fx_chain_cost_one_step :
  fx_chain_cost 1 = fx_step_cost 64.
Proof.
  rewrite fx_chain_cost_linear. apply Nat.mul_1_l.
Qed.

(* ================================================ *)
(*  LOWER BOUND: the whole chain cannot cost less    *)
(*  than the single most expensive step.             *)
(* ================================================ *)

Lemma mul_ge_one_factor_abs :
  forall (c n : nat), 1 <= n -> c <= n * c.
Proof.
  intros c n Hn. destruct n as [| k].
  - lia.
  - simpl. lia.
Qed.

Theorem fx_chain_cost_lower_bound :
  forall n, n > 0 -> fx_chain_cost n >= fx_step_cost 64.
Proof.
  intros n Hn. rewrite fx_chain_cost_linear.
  apply mul_ge_one_factor_abs. lia.
Qed.
