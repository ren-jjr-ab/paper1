(* ================================================ *)
(*  LatticeModel.v                                   *)
(*                                                   *)
(*  A concrete MaterializedExistenceSig instance       *)
(*  where gcd-based pair merging makes information   *)
(*  loss directly visible in info_size,              *)
(*  storage_cost, and flip_cost. freeze is provided  *)
(*  as an instance-internal wrapper.                 *)
(*                                                   *)
(*  Entity structure (Inductive):                    *)
(*                                                   *)
(*    LENormal  d vals s f                           *)
(*      a plain value at category d, with            *)
(*      accumulated storage s and flip f.            *)
(*      vals: [a;b] (pair), [v] (scalar), [] (bare). *)
(*                                                   *)
(*    LEFrozen  d s f inner                          *)
(*      a frozen wrapper carrying category, costs,   *)
(*      and an inner entity. Interaction on a frozen *)
(*      entity only updates category and costs; the  *)
(*      inner entity is preserved structurally so    *)
(*      distinct frozens cannot merge.               *)
(*                                                   *)
(*  The freeze invariant (distinct frozens stay      *)
(*  distinct under every interaction) holds          *)
(*  structurally because of how interact is defined  *)
(*  on each constructor:                             *)
(*                                                   *)
(*    - LENormal interaction is lossy (gcd merge).   *)
(*    - LEFrozen interaction is injective in the     *)
(*      inner entity — two distinct frozen sources   *)
(*      with the same inner produce different        *)
(*      frozen targets via their dim/stor/flip       *)
(*      fields; two with different inners produce    *)
(*      results that disagree in the inner slot.     *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Eqdep_dec.
From Stdlib Require Import List.
Import ListNotations.

Require Import Existence.
Require Import Materialized.

(* ================================================ *)
(*  ENTITY                                           *)
(* ================================================ *)

Inductive LatEnt : Type :=
  | LENormal  : nat -> list nat -> nat -> nat -> LatEnt
  | LEFrozen  : nat -> nat -> nat -> LatEnt -> LatEnt.

(* ================================================ *)
(*  DERIVED OBSERVERS                                *)
(* ================================================ *)

Fixpoint lat_dim (x : LatEnt) : nat :=
  match x with
  | LENormal d _ _ _ => d
  | LEFrozen d _ _ _ => d
  end.

Fixpoint lat_info (x : LatEnt) : nat :=
  match x with
  | LENormal _ vs _ _ => fold_right Nat.add 0 vs
  | LEFrozen _ _ _ e => lat_info e
  end.

Fixpoint lat_stor (x : LatEnt) : nat :=
  match x with
  | LENormal _ _ s _ => s
  | LEFrozen _ s _ _ => s
  end.

Fixpoint lat_flip (x : LatEnt) : nat :=
  match x with
  | LENormal _ _ _ f => f
  | LEFrozen _ _ f _ => f
  end.

(* Canonical "category entity" — used to target
   interactions when only a category matters. *)
Definition dim_as_entity (d : nat) : LatEnt := LENormal d [] 0 0.

(* ================================================ *)
(*  INTERACTION                                      *)
(*                                                   *)
(*  LENormal: gcd-based pair collapse at non-self    *)
(*    category; old info accumulates into s, and f  *)
(*    advances by at least 1 per interaction.        *)
(*  LEFrozen: category and costs advance, but the   *)
(*    inner entity is never touched. This is the     *)
(*    structural reason freeze_preserves_existence   *)
(*    holds.                                         *)
(* ================================================ *)

Definition lat_next_vals (vs : list nat) : list nat :=
  match vs with
  | [a; b] => [Nat.gcd a b]
  | [_]    => [0]
  | _      => []
  end.

Fixpoint lat_project_at (x : LatEnt) (d : nat) : LatEnt :=
  match x with
  | LENormal src_d vs s f =>
    if Nat.eq_dec src_d d then x
    else
      let new_vals := lat_next_vals vs in
      let old_info := fold_right Nat.add 0 vs in
      let new_info := fold_right Nat.add 0 new_vals in
      LENormal d new_vals
               (s + old_info)
               (f + Nat.max 1 (new_info - old_info))
  | LEFrozen src_d s f e =>
    if Nat.eq_dec src_d d then x
    else LEFrozen d (s + lat_info e) (f + 1) e
  end.

Lemma lat_project_at_dim : forall x d, lat_dim (lat_project_at x d) = d.
Proof.
  induction x as [da vs s f | da s f e IHe]; intros d; simpl.
  - destruct (Nat.eq_dec da d); simpl; congruence.
  - destruct (Nat.eq_dec da d); simpl; congruence.
Qed.

Lemma lat_project_at_self : forall x, lat_project_at x (lat_dim x) = x.
Proof.
  induction x as [da vs s f | da s f e IHe]; simpl.
  - destruct (Nat.eq_dec da da); [reflexivity | exfalso; apply n; reflexivity].
  - destruct (Nat.eq_dec da da); [reflexivity | exfalso; apply n; reflexivity].
Qed.

(* ================================================ *)
(*  FREEZE (instance-internal)                       *)
(* ================================================ *)

Definition lat_freeze (e : LatEnt) : LatEnt :=
  LEFrozen (lat_dim e) 0 0 e.

Lemma lat_freeze_injective :
  forall a b, lat_freeze a = lat_freeze b -> a = b.
Proof.
  intros a b H. unfold lat_freeze in H.
  inversion H. reflexivity.
Qed.

(* ================================================ *)
(*  COMPUTABLE EXISTENCE SIGNATURE INSTANCE          *)
(* ================================================ *)

Module LatticeComputable <: MaterializedExistenceSig.

  Definition Entity : Type := LatEnt.

  Definition interact (a b : Entity) : Entity :=
    lat_project_at a (lat_dim b).

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a. unfold interact. apply lat_project_at_self.
  Qed.

  (* Decidable equality on LatEnt. *)
  Fixpoint lat_eq_dec (a b : LatEnt) : {a = b} + {a <> b}.
  Proof.
    refine (
      match a, b with
      | LENormal da vsa sa fa, LENormal db vsb sb fb => _
      | LEFrozen da sa fa ea, LEFrozen db sb fb eb => _
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
      destruct (lat_eq_dec ea eb) as [He|He];
        [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
  Defined.

  Definition entity_eq_dec :
    forall a b : Entity, {a = b} + {a <> b} := lat_eq_dec.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply entity_eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (LENormal 0 nil 0 0), (LENormal 1 nil 0 0).
    intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intros a. exists (dim_as_entity (S (lat_dim a))).
    unfold interact, dim_as_entity. simpl lat_dim.
    intro H.
    assert (Hd : lat_dim (lat_project_at a (S (lat_dim a))) = S (lat_dim a)).
    { apply lat_project_at_dim. }
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

  (* ============================================= *)
  (*  COMPUTABLE LAYER                             *)
  (* ============================================= *)

  Definition info_size (e : Entity) : nat := lat_info e.
  Definition storage_cost (e : Entity) : nat := lat_stor e.
  Definition flip_cost (e : Entity) : nat := lat_flip e.

  Lemma lat_project_at_change :
    forall x d,
      lat_project_at x d <> x ->
      lat_stor (lat_project_at x d) = lat_stor x + lat_info x /\
      lat_flip (lat_project_at x d) =
        lat_flip x + Nat.max 1 (lat_info (lat_project_at x d) - lat_info x).
  Proof.
    induction x as [da vs s f | da s f e IHe]; intros d Hne; simpl in *.
    - destruct (Nat.eq_dec da d) as [Hd|Hd].
      + exfalso. apply Hne. reflexivity.
      + simpl. split; reflexivity.
    - destruct (Nat.eq_dec da d) as [Hd|Hd].
      + exfalso. apply Hne. reflexivity.
      + simpl. split.
        * reflexivity.
        * assert (Hsub : lat_info e - lat_info e = 0) by lia.
          rewrite Hsub. simpl. reflexivity.
  Qed.

  Theorem storage_pays_capacity :
    forall (a c : Entity),
      interact a c <> a ->
      storage_cost (interact a c) = storage_cost a + info_size a.
  Proof.
    intros a c Hne.
    unfold storage_cost, info_size, interact.
    apply (proj1 (lat_project_at_change a (lat_dim c) Hne)).
  Qed.

  Theorem flip_pays_work :
    forall (a c : Entity),
      interact a c <> a ->
      flip_cost (interact a c) =
        flip_cost a +
        Nat.max 1 (info_size (interact a c) - info_size a).
  Proof.
    intros a c Hne.
    unfold flip_cost, info_size, interact.
    apply (proj2 (lat_project_at_change a (lat_dim c) Hne)).
  Qed.

End LatticeComputable.

(* ================================================ *)
(*  INSTANCE-INTERNAL FREEZE                         *)
(*                                                   *)
(*  freeze is not a framework primitive. It is       *)
(*  provided here as an instance-level wrapper, and  *)
(*  the key property (distinct frozen entities stay  *)
(*  distinct under every interaction) is a local     *)
(*  theorem.                                         *)
(* ================================================ *)

Module LCT := MaterializedExistenceTheory LatticeComputable.
Import LatticeComputable LCT.

Definition freeze (e : Entity) : Entity := lat_freeze e.

Definition is_frozen (a : Entity) : Prop :=
  exists b, a = freeze b.

Theorem freeze_injective :
  forall a b, freeze a = freeze b -> a = b.
Proof. exact lat_freeze_injective. Qed.

Theorem freeze_preserves_existence :
  forall (a b c : Entity),
    is_frozen a ->
    is_frozen b ->
    interact a c = interact b c ->
    a = b.
Proof.
  intros a b c Hfa Hfb Hproj.
  destruct Hfa as [a' Ha]. destruct Hfb as [b' Hb].
  unfold freeze, lat_freeze in Ha, Hb.
  subst a b.
  unfold interact in Hproj. simpl in Hproj.
  destruct (Nat.eq_dec (lat_dim a') (lat_dim c)) as [Hea | Hea];
    destruct (Nat.eq_dec (lat_dim b') (lat_dim c)) as [Heb | Heb];
    inversion Hproj; try congruence.
Qed.

(* ================================================ *)
(*  WITNESS: information loss in meet collapse      *)
(* ================================================ *)

Definition pair_2_4 : Entity := LENormal 0 [2; 4] 0 0.
Definition pair_4_2 : Entity := LENormal 0 [4; 2] 0 0.

Example pair_2_4_info : info_size pair_2_4 = 6.
Proof. reflexivity. Qed.

Example pair_4_2_info : info_size pair_4_2 = 6.
Proof. reflexivity. Qed.

Example pair_2_4_distinct_from_pair_4_2 : pair_2_4 <> pair_4_2.
Proof. intro H. inversion H. Qed.

Example meet_collapses_distinct_pairs :
  interact pair_2_4 (dim_as_entity 1) =
  interact pair_4_2 (dim_as_entity 1).
Proof.
  unfold interact, dim_as_entity, pair_2_4, pair_4_2. simpl.
  reflexivity.
Qed.

Example meet_result_info_size :
  info_size (interact pair_2_4 (dim_as_entity 1)) = 2.
Proof. reflexivity. Qed.

Example meet_loses_four :
  info_size pair_2_4 - info_size (interact pair_2_4 (dim_as_entity 1)) = 4.
Proof. reflexivity. Qed.

Example meet_storage_cost :
  storage_cost (interact pair_2_4 (dim_as_entity 1)) = 6.
Proof. reflexivity. Qed.

Example meet_flip_cost :
  flip_cost (interact pair_2_4 (dim_as_entity 1)) = 1.
Proof. reflexivity. Qed.

(* ================================================ *)
(*  WITNESS: freeze preserves distinction           *)
(*                                                   *)
(*  Freezing pair_2_4 and pair_4_2 gives two        *)
(*  distinct frozen entities. Interacting both with *)
(*  the (1, _) viewpoint keeps them distinct — the  *)
(*  gcd collapse does not penetrate the freeze      *)
(*  wrapper.                                         *)
(* ================================================ *)

Definition frozen_2_4 : Entity := freeze pair_2_4.
Definition frozen_4_2 : Entity := freeze pair_4_2.

Example frozen_distinct : frozen_2_4 <> frozen_4_2.
Proof. intro H. unfold frozen_2_4, frozen_4_2, freeze, lat_freeze in H.
       inversion H. Qed.

Example frozen_stays_distinct_under_interaction :
  interact frozen_2_4 (dim_as_entity 1) <>
  interact frozen_4_2 (dim_as_entity 1).
Proof.
  unfold interact, dim_as_entity, frozen_2_4, frozen_4_2,
         freeze, lat_freeze, pair_2_4, pair_4_2.
  simpl. intro H. inversion H.
Qed.

(* freeze는 inner의 info_size를 그대로 유지한다. *)
Example frozen_preserves_info_size :
  info_size frozen_2_4 = info_size pair_2_4.
Proof. reflexivity. Qed.

(* ================================================ *)
(*  WITNESS: lattice semantics                       *)
(*                                                   *)
(*  meet (gcd) is commutative and idempotent on the *)
(*  entity level — distinct representations of the  *)
(*  "same" pair converge under interaction.          *)
(* ================================================ *)

(* Commutativity: (a,b) and (b,a) are distinct pair *)
(* entities but meet at the same scalar.             *)
Definition pair_ab (a b : nat) : Entity := LENormal 0 [a; b] 0 0.

Example meet_commutative_3_6 :
  interact (pair_ab 3 6) (dim_as_entity 1) =
  interact (pair_ab 6 3) (dim_as_entity 1).
Proof. compute. reflexivity. Qed.

Example meet_commutative_12_18 :
  interact (pair_ab 12 18) (dim_as_entity 1) =
  interact (pair_ab 18 12) (dim_as_entity 1).
Proof. compute. reflexivity. Qed.

(* General commutativity: for any a, b, meet is commutative. *)
Example meet_commutative_general :
  forall a b,
    interact (pair_ab a b) (dim_as_entity 1) =
    interact (pair_ab b a) (dim_as_entity 1).
Proof.
  intros a b. unfold interact, dim_as_entity, pair_ab, lat_project_at. simpl.
  assert (Hgcd : Nat.gcd a b = Nat.gcd b a) by apply Nat.gcd_comm.
  assert (Hsum : a + (b + 0) = b + (a + 0)) by lia.
  rewrite Hgcd, Hsum. reflexivity.
Qed.

(* Idempotency: meet of an element with itself is   *)
(* itself. info_size halves: 2a → a.                 *)
Example meet_idempotent_5 :
  lat_info (interact (pair_ab 5 5) (dim_as_entity 1)) = 5.
Proof. reflexivity. Qed.

Example meet_idempotent_info_halves :
  forall a,
    info_size (pair_ab a a) = 2 * a /\
    lat_info (interact (pair_ab a a) (dim_as_entity 1)) = a.
Proof.
  intro a. split.
  - unfold info_size, pair_ab, lat_info. simpl. lia.
  - unfold interact, dim_as_entity, pair_ab, lat_info. simpl.
    rewrite Nat.gcd_diag. simpl. lia.
Qed.

(* ================================================ *)
(*  WITNESS: multi-way merge                        *)
(*                                                  *)
(*  Four distinct pair entities with identical      *)
(*  info_size=10 and identical gcd=2 all collapse   *)
(*  to the EXACT same scalar result. All four are   *)
(*  interact_eq_at at the (1, _) viewpoint —        *)
(*  equivalent under interaction.                   *)
(*                                                  *)
(*  Note: pairs must share info_size to merge to    *)
(*  identical entities. Pairs with different total  *)
(*  info (e.g., (2,4) and (4,6)) produce scalars    *)
(*  with different storage_cost, so they don't      *)
(*  merge — the framework's cost tracking           *)
(*  automatically prevents the "phantom merger".    *)
(* ================================================ *)

Definition pair_2_8 : Entity := pair_ab 2 8.
Definition pair_8_2 : Entity := pair_ab 8 2.
Definition pair_4_6 : Entity := pair_ab 4 6.
Definition pair_6_4 : Entity := pair_ab 6 4.

Example four_pairs_same_info :
  info_size pair_2_8 = 10 /\
  info_size pair_8_2 = 10 /\
  info_size pair_4_6 = 10 /\
  info_size pair_6_4 = 10.
Proof. repeat split. Qed.

Example four_pairs_distinct :
  pair_2_8 <> pair_8_2 /\
  pair_8_2 <> pair_4_6 /\
  pair_4_6 <> pair_6_4 /\
  pair_2_8 <> pair_4_6.
Proof.
  repeat split; intro H; inversion H.
Qed.

Example four_pairs_all_meet_at_two :
  let r := interact pair_2_8 (dim_as_entity 1) in
  interact pair_8_2 (dim_as_entity 1) = r /\
  interact pair_4_6 (dim_as_entity 1) = r /\
  interact pair_6_4 (dim_as_entity 1) = r.
Proof.
  repeat split; compute; reflexivity.
Qed.

(* ================================================ *)
(*  INTERACTION EQUALITY (interact_eq_at)           *)
(*                                                  *)
(*  The gcd collapse makes distinct pairs satisfy   *)
(*  interact_eq_at at the (1, _) viewpoint: their   *)
(*  interactions agree even though the entities     *)
(*  themselves remain distinct.                     *)
(* ================================================ *)

Example pair_2_4_interact_eq_at :
  LCT.DT.interact_eq_at pair_2_4 pair_4_2 (dim_as_entity 1).
Proof. exact meet_collapses_distinct_pairs. Qed.

Example four_way_interact_eq_at :
  LCT.DT.interact_eq_at pair_2_8 pair_8_2 (dim_as_entity 1) /\
  LCT.DT.interact_eq_at pair_2_8 pair_4_6 (dim_as_entity 1) /\
  LCT.DT.interact_eq_at pair_2_8 pair_6_4 (dim_as_entity 1).
Proof.
  unfold LCT.DT.interact_eq_at.
  exact four_pairs_all_meet_at_two.
Qed.
