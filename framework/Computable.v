(* ============================================== *)
(*  Computable — quantitative extension           *)
(*                                                *)
(*  Extends ExistenceSig with three               *)
(*  quantitative primitives:                      *)
(*                                                *)
(*    info_size     current capacity              *)
(*    storage_cost  accumulated holding cost      *)
(*    flip_cost     accumulated work cost         *)
(*                                                *)
(*  Two axioms:                                   *)
(*    storage_pays_capacity                       *)
(*    flip_pays_work                              *)
(*                                                *)
(*  No info_monotone — info_size may grow or      *)
(*  shrink under interaction; growth is charged   *)
(*  to flip_cost.                                 *)
(* ============================================== *)

Require Import Existence.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Lia.

Module Type ComputableExistenceSig.
  Include ExistenceSig.

  (* ============================================= *)
  (*  NEW PRIMITIVES                               *)
  (* ============================================= *)

  (* Current capacity — number of distinguishable
     states this entity carries. Finite by
     convention. *)
  Parameter info_size : Entity -> nat.

  (* Accumulated holding cost — the integral of
     info_size across the interaction chain that led
     to this entity. *)
  Parameter storage_cost : Entity -> nat.

  (* Accumulated work cost — the operator count
     across the interaction chain, each non-identity
     step paying at least one unit. *)
  Parameter flip_cost : Entity -> nat.

  (* ============================================= *)
  (*  AXIOMS                                       *)
  (* ============================================= *)

  (* ----- storage_pays_capacity -----
     Each non-identity interaction step advances
     storage_cost by the source's info_size. *)
  Axiom storage_pays_capacity :
    forall (a c : Entity),
      interact a c <> a ->
      storage_cost (interact a c) = storage_cost a + info_size a.

  (* ----- flip_pays_work -----
     Each non-identity interaction pays at least one
     flip token. If info_size grows by k >= 1, it
     pays k; otherwise it pays the minimum of one. *)
  Axiom flip_pays_work :
    forall (a c : Entity),
      interact a c <> a ->
      flip_cost (interact a c) =
        flip_cost a +
        Nat.max 1 (info_size (interact a c) - info_size a).

End ComputableExistenceSig.


(* ============================================== *)
(*  THEORY FUNCTOR                                *)
(* ============================================== *)

Module ComputableExistenceTheory (C : ComputableExistenceSig).
  Module DT := ExistenceTheory C.
  Import C DT.

  (* At the self-viewpoint, interaction is identity
     (interact_self) so both costs are preserved. *)
  Lemma storage_preserved_at_self :
    forall (a : Entity),
      storage_cost (interact a a) = storage_cost a.
  Proof.
    intros a. rewrite interact_self. reflexivity.
  Qed.

  Lemma flip_preserved_at_self :
    forall (a : Entity),
      flip_cost (interact a a) = flip_cost a.
  Proof.
    intros a. rewrite interact_self. reflexivity.
  Qed.

  (* Non-identity interaction that does NOT grow
     info_size: flip advances by exactly one. *)
  Lemma flip_shrink_is_unit :
    forall (a c : Entity),
      interact a c <> a ->
      info_size (interact a c) <= info_size a ->
      flip_cost (interact a c) = flip_cost a + 1.
  Proof.
    intros a c Hne Hshrink.
    rewrite (flip_pays_work a c Hne).
    assert (Hzero : info_size (interact a c) - info_size a = 0).
    { apply Nat.sub_0_le. exact Hshrink. }
    rewrite Hzero. reflexivity.
  Qed.

  (* Non-identity interaction that grows info_size by
     k > 0: flip advances by exactly k. *)
  Lemma flip_grow_pays_growth :
    forall (a c : Entity),
      interact a c <> a ->
      info_size a < info_size (interact a c) ->
      flip_cost (interact a c) =
        flip_cost a + (info_size (interact a c) - info_size a).
  Proof.
    intros a c Hne Hgrow.
    rewrite (flip_pays_work a c Hne).
    assert (Hdiff_ge_one :
      1 <= info_size (interact a c) - info_size a).
    { apply Nat.le_add_le_sub_r. simpl. exact Hgrow. }
    assert (Hmax :
      Nat.max 1 (info_size (interact a c) - info_size a) =
      info_size (interact a c) - info_size a).
    { apply Nat.max_r. exact Hdiff_ge_one. }
    rewrite Hmax. reflexivity.
  Qed.

  (* For any non-identity interaction, storage does
     not decrease and flip strictly advances. No free
     lunch on the work axis. *)
  Lemma both_costs_advance :
    forall (a c : Entity),
      interact a c <> a ->
      storage_cost a <= storage_cost (interact a c) /\
      flip_cost a < flip_cost (interact a c).
  Proof.
    intros a c Hne. split.
    - rewrite (storage_pays_capacity a c Hne). apply Nat.le_add_r.
    - rewrite (flip_pays_work a c Hne).
      apply Nat.lt_add_pos_r.
      apply Nat.lt_le_trans with 1.
      + apply Nat.lt_0_1.
      + apply Nat.le_max_l.
  Qed.

  (* ============================================= *)
  (*  CHAIN-BASED COST ACCUMULATION                *)
  (*                                               *)
  (*  A chain is a list of viewpoints; apply_chain *)
  (*  folds interact. Under the non-self           *)
  (*  condition at each step, flip_cost advances   *)
  (*  by at least one per step — the framework's   *)
  (*  "no free work" principle lifted to chains.   *)
  (* ============================================= *)

  Fixpoint apply_chain (chain : list Entity) (a : Entity) : Entity :=
    match chain with
    | [] => a
    | c :: rest => apply_chain rest (interact a c)
    end.

  (* Predicate: every step of the chain is non-self. *)

  Fixpoint all_non_self (a : Entity) (chain : list Entity) : Prop :=
    match chain with
    | [] => True
    | c :: rest =>
        interact a c <> a /\ all_non_self (interact a c) rest
    end.

  (* Flip cost lower bound on non-self chains: at
     least length(chain) work tokens are consumed. *)

  Theorem chain_flip_cost_bound :
    forall (chain : list Entity) (a : Entity),
      all_non_self a chain ->
      flip_cost (apply_chain chain a) >= flip_cost a + length chain.
  Proof.
    intros chain. induction chain as [| c rest IH].
    - intros a _. simpl. lia.
    - intros a [Hne Hrest]. simpl.
      specialize (IH (interact a c) Hrest).
      destruct (both_costs_advance a c Hne) as [_ Hflip].
      lia.
  Qed.

  (* Storage cost also accumulates monotonically on
     non-self chains, though the increment depends
     on info_size along the way. A weaker, uniform
     statement: storage is non-decreasing. *)

  Theorem chain_storage_cost_monotone :
    forall (chain : list Entity) (a : Entity),
      all_non_self a chain ->
      storage_cost a <= storage_cost (apply_chain chain a).
  Proof.
    intros chain. induction chain as [| c rest IH].
    - intros a _. simpl. lia.
    - intros a [Hne Hrest]. simpl.
      specialize (IH (interact a c) Hrest).
      destruct (both_costs_advance a c Hne) as [Hstor _].
      lia.
  Qed.

End ComputableExistenceTheory.


(* ================================================ *)
(*  COMPUTABLE MORPHISM                              *)
(*                                                   *)
(*  A morphism between ComputableExistenceSig        *)
(*  instances that preserves the cost structure.    *)
(*  Framework-level definitions — instances assert  *)
(*  these properties against their own cost         *)
(*  functions.                                      *)
(* ================================================ *)

Module ComputableMorphism (C1 C2 : ComputableExistenceSig).

  Definition preserves_interact (phi : C1.Entity -> C2.Entity) : Prop :=
    forall a b : C1.Entity,
      phi (C1.interact a b) = C2.interact (phi a) (phi b).

  Definition preserves_info_size (phi : C1.Entity -> C2.Entity) : Prop :=
    forall a : C1.Entity,
      C2.info_size (phi a) = C1.info_size a.

  Definition preserves_storage_cost (phi : C1.Entity -> C2.Entity) : Prop :=
    forall a : C1.Entity,
      C2.storage_cost (phi a) = C1.storage_cost a.

  Definition preserves_flip_cost (phi : C1.Entity -> C2.Entity) : Prop :=
    forall a : C1.Entity,
      C2.flip_cost (phi a) = C1.flip_cost a.

  (* Full cost-preserving morphism: all three quantitative
     primitives and interact preserved. *)

  Definition computable_morphism (phi : C1.Entity -> C2.Entity) : Prop :=
    preserves_interact phi /\
    preserves_info_size phi /\
    preserves_storage_cost phi /\
    preserves_flip_cost phi.

  (* Convenience projections. *)

  Theorem computable_morphism_preserves_interact :
    forall phi, computable_morphism phi -> preserves_interact phi.
  Proof. intros phi [H _]. exact H. Qed.

  Theorem computable_morphism_preserves_info_size :
    forall phi, computable_morphism phi -> preserves_info_size phi.
  Proof. intros phi [_ [H _]]. exact H. Qed.

  Theorem computable_morphism_preserves_storage_cost :
    forall phi, computable_morphism phi -> preserves_storage_cost phi.
  Proof. intros phi [_ [_ [H _]]]. exact H. Qed.

  Theorem computable_morphism_preserves_flip_cost :
    forall phi, computable_morphism phi -> preserves_flip_cost phi.
  Proof. intros phi [_ [_ [_ H]]]. exact H. Qed.

  (* Observation: cost-preserving morphisms are rare.
     Even a structural embedding typically adjusts costs
     by some offset. A useful weakening is a "shifted"
     morphism that preserves up to constants. *)

  Definition preserves_storage_cost_shifted
    (phi : C1.Entity -> C2.Entity) (k : nat) : Prop :=
    forall a : C1.Entity,
      C2.storage_cost (phi a) = C1.storage_cost a + k.

  Definition preserves_flip_cost_shifted
    (phi : C1.Entity -> C2.Entity) (k : nat) : Prop :=
    forall a : C1.Entity,
      C2.flip_cost (phi a) = C1.flip_cost a + k.

End ComputableMorphism.


(* ================================================ *)
(*  COMPUTABLE COMPOSITION                           *)
(*                                                   *)
(*  Three-instance composition closed under         *)
(*  cost-preserving morphism class. Each cost       *)
(*  primitive composes independently.               *)
(* ================================================ *)

Module ComputableCompose
  (C1 C2 C3 : ComputableExistenceSig).

  Definition compose
    (psi : C2.Entity -> C3.Entity)
    (phi : C1.Entity -> C2.Entity) : C1.Entity -> C3.Entity :=
    fun x => psi (phi x).

  Theorem compose_preserves_interact :
    forall psi phi,
      (forall a b,
        phi (C1.interact a b) = C2.interact (phi a) (phi b)) ->
      (forall a b,
        psi (C2.interact a b) = C3.interact (psi a) (psi b)) ->
      forall a b,
        compose psi phi (C1.interact a b) =
        C3.interact (compose psi phi a) (compose psi phi b).
  Proof.
    intros psi phi Hphi Hpsi a b.
    unfold compose. rewrite Hphi. apply Hpsi.
  Qed.

  Theorem compose_preserves_info_size :
    forall psi phi,
      (forall a, C2.info_size (phi a) = C1.info_size a) ->
      (forall a, C3.info_size (psi a) = C2.info_size a) ->
      forall a, C3.info_size (compose psi phi a) = C1.info_size a.
  Proof.
    intros psi phi Hphi Hpsi a. unfold compose.
    rewrite Hpsi. apply Hphi.
  Qed.

  Theorem compose_preserves_storage_cost :
    forall psi phi,
      (forall a, C2.storage_cost (phi a) = C1.storage_cost a) ->
      (forall a, C3.storage_cost (psi a) = C2.storage_cost a) ->
      forall a, C3.storage_cost (compose psi phi a) = C1.storage_cost a.
  Proof.
    intros psi phi Hphi Hpsi a. unfold compose.
    rewrite Hpsi. apply Hphi.
  Qed.

  Theorem compose_preserves_flip_cost :
    forall psi phi,
      (forall a, C2.flip_cost (phi a) = C1.flip_cost a) ->
      (forall a, C3.flip_cost (psi a) = C2.flip_cost a) ->
      forall a, C3.flip_cost (compose psi phi a) = C1.flip_cost a.
  Proof.
    intros psi phi Hphi Hpsi a. unfold compose.
    rewrite Hpsi. apply Hphi.
  Qed.

  (* The full computable-morphism class is closed under
     composition. Shifted variants compose additively
     (k1 + k2), not proved here to keep scope tight. *)

  Theorem compose_of_computable_morphisms :
    forall psi phi,
      (* phi is computable C1 → C2 *)
      (forall a b,
        phi (C1.interact a b) = C2.interact (phi a) (phi b)) ->
      (forall a, C2.info_size (phi a) = C1.info_size a) ->
      (forall a, C2.storage_cost (phi a) = C1.storage_cost a) ->
      (forall a, C2.flip_cost (phi a) = C1.flip_cost a) ->
      (* psi is computable C2 → C3 *)
      (forall a b,
        psi (C2.interact a b) = C3.interact (psi a) (psi b)) ->
      (forall a, C3.info_size (psi a) = C2.info_size a) ->
      (forall a, C3.storage_cost (psi a) = C2.storage_cost a) ->
      (forall a, C3.flip_cost (psi a) = C2.flip_cost a) ->
      (* then compose is computable C1 → C3 *)
      (forall a b,
        compose psi phi (C1.interact a b) =
        C3.interact (compose psi phi a) (compose psi phi b)) /\
      (forall a, C3.info_size (compose psi phi a) = C1.info_size a) /\
      (forall a, C3.storage_cost (compose psi phi a) = C1.storage_cost a) /\
      (forall a, C3.flip_cost (compose psi phi a) = C1.flip_cost a).
  Proof.
    intros psi phi Hi1 Hs1 Hstor1 Hflip1 Hi2 Hs2 Hstor2 Hflip2.
    split; [|split; [|split]].
    - apply compose_preserves_interact; assumption.
    - apply compose_preserves_info_size; assumption.
    - apply compose_preserves_storage_cost; assumption.
    - apply compose_preserves_flip_cost; assumption.
  Qed.

End ComputableCompose.
