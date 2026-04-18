(* ================================================ *)
(*  ConsistencyModelPD.v                             *)
(*                                                   *)
(*  Path-dependent concrete ExistenceSig instance.   *)
(*                                                   *)
(*  Model:                                           *)
(*    Entity = (nat, nat)  (category, index)         *)
(*    interact (d, i) (d', _) =                      *)
(*      if d = d' then (d, i)                        *)
(*      else (d', i mod (S (d' - d)))                *)
(*                                                   *)
(*  The second argument's first component picks the  *)
(*  target category. Different intermediate          *)
(*  categories apply different mod divisors, so the  *)
(*  chain of interactions determines what survives.  *)
(*                                                   *)
(*  Witnesses:                                       *)
(*  1. path dependence (non-trivial);                *)
(*  2. the paper canonical 7 mod 3 = 1 example;      *)
(*  3. K grows unbounded across pairs (via           *)
(*     lcm_range) while remaining finite per pair;   *)
(*  4. high-category interaction preserves index.    *)
(*                                                   *)
(*  This is the "ConsistencyModelPD" companion to    *)
(*  YouAndMe: same (nat × nat) entity shape, but     *)
(*  with a non-trivial path-dependent interact       *)
(*  instead of collapse-to-zero. Together they mark  *)
(*  two extremes within the ExistenceSig layer.      *)
(*                                                   *)
(*  Uses only base ExistenceSig. No Computable       *)
(*  layer needed — the path dependence and K-growth  *)
(*  witnesses are pure information-preservation      *)
(*  facts that the base framework can already        *)
(*  express.                                         *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Eqdep_dec.
From Stdlib Require Import List.
Import ListNotations.

Require Import Existence.

(* ================================================ *)
(*  EXISTENCE SIG INSTANCE                           *)
(* ================================================ *)

Module ConsistencyModelPDSig <: ExistenceSig.

  Definition Entity : Type := (nat * nat)%type.

  (* Path-dependent interaction. b's first component
     acts as the target category. *)
  Definition interact (a b : Entity) : Entity :=
    if Nat.eqb (fst a) (fst b) then a
    else (fst b, Nat.modulo (snd a) (S (fst b - fst a))).

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a. unfold interact. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof.
    intros a b c.
    destruct (interact a c) as [x1 y1] eqn:Ea.
    destruct (interact b c) as [x2 y2] eqn:Eb.
    destruct (Nat.eq_dec x1 x2) as [Hx | Hx];
      destruct (Nat.eq_dec y1 y2) as [Hy | Hy].
    - left. subst. reflexivity.
    - right. intro H. inversion H. contradiction.
    - right. intro H. inversion H. contradiction.
    - right. intro H. inversion H. contradiction.
  Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (0, 0), (0, 1). intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intros [d i]. exists (S d, 0).
    unfold interact. simpl fst.
    assert (Heqb : (d =? S d) = false) by (apply Nat.eqb_neq; lia).
    rewrite Heqb. intro H. inversion H. lia.
  Qed.

  Definition convention_eq : Entity -> Entity -> Prop :=
    fun _ _ => False.

  Theorem convention_not_derivable :
    forall (a b : Entity),
      convention_eq a b ->
      forall c : Entity,
        interact a c <> interact b c.
  Proof. intros a b H. exfalso. exact H. Qed.

End ConsistencyModelPDSig.

Module ConsistencyModelPDTheory := ExistenceTheory ConsistencyModelPDSig.

Export ConsistencyModelPDSig.
Import ConsistencyModelPDSig.
Import ConsistencyModelPDTheory.

(* ================================================ *)
(*  PATH DEPENDENCE WITNESS                          *)
(*                                                   *)
(*  Entity (0, 5) reaches category 2 via two paths:  *)
(*                                                   *)
(*  Path A: 0 → 1 → 2                                *)
(*    interact (0,5) (1,_) = (1, 5 mod 2) = (1, 1)   *)
(*    interact (1,1) (2,_) = (2, 1 mod 2) = (2, 1)   *)
(*                                                   *)
(*  Path B: 0 → 2                                    *)
(*    interact (0,5) (2,_) = (2, 5 mod 3) = (2, 2)   *)
(*                                                   *)
(*  (2, 1) ≠ (2, 2). Path dependence.                *)
(* ================================================ *)

Theorem v_path_dependence :
  interact (interact (0, 5) (1, 0)) (2, 0) <>
  interact (0, 5) (2, 0).
Proof.
  intro Heq.
  apply (f_equal snd) in Heq.
  vm_compute in Heq.
  discriminate Heq.
Qed.

(* Paper canonical example: 7 mod 3 = 1. *)
Theorem paper_seven_mod_three :
  interact (0, 7) (2, 0) = (2, 1).
Proof.
  vm_compute. reflexivity.
Qed.

(* ================================================ *)
(*  ILLUSTRATIVE WITNESSES                           *)
(* ================================================ *)

Definition red_apple   : Entity := (0, 0).
Definition green_apple : Entity := (0, 2).

Theorem w_apples_differ : red_apple <> green_apple.
Proof. discriminate. Qed.

Theorem w_interactions_collapse :
  interact red_apple (1, 0) = interact green_apple (1, 0).
Proof. vm_compute. reflexivity. Qed.

(* ================================================ *)
(*  K GROWS: CONCRETE WITNESSES                      *)
(* ================================================ *)

Theorem distinct_indices :
  forall v1 v2 : nat, v1 <> v2 -> (0, v1) <> (0, v2).
Proof. intros v1 v2 Hv Heq. inversion Heq. contradiction. Qed.

(* (0,0) vs (0,2): category 1 fails, category 2 works. *)
Theorem K_grows_step1_fail :
  interact (0, 0) (1, 0) = interact (0, 2) (1, 0).
Proof. vm_compute. reflexivity. Qed.

Theorem K_grows_step1_success :
  interact (0, 0) (2, 0) <> interact (0, 2) (2, 0).
Proof.
  intro Heq. apply (f_equal snd) in Heq.
  vm_compute in Heq. discriminate Heq.
Qed.

(* (0,0) vs (0,6): categories 1,2 fail, 3 works. *)
Theorem K_grows_step2_fail1 :
  interact (0, 0) (1, 0) = interact (0, 6) (1, 0).
Proof. vm_compute. reflexivity. Qed.

Theorem K_grows_step2_fail2 :
  interact (0, 0) (2, 0) = interact (0, 6) (2, 0).
Proof. vm_compute. reflexivity. Qed.

Theorem K_grows_step2_success :
  interact (0, 0) (3, 0) <> interact (0, 6) (3, 0).
Proof.
  intro Heq. apply (f_equal snd) in Heq.
  vm_compute in Heq. discriminate Heq.
Qed.

(* (0,0) vs (0,12): categories 1,2,3 fail, 4 works. *)
Theorem K_grows_step3_fail1 :
  interact (0, 0) (1, 0) = interact (0, 12) (1, 0).
Proof. vm_compute. reflexivity. Qed.

Theorem K_grows_step3_fail2 :
  interact (0, 0) (2, 0) = interact (0, 12) (2, 0).
Proof. vm_compute. reflexivity. Qed.

Theorem K_grows_step3_fail3 :
  interact (0, 0) (3, 0) = interact (0, 12) (3, 0).
Proof. vm_compute. reflexivity. Qed.

Theorem K_grows_step3_success :
  interact (0, 0) (4, 0) <> interact (0, 12) (4, 0).
Proof.
  intro Heq. apply (f_equal snd) in Heq.
  vm_compute in Heq. discriminate Heq.
Qed.

(* ================================================ *)
(*  K GROWS: GENERAL THEOREM                         *)
(*                                                   *)
(*  For any k, there exist distinct entities that    *)
(*  categories 1..k all fail to distinguish.         *)
(* ================================================ *)

Fixpoint lcm_range (n : nat) : nat :=
  match n with
  | O => 1
  | S m => Nat.lcm (S (S m)) (lcm_range m)
  end.

Lemma lcm_range_pos : forall k, 0 < lcm_range k.
Proof.
  induction k; simpl.
  - lia.
  - destruct (Nat.eq_dec (Nat.lcm (S (S k)) (lcm_range k)) 0) as [H|H].
    + apply Nat.lcm_eq_0 in H. lia.
    + lia.
Qed.

Lemma divide_trans :
  forall a b c,
    Nat.divide a b -> Nat.divide b c -> Nat.divide a c.
Proof. intros a b c [x Hx] [y Hy]. exists (y * x). lia. Qed.

Lemma lcm_range_divides_all :
  forall k d : nat, d <= k ->
    Nat.divide (S (S d)) (lcm_range (S k)).
Proof.
  induction k.
  - intros d Hd.
    apply Nat.le_0_r in Hd. subst. simpl. apply Nat.divide_lcm_l.
  - intros d Hd.
    destruct (Nat.eq_dec d (S k)).
    + subst. simpl. apply Nat.divide_lcm_l.
    + apply (divide_trans _ (lcm_range (S k)) _).
      * apply IHk. apply Nat.lt_succ_r.
        apply Nat.lt_eq_cases in Hd as [Hlt | Heq].
        -- exact Hlt.
        -- exfalso. apply n. exact Heq.
      * simpl. apply Nat.divide_lcm_r.
Qed.

Lemma divide_mod_0 :
  forall v d, Nat.divide (S (S d)) v -> Nat.modulo v (S (S d)) = 0.
Proof.
  intros v d [x Hx]. subst. apply Nat.Div0.mod_mul.
Qed.

Theorem K_grows_general :
  forall k d : nat,
    d <= k ->
    interact (0, 0) (S d, 0) =
    interact (0, lcm_range (S k)) (S d, 0).
Proof.
  intros k d Hd.
  unfold interact. simpl fst. simpl snd.
  assert (Heqb : (0 =? S d) = false) by (apply Nat.eqb_neq; lia).
  rewrite Heqb. rewrite Nat.sub_0_r.
  cut (Nat.modulo 0 (S (S d)) = Nat.modulo (lcm_range (S k)) (S (S d))).
  { intro H. rewrite H. reflexivity. }
  transitivity 0.
  - apply Nat.Div0.mod_0_l.
  - symmetry. apply divide_mod_0. apply lcm_range_divides_all. exact Hd.
Qed.

Lemma pair_snd_eq :
  forall (a b c d : nat), (a, b) = (c, d) -> b = d.
Proof. intros. congruence. Qed.

Theorem K_grows_entities_differ :
  forall k : nat, (0, 0) <> (0, lcm_range (S k)).
Proof.
  intros k Heq.
  apply pair_snd_eq in Heq.
  pose proof (lcm_range_pos (S k)) as Hpos.
  rewrite <- Heq in Hpos.
  exact (Nat.lt_irrefl 0 Hpos).
Qed.

Theorem K_unbounded :
  forall k : nat,
    exists v : nat,
      (0, 0) <> (0, v) /\
      forall d : nat, d <= k ->
        interact (0, 0) (S d, 0) = interact (0, v) (S d, 0).
Proof.
  intro k.
  exists (lcm_range (S k)).
  split. { exact (K_grows_entities_differ k). }
  intros d Hd.
  exact (K_grows_general k d Hd).
Qed.

(* ================================================ *)
(*  HIGH CATEGORY PRESERVES FULL INDEX               *)
(* ================================================ *)

Theorem high_dim_preserves_full :
  forall v d : nat,
    d > v ->
    interact (0, v) (d, 0) = (d, v).
Proof.
  intros v d Hd.
  unfold interact. simpl fst. simpl snd.
  assert (Heqb : (0 =? d) = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Heqb. rewrite Nat.sub_0_r.
  replace (Nat.modulo v (S d)) with v.
  - reflexivity.
  - symmetry. apply Nat.mod_small. lia.
Qed.

Theorem K_finite_per_pair :
  forall v : nat,
    v > 0 ->
    interact (0, 0) (S v, 0) <> interact (0, v) (S v, 0).
Proof.
  intros v Hv Heq.
  assert (Hp1 : interact (0, 0) (S v, 0) = (S v, 0)).
  { apply high_dim_preserves_full. lia. }
  assert (Hp2 : interact (0, v) (S v, 0) = (S v, v)).
  { apply high_dim_preserves_full. lia. }
  rewrite Hp1, Hp2 in Heq.
  inversion Heq. lia.
Qed.

(* ================================================ *)
(*  PATH DEPENDENCE SECOND WITNESS                   *)
(* ================================================ *)

Theorem path_dependence_four :
  interact (interact (0, 4) (1, 0)) (2, 0) <>
  interact (0, 4) (2, 0).
Proof.
  intro Heq.
  apply (f_equal snd) in Heq.
  vm_compute in Heq.
  discriminate Heq.
Qed.

(* Sometimes paths collide: (0,7) at category 2 gives
   the same result via both paths. *)
Theorem path_collision_seven :
  interact (interact (0, 7) (1, 0)) (2, 0) =
  interact (0, 7) (2, 0).
Proof. vm_compute. reflexivity. Qed.

(* ================================================ *)
(*  PRESERVED PROPERTIES AND K-GROWTH                *)
(*                                                   *)
(*  A property P is "preserved at target c" iff      *)
(*  entities that are interact_eq_at c also agree    *)
(*  on P.                                            *)
(*                                                   *)
(*  K-growth in this language: (0,0) and (0,2) are   *)
(*  interact_eq_at (1,0), so any property preserved  *)
(*  at the category-1 target cannot distinguish      *)
(*  them. Target (2,0) breaks the agreement —        *)
(*  properties preserved there CAN distinguish them. *)
(*                                                   *)
(*  The general pattern: lcm_range witnesses make    *)
(*  the minimum category at which a preserved        *)
(*  property CAN distinguish a pair grow without     *)
(*  bound.                                           *)
(* ================================================ *)

(* At category 1, (0,0) and (0,2) are interact_eq_at. *)
Theorem pair_02_interact_eq_at_1 :
  interact_eq_at (0,0) (0,2) (1, 0).
Proof. unfold interact_eq_at. apply K_grows_step1_fail. Qed.

(* Any property preserved at category 1 cannot
   distinguish (0,0) from (0,2). *)
Theorem preserved_at_1_merges_02 :
  forall (P : Entity -> Prop),
    preserves_at P (1, 0) ->
    P (0,0) <-> P (0,2).
Proof.
  intros P Hpres.
  apply Hpres. apply pair_02_interact_eq_at_1.
Qed.

(* At category 2, (0,0) and (0,2) are NOT interact_eq_at. *)
Theorem pair_02_not_interact_eq_at_2 :
  ~ interact_eq_at (0,0) (0,2) (2, 0).
Proof.
  unfold interact_eq_at. apply K_grows_step1_success.
Qed.

(* General: for any k, there exists a pair that is
   interact_eq_at categories 1..k. *)
Theorem preserved_merges_up_to_k :
  forall k : nat,
    exists v : nat,
      (0, 0) <> (0, v) /\
      forall d : nat, d <= k ->
        interact_eq_at (0,0) (0,v) (S d, 0).
Proof.
  intro k.
  destruct (K_unbounded k) as [v [Hne Hfail]].
  exists v. split. { exact Hne. }
  intros d Hd. unfold interact_eq_at. exact (Hfail d Hd).
Qed.
