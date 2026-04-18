(* ================================================ *)
(*  EpsilonDelta.v                                   *)
(*                                                   *)
(*  Classical epsilon-delta convergence embedded     *)
(*  into the framework as convention_eq.             *)
(*                                                   *)
(*  Structure:                                       *)
(*    EDNormal d i sid : partial observation of      *)
(*                      sequence sid at observation  *)
(*                      index i, at dim d            *)
(*    EDLimit  d lid   : wrapper entity for a limit  *)
(*                      value identified by lid      *)
(*    EDFrozen         : standard freeze wrapper     *)
(*                                                   *)
(*  interact on EDNormal advances i by one; interact *)
(*  on EDLimit only relabels the dim. The two        *)
(*  constructors live in disjoint orbits — no        *)
(*  interaction takes an EDNormal to an EDLimit or   *)
(*  vice versa. Any statement that classical math    *)
(*  treats as "sequence converges to limit" is       *)
(*  therefore a relation between two entities in     *)
(*  distinct orbits.                                 *)
(*                                                   *)
(*  classical_converges is taken as an opaque        *)
(*  Parameter. The intended reading is "the usual    *)
(*  epsilon-delta statement holds classically,       *)
(*  possibly requiring excluded middle and choice to *)
(*  express". This file does not commit to any       *)
(*  computable definition — classical convergence    *)
(*  is whatever it is in classical analysis.         *)
(*                                                   *)
(*  Key theorem: if classical_converges sid lid      *)
(*  holds, the corresponding EDNormal and EDLimit    *)
(*  entities are connected by convention_eq and      *)
(*  *not* by any interaction. This is the structural *)
(*  reading of the paper's thesis — classical        *)
(*  "lim s = L" is framework ~=, not =.              *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Eqdep_dec.

Require Import Existence.
Require Import Computable.

(* ================================================ *)
(*  CLASSICAL CONVERGENCE AS A PARAMETER             *)
(*                                                   *)
(*  Opaque. The framework does not care what this    *)
(*  predicate is internally; we only need its truth  *)
(*  to be independent of framework machinery.        *)
(*  Concrete classical analysis would instantiate    *)
(*  this with the usual epsilon-delta statement      *)
(*  over a reals library.                            *)
(*                                                   *)
(*  --- Soundness note ---                           *)
(*                                                   *)
(*  `classical_converges` is declared at file scope  *)
(*  as a `Parameter` of type `nat -> nat -> Prop`.   *)
(*  In Coq this is equivalent to an `Axiom` asserting*)
(*  that *some* predicate of this type exists, which *)
(*  is trivially true (e.g., `fun _ _ => False`      *)
(*  inhabits the type). The parameter asserts        *)
(*  nothing about the PREDICATE'S CONTENT — no       *)
(*  theorem in this file claims `classical_converges *)
(*  sid lid` holds or fails for any specific pair.   *)
(*  Every claim in this file that mentions           *)
(*  `classical_converges` is CONDITIONAL: "if        *)
(*  `classical_converges sid lid` holds, then        *)
(*  ... convention_eq ...".                          *)
(*                                                   *)
(*  Consequence for `Print Assumptions`: any theorem *)
(*  that transitively depends on this file will     *)
(*  list `classical_converges` as an assumption.     *)
(*  This is BY DESIGN — the file supplies a hook for *)
(*  classical analysis to plug in, not a commitment  *)
(*  of framework-internal truth.                     *)
(*                                                   *)
(*  The companion paper's cited theorems (in         *)
(*  `RationalRep`, `CauchyReal`, `CauchyLimits`,     *)
(*  `RationalToCauchyMorphism`,                      *)
(*  `RationalCauchyFactorization`) do NOT import     *)
(*  this file, so their `Print Assumptions` sets are *)
(*  closed and this parameter never enters the       *)
(*  paper's logical chain.                           *)
(*                                                   *)
(*  If a constructive instantiation is preferred,    *)
(*  replace this `Parameter` with `Definition`       *)
(*  supplying a concrete predicate (e.g.,            *)
(*  `fun _ _ => False` for the degenerate model, or  *)
(*  a full epsilon-delta formula over the chosen     *)
(*  reals library).                                  *)
(* ================================================ *)

Parameter classical_converges : nat -> nat -> Prop.

(* ================================================ *)
(*  ENTITY                                           *)
(* ================================================ *)

Inductive EDEnt : Type :=
  | EDNormal  : nat (*dim*) -> nat (*obs_index*) -> nat (*seq_id*)
                -> nat (*stor*) -> nat (*flip*) -> EDEnt
  | EDLimit   : nat (*dim*) -> nat (*lim_id*)
                -> nat (*stor*) -> nat (*flip*) -> EDEnt
  | EDFrozen  : nat (*dim*) -> nat -> nat -> EDEnt -> EDEnt.

Fixpoint ed_dim (x : EDEnt) : nat :=
  match x with
  | EDNormal d _ _ _ _ => d
  | EDLimit  d _ _ _   => d
  | EDFrozen d _ _ _   => d
  end.

Fixpoint ed_info (x : EDEnt) : nat :=
  match x with
  | EDNormal _ i _ _ _  => S i
  | EDLimit  _ _ _ _    => 1
  | EDFrozen _ _ _ inner => ed_info inner
  end.

Fixpoint ed_stor (x : EDEnt) : nat :=
  match x with
  | EDNormal _ _ _ s _ => s
  | EDLimit  _ _ s _   => s
  | EDFrozen _ s _ _   => s
  end.

Fixpoint ed_flip (x : EDEnt) : nat :=
  match x with
  | EDNormal _ _ _ _ f => f
  | EDLimit  _ _ _ f   => f
  | EDFrozen _ _ f _   => f
  end.

Definition dim_as_entity (d : nat) : EDEnt := EDLimit d 0 0 0.

(* ================================================ *)
(*  STEP AND INTERACT                                *)
(*                                                   *)
(*  ed_step advances the observation index on a      *)
(*  Normal entity (one more sample observed) and     *)
(*  relabels its dim. On a Limit entity it only      *)
(*  relabels the dim. Crucially, the constructor     *)
(*  never changes — EDNormal stays EDNormal,         *)
(*  EDLimit stays EDLimit. This disjointness is      *)
(*  what forces classical convergence to live at     *)
(*  the convention_eq layer.                         *)
(* ================================================ *)

Definition ed_step (e : EDEnt) (d : nat) : EDEnt :=
  match e with
  | EDNormal _ i sid s f =>
      EDNormal d (S i) sid (s + S i) (f + 1)
  | EDLimit _ lid s f =>
      EDLimit d lid (s + 1) (f + 1)
  | EDFrozen _ s f inner =>
      EDFrozen d (s + ed_info inner) (f + 1) inner
  end.

Fixpoint ed_project_at (x : EDEnt) (d : nat) : EDEnt :=
  match x with
  | EDNormal src_d _ _ _ _ =>
      if Nat.eq_dec src_d d then x else ed_step x d
  | EDLimit src_d _ _ _ =>
      if Nat.eq_dec src_d d then x else ed_step x d
  | EDFrozen src_d _ _ _ =>
      if Nat.eq_dec src_d d then x else ed_step x d
  end.

Lemma ed_project_at_dim : forall x d, ed_dim (ed_project_at x d) = d.
Proof.
  induction x as [d0 i sid s f | d0 lid s f | d0 s f inner IH]; intro d; simpl.
  - destruct (Nat.eq_dec d0 d); simpl; congruence.
  - destruct (Nat.eq_dec d0 d); simpl; congruence.
  - destruct (Nat.eq_dec d0 d); simpl; congruence.
Qed.

Lemma ed_project_at_self : forall x, ed_project_at x (ed_dim x) = x.
Proof.
  induction x as [d i sid s f | d lid s f | d s f inner IH]; simpl.
  - destruct (Nat.eq_dec d d); [reflexivity | contradiction].
  - destruct (Nat.eq_dec d d); [reflexivity | contradiction].
  - destruct (Nat.eq_dec d d); [reflexivity | contradiction].
Qed.

(* ================================================ *)
(*  ORBIT SEPARATION                                 *)
(*                                                   *)
(*  The central structural property: ed_project_at   *)
(*  never transforms an EDNormal into an EDLimit or  *)
(*  vice versa. Proven by case analysis on the       *)
(*  source constructor.                              *)
(* ================================================ *)

Lemma ed_project_preserves_normal :
  forall d0 i sid s f d,
    exists d' i' sid' s' f',
      ed_project_at (EDNormal d0 i sid s f) d = EDNormal d' i' sid' s' f'.
Proof.
  intros. simpl.
  destruct (Nat.eq_dec d0 d).
  - exists d0, i, sid, s, f. reflexivity.
  - exists d, (S i), sid, (s + S i), (f + 1). reflexivity.
Qed.

Lemma ed_project_preserves_limit :
  forall d0 lid s f d,
    exists d' lid' s' f',
      ed_project_at (EDLimit d0 lid s f) d = EDLimit d' lid' s' f'.
Proof.
  intros. simpl.
  destruct (Nat.eq_dec d0 d).
  - exists d0, lid, s, f. reflexivity.
  - exists d, lid, (s + 1), (f + 1). reflexivity.
Qed.

Lemma ed_project_preserves_frozen :
  forall d0 s f inner d,
    exists d' s' f',
      ed_project_at (EDFrozen d0 s f inner) d = EDFrozen d' s' f' inner.
Proof.
  intros. simpl.
  destruct (Nat.eq_dec d0 d).
  - exists d0, s, f. reflexivity.
  - exists d, (s + ed_info inner), (f + 1). reflexivity.
Qed.

Lemma normal_project_never_limit :
  forall d0 i sid s f d d' lid' s' f',
    ed_project_at (EDNormal d0 i sid s f) d <> EDLimit d' lid' s' f'.
Proof.
  intros.
  destruct (ed_project_preserves_normal d0 i sid s f d) as [d2 [i2 [sid2 [s2 [f2 Heq]]]]].
  rewrite Heq. discriminate.
Qed.

Lemma limit_project_never_normal :
  forall d0 lid s f d d' i' sid' s' f',
    ed_project_at (EDLimit d0 lid s f) d <> EDNormal d' i' sid' s' f'.
Proof.
  intros.
  destruct (ed_project_preserves_limit d0 lid s f d) as [d2 [lid2 [s2 [f2 Heq]]]].
  rewrite Heq. discriminate.
Qed.

Lemma frozen_project_never_limit :
  forall d0 s f inner d d' lid' s' f',
    ed_project_at (EDFrozen d0 s f inner) d <> EDLimit d' lid' s' f'.
Proof.
  intros.
  destruct (ed_project_preserves_frozen d0 s f inner d) as [d2 [s2 [f2 Heq]]].
  rewrite Heq. discriminate.
Qed.

Lemma limit_project_never_frozen :
  forall d0 lid s f d d' s' f' inner',
    ed_project_at (EDLimit d0 lid s f) d <> EDFrozen d' s' f' inner'.
Proof.
  intros.
  destruct (ed_project_preserves_limit d0 lid s f d) as [d2 [lid2 [s2 [f2 Heq]]]].
  rewrite Heq. discriminate.
Qed.

(* ================================================ *)
(*  FREEZE (instance-internal)                       *)
(* ================================================ *)

Definition ed_freeze (e : EDEnt) : EDEnt := EDFrozen (ed_dim e) 0 0 e.

Lemma ed_freeze_injective :
  forall a b, ed_freeze a = ed_freeze b -> a = b.
Proof. intros. unfold ed_freeze in H. inversion H. reflexivity. Qed.

(* ================================================ *)
(*  FRAMEWORK INSTANCE                               *)
(* ================================================ *)

Module EpsilonDeltaComputable <: ComputableExistenceSig.

  Definition Entity : Type := EDEnt.

  Definition interact (a b : Entity) : Entity :=
    ed_project_at a (ed_dim b).

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof. intros. apply ed_project_at_self. Qed.

  Fixpoint ed_eq_dec (a b : EDEnt) : {a = b} + {a <> b}.
  Proof.
    refine (
      match a, b with
      | EDNormal d1 i1 sid1 s1 f1, EDNormal d2 i2 sid2 s2 f2 => _
      | EDLimit d1 lid1 s1 f1, EDLimit d2 lid2 s2 f2 => _
      | EDFrozen d1 s1 f1 inner1, EDFrozen d2 s2 f2 inner2 => _
      | _, _ => right _
      end); try (intro H; inversion H).
    - destruct (Nat.eq_dec d1 d2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec i1 i2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec sid1 sid2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec s1 s2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec f1 f2); [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
    - destruct (Nat.eq_dec d1 d2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec lid1 lid2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec s1 s2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec f1 f2); [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
    - destruct (Nat.eq_dec d1 d2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec s1 s2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec f1 f2); [| right; intro H; inversion H; contradiction].
      destruct (ed_eq_dec inner1 inner2); [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
  Defined.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply ed_eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (EDNormal 0 0 0 0 0), (EDLimit 0 0 0 0).
    intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intros a. exists (dim_as_entity (S (ed_dim a))).
    unfold interact, dim_as_entity. simpl ed_dim.
    intro H.
    assert (Hd : ed_dim (ed_project_at a (S (ed_dim a))) = S (ed_dim a)).
    { apply ed_project_at_dim. }
    rewrite H in Hd. lia.
  Qed.

  (* convention_eq: classical convergence between a Normal
     (sequence partial observation) and a Limit. Both orientations
     are accepted. Any other constructor pair is False. *)
  Definition convention_eq (a b : Entity) : Prop :=
    match a, b with
    | EDNormal _ _ sid _ _, EDLimit _ lid _ _ => classical_converges sid lid
    | EDLimit _ lid _ _, EDNormal _ _ sid _ _ => classical_converges sid lid
    | _, _ => False
    end.

  (* ----------------------------------------------- *)
  (*  THE KEY THEOREM                                *)
  (*                                                 *)
  (*  convention_not_derivable: if a and b are       *)
  (*  related by convention_eq (i.e., classical      *)
  (*  convergence holds), then no interaction with   *)
  (*  any context c equates them.                    *)
  (*                                                 *)
  (*  Proof idea: convention_eq only holds between   *)
  (*  an EDNormal and an EDLimit. The orbit          *)
  (*  separation lemmas show that interaction never  *)
  (*  crosses these two constructors. Done.          *)
  (* ----------------------------------------------- *)

  Theorem convention_not_derivable :
    forall a b, convention_eq a b ->
    forall c, interact a c <> interact b c.
  Proof.
    intros a b Hconv c.
    destruct a as [da ia sida sa fa | da lida sa fa | da sa fa ainner];
      destruct b as [db ib sidb sb fb | db lidb sb fb | db sb fb binner];
      try (simpl in Hconv; contradiction).
    - (* a = EDNormal, b = EDLimit *)
      unfold interact. intro Heq.
      destruct (ed_project_preserves_normal da ia sida sa fa (ed_dim c))
        as [d' [i' [sid' [s' [f' Hna]]]]].
      destruct (ed_project_preserves_limit db lidb sb fb (ed_dim c))
        as [d'' [lid'' [s'' [f'' Hnb]]]].
      rewrite Hna, Hnb in Heq. discriminate.
    - (* a = EDLimit, b = EDNormal *)
      unfold interact. intro Heq.
      destruct (ed_project_preserves_limit da lida sa fa (ed_dim c))
        as [d' [lid' [s' [f' Hna]]]].
      destruct (ed_project_preserves_normal db ib sidb sb fb (ed_dim c))
        as [d'' [i'' [sid'' [s'' [f'' Hnb]]]]].
      rewrite Hna, Hnb in Heq. discriminate.
  Qed.

  (* ---- Computable layer ---- *)

  Definition info_size (e : Entity) : nat := ed_info e.
  Definition storage_cost (e : Entity) : nat := ed_stor e.
  Definition flip_cost (e : Entity) : nat := ed_flip e.

  Lemma sub_succ_diag : forall n, S n - n = 1.
  Proof.
    induction n; [reflexivity | simpl; exact IHn].
  Qed.

  Lemma ed_project_at_normal_non_id :
    forall d0 i sid s f d,
      d0 <> d ->
      ed_project_at (EDNormal d0 i sid s f) d = ed_step (EDNormal d0 i sid s f) d.
  Proof.
    intros. simpl. destruct (Nat.eq_dec d0 d); [contradiction | reflexivity].
  Qed.

  Lemma ed_project_at_limit_non_id :
    forall d0 lid s f d,
      d0 <> d ->
      ed_project_at (EDLimit d0 lid s f) d = ed_step (EDLimit d0 lid s f) d.
  Proof.
    intros. simpl. destruct (Nat.eq_dec d0 d); [contradiction | reflexivity].
  Qed.

  Lemma ed_project_at_frozen_non_id :
    forall d0 s f inner d,
      d0 <> d ->
      ed_project_at (EDFrozen d0 s f inner) d = ed_step (EDFrozen d0 s f inner) d.
  Proof.
    intros. simpl. destruct (Nat.eq_dec d0 d); [contradiction | reflexivity].
  Qed.

  Theorem storage_pays_capacity :
    forall (a c : Entity),
      interact a c <> a ->
      storage_cost (interact a c) = storage_cost a + info_size a.
  Proof.
    intros a c Hne.
    unfold storage_cost, info_size, interact in *.
    induction a as [d0 i sid s f | d0 lid s f | d0 s f inner _].
    - assert (Hd : d0 <> ed_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ed_dim c)); [reflexivity | contradiction]. }
      rewrite (ed_project_at_normal_non_id d0 i sid s f (ed_dim c) Hd). simpl. reflexivity.
    - assert (Hd : d0 <> ed_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ed_dim c)); [reflexivity | contradiction]. }
      rewrite (ed_project_at_limit_non_id d0 lid s f (ed_dim c) Hd). simpl. reflexivity.
    - assert (Hd : d0 <> ed_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ed_dim c)); [reflexivity | contradiction]. }
      rewrite (ed_project_at_frozen_non_id d0 s f inner (ed_dim c) Hd). simpl. reflexivity.
  Qed.

  Theorem flip_pays_work :
    forall (a c : Entity),
      interact a c <> a ->
      flip_cost (interact a c) =
        flip_cost a + Nat.max 1 (info_size (interact a c) - info_size a).
  Proof.
    intros a c Hne.
    unfold flip_cost, info_size, interact in *.
    induction a as [d0 i sid s f | d0 lid s f | d0 s f inner _].
    - assert (Hd : d0 <> ed_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ed_dim c)); [reflexivity | contradiction]. }
      rewrite (ed_project_at_normal_non_id d0 i sid s f (ed_dim c) Hd).
      unfold ed_step, ed_flip, ed_info. fold ed_info. fold ed_flip.
      rewrite (Nat.sub_succ (S i) i). rewrite sub_succ_diag. reflexivity.
    - assert (Hd : d0 <> ed_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ed_dim c)); [reflexivity | contradiction]. }
      rewrite (ed_project_at_limit_non_id d0 lid s f (ed_dim c) Hd).
      unfold ed_step, ed_flip, ed_info. fold ed_info. fold ed_flip.
      replace (1 - 1) with 0 by lia. reflexivity.
    - assert (Hd : d0 <> ed_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ed_dim c)); [reflexivity | contradiction]. }
      rewrite (ed_project_at_frozen_non_id d0 s f inner (ed_dim c) Hd).
      unfold ed_step, ed_flip, ed_info. fold ed_info. fold ed_flip.
      replace (ed_info inner - ed_info inner) with 0 by lia. reflexivity.
  Qed.

End EpsilonDeltaComputable.

(* ================================================ *)
(*  INSTANCE-INTERNAL FREEZE                         *)
(* ================================================ *)

Module EDTheory := ExistenceTheory EpsilonDeltaComputable.
Import EpsilonDeltaComputable EDTheory.

Definition freeze (e : Entity) : Entity := ed_freeze e.

Definition is_frozen (a : Entity) : Prop :=
  exists b, a = freeze b.

Theorem freeze_injective :
  forall a b, freeze a = freeze b -> a = b.
Proof. exact ed_freeze_injective. Qed.

Theorem freeze_preserves_existence :
  forall (a b c : Entity),
    is_frozen a -> is_frozen b ->
    interact a c = interact b c -> a = b.
Proof.
  intros a b c Hfa Hfb Hproj.
  destruct Hfa as [a' Ha]. destruct Hfb as [b' Hb].
  unfold freeze, ed_freeze in Ha, Hb. subst a b.
  unfold interact in Hproj. simpl in Hproj.
  destruct (Nat.eq_dec (ed_dim a') (ed_dim c));
    destruct (Nat.eq_dec (ed_dim b') (ed_dim c));
    inversion Hproj; try congruence.
Qed.

(* ================================================ *)
(*  TWO STRATEGIES FOR FINITE DEPTH                  *)
(*                                                   *)
(*  When observation must stop (resource limit),     *)
(*  two strategies exist:                            *)
(*                                                   *)
(*  Strategy 1 — FREEZE: stop observing, preserve    *)
(*  the current state. The frozen observation stays  *)
(*  permanently separated from the limit entity.     *)
(*  Information is preserved but the limit is never  *)
(*  reached.                                         *)
(*                                                   *)
(*  Strategy 2 — CONVENTION: declare convention_eq   *)
(*  between the observation and the limit. The limit *)
(*  is "reached" by fiat — no interaction derives    *)
(*  it.                                              *)
(*                                                   *)
(*  Structurally: freeze preserves but never         *)
(*  connects; convention connects but never          *)
(*  derives.                                         *)
(* ================================================ *)

Definition obs_depth3 : Entity := EDNormal 0 3 0 6 3.
Definition the_limit : Entity := EDLimit 0 0 0 0.

(* ---- Strategy 1: Freeze ---- *)

Definition frozen_obs : Entity := freeze obs_depth3.

Theorem frozen_is_frozen : is_frozen frozen_obs.
Proof. exists obs_depth3. reflexivity. Qed.

Theorem frozen_never_is_limit : frozen_obs <> the_limit.
Proof. unfold frozen_obs, the_limit, freeze, ed_freeze. discriminate. Qed.

Theorem frozen_projection_never_meets_limit :
  forall c : Entity,
    interact frozen_obs c <> interact the_limit c.
Proof.
  intros c Heq.
  unfold interact, frozen_obs, freeze, ed_freeze, the_limit in Heq.
  destruct (ed_project_preserves_frozen (ed_dim obs_depth3) 0 0 obs_depth3 (ed_dim c))
    as [d1 [s1 [f1 Hfr]]].
  destruct (ed_project_preserves_limit 0 0 0 0 (ed_dim c))
    as [d2 [lid2 [s2 [f2 Hlm]]]].
  rewrite Hfr in Heq. rewrite Hlm in Heq. discriminate.
Qed.

(* ---- Strategy 2: Convention ---- *)

Theorem convention_connects_to_limit :
  classical_converges 0 0 ->
  convention_eq obs_depth3 the_limit.
Proof. intro H. exact H. Qed.

Theorem convention_not_derived_to_limit :
  classical_converges 0 0 ->
  forall c : Entity,
    interact obs_depth3 c <> interact the_limit c.
Proof.
  intros Hconv c.
  apply (convention_not_derivable obs_depth3 the_limit
           (convention_connects_to_limit Hconv) c).
Qed.

(* ================================================ *)
(*  INTERACTION EQUALITY IN EPSILON-DELTA            *)
(*                                                   *)
(*  interact_eq_at is extremely restrictive here.    *)
(*  Orbit separation means a Normal and a Limit are  *)
(*  NEVER interact_eq_at. Different seq_ids/lids     *)
(*  are preserved by interaction, so different       *)
(*  sequences or different limits also never agree.  *)
(*                                                   *)
(*  Consequence: preserves_at properties cannot      *)
(*  connect observations to limits. convention_eq    *)
(*  is the ONLY bridge.                              *)
(* ================================================ *)

Theorem normal_limit_never_proj_eq :
  forall d0 i sid s0 f0 d1 lid s1 f1 c,
    ~ interact_eq_at (EDNormal d0 i sid s0 f0) (EDLimit d1 lid s1 f1) c.
Proof.
  intros. unfold interact_eq_at, interact. intro Heq.
  destruct (ed_project_preserves_normal d0 i sid s0 f0 (ed_dim c)) as [? [? [? [? [? Hn]]]]].
  destruct (ed_project_preserves_limit d1 lid s1 f1 (ed_dim c)) as [? [? [? [? Hl]]]].
  rewrite Hn in Heq. rewrite Hl in Heq. discriminate.
Qed.

Theorem frozen_limit_never_proj_eq :
  forall d0 s0 f0 inner d1 lid s1 f1 c,
    ~ interact_eq_at (EDFrozen d0 s0 f0 inner) (EDLimit d1 lid s1 f1) c.
Proof.
  intros. unfold interact_eq_at, interact. intro Heq.
  destruct (ed_project_preserves_frozen d0 s0 f0 inner (ed_dim c)) as [? [? [? Hf]]].
  destruct (ed_project_preserves_limit d1 lid s1 f1 (ed_dim c)) as [? [? [? [? Hl]]]].
  rewrite Hf in Heq. rewrite Hl in Heq. discriminate.
Qed.

(* No preserved property can connect obs_depth3 to the_limit,
   because interact_eq_at never holds between them. *)
Theorem preserved_cannot_bridge_to_limit :
  forall c : Entity,
    ~ interact_eq_at obs_depth3 the_limit c.
Proof.
  intros c. unfold obs_depth3, the_limit.
  apply normal_limit_never_proj_eq.
Qed.

(* Frozen obs also cannot be bridged to the limit. *)
Theorem preserved_cannot_bridge_frozen_to_limit :
  forall c : Entity,
    ~ interact_eq_at frozen_obs the_limit c.
Proof.
  intros c. unfold frozen_obs, freeze, ed_freeze, the_limit.
  apply frozen_limit_never_proj_eq.
Qed.

(* ---- Summary ---- *)

(* interact_eq_at: never holds between Normal and Limit,
   never holds between Frozen and Limit.
   preserves_at: cannot connect observation to limit.
   convention_eq: the ONLY bridge between the two orbits.

   freeze: information preserved, limit unreachable.
   convention: limit declared reached, derivation impossible.

   There is no third option. Either you stop and keep
   what you have (freeze), or you declare what you
   cannot derive (convention). Both carry a cost —
   freeze pays by never reaching the limit, convention
   pays by standing outside the derivation apparatus. *)

(* ================================================ *)
(*  WHAT THIS FILE SAYS                              *)
(*                                                   *)
(*  The classical mathematical assertion             *)
(*                                                   *)
(*    lim_{n -> infty} s(n) = L                      *)
(*                                                   *)
(*  is represented in this framework by the relation *)
(*  convention_eq between a Normal entity (the       *)
(*  partial observation of the sequence) and a Limit *)
(*  entity (the value L). The theorem                *)
(*  convention_not_derivable establishes that no     *)
(*  interaction path connects these two entities,    *)
(*  regardless of whether classical convergence      *)
(*  holds — the equality sign in classical math is   *)
(*  carried by convention, not by derivation.        *)
(*                                                   *)
(*  In the framework's three-way distinction:        *)
(*                                                   *)
(*    ==  (Leibniz identity)     — not applicable    *)
(*    =   (interaction equality) — cannot be shown   *)
(*    ~=  (convention_eq)        — the actual status *)
(*                                                   *)
(*  Classical analysis writes "=" in all three       *)
(*  positions. The framework separates them.         *)
(* ================================================ *)
