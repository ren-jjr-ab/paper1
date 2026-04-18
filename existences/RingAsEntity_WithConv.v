(* ============================================== *)
(*  RingAsEntity_WithConv                           *)
(*                                                  *)
(*  Extension of RingAsEntity where the ≈ layer    *)
(*  is populated by a ring-native convention       *)
(*  predicate (typically a non-trivial ideal       *)
(*  quotient). The base functor (marker-augmented  *)
(*  Entity) gets two adjustments:                  *)
(*                                                  *)
(*    1.  REnt–Mark interact is extended to carry  *)
(*        source ring-element information forward, *)
(*        so markers can still distinguish          *)
(*        convention-equal REnt pairs.              *)
(*                                                  *)
(*    2.  convention_eq is defined on REnt pairs   *)
(*        from an external predicate `conv`         *)
(*        required to be distinct and to avoid     *)
(*        relating the zero element (otherwise the *)
(*        self-check branch of REnt–REnt interact  *)
(*        would collapse).                          *)
(*                                                  *)
(*  The running instance is ℤ with mod-7           *)
(*  equivalence restricted to non-zero reps. It    *)
(*  realises the classical statement                *)
(*                                                  *)
(*        7 ≡ 14 (mod 7), 14 ≡ 21 (mod 7), …       *)
(*                                                  *)
(*  as the framework relation ≈ (convention_eq),   *)
(*  with `convention_not_derivable` proved.         *)
(* ============================================== *)

Require Import Existence.
Require Import Ring.
Require IntegerRing.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.


(* =========================================== *)
(*  CONVENTION SPECIFICATION                    *)
(*                                              *)
(*  External data the functor needs:             *)
(*    · a binary relation `conv` declaring      *)
(*      which distinct non-zero pairs are ≈;    *)
(*    · a non-zero `witness` element used for   *)
(*      marker-observed REnt dynamics to keep   *)
(*      ring-element information visible.       *)
(* =========================================== *)

Module Type RingConventionSpec (R : DecEqCommRingSig).

  Parameter conv : R.Carrier -> R.Carrier -> Prop.

  Axiom conv_distinct :
    forall a b : R.Carrier, conv a b -> a <> b.

  Axiom conv_nonzero_l :
    forall a b : R.Carrier, conv a b -> a <> R.zero.

  Axiom conv_nonzero_r :
    forall a b : R.Carrier, conv a b -> b <> R.zero.

  Parameter witness : R.Carrier.

  Axiom witness_nonzero : witness <> R.zero.

End RingConventionSpec.


(* =========================================== *)
(*  FUNCTOR — RingAsEntity_WithConv             *)
(* =========================================== *)

Module RingAsEntity_WithConv
  (R : DecEqCommRingSig)
  (CS : RingConventionSpec R)
  <: ExistenceSig.

  Module RT := RingTheory R.

  Inductive _Entity : Type :=
    | REnt : R.Carrier -> _Entity
    | Mark : nat       -> _Entity.

  Definition Entity : Type := _Entity.

  Definition entity_eq_dec : forall a b : Entity, {a = b} + {a <> b}.
  Proof.
    intros [xa | ma] [xb | mb].
    - destruct (R.carrier_eq_dec xa xb) as [Hx | Hx].
      + left. subst. reflexivity.
      + right. intros H. inversion H. contradiction.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - destruct (Nat.eq_dec ma mb) as [Ht | Ht].
      + left. subst. reflexivity.
      + right. intros H. inversion H. contradiction.
  Defined.

  Definition interact (a b : Entity) : Entity :=
    match a, b with
    | REnt x, REnt y =>
        match R.carrier_eq_dec x y with
        | left  _ => REnt x
        | right _ => REnt (R.add x y)
        end
    | REnt x, Mark _ => REnt (R.add x CS.witness)
    | Mark m, REnt _ => Mark (S m)
    | Mark m, Mark n =>
        match Nat.eq_dec m n with
        | left  _ => Mark m
        | right _ => Mark (S (Nat.max m n))
        end
    end.

  Definition convention_eq (a b : Entity) : Prop :=
    match a, b with
    | REnt x, REnt y => CS.conv x y
    | _, _           => False
    end.


  (* ------------------------------------------- *)
  (*  AXIOM PROOFS                               *)
  (* ------------------------------------------- *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros [x | m]; simpl.
    - destruct (R.carrier_eq_dec x x) as [_ | H].
      + reflexivity.
      + exfalso. apply H. reflexivity.
    - destruct (Nat.eq_dec m m) as [_ | H].
      + reflexivity.
      + exfalso. apply H. reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply entity_eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (REnt R.zero), (Mark 0).
    intros H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b : Entity, interact a b <> a.
  Proof.
    intros [x | m].
    - (* REnt x: partner Mark 0. Result REnt (x + witness). *)
      exists (Mark 0). simpl. intros H. inversion H as [Heq].
      (* Heq : R.add x CS.witness = x *)
      apply CS.witness_nonzero.
      apply (RT.add_cancel_l x).
      rewrite RT.add_zero_r. exact Heq.
    - (* Mark m: partner Mark (S m). Result Mark (S (S m)). *)
      exists (Mark (S m)). simpl.
      destruct (Nat.eq_dec m (S m)) as [Heq | _].
      + lia.
      + intros H. inversion H.
        assert (Hmax : Nat.max m (S m) = S m) by lia.
        lia.
  Qed.

  Theorem convention_not_derivable :
    forall a b : Entity,
      convention_eq a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof.
    intros [x | mx] [y | my] Hconv c;
      try (simpl in Hconv; contradiction).
    (* Only REnt x, REnt y case remains. *)
    simpl in Hconv.
    pose proof (CS.conv_distinct  x y Hconv) as Hxy.
    pose proof (CS.conv_nonzero_l x y Hconv) as Hx0.
    pose proof (CS.conv_nonzero_r x y Hconv) as Hy0.
    destruct c as [z | k].
    - (* c = REnt z: split on x=z, y=z *)
      simpl.
      destruct (R.carrier_eq_dec x z) as [Hxz | Hxz];
        destruct (R.carrier_eq_dec y z) as [Hyz | Hyz].
      + (* x = z = y contradicts x ≠ y *)
        subst. contradiction.
      + (* x = z, y ≠ z: REnt x vs REnt (y + z) *)
        subst z. intros H. inversion H as [Heq].
        (* Heq : x = R.add y x ⇒ y = zero *)
        apply Hy0.
        apply (RT.add_cancel_l x).
        rewrite RT.add_zero_r.
        rewrite (R.add_comm x y).
        symmetry. exact Heq.
      + (* x ≠ z, y = z: REnt (x+z) vs REnt y *)
        subst z. intros H. inversion H as [Heq].
        (* Heq : R.add x y = y ⇒ x = zero *)
        apply Hx0.
        apply (RT.add_cancel_l y).
        rewrite RT.add_zero_r.
        rewrite (R.add_comm y x).
        exact Heq.
      + (* x ≠ z AND y ≠ z: REnt (x+z) vs REnt (y+z) *)
        intros H. inversion H as [Heq].
        (* Heq : R.add x z = R.add y z ⇒ x = y *)
        apply Hxy.
        apply (RT.add_cancel_l z).
        rewrite (R.add_comm z x).
        rewrite (R.add_comm z y).
        exact Heq.
    - (* c = Mark k: REnt (x + witness) vs REnt (y + witness) *)
      simpl. intros H. inversion H as [Heq].
      (* Heq : R.add x CS.witness = R.add y CS.witness ⇒ x = y *)
      apply Hxy.
      apply (RT.add_cancel_l CS.witness).
      rewrite (R.add_comm CS.witness x).
      rewrite (R.add_comm CS.witness y).
      exact Heq.
  Qed.

End RingAsEntity_WithConv.


(* =========================================== *)
(*  INSTANCE — ℤ with mod-7 (non-zero reps)     *)
(* =========================================== *)

Module IntegerMod7Conv <: RingConventionSpec IntegerRing.IntegerRing.

  Definition conv (a b : Z) : Prop :=
    a <> 0%Z /\ b <> 0%Z /\ a <> b /\ exists k : Z, (a - b = k * 7)%Z.

  Theorem conv_distinct :
    forall a b : IntegerRing.IntegerRing.Carrier, conv a b -> a <> b.
  Proof. unfold conv. intros a b [_ [_ [H _]]]. exact H. Qed.

  Theorem conv_nonzero_l :
    forall a b : IntegerRing.IntegerRing.Carrier,
      conv a b -> a <> IntegerRing.IntegerRing.zero.
  Proof. unfold conv. intros a b [H _]. exact H. Qed.

  Theorem conv_nonzero_r :
    forall a b : IntegerRing.IntegerRing.Carrier,
      conv a b -> b <> IntegerRing.IntegerRing.zero.
  Proof. unfold conv. intros a b [_ [H _]]. exact H. Qed.

  Definition witness : IntegerRing.IntegerRing.Carrier := 1%Z.

  Theorem witness_nonzero : witness <> IntegerRing.IntegerRing.zero.
  Proof. unfold witness. discriminate. Qed.

End IntegerMod7Conv.


Module IntegerMod7Entity :=
  RingAsEntity_WithConv IntegerRing.IntegerRing IntegerMod7Conv.


(* =========================================== *)
(*  WITNESSES — ≈ LAYER REALISED                *)
(*                                              *)
(*  Classical mod-7 equalities between non-zero *)
(*  integer representatives now inhabit         *)
(*  framework convention_eq.                    *)
(* =========================================== *)

Example seven_approx_fourteen :
  IntegerMod7Entity.convention_eq
    (IntegerMod7Entity.REnt 7%Z) (IntegerMod7Entity.REnt 14%Z).
Proof.
  unfold IntegerMod7Entity.convention_eq, IntegerMod7Conv.conv.
  repeat split; try discriminate.
  exists (-1)%Z. reflexivity.
Qed.

Example fourteen_approx_twentyone :
  IntegerMod7Entity.convention_eq
    (IntegerMod7Entity.REnt 14%Z) (IntegerMod7Entity.REnt 21%Z).
Proof.
  unfold IntegerMod7Entity.convention_eq, IntegerMod7Conv.conv.
  repeat split; try discriminate.
  exists (-1)%Z. reflexivity.
Qed.

Example nine_approx_two :
  IntegerMod7Entity.convention_eq
    (IntegerMod7Entity.REnt 9%Z) (IntegerMod7Entity.REnt 2%Z).
Proof.
  unfold IntegerMod7Entity.convention_eq, IntegerMod7Conv.conv.
  repeat split; try discriminate.
  exists 1%Z. reflexivity.
Qed.

(* convention_eq is irreflexive via conv_distinct. *)

Example seven_not_approx_seven :
  ~ IntegerMod7Entity.convention_eq
      (IntegerMod7Entity.REnt 7%Z) (IntegerMod7Entity.REnt 7%Z).
Proof.
  unfold IntegerMod7Entity.convention_eq, IntegerMod7Conv.conv.
  intros [_ [_ [H _]]]. apply H. reflexivity.
Qed.


(* =========================================== *)
(*  CONVENTION_NOT_DERIVABLE AT WORK            *)
(*                                              *)
(*  The framework's convention-axiom guarantees *)
(*  that no interaction witnesses ≈. Here we    *)
(*  invoke the derived theorem for a specific   *)
(*  convention pair.                            *)
(* =========================================== *)

Example seven_fourteen_no_witness :
  forall c : IntegerMod7Entity.Entity,
    IntegerMod7Entity.interact (IntegerMod7Entity.REnt 7%Z) c
    <> IntegerMod7Entity.interact (IntegerMod7Entity.REnt 14%Z) c.
Proof.
  apply IntegerMod7Entity.convention_not_derivable.
  apply seven_approx_fourteen.
Qed.


(* =========================================== *)
(*  REMARK                                      *)
(*                                              *)
(*  The ≈ layer was empty in the default        *)
(*  RingAsEntity (convention_eq = False). By    *)
(*  supplying an ideal-based convention and a   *)
(*  non-zero witness, the layer becomes         *)
(*  inhabited and the classical mod-n           *)
(*  equivalence — restricted to non-zero        *)
(*  representatives — takes its place in the    *)
(*  framework's three-layer equality structure. *)
(*                                              *)
(*  Zero is excluded not by cosmetic choice but *)
(*  by structural necessity: REnt 0 at a        *)
(*  REnt-viewpoint c collapses to c via add, so *)
(*  a convention relating 0 to anything would   *)
(*  produce witness-agreement at that single    *)
(*  viewpoint and fail convention_not_derivable.*)
(*  The non-zero restriction is exactly the     *)
(*  cut the framework axioms demand.            *)
(* =========================================== *)
