(* ============================================== *)
(*  RingAsEntity                                    *)
(*                                                  *)
(*  Any commutative ring with decidable equality    *)
(*  can inhabit ExistenceSig via the marker-        *)
(*  augmented construction                          *)
(*                                                  *)
(*    Entity = REnt (ring element) | Mark (nat)     *)
(*                                                  *)
(*  REnt embeds the ring carrier verbatim. Mark     *)
(*  supplies viewpoint entities that are not ring   *)
(*  elements themselves — the same pattern          *)
(*  RationalRep uses with CMark.                    *)
(*                                                  *)
(*  interact:                                       *)
(*    REnt–REnt : ring add with self-check on       *)
(*                the diagonal (self-check is       *)
(*                R.carrier_eq_dec, part of the     *)
(*                ring data already).               *)
(*    REnt–Mark : marker advances.                  *)
(*    Mark–REnt : marker advances.                  *)
(*    Mark–Mark : nat successor-max on distinct,    *)
(*                self on diagonal.                 *)
(*                                                  *)
(*  convention_eq := False. The functor supplies    *)
(*  only the ≡ and = layers by default; ≈ is left   *)
(*  to optional convention extensions (ideal,       *)
(*  morphism kernel) built on top.                  *)
(*                                                  *)
(*  Coverage.                                       *)
(*                                                  *)
(*  Unlike a carrier-only embedding (which          *)
(*  requires |R| ≥ 3 to satisfy interact_with),     *)
(*  the marker-augmented Entity satisfies all five  *)
(*  axioms for every ring, including the edge       *)
(*  cases previously excluded:                      *)
(*                                                  *)
(*    · F₂ = ℤ/2ℤ (|R| = 2)                         *)
(*    · Trivial ring (|R| = 1, zero = one)          *)
(*                                                  *)
(*  Framework axioms are statements about Entity,   *)
(*  not about Carrier. The sum-type Entity          *)
(*  satisfies them uniformly while keeping the      *)
(*  ring's own operations untouched.                *)
(* ============================================== *)

Require Import Existence.
Require Import Ring.
Require IntegerRing.
Require ModularRing.
Require FinSetRing.
Require PolynomialRing.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.


(* =========================================== *)
(*  FUNCTOR — RingAsEntity                      *)
(* =========================================== *)

Module RingAsEntity (R : DecEqCommRingSig) <: ExistenceSig.

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
    | REnt _, Mark n => Mark (S n)
    | Mark m, REnt _ => Mark (S m)
    | Mark m, Mark n =>
        match Nat.eq_dec m n with
        | left  _ => Mark m
        | right _ => Mark (S (Nat.max m n))
        end
    end.

  Definition convention_eq (_ _ : Entity) : Prop := False.


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
    - (* REnt x: partner is Mark 0, result is Mark 1 — different constructor *)
      exists (Mark 0). simpl. intros H. inversion H.
    - (* Mark m: partner is Mark (S m), result Mark (S (S m)) ≠ Mark m *)
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
  Proof. intros a b []. Qed.

End RingAsEntity.


(* =========================================== *)
(*  INSTANTIATIONS                              *)
(*                                              *)
(*  Six rings lifted into ExistenceSig. The     *)
(*  last two — F₂ and trivial — demonstrate     *)
(*  that the marker pattern covers the          *)
(*  cardinality-boundary cases that a bare      *)
(*  Carrier embedding cannot reach.             *)
(* =========================================== *)

(* ℤ — infinite, straightforward *)
Module IntegerEntity := RingAsEntity IntegerRing.IntegerRing.

(* ℤ/7ℤ — finite, cardinality 7 *)
Module Mod7Entity := RingAsEntity ModularRing.Mod7Ring.

(* Boolean ring on 3-element universe — 8 elements *)
Module FinSet3Entity := RingAsEntity FinSetRing.FinSet3.

(* ℤ[x] — polynomial ring over integers *)
Module IntPoly := PolynomialRing.PolynomialRing IntegerRing.IntegerRing.
Module IntPolyEntity := RingAsEntity IntPoly.

(* F₂ = FinSetRing over 1-element universe = 2 elements ({∅, {0}}) *)
Module F2Size <: FinSetRing.UniverseSize.
  Definition n : nat := 1.
End F2Size.
Module F2 := FinSetRing.FinSetRing F2Size.
Module F2Entity := RingAsEntity F2.

(* Trivial ring = FinSetRing over 0-element universe = 1 element ({∅}) *)
Module TrivialSize <: FinSetRing.UniverseSize.
  Definition n : nat := 0.
End TrivialSize.
Module TrivialRing := FinSetRing.FinSetRing TrivialSize.
Module TrivialEntity := RingAsEntity TrivialRing.


(* =========================================== *)
(*  WITNESSES                                   *)
(*                                              *)
(*  Small computations confirming the encoding  *)
(*  is live. The F₂ and trivial-ring cases are  *)
(*  the headline: they satisfy interact_with    *)
(*  even though their ring carrier is too small *)
(*  for a bare embedding.                       *)
(* =========================================== *)

(* ℤ additive interact on distinct entities. *)

Example integer_add_interact :
  IntegerEntity.interact (IntegerEntity.REnt 3%Z) (IntegerEntity.REnt 5%Z)
    = IntegerEntity.REnt 8%Z.
Proof. reflexivity. Qed.

(* ℤ self-interact returns source. *)

Example integer_self :
  IntegerEntity.interact (IntegerEntity.REnt 7%Z) (IntegerEntity.REnt 7%Z)
    = IntegerEntity.REnt 7%Z.
Proof. apply IntegerEntity.interact_self. Qed.


(* F₂: the previously-impossible case. The element `1` in F₂ has no      *)
(* ring-level partner (0 and 1 are the only choices, and 1+0 = 1). The   *)
(* marker Mark 0 supplies the motion the bare embedding could not.       *)

Example f2_marker_is_partner :
  F2Entity.interact (F2Entity.REnt F2.one) (F2Entity.Mark 0)
    = F2Entity.Mark 1.
Proof. reflexivity. Qed.

Example f2_marker_actually_moves :
  F2Entity.interact (F2Entity.REnt F2.one) (F2Entity.Mark 0)
    <> F2Entity.REnt F2.one.
Proof. intros H. inversion H. Qed.


(* Trivial ring: zero = one, only one ring element. The bare embedding  *)
(* cannot even satisfy `existence`. Marker Mark 0 is distinct from       *)
(* REnt (trivial zero) by constructor, and provides motion for it.      *)

Example trivial_existence :
  TrivialEntity.REnt TrivialRing.zero <> TrivialEntity.Mark 0.
Proof. intros H. inversion H. Qed.

Example trivial_marker_moves :
  TrivialEntity.interact
    (TrivialEntity.REnt TrivialRing.zero) (TrivialEntity.Mark 0)
    = TrivialEntity.Mark 1.
Proof. reflexivity. Qed.


(* Mark–Mark dynamics: distinct markers interact to a fresh marker      *)
(* whose index strictly exceeds both sources.                            *)

Example mark_mark_advance :
  IntegerEntity.interact (IntegerEntity.Mark 3) (IntegerEntity.Mark 5)
    = IntegerEntity.Mark 6.
Proof. reflexivity. Qed.

Example mark_self_preserves :
  IntegerEntity.interact (IntegerEntity.Mark 5) (IntegerEntity.Mark 5)
    = IntegerEntity.Mark 5.
Proof. apply IntegerEntity.interact_self. Qed.


(* =========================================== *)
(*  REMARK                                      *)
(*                                              *)
(*  The ring's own operations are untouched.    *)
(*  interact on REnt–REnt uses `R.add` with a   *)
(*  self-check provided by `R.carrier_eq_dec`   *)
(*  — both components of the ring's declared    *)
(*  interface. The marker machinery is          *)
(*  orthogonal: it lives outside the ring but   *)
(*  within the Entity type, providing motion    *)
(*  partners where the ring is too small or     *)
(*  too rigid to supply them.                   *)
(*                                              *)
(*  Framework position: Entity is declared in   *)
(*  ExistenceSig as a Type, without constraint  *)
(*  on its shape. The sum-type construction     *)
(*  here respects that by extending the ring    *)
(*  carrier into a larger Entity population —   *)
(*  the same move RationalRep makes with CMark. *)
(* =========================================== *)
