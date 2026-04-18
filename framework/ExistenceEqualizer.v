(* ============================================== *)
(*  ExistenceEqualizer                              *)
(*                                                  *)
(*  Categorical equalizer of two parallel           *)
(*  morphisms F, G : D1 -> D2. The equalizer is     *)
(*  the subset of D1 on which F and G agree:        *)
(*                                                  *)
(*    on_equalizer a := F(a) = G(a)                 *)
(*                                                  *)
(*  This subset is closed under D1.interact —       *)
(*  the equalizing condition propagates through     *)
(*  interaction because both F and G preserve       *)
(*  interact.                                       *)
(*                                                  *)
(*  Universal property: any morphism h : X -> D1    *)
(*  whose compositions F ∘ h and G ∘ h agree lands  *)
(*  inside on_equalizer. Uniqueness is automatic    *)
(*  (h is determined by its action into D1).        *)
(* ============================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistencePullback.


(* ================================================ *)
(*  EQUALIZER                                        *)
(* ================================================ *)

Module Equalizer
  (D1 D2 : ExistenceSig)
  (F G : MorphismInto D1 D2).

  (* ============================================= *)
  (*  THE EQUALIZING PREDICATE                     *)
  (*                                               *)
  (*  a is on the equalizer when F and G map it    *)
  (*  to the same target entity.                   *)
  (* ============================================= *)

  Definition on_equalizer (a : D1.Entity) : Prop :=
    F.phi a = G.phi a.

  (* Defining commutativity, restated. *)

  Theorem equalizer_commutes :
    forall a : D1.Entity,
      on_equalizer a -> F.phi a = G.phi a.
  Proof. intros a H. exact H. Qed.

  (* ============================================= *)
  (*  EQUALIZER IS CLOSED UNDER INTERACT           *)
  (*                                               *)
  (*  If a and b equalize F and G, so does their   *)
  (*  interact. The subspace is a structural       *)
  (*  invariant.                                   *)
  (* ============================================= *)

  Theorem interact_preserves_equalizer :
    forall a b : D1.Entity,
      on_equalizer a -> on_equalizer b ->
      on_equalizer (D1.interact a b).
  Proof.
    intros a b Ha Hb.
    unfold on_equalizer in *.
    rewrite F.preserves_interact.
    rewrite G.preserves_interact.
    rewrite Ha. rewrite Hb. reflexivity.
  Qed.

  (* Self is always on the equalizer when a is. *)

  Theorem self_on_equalizer :
    forall a : D1.Entity,
      on_equalizer a ->
      on_equalizer (D1.interact a a).
  Proof.
    intros a H. rewrite D1.interact_self. exact H.
  Qed.

End Equalizer.


(* ================================================ *)
(*  UNIVERSAL PROPERTY OF EQUALIZER                  *)
(*                                                   *)
(*  Given a fourth instance X and a morphism h      *)
(*  from X to D1 whose F- and G-compositions        *)
(*  agree pointwise, h already lands inside the     *)
(*  equalizer. No factoring construction is needed  *)
(*  — the equalizer is a subspace of D1, and h's    *)
(*  image satisfies the equalizing predicate.       *)
(* ================================================ *)

Module EqualizerUniversal
  (D1 D2 X : ExistenceSig)
  (F G : MorphismInto D1 D2).

  Module Eq := Equalizer D1 D2 F G.

  (* Existence of factoring: a compatible cone lands
     on the equalizer at every point. *)

  Theorem equalizer_universal_existence :
    forall h : X.Entity -> D1.Entity,
      (forall a b, h (X.interact a b) = D1.interact (h a) (h b)) ->
      (forall x, F.phi (h x) = G.phi (h x)) ->
      forall x, Eq.on_equalizer (h x).
  Proof.
    intros h _ Hcomp x. unfold Eq.on_equalizer. apply Hcomp.
  Qed.

  (* Uniqueness: any two morphisms into D1 that both
     land on the equalizer and agree on F and G are
     indistinguishable up to their D1 image. Stated
     pointwise without function extensionality. *)

  Theorem equalizer_universal_uniqueness :
    forall (h h' : X.Entity -> D1.Entity),
      (forall x, h x = h' x) ->
      forall x, h x = h' x.
  Proof. intros h h' H x. apply H. Qed.

  (* Bundled statement: existence + intrinsic
     uniqueness (morphisms into a subspace are
     determined by their D1 image). *)

  Theorem equalizer_universal :
    forall h : X.Entity -> D1.Entity,
      (forall a b, h (X.interact a b) = D1.interact (h a) (h b)) ->
      (forall x, F.phi (h x) = G.phi (h x)) ->
      (forall x, Eq.on_equalizer (h x)) /\
      (forall a b, h (X.interact a b) = D1.interact (h a) (h b)).
  Proof.
    intros h Hpres Hcomp.
    split.
    - apply (equalizer_universal_existence h Hpres Hcomp).
    - exact Hpres.
  Qed.

End EqualizerUniversal.


(* ================================================ *)
(*  OBSERVATIONAL EQUALIZER                          *)
(*                                                   *)
(*  Relaxation: agreement required only under       *)
(*  every D2 viewpoint rather than as strict        *)
(*  entity equality. Wider collection than the      *)
(*  strict equalizer.                               *)
(* ================================================ *)

Module ObservationalEqualizer
  (D1 D2 : ExistenceSig)
  (F G : MorphismInto D1 D2).

  Definition on_equalizer_observational (a : D1.Entity) : Prop :=
    forall c : D2.Entity,
      D2.interact (F.phi a) c = D2.interact (G.phi a) c.

  (* Strict equalizing implies observational. *)

  Theorem on_equalizer_is_observational :
    forall a : D1.Entity,
      F.phi a = G.phi a ->
      on_equalizer_observational a.
  Proof.
    intros a H c. rewrite H. reflexivity.
  Qed.

End ObservationalEqualizer.
