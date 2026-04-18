(* ============================================== *)
(*  ExistenceCoequalizer                            *)
(*                                                  *)
(*  Categorical coequalizer of two parallel         *)
(*  morphisms F, G : D1 -> D2. The coequalizer is  *)
(*  D2 quotiented by the smallest interact-         *)
(*  respecting equivalence that identifies F(a)     *)
(*  with G(a) for every a ∈ D1.                    *)
(*                                                  *)
(*  Dual of the equalizer: where the equalizer is  *)
(*  a subspace of the source (points where F and   *)
(*  G agree), the coequalizer is a quotient of     *)
(*  the target (forcing F and G to agree).         *)
(*                                                  *)
(*  Construction parallels Pushout:                 *)
(*   - equiv: inductive equivalence respecting     *)
(*     Mul congruence and identifying F(a) with    *)
(*     G(a).                                        *)
(*   - Entity := D2.Entity quotiented by equiv.    *)
(*   - The quotient axiom is inherited from        *)
(*     ExistencePushout (the one meta-axiom in     *)
(*     the framework).                              *)
(* ============================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistencePullback.
Require Import ExistencePushout.


Module Construction
  (D1 D2 : ExistenceSig)
  (F G : MorphismInto D1 D2).

  (* ============================================= *)
  (*  EQUIVALENCE                                  *)
  (*                                               *)
  (*  Smallest equivalence on D2.Entity that:      *)
  (*    - is reflexive, symmetric, transitive,     *)
  (*    - identifies F(a) with G(a) for every a,   *)
  (*    - respects D2.interact.                    *)
  (* ============================================= *)

  Inductive equiv : D2.Entity -> D2.Entity -> Prop :=
    | e_refl : forall x, equiv x x
    | e_sym  : forall u v, equiv u v -> equiv v u
    | e_trans : forall u v w,
        equiv u v -> equiv v w -> equiv u w
    | e_identify : forall a : D1.Entity,
        equiv (F.phi a) (G.phi a)
    | e_interact : forall u u' v v',
        equiv u u' -> equiv v v' ->
        equiv (D2.interact u v) (D2.interact u' v').

  Lemma equiv_refl : forall x, equiv x x.
  Proof. exact e_refl. Qed.

  Lemma equiv_sym : forall u v, equiv u v -> equiv v u.
  Proof. exact e_sym. Qed.

  Lemma equiv_trans :
    forall u v w, equiv u v -> equiv v w -> equiv u w.
  Proof. exact e_trans. Qed.

  (* ============================================= *)
  (*  QUOTIENT                                     *)
  (* ============================================= *)

  Definition Q : QuotientStructure D2.Entity equiv :=
    quotient_exists D2.Entity equiv equiv_refl equiv_sym equiv_trans.

  Definition Entity : Type := qcarrier _ _ Q.
  Definition cls : D2.Entity -> Entity := qcls _ _ Q.

  Lemma cls_correct :
    forall u v, cls u = cls v <-> equiv u v.
  Proof. exact (qcls_correct _ _ Q). Qed.

  Lemma cls_surjective :
    forall q : Entity, exists w, cls w = q.
  Proof. exact (qcls_surjective _ _ Q). Qed.

  Definition Quot_rec
    {B : Type} (f : D2.Entity -> B)
    (Hwd : forall u v, equiv u v -> f u = f v)
    : Entity -> B :=
    proj1_sig (qlift1 _ _ Q B f Hwd).

  Lemma Quot_rec_spec :
    forall {B : Type} (f : D2.Entity -> B) Hwd w,
      Quot_rec f Hwd (cls w) = f w.
  Proof.
    intros B f Hwd w. unfold Quot_rec.
    destruct (qlift1 _ _ Q B f Hwd) as [lifted Hlift].
    simpl. apply Hlift.
  Qed.

  (* ============================================= *)
  (*  INTERACT                                     *)
  (* ============================================= *)

  Definition interact_lift_fun (u v : D2.Entity) : Entity :=
    cls (D2.interact u v).

  Lemma interact_lift_fun_respects :
    forall u u' v v',
      equiv u u' -> equiv v v' ->
      interact_lift_fun u v = interact_lift_fun u' v'.
  Proof.
    intros u u' v v' Hu Hv. unfold interact_lift_fun.
    apply cls_correct. apply e_interact; assumption.
  Qed.

  Definition interact : Entity -> Entity -> Entity :=
    proj1_sig (qlift2 _ _ Q Entity
                 interact_lift_fun interact_lift_fun_respects).

  Lemma interact_spec :
    forall u v : D2.Entity,
      interact (cls u) (cls v) = cls (D2.interact u v).
  Proof.
    intros u v. unfold interact.
    destruct (qlift2 _ _ Q Entity
                     interact_lift_fun interact_lift_fun_respects)
      as [lifted Hlift].
    simpl. unfold interact_lift_fun in Hlift. apply Hlift.
  Qed.

  (* ============================================= *)
  (*  CONVENTION_EQ                                *)
  (*                                               *)
  (*  Same design choice as Pushout: no convention *)
  (*  introduced by the construction.              *)
  (* ============================================= *)

  Definition convention_eq (_ _ : Entity) : Prop := False.

  (* ============================================= *)
  (*  interact_self (PROVED)                       *)
  (* ============================================= *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a.
    destruct (cls_surjective a) as [w Hw].
    rewrite <- Hw.
    rewrite interact_spec.
    rewrite D2.interact_self. reflexivity.
  Qed.

  (* ============================================= *)
  (*  convention_not_derivable (VACUOUS)           *)
  (* ============================================= *)

  Theorem convention_not_derivable :
    forall a b : Entity,
      convention_eq a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof.
    intros a b Hconv. unfold convention_eq in Hconv. destruct Hconv.
  Qed.

  (* ============================================= *)
  (*  QUOTIENT MAP q : D2 -> Coequalizer           *)
  (* ============================================= *)

  Definition q : D2.Entity -> Entity := cls.

  Theorem q_preserves_interact :
    forall a b : D2.Entity,
      q (D2.interact a b) = interact (q a) (q b).
  Proof.
    intros a b. unfold q. rewrite interact_spec. reflexivity.
  Qed.

  (* q identifies F and G: q ∘ F = q ∘ G pointwise. *)

  Theorem q_coequalizes :
    forall a : D1.Entity, q (F.phi a) = q (G.phi a).
  Proof.
    intros a. unfold q.
    apply cls_correct. apply e_identify.
  Qed.

End Construction.


(* ================================================ *)
(*  UNIVERSAL PROPERTY                               *)
(*                                                   *)
(*  Given a third instance D3 and a morphism r       *)
(*  from D2 to D3 that coequalizes F and G (i.e.,   *)
(*  r ∘ F = r ∘ G pointwise), the factoring arrow   *)
(*  r_star : Coequalizer -> D3 exists and is        *)
(*  uniquely characterized by r_star ∘ q = r.       *)
(* ================================================ *)

Module Type CoequalizerInput
  (D1 D2 : ExistenceSig)
  (F G : MorphismInto D1 D2).
End CoequalizerInput.

Module Universal
  (D1 D2 : ExistenceSig)
  (F G : MorphismInto D1 D2)
  (D3 : ExistenceSig)
  (R : MorphismInto D2 D3).

  Module C := Construction D1 D2 F G.

  (* Hypothesis bundled as a Module Type. Users
     supply a concrete instance by proving the
     coequalizing condition as a Theorem. This
     keeps coequalizing conditions out of the trust
     base. *)

  Module Type CoequalizingRmorphism.
    Axiom r_coequalizes :
      forall a : D1.Entity, R.phi (F.phi a) = R.phi (G.phi a).
  End CoequalizingRmorphism.

  Module Factor (CR : CoequalizingRmorphism).

    (* interpret respects equiv by induction on equiv.
       The e_identify case uses r_coequalizes; other
       cases are standard congruence reasoning. *)

    Lemma R_respects_equiv :
      forall u v : D2.Entity, C.equiv u v -> R.phi u = R.phi v.
    Proof.
      intros u v H.
      induction H.
      - reflexivity.
      - symmetry. exact IHequiv.
      - rewrite IHequiv1. exact IHequiv2.
      - apply CR.r_coequalizes.
      - rewrite R.preserves_interact.
        rewrite R.preserves_interact.
        rewrite IHequiv1. rewrite IHequiv2. reflexivity.
    Qed.

    (* The factoring arrow. *)

    Definition r_star : C.Entity -> D3.Entity :=
      C.Quot_rec R.phi R_respects_equiv.

    (* r_star factors through q. *)

    Theorem r_star_factors :
      forall a : D2.Entity, r_star (C.q a) = R.phi a.
    Proof.
      intros a. unfold r_star, C.q.
      rewrite C.Quot_rec_spec. reflexivity.
    Qed.

    (* r_star preserves interact. *)

    Theorem r_star_preserves_interact :
      forall a b : C.Entity,
        r_star (C.interact a b) = D3.interact (r_star a) (r_star b).
    Proof.
      intros a b.
      destruct (C.cls_surjective a) as [u Hu].
      destruct (C.cls_surjective b) as [v Hv].
      rewrite <- Hu. rewrite <- Hv.
      rewrite C.interact_spec.
      unfold r_star.
      rewrite C.Quot_rec_spec.
      rewrite C.Quot_rec_spec.
      rewrite C.Quot_rec_spec.
      apply R.preserves_interact.
    Qed.

    (* Uniqueness: any other factoring arrow r' that
       satisfies the same factoring agrees with
       r_star pointwise. *)

    Theorem r_star_unique :
      forall r' : C.Entity -> D3.Entity,
        (forall a b, r' (C.interact a b) =
                     D3.interact (r' a) (r' b)) ->
        (forall a, r' (C.q a) = R.phi a) ->
        forall e, r' e = r_star e.
    Proof.
      intros r' Hpres Hfact e.
      destruct (C.cls_surjective e) as [w Hw].
      subst e.
      (* Goal: r' (C.cls w) = r_star (C.cls w) *)
      (* C.cls w = C.q w since q := cls *)
      transitivity (R.phi w).
      - exact (Hfact w).
      - symmetry. exact (r_star_factors w).
    Qed.

  End Factor.

End Universal.
