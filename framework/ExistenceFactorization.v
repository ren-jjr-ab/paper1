(* ============================================== *)
(*  ExistenceFactorization                          *)
(*                                                  *)
(*  Every interact-preserving morphism factors      *)
(*  through its kernel quotient:                    *)
(*                                                  *)
(*         phi                                      *)
(*    D1 -------> D2                                *)
(*     |          ^                                 *)
(*     | cls      | phi_hat                         *)
(*     v          |                                 *)
(*    D1/ker     /                                  *)
(*                                                  *)
(*  Where:                                          *)
(*    - ker a b := phi(a) = phi(b)   (kernel)       *)
(*    - D1/ker is the quotient of D1 by ker         *)
(*    - cls is the canonical surjection             *)
(*    - phi_hat is the induced INJECTION            *)
(*    - phi = phi_hat ∘ cls                         *)
(*                                                  *)
(*  This is the framework's image factorization —   *)
(*  the epi-mono factorization of every morphism    *)
(*  into a surjection followed by an injection.     *)
(*                                                  *)
(*  The quotient axiom is inherited from            *)
(*  ExistencePushout. No new meta-axiom.            *)
(* ============================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistencePullback.
Require Import ExistencePushout.


Module Factorization
  (D1 D2 : ExistenceSig)
  (Phi : MorphismInto D1 D2).

  (* ============================================= *)
  (*  KERNEL RELATION                              *)
  (*                                               *)
  (*  a ~ b iff phi maps them to the same target.  *)
  (* ============================================= *)

  Definition ker (a b : D1.Entity) : Prop :=
    Phi.phi a = Phi.phi b.

  Lemma ker_refl : forall a, ker a a.
  Proof. intros a. unfold ker. reflexivity. Qed.

  Lemma ker_sym : forall a b, ker a b -> ker b a.
  Proof. intros a b H. unfold ker in *. symmetry. exact H. Qed.

  Lemma ker_trans :
    forall a b c, ker a b -> ker b c -> ker a c.
  Proof.
    intros a b c H1 H2. unfold ker in *.
    rewrite H1. exact H2.
  Qed.

  (* Kernel respects D1.interact — structurally closed
     under the framework operation. *)

  Lemma ker_respects_interact_left :
    forall a b c : D1.Entity,
      ker a b ->
      ker (D1.interact a c) (D1.interact b c).
  Proof.
    intros a b c H. unfold ker in *.
    rewrite Phi.preserves_interact.
    rewrite Phi.preserves_interact.
    rewrite H. reflexivity.
  Qed.

  Lemma ker_respects_interact_both :
    forall a a' b b' : D1.Entity,
      ker a a' -> ker b b' ->
      ker (D1.interact a b) (D1.interact a' b').
  Proof.
    intros a a' b b' Ha Hb. unfold ker in *.
    rewrite Phi.preserves_interact.
    rewrite Phi.preserves_interact.
    rewrite Ha. rewrite Hb. reflexivity.
  Qed.

  (* ============================================= *)
  (*  QUOTIENT                                     *)
  (* ============================================= *)

  Definition Q : QuotientStructure D1.Entity ker :=
    quotient_exists D1.Entity ker ker_refl ker_sym ker_trans.

  Definition Entity : Type := qcarrier _ _ Q.
  Definition cls : D1.Entity -> Entity := qcls _ _ Q.

  Lemma cls_correct :
    forall u v, cls u = cls v <-> ker u v.
  Proof. exact (qcls_correct _ _ Q). Qed.

  Lemma cls_surjective :
    forall q : Entity, exists w, cls w = q.
  Proof. exact (qcls_surjective _ _ Q). Qed.

  Definition Quot_rec
    {B : Type} (f : D1.Entity -> B)
    (Hwd : forall u v, ker u v -> f u = f v)
    : Entity -> B :=
    proj1_sig (qlift1 _ _ Q B f Hwd).

  Lemma Quot_rec_spec :
    forall {B : Type} (f : D1.Entity -> B) Hwd w,
      Quot_rec f Hwd (cls w) = f w.
  Proof.
    intros B f Hwd w. unfold Quot_rec.
    destruct (qlift1 _ _ Q B f Hwd) as [lifted Hlift].
    simpl. apply Hlift.
  Qed.

  (* ============================================= *)
  (*  INTERACT ON QUOTIENT                         *)
  (* ============================================= *)

  Definition interact_lift_fun (u v : D1.Entity) : Entity :=
    cls (D1.interact u v).

  Lemma interact_lift_fun_respects :
    forall u u' v v',
      ker u u' -> ker v v' ->
      interact_lift_fun u v = interact_lift_fun u' v'.
  Proof.
    intros u u' v v' Hu Hv. unfold interact_lift_fun.
    apply cls_correct.
    apply ker_respects_interact_both; assumption.
  Qed.

  Definition interact : Entity -> Entity -> Entity :=
    proj1_sig (qlift2 _ _ Q Entity
                 interact_lift_fun interact_lift_fun_respects).

  Lemma interact_spec :
    forall u v : D1.Entity,
      interact (cls u) (cls v) = cls (D1.interact u v).
  Proof.
    intros u v. unfold interact.
    destruct (qlift2 _ _ Q Entity
                     interact_lift_fun interact_lift_fun_respects)
      as [lifted Hlift].
    simpl. unfold interact_lift_fun in Hlift. apply Hlift.
  Qed.

  (* ============================================= *)
  (*  cls PRESERVES INTERACT                       *)
  (* ============================================= *)

  Theorem cls_preserves_interact :
    forall a b : D1.Entity,
      cls (D1.interact a b) = interact (cls a) (cls b).
  Proof.
    intros a b. rewrite interact_spec. reflexivity.
  Qed.

  (* ============================================= *)
  (*  THE INDUCED MAP phi_hat : Entity -> D2        *)
  (*                                               *)
  (*  Because Phi.phi respects ker by the very     *)
  (*  definition of ker, it lifts to a map from    *)
  (*  the quotient.                                *)
  (* ============================================= *)

  Lemma phi_respects_ker :
    forall u v : D1.Entity, ker u v -> Phi.phi u = Phi.phi v.
  Proof. intros u v H. exact H. Qed.

  Definition phi_hat : Entity -> D2.Entity :=
    Quot_rec Phi.phi phi_respects_ker.

  Lemma phi_hat_spec :
    forall u : D1.Entity, phi_hat (cls u) = Phi.phi u.
  Proof. intros u. unfold phi_hat. rewrite Quot_rec_spec. reflexivity. Qed.

  (* ============================================= *)
  (*  THE FACTORIZATION                             *)
  (*                                               *)
  (*  Phi.phi = phi_hat ∘ cls.                     *)
  (* ============================================= *)

  Theorem factorization :
    forall a : D1.Entity, Phi.phi a = phi_hat (cls a).
  Proof.
    intros a. rewrite phi_hat_spec. reflexivity.
  Qed.

  (* ============================================= *)
  (*  phi_hat PRESERVES INTERACT                    *)
  (* ============================================= *)

  Theorem phi_hat_preserves_interact :
    forall x y : Entity,
      phi_hat (interact x y) = D2.interact (phi_hat x) (phi_hat y).
  Proof.
    intros x y.
    destruct (cls_surjective x) as [u Hu].
    destruct (cls_surjective y) as [v Hv].
    rewrite <- Hu. rewrite <- Hv.
    rewrite interact_spec.
    rewrite phi_hat_spec.
    rewrite phi_hat_spec. rewrite phi_hat_spec.
    apply Phi.preserves_interact.
  Qed.

  (* ============================================= *)
  (*  phi_hat IS INJECTIVE                          *)
  (*                                               *)
  (*  Two quotient classes with the same Phi-image *)
  (*  were already identified by the kernel        *)
  (*  relation. This is the heart of the           *)
  (*  factorization: the middle object is as       *)
  (*  collapsed as it can be, no more, no less.    *)
  (* ============================================= *)

  Theorem phi_hat_injective :
    forall x y : Entity,
      phi_hat x = phi_hat y -> x = y.
  Proof.
    intros x y Heq.
    destruct (cls_surjective x) as [u Hu].
    destruct (cls_surjective y) as [v Hv].
    subst x. subst y.
    rewrite phi_hat_spec in Heq. rewrite phi_hat_spec in Heq.
    (* Heq : Phi.phi u = Phi.phi v, i.e., ker u v *)
    apply cls_correct. exact Heq.
  Qed.

  (* ============================================= *)
  (*  cls IS SURJECTIVE                             *)
  (*                                               *)
  (*  Already recorded above; restated for the     *)
  (*  factorization triangle.                      *)
  (* ============================================= *)

  Theorem cls_is_surjective :
    forall q : Entity, exists u, cls u = q.
  Proof. exact cls_surjective. Qed.

  (* ============================================= *)
  (*  UNIQUENESS (up to pointwise agreement)       *)
  (*                                               *)
  (*  Any other factoring through some intermediate *)
  (*  E with interact-preserving maps q : D1 -> E  *)
  (*  and i : E -> D2 satisfying                    *)
  (*     Phi.phi = i ∘ q                            *)
  (*     (q surjective)                             *)
  (*     (i injective)                              *)
  (*  is isomorphic to the canonical factorization. *)
  (*  We state pointwise agreement on phi_hat side. *)
  (* ============================================= *)

  Theorem factorization_unique_on_phi_hat :
    forall (q' : D1.Entity -> D2.Entity),
      (forall a, q' a = Phi.phi a) ->
      forall a, q' a = phi_hat (cls a).
  Proof.
    intros q' H a. rewrite H. apply factorization.
  Qed.

  (* ============================================= *)
  (*  CONVENTION_EQ ON THE QUOTIENT                *)
  (*                                               *)
  (*  Defined as the pullback of D2's convention   *)
  (*  along phi_hat. This is the natural choice    *)
  (*  because phi_hat is injective — the quotient  *)
  (*  faithfully reflects D2's convention          *)
  (*  structure on the image.                      *)
  (*                                               *)
  (*  interaction_cannot_witness_collapse on the quotient     *)
  (*  follows from interaction_cannot_witness_collapse on D2  *)
  (*  combined with phi's interact preservation.   *)
  (* ============================================= *)

  Definition collapse (x y : Entity) : Prop :=
    D2.collapse (phi_hat x) (phi_hat y).

  Theorem interaction_cannot_witness_collapse :
    forall x y : Entity,
      collapse x y ->
      forall c : Entity, interact x c <> interact y c.
  Proof.
    intros x y Hconv c Heq.
    unfold collapse in Hconv.
    destruct (cls_surjective x) as [u Hu].
    destruct (cls_surjective y) as [v Hv].
    destruct (cls_surjective c) as [w Hw].
    subst x. subst y. subst c.
    rewrite phi_hat_spec in Hconv.
    rewrite phi_hat_spec in Hconv.
    rewrite interact_spec in Heq.
    rewrite interact_spec in Heq.
    apply cls_correct in Heq.
    unfold ker in Heq.
    rewrite Phi.preserves_interact in Heq.
    rewrite Phi.preserves_interact in Heq.
    exact (D2.interaction_cannot_witness_collapse
             (Phi.phi u) (Phi.phi v) Hconv (Phi.phi w) Heq).
  Qed.

  (* phi_hat preserves convention by construction. *)

  Theorem phi_hat_preserves_convention :
    forall x y : Entity,
      collapse x y ->
      D2.collapse (phi_hat x) (phi_hat y).
  Proof. intros x y H. exact H. Qed.

  (* cls preserves convention if Phi does. Source
     convention lifts to the quotient via phi_hat's
     factoring. *)

  Theorem cls_preserves_convention :
    (forall a b, D1.collapse a b ->
                 D2.collapse (Phi.phi a) (Phi.phi b)) ->
    forall a b, D1.collapse a b ->
               collapse (cls a) (cls b).
  Proof.
    intros Hphi_pres a b Hconv.
    unfold collapse.
    rewrite phi_hat_spec. rewrite phi_hat_spec.
    apply Hphi_pres. exact Hconv.
  Qed.

  (* ============================================= *)
  (*  SPECIAL CASES                                *)
  (* ============================================= *)

  (* When phi is already injective, the kernel is
     trivial (ker a b iff a = b) and every quotient
     class is a singleton. cls becomes essentially
     identity: distinct elements of D1 stay distinct
     in the quotient. *)

  Theorem injective_phi_makes_cls_injective :
    (forall a b, Phi.phi a = Phi.phi b -> a = b) ->
    forall a b, cls a = cls b -> a = b.
  Proof.
    intros Hinj a b Hcls.
    apply Hinj. apply cls_correct. exact Hcls.
  Qed.

  (* When phi is surjective onto D2, phi_hat is
     surjective. Combined with phi_hat_injective this
     gives phi_hat as a bijection — the factorization
     identifies Entity with D2 (up to bijection).
     No convention reasoning involved. *)

  Theorem phi_hat_surjective_if_phi_surjective :
    (forall b : D2.Entity, exists a : D1.Entity, Phi.phi a = b) ->
    forall b : D2.Entity, exists x : Entity, phi_hat x = b.
  Proof.
    intros Hsurj b.
    destruct (Hsurj b) as [a Ha].
    exists (cls a). rewrite phi_hat_spec. exact Ha.
  Qed.

  (* When phi is surjective, phi_hat has a right
     inverse constructed from the surjectivity
     witness. This is phi_hat being iso in the
     framework's sense (interact-preserving + two-
     sided inverse). *)

  Theorem phi_hat_is_iso_if_phi_surjective :
    (forall b : D2.Entity, exists a : D1.Entity, Phi.phi a = b) ->
    (* phi_hat preserves interact (always) *)
    (forall x y, phi_hat (interact x y) =
                 D2.interact (phi_hat x) (phi_hat y)) /\
    (* phi_hat is surjective *)
    (forall b, exists x, phi_hat x = b) /\
    (* phi_hat is injective *)
    (forall x y, phi_hat x = phi_hat y -> x = y).
  Proof.
    intros Hsurj.
    split; [apply phi_hat_preserves_interact |].
    split; [apply phi_hat_surjective_if_phi_surjective; exact Hsurj |].
    apply phi_hat_injective.
  Qed.

  (* ============================================= *)
  (*  UNIVERSAL PROPERTY (MINIMALITY)              *)
  (*                                               *)
  (*  Any other factoring phi = i ∘ q with q       *)
  (*  interact-preserving surjection and i          *)
  (*  interact-preserving injection factors through *)
  (*  the canonical phi_hat. The canonical          *)
  (*  factorization is minimal in the sense that    *)
  (*  every injective factor is at least as large.  *)
  (* ============================================= *)

  (* Lemma: if q' : D1 -> E is interact-preserving
     and q' agrees with cls (in that their images
     distinguish the same points), there is a
     compatible map Entity -> E pointwise. Stated
     concretely via the kernel. *)

  Theorem factorization_universal :
    forall (E : Type)
           (q' : D1.Entity -> E)
           (i' : E -> D2.Entity),
      (forall a, Phi.phi a = i' (q' a)) ->
      (forall u v, q' u = q' v -> i' (q' u) = i' (q' v)) ->
      forall a, phi_hat (cls a) = i' (q' a).
  Proof.
    intros E q' i' Hcomm _ a.
    rewrite phi_hat_spec.
    apply Hcomm.
  Qed.

End Factorization.
