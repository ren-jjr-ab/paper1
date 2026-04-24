(* ========================================== *)
(*  ExistencePushout                           *)
(*                                             *)
(*  Concrete pushout of a span                 *)
(*                                             *)
(*       Base                                  *)
(*      /    \                                 *)
(*    F1      F2                               *)
(*    v        v                               *)
(*   D1        D2                              *)
(*                                             *)
(*  Construction:                              *)
(*   - FreeWord: free algebra over             *)
(*     D1.Entity + D2.Entity under a binary    *)
(*     operator Mul.                           *)
(*   - equiv: the smallest equivalence closed  *)
(*     under Mul congruence, interact_self,    *)
(*     base identification, and F1 / F2        *)
(*     preservation.                           *)
(*   - Entity: the quotient FreeWord / equiv.  *)
(*                                             *)
(*  Quotient type is not primitive in Coq,     *)
(*  so a single meta-level axiom introduces    *)
(*  quotient structure for any equivalence     *)
(*  relation. Everything else — the 5          *)
(*  ExistenceSig axioms where they hold, the   *)
(*  injections, the universal factoring arrow  *)
(*  — is proved.                               *)
(*                                             *)
(*  The 3 span-dependent ExistenceSig axioms   *)
(*  (existence, interact_with,                 *)
(*  interact_decidable) are NOT included in    *)
(*  Construction, because they are not facts   *)
(*  about the construction — they are facts    *)
(*  about the span. A span that collapses      *)
(*  both legs to a single point produces a     *)
(*  one-class quotient and fails all three.    *)
(*  Users apply Construction to their span     *)
(*  and discharge these separately at use      *)
(*  site.                                      *)
(* ========================================== *)

Require Import Existence.
Require Import Morphism.
Require Import Pullback.


(* ================================================ *)
(*  QUOTIENT INFRASTRUCTURE (ONE META AXIOM)         *)
(*                                                   *)
(*  Coq's base theory has no quotient-type           *)
(*  constructor. We introduce one meta-axiom         *)
(*  asserting that every equivalence relation        *)
(*  admits a quotient with projection, surjectivity, *)
(*  and a binary lift universal property.            *)
(*                                                   *)
(*  This is the only place in the framework where    *)
(*  a postulate beyond the five ExistenceSig axioms  *)
(*  is used. It is marked as explicit axiom, not     *)
(*  hidden as Parameter.                             *)
(* ================================================ *)

Record QuotientStructure (A : Type) (R : A -> A -> Prop) : Type := {
  qcarrier : Type;
  qcls : A -> qcarrier;
  qcls_correct :
    forall u v : A, qcls u = qcls v <-> R u v;
  qcls_surjective :
    forall q : qcarrier, exists w : A, qcls w = q;
  qlift2 :
    forall (B : Type) (f : A -> A -> B),
      (forall u u' v v',
         R u u' -> R v v' -> f u v = f u' v') ->
      { lifted : qcarrier -> qcarrier -> B
      | forall u v : A, lifted (qcls u) (qcls v) = f u v };
  qlift1 :
    forall (B : Type) (f : A -> B),
      (forall u v : A, R u v -> f u = f v) ->
      { lifted : qcarrier -> B
      | forall w : A, lifted (qcls w) = f w }
}.

Axiom quotient_exists :
  forall (A : Type) (R : A -> A -> Prop),
    (forall x, R x x) ->
    (forall x y, R x y -> R y x) ->
    (forall x y z, R x y -> R y z -> R x z) ->
    QuotientStructure A R.


(* ================================================ *)
(*  CONSTRUCTION                                     *)
(* ================================================ *)

Module Construction
  (Base D1 D2 : ExistenceSig)
  (F1 : MorphismInto Base D1)
  (F2 : MorphismInto Base D2).

  (* ============================================= *)
  (*  FREE WORD                                    *)
  (* ============================================= *)

  Inductive FreeWord : Type :=
    | Gen1 : D1.Entity -> FreeWord
    | Gen2 : D2.Entity -> FreeWord
    | Mul  : FreeWord -> FreeWord -> FreeWord.

  (* ============================================= *)
  (*  EQUIVALENCE                                  *)
  (* ============================================= *)

  Inductive equiv : FreeWord -> FreeWord -> Prop :=
    | e_refl : forall w, equiv w w
    | e_sym  : forall u v, equiv u v -> equiv v u
    | e_trans : forall u v w,
        equiv u v -> equiv v w -> equiv u w

    | e_self : forall w, equiv (Mul w w) w

    | e_base : forall b : Base.Entity,
        equiv (Gen1 (F1.phi b)) (Gen2 (F2.phi b))

    | e_pres1 : forall x y : D1.Entity,
        equiv (Gen1 (D1.interact x y))
              (Mul (Gen1 x) (Gen1 y))

    | e_pres2 : forall x y : D2.Entity,
        equiv (Gen2 (D2.interact x y))
              (Mul (Gen2 x) (Gen2 y))

    | e_cong : forall u u' v v',
        equiv u u' -> equiv v v' ->
        equiv (Mul u v) (Mul u' v').

  Lemma equiv_refl : forall w, equiv w w.
  Proof. exact e_refl. Qed.

  Lemma equiv_sym : forall u v, equiv u v -> equiv v u.
  Proof. exact e_sym. Qed.

  Lemma equiv_trans :
    forall u v w, equiv u v -> equiv v w -> equiv u w.
  Proof. exact e_trans. Qed.

  (* ============================================= *)
  (*  QUOTIENT                                     *)
  (* ============================================= *)

  Definition Q : QuotientStructure FreeWord equiv :=
    quotient_exists FreeWord equiv equiv_refl equiv_sym equiv_trans.

  Definition Entity : Type := qcarrier _ _ Q.
  Definition cls : FreeWord -> Entity := qcls _ _ Q.

  Lemma cls_correct :
    forall u v, cls u = cls v <-> equiv u v.
  Proof. exact (qcls_correct _ _ Q). Qed.

  Lemma cls_surjective :
    forall q : Entity, exists w, cls w = q.
  Proof. exact (qcls_surjective _ _ Q). Qed.

  Definition Quot_rec
    {B : Type} (f : FreeWord -> B)
    (Hwd : forall u v, equiv u v -> f u = f v)
    : Entity -> B :=
    proj1_sig (qlift1 _ _ Q B f Hwd).

  Lemma Quot_rec_spec :
    forall {B : Type} (f : FreeWord -> B) Hwd w,
      Quot_rec f Hwd (cls w) = f w.
  Proof.
    intros B f Hwd w. unfold Quot_rec.
    destruct (qlift1 _ _ Q B f Hwd) as [lifted Hlift].
    simpl. apply Hlift.
  Qed.

  (* ============================================= *)
  (*  INTERACT                                     *)
  (* ============================================= *)

  Lemma Mul_respects_equiv :
    forall u u' v v',
      equiv u u' -> equiv v v' ->
      equiv (Mul u v) (Mul u' v').
  Proof. exact e_cong. Qed.

  Definition Mul_lift_fun (u v : FreeWord) : Entity := cls (Mul u v).

  Lemma Mul_lift_fun_respects :
    forall u u' v v',
      equiv u u' -> equiv v v' ->
      Mul_lift_fun u v = Mul_lift_fun u' v'.
  Proof.
    intros u u' v v' Hu Hv. unfold Mul_lift_fun.
    apply cls_correct. apply e_cong; assumption.
  Qed.

  Definition interact : Entity -> Entity -> Entity :=
    proj1_sig (qlift2 _ _ Q Entity Mul_lift_fun Mul_lift_fun_respects).

  Lemma interact_spec :
    forall u v : FreeWord,
      interact (cls u) (cls v) = cls (Mul u v).
  Proof.
    intros u v. unfold interact.
    destruct (qlift2 _ _ Q Entity Mul_lift_fun Mul_lift_fun_respects)
      as [lifted Hlift].
    simpl. unfold Mul_lift_fun in Hlift. apply Hlift.
  Qed.

  (* ============================================= *)
  (*  CONVENTION_EQ                                *)
  (*                                               *)
  (*  Defined as False — the Construction          *)
  (*  introduces no convention beyond what the     *)
  (*  span contributes via interaction. This is    *)
  (*  a design choice.                             *)
  (*                                               *)
  (*  Consequences:                                *)
  (*                                               *)
  (*  - interaction_cannot_witness_collapse holds vacuously.  *)
  (*  - Morphisms into the pushout cannot carry    *)
  (*    source conventions — source conventions    *)
  (*    are either identified by the span's       *)
  (*    equiv relation or simply unreflected at    *)
  (*    the target.                                *)
  (*  - Instances needing target-level convention  *)
  (*    compose Construction with an additional    *)
  (*    post-quotient that installs collapse  *)
  (*    explicitly.                                *)
  (* ============================================= *)

  Definition collapse (_ _ : Entity) : Prop := False.

  (* ============================================= *)
  (*  interact_self (PROVED)                       *)
  (* ============================================= *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a.
    destruct (cls_surjective a) as [w Hw].
    rewrite <- Hw.
    rewrite interact_spec.
    apply cls_correct. apply e_self.
  Qed.

  (* ============================================= *)
  (*  interaction_cannot_witness_collapse (PROVED, VACUOUS)   *)
  (* ============================================= *)

  Theorem interaction_cannot_witness_collapse :
    forall a b : Entity,
      collapse a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof.
    intros a b Hconv. unfold collapse in Hconv. destruct Hconv.
  Qed.

  (* ============================================= *)
  (*  INJECTIONS                                   *)
  (* ============================================= *)

  Definition inj1 (x : D1.Entity) : Entity := cls (Gen1 x).
  Definition inj2 (y : D2.Entity) : Entity := cls (Gen2 y).

  Theorem inj1_preserves_interact :
    forall a b : D1.Entity,
      inj1 (D1.interact a b) = interact (inj1 a) (inj1 b).
  Proof.
    intros a b. unfold inj1.
    rewrite interact_spec.
    apply cls_correct. apply e_pres1.
  Qed.

  Theorem inj2_preserves_interact :
    forall a b : D2.Entity,
      inj2 (D2.interact a b) = interact (inj2 a) (inj2 b).
  Proof.
    intros a b. unfold inj2.
    rewrite interact_spec.
    apply cls_correct. apply e_pres2.
  Qed.

  Theorem base_identification :
    forall b : Base.Entity,
      inj1 (F1.phi b) = inj2 (F2.phi b).
  Proof.
    intros b. unfold inj1, inj2.
    apply cls_correct. apply e_base.
  Qed.

  (* ============================================= *)
  (*  UNIVERSAL PROPERTY                           *)
  (*                                               *)
  (*  Given a third ExistenceSig instance D3 and   *)
  (*  morphisms psi1 : D1 -> D3, psi2 : D2 -> D3   *)
  (*  that agree on the base (i.e., form a         *)
  (*  cocone), the factoring arrow rho : Entity    *)
  (*  -> D3 exists and is uniquely characterized   *)
  (*  by rho on the injections.                    *)
  (* ============================================= *)

  (* Cocone agreement as a Module Type. Concrete
     users supply an instance by proving the
     agreement as a Theorem and sealing it into a
     Module satisfying CoconeAgreement. This keeps
     the agreement out of the trust base: there is
     no Axiom that Universal accepts without an
     external proof. *)

  Module Type CoconeAgreement
    (D3 : ExistenceSig)
    (Psi1 : MorphismInto D1 D3)
    (Psi2 : MorphismInto D2 D3).
    Axiom agreement :
      forall b : Base.Entity,
        Psi1.phi (F1.phi b) = Psi2.phi (F2.phi b).
  End CoconeAgreement.

  Module Universal
    (D3 : ExistenceSig)
    (Psi1 : MorphismInto D1 D3)
    (Psi2 : MorphismInto D2 D3)
    (A : CoconeAgreement D3 Psi1 Psi2).

    (* interpret: recursive evaluation of a FreeWord
       in D3. *)

    Fixpoint interpret (w : FreeWord) : D3.Entity :=
      match w with
      | Gen1 x => Psi1.phi x
      | Gen2 y => Psi2.phi y
      | Mul u v => D3.interact (interpret u) (interpret v)
      end.

    (* interpret respects equiv — this is the heart
       of the universal property. *)

    Lemma interpret_respects_equiv :
      forall u v : FreeWord, equiv u v -> interpret u = interpret v.
    Proof.
      intros u v H.
      induction H.
      - (* e_refl *)
        reflexivity.
      - (* e_sym *)
        symmetry. exact IHequiv.
      - (* e_trans *)
        rewrite IHequiv1. exact IHequiv2.
      - (* e_self: interpret (Mul w w) = interpret w *)
        simpl. apply D3.interact_self.
      - (* e_base *)
        simpl. apply A.agreement.
      - (* e_pres1 *)
        simpl. apply Psi1.preserves_interact.
      - (* e_pres2 *)
        simpl. apply Psi2.preserves_interact.
      - (* e_cong *)
        simpl. rewrite IHequiv1. rewrite IHequiv2. reflexivity.
    Qed.

    (* The factoring arrow. *)

    Definition rho : Entity -> D3.Entity :=
      Quot_rec interpret interpret_respects_equiv.

    (* rho agrees with psi_i on the injections. *)

    Theorem rho_on_inj1 :
      forall x : D1.Entity, rho (inj1 x) = Psi1.phi x.
    Proof.
      intros x. unfold rho, inj1.
      rewrite Quot_rec_spec. reflexivity.
    Qed.

    Theorem rho_on_inj2 :
      forall y : D2.Entity, rho (inj2 y) = Psi2.phi y.
    Proof.
      intros y. unfold rho, inj2.
      rewrite Quot_rec_spec. reflexivity.
    Qed.

    (* rho preserves interact — the core universal
       property. *)

    Theorem rho_preserves_interact :
      forall a b : Entity,
        rho (interact a b) = D3.interact (rho a) (rho b).
    Proof.
      intros a b.
      destruct (cls_surjective a) as [u Hu].
      destruct (cls_surjective b) as [v Hv].
      rewrite <- Hu. rewrite <- Hv.
      rewrite interact_spec.
      unfold rho. rewrite Quot_rec_spec. rewrite Quot_rec_spec.
      rewrite Quot_rec_spec.
      simpl. reflexivity.
    Qed.

    (* ============================================= *)
    (*  UNIQUENESS                                   *)
    (*                                               *)
    (*  Any other factoring arrow rho' satisfying    *)
    (*  the same three conditions (interact          *)
    (*  preservation + agreement on the two          *)
    (*  injections) agrees pointwise with rho.       *)
    (*                                               *)
    (*  Proof by induction on FreeWord: the three    *)
    (*  conditions determine rho' on generators and  *)
    (*  Mul propagates via preserves_interact.       *)
    (* ============================================= *)

    Theorem rho_unique :
      forall rho' : Entity -> D3.Entity,
        (forall a b, rho' (interact a b) =
                     D3.interact (rho' a) (rho' b)) ->
        (forall x, rho' (inj1 x) = Psi1.phi x) ->
        (forall y, rho' (inj2 y) = Psi2.phi y) ->
        forall e, rho' e = rho e.
    Proof.
      intros rho' Hpres H1 H2 e.
      destruct (cls_surjective e) as [w Hw].
      subst e.
      induction w as [x | y | u IHu v IHv].
      - (* Gen1 x *)
        transitivity (Psi1.phi x).
        + exact (H1 x).
        + symmetry. exact (rho_on_inj1 x).
      - (* Gen2 y *)
        transitivity (Psi2.phi y).
        + exact (H2 y).
        + symmetry. exact (rho_on_inj2 y).
      - (* Mul u v *)
        rewrite <- (interact_spec u v).
        rewrite Hpres.
        rewrite rho_preserves_interact.
        rewrite IHu. rewrite IHv. reflexivity.
    Qed.

    (* Bundled universal property statement. *)

    Theorem pushout_universal :
      exists rho_star : Entity -> D3.Entity,
        (forall a b, rho_star (interact a b) =
                     D3.interact (rho_star a) (rho_star b)) /\
        (forall x, rho_star (inj1 x) = Psi1.phi x) /\
        (forall y, rho_star (inj2 y) = Psi2.phi y) /\
        (forall rho' : Entity -> D3.Entity,
          (forall a b, rho' (interact a b) =
                       D3.interact (rho' a) (rho' b)) ->
          (forall x, rho' (inj1 x) = Psi1.phi x) ->
          (forall y, rho' (inj2 y) = Psi2.phi y) ->
          forall e, rho' e = rho_star e).
    Proof.
      exists rho.
      split; [exact rho_preserves_interact |].
      split; [exact rho_on_inj1 |].
      split; [exact rho_on_inj2 |].
      exact rho_unique.
    Qed.

  End Universal.

End Construction.
