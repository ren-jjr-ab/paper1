(* ========================================== *)
(*  ExistenceMorphism                          *)
(*                                             *)
(*  Maps between ExistenceSig instances.       *)
(*                                             *)
(*  A morphism preserves the primary           *)
(*  primitive — interact — and nothing more.   *)
(*  collapse is secondary in the          *)
(*  framework (four axioms govern interact;    *)
(*  one relative axiom ties collapse to   *)
(*  interact), and the morphism definition     *)
(*  reflects that asymmetry. Convention        *)
(*  handling is layered on top as optional     *)
(*  strengthening.                             *)
(*                                             *)
(*  Three main observations captured here:     *)
(*                                             *)
(*    1. Interact preservation carries every   *)
(*       projection-agreement from source to   *)
(*       target. If a and b agree at some      *)
(*       viewpoint in the source, their        *)
(*       images agree at the corresponding     *)
(*       image-viewpoint in the target.        *)
(*                                             *)
(*    2. Injective morphisms carry             *)
(*       projection distinctly: agreement      *)
(*       lifts, and source distinctness        *)
(*       survives in the target.               *)
(*                                             *)
(*    3. Injective morphisms REFLECT target    *)
(*       collapse back into source        *)
(*       observational-inequality. What the    *)
(*       target convention forbids every       *)
(*       interaction to witness, the source    *)
(*       already forbids one layer up.         *)
(*                                             *)
(*  Non-injective direction — creating new     *)
(*  target convention by collapsing source     *)
(*  distinctions — is the quotient             *)
(*  construction, kept in a separate file.     *)
(* ========================================== *)

Require Import Existence.


(* ================================================ *)
(*  IDENTITY (single-instance)                       *)
(* ================================================ *)

Module Identity (D : ExistenceSig).
  Import D.

  Definition id : Entity -> Entity := fun x => x.

  Theorem id_preserves_interact :
    forall a b, id (interact a b) = interact (id a) (id b).
  Proof. intros. unfold id. reflexivity. Qed.

  (* Identity preserves convention trivially. *)

  Theorem id_preserves_convention :
    forall a b, collapse a b -> collapse (id a) (id b).
  Proof. intros a b H. unfold id. exact H. Qed.

  (* Identity is faithful (image agreement = source
     agreement, by definition). *)

  Theorem id_faithful :
    forall a b c : Entity,
      interact (id a) (id c) <> interact (id b) (id c) ->
      interact a c <> interact b c.
  Proof. intros a b c. unfold id. intros H; exact H. Qed.

  (* Identity is observational. *)

  Theorem id_observational :
    forall a b c : Entity,
      interact (id (interact a b)) c =
      interact (interact (id a) (id b)) c.
  Proof. intros. unfold id. reflexivity. Qed.

  (* Identity is its own inverse — it is an isomorphism. *)

  Theorem id_is_iso :
    exists psi : Entity -> Entity,
      (forall a b, id (interact a b) = interact (id a) (id b)) /\
      (forall a, psi (id a) = a) /\
      (forall b, id (psi b) = b).
  Proof.
    exists id. repeat split; intros; unfold id; reflexivity.
  Qed.

End Identity.


(* ================================================ *)
(*  MORPHISM (two instances)                         *)
(* ================================================ *)

Module Make (D1 D2 : ExistenceSig).

  (* ============================================= *)
  (*  BASIC DEFINITIONS                            *)
  (* ============================================= *)

  Definition preserves_interact
    (phi : D1.Entity -> D2.Entity) : Prop :=
    forall a b : D1.Entity,
      phi (D1.interact a b) = D2.interact (phi a) (phi b).

  Definition injective
    (phi : D1.Entity -> D2.Entity) : Prop :=
    forall a b : D1.Entity, phi a = phi b -> a = b.

  (* ============================================= *)
  (*  SELF-INTERACTION IS AUTOMATIC                *)
  (*                                               *)
  (*  interact_self survives morphism without any  *)
  (*  extra clause in the definition.              *)
  (* ============================================= *)

  Theorem morphism_fixes_self :
    forall phi,
      preserves_interact phi ->
      forall a, D2.interact (phi a) (phi a) = phi a.
  Proof.
    intros phi Hphi a.
    rewrite <- (Hphi a a).
    rewrite D1.interact_self.
    reflexivity.
  Qed.

  (* ============================================= *)
  (*  CARRYING AGREEMENT                           *)
  (*                                               *)
  (*  If a and b agree at viewpoint c in D1,       *)
  (*  their images agree at phi(c) in D2. This is  *)
  (*  the core movement lemma — every later        *)
  (*  theorem about paper_projection builds on it. *)
  (* ============================================= *)

  Theorem morphism_carries_agreement :
    forall phi,
      preserves_interact phi ->
      forall a b c : D1.Entity,
        D1.interact a c = D1.interact b c ->
        D2.interact (phi a) (phi c) = D2.interact (phi b) (phi c).
  Proof.
    intros phi Hphi a b c Hagree.
    rewrite <- (Hphi a c).
    rewrite <- (Hphi b c).
    f_equal. exact Hagree.
  Qed.

  (* ============================================= *)
  (*  PAPER-LEVEL TRANSLATION                      *)
  (*                                               *)
  (*  paper_equiv is just entity equality, so any  *)
  (*  function carries it. paper_projection may    *)
  (*  survive or collapse depending on whether     *)
  (*  the morphism distinguishes phi(a) from       *)
  (*  phi(b).                                      *)
  (* ============================================= *)

  Theorem morphism_preserves_paper_equiv :
    forall (phi : D1.Entity -> D2.Entity) (a b : D1.Entity),
      a = b -> phi a = phi b.
  Proof.
    intros phi a b Heq. rewrite Heq. reflexivity.
  Qed.

  Theorem injective_morphism_preserves_projection :
    forall phi,
      preserves_interact phi -> injective phi ->
      forall a b : D1.Entity,
        a <> b ->
        forall c,
          D1.interact a c = D1.interact b c ->
          (exists c', D2.interact (phi a) c' = D2.interact (phi b) c')
          /\ phi a <> phi b.
  Proof.
    intros phi Hphi Hinj a b Hne c Hagree.
    split.
    - exists (phi c).
      apply (morphism_carries_agreement phi Hphi a b c Hagree).
    - intros Hfeq. apply Hne. apply Hinj. exact Hfeq.
  Qed.

  (* ============================================= *)
  (*  CONVENTION REFLECTION                        *)
  (*                                               *)
  (*  Core observation. Under an injective         *)
  (*  interact-preserving morphism, target         *)
  (*  collapse forces source observational    *)
  (*  inequality: no D1 viewpoint can witness      *)
  (*  agreement between a and b.                   *)
  (*                                               *)
  (*  Classical reading: if two objects are        *)
  (*  "the same up to convention" in D2, their     *)
  (*  pre-images in D1 are as interaction-         *)
  (*  distinct as D1 allows. What classical math   *)
  (*  calls an "equivalence class identification"  *)
  (*  is, in this framework, exactly D2's          *)
  (*  collapse sitting on top of D1's         *)
  (*  observational inequality.                    *)
  (* ============================================= *)

  Theorem injective_morphism_reflects_convention :
    forall phi,
      preserves_interact phi -> injective phi ->
      forall a b : D1.Entity,
        D2.collapse (phi a) (phi b) ->
        forall c : D1.Entity,
          D1.interact a c <> D1.interact b c.
  Proof.
    intros phi Hphi Hinj a b Hconv c Heq.
    apply (D2.interaction_cannot_witness_collapse
             (phi a) (phi b) Hconv (phi c)).
    apply (morphism_carries_agreement phi Hphi a b c Heq).
  Qed.

  (* Immediate corollary: convention-equated images
     come from distinct sources. *)

  Theorem injective_morphism_convention_distinct :
    forall phi,
      preserves_interact phi -> injective phi ->
      forall a b : D1.Entity,
        D2.collapse (phi a) (phi b) ->
        a <> b.
  Proof.
    intros phi Hphi Hinj a b Hconv Heq.
    subst b.
    apply (injective_morphism_reflects_convention
             phi Hphi Hinj a a Hconv a).
    reflexivity.
  Qed.

  (* ============================================= *)
  (*  CONVENTION PRESERVATION                      *)
  (*                                               *)
  (*  Dual of convention reflection. Forward       *)
  (*  direction — source collapse carries to  *)
  (*  target. Unlike reflection (target → source,  *)
  (*  derivable from injective + preserves_interact*)
  (*  via morphism_carries_agreement), preservation*)
  (*  is NOT automatic: target may contain         *)
  (*  viewpoints outside phi's image at which      *)
  (*  phi(a) and phi(b) agree, even when source    *)
  (*  convention forbids agreement at every        *)
  (*  source-derived viewpoint. Exposed as a       *)
  (*  separate property; instances assert it       *)
  (*  explicitly when it holds.                    *)
  (*                                               *)
  (*  Note on framework scope: a bare              *)
  (*  preserves_convention proof cannot be         *)
  (*  discharged at signature level — collapse*)
  (*  is an opaque Parameter with no constructor.  *)
  (*  Each instance's collapse has its own    *)
  (*  witness form, and the instance's morphism    *)
  (*  author proves preservation against that form.*)
  (* ============================================= *)

  Definition preserves_convention
    (phi : D1.Entity -> D2.Entity) : Prop :=
    forall a b : D1.Entity,
      D1.collapse a b -> D2.collapse (phi a) (phi b).

  Definition full_morphism
    (phi : D1.Entity -> D2.Entity) : Prop :=
    preserves_interact phi /\ preserves_convention phi.

  (* Source convention pair survives as target distinct
     pair under preservation. *)

  Theorem preserves_convention_distinct :
    forall phi a b,
      preserves_convention phi ->
      D1.collapse a b ->
      phi a <> phi b.
  Proof.
    intros phi a b Hpres Hconv Heq.
    apply (D2.interaction_cannot_witness_collapse
             (phi a) (phi b) (Hpres a b Hconv) (phi a)).
    rewrite <- Heq. reflexivity.
  Qed.

  (* Convention-pair's disagreement lifts to the image
     of every source viewpoint, without needing
     preserves_convention — only preserves_interact and
     injectivity. This is the "image-level" half of
     what full preservation would give. *)

  Theorem injective_preserves_convention_in_image :
    forall phi,
      preserves_interact phi -> injective phi ->
      forall a b c : D1.Entity,
        D1.collapse a b ->
        D2.interact (phi a) (phi c) <> D2.interact (phi b) (phi c).
  Proof.
    intros phi Hphi Hinj a b c Hconv Heq.
    rewrite <- (Hphi a c) in Heq.
    rewrite <- (Hphi b c) in Heq.
    apply Hinj in Heq.
    exact (D1.interaction_cannot_witness_collapse a b Hconv c Heq).
  Qed.

  (* Projections from full_morphism. *)

  Theorem full_morphism_preserves_interact :
    forall phi, full_morphism phi -> preserves_interact phi.
  Proof. intros phi [H _]. exact H. Qed.

  Theorem full_morphism_preserves_convention :
    forall phi, full_morphism phi -> preserves_convention phi.
  Proof. intros phi [_ H]. exact H. Qed.

  (* ============================================= *)
  (*  FAITHFULNESS                                 *)
  (*                                               *)
  (*  A morphism is faithful when target           *)
  (*  disagreement reflects back to source         *)
  (*  disagreement. Equivalently, morphism         *)
  (*  agreement is "if and only if" at the         *)
  (*  image of any viewpoint.                      *)
  (*                                               *)
  (*  Under strict preservation, faithfulness is   *)
  (*  automatic via the contrapositive of          *)
  (*  morphism_carries_agreement. Exposed as a     *)
  (*  separate name for clarity of use.            *)
  (* ============================================= *)

  Definition faithful (phi : D1.Entity -> D2.Entity) : Prop :=
    forall a b c : D1.Entity,
      D2.interact (phi a) (phi c) <> D2.interact (phi b) (phi c) ->
      D1.interact a c <> D1.interact b c.

  Theorem preserves_interact_is_faithful :
    forall phi, preserves_interact phi -> faithful phi.
  Proof.
    intros phi Hphi a b c Hne Heq.
    apply Hne.
    apply (morphism_carries_agreement phi Hphi a b c Heq).
  Qed.

  (* ============================================= *)
  (*  KERNEL                                       *)
  (*                                               *)
  (*  The equivalence on D1 that records which     *)
  (*  pairs the morphism fails to distinguish.     *)
  (*  It is interact-compatible automatically      *)
  (*  from preserves_interact, and its triviality  *)
  (*  coincides with phi's injectivity.            *)
  (* ============================================= *)

  Definition morphism_kernel
    (phi : D1.Entity -> D2.Entity)
    (a b : D1.Entity) : Prop :=
    phi a = phi b.

  Theorem kernel_reflexive :
    forall phi a, morphism_kernel phi a a.
  Proof. intros. reflexivity. Qed.

  Theorem kernel_symmetric :
    forall phi a b,
      morphism_kernel phi a b -> morphism_kernel phi b a.
  Proof.
    intros phi a b H. unfold morphism_kernel in *.
    symmetry. exact H.
  Qed.

  Theorem kernel_transitive :
    forall phi a b c,
      morphism_kernel phi a b ->
      morphism_kernel phi b c ->
      morphism_kernel phi a c.
  Proof.
    intros phi a b c H1 H2. unfold morphism_kernel in *.
    rewrite H1. exact H2.
  Qed.

  (* preserves_interact already makes the kernel
     respect the framework's primary operation.
     Quotient by this relation is well-defined at
     the interact level. *)

  Theorem kernel_respects_interact :
    forall phi,
      preserves_interact phi ->
      forall a b c : D1.Entity,
        morphism_kernel phi a b ->
        morphism_kernel phi
          (D1.interact a c) (D1.interact b c).
  Proof.
    intros phi Hphi a b c Hker.
    unfold morphism_kernel in *.
    rewrite (Hphi a c).
    rewrite (Hphi b c).
    f_equal. exact Hker.
  Qed.

  Theorem injective_iff_trivial_kernel :
    forall phi,
      injective phi <->
      (forall a b, morphism_kernel phi a b -> a = b).
  Proof.
    intros phi. split.
    - intros Hinj a b Hker. apply Hinj. exact Hker.
    - intros Htriv a b Heq. apply Htriv. exact Heq.
  Qed.

  (* ============================================= *)
  (*  COLLAPSE                                     *)
  (*                                               *)
  (*  A non-injective morphism has at least one    *)
  (*  distinct source pair that the morphism       *)
  (*  identifies. We expose this as the explicit   *)
  (*  witness `has_collapse`, which is the         *)
  (*  constructive dual of `injective`: injective  *)
  (*  rules out any collapse pair; has_collapse    *)
  (*  exhibits one.                                *)
  (*                                               *)
  (*  The central structural observation: every    *)
  (*  collapse pair upgrades in the target — what  *)
  (*  was paper_projection (or any distinct pair)  *)
  (*  in the source becomes paper_equiv at the     *)
  (*  target, and the distinction is lost.         *)
  (* ============================================= *)

  Definition has_collapse
    (phi : D1.Entity -> D2.Entity) : Prop :=
    exists a b, a <> b /\ phi a = phi b.

  Theorem has_collapse_not_injective :
    forall phi,
      has_collapse phi -> ~ injective phi.
  Proof.
    intros phi [a [b [Hne Heq]]] Hinj.
    apply Hne. apply Hinj. exact Heq.
  Qed.

  Theorem collapse_upgrades_to_target_equiv :
    forall phi a b,
      morphism_kernel phi a b ->
      phi a = phi b.
  Proof. intros phi a b H. exact H. Qed.

  (* Source distinction + kernel-related is exactly
     the "collapse at this pair" situation. Reading
     it the other way: collapse pairs can come from
     paper_projection (witnessed agreement), from
     paper_convention (if the instance asserts one),
     or from a distinct pair not related through
     either. The morphism does not ask why — only
     that phi collapses them. *)

  Theorem collapse_pair_loses_distinction :
    forall phi a b,
      preserves_interact phi ->
      a <> b ->
      morphism_kernel phi a b ->
      (phi a = phi b) /\
      (forall c, D2.interact (phi a) c =
                 D2.interact (phi b) c).
  Proof.
    intros phi Hphi a b Hne Hker.
    split; [exact Hker |].
    intro c. rewrite Hker. reflexivity.
  Qed.

  (* ============================================= *)
  (*  OBSERVATIONAL MORPHISM                       *)
  (*                                               *)
  (*  A weaker preservation: phi preserves         *)
  (*  interact up to target observation. The two   *)
  (*  candidate outputs, phi(interact a b) and     *)
  (*  interact(phi a)(phi b), may be different     *)
  (*  entities in D2 as long as they act the same  *)
  (*  under every D2 viewpoint.                    *)
  (*                                               *)
  (*  Motivation: strict equality is a very        *)
  (*  strong condition. In many translations       *)
  (*  between axiom systems, the direct image of   *)
  (*  an operation is not literally the            *)
  (*  corresponding target operation — but no      *)
  (*  observer in the target can distinguish the   *)
  (*  two. This is the framework's native way of   *)
  (*  expressing what classical abstraction calls  *)
  (*  "sound but not complete": correct under all  *)
  (*  observation, without being exact.            *)
  (* ============================================= *)

  Definition observational_morphism
    (phi : D1.Entity -> D2.Entity) : Prop :=
    forall (a b : D1.Entity) (c : D2.Entity),
      D2.interact (phi (D1.interact a b)) c =
      D2.interact (D2.interact (phi a) (phi b)) c.

  Theorem preserves_interact_is_observational :
    forall phi,
      preserves_interact phi -> observational_morphism phi.
  Proof.
    intros phi Hphi a b c. rewrite Hphi. reflexivity.
  Qed.

  (* Agreement carries at observational level. *)

  Theorem observational_carries_agreement :
    forall phi,
      observational_morphism phi ->
      forall a b c : D1.Entity,
        D1.interact a c = D1.interact b c ->
        forall c' : D2.Entity,
          D2.interact (D2.interact (phi a) (phi c)) c' =
          D2.interact (D2.interact (phi b) (phi c)) c'.
  Proof.
    intros phi Hobs a b c Hagree c'.
    rewrite <- (Hobs a c c').
    rewrite <- (Hobs b c c').
    f_equal. f_equal. exact Hagree.
  Qed.

  (* Self-fixing weakens to observational form. *)

  Theorem observational_fixes_self :
    forall phi,
      observational_morphism phi ->
      forall (a : D1.Entity) (c : D2.Entity),
        D2.interact (phi a) c =
        D2.interact (D2.interact (phi a) (phi a)) c.
  Proof.
    intros phi Hobs a c.
    rewrite <- (Hobs a a c).
    rewrite D1.interact_self.
    reflexivity.
  Qed.

  (* ============================================= *)
  (*  EXTENSIONALITY BRIDGES OBSERVATIONAL AND     *)
  (*  STRICT                                       *)
  (*                                               *)
  (*  When the target has no observationally       *)
  (*  equivalent distinct pair, observational      *)
  (*  morphism collapses back into strict          *)
  (*  preservation. This is the framework-native   *)
  (*  description of the exact-vs-approximate      *)
  (*  gap: the gap is exactly D2's failure of      *)
  (*  extensionality.                              *)
  (*                                               *)
  (*  Under target extensionality, every           *)
  (*  observational result — including convention  *)
  (*  reflection — recovers its strict form.       *)
  (* ============================================= *)

  Definition target_extensional : Prop :=
    forall a b : D2.Entity,
      (forall c : D2.Entity, D2.interact a c = D2.interact b c) ->
      a = b.

  Theorem observational_to_strict_if_extensional :
    target_extensional ->
    forall phi,
      observational_morphism phi -> preserves_interact phi.
  Proof.
    intros Hext phi Hobs a b.
    apply Hext. intro c.
    exact (Hobs a b c).
  Qed.

  (* ============================================= *)
  (*  ISOMORPHISM                                  *)
  (*                                               *)
  (*  phi is an isomorphism when it has a two-     *)
  (*  sided inverse psi. The inverse's interact    *)
  (*  preservation is automatic (derived below);   *)
  (*  convention preservation of the inverse is    *)
  (*  NOT automatic, since collapse is opaque *)
  (*  at signature level. A full iso bundles       *)
  (*  convention preservation in both directions.  *)
  (* ============================================= *)

  Definition is_iso (phi : D1.Entity -> D2.Entity) : Prop :=
    exists psi : D2.Entity -> D1.Entity,
      preserves_interact phi /\
      (forall a : D1.Entity, psi (phi a) = a) /\
      (forall b : D2.Entity, phi (psi b) = b).

  (* The inverse of an iso is itself interact-preserving.
     No additional hypothesis needed — follows from phi's
     preservation and the two inverse laws. *)

  Theorem iso_inverse_preserves_interact :
    forall (phi : D1.Entity -> D2.Entity)
           (psi : D2.Entity -> D1.Entity),
      preserves_interact phi ->
      (forall a : D1.Entity, psi (phi a) = a) ->
      (forall b : D2.Entity, phi (psi b) = b) ->
      forall b1 b2 : D2.Entity,
        psi (D2.interact b1 b2) = D1.interact (psi b1) (psi b2).
  Proof.
    intros phi psi Hphi Hleft Hright b1 b2.
    pose proof (Hphi (psi b1) (psi b2)) as H.
    rewrite (Hright b1) in H.
    rewrite (Hright b2) in H.
    rewrite <- H.
    apply Hleft.
  Qed.

  Theorem iso_injective :
    forall phi, is_iso phi -> injective phi.
  Proof.
    intros phi [psi [_ [Hleft _]]].
    intros a b Heq.
    rewrite <- (Hleft a).
    rewrite <- (Hleft b).
    rewrite Heq.
    reflexivity.
  Qed.

  Theorem iso_surjective :
    forall phi,
      is_iso phi ->
      forall b : D2.Entity, exists a : D1.Entity, phi a = b.
  Proof.
    intros phi [psi [_ [_ Hright]]] b.
    exists (psi b). apply Hright.
  Qed.

  (* ============================================= *)
  (*  FULL ISOMORPHISM                             *)
  (*                                               *)
  (*  Iso bundled with convention preservation in  *)
  (*  both directions. Convention preservation is  *)
  (*  not derivable from interact-preserving       *)
  (*  inverse (collapse is opaque), so it is  *)
  (*  explicit in the bundle.                      *)
  (* ============================================= *)

  Definition is_full_iso (phi : D1.Entity -> D2.Entity) : Prop :=
    exists psi : D2.Entity -> D1.Entity,
      preserves_interact phi /\
      preserves_convention phi /\
      (forall a : D1.Entity, psi (phi a) = a) /\
      (forall b : D2.Entity, phi (psi b) = b) /\
      (forall b1 b2 : D2.Entity,
         D2.collapse b1 b2 ->
         D1.collapse (psi b1) (psi b2)).

  Theorem full_iso_is_iso :
    forall phi, is_full_iso phi -> is_iso phi.
  Proof.
    intros phi [psi [Hphi [_ [Hleft [Hright _]]]]].
    exists psi.
    exact (conj Hphi (conj Hleft Hright)).
  Qed.

End Make.


(* ================================================ *)
(*  COMPOSITION (three instances)                    *)
(*                                                   *)
(*  Chain of two morphisms is a morphism.            *)
(*  "Translation across axiom systems" composes.     *)
(* ================================================ *)

Module Compose (D1 D2 D3 : ExistenceSig).

  Definition compose
    (psi : D2.Entity -> D3.Entity)
    (phi : D1.Entity -> D2.Entity) : D1.Entity -> D3.Entity :=
    fun x => psi (phi x).

  Theorem compose_preserves_interact :
    forall (psi : D2.Entity -> D3.Entity)
           (phi : D1.Entity -> D2.Entity),
      (forall a b,
        phi (D1.interact a b) = D2.interact (phi a) (phi b)) ->
      (forall a b,
        psi (D2.interact a b) = D3.interact (psi a) (psi b)) ->
      forall a b,
        compose psi phi (D1.interact a b) =
        D3.interact (compose psi phi a) (compose psi phi b).
  Proof.
    intros psi phi Hphi Hpsi a b.
    unfold compose. rewrite Hphi. rewrite Hpsi. reflexivity.
  Qed.

  Theorem compose_preserves_injective :
    forall (psi : D2.Entity -> D3.Entity)
           (phi : D1.Entity -> D2.Entity),
      (forall a b, phi a = phi b -> a = b) ->
      (forall a b, psi a = psi b -> a = b) ->
      forall a b,
        compose psi phi a = compose psi phi b -> a = b.
  Proof.
    intros psi phi Hphi_inj Hpsi_inj a b Heq.
    unfold compose in Heq.
    apply Hphi_inj. apply Hpsi_inj. exact Heq.
  Qed.

  (* Convention preservation composes. *)

  Theorem compose_preserves_convention :
    forall (psi : D2.Entity -> D3.Entity)
           (phi : D1.Entity -> D2.Entity),
      (forall a b, D1.collapse a b ->
                   D2.collapse (phi a) (phi b)) ->
      (forall a b, D2.collapse a b ->
                   D3.collapse (psi a) (psi b)) ->
      forall a b,
        D1.collapse a b ->
        D3.collapse (compose psi phi a) (compose psi phi b).
  Proof.
    intros psi phi Hphi Hpsi a b Hconv.
    unfold compose.
    apply Hpsi. apply Hphi. exact Hconv.
  Qed.

  (* Faithfulness composes: target disagreement reflects
     back through both layers. *)

  Theorem compose_preserves_faithful :
    forall (psi : D2.Entity -> D3.Entity)
           (phi : D1.Entity -> D2.Entity),
      (forall a b c : D1.Entity,
         D2.interact (phi a) (phi c) <> D2.interact (phi b) (phi c) ->
         D1.interact a c <> D1.interact b c) ->
      (forall a b c : D2.Entity,
         D3.interact (psi a) (psi c) <> D3.interact (psi b) (psi c) ->
         D2.interact a c <> D2.interact b c) ->
      forall a b c : D1.Entity,
        D3.interact (compose psi phi a) (compose psi phi c) <>
        D3.interact (compose psi phi b) (compose psi phi c) ->
        D1.interact a c <> D1.interact b c.
  Proof.
    intros psi phi Hphi Hpsi a b c Hne.
    apply Hphi. apply (Hpsi (phi a) (phi b) (phi c)). exact Hne.
  Qed.

  (* Observational preservation composes when the inner
     morphism is strict. Pure observational × observational
     does not compose straightforwardly; the strict inner
     layer eliminates the gap. *)

  Theorem compose_strict_then_observational :
    forall (psi : D2.Entity -> D3.Entity)
           (phi : D1.Entity -> D2.Entity),
      (forall a b,
        phi (D1.interact a b) = D2.interact (phi a) (phi b)) ->
      (forall a b c,
         D3.interact (psi (D2.interact a b)) c =
         D3.interact (D3.interact (psi a) (psi b)) c) ->
      forall a b c,
        D3.interact (compose psi phi (D1.interact a b)) c =
        D3.interact
          (D3.interact (compose psi phi a) (compose psi phi b)) c.
  Proof.
    intros psi phi Hphi Hpsi a b c.
    unfold compose. rewrite Hphi. apply Hpsi.
  Qed.

  (* Reverse-order composition — the type of an iso's
     inverse. psi : D2→D3, phi : D1→D2 compose to
     D1→D3; their inverses psi_inv : D3→D2, phi_inv :
     D2→D1 compose to D3→D1 in reverse order. *)

  Definition compose_inv
    (psi_inv : D3.Entity -> D2.Entity)
    (phi_inv : D2.Entity -> D1.Entity) : D3.Entity -> D1.Entity :=
    fun x => phi_inv (psi_inv x).

  (* Composition of isomorphisms is an isomorphism.
     The inverse of the composite is the composite of
     the inverses (in reverse order). *)

  Theorem compose_of_iso_is_iso :
    forall (psi : D2.Entity -> D3.Entity)
           (phi : D1.Entity -> D2.Entity)
           (psi_inv : D3.Entity -> D2.Entity)
           (phi_inv : D2.Entity -> D1.Entity),
      (* psi iso with inverse psi_inv *)
      (forall a b, psi (D2.interact a b) =
                   D3.interact (psi a) (psi b)) ->
      (forall a, psi_inv (psi a) = a) ->
      (forall b, psi (psi_inv b) = b) ->
      (* phi iso with inverse phi_inv *)
      (forall a b, phi (D1.interact a b) =
                   D2.interact (phi a) (phi b)) ->
      (forall a, phi_inv (phi a) = a) ->
      (forall b, phi (phi_inv b) = b) ->
      (* compose psi phi is iso with compose_inv psi_inv phi_inv *)
      (forall a b, compose psi phi (D1.interact a b) =
                   D3.interact (compose psi phi a)
                               (compose psi phi b)) /\
      (forall a, compose_inv psi_inv phi_inv (compose psi phi a) = a) /\
      (forall b, compose psi phi (compose_inv psi_inv phi_inv b) = b).
  Proof.
    intros psi phi psi_inv phi_inv Hpsi Hpsi_l Hpsi_r Hphi Hphi_l Hphi_r.
    split; [|split].
    - apply compose_preserves_interact; assumption.
    - intros a. unfold compose, compose_inv.
      rewrite Hpsi_l. apply Hphi_l.
    - intros b. unfold compose, compose_inv.
      rewrite Hphi_r. apply Hpsi_r.
  Qed.

End Compose.
