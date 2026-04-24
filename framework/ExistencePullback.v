(* ========================================== *)
(*  ExistencePullback                          *)
(*                                             *)
(*  Two instances D1 and D2 "meet" when they   *)
(*  share a common substrate. Formally: a      *)
(*  base instance Base together with two       *)
(*  morphisms                                  *)
(*                                             *)
(*    F1 : D1 -> Base                          *)
(*    F2 : D2 -> Base                          *)
(*                                             *)
(*  The pullback picks out pairs (a, b) in     *)
(*  D1 x D2 whose images in Base agree:        *)
(*                                             *)
(*    F1.phi a = F2.phi b                      *)
(*                                             *)
(*  Each such pair is a "meeting" — a point    *)
(*  where D1 and D2 reconcile under their      *)
(*  shared encoding. The set of meetings is    *)
(*  closed under coordinate-wise interact:     *)
(*  the joint dynamics of D1 and D2 do not     *)
(*  break reconciliation once it has been      *)
(*  achieved.                                  *)
(*                                             *)
(*  This is the formal correlate of the        *)
(*  intuition that "different axiom systems    *)
(*  meet at some level of encoding". Where     *)
(*  they meet, structure survives the joint    *)
(*  operation.                                 *)
(* ========================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistenceProduct.


(* ================================================ *)
(*  MORPHISM AS A MODULE TYPE                        *)
(*                                                   *)
(*  Needed because Coq module functors take modules  *)
(*  as parameters, not bare functions. Wrapping a    *)
(*  morphism (phi + preserves_interact) in a module  *)
(*  type lets Pullback receive it functorially.      *)
(* ================================================ *)

Module Type MorphismInto (Src Tgt : ExistenceSig).
  Parameter phi : Src.Entity -> Tgt.Entity.
  Axiom preserves_interact :
    forall a b : Src.Entity,
      phi (Src.interact a b) = Tgt.interact (phi a) (phi b).
End MorphismInto.


(* ================================================ *)
(*  IDENTITY MORPHISM (self-to-self)                 *)
(*                                                   *)
(*  Supplied as a concrete MorphismInto for use      *)
(*  with Pullback and other functors that take       *)
(*  morphisms as arguments.                          *)
(* ================================================ *)

Module IdentityInto (D : ExistenceSig) <: MorphismInto D D.
  Definition phi : D.Entity -> D.Entity := fun x => x.
  Theorem preserves_interact :
    forall a b : D.Entity,
      phi (D.interact a b) = D.interact (phi a) (phi b).
  Proof. intros. unfold phi. reflexivity. Qed.
End IdentityInto.


(* ================================================ *)
(*  PULLBACK                                         *)
(* ================================================ *)

Module Pullback (D1 D2 Base : ExistenceSig)
                (F1 : MorphismInto D1 Base)
                (F2 : MorphismInto D2 Base).

  Module P := ExistenceProduct.Make D1 D2.

  (* ============================================= *)
  (*  THE MEETING PREDICATE                        *)
  (*                                               *)
  (*  A pair (a, b) in D1 x D2 is a meeting when   *)
  (*  F1 and F2 send it to the same point in the   *)
  (*  base. The pullback is the collection of      *)
  (*  such pairs.                                  *)
  (* ============================================= *)

  Definition on_pullback (p : P.Entity) : Prop :=
    F1.phi (fst p) = F2.phi (snd p).

  (* The defining commutativity of the pullback
     square — restated for external callers. *)

  Theorem pullback_commutes :
    forall p : P.Entity,
      on_pullback p -> F1.phi (fst p) = F2.phi (snd p).
  Proof. intros p H. exact H. Qed.

  (* ============================================= *)
  (*  MEETINGS ARE STABLE UNDER INTERACT           *)
  (*                                               *)
  (*  If two pairs are both meetings, their joint  *)
  (*  interact is still a meeting. The meeting     *)
  (*  subspace is closed under the framework's     *)
  (*  primary operation — not just a snapshot but  *)
  (*  a structural invariant.                      *)
  (* ============================================= *)

  Theorem interact_preserves_pullback :
    forall a b : P.Entity,
      on_pullback a -> on_pullback b ->
      on_pullback (P.interact a b).
  Proof.
    intros [a1 a2] [b1 b2] Ha Hb.
    unfold on_pullback, P.interact in *. simpl in *.
    rewrite F1.preserves_interact.
    rewrite F2.preserves_interact.
    rewrite Ha, Hb. reflexivity.
  Qed.

  (* ============================================= *)
  (*  SELF-MEETINGS                                *)
  (*                                               *)
  (*  Every diagonal pair (x, y) with F1(x)=F2(y)  *)
  (*  is a meeting; trivially, whenever F1 and F2  *)
  (*  agree on corresponding entities, the pair    *)
  (*  lands in the pullback. In particular, if     *)
  (*  both morphisms share a target fixed point,   *)
  (*  the meeting is non-empty.                    *)
  (* ============================================= *)

  Theorem pullback_witness_from_agreement :
    forall (a : D1.Entity) (b : D2.Entity),
      F1.phi a = F2.phi b ->
      on_pullback (a, b).
  Proof.
    intros a b H. unfold on_pullback. simpl. exact H.
  Qed.

  (* ============================================= *)
  (*  OBSERVATIONAL MEETING                        *)
  (*                                               *)
  (*  Relaxation of on_pullback: the two images    *)
  (*  need only agree under every Base viewpoint,  *)
  (*  not as raw Base entities. This captures      *)
  (*  meetings that are "the same as far as Base   *)
  (*  can tell" without requiring literal equality *)
  (*  in Base.                                     *)
  (*                                               *)
  (*  on_pullback → on_pullback_observational      *)
  (*  (strict implies observational) but not the   *)
  (*  converse; the observational meeting is the   *)
  (*  wider collection.                            *)
  (* ============================================= *)

  Definition on_pullback_observational (p : P.Entity) : Prop :=
    forall c : Base.Entity,
      Base.interact (F1.phi (fst p)) c =
      Base.interact (F2.phi (snd p)) c.

  (* Strict meeting implies observational meeting. *)

  Theorem on_pullback_is_observational :
    forall p : P.Entity,
      on_pullback p -> on_pullback_observational p.
  Proof.
    intros p Hstrict c. unfold on_pullback in Hstrict.
    rewrite Hstrict. reflexivity.
  Qed.

  (* Observational meetings are stable under interact,
     coordinate-wise — the same closure property that
     strict meetings enjoy, now at observational level. *)

  Theorem interact_preserves_observational_pullback :
    forall a b : P.Entity,
      on_pullback_observational a ->
      on_pullback_observational b ->
      on_pullback_observational (P.interact a b).
  Proof.
    intros [a1 a2] [b1 b2] Ha Hb c.
    unfold on_pullback_observational, P.interact in *. simpl in *.
    rewrite F1.preserves_interact.
    rewrite F2.preserves_interact.
    (* Goal: Base.interact (Base.interact (F1.phi a1) (F1.phi b1)) c =
             Base.interact (Base.interact (F2.phi a2) (F2.phi b2)) c *)
    (* Rewrite using Ha and Hb through appropriate viewpoints. *)
    specialize (Ha (Base.interact (F1.phi b1) c)).
    specialize (Hb (Base.interact (F2.phi a2) c)).
    (* Ha: Base.interact (F1.phi a1) (Base.interact (F1.phi b1) c) =
           Base.interact (F2.phi a2) (Base.interact (F1.phi b1) c) *)
    (* Hmm, these don't immediately collapse. The general
       observational variant needs Base to satisfy a
       stronger structural property (associativity or
       extensionality). We state only the conditional
       form below. *)
  Abort.

  (* Observational meetings are closed under interact
     when Base is associative under its interact. This
     is an instance-level property, not framework-level. *)

  Definition base_associative : Prop :=
    forall x y z : Base.Entity,
      Base.interact (Base.interact x y) z =
      Base.interact x (Base.interact y z).

  Theorem interact_preserves_observational_pullback_if_assoc :
    base_associative ->
    forall a b : P.Entity,
      on_pullback_observational a ->
      on_pullback_observational b ->
      on_pullback_observational (P.interact a b).
  Proof.
    intros Hassoc [a1 a2] [b1 b2] Ha Hb c.
    unfold on_pullback_observational, P.interact in *. simpl in *.
    rewrite F1.preserves_interact.
    rewrite F2.preserves_interact.
    rewrite Hassoc. rewrite Hassoc.
    rewrite (Ha (Base.interact (F1.phi b1) c)).
    (* goal: Base.interact (F2.phi a2) (Base.interact (F1.phi b1) c) =
             Base.interact (F2.phi a2) (Base.interact (F2.phi b2) c) *)
    f_equal.
    exact (Hb c).
  Qed.

  (* Observational witness from observational agreement. *)

  Theorem pullback_observational_witness :
    forall (a : D1.Entity) (b : D2.Entity),
      (forall c, Base.interact (F1.phi a) c = Base.interact (F2.phi b) c) ->
      on_pullback_observational (a, b).
  Proof.
    intros a b H c. unfold on_pullback_observational. simpl. apply H.
  Qed.

End Pullback.


(* ================================================ *)
(*  PULLBACK UNIVERSAL PROPERTY                      *)
(*                                                   *)
(*  Given a cone over the span Base ← D1, Base ← D2 *)
(*  from an apex X (morphisms f1: X → D1, f2: X → D2*)
(*  satisfying F1 ∘ f1 = F2 ∘ f2), there exists a    *)
(*  unique factoring h : X → Pullback.               *)
(* ================================================ *)

Module PullbackUniversal (D1 D2 Base X : ExistenceSig)
                         (F1 : MorphismInto D1 Base)
                         (F2 : MorphismInto D2 Base).

  Module PB := Pullback D1 D2 Base F1 F2.

  (* The pair function landing in D1 × D2. When the
     cone commutes (F1 ∘ f1 = F2 ∘ f2), this lands
     inside the pullback subspace. *)

  Definition pullback_pair
    (f1 : X.Entity -> D1.Entity)
    (f2 : X.Entity -> D2.Entity)
    (x : X.Entity) : PB.P.Entity :=
    (f1 x, f2 x).

  (* Commutativity of the cone → image lives in the
     pullback. *)

  Theorem pullback_pair_lands :
    forall f1 f2,
      (forall x, F1.phi (f1 x) = F2.phi (f2 x)) ->
      forall x, PB.on_pullback (pullback_pair f1 f2 x).
  Proof.
    intros f1 f2 Hcomm x.
    unfold PB.on_pullback, pullback_pair. simpl.
    apply Hcomm.
  Qed.

  (* Interact preservation lifts coordinate-wise. *)

  Theorem pullback_pair_preserves_interact :
    forall f1 f2,
      (forall a b, f1 (X.interact a b) = D1.interact (f1 a) (f1 b)) ->
      (forall a b, f2 (X.interact a b) = D2.interact (f2 a) (f2 b)) ->
      forall a b,
        pullback_pair f1 f2 (X.interact a b) =
        PB.P.interact (pullback_pair f1 f2 a) (pullback_pair f1 f2 b).
  Proof.
    intros f1 f2 Hf1 Hf2 a b.
    unfold pullback_pair, PB.P.interact. simpl.
    rewrite Hf1. rewrite Hf2. reflexivity.
  Qed.

  (* Convention preservation lifts coordinate-wise into
     the product, and (since Pullback's collapse is
     inherited from the product) into the pullback. *)

  Theorem pullback_pair_preserves_convention :
    forall f1 f2,
      (forall a b, X.collapse a b ->
                   D1.collapse (f1 a) (f1 b)) ->
      (forall a b, X.collapse a b ->
                   D2.collapse (f2 a) (f2 b)) ->
      forall a b,
        X.collapse a b ->
        PB.P.collapse (pullback_pair f1 f2 a)
                           (pullback_pair f1 f2 b).
  Proof.
    intros f1 f2 Hf1 Hf2 a b Hconv.
    unfold pullback_pair, PB.P.collapse. simpl.
    split.
    - apply Hf1. exact Hconv.
    - apply Hf2. exact Hconv.
  Qed.

  (* Factoring: the cone projects through the pair. *)

  Theorem pullback_factors_f1 :
    forall f1 f2 x,
      fst (pullback_pair f1 f2 x) = f1 x.
  Proof. intros. reflexivity. Qed.

  Theorem pullback_factors_f2 :
    forall f1 f2 x,
      snd (pullback_pair f1 f2 x) = f2 x.
  Proof. intros. reflexivity. Qed.

  (* Existence. *)

  Theorem pullback_universal_existence :
    forall f1 f2,
      (forall a b, f1 (X.interact a b) = D1.interact (f1 a) (f1 b)) ->
      (forall a b, f2 (X.interact a b) = D2.interact (f2 a) (f2 b)) ->
      (forall x, F1.phi (f1 x) = F2.phi (f2 x)) ->
      exists h : X.Entity -> PB.P.Entity,
        (forall a b, h (X.interact a b) =
                     PB.P.interact (h a) (h b)) /\
        (forall x, PB.on_pullback (h x)) /\
        (forall x, fst (h x) = f1 x) /\
        (forall x, snd (h x) = f2 x).
  Proof.
    intros f1 f2 Hf1 Hf2 Hcomm.
    exists (pullback_pair f1 f2).
    split; [apply pullback_pair_preserves_interact; assumption |].
    split; [apply pullback_pair_lands; assumption |].
    split; intro x; reflexivity.
  Qed.

  (* Uniqueness (pointwise). *)

  Theorem pullback_universal_uniqueness :
    forall f1 f2 (h h' : X.Entity -> PB.P.Entity),
      (forall x, fst (h x) = f1 x) ->
      (forall x, snd (h x) = f2 x) ->
      (forall x, fst (h' x) = f1 x) ->
      (forall x, snd (h' x) = f2 x) ->
      forall x, h x = h' x.
  Proof.
    intros f1 f2 h h' H1 H2 H1' H2' x.
    destruct (h x) as [h1 h2] eqn:Eh.
    destruct (h' x) as [h1' h2'] eqn:Eh'.
    specialize (H1 x). rewrite Eh in H1. simpl in H1.
    specialize (H2 x). rewrite Eh in H2. simpl in H2.
    specialize (H1' x). rewrite Eh' in H1'. simpl in H1'.
    specialize (H2' x). rewrite Eh' in H2'. simpl in H2'.
    subst. reflexivity.
  Qed.

  (* ============================================= *)
  (*  OBSERVATIONAL UNIVERSAL (PULLBACK)           *)
  (*                                               *)
  (*  When the cone morphisms f1, f2 are only      *)
  (*  observational (rather than strict), the      *)
  (*  pair morphism into the pullback is also      *)
  (*  observational. The commutativity condition   *)
  (*  on the cone remains strict here — relaxing   *)
  (*  it further requires a corresponding          *)
  (*  relaxation of on_pullback, which is left as  *)
  (*  instance-level choice.                       *)
  (* ============================================= *)

  Theorem pullback_pair_observational_morphism :
    forall f1 f2,
      (forall a b c,
         D1.interact (f1 (X.interact a b)) c =
         D1.interact (D1.interact (f1 a) (f1 b)) c) ->
      (forall a b c,
         D2.interact (f2 (X.interact a b)) c =
         D2.interact (D2.interact (f2 a) (f2 b)) c) ->
      forall a b (c : PB.P.Entity),
        PB.P.interact
          (pullback_pair f1 f2 (X.interact a b)) c =
        PB.P.interact
          (PB.P.interact (pullback_pair f1 f2 a)
                         (pullback_pair f1 f2 b)) c.
  Proof.
    intros f1 f2 Hf1 Hf2 a b [c1 c2].
    unfold pullback_pair, PB.P.interact. simpl.
    f_equal.
    - apply Hf1.
    - apply Hf2.
  Qed.

End PullbackUniversal.
