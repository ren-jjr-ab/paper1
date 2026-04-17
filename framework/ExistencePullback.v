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

End Pullback.
