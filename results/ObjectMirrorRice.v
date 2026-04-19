(* ============================================== *)
(*  ObjectMirrorRice                                *)
(*                                                  *)
(*  Rice's theorem, applied to ObjectMirror.        *)
(*                                                  *)
(*  Collapse witness: a dark mirror (reflection     *)
(*  coefficient 0) absorbs any object's intensity.  *)
(*  Two objects of different intrinsic intensity,   *)
(*  viewed through the same dark mirror, produce    *)
(*  the identical observation.                      *)
(*                                                  *)
(*    Object 80  ⊳  Mirror 0  =  Object 0 (at t+1)  *)
(*    Object 10  ⊳  Mirror 0  =  Object 0 (at t+1)  *)
(*                                                  *)
(*  Distinct sources, same observation. Rice's      *)
(*  theorem forbids any universal decoder that      *)
(*  recovers the source from the observation.       *)
(*                                                  *)
(*  Translated to ordinary language: there is no    *)
(*  algorithm that, given a reflected image,        *)
(*  reconstructs the original object from which     *)
(*  the image came.                                 *)
(*                                                  *)
(*  Two entirely distinct traditions — Rice-type    *)
(*  computability (1953) and optical information    *)
(*  loss in imaging — are here the *same* theorem,  *)
(*  instantiated through different collapse         *)
(*  witnesses of the framework's meta-level Rice.   *)
(* ============================================== *)

Require Import Existence.
Require ObjectMirror.
Require FrameworkRice.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


(* =========================================== *)
(*  EXISTENCEWITHCOLLAPSE FOR OBJECTMIRROR      *)
(* =========================================== *)

Module ObjectMirrorWithCollapse <: FrameworkRice.ExistenceWithCollapse.

  Definition Entity        := ObjectMirror.ObjectMirror.Entity.
  Definition interact      := ObjectMirror.ObjectMirror.interact.
  Definition convention_eq := ObjectMirror.ObjectMirror.convention_eq.

  Definition interact_self       := ObjectMirror.ObjectMirror.interact_self.
  Definition interact_decidable  := ObjectMirror.ObjectMirror.interact_decidable.
  Definition existence           := ObjectMirror.ObjectMirror.existence.
  Definition interact_with       := ObjectMirror.ObjectMirror.interact_with.
  Definition convention_not_derivable :=
    ObjectMirror.ObjectMirror.convention_not_derivable.

  (* Nothing is frozen in ObjectMirror — freeze is a framework
     concept the instance doesn't carry. *)

  Definition is_frozen (_ : Entity) : Prop := False.

  (* Two objects of intensities 80 and 10, observed through a dark
     mirror (r = 0), collapse to Object 0 at timestamp 1. *)

  Definition collapse_a      : Entity := ObjectMirror.ObjectMirror.Object 80 0.
  Definition collapse_a'     : Entity := ObjectMirror.ObjectMirror.Object 10 0.
  Definition collapse_via    : Entity := ObjectMirror.ObjectMirror.Mirror 0 0.
  Definition collapse_target : Entity := ObjectMirror.ObjectMirror.Object 0 1.

  Theorem collapse_distinct : collapse_a <> collapse_a'.
  Proof. intros H. inversion H. Qed.

  Theorem collapse_a_not_frozen  : ~ is_frozen collapse_a.
  Proof. intros H. exact H. Qed.

  Theorem collapse_a'_not_frozen : ~ is_frozen collapse_a'.
  Proof. intros H. exact H. Qed.

  Theorem collapse_interacts_a :
    interact collapse_a collapse_via = collapse_target.
  Proof. reflexivity. Qed.

  Theorem collapse_interacts_a' :
    interact collapse_a' collapse_via = collapse_target.
  Proof. reflexivity. Qed.

End ObjectMirrorWithCollapse.


Module ObjectMirrorRice := FrameworkRice.Make ObjectMirrorWithCollapse.


(* =========================================== *)
(*  THE ABSURD THEOREM                          *)
(*                                              *)
(*  Stated in framework vocabulary and then in  *)
(*  imaging-physics vocabulary. The same        *)
(*  statement twice.                            *)
(* =========================================== *)

(* Framework vocabulary: *)

Theorem mirror_no_universal_decoder :
  ~ (exists (decode : ObjectMirrorWithCollapse.Entity
                   -> ObjectMirrorWithCollapse.Entity),
       forall a c : ObjectMirrorWithCollapse.Entity,
         decode (ObjectMirrorWithCollapse.interact a c) = a).
Proof. apply ObjectMirrorRice.rice_no_universal_decoder. Qed.

(* Imaging-physics reading: no algorithm reconstructs an object
   from its reflected image across all object-mirror pairs. *)

Theorem mirror_no_universal_reconstruction :
  ~ (exists (reconstruct : ObjectMirror.ObjectMirror.Entity
                         -> ObjectMirror.ObjectMirror.Entity),
       forall (original mirror : ObjectMirror.ObjectMirror.Entity),
         reconstruct
           (ObjectMirror.ObjectMirror.interact original mirror)
         = original).
Proof. apply ObjectMirrorRice.rice_no_universal_decoder. Qed.


(* =========================================== *)
(*  CONCRETE WITNESSES                          *)
(* =========================================== *)

(* Dark-mirror absorption: the collapse in literal values. *)

Example dark_mirror_absorbs_eighty :
  ObjectMirror.ObjectMirror.interact
    (ObjectMirror.ObjectMirror.Object 80 0)
    (ObjectMirror.ObjectMirror.Mirror 0 0)
  = ObjectMirror.ObjectMirror.Object 0 1.
Proof. reflexivity. Qed.

Example dark_mirror_absorbs_ten :
  ObjectMirror.ObjectMirror.interact
    (ObjectMirror.ObjectMirror.Object 10 0)
    (ObjectMirror.ObjectMirror.Mirror 0 0)
  = ObjectMirror.ObjectMirror.Object 0 1.
Proof. reflexivity. Qed.

(* The same observation, two distinct sources. *)

Example collapse_is_real :
  ObjectMirror.ObjectMirror.interact
    (ObjectMirror.ObjectMirror.Object 80 0)
    (ObjectMirror.ObjectMirror.Mirror 0 0)
  =
  ObjectMirror.ObjectMirror.interact
    (ObjectMirror.ObjectMirror.Object 10 0)
    (ObjectMirror.ObjectMirror.Mirror 0 0).
Proof. reflexivity. Qed.


(* =========================================== *)
(*  REMARK                                      *)
(*                                              *)
(*  The collapse is not special to dark         *)
(*  mirrors. Any mirror with reflection         *)
(*  coefficient r < 100 induces collapses at    *)
(*  nat division rounding: e.g., r = 50 maps    *)
(*  i = 2 and i = 3 both to floor(r*i/100) = 1. *)
(*  Rice applies to any instance that exhibits  *)
(*  a single collapse; our proof uses r = 0 for *)
(*  syntactic cleanliness.                      *)
(*                                              *)
(*  Two traditions meet here:                   *)
(*                                              *)
(*   · Rice, 1953: semantic properties of       *)
(*     programs are undecidable because         *)
(*     distinct programs can have the same      *)
(*     behaviour.                               *)
(*                                              *)
(*   · Classical optics: a reflection           *)
(*     projection is information-lossy.         *)
(*                                              *)
(*  Both inhabit the same framework-level Rice  *)
(*  collapse, differing only in the chosen      *)
(*  collapse witness.                           *)
(* =========================================== *)
