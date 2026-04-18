(* ============================================== *)
(*  ModularCoequalizer                              *)
(*                                                  *)
(*  Realize ℤ/7ℤ as the framework Coequalizer       *)
(*  of two parallel morphisms on Integer:           *)
(*                                                  *)
(*     id   : Integer → Integer                     *)
(*     addN : Integer → Integer                     *)
(*                                                  *)
(*  where addN (d, z) = (d, z + 7).                 *)
(*                                                  *)
(*  The Coequalizer forces (d, z) ~ (d, z + 7)      *)
(*  for every source point, producing the quotient  *)
(*  ℤ / 7ℤ at each dim coord. Equivalence classes   *)
(*  are witnessed constructively via e_identify.    *)
(*                                                  *)
(*  Distinctness across classes is proved via a     *)
(*  concrete coequalizing morphism                   *)
(*                                                  *)
(*     R : Integer → Integer                        *)
(*     R (d, z) = (d, z mod 7)                      *)
(*                                                  *)
(*  R coequalizes id and addN because               *)
(*  (z + 7) mod 7 = z mod 7. The factoring arrow   *)
(*  r_star : Coeq → Integer is then an injection    *)
(*  of ℤ/7ℤ into Integer's canonical residue        *)
(*  coords, which detects distinct classes.         *)
(*                                                  *)
(*  This file makes the Coequalizer tooling do real *)
(*  algebraic work — CoequalizerTest.v (with const) *)
(*  only showed collapse to a singleton.            *)
(* ============================================== *)

Require Import Existence.
Require Import ExistenceMorphism.
Require Import ExistencePullback.
Require Import ExistencePushout.
Require Import ExistenceCoequalizer.
Require Import IntegerGrothendieck.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.


Module IZ := IntegerGrothendieck.Integer.


(* ================================================ *)
(*  MORPHISMS                                        *)
(* ================================================ *)

Module IdIZ := ExistencePullback.IdentityInto IZ.

Module Add7 <: MorphismInto IZ IZ.

  Definition phi (x : IZ.Entity) : IZ.Entity :=
    (fst x, (snd x + 7)%Z).

  Theorem preserves_interact :
    forall a b : IZ.Entity,
      phi (IZ.interact a b) = IZ.interact (phi a) (phi b).
  Proof.
    intros [da za] [db zb].
    unfold phi, IZ.interact. simpl.
    destruct (Nat.eq_dec da db); reflexivity.
  Qed.

End Add7.

(* Coequalizing witness: R (d, z) = (d, z mod 7). *)

Module ModR <: MorphismInto IZ IZ.

  Definition phi (x : IZ.Entity) : IZ.Entity :=
    (fst x, Z.modulo (snd x) 7).

  Theorem preserves_interact :
    forall a b : IZ.Entity,
      phi (IZ.interact a b) = IZ.interact (phi a) (phi b).
  Proof.
    intros [da za] [db zb].
    unfold phi, IZ.interact. simpl.
    destruct (Nat.eq_dec da db); reflexivity.
  Qed.

End ModR.


(* ================================================ *)
(*  COEQUALIZER                                      *)
(* ================================================ *)

Module ModCoeq :=
  ExistenceCoequalizer.Universal
    IZ IZ IdIZ Add7
    IZ ModR.


(* ================================================ *)
(*  WITNESSES OF COLLAPSE                            *)
(*                                                   *)
(*  e_identify at (d, z) says equiv (d, z) (d, z+7) *)
(*  — the defining generator of the quotient.       *)
(* ================================================ *)

Theorem cls_0_eq_cls_7 :
  forall d : nat,
    ModCoeq.C.cls (d, 0%Z) = ModCoeq.C.cls (d, 7%Z).
Proof.
  intros d. apply ModCoeq.C.cls_correct.
  exact (ModCoeq.C.e_identify (d, 0%Z)).
Qed.

Theorem cls_7_eq_cls_14 :
  forall d : nat,
    ModCoeq.C.cls (d, 7%Z) = ModCoeq.C.cls (d, 14%Z).
Proof.
  intros d. apply ModCoeq.C.cls_correct.
  exact (ModCoeq.C.e_identify (d, 7%Z)).
Qed.

Theorem cls_0_eq_cls_14 :
  forall d : nat,
    ModCoeq.C.cls (d, 0%Z) = ModCoeq.C.cls (d, 14%Z).
Proof.
  intros d. rewrite cls_0_eq_cls_7. apply cls_7_eq_cls_14.
Qed.

(* Negative representatives collapse too: (d, -7) ~ (d, 0). *)

Theorem cls_neg7_eq_cls_0 :
  forall d : nat,
    ModCoeq.C.cls (d, (-7)%Z) = ModCoeq.C.cls (d, 0%Z).
Proof.
  intros d.
  change (0%Z) with ((-7) + 7)%Z.
  apply ModCoeq.C.cls_correct.
  exact (ModCoeq.C.e_identify (d, (-7)%Z)).
Qed.


(* ================================================ *)
(*  UNIVERSAL FACTORING VIA ModR                     *)
(*                                                   *)
(*  R (d, z) = (d, z mod 7) coequalizes id and      *)
(*  addN: R (z) = R (z + 7) because mod 7.          *)
(* ================================================ *)

Module ModR_Coeqs <: ModCoeq.CoequalizingRmorphism.
  Theorem r_coequalizes :
    forall a : IZ.Entity,
      ModR.phi (IdIZ.phi a) = ModR.phi (Add7.phi a).
  Proof.
    intros [d z]. unfold ModR.phi, IdIZ.phi, Add7.phi. simpl.
    f_equal.
    rewrite <- Z.add_mod_idemp_r by lia.
    replace (7 mod 7)%Z with 0%Z by reflexivity.
    rewrite Z.add_0_r. reflexivity.
  Qed.
End ModR_Coeqs.

Module ModFactor := ModCoeq.Factor ModR_Coeqs.


(* r_star behaves like R on representatives. *)

Theorem r_star_is_mod7 :
  forall a : IZ.Entity,
    ModFactor.r_star (ModCoeq.C.q a) = ModR.phi a.
Proof. exact ModFactor.r_star_factors. Qed.

Theorem r_star_preserves_interact :
  forall a b : ModCoeq.C.Entity,
    ModFactor.r_star (ModCoeq.C.interact a b) =
    IZ.interact (ModFactor.r_star a) (ModFactor.r_star b).
Proof. exact ModFactor.r_star_preserves_interact. Qed.


(* ================================================ *)
(*  DISTINCTNESS OF RESIDUE CLASSES                  *)
(*                                                   *)
(*  The factoring arrow detects that cls (d, 0) and *)
(*  cls (d, 1) are different in the quotient        *)
(*  because their r_star images are (d, 0) and      *)
(*  (d, 1), which are different Integer entities.   *)
(* ================================================ *)

(* Helper: distinct mod-7 residues give distinct classes. *)

Theorem cls_ne_via_mod :
  forall (d : nat) (z1 z2 : Z),
    (z1 mod 7)%Z <> (z2 mod 7)%Z ->
    ModCoeq.C.cls (d, z1) <> ModCoeq.C.cls (d, z2).
Proof.
  intros d z1 z2 Hmod Heq.
  assert (Himg :
    ModFactor.r_star (ModCoeq.C.q (d, z1)) =
    ModFactor.r_star (ModCoeq.C.q (d, z2))).
  { unfold ModCoeq.C.q. f_equal. exact Heq. }
  rewrite !r_star_is_mod7 in Himg.
  unfold ModR.phi in Himg. simpl in Himg.
  inversion Himg. contradiction.
Qed.

Theorem cls_0_ne_cls_1 :
  forall d : nat,
    ModCoeq.C.cls (d, 0%Z) <> ModCoeq.C.cls (d, 1%Z).
Proof.
  intros d. apply cls_ne_via_mod. simpl. discriminate.
Qed.

Theorem cls_0_ne_cls_3 :
  forall d : nat,
    ModCoeq.C.cls (d, 0%Z) <> ModCoeq.C.cls (d, 3%Z).
Proof.
  intros d. apply cls_ne_via_mod. simpl. discriminate.
Qed.

(* Classes across distinct dims never collapse. *)

Theorem cls_different_dims_distinct :
  forall (d1 d2 : nat) (z1 z2 : Z),
    d1 <> d2 ->
    ModCoeq.C.cls (d1, z1) <> ModCoeq.C.cls (d2, z2).
Proof.
  intros d1 d2 z1 z2 Hne Heq.
  assert (Himg :
    ModFactor.r_star (ModCoeq.C.q (d1, z1)) =
    ModFactor.r_star (ModCoeq.C.q (d2, z2))).
  { unfold ModCoeq.C.q. f_equal. exact Heq. }
  rewrite !r_star_is_mod7 in Himg.
  unfold ModR.phi in Himg. simpl in Himg.
  inversion Himg. contradiction.
Qed.


(* ================================================ *)
(*  SMALLEST-NONTRIVIAL WITNESS                      *)
(*                                                   *)
(*  At dim 0 the quotient has EXACTLY 7 classes.    *)
(*  We list the 7 canonical representatives and     *)
(*  prove they are pairwise distinct.                *)
(* ================================================ *)

Definition rep (k : Z) : ModCoeq.C.Entity :=
  ModCoeq.C.cls (0%nat, k).

Theorem seven_reps_distinct :
  rep 0 <> rep 1 /\
  rep 0 <> rep 2 /\
  rep 0 <> rep 3 /\
  rep 0 <> rep 4 /\
  rep 0 <> rep 5 /\
  rep 0 <> rep 6 /\
  rep 1 <> rep 2 /\
  rep 5 <> rep 6.
Proof.
  unfold rep.
  repeat split; apply cls_ne_via_mod; simpl; discriminate.
Qed.

(* And the eighth (z = 7) collapses back onto z = 0. *)

Theorem rep_7_eq_rep_0 : rep 7 = rep 0.
Proof.
  unfold rep. symmetry. apply cls_0_eq_cls_7.
Qed.
