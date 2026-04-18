(* ============================================== *)
(*  DedekindCauchyIsomorphism                       *)
(*                                                  *)
(*  DedekindReal ≅ CauchyReal as framework          *)
(*  ExistenceSig instances.                         *)
(*                                                  *)
(*  Construction:                                   *)
(*                                                  *)
(*    to_ct : DCut -> CauchyTerm                    *)
(*    from_ct : CauchyTerm -> DCut                  *)
(*                                                  *)
(*  — structural renaming of constructors.          *)
(*  Inverses established by induction over each     *)
(*  grammar. Semantics aligned:                     *)
(*                                                  *)
(*    denote_dr c n = denote_cr (to_ct c) n         *)
(*                                                  *)
(*  Lifted to Entity:                               *)
(*                                                  *)
(*    phi : DR.Entity -> CR.Entity                  *)
(*    psi : CR.Entity -> DR.Entity                  *)
(*                                                  *)
(*  phi preserves_interact via the interact         *)
(*  definition being parallel in both instances     *)
(*  (same dispatch, same denote-threaded DEval      *)
(*  case). is_iso follows from phi preserving      *)
(*  interact and psi being a two-sided inverse.     *)
(*                                                  *)
(*  The classical statement "Dedekind cuts and      *)
(*  Cauchy sequences construct the same ℝ" becomes  *)
(*  framework's is_iso at the level of finite       *)
(*  syntactic representation. The iso is            *)
(*  constructive: no Classical, no FunExt, no       *)
(*  external axioms beyond the framework's own.     *)
(* ============================================== *)

Require Existence.
Require ExistenceMorphism.
Require ExternalTime.
Require CauchyReal.
Require DedekindReal.
From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import PArith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module CR := CauchyReal.CauchyReal.
Module DR := DedekindReal.DedekindReal.
Module Phi := ExistenceMorphism.Make DR CR.
Module Psi := ExistenceMorphism.Make CR DR.


(* ================================================ *)
(*  CUT ↔ TERM BIJECTION                             *)
(* ================================================ *)

Fixpoint to_ct (c : DR.DCut) : CR.CauchyTerm :=
  match c with
  | DR.DConst q     => CR.CTConst q
  | DR.DInvSucc     => CR.CTInvSucc
  | DR.DSum a b     => CR.CTSum (to_ct a) (to_ct b)
  | DR.DNeg a       => CR.CTNeg (to_ct a)
  | DR.DScale q a   => CR.CTScale q (to_ct a)
  | DR.DMul a b     => CR.CTMul (to_ct a) (to_ct b)
  end.

Fixpoint from_ct (s : CR.CauchyTerm) : DR.DCut :=
  match s with
  | CR.CTConst q     => DR.DConst q
  | CR.CTInvSucc     => DR.DInvSucc
  | CR.CTSum a b     => DR.DSum (from_ct a) (from_ct b)
  | CR.CTNeg a       => DR.DNeg (from_ct a)
  | CR.CTScale q a   => DR.DScale q (from_ct a)
  | CR.CTMul a b     => DR.DMul (from_ct a) (from_ct b)
  end.

Theorem from_to_ct : forall c : DR.DCut, from_ct (to_ct c) = c.
Proof.
  induction c; simpl;
    try reflexivity;
    try (rewrite IHc1, IHc2; reflexivity);
    try (rewrite IHc; reflexivity).
Qed.

Theorem to_from_ct : forall s : CR.CauchyTerm, to_ct (from_ct s) = s.
Proof.
  induction s; simpl;
    try reflexivity;
    try (rewrite IHs1, IHs2; reflexivity);
    try (rewrite IHs; reflexivity).
Qed.

(* Denote semantics align under the bijection. *)

Theorem denote_to_ct :
  forall (c : DR.DCut) (n : nat),
    (CR.denote (to_ct c) n == DR.denote c n)%Q.
Proof.
  induction c; intros n; simpl;
    try reflexivity.
  - rewrite IHc1, IHc2. reflexivity.
  - rewrite IHc. reflexivity.
  - rewrite IHc. reflexivity.
  - rewrite IHc1, IHc2. reflexivity.
Qed.

(* Leibniz version of denote_to_ct, under Qred. *)

Theorem qred_denote_to_ct :
  forall (c : DR.DCut) (n : nat),
    Qred (CR.denote (to_ct c) n) = Qred (DR.denote c n).
Proof.
  intros c n. apply Qred_complete. apply denote_to_ct.
Qed.

(* Companion lemma on the from_ct side. *)

Theorem qred_denote_from_ct :
  forall (s : CR.CauchyTerm) (n : nat),
    Qred (CR.denote s n) = Qred (DR.denote (from_ct s) n).
Proof.
  intros s n.
  rewrite <- (to_from_ct s) at 1.
  apply qred_denote_to_ct.
Qed.


(* ================================================ *)
(*  ENTITY-LEVEL MAPS                                *)
(* ================================================ *)

Definition phi (a : DR.Entity) : CR.Entity :=
  match a with
  | DR.DREnt c t => CR.REnt (to_ct c) t
  | DR.DEval n t => CR.CEval n t
  end.

Definition psi (b : CR.Entity) : DR.Entity :=
  match b with
  | CR.REnt s t  => DR.DREnt (from_ct s) t
  | CR.CEval n t => DR.DEval n t
  end.


(* ================================================ *)
(*  TWO-SIDED INVERSE                                *)
(* ================================================ *)

Theorem psi_phi_id : forall a : DR.Entity, psi (phi a) = a.
Proof.
  intros [c t | n t]; simpl.
  - rewrite from_to_ct. reflexivity.
  - reflexivity.
Qed.

Theorem phi_psi_id : forall b : CR.Entity, phi (psi b) = b.
Proof.
  intros [s t | n t]; simpl.
  - rewrite to_from_ct. reflexivity.
  - reflexivity.
Qed.


(* ================================================ *)
(*  PRESERVES_INTERACT                               *)
(*                                                   *)
(*  Case analysis mirrors the parallel interact      *)
(*  definitions. The REnt / DEval case invokes the  *)
(*  denote-Qred lemma above.                         *)
(* ================================================ *)

Theorem phi_preserves_interact :
  forall a b : DR.Entity,
    phi (DR.interact a b) = CR.interact (phi a) (phi b).
Proof.
  intros a b. unfold DR.interact, CR.interact.
  destruct (DR.entity_eq_dec a b) as [Heq | Hne];
    destruct (CR.entity_eq_dec (phi a) (phi b)) as [Heq' | Hne'].
  - reflexivity.
  - exfalso. apply Hne'. rewrite Heq. reflexivity.
  - exfalso. apply Hne.
    destruct a as [c1 t1 | n1 t1]; destruct b as [c2 t2 | n2 t2];
      simpl in Heq'; inversion Heq'; subst;
      try reflexivity.
    + f_equal. rewrite <- (from_to_ct c1), <- (from_to_ct c2).
      rewrite H0. reflexivity.
  - destruct a as [c1 t1 | n1 t1]; destruct b as [c2 t2 | n2 t2]; simpl.
    + (* DREnt, DREnt *) reflexivity.
    + (* DREnt, DEval *)
      f_equal. f_equal. symmetry. apply qred_denote_to_ct.
    + (* DEval, DREnt *) reflexivity.
    + (* DEval, DEval *) reflexivity.
Qed.

Theorem psi_preserves_interact :
  forall a b : CR.Entity,
    psi (CR.interact a b) = DR.interact (psi a) (psi b).
Proof.
  intros a b. unfold CR.interact, DR.interact.
  destruct (CR.entity_eq_dec a b) as [Heq | Hne];
    destruct (DR.entity_eq_dec (psi a) (psi b)) as [Heq' | Hne'].
  - reflexivity.
  - exfalso. apply Hne'. rewrite Heq. reflexivity.
  - exfalso. apply Hne.
    destruct a as [s1 t1 | n1 t1]; destruct b as [s2 t2 | n2 t2];
      simpl in Heq'; inversion Heq'; subst;
      try reflexivity.
    + f_equal. rewrite <- (to_from_ct s1), <- (to_from_ct s2).
      rewrite H0. reflexivity.
  - destruct a as [s1 t1 | n1 t1]; destruct b as [s2 t2 | n2 t2]; simpl.
    + reflexivity.
    + f_equal. f_equal. apply qred_denote_from_ct.
    + reflexivity.
    + reflexivity.
Qed.


(* ================================================ *)
(*  IS_ISO                                           *)
(*                                                   *)
(*  Framework isomorphism: preserves_interact       *)
(*  plus two-sided inverse.                          *)
(* ================================================ *)

Theorem phi_is_iso : Phi.is_iso phi.
Proof.
  unfold Phi.is_iso. exists psi.
  repeat split.
  - exact phi_preserves_interact.
  - exact psi_phi_id.
  - exact phi_psi_id.
Qed.

Theorem psi_is_iso : Psi.is_iso psi.
Proof.
  unfold Psi.is_iso. exists phi.
  repeat split.
  - exact psi_preserves_interact.
  - exact phi_psi_id.
  - exact psi_phi_id.
Qed.


(* ================================================ *)
(*  CONCRETE CORRESPONDENCES                         *)
(*                                                   *)
(*  Sanity witnesses for the iso on specific real    *)
(*  approximations.                                  *)
(* ================================================ *)

Example phi_const_2 :
  phi (DR.DREnt (DR.DConst 2) 0) = CR.REnt (CR.CTConst 2) 0.
Proof. reflexivity. Qed.

Example psi_const_2 :
  psi (CR.REnt (CR.CTConst 2) 0) = DR.DREnt (DR.DConst 2) 0.
Proof. reflexivity. Qed.

Example phi_invsucc :
  phi (DR.DREnt DR.DInvSucc 0) = CR.REnt CR.CTInvSucc 0.
Proof. reflexivity. Qed.

Example phi_sum_invsucc_const :
  phi (DR.DREnt (DR.DSum DR.DInvSucc (DR.DConst 1)) 0) =
  CR.REnt (CR.CTSum CR.CTInvSucc (CR.CTConst 1)) 0.
Proof. reflexivity. Qed.

Example phi_eval :
  phi (DR.DEval 3 5) = CR.CEval 3 5.
Proof. reflexivity. Qed.

(* Roundtrip on a compound entity. *)

Example roundtrip_compound :
  psi (phi (DR.DREnt
             (DR.DMul (DR.DScale 3 DR.DInvSucc)
                       (DR.DSum (DR.DConst 2) (DR.DNeg (DR.DConst 1))))
             7))
  = DR.DREnt
      (DR.DMul (DR.DScale 3 DR.DInvSucc)
                (DR.DSum (DR.DConst 2) (DR.DNeg (DR.DConst 1))))
      7.
Proof. apply psi_phi_id. Qed.


(* ================================================ *)
(*  CONVENTION_EQ CORRESPONDENCE                     *)
(*                                                   *)
(*  Although is_iso alone does not require            *)
(*  convention preservation, the convention_eq       *)
(*  structure is parallel across the two instances  *)
(*  — denote aligns, so cauchy_equivalent /          *)
(*  pointwise_distinct also align. convention_eq    *)
(*  therefore transports both ways.                 *)
(* ================================================ *)

Theorem cauchy_equivalent_transport :
  forall c1 c2 : DR.DCut,
    DR.cauchy_equivalent c1 c2 ->
    CR.cauchy_equivalent (to_ct c1) (to_ct c2).
Proof.
  intros c1 c2 H k.
  destruct (H k) as [N HN]. exists N.
  intros n Hn.
  rewrite (denote_to_ct c1 n).
  rewrite (denote_to_ct c2 n).
  apply HN. exact Hn.
Qed.

Theorem pointwise_distinct_transport :
  forall c1 c2 : DR.DCut,
    DR.pointwise_distinct c1 c2 ->
    CR.pointwise_distinct (to_ct c1) (to_ct c2).
Proof.
  intros c1 c2 H n Hpe.
  apply (H n).
  rewrite <- (denote_to_ct c1 n).
  rewrite <- (denote_to_ct c2 n).
  exact Hpe.
Qed.

Theorem phi_preserves_convention :
  forall a b : DR.Entity,
    DR.convention_eq a b ->
    CR.convention_eq (phi a) (phi b).
Proof.
  intros a b Hconv.
  destruct a as [c1 t1 | n1 t1];
    destruct b as [c2 t2 | n2 t2];
    try (simpl in Hconv; contradiction).
  simpl in Hconv. destruct Hconv as [Hne [Hce Hpd]].
  simpl. repeat split.
  - intros Heq.
    apply Hne. rewrite <- (from_to_ct c1), <- (from_to_ct c2).
    rewrite Heq. reflexivity.
  - apply cauchy_equivalent_transport. exact Hce.
  - apply pointwise_distinct_transport. exact Hpd.
Qed.
