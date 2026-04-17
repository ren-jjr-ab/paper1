(* ============================================== *)
(*  RationalToCauchyMorphism                        *)
(*                                                  *)
(*  phi : RationalRep.Entity -> CauchyReal.Entity   *)
(*                                                  *)
(*    REnt q t   ↦   REnt (CTConst q) t            *)
(*    CMark t    ↦   CEval 0 t                     *)
(*                                                  *)
(*  phi is interact-preserving and injective.       *)
(*                                                  *)
(*  Cross-system demonstration:                     *)
(*                                                  *)
(*  1. Actual computation — interact values match   *)
(*     between RationalRep (Qred) and CauchyReal    *)
(*     (CEval with denote of CTConst).              *)
(*                                                  *)
(*  2. Paper_projection from RationalRep lifts      *)
(*     to CauchyReal via framework's                *)
(*     morphism_carries_agreement. No ad-hoc        *)
(*     re-proof.                                    *)
(*                                                  *)
(*  3. CauchyReal's convention_eq has no phi        *)
(*     pre-image — CTSum / CTInvSucc / CTScale /    *)
(*     CTNeg shapes are outside phi's range. The    *)
(*     ≈ layer is genuinely new information.        *)
(* ============================================== *)

Require Existence.
Require ExistenceMorphism.
Require ExternalTime.
Require RationalRep.
Require CauchyReal.
Require RationalRepTest.
Require CauchyRealTest.
From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import PArith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


(* =========================================== *)
(*  MODULE ALIASES + FUNCTOR                   *)
(* =========================================== *)

Module RR := RationalRep.RationalRep.
Module CR := CauchyReal.CauchyReal.
Module Phi := ExistenceMorphism.Make RR CR.


(* =========================================== *)
(*  phi                                         *)
(* =========================================== *)

Definition phi (a : RR.Entity) : CR.Entity :=
  match a with
  | RR.REnt q t => CR.REnt (CR.CTConst q) t
  | RR.CMark t  => CR.CEval 0 t
  end.


(* =========================================== *)
(*  STEP 3 — phi is injective                  *)
(* =========================================== *)

Theorem phi_injective : Phi.injective phi.
Proof.
  intros a b Hab.
  destruct a as [q1 t1 | t1]; destruct b as [q2 t2 | t2];
    simpl in Hab; inversion Hab; reflexivity.
Qed.


(* =========================================== *)
(*  STEP 4 — phi preserves interact            *)
(* =========================================== *)

Theorem phi_preserves_interact : Phi.preserves_interact phi.
Proof.
  intros a b.
  unfold RR.interact, CR.interact.
  destruct (RR.entity_eq_dec a b) as [Hab_eq | Hab_ne].
  - (* a = b: both sides self-return *)
    subst b.
    destruct (CR.entity_eq_dec (phi a) (phi a)) as [_ | Hne].
    + reflexivity.
    + exfalso. apply Hne. reflexivity.
  - (* a <> b: show phi a <> phi b, then compare computed forms *)
    destruct (CR.entity_eq_dec (phi a) (phi b)) as [Hphi_eq | Hphi_ne].
    + exfalso. apply Hab_ne. apply phi_injective. exact Hphi_eq.
    + destruct a as [q1 t1 | t1]; destruct b as [q2 t2 | t2];
        simpl; reflexivity.
Qed.


(* =========================================== *)
(*  STEP 5 — RATIONAL SIDE COMPUTATION         *)
(*                                             *)
(*  1/2 and 2/4 at CMark viewpoint: both       *)
(*  canonicalize to REnt (1#2) 1 via Qred.     *)
(* =========================================== *)

Compute RR.interact (RR.REnt (1#2) 0) (RR.CMark 0).
(* = RR.REnt (1#2) 1 *)

Compute RR.interact (RR.REnt (2#4) 0) (RR.CMark 0).
(* = RR.REnt (1#2) 1  — same concrete term *)


(* =========================================== *)
(*  STEP 6 — phi-LIFTED COMPUTATION            *)
(*                                             *)
(*  Through phi, the same canonicalization     *)
(*  happens in CauchyReal via CEval: denote    *)
(*  of CTConst q at index 0 is q, Qred'd.      *)
(* =========================================== *)

Compute CR.interact (phi (RR.REnt (1#2) 0))
                    (phi (RR.CMark 0)).
(* = CR.REnt (CR.CTConst (1#2)) 1 *)

Compute CR.interact (phi (RR.REnt (2#4) 0))
                    (phi (RR.CMark 0)).
(* = CR.REnt (CR.CTConst (1#2)) 1  — same concrete term *)

(* ε-δ side demo: Cauchy sum evaluated at n=3 *)
Compute CR.denote (CR.CTSum (CR.CTConst 1) CR.CTInvSucc) 3.
(* = 5 # 4  (1 + 1/4) *)

Compute CR.interact
  (CR.REnt (CR.CTSum (CR.CTConst 1) CR.CTInvSucc) 0)
  (CR.CEval 3 0).
(* = CR.REnt (CR.CTConst (5#4)) 1 *)

Compute CR.interact
  (CR.REnt (CR.CTConst 1) 0)
  (CR.CEval 3 0).
(* = CR.REnt (CR.CTConst 1) 1 *)

(* These two differ at n=3 — witnesses pointwise_distinct concretely. *)


(* =========================================== *)
(*  STEP 7 — PAPER_PROJECTION LIFT             *)
(*                                             *)
(*  RationalRepTest.halves_1_2_and_2_4_        *)
(*  paper_projection provides the fact in      *)
(*  RR. We lift it to CR via framework's       *)
(*  morphism_carries_agreement — no ad-hoc     *)
(*  Qred_complete / rational_equivalent_       *)
(*  paper_projection re-invocation.            *)
(* =========================================== *)

Theorem halves_paper_projection_in_cauchyreal :
  (exists c : CR.Entity,
     CR.interact (phi RationalRepTest.half_1_2) c =
     CR.interact (phi RationalRepTest.half_2_4) c)
  /\ phi RationalRepTest.half_1_2 <> phi RationalRepTest.half_2_4.
Proof.
  destruct RationalRepTest.halves_1_2_and_2_4_paper_projection
    as [[c Hc] Hne].
  split.
  - exists (phi c).
    apply (Phi.morphism_carries_agreement phi phi_preserves_interact
             RationalRepTest.half_1_2 RationalRepTest.half_2_4 c Hc).
  - intro Heq. apply Hne. apply phi_injective. exact Heq.
Qed.


(* =========================================== *)
(*  STEP 8 — phi IMAGE SHAPE                   *)
(*                                             *)
(*  Every phi output is either REnt (CTConst   *)
(*  q) t or CEval 0 t. No other shape.         *)
(* =========================================== *)

Theorem phi_image_shape :
  forall a : RR.Entity,
    (exists q t, phi a = CR.REnt (CR.CTConst q) t) \/
    (exists t, phi a = CR.CEval 0 t).
Proof.
  intro a. destruct a as [q t | t].
  - left. exists q, t. reflexivity.
  - right. exists t. reflexivity.
Qed.


(* =========================================== *)
(*  STEP 9 — ≈ ELEMENT HAS NO phi PRE-IMAGE    *)
(*                                             *)
(*  CauchyRealTest.one_plus_invsucc =          *)
(*    CTSum (CTConst 1) CTInvSucc              *)
(*                                             *)
(*  is a CTSum shape. phi never produces       *)
(*  CTSum. Therefore no RR entity maps to      *)
(*  REnt one_plus_invsucc _, and the           *)
(*  convention_eq pair involving it is         *)
(*  strictly outside phi's range.              *)
(* =========================================== *)

Theorem one_plus_invsucc_no_phi_preimage :
  ~ exists a : RR.Entity,
      phi a = CR.REnt CauchyRealTest.one_plus_invsucc 0.
Proof.
  intros [a Ha].
  destruct a as [q t | t]; simpl in Ha; inversion Ha.
Qed.


(* =========================================== *)
(*  NON-TRIVIAL BONUS                           *)
(* =========================================== *)

(* --- 1. preserves_interact, reflexivity-level --- *)
(*                                                 *)
(*  For specific pairs, phi's commutation with     *)
(*  interact reduces to literal Leibniz equality.  *)
(*  The theorem phi_preserves_interact holds       *)
(*  abstractly; these examples show it holds       *)
(*  COMPUTATIONALLY for concrete rationals.        *)

Example phi_preserves_halves_cmark_computationally :
  phi (RR.interact (RR.REnt (1#2) 0) (RR.CMark 0)) =
  CR.interact (phi (RR.REnt (1#2) 0)) (phi (RR.CMark 0)).
Proof. reflexivity. Qed.

Example phi_preserves_two_sixths_computationally :
  phi (RR.interact (RR.REnt (2#6) 3) (RR.CMark 5)) =
  CR.interact (phi (RR.REnt (2#6) 3)) (phi (RR.CMark 5)).
Proof. reflexivity. Qed.


(* --- 2. witness identification ------------- *)
(*                                             *)
(*  RationalRep's rational_equivalent_paper_    *)
(*  projection uses CMark 0 as the witness.    *)
(*  Under phi this becomes CEval 0 0 —          *)
(*  the natural "evaluate at index 0"           *)
(*  viewpoint in CauchyReal.                    *)

Example phi_maps_CMark_0_to_CEval_0 :
  phi (RR.CMark 0) = CR.CEval 0 0.
Proof. reflexivity. Qed.


(* --- 3. generalized rational pair transfer -------- *)
(*                                                     *)
(*  For ANY Qeq-equal but Leibniz-distinct q1, q2,    *)
(*  their REnt embeddings are paper_projection in      *)
(*  CauchyReal, with witness CEval 0 0. Framework     *)
(*  theorem does the lifting — no re-proof of Qred.   *)

Theorem phi_transfers_rational_projection :
  forall (q1 q2 : Q) (t : nat),
    (q1 == q2)%Q ->
    q1 <> q2 ->
    (exists c : CR.Entity,
       CR.interact (phi (RR.REnt q1 t)) c =
       CR.interact (phi (RR.REnt q2 t)) c)
    /\ phi (RR.REnt q1 t) <> phi (RR.REnt q2 t).
Proof.
  intros q1 q2 t Heq Hne.
  destruct (RR.rational_equivalent_paper_projection q1 q2 t Heq Hne)
    as [[c Hc] Hne2].
  apply (Phi.injective_morphism_preserves_projection
           phi phi_preserves_interact phi_injective
           (RR.REnt q1 t) (RR.REnt q2 t) Hne2 c Hc).
Qed.


(* --- 4. classical "1/2 = 2/4" disambiguation --- *)
(*                                                  *)
(*  Classical math writes "1/2 = 2/4" with one      *)
(*  sign. The framework splits this into three      *)
(*  verdicts, each computable/provable.             *)

Definition half_image  : CR.Entity := phi (RR.REnt (1#2) 0).
Definition fourth_image : CR.Entity := phi (RR.REnt (2#4) 0).

(* (a) NOT ≡ (Leibniz-distinct) *)
Example half_and_fourth_not_leibniz :
  half_image <> fourth_image.
Proof. intro H. inversion H. Qed.

(* (b) IS = (paper_projection via CEval 0 0) *)
Example half_and_fourth_paper_projection :
  CR.interact half_image (CR.CEval 0 0) =
  CR.interact fourth_image (CR.CEval 0 0).
Proof. reflexivity. Qed.

(* (c) NOT ≈ (not convention_eq; pointwise EQUAL
       contradicts pointwise_distinct) *)
Example half_and_fourth_not_convention :
  ~ CR.convention_eq half_image fourth_image.
Proof.
  intros [_ [_ Hpd]].
  apply (Hpd 0%nat). simpl. reflexivity.
Qed.


(* --- 5. non-equivalent rationals stay distinct --- *)
(*                                                    *)
(*  1/2 and 1/3 disagree valuewise. Through phi       *)
(*  + CEval, their evaluation viewpoints yield        *)
(*  distinct concrete terms. No collapse.             *)

Example half_and_third_disagree_at_CEval_0 :
  CR.interact (phi (RR.REnt (1#2) 0)) (CR.CEval 0 0) <>
  CR.interact (phi (RR.REnt (1#3) 0)) (CR.CEval 0 0).
Proof. intro H. inversion H. Qed.


(* =========================================== *)
(*  STEP 10 — phi CANNOT WITNESS CONVENTION    *)
(*                                             *)
(*  Strongest non-liftability result:          *)
(*  NO pair a, b in RationalRep produces a     *)
(*  convention_eq pair in CauchyReal under     *)
(*  phi.                                       *)
(*                                             *)
(*  Structural reason — phi's image is         *)
(*  constant-sequence-or-CEval-only. Two       *)
(*  constants being cauchy_equivalent forces   *)
(*  their Q-values to agree (archimedean),     *)
(*  but convention_eq also demands pointwise   *)
(*  distinctness — contradiction.              *)
(* =========================================== *)

Lemma archimedean_inv_succ :
  forall eps : Q, (0 < eps)%Q ->
    exists k : nat, (1 # Pos.of_succ_nat k < eps)%Q.
Proof.
  intros [a b] Hpos.
  assert (Ha : (0 < a)%Z).
  { unfold Qlt in Hpos. simpl in Hpos. lia. }
  exists (Pos.to_nat b).
  unfold Qlt. simpl.
  assert (Hsucc : (Zpos (Pos.of_succ_nat (Pos.to_nat b)) = Zpos b + 1)%Z).
  { replace (Pos.of_succ_nat (Pos.to_nat b)) with (Pos.succ b).
    - apply Pos2Z.inj_succ.
    - apply Pos2Nat.inj.
      rewrite SuccNat2Pos.id_succ.
      rewrite Pos2Nat.inj_succ.
      reflexivity. }
  rewrite Hsucc.
  nia.
Qed.

Lemma cauchy_equivalent_CTConst_forces_Qeq :
  forall q1 q2 : Q,
    CR.cauchy_equivalent (CR.CTConst q1) (CR.CTConst q2) ->
    (q1 == q2)%Q.
Proof.
  intros q1 q2 Hce.
  destruct (Qeq_dec q1 q2) as [Heq | Hne]; [exact Heq |].
  exfalso.
  (* ~(q1 == q2) ⇒ ~(q1 - q2 == 0) *)
  assert (Hdiff_ne : ~ (q1 - q2 == 0)%Q).
  { intro H. apply Hne.
    setoid_replace q1 with (q1 - q2 + q2) by ring.
    rewrite H. ring. }
  (* Qabs (q1 - q2) > 0 *)
  assert (Habs_pos : (0 < Qabs (q1 - q2))%Q).
  { pose proof (Qabs_nonneg (q1 - q2)) as Hge.
    apply Qle_lteq in Hge.
    destruct Hge as [Hlt | Heq_abs]; [exact Hlt |].
    exfalso. apply Hdiff_ne.
    apply (Qabs_case (q1 - q2)
             (fun y => (y == 0 -> q1 - q2 == 0)%Q)).
    - intros _ H. exact H.
    - intros _ H.
      setoid_replace (q1 - q2) with (- - (q1 - q2)) by ring.
      rewrite H. ring.
    - symmetry. exact Heq_abs. }
  (* Archimedean: ∃k, 1/(k+1) < Qabs (q1 - q2) *)
  destruct (archimedean_inv_succ (Qabs (q1 - q2)) Habs_pos) as [k Hk].
  (* Cauchy bound at this k *)
  destruct (Hce k) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  simpl in HN.
  (* HN: Qabs (q1 - q2) ≤ 1/(k+1); Hk: 1/(k+1) < Qabs (q1 - q2) *)
  apply (Qlt_irrefl (Qabs (q1 - q2))).
  apply (Qle_lt_trans _ (1 # Pos.of_succ_nat k)); assumption.
Qed.

Theorem phi_cannot_witness_convention :
  forall a b : RR.Entity,
    ~ CR.convention_eq (phi a) (phi b).
Proof.
  intros a b Hconv.
  destruct a as [q1 t1 | t1]; destruct b as [q2 t2 | t2];
    simpl in Hconv; try contradiction.
  destruct Hconv as [_ [Hce Hpd]].
  apply (Hpd 0%nat). simpl.
  apply cauchy_equivalent_CTConst_forces_Qeq. exact Hce.
Qed.
