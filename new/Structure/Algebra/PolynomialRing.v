(* ============================================== *)
(*  PolynomialRing                                  *)
(*                                                  *)
(*  R[x] for an arbitrary DecEqCommRingSig R.       *)
(*                                                  *)
(*  Representation:                                 *)
(*    RawPoly := list R.Carrier                     *)
(*                 (index i is the xⁱ coefficient)  *)
(*    Carrier := { p : RawPoly | canonical p }      *)
(*                 canonical = last element non-zero*)
(*                 (or the empty list).             *)
(*                                                  *)
(*  Leibniz equality holds on Carrier because       *)
(*  canonical_prop p is a decidable `= on list`     *)
(*  statement, so UIP applies.                      *)
(*                                                  *)
(*  Operations normalise their result through       *)
(*  raw_normalize, so the subset-type invariant is  *)
(*  preserved constructively.                       *)
(*                                                  *)
(*  The functor exposes itself as DecEqCommRingSig  *)
(*  so PolynomialRing can be iterated:              *)
(*    R → R[x] → R[x][y] → …                        *)
(*  — ring-over-ring nesting that mirrors the       *)
(*  NatSet / NatSetSet pattern.                     *)
(* ============================================== *)

Require Import Ring.
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.


Module PolynomialRing (R : DecEqCommRingSig) <: DecEqCommRingSig.

  Module RT := RingTheory R.


  (* =========================================== *)
  (*  RAW POLYNOMIALS                            *)
  (* =========================================== *)

  Definition RawPoly : Type := list R.Carrier.

  (* raw_normalize strips trailing zeros. *)

  Fixpoint raw_normalize (p : RawPoly) : RawPoly :=
    match p with
    | [] => []
    | c :: p' =>
        match raw_normalize p' with
        | [] => if R.carrier_eq_dec c R.zero then [] else [c]
        | q :: qs => c :: q :: qs
        end
    end.

  Definition canonical_prop (p : RawPoly) : Prop := raw_normalize p = p.


  (* =========================================== *)
  (*  NORMALISATION LEMMAS                        *)
  (* =========================================== *)

  Lemma raw_normalize_cons :
    forall (c : R.Carrier) (p : RawPoly),
      raw_normalize (c :: p) =
      match raw_normalize p with
      | [] => if R.carrier_eq_dec c R.zero then [] else [c]
      | q :: qs => c :: q :: qs
      end.
  Proof. intros. reflexivity. Qed.

  Lemma raw_normalize_idempotent :
    forall p : RawPoly, raw_normalize (raw_normalize p) = raw_normalize p.
  Proof.
    induction p as [| c p' IH]; [reflexivity |].
    destruct (raw_normalize p') as [| q qs] eqn:Hnp.
    - (* raw_normalize p' = [] *)
      destruct (R.carrier_eq_dec c R.zero) as [Hc | Hc].
      + assert (Hcp : raw_normalize (c :: p') = []).
        { rewrite raw_normalize_cons. rewrite Hnp.
          destruct (R.carrier_eq_dec c R.zero); [reflexivity | contradiction]. }
        rewrite Hcp. reflexivity.
      + assert (Hcp : raw_normalize (c :: p') = [c]).
        { rewrite raw_normalize_cons. rewrite Hnp.
          destruct (R.carrier_eq_dec c R.zero); [contradiction | reflexivity]. }
        rewrite Hcp. rewrite raw_normalize_cons. simpl.
        destruct (R.carrier_eq_dec c R.zero); [contradiction | reflexivity].
    - (* raw_normalize p' = q :: qs; Hnp rewrites IH to raw_normalize (q :: qs) = q :: qs *)
      assert (Hcp : raw_normalize (c :: p') = c :: q :: qs).
      { rewrite raw_normalize_cons. rewrite Hnp. reflexivity. }
      rewrite Hcp. rewrite raw_normalize_cons. rewrite IH. reflexivity.
  Qed.

  Lemma raw_normalize_canonical :
    forall p : RawPoly, canonical_prop (raw_normalize p).
  Proof. intros. unfold canonical_prop. apply raw_normalize_idempotent. Qed.


  (* =========================================== *)
  (*  CARRIER — SUBSET TYPE                       *)
  (* =========================================== *)

  Definition Carrier : Type := { p : RawPoly | canonical_prop p }.

  Lemma canonical_prop_unique :
    forall (p : RawPoly) (h1 h2 : canonical_prop p), h1 = h2.
  Proof.
    intros p h1 h2. unfold canonical_prop in *.
    apply UIP_dec. apply list_eq_dec. apply R.carrier_eq_dec.
  Qed.

  Lemma sig_eq_by_value :
    forall (x y : Carrier), proj1_sig x = proj1_sig y -> x = y.
  Proof.
    intros [xv xp] [yv yp] Hv. simpl in Hv. subst yv.
    f_equal. apply canonical_prop_unique.
  Qed.

  Definition canonicalize (p : RawPoly) : Carrier :=
    exist _ (raw_normalize p) (raw_normalize_canonical p).

  Lemma canonicalize_proj :
    forall p : RawPoly, proj1_sig (canonicalize p) = raw_normalize p.
  Proof. intros. reflexivity. Qed.

  Lemma canonicalize_of_canonical :
    forall x : Carrier, canonicalize (proj1_sig x) = x.
  Proof.
    intros [xv xp]. apply sig_eq_by_value. simpl.
    exact xp.
  Qed.


  (* =========================================== *)
  (*  RAW ADD / NEG                               *)
  (* =========================================== *)

  Fixpoint raw_add (p q : RawPoly) : RawPoly :=
    match p, q with
    | [], _ => q
    | _, [] => p
    | a :: p', b :: q' => R.add a b :: raw_add p' q'
    end.

  Lemma raw_add_nil_l : forall q, raw_add [] q = q.
  Proof. intros. reflexivity. Qed.

  Lemma raw_add_nil_r : forall p, raw_add p [] = p.
  Proof. destruct p; reflexivity. Qed.

  Lemma raw_add_comm : forall p q, raw_add p q = raw_add q p.
  Proof.
    induction p as [| a p' IH]; intros [| b q'].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - simpl. rewrite R.add_comm. rewrite IH. reflexivity.
  Qed.

  Lemma raw_add_assoc :
    forall p q r,
      raw_add (raw_add p q) r = raw_add p (raw_add q r).
  Proof.
    induction p as [| a p' IH]; intros q r.
    - reflexivity.
    - destruct q as [| b q'].
      + simpl. reflexivity.
      + destruct r as [| c r'].
        * simpl. reflexivity.
        * simpl. rewrite R.add_assoc. rewrite IH. reflexivity.
  Qed.

  Fixpoint raw_neg (p : RawPoly) : RawPoly :=
    match p with
    | [] => []
    | a :: p' => R.neg a :: raw_neg p'
    end.

  Lemma raw_add_neg_l :
    forall p, raw_normalize (raw_add (raw_neg p) p) = [].
  Proof.
    induction p as [| a p' IH]; simpl.
    - reflexivity.
    - rewrite IH.
      rewrite R.add_neg_l.
      destruct (R.carrier_eq_dec R.zero R.zero) as [_ | Hne];
        [reflexivity | contradiction Hne; reflexivity].
  Qed.


  (* =========================================== *)
  (*  RAW MUL                                     *)
  (* =========================================== *)

  Fixpoint raw_scale (c : R.Carrier) (p : RawPoly) : RawPoly :=
    match p with
    | [] => []
    | a :: p' => R.mul c a :: raw_scale c p'
    end.

  Fixpoint raw_mul (p q : RawPoly) : RawPoly :=
    match p with
    | [] => []
    | a :: p' => raw_add (raw_scale a q) (R.zero :: raw_mul p' q)
    end.


  (* =========================================== *)
  (*  NORMALIZE-COMPATIBLE LEMMAS                 *)
  (* =========================================== *)

  (* If the head is non-zero and the tail is canonical, the whole is canonical. *)

  Lemma canonical_cons :
    forall c p',
      canonical_prop p' ->
      (p' <> [] \/ c <> R.zero) ->
      canonical_prop (c :: p').
  Proof.
    intros c p' Hp Hne. unfold canonical_prop in *. simpl.
    rewrite Hp. destruct p' as [| b p''].
    - destruct Hne as [H | H].
      + exfalso. apply H. reflexivity.
      + destruct (R.carrier_eq_dec c R.zero) as [Hc | Hc];
          [contradiction | reflexivity].
    - reflexivity.
  Qed.

  (* raw_normalize preserves raw_normalize equivalence. *)

  Lemma raw_normalize_add_norm_l :
    forall p q,
      raw_normalize (raw_add (raw_normalize p) q) =
      raw_normalize (raw_add p q).
  Proof.
    induction p as [| a p' IH]; intros q.
    - reflexivity.
    - destruct q as [| c q'].
      + (* q = [] — fold both sides via raw_add_nil_r, then idempotent *)
        rewrite raw_add_nil_r. rewrite raw_add_nil_r.
        apply raw_normalize_idempotent.
      + (* q = c :: q' *)
        destruct (raw_normalize p') as [| b p''] eqn:Hnp'.
        * (* raw_normalize p' = [] *)
          destruct (R.carrier_eq_dec a R.zero) as [Ha | Ha].
          -- (* a = zero *)
             subst a.
             assert (Hn : raw_normalize (R.zero :: p') = []).
             { rewrite raw_normalize_cons. rewrite Hnp'.
               destruct (R.carrier_eq_dec R.zero R.zero) as [_ | Hne];
                 [reflexivity | contradiction Hne; reflexivity]. }
             rewrite Hn. simpl raw_add.
             rewrite R.add_zero_l.
             rewrite raw_normalize_cons.
             rewrite raw_normalize_cons.
             specialize (IH q'). simpl raw_add in IH.
             rewrite IH. reflexivity.
          -- (* a ≠ zero *)
             assert (Hn : raw_normalize (a :: p') = [a]).
             { rewrite raw_normalize_cons. rewrite Hnp'.
               destruct (R.carrier_eq_dec a R.zero);
                 [contradiction | reflexivity]. }
             rewrite Hn. simpl raw_add.
             rewrite raw_normalize_cons.
             rewrite raw_normalize_cons.
             specialize (IH q'). simpl raw_add in IH.
             rewrite IH. reflexivity.
        * (* raw_normalize p' = b :: p'' *)
          assert (Hn : raw_normalize (a :: p') = a :: b :: p'').
          { rewrite raw_normalize_cons. rewrite Hnp'. reflexivity. }
          rewrite Hn.
          change (raw_add (a :: b :: p'') (c :: q'))
            with (R.add a c :: raw_add (b :: p'') q').
          change (raw_add (a :: p') (c :: q'))
            with (R.add a c :: raw_add p' q').
          rewrite (raw_normalize_cons (R.add a c) (raw_add (b :: p'') q')).
          rewrite (raw_normalize_cons (R.add a c) (raw_add p' q')).
          specialize (IH q').
          rewrite IH. reflexivity.
  Qed.

  Lemma raw_normalize_add_norm_r :
    forall p q,
      raw_normalize (raw_add p (raw_normalize q)) =
      raw_normalize (raw_add p q).
  Proof.
    intros p q.
    rewrite (raw_add_comm p (raw_normalize q)).
    rewrite (raw_add_comm p q).
    apply raw_normalize_add_norm_l.
  Qed.


  (* =========================================== *)
  (*  ZERO, ONE, OPERATIONS ON CARRIER            *)
  (* =========================================== *)

  Definition zero : Carrier.
  Proof. exists []. unfold canonical_prop. reflexivity. Defined.

  Definition one : Carrier := canonicalize [R.one].

  Definition add (p q : Carrier) : Carrier :=
    canonicalize (raw_add (proj1_sig p) (proj1_sig q)).

  Definition mul (p q : Carrier) : Carrier :=
    canonicalize (raw_mul (proj1_sig p) (proj1_sig q)).

  Definition neg (p : Carrier) : Carrier :=
    canonicalize (raw_neg (proj1_sig p)).


  (* =========================================== *)
  (*  ADDITIVE ABELIAN GROUP AXIOMS              *)
  (* =========================================== *)

  Theorem add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof.
    intros a b c. apply sig_eq_by_value. simpl.
    rewrite raw_normalize_add_norm_l.
    rewrite raw_normalize_add_norm_r.
    rewrite raw_add_assoc. reflexivity.
  Qed.

  Theorem add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b. apply sig_eq_by_value. simpl.
    rewrite raw_add_comm. reflexivity.
  Qed.

  Theorem add_zero_l : forall a, add zero a = a.
  Proof.
    intros a. apply sig_eq_by_value. simpl.
    destruct a as [av ap]. simpl. exact ap.
  Qed.

  Theorem add_neg_l : forall a, add (neg a) a = zero.
  Proof.
    intros a. apply sig_eq_by_value. simpl.
    rewrite raw_normalize_add_norm_l.
    apply raw_add_neg_l.
  Qed.


  (* =========================================== *)
  (*  MULTIPLICATION: SUPPORTING LEMMAS           *)
  (* =========================================== *)

  Lemma raw_scale_zero_l :
    forall p, raw_normalize (raw_scale R.zero p) = [].
  Proof.
    induction p as [| a p' IH]; simpl.
    - reflexivity.
    - rewrite IH.
      rewrite R.mul_zero_l.
      destruct (R.carrier_eq_dec R.zero R.zero) as [_ | Hne];
        [reflexivity | contradiction Hne; reflexivity].
  Qed.

  Lemma raw_scale_one_l :
    forall p, raw_scale R.one p = p.
  Proof.
    induction p as [| a p' IH]; simpl.
    - reflexivity.
    - rewrite R.mul_one_l. rewrite IH. reflexivity.
  Qed.

  Lemma raw_mul_nil_l : forall q, raw_mul [] q = [].
  Proof. reflexivity. Qed.

  Lemma raw_mul_nil_r :
    forall p, raw_normalize (raw_mul p []) = [].
  Proof.
    induction p as [| a p' IH]; simpl.
    - reflexivity.
    - rewrite IH.
      destruct (R.carrier_eq_dec R.zero R.zero) as [_ | Hne];
        [reflexivity | contradiction Hne; reflexivity].
  Qed.


  (* =========================================== *)
  (*  RAW-LEVEL MUL/SCALE LEMMAS                  *)
  (* =========================================== *)

  Lemma raw_scale_distr_add :
    forall c p q,
      raw_scale c (raw_add p q) = raw_add (raw_scale c p) (raw_scale c q).
  Proof.
    intros c. induction p as [| a p' IH]; intros q.
    - reflexivity.
    - destruct q as [| b q'].
      + simpl. reflexivity.
      + simpl. rewrite R.distrib_l. rewrite IH. reflexivity.
  Qed.

  Lemma raw_scale_scale :
    forall c d p,
      raw_scale c (raw_scale d p) = raw_scale (R.mul c d) p.
  Proof.
    intros c d. induction p as [| a p' IH]; simpl.
    - reflexivity.
    - rewrite IH. rewrite R.mul_assoc. reflexivity.
  Qed.

  (* Adding a "single-zero" polynomial doesn't change the normalize. *)

  Lemma raw_normalize_add_single_zero :
    forall p, raw_normalize (raw_add p [R.zero]) = raw_normalize p.
  Proof.
    induction p as [| a p' IH]; simpl.
    - destruct (R.carrier_eq_dec R.zero R.zero);
        [reflexivity | contradiction].
    - destruct p' as [| b p''].
      + simpl. rewrite RT.add_zero_r. reflexivity.
      + rewrite raw_add_nil_r. rewrite RT.add_zero_r. reflexivity.
  Qed.


  (* =========================================== *)
  (*  DECIDABLE EQUALITY ON CARRIER              *)
  (* =========================================== *)

  Definition carrier_eq_dec : forall a b : Carrier, {a = b} + {a <> b}.
  Proof.
    intros a b.
    destruct (list_eq_dec R.carrier_eq_dec (proj1_sig a) (proj1_sig b))
      as [Heq | Hne].
    - left. apply sig_eq_by_value. exact Heq.
    - right. intros H. apply Hne. rewrite H. reflexivity.
  Defined.


  (* =========================================== *)
  (*  MULTIPLICATIVE MONOID                       *)
  (* =========================================== *)

  Theorem mul_one_l : forall a, mul one a = a.
  Proof.
    intros a. apply sig_eq_by_value.
    unfold mul, one.
    rewrite canonicalize_proj. rewrite canonicalize_proj.
    destruct (R.carrier_eq_dec R.one R.zero) as [Hone | Hone].
    - (* Trivial ring: R.one = R.zero → every carrier element is R.zero
         via x = R.mul R.one x = R.mul R.zero x = R.zero.
         Consequently raw_normalize of any list collapses to []. *)
      assert (Hxzero : forall x : R.Carrier, x = R.zero).
      { intros x. rewrite <- (R.mul_one_l x). rewrite Hone.
        apply R.mul_zero_l. }
      assert (Hnorm_triv : forall p, raw_normalize p = []).
      { induction p as [| x p' IH].
        - reflexivity.
        - rewrite raw_normalize_cons. rewrite IH.
          rewrite (Hxzero x).
          destruct (R.carrier_eq_dec R.zero R.zero);
            [reflexivity | contradiction]. }
      assert (Hav : proj1_sig a = []).
      { destruct a as [av ap]; simpl.
        unfold canonical_prop in ap. rewrite Hnorm_triv in ap.
        symmetry. exact ap. }
      rewrite Hav.
      apply raw_mul_nil_r.
    - (* Normal: R.one ≠ R.zero *)
      assert (Hn : raw_normalize [R.one] = [R.one]).
      { rewrite raw_normalize_cons. simpl.
        destruct (R.carrier_eq_dec R.one R.zero);
          [contradiction | reflexivity]. }
      rewrite Hn.
      simpl raw_mul.
      rewrite raw_scale_one_l.
      simpl raw_mul.
      rewrite raw_normalize_add_single_zero.
      destruct a as [av ap]; simpl. exact ap.
  Qed.

  (* raw_mul by singleton-one on the right preserves normalize. *)

  Lemma raw_mul_single_one_r :
    forall p, raw_normalize (raw_mul p [R.one]) = raw_normalize p.
  Proof.
    induction p as [| a p' IH].
    - reflexivity.
    - simpl raw_mul. simpl raw_scale.
      rewrite R.mul_one_r.
      simpl raw_add.
      rewrite RT.add_zero_r.
      rewrite (raw_normalize_cons a (raw_mul p' [R.one])).
      rewrite (raw_normalize_cons a p').
      rewrite IH. reflexivity.
  Qed.

  Theorem mul_one_r : forall a, mul a one = a.
  Proof.
    intros a. apply sig_eq_by_value.
    unfold mul, one.
    rewrite canonicalize_proj. rewrite canonicalize_proj.
    destruct (R.carrier_eq_dec R.one R.zero) as [Hone | Hone].
    - (* Trivial ring: proj1_sig a = [] *)
      assert (Hxzero : forall x : R.Carrier, x = R.zero).
      { intros x. rewrite <- (R.mul_one_l x). rewrite Hone.
        apply R.mul_zero_l. }
      assert (Hnorm_triv : forall p, raw_normalize p = []).
      { induction p as [| x p' IH].
        - reflexivity.
        - rewrite raw_normalize_cons. rewrite IH.
          rewrite (Hxzero x).
          destruct (R.carrier_eq_dec R.zero R.zero);
            [reflexivity | contradiction]. }
      assert (Hav : proj1_sig a = []).
      { destruct a as [av ap]; simpl.
        unfold canonical_prop in ap. rewrite Hnorm_triv in ap.
        symmetry. exact ap. }
      rewrite Hav.
      simpl raw_mul.
      reflexivity.
    - (* Normal: R.one ≠ R.zero *)
      assert (Hn : raw_normalize [R.one] = [R.one]).
      { rewrite raw_normalize_cons. simpl.
        destruct (R.carrier_eq_dec R.one R.zero);
          [contradiction | reflexivity]. }
      rewrite Hn.
      rewrite raw_mul_single_one_r.
      destruct a as [av ap]; simpl. exact ap.
  Qed.

  (* =========================================== *)
  (*  RAW-LEVEL MUL DISTRIBUTIVITY                *)
  (* =========================================== *)

  Lemma raw_add_cons_cons :
    forall a p b q,
      raw_add (a :: p) (b :: q) = R.add a b :: raw_add p q.
  Proof. reflexivity. Qed.

  Lemma raw_add_zero_cons_zero_cons :
    forall p q,
      raw_add (R.zero :: p) (R.zero :: q) = R.zero :: raw_add p q.
  Proof.
    intros. simpl. rewrite R.add_zero_l. reflexivity.
  Qed.

  (* raw_add is commutative — already have raw_add_comm. *)
  (* raw_add is associative — already have raw_add_assoc. *)

  (* Abelian-group rearrangement: (A + B) + (C + D) = (A + C) + (B + D). *)

  Lemma raw_add_swap :
    forall A B C D,
      raw_add (raw_add A B) (raw_add C D) =
      raw_add (raw_add A C) (raw_add B D).
  Proof.
    intros A B C D.
    rewrite raw_add_assoc.
    rewrite <- (raw_add_assoc B C D).
    rewrite (raw_add_comm B C).
    rewrite (raw_add_assoc C B D).
    rewrite <- (raw_add_assoc A C (raw_add B D)).
    reflexivity.
  Qed.

  Lemma raw_mul_distr_add_r :
    forall p q r,
      raw_mul p (raw_add q r) = raw_add (raw_mul p q) (raw_mul p r).
  Proof.
    induction p as [| a p' IH]; intros q r.
    - reflexivity.
    - simpl raw_mul.
      rewrite raw_scale_distr_add.
      rewrite IH.
      rewrite <- raw_add_zero_cons_zero_cons.
      apply raw_add_swap.
  Qed.

  (* =========================================== *)
  (*  NORMALIZE-INTERCHANGE FOR SCALE             *)
  (* =========================================== *)

  Lemma raw_scale_cons :
    forall c a p,
      raw_scale c (a :: p) = R.mul c a :: raw_scale c p.
  Proof. reflexivity. Qed.

  Lemma raw_normalize_scale_norm :
    forall a q,
      raw_normalize (raw_scale a (raw_normalize q)) =
      raw_normalize (raw_scale a q).
  Proof.
    intros a. induction q as [| b q' IH].
    - reflexivity.
    - destruct (raw_normalize q') as [| r rs] eqn:Hnq'.
      + (* raw_normalize q' = [] *)
        assert (IH' : raw_normalize (raw_scale a q') = []).
        { simpl raw_scale in IH. simpl raw_normalize in IH.
          symmetry. exact IH. }
        destruct (R.carrier_eq_dec b R.zero) as [Hb | Hb].
        * (* b = zero *)
          subst b.
          assert (Hnbq' : raw_normalize (R.zero :: q') = []).
          { rewrite raw_normalize_cons. rewrite Hnq'.
            destruct (R.carrier_eq_dec R.zero R.zero);
              [reflexivity | contradiction]. }
          rewrite Hnbq'.
          rewrite (raw_scale_cons a R.zero q').
          simpl raw_scale.
          simpl raw_normalize at 1.
          rewrite R.mul_zero_r.
          rewrite raw_normalize_cons.
          rewrite IH'.
          destruct (R.carrier_eq_dec R.zero R.zero);
            [reflexivity | contradiction].
        * (* b ≠ zero *)
          assert (Hnbq' : raw_normalize (b :: q') = [b]).
          { rewrite raw_normalize_cons. rewrite Hnq'.
            destruct (R.carrier_eq_dec b R.zero);
              [contradiction | reflexivity]. }
          rewrite Hnbq'.
          rewrite (raw_scale_cons a b q').
          simpl raw_scale.
          rewrite raw_normalize_cons.
          rewrite (raw_normalize_cons (R.mul a b) (raw_scale a q')).
          rewrite IH'.
          reflexivity.
      + (* raw_normalize q' = r :: rs *)
        assert (Hnbq' : raw_normalize (b :: q') = b :: r :: rs).
        { rewrite raw_normalize_cons. rewrite Hnq'. reflexivity. }
        rewrite Hnbq'.
        rewrite (raw_scale_cons a b (r :: rs)).
        rewrite (raw_scale_cons a b q').
        rewrite raw_normalize_cons. rewrite raw_normalize_cons.
        rewrite IH. reflexivity.
  Qed.

  (* =========================================== *)
  (*  NORMALIZE-INTERCHANGE FOR MUL (right arg)   *)
  (* =========================================== *)

  Lemma raw_normalize_mul_norm_r :
    forall p q,
      raw_normalize (raw_mul p (raw_normalize q)) =
      raw_normalize (raw_mul p q).
  Proof.
    induction p as [| a p' IH]; intros q.
    - reflexivity.
    - simpl raw_mul.
      (* LHS: raw_normalize (raw_add (raw_scale a (raw_normalize q))
                                      (R.zero :: raw_mul p' (raw_normalize q))) *)
      (* RHS: raw_normalize (raw_add (raw_scale a q)
                                      (R.zero :: raw_mul p' q)) *)
      rewrite <- raw_normalize_add_norm_l.
      rewrite <- (raw_normalize_add_norm_l (raw_scale a q)).
      rewrite raw_normalize_scale_norm.
      (* Now normalize of (R.zero :: raw_mul p' ...) parts *)
      rewrite <- raw_normalize_add_norm_r.
      rewrite <- (raw_normalize_add_norm_r _ (R.zero :: raw_mul p' q)).
      rewrite raw_normalize_cons.
      rewrite (raw_normalize_cons R.zero (raw_mul p' q)).
      rewrite IH. reflexivity.
  Qed.

  (* =========================================== *)
  (*  DISTRIB_L                                   *)
  (* =========================================== *)

  Theorem distrib_l : forall a b c,
    mul a (add b c) = add (mul a b) (mul a c).
  Proof.
    intros a b c. apply sig_eq_by_value.
    unfold mul, add.
    rewrite !canonicalize_proj.
    rewrite raw_normalize_add_norm_l.
    rewrite raw_normalize_add_norm_r.
    rewrite raw_normalize_mul_norm_r.
    rewrite raw_mul_distr_add_r.
    reflexivity.
  Qed.

  (* =========================================== *)
  (*  RAW-LEVEL MUL DISTRIBUTES OVER ADD (LEFT)   *)
  (* =========================================== *)

  Lemma raw_scale_distr_scalar_add :
    forall c d p,
      raw_scale (R.add c d) p = raw_add (raw_scale c p) (raw_scale d p).
  Proof.
    intros c d. induction p as [| a p' IH].
    - reflexivity.
    - simpl raw_scale. simpl raw_add.
      rewrite R.distrib_r. rewrite IH. reflexivity.
  Qed.

  Lemma raw_mul_distr_add_l :
    forall p q r,
      raw_mul (raw_add p q) r = raw_add (raw_mul p r) (raw_mul q r).
  Proof.
    induction p as [| a p' IH]; intros q r.
    - reflexivity.
    - destruct q as [| b q'].
      + simpl raw_add. rewrite raw_add_nil_r. reflexivity.
      + simpl raw_add. simpl raw_mul.
        rewrite raw_scale_distr_scalar_add.
        rewrite IH.
        rewrite <- raw_add_zero_cons_zero_cons.
        apply raw_add_swap.
  Qed.

  (* =========================================== *)
  (*  NORMALIZE-INTERCHANGE FOR MUL (left arg)    *)
  (* =========================================== *)

  Lemma raw_normalize_mul_norm_l :
    forall p q,
      raw_normalize (raw_mul (raw_normalize p) q) =
      raw_normalize (raw_mul p q).
  Proof.
    induction p as [| a p' IH]; intros q.
    - reflexivity.
    - destruct (raw_normalize p') as [| b p''] eqn:Hnp'.
      + (* raw_normalize p' = []; IH(q): raw_mul [] q = raw_mul p' q at normalize *)
        assert (IH' : raw_normalize (raw_mul p' q) = []).
        { specialize (IH q). simpl raw_mul in IH. symmetry. exact IH. }
        destruct (R.carrier_eq_dec a R.zero) as [Ha | Ha].
        * (* a = zero *)
          subst a.
          assert (Hnap' : raw_normalize (R.zero :: p') = []).
          { rewrite raw_normalize_cons. rewrite Hnp'.
            destruct (R.carrier_eq_dec R.zero R.zero);
              [reflexivity | contradiction]. }
          rewrite Hnap'.
          simpl raw_mul.
          (* RHS: raw_normalize (raw_add (raw_scale R.zero q) (R.zero :: raw_mul p' q)) *)
          rewrite <- raw_normalize_add_norm_l.
          rewrite raw_scale_zero_l.
          rewrite <- raw_normalize_add_norm_r.
          rewrite raw_normalize_cons.
          rewrite IH'.
          destruct (R.carrier_eq_dec R.zero R.zero);
            [reflexivity | contradiction].
        * (* a ≠ zero *)
          assert (Hnap' : raw_normalize (a :: p') = [a]).
          { rewrite raw_normalize_cons. rewrite Hnp'.
            destruct (R.carrier_eq_dec a R.zero);
              [contradiction | reflexivity]. }
          rewrite Hnap'.
          simpl raw_mul at 1.
          rewrite raw_normalize_add_single_zero.
          simpl raw_mul.
          rewrite <- raw_normalize_add_norm_r.
          rewrite raw_normalize_cons.
          rewrite IH'.
          destruct (R.carrier_eq_dec R.zero R.zero) as [_ | Hne];
            [| contradiction Hne; reflexivity].
          rewrite raw_add_nil_r. reflexivity.
      + (* raw_normalize p' = b :: p'' *)
        assert (Hnap' : raw_normalize (a :: p') = a :: b :: p'').
        { rewrite raw_normalize_cons. rewrite Hnp'. reflexivity. }
        rewrite Hnap'.
        change (raw_mul (a :: b :: p'') q)
          with (raw_add (raw_scale a q) (R.zero :: raw_mul (b :: p'') q)).
        change (raw_mul (a :: p') q)
          with (raw_add (raw_scale a q) (R.zero :: raw_mul p' q)).
        rewrite <- raw_normalize_add_norm_r.
        rewrite <- (raw_normalize_add_norm_r (raw_scale a q) (R.zero :: raw_mul p' q)).
        rewrite (raw_normalize_cons R.zero (raw_mul (b :: p'') q)).
        rewrite (raw_normalize_cons R.zero (raw_mul p' q)).
        specialize (IH q).
        rewrite IH. reflexivity.
  Qed.

  (* =========================================== *)
  (*  DISTRIB_R                                   *)
  (* =========================================== *)

  Theorem distrib_r : forall a b c,
    mul (add a b) c = add (mul a c) (mul b c).
  Proof.
    intros a b c. apply sig_eq_by_value.
    unfold mul, add.
    rewrite !canonicalize_proj.
    rewrite raw_normalize_add_norm_l.
    rewrite raw_normalize_add_norm_r.
    rewrite raw_normalize_mul_norm_l.
    rewrite raw_mul_distr_add_l.
    reflexivity.
  Qed.

  (* =========================================== *)
  (*  RAW MUL COMMUTATIVITY (via normalize)       *)
  (* =========================================== *)

  Lemma raw_mul_cons_r_norm :
    forall p b q',
      raw_normalize (raw_mul p (b :: q')) =
      raw_normalize (raw_add (raw_scale b p) (R.zero :: raw_mul p q')).
  Proof.
    induction p as [| a p' IH]; intros b q'.
    - simpl.
      destruct (R.carrier_eq_dec R.zero R.zero);
        [reflexivity | contradiction].
    - change (raw_mul (a :: p') (b :: q'))
        with (raw_add (raw_scale a (b :: q')) (R.zero :: raw_mul p' (b :: q'))).
      rewrite raw_scale_cons.
      change (raw_scale b (a :: p'))
        with (R.mul b a :: raw_scale b p').
      change (raw_mul (a :: p') q')
        with (raw_add (raw_scale a q') (R.zero :: raw_mul p' q')).
      change (raw_add (R.mul a b :: raw_scale a q')
                       (R.zero :: raw_mul p' (b :: q')))
        with (R.add (R.mul a b) R.zero ::
              raw_add (raw_scale a q') (raw_mul p' (b :: q'))).
      change (raw_add (R.mul b a :: raw_scale b p')
                       (R.zero :: raw_add (raw_scale a q')
                                          (R.zero :: raw_mul p' q')))
        with (R.add (R.mul b a) R.zero ::
              raw_add (raw_scale b p')
                      (raw_add (raw_scale a q') (R.zero :: raw_mul p' q'))).
      rewrite !RT.add_zero_r.
      rewrite (R.mul_comm a b).
      rewrite raw_normalize_cons.
      rewrite (raw_normalize_cons (R.mul b a) _).
      rewrite <- raw_normalize_add_norm_r.
      rewrite (IH b q').
      rewrite raw_normalize_add_norm_r.
      rewrite <- raw_add_assoc.
      rewrite (raw_add_comm (raw_scale a q') (raw_scale b p')).
      rewrite raw_add_assoc.
      reflexivity.
  Qed.

  Lemma raw_mul_comm_norm :
    forall p q, raw_normalize (raw_mul p q) = raw_normalize (raw_mul q p).
  Proof.
    induction p as [| a p' IH]; intros q.
    - rewrite raw_mul_nil_r. reflexivity.
    - rewrite (raw_mul_cons_r_norm q a p').
      change (raw_mul (a :: p') q)
        with (raw_add (raw_scale a q) (R.zero :: raw_mul p' q)).
      rewrite <- raw_normalize_add_norm_r.
      rewrite <- (raw_normalize_add_norm_r (raw_scale a q) (R.zero :: raw_mul q p')).
      rewrite (raw_normalize_cons R.zero (raw_mul p' q)).
      rewrite (raw_normalize_cons R.zero (raw_mul q p')).
      specialize (IH q). rewrite IH. reflexivity.
  Qed.

  Theorem mul_comm : forall a b, mul a b = mul b a.
  Proof.
    intros a b. apply sig_eq_by_value.
    unfold mul. rewrite !canonicalize_proj.
    apply raw_mul_comm_norm.
  Qed.

  (* =========================================== *)
  (*  RAW MUL ASSOCIATIVITY                       *)
  (* =========================================== *)

  Lemma raw_mul_scale_l :
    forall a p q,
      raw_mul (raw_scale a p) q = raw_scale a (raw_mul p q).
  Proof.
    intros a. induction p as [| b p' IH]; intros q.
    - reflexivity.
    - rewrite raw_scale_cons.
      change (raw_mul (R.mul a b :: raw_scale a p') q)
        with (raw_add (raw_scale (R.mul a b) q) (R.zero :: raw_mul (raw_scale a p') q)).
      change (raw_mul (b :: p') q)
        with (raw_add (raw_scale b q) (R.zero :: raw_mul p' q)).
      rewrite raw_scale_distr_add.
      rewrite raw_scale_scale.
      rewrite IH.
      rewrite raw_scale_cons.
      rewrite R.mul_zero_r.
      reflexivity.
  Qed.

  Lemma raw_mul_cons_zero_l_norm :
    forall p r, raw_normalize (raw_mul (R.zero :: p) r) = raw_normalize (R.zero :: raw_mul p r).
  Proof.
    intros p r.
    change (raw_mul (R.zero :: p) r)
      with (raw_add (raw_scale R.zero r) (R.zero :: raw_mul p r)).
    rewrite <- raw_normalize_add_norm_l.
    rewrite raw_scale_zero_l.
    rewrite raw_add_nil_l.
    reflexivity.
  Qed.

  Lemma raw_mul_assoc_norm :
    forall p q r,
      raw_normalize (raw_mul (raw_mul p q) r) =
      raw_normalize (raw_mul p (raw_mul q r)).
  Proof.
    induction p as [| a p' IH]; intros q r.
    - reflexivity.
    - change (raw_mul (a :: p') q)
        with (raw_add (raw_scale a q) (R.zero :: raw_mul p' q)).
      rewrite raw_mul_distr_add_l.
      rewrite raw_mul_scale_l.
      rewrite <- raw_normalize_add_norm_r.
      rewrite raw_mul_cons_zero_l_norm.
      rewrite raw_normalize_add_norm_r.
      change (raw_mul (a :: p') (raw_mul q r))
        with (raw_add (raw_scale a (raw_mul q r))
                      (R.zero :: raw_mul p' (raw_mul q r))).
      rewrite <- raw_normalize_add_norm_r.
      rewrite <- (raw_normalize_add_norm_r
                    (raw_scale a (raw_mul q r))
                    (R.zero :: raw_mul p' (raw_mul q r))).
      rewrite (raw_normalize_cons R.zero (raw_mul (raw_mul p' q) r)).
      rewrite (raw_normalize_cons R.zero (raw_mul p' (raw_mul q r))).
      specialize (IH q r). rewrite IH. reflexivity.
  Qed.

  Theorem mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof.
    intros a b c. apply sig_eq_by_value.
    unfold mul. rewrite !canonicalize_proj.
    rewrite raw_normalize_mul_norm_l.
    rewrite raw_normalize_mul_norm_r.
    apply raw_mul_assoc_norm.
  Qed.

  Theorem mul_zero_l : forall a, mul zero a = zero.
  Proof.
    intros a. unfold mul, zero.
    apply sig_eq_by_value. simpl. reflexivity.
  Qed.

  Theorem mul_zero_r : forall a, mul a zero = zero.
  Proof.
    intros a. unfold mul, zero.
    apply sig_eq_by_value. rewrite canonicalize_proj.
    apply raw_mul_nil_r.
  Qed.

End PolynomialRing.
