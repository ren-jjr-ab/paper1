(* ============================================== *)
(*  ModularRing                                     *)
(*                                                  *)
(*  ℤ/nℤ as a DecEqCommRingSig instance, for an    *)
(*  arbitrary positive modulus n. Carrier is the   *)
(*  canonical subset {z : Z | 0 <= z < n}. All      *)
(*  operations funnel through canonicalize         *)
(*  (Z.modulo).                                     *)
(*                                                  *)
(*  Concrete instantiation:                         *)
(*    Mod7Ring := ModularRing Mod7Modulus          *)
(* ============================================== *)

Require Import Ring.
Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Eqdep_dec.


Module Type ModulusSig.
  Parameter n : Z.
  Axiom n_positive : (0 < n)%Z.
End ModulusSig.


Module ModularRing (M : ModulusSig) <: DecEqCommRingSig.

  Lemma n_nonzero : (M.n <> 0)%Z.
  Proof. pose proof M.n_positive. lia. Qed.

  Definition in_range_bool (z : Z) : bool :=
    (0 <=? z)%Z && (z <? M.n)%Z.

  Lemma in_range_bool_spec :
    forall z : Z, in_range_bool z = true <-> (0 <= z < M.n)%Z.
  Proof.
    intros z. unfold in_range_bool.
    rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. reflexivity.
  Qed.

  Lemma in_range_proof_unique :
    forall (z : Z) (p1 p2 : in_range_bool z = true), p1 = p2.
  Proof.
    intros z p1 p2. apply UIP_dec. apply bool_dec.
  Qed.

  Definition Carrier : Type := { z : Z | in_range_bool z = true }.

  Lemma sig_eq_by_value :
    forall (x y : Carrier), proj1_sig x = proj1_sig y -> x = y.
  Proof.
    intros [xv xp] [yv yp] Hv. simpl in Hv. subst yv.
    f_equal. apply in_range_proof_unique.
  Qed.

  Lemma proj_in_range :
    forall x : Carrier, (0 <= proj1_sig x < M.n)%Z.
  Proof.
    intros [xv xp]. simpl. apply in_range_bool_spec. exact xp.
  Qed.

  Definition canonicalize (z : Z) : Carrier.
  Proof.
    exists (Z.modulo z M.n).
    apply in_range_bool_spec.
    apply Z.mod_pos_bound. apply M.n_positive.
  Defined.

  Definition zero : Carrier.
  Proof.
    exists 0%Z.
    apply in_range_bool_spec.
    split; [apply Z.le_refl | apply M.n_positive].
  Defined.

  Definition one : Carrier := canonicalize 1%Z.

  Definition add (x y : Carrier) : Carrier :=
    canonicalize (proj1_sig x + proj1_sig y).

  Definition mul (x y : Carrier) : Carrier :=
    canonicalize (proj1_sig x * proj1_sig y).

  Definition neg (x : Carrier) : Carrier :=
    canonicalize (- proj1_sig x).

  (* --- Semiring / Ring axioms --- *)

  Theorem add_assoc : forall a b c, add (add a b) c = add a (add b c).
  Proof.
    intros a b c. apply sig_eq_by_value. simpl.
    rewrite Z.add_mod_idemp_l by apply n_nonzero.
    rewrite Z.add_mod_idemp_r by apply n_nonzero.
    rewrite Z.add_assoc. reflexivity.
  Qed.

  Theorem add_comm : forall a b, add a b = add b a.
  Proof.
    intros a b. apply sig_eq_by_value. simpl.
    rewrite Z.add_comm. reflexivity.
  Qed.

  Theorem add_zero_l : forall a, add zero a = a.
  Proof.
    intros a. apply sig_eq_by_value. simpl.
    apply Z.mod_small. apply proj_in_range.
  Qed.

  Theorem mul_assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
  Proof.
    intros a b c. apply sig_eq_by_value. simpl.
    rewrite Z.mul_mod_idemp_l by apply n_nonzero.
    rewrite Z.mul_mod_idemp_r by apply n_nonzero.
    rewrite Z.mul_assoc. reflexivity.
  Qed.

  Theorem mul_one_l : forall a, mul one a = a.
  Proof.
    intros a. apply sig_eq_by_value. simpl.
    rewrite Z.mul_mod_idemp_l by apply n_nonzero.
    rewrite Z.mul_1_l. apply Z.mod_small. apply proj_in_range.
  Qed.

  Theorem mul_one_r : forall a, mul a one = a.
  Proof.
    intros a. apply sig_eq_by_value. simpl.
    rewrite Z.mul_mod_idemp_r by apply n_nonzero.
    rewrite Z.mul_1_r. apply Z.mod_small. apply proj_in_range.
  Qed.

  Theorem mul_zero_l : forall a, mul zero a = zero.
  Proof.
    intros a. unfold mul, zero. apply sig_eq_by_value. simpl.
    apply Z.mod_0_l. apply n_nonzero.
  Qed.

  Theorem mul_zero_r : forall a, mul a zero = zero.
  Proof.
    intros a. unfold mul, zero. apply sig_eq_by_value. simpl.
    rewrite Z.mul_0_r. apply Z.mod_0_l. apply n_nonzero.
  Qed.

  Theorem distrib_l : forall a b c,
    mul a (add b c) = add (mul a b) (mul a c).
  Proof.
    intros a b c. apply sig_eq_by_value. simpl.
    rewrite Z.mul_mod_idemp_r by apply n_nonzero.
    rewrite Z.mul_add_distr_l.
    rewrite Z.add_mod_idemp_l by apply n_nonzero.
    rewrite Z.add_mod_idemp_r by apply n_nonzero.
    reflexivity.
  Qed.

  Theorem distrib_r : forall a b c,
    mul (add a b) c = add (mul a c) (mul b c).
  Proof.
    intros a b c. apply sig_eq_by_value. simpl.
    rewrite Z.mul_mod_idemp_l by apply n_nonzero.
    rewrite Z.mul_add_distr_r.
    rewrite Z.add_mod_idemp_l by apply n_nonzero.
    rewrite Z.add_mod_idemp_r by apply n_nonzero.
    reflexivity.
  Qed.

  Theorem mul_comm : forall a b, mul a b = mul b a.
  Proof.
    intros a b. apply sig_eq_by_value. simpl.
    rewrite Z.mul_comm. reflexivity.
  Qed.

  Theorem add_neg_l : forall a, add (neg a) a = zero.
  Proof.
    intros a. apply sig_eq_by_value. simpl.
    rewrite Z.add_mod_idemp_l by apply n_nonzero.
    rewrite Z.add_opp_diag_l.
    apply Z.mod_0_l. apply n_nonzero.
  Qed.

  Definition carrier_eq_dec : forall a b : Carrier, {a = b} + {a <> b}.
  Proof.
    intros a b.
    destruct (Z.eq_dec (proj1_sig a) (proj1_sig b)) as [Heq | Hne].
    - left. apply sig_eq_by_value. exact Heq.
    - right. intros H. apply Hne. rewrite H. reflexivity.
  Defined.

End ModularRing.


(* ================================================ *)
(*  Mod7Ring — ℤ/7ℤ                                 *)
(* ================================================ *)

Module Mod7Modulus <: ModulusSig.
  Definition n : Z := 7%Z.
  Theorem n_positive : (0 < n)%Z.
  Proof. unfold n. lia. Qed.
End Mod7Modulus.

Module Mod7Ring := ModularRing Mod7Modulus.
