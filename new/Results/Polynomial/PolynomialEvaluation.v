(* ============================================== *)
(*  PolynomialEvaluation                            *)
(*                                                  *)
(*  The classical ring morphism                      *)
(*                                                  *)
(*     eval_n : ℤ[x] → ℤ                             *)
(*     eval_n p = p(n)                              *)
(*                                                  *)
(*  Implemented via Horner's method:                *)
(*                                                  *)
(*     eval_n (a₀ + a₁ x + a₂ x² + ... + aₖ xᵏ)     *)
(*       = a₀ + n * (a₁ + n * (a₂ + ...))           *)
(*                                                  *)
(*  preserves add, mul, one. A ring homomorphism    *)
(*  in framework form, parameterised by the         *)
(*  evaluation point via a module functor.          *)
(* ============================================== *)

Require Ring.
Require RingMorphism.
Require IntegerRing.
Require PolynomialRing.
Require MultivariatePolynomial.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.


Module IntPoly := MultivariatePolynomial.IntPoly.
Module Z_ := IntegerRing.IntegerRing.


(* =========================================== *)
(*  RAW-LEVEL EVALUATION (Horner's method)     *)
(* =========================================== *)

Fixpoint eval_raw (n : Z) (p : list Z) : Z :=
  match p with
  | [] => 0%Z
  | a :: p' => (a + n * eval_raw n p')%Z
  end.

(* eval_raw distributes over raw_add. *)

Lemma eval_raw_add :
  forall n p q,
    (eval_raw n (IntPoly.raw_add p q) = eval_raw n p + eval_raw n q)%Z.
Proof.
  intros n p. induction p as [| a p' IH]; intros q.
  - simpl. lia.
  - destruct q as [| b q'].
    + simpl. lia.
    + simpl. rewrite IH. unfold Z_.add. lia.
Qed.

(* eval_raw distributes scalar over raw_scale. *)

Lemma eval_raw_scale :
  forall n a p,
    (eval_raw n (IntPoly.raw_scale a p) = a * eval_raw n p)%Z.
Proof.
  intros n a. induction p as [| b p' IH].
  - simpl. lia.
  - simpl. rewrite IH. unfold Z_.mul. lia.
Qed.

(* eval_raw distributes over raw_mul. *)

Lemma eval_raw_mul :
  forall n p q,
    (eval_raw n (IntPoly.raw_mul p q) = eval_raw n p * eval_raw n q)%Z.
Proof.
  intros n p. induction p as [| a p' IH]; intros q.
  - simpl. lia.
  - change (IntPoly.raw_mul (a :: p') q)
      with (IntPoly.raw_add (IntPoly.raw_scale a q) (0%Z :: IntPoly.raw_mul p' q)).
    rewrite eval_raw_add.
    rewrite eval_raw_scale.
    simpl eval_raw at 2.
    rewrite IH.
    simpl.
    unfold Z_.add, Z_.mul.
    lia.
Qed.

(* eval_raw is invariant under raw_normalize. *)

Lemma eval_raw_normalize :
  forall n p,
    (eval_raw n (IntPoly.raw_normalize p) = eval_raw n p)%Z.
Proof.
  intros n. induction p as [| a p' IH].
  - reflexivity.
  - rewrite IntPoly.raw_normalize_cons.
    destruct (IntPoly.raw_normalize p') as [| b bs] eqn:Hn.
    + (* raw_normalize p' = []; IH auto-rewritten to eval_raw n [] = eval_raw n p' *)
      assert (Hp' : (eval_raw n p' = 0)%Z).
      { simpl in IH. symmetry. exact IH. }
      destruct (Z_.carrier_eq_dec a Z_.zero) as [Ha | Ha].
      * subst a. simpl. rewrite Hp'. unfold Z_.zero. lia.
      * simpl. rewrite Hp'. reflexivity.
    + change (eval_raw n (a :: b :: bs)) with (a + n * eval_raw n (b :: bs))%Z.
      change (eval_raw n (a :: p')) with (a + n * eval_raw n p')%Z.
      rewrite IH. reflexivity.
Qed.


(* =========================================== *)
(*  RING MORPHISM VIA FUNCTOR                  *)
(* =========================================== *)

Module Type EvalPoint.
  Parameter n : Z.
End EvalPoint.

Module EvalMor (P : EvalPoint) <:
  RingMorphism.RingMorphism IntPoly Z_.

  Definition phi (p : IntPoly.Carrier) : Z_.Carrier :=
    eval_raw P.n (proj1_sig p).

  Theorem preserves_add :
    forall p q : IntPoly.Carrier,
      phi (IntPoly.add p q) = Z_.add (phi p) (phi q).
  Proof.
    intros p q. unfold phi, IntPoly.add.
    rewrite IntPoly.canonicalize_proj.
    rewrite eval_raw_normalize.
    apply eval_raw_add.
  Qed.

  Theorem preserves_mul :
    forall p q : IntPoly.Carrier,
      phi (IntPoly.mul p q) = Z_.mul (phi p) (phi q).
  Proof.
    intros p q. unfold phi, IntPoly.mul.
    rewrite IntPoly.canonicalize_proj.
    rewrite eval_raw_normalize.
    apply eval_raw_mul.
  Qed.

  Theorem preserves_one : phi IntPoly.one = Z_.one.
  Proof.
    unfold phi, IntPoly.one.
    rewrite IntPoly.canonicalize_proj.
    rewrite eval_raw_normalize.
    unfold Z_.one, IntegerRing.IntegerRing.one.
    change (eval_raw P.n [1%Z]) with (1 + P.n * 0)%Z.
    rewrite Z.mul_0_r. reflexivity.
  Qed.

End EvalMor.


(* =========================================== *)
(*  CONCRETE INSTANTIATIONS                    *)
(* =========================================== *)

Module EvalAt0 <: EvalPoint.
  Definition n : Z := 0%Z.
End EvalAt0.

Module EvalAt2 <: EvalPoint.
  Definition n : Z := 2%Z.
End EvalAt2.

Module Ev0 := EvalMor EvalAt0.
Module Ev2 := EvalMor EvalAt2.


(* =========================================== *)
(*  DERIVED THEOREMS VIA MORPHISM THEORY       *)
(* =========================================== *)

Module Ev0_Theory := RingMorphism.RingMorphismTheory IntPoly Z_ Ev0.
Module Ev2_Theory := RingMorphism.RingMorphismTheory IntPoly Z_ Ev2.

(* phi preserves zero and negation, derived. *)

Check Ev0_Theory.preserves_zero.
Check Ev2_Theory.preserves_neg.


(* =========================================== *)
(*  CONCRETE WITNESSES                         *)
(* =========================================== *)

(* eval_at 0 applied to the zero polynomial. *)

Example ev0_of_zero : Ev0.phi IntPoly.zero = 0%Z.
Proof. unfold Ev0.phi. simpl. reflexivity. Qed.

(* eval_at 2 applied to the one polynomial. *)

Example ev2_of_one : Ev2.phi IntPoly.one = 1%Z.
Proof. apply Ev2.preserves_one. Qed.

(* eval_at 0 of any p gives the constant coefficient. For the
   zero polynomial, that is 0. *)

Example ev0_zero_is_zero : Ev0.phi IntPoly.zero = 0%Z.
Proof. exact ev0_of_zero. Qed.
