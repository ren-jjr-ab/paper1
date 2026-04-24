(* ============================================== *)
(*  CauchyLimits — Classical limit theorems         *)
(*                                                  *)
(*  Using CauchyReal's structural grammar           *)
(*  (CTConst, CTInvSucc, CTSum, CTNeg, CTScale),    *)
(*  prove several classical limits via direct       *)
(*  ε-δ reasoning — no external axioms, no          *)
(*  postulates.                                     *)
(*                                                  *)
(*  Limits proved:                                  *)
(*                                                  *)
(*    1/(n+1)       →  0                            *)
(*    -1/(n+1)      →  0                            *)
(*    q + 1/(n+1)   →  q   (for any rational q)    *)
(*    q - 1/(n+1)   →  q   (for any rational q)    *)
(*                                                  *)
(*  Specializations (classical textbook names):     *)
(*                                                  *)
(*    (n+1)/n → 1   as   1 + 1/(n+1) → 1           *)
(*    n/(n+1) → 1   as   1 - 1/(n+1) → 1           *)
(*                                                  *)
(*  Utility lemmas:                                 *)
(*                                                  *)
(*    pointwise_equal ⇒ cauchy_equivalent           *)
(*    cauchy_equivalent is reflexive                *)
(* ============================================== *)

Require Cauchy.
From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import PArith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


Module CR := Cauchy.CauchyReal.


(* =========================================== *)
(*  HELPERS                                    *)
(* =========================================== *)

Lemma Qle_inv_succ_nat :
  forall k n : nat, (k <= n)%nat ->
    (1 # Pos.of_succ_nat n <= 1 # Pos.of_succ_nat k)%Q.
Proof.
  intros k n Hle.
  unfold Qle. simpl.
  apply Pos2Z.pos_le_pos.
  apply Pos2Nat.inj_le.
  rewrite !SuccNat2Pos.id_succ.
  lia.
Qed.


(* =========================================== *)
(*  UTILITY                                    *)
(* =========================================== *)

Lemma Qminus_diag_eq : forall x : Q, (x - x == 0 # 1)%Q.
Proof. intros x. ring. Qed.

Lemma pointwise_equal_cauchy_equivalent :
  forall s1 s2 : CR.CauchyTerm,
    CR.pointwise_equal s1 s2 ->
    CR.cauchy_equivalent s1 s2.
Proof.
  intros s1 s2 Hpe k. exists 0%nat. intros n _.
  rewrite (Hpe n).
  rewrite (Qminus_diag_eq (CR.denote s2 n)).
  simpl. unfold Qle. simpl. lia.
Qed.

Lemma cauchy_equivalent_refl :
  forall s : CR.CauchyTerm, CR.cauchy_equivalent s s.
Proof.
  intro s. apply pointwise_equal_cauchy_equivalent.
  intro n. reflexivity.
Qed.


(* =========================================== *)
(*  CLASSICAL LIMIT THEOREMS                   *)
(* =========================================== *)

(* 1/(n+1) → 0 *)
Theorem invsucc_to_zero :
  CR.cauchy_equivalent CR.CTInvSucc (CR.CTConst 0).
Proof.
  intros k. exists k. intros n Hn.
  cbn [CR.denote].
  setoid_replace (Qabs ((1 # Pos.of_succ_nat n) - 0))%Q
    with (1 # Pos.of_succ_nat n)%Q.
  - apply Qle_inv_succ_nat. exact Hn.
  - rewrite Qabs_pos; [ring | unfold Qle; simpl; lia].
Qed.

(* -1/(n+1) → 0 *)
Theorem neg_invsucc_to_zero :
  CR.cauchy_equivalent (CR.CTNeg CR.CTInvSucc) (CR.CTConst 0).
Proof.
  intros k. exists k. intros n Hn.
  cbn [CR.denote].
  setoid_replace (Qabs ((- (1 # Pos.of_succ_nat n)) - 0))%Q
    with (1 # Pos.of_succ_nat n)%Q.
  - apply Qle_inv_succ_nat. exact Hn.
  - setoid_replace ((- (1 # Pos.of_succ_nat n)) - 0)%Q
      with (- (1 # Pos.of_succ_nat n))%Q by ring.
    rewrite Qabs_opp.
    rewrite Qabs_pos; [reflexivity | unfold Qle; simpl; lia].
Qed.

(* q + 1/(n+1) → q, any rational q *)
Theorem const_plus_invsucc_to_const :
  forall q : Q,
    CR.cauchy_equivalent
      (CR.CTSum (CR.CTConst q) CR.CTInvSucc)
      (CR.CTConst q).
Proof.
  intros q k. exists k. intros n Hn.
  cbn [CR.denote].
  setoid_replace (Qabs ((q + (1 # Pos.of_succ_nat n)) - q))%Q
    with (1 # Pos.of_succ_nat n)%Q.
  - apply Qle_inv_succ_nat. exact Hn.
  - setoid_replace ((q + (1 # Pos.of_succ_nat n)) - q)%Q
      with (1 # Pos.of_succ_nat n)%Q by ring.
    rewrite Qabs_pos; [reflexivity | unfold Qle; simpl; lia].
Qed.

(* q - 1/(n+1) → q, any rational q *)
Theorem const_minus_invsucc_to_const :
  forall q : Q,
    CR.cauchy_equivalent
      (CR.CTSum (CR.CTConst q) (CR.CTNeg CR.CTInvSucc))
      (CR.CTConst q).
Proof.
  intros q k. exists k. intros n Hn.
  cbn [CR.denote].
  setoid_replace (Qabs ((q + - (1 # Pos.of_succ_nat n)) - q))%Q
    with (1 # Pos.of_succ_nat n)%Q.
  - apply Qle_inv_succ_nat. exact Hn.
  - setoid_replace ((q + - (1 # Pos.of_succ_nat n)) - q)%Q
      with (- (1 # Pos.of_succ_nat n))%Q by ring.
    rewrite Qabs_opp.
    rewrite Qabs_pos; [reflexivity | unfold Qle; simpl; lia].
Qed.


(* =========================================== *)
(*  CLASSICAL NAMED IDENTITIES                 *)
(* =========================================== *)

(* (n+1)/n → 1   as   1 + 1/(n+1) → 1 *)
Example one_plus_inv_to_one :
  CR.cauchy_equivalent
    (CR.CTSum (CR.CTConst 1) CR.CTInvSucc)
    (CR.CTConst 1).
Proof. apply const_plus_invsucc_to_const. Qed.

(* n/(n+1) → 1   as   1 - 1/(n+1) → 1 *)
Example n_over_n_plus_1_to_one :
  CR.cauchy_equivalent
    (CR.CTSum (CR.CTConst 1) (CR.CTNeg CR.CTInvSucc))
    (CR.CTConst 1).
Proof. apply const_minus_invsucc_to_const. Qed.

(* 1/2 + 1/(n+1) → 1/2 *)
Example half_plus_inv_to_half :
  CR.cauchy_equivalent
    (CR.CTSum (CR.CTConst (1#2)) CR.CTInvSucc)
    (CR.CTConst (1#2)).
Proof. apply const_plus_invsucc_to_const. Qed.

(* 0 + 1/(n+1) → 0, equivalently CTInvSucc ~ CTConst 0 pathway *)
Example zero_plus_inv_to_zero :
  CR.cauchy_equivalent
    (CR.CTSum (CR.CTConst 0) CR.CTInvSucc)
    (CR.CTConst 0).
Proof. apply const_plus_invsucc_to_const. Qed.


(* =========================================== *)
(*  QUADRATIC DECAY — uses CTMul extension     *)
(*                                             *)
(*  1/(n+1)²  →  0                             *)
(*                                             *)
(*  (n+1)² decays FASTER than (n+1). The        *)
(*  proof uses the same N = k trick, plus       *)
(*  (n+1)² ≥ (n+1) ≥ k+1 for n ≥ k.            *)
(* =========================================== *)

Theorem invsucc_squared_to_zero :
  CR.cauchy_equivalent (CR.CTMul CR.CTInvSucc CR.CTInvSucc)
                        (CR.CTConst 0).
Proof.
  intros k. exists k. intros n Hn.
  cbn [CR.denote].
  setoid_replace
    ((1 # Pos.of_succ_nat n) * (1 # Pos.of_succ_nat n) - 0)%Q
    with ((1 # Pos.of_succ_nat n) * (1 # Pos.of_succ_nat n))%Q by ring.
  unfold Qle. simpl.
  apply Pos2Z.pos_le_pos.
  apply Pos2Nat.inj_le.
  rewrite Pos2Nat.inj_mul.
  rewrite !SuccNat2Pos.id_succ.
  nia.
Qed.


(* =========================================== *)
(*  CLASSICAL QUADRATIC IDENTITIES             *)
(* =========================================== *)

(* (1/(n+1))² → 0 *)
Example one_over_n_sq_to_zero :
  CR.cauchy_equivalent (CR.CTMul CR.CTInvSucc CR.CTInvSucc)
                        (CR.CTConst 0).
Proof. exact invsucc_squared_to_zero. Qed.

(* 1 + 1/(n+1)² → 1   (approaches 1 from above, quadratically) *)
Example one_plus_inv_sq_to_one :
  CR.cauchy_equivalent
    (CR.CTSum (CR.CTConst 1) (CR.CTMul CR.CTInvSucc CR.CTInvSucc))
    (CR.CTConst 1).
Proof.
  intros k. exists k. intros n Hn.
  cbn [CR.denote].
  setoid_replace
    ((1 + (1 # Pos.of_succ_nat n) * (1 # Pos.of_succ_nat n)) - 1)%Q
    with ((1 # Pos.of_succ_nat n) * (1 # Pos.of_succ_nat n))%Q by ring.
  unfold Qle. simpl.
  apply Pos2Z.pos_le_pos.
  apply Pos2Nat.inj_le.
  rewrite Pos2Nat.inj_mul.
  rewrite !SuccNat2Pos.id_succ.
  nia.
Qed.


(* =========================================== *)
(*  CONVENTION_EQ FROM DECAY RATES             *)
(*                                             *)
(*  CTMul CTInvSucc CTInvSucc (1/(n+1)²) and   *)
(*  CTConst 0 differ at every n (the squared   *)
(*  value is positive, 0 is zero). They're     *)
(*  cauchy_equivalent (both → 0). Framework    *)
(*  classifies them as ≈ — quadratic decay is  *)
(*  witnessably different from being zero at   *)
(*  every finite index.                        *)
(* =========================================== *)

Theorem invsucc_squared_convention_eq_zero :
  CR.collapse
    (CR.REnt (CR.CTMul CR.CTInvSucc CR.CTInvSucc) 0%nat)
    (CR.REnt (CR.CTConst 0) 0%nat).
Proof.
  apply CR.cauchy_pointwise_distinct_convention.
  - intro H. inversion H.
  - exact invsucc_squared_to_zero.
  - intro n. cbn [CR.denote].
    intro H. unfold Qeq in H. simpl in H. lia.
Qed.


(* =========================================== *)
(*  EDGE CASES — algebraic identities are =   *)
(*                                             *)
(*  Classical algebra (double negation,        *)
(*  identity scalar, zero/one multiplication,  *)
(*  cancellation) produces syntactically       *)
(*  distinct but pointwise-equal terms —       *)
(*  framework classifies as =, not ≈.          *)
(* =========================================== *)

Lemma double_neg_pointwise :
  forall x : CR.CauchyTerm,
    CR.pointwise_equal (CR.CTNeg (CR.CTNeg x)) x.
Proof. intros x n. cbn [CR.denote]. ring. Qed.

Lemma scale_1_pointwise :
  forall x : CR.CauchyTerm,
    CR.pointwise_equal (CR.CTScale 1 x) x.
Proof. intros x n. cbn [CR.denote]. ring. Qed.

Lemma scale_0_pointwise :
  forall x : CR.CauchyTerm,
    CR.pointwise_equal (CR.CTScale 0 x) (CR.CTConst 0).
Proof. intros x n. cbn [CR.denote]. ring. Qed.

Lemma mul_const_0_pointwise :
  forall x : CR.CauchyTerm,
    CR.pointwise_equal (CR.CTMul x (CR.CTConst 0)) (CR.CTConst 0).
Proof. intros x n. cbn [CR.denote]. ring. Qed.

Lemma mul_const_1_pointwise :
  forall x : CR.CauchyTerm,
    CR.pointwise_equal (CR.CTMul x (CR.CTConst 1)) x.
Proof. intros x n. cbn [CR.denote]. ring. Qed.

Lemma sum_neg_pointwise :
  forall x : CR.CauchyTerm,
    CR.pointwise_equal (CR.CTSum x (CR.CTNeg x)) (CR.CTConst 0).
Proof. intros x n. cbn [CR.denote]. ring. Qed.

Lemma mul_assoc_pointwise :
  forall x y z : CR.CauchyTerm,
    CR.pointwise_equal
      (CR.CTMul (CR.CTMul x y) z)
      (CR.CTMul x (CR.CTMul y z)).
Proof. intros x y z n. cbn [CR.denote]. ring. Qed.


(* =========================================== *)
(*  edge identities ⇒ cauchy_equivalent        *)
(*                                             *)
(*  Pointwise-equal implies cauchy_equivalent  *)
(*  trivially. Algebraic edge cases survive    *)
(*  as paper_projection (via CEval) but never  *)
(*  as collapse (≈ requires pointwise_    *)
(*  DIS-tinct).                                *)
(* =========================================== *)

Example double_neg_cauchy_equiv :
  forall x : CR.CauchyTerm,
    CR.cauchy_equivalent (CR.CTNeg (CR.CTNeg x)) x.
Proof.
  intros x. apply pointwise_equal_cauchy_equivalent.
  apply double_neg_pointwise.
Qed.

Example sum_neg_cauchy_equiv :
  forall x : CR.CauchyTerm,
    CR.cauchy_equivalent (CR.CTSum x (CR.CTNeg x)) (CR.CTConst 0).
Proof.
  intros x. apply pointwise_equal_cauchy_equivalent.
  apply sum_neg_pointwise.
Qed.

(* Algebraic identities CANNOT be collapse:
   pointwise_equal means they AGREE at every n,
   contradicting pointwise_distinct. *)

Example double_neg_not_convention :
  forall x : CR.CauchyTerm, forall t1 t2 : nat,
    ~ CR.collapse
        (CR.REnt (CR.CTNeg (CR.CTNeg x)) t1)
        (CR.REnt x t2).
Proof.
  intros x t1 t2 [_ [_ Hpd]].
  apply (Hpd 0%nat).
  apply double_neg_pointwise.
Qed.


(* =========================================== *)
(*  BINOMIAL SQUARE — (a+b)² = a² + 2ab + b²  *)
(*                                             *)
(*  Classical algebraic identity. In the       *)
(*  framework, two DIFFERENT CauchyTerm       *)
(*  syntax trees (multiplied sum vs expanded   *)
(*  sum of products) denote the SAME pointwise *)
(*  value at every n.                          *)
(*                                             *)
(*  Ring tactic closes it — classical algebra  *)
(*  lives IN the = layer of the framework:     *)
(*  syntactically distinct, CEval-witnessed    *)
(*  agreement. Not ≡, not ≈.                   *)
(* =========================================== *)

Theorem binom_square_pointwise :
  forall a b : CR.CauchyTerm,
    CR.pointwise_equal
      (CR.CTMul (CR.CTSum a b) (CR.CTSum a b))
      (CR.CTSum
         (CR.CTSum
            (CR.CTMul a a)
            (CR.CTScale 2 (CR.CTMul a b)))
         (CR.CTMul b b)).
Proof. intros a b n. cbn [CR.denote]. ring. Qed.

Theorem binom_square_cauchy_equivalent :
  forall a b : CR.CauchyTerm,
    CR.cauchy_equivalent
      (CR.CTMul (CR.CTSum a b) (CR.CTSum a b))
      (CR.CTSum
         (CR.CTSum
            (CR.CTMul a a)
            (CR.CTScale 2 (CR.CTMul a b)))
         (CR.CTMul b b)).
Proof.
  intros. apply pointwise_equal_cauchy_equivalent.
  apply binom_square_pointwise.
Qed.

(* Framework verdict: binomial identity is =,
   NOT ≈. The two syntactically distinct terms
   agree at every CEval viewpoint. *)

Theorem binom_square_paper_projection :
  forall a b : CR.CauchyTerm, forall t : nat,
    (CR.CTMul (CR.CTSum a b) (CR.CTSum a b)) <>
    (CR.CTSum
       (CR.CTSum
          (CR.CTMul a a)
          (CR.CTScale 2 (CR.CTMul a b)))
       (CR.CTMul b b)) ->
    (exists c : CR.Entity,
       CR.interact
         (CR.REnt (CR.CTMul (CR.CTSum a b) (CR.CTSum a b)) t) c =
       CR.interact
         (CR.REnt (CR.CTSum
                     (CR.CTSum
                        (CR.CTMul a a)
                        (CR.CTScale 2 (CR.CTMul a b)))
                     (CR.CTMul b b)) t) c)
    /\ CR.REnt (CR.CTMul (CR.CTSum a b) (CR.CTSum a b)) t <>
       CR.REnt (CR.CTSum
                  (CR.CTSum
                     (CR.CTMul a a)
                     (CR.CTScale 2 (CR.CTMul a b)))
                  (CR.CTMul b b)) t.
Proof.
  intros a b t Hne.
  apply CR.pointwise_equal_paper_projection.
  - exact Hne.
  - apply binom_square_pointwise.
Qed.


(* =========================================== *)
(*  CONCRETE INSTANCE                           *)
(*                                             *)
(*  (1 + 1/(n+1))² = 1 + 2/(n+1) + 1/(n+1)²    *)
(*                                             *)
(*  Famous. Classical expansion of (1 + 1/n)². *)
(* =========================================== *)

Example one_plus_invsucc_squared_expands :
  CR.pointwise_equal
    (CR.CTMul (CR.CTSum (CR.CTConst 1) CR.CTInvSucc)
              (CR.CTSum (CR.CTConst 1) CR.CTInvSucc))
    (CR.CTSum
       (CR.CTSum
          (CR.CTMul (CR.CTConst 1) (CR.CTConst 1))
          (CR.CTScale 2 (CR.CTMul (CR.CTConst 1) CR.CTInvSucc)))
       (CR.CTMul CR.CTInvSucc CR.CTInvSucc)).
Proof. apply binom_square_pointwise. Qed.
