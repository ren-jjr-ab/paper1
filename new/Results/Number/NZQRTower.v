(* ============================================== *)
(*  NZQRTower                                        *)
(*                                                    *)
(*  The full number-system tower                      *)
(*                                                    *)
(*    ℕ → ℤ → ℚ → ℝ_Cauchy ≅ ℝ_Dedekind              *)
(*    NT   ZT   QT    CR           DR                 *)
(*                                                    *)
(*  Every layer is Expr-based (EConst, EAdd, EMul,   *)
(*  ENeg for Z and Q) with an observer time.         *)
(*  Arithmetic is live at every layer: 3 + 5 can be  *)
(*  written, reduced, and tracked through morphisms  *)
(*  to the reals.                                     *)
(*                                                    *)
(*  All instances share time arithmetic               *)
(*  S (Nat.max (snd a) (snd b)) on non-self          *)
(*  interaction, which is what makes the morphism    *)
(*  chain compose as strict preserves_interact.      *)
(*                                                    *)
(*  Morphisms                                         *)
(*                                                    *)
(*    phi_NZ : NT → ZT  — EConst n ↦ EConst          *)
(*                        (Z.of_nat n); EAdd/EMul    *)
(*                        preserved structurally.    *)
(*                                                    *)
(*    phi_ZQ : ZT → QT  — EConst z ↦ EConst (z#1);   *)
(*                        EAdd/EMul/ENeg preserved   *)
(*                        structurally.              *)
(*                                                    *)
(*    phi_QC : QT → CR  — EConst q ↦ REnt (CTConst   *)
(*                        q) t; EAdd→CTSum,          *)
(*                        EMul→CTMul, ENeg→CTNeg.    *)
(*                                                    *)
(*    psi_CD : CR → DR  — CauchyDedekind isomorphism.*)
(*                                                    *)
(*  All morphisms are strict preserves_interact.     *)
(*  Injectivity and faithfulness are derived.        *)
(*                                                    *)
(*  The algebraic track (IntegerGrothendieck) stays  *)
(*  separate: its dim-dispatch regime is orthogonal  *)
(*  to the analytic S(max) regime used here.         *)
(* ============================================== *)

Require Import Existence.
Require Morphism.
Require Witnessed.
Require SemiringAsWitnessed.
Require RingAsWitnessed.
Require NatSemiring.
Require IntegerRing.
Require RationalField.
Require Cauchy.
Require Dedekind.
Require CauchyDedekind.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qcanon.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.


(* =========================================== *)
(*  INSTANCES                                    *)
(*                                              *)
(*  QT uses RingAsWitnessed applied to          *)
(*  RationalField. RationalField is a           *)
(*  DecEqFieldSig, whose ring substructure      *)
(*  (CommRingSig + carrier_eq_dec) satisfies    *)
(*  DecEqCommRingSig — so the ring functor      *)
(*  accepts it and produces a ring-only Expr    *)
(*  grammar over ℚ. The field's multiplicative  *)
(*  inverse is omitted from QT's grammar, which *)
(*  is what lets phi_QC embed QT structurally   *)
(*  into the CauchyTerm grammar (which has no   *)
(*  general inverse, only CTInvSucc).           *)
(* =========================================== *)

Module NT := SemiringAsWitnessed.Make NatSemiring.NatSemiring.
Module ZT := RingAsWitnessed.Make IntegerRing.IntegerRing.
Module QT := RingAsWitnessed.Make RationalField.RationalField.
Module CR := Cauchy.CauchyReal.
Module DR := Dedekind.DedekindReal.


(* =========================================== *)
(*  MORPHISM MODULES                            *)
(* =========================================== *)

Module M_NZ := Morphism.Make NT ZT.
Module M_ZQ := Morphism.Make ZT QT.
Module M_QC := Morphism.Make QT CR.
Module M_ND := Morphism.Make NT DR.


(* =========================================== *)
(*  phi_NZ : NT → ZT                            *)
(*                                              *)
(*  Map a Semiring-Expr over ℕ to a Ring-Expr   *)
(*  over ℤ by converting constants via          *)
(*  Z.of_nat and preserving the Expr structure. *)
(* =========================================== *)

Fixpoint expr_NZ (e : NT.Expr) : ZT.Expr :=
  match e with
  | NT.EConst n => ZT.EConst (Z.of_nat n)
  | NT.EAdd a b => ZT.EAdd (expr_NZ a) (expr_NZ b)
  | NT.EMul a b => ZT.EMul (expr_NZ a) (expr_NZ b)
  end.

Definition phi_NZ (x : NT.Entity) : ZT.Entity :=
  (expr_NZ (fst x), snd x).

Lemma expr_NZ_injective : forall e1 e2, expr_NZ e1 = expr_NZ e2 -> e1 = e2.
Proof.
  induction e1; intros e2 H; destruct e2;
    try (simpl in H; inversion H; fail); simpl in H.
  - inversion H. apply Nat2Z.inj in H1. subst. reflexivity.
  - inversion H. apply IHe1_1 in H1. apply IHe1_2 in H2. subst. reflexivity.
  - inversion H. apply IHe1_1 in H1. apply IHe1_2 in H2. subst. reflexivity.
Qed.

Theorem phi_NZ_injective : M_NZ.injective phi_NZ.
Proof.
  intros [e1 t1] [e2 t2] H. unfold phi_NZ in H. simpl in H.
  inversion H. apply expr_NZ_injective in H1. subst. reflexivity.
Qed.

Theorem phi_NZ_preserves_interact : M_NZ.preserves_interact phi_NZ.
Proof.
  intros [e1 t1] [e2 t2]. unfold phi_NZ. simpl.
  unfold NT.interact, ZT.interact.
  destruct (NT.entity_eq_dec (e1, t1) (e2, t2)) as [HeqN | HneN].
  - inversion HeqN. subst.
    destruct (ZT.entity_eq_dec (expr_NZ e2, t2) (expr_NZ e2, t2)) as [_ | Hne];
      [reflexivity | exfalso; apply Hne; reflexivity].
  - destruct (ZT.entity_eq_dec (expr_NZ e1, t1) (expr_NZ e2, t2)) as [HeqZ | _].
    + exfalso. apply HneN. inversion HeqZ.
      apply expr_NZ_injective in H0. subst. reflexivity.
    + simpl. reflexivity.
Qed.


(* =========================================== *)
(*  phi_ZQ : ZT → QT                            *)
(*                                              *)
(*  Map a Ring-Expr over ℤ to a Ring-Expr over  *)
(*  ℚ by converting constants via z ↦ z#1 and   *)
(*  preserving the Expr structure.              *)
(* =========================================== *)

Fixpoint expr_ZQ (e : ZT.Expr) : QT.Expr :=
  match e with
  | ZT.EConst z => QT.EConst (Q2Qc (z # 1))
  | ZT.EAdd a b => QT.EAdd (expr_ZQ a) (expr_ZQ b)
  | ZT.EMul a b => QT.EMul (expr_ZQ a) (expr_ZQ b)
  | ZT.ENeg a   => QT.ENeg (expr_ZQ a)
  end.

Definition phi_ZQ (x : ZT.Entity) : QT.Entity :=
  (expr_ZQ (fst x), snd x).

Lemma Q2Qc_inj_equiv : forall p q : Q, Q2Qc p = Q2Qc q -> p == q.
Proof.
  intros p q H. apply (f_equal this) in H. simpl in H.
  rewrite <- (Qred_correct p), <- (Qred_correct q). rewrite H. reflexivity.
Qed.

Lemma Q2Qc_z_over_1_inj : forall z1 z2 : Z,
  Q2Qc (z1 # 1) = Q2Qc (z2 # 1) -> z1 = z2.
Proof.
  intros z1 z2 H. apply Q2Qc_inj_equiv in H.
  unfold Qeq in H. simpl in H. lia.
Qed.

Definition qt_econst_proj (e : QT.Expr) : RationalField.RationalField.Carrier :=
  match e with
  | QT.EConst q => q
  | _ => RationalField.RationalField.zero
  end.

Lemma expr_ZQ_injective : forall e1 e2, expr_ZQ e1 = expr_ZQ e2 -> e1 = e2.
Proof.
  induction e1; intros e2 H; destruct e2;
    try (simpl in H; inversion H; fail); simpl in H.
  - apply (f_equal qt_econst_proj) in H. simpl in H.
    apply Q2Qc_z_over_1_inj in H. subst. reflexivity.
  - inversion H. apply IHe1_1 in H1. apply IHe1_2 in H2. subst. reflexivity.
  - inversion H. apply IHe1_1 in H1. apply IHe1_2 in H2. subst. reflexivity.
  - inversion H. apply IHe1 in H1. subst. reflexivity.
Qed.

Theorem phi_ZQ_injective : M_ZQ.injective phi_ZQ.
Proof.
  intros [e1 t1] [e2 t2] H. unfold phi_ZQ in H. simpl in H.
  inversion H. apply expr_ZQ_injective in H1. subst. reflexivity.
Qed.

Theorem phi_ZQ_preserves_interact : M_ZQ.preserves_interact phi_ZQ.
Proof.
  intros [e1 t1] [e2 t2]. unfold phi_ZQ. simpl.
  unfold ZT.interact, QT.interact.
  destruct (ZT.entity_eq_dec (e1, t1) (e2, t2)) as [HeqZ | HneZ].
  - inversion HeqZ. subst.
    destruct (QT.entity_eq_dec (expr_ZQ e2, t2) (expr_ZQ e2, t2)) as [_ | Hne];
      [reflexivity | exfalso; apply Hne; reflexivity].
  - destruct (QT.entity_eq_dec (expr_ZQ e1, t1) (expr_ZQ e2, t2)) as [HeqQ | _].
    + exfalso. apply HneZ. inversion HeqQ.
      apply expr_ZQ_injective in H0. subst. reflexivity.
    + simpl. reflexivity.
Qed.


(* =========================================== *)
(*  phi_QC : QT → CR                            *)
(*                                              *)
(*  Map a Ring-Expr over ℚ to a CauchyTerm by   *)
(*  structural recursion: EConst q ↦ CTConst q, *)
(*  EAdd → CTSum, EMul → CTMul, ENeg → CTNeg.   *)
(*  Wrap in REnt with the observer time.        *)
(* =========================================== *)

Fixpoint expr_QC (e : QT.Expr) : CR.CauchyTerm :=
  match e with
  | QT.EConst q => CR.CTConst (this q)
  | QT.EAdd a b => CR.CTSum (expr_QC a) (expr_QC b)
  | QT.EMul a b => CR.CTMul (expr_QC a) (expr_QC b)
  | QT.ENeg a   => CR.CTNeg (expr_QC a)
  end.

Definition phi_QC (x : QT.Entity) : CR.Entity :=
  CR.REnt (expr_QC (fst x)) (snd x).

Lemma expr_QC_injective : forall e1 e2, expr_QC e1 = expr_QC e2 -> e1 = e2.
Proof.
  induction e1; intros e2 H; destruct e2;
    try (simpl in H; inversion H; fail); simpl in H.
  - inversion H. reflexivity.
  - inversion H. apply IHe1_1 in H1. apply IHe1_2 in H2. subst. reflexivity.
  - inversion H. apply IHe1_1 in H1. apply IHe1_2 in H2. subst. reflexivity.
  - inversion H. apply IHe1 in H1. subst. reflexivity.
Qed.

Theorem phi_QC_injective : M_QC.injective phi_QC.
Proof.
  intros [e1 t1] [e2 t2] H. unfold phi_QC in H. simpl in H.
  inversion H. apply expr_QC_injective in H1. subst. reflexivity.
Qed.

Theorem phi_QC_preserves_interact : M_QC.preserves_interact phi_QC.
Proof.
  intros [e1 t1] [e2 t2]. unfold phi_QC. simpl.
  unfold QT.interact, CR.interact.
  destruct (QT.entity_eq_dec (e1, t1) (e2, t2)) as [HeqQ | HneQ].
  - inversion HeqQ. subst.
    destruct (CR.entity_eq_dec (CR.REnt (expr_QC e2) t2) (CR.REnt (expr_QC e2) t2))
      as [_ | Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
  - destruct (CR.entity_eq_dec (CR.REnt (expr_QC e1) t1) (CR.REnt (expr_QC e2) t2))
      as [HeqC | _].
    + exfalso. apply HneQ. inversion HeqC.
      apply expr_QC_injective in H0. subst. reflexivity.
    + simpl. reflexivity.
Qed.


(* =========================================== *)
(*  COMPOSED MORPHISM phi_ND : NT → DR          *)
(* =========================================== *)

Definition phi_ND (x : NT.Entity) : DR.Entity :=
  CauchyDedekind.psi (phi_QC (phi_ZQ (phi_NZ x))).

Theorem phi_ND_preserves_interact : M_ND.preserves_interact phi_ND.
Proof.
  intros a b. unfold phi_ND.
  rewrite phi_NZ_preserves_interact.
  rewrite phi_ZQ_preserves_interact.
  rewrite phi_QC_preserves_interact.
  rewrite CauchyDedekind.psi_preserves_interact. reflexivity.
Qed.


(* =========================================== *)
(*  EXPRESSIVENESS — 3 + 5 at every layer      *)
(*                                              *)
(*  The sum 3 + 5 can be written as an Expr at *)
(*  each level. reduce_one contracts it to 8.  *)
(* =========================================== *)

Definition three_plus_five_N : NT.Entity :=
  (NT.EAdd (NT.EConst 3%nat) (NT.EConst 5%nat), 0%nat).

Definition eight_N : NT.Entity := (NT.EConst 8%nat, 0%nat).

Example reduce_at_N :
  NT.reduce_one (NT.EAdd (NT.EConst 3%nat) (NT.EConst 5%nat))
  = NT.EConst 8%nat.
Proof. reflexivity. Qed.

Definition three_plus_five_Z : ZT.Entity := phi_NZ three_plus_five_N.

Example three_plus_five_Z_form :
  three_plus_five_Z
  = (ZT.EAdd (ZT.EConst 3%Z) (ZT.EConst 5%Z), 0%nat).
Proof. reflexivity. Qed.

Example reduce_at_Z :
  ZT.reduce_one (ZT.EAdd (ZT.EConst 3%Z) (ZT.EConst 5%Z))
  = ZT.EConst 8%Z.
Proof. reflexivity. Qed.

Definition three_plus_five_Q : QT.Entity := phi_ZQ three_plus_five_Z.

Example three_plus_five_Q_form :
  three_plus_five_Q
  = (QT.EAdd (QT.EConst (3 # 1)) (QT.EConst (5 # 1)), 0%nat).
Proof. reflexivity. Qed.

Example reduce_at_Q :
  QT.reduce_one (QT.EAdd (QT.EConst (3 # 1)) (QT.EConst (5 # 1)))
  = QT.EConst ((3 # 1) + (5 # 1))%Q.
Proof. reflexivity. Qed.

Definition three_plus_five_C : CR.Entity := phi_QC three_plus_five_Q.

Example three_plus_five_C_form :
  three_plus_five_C
  = CR.REnt (CR.CTSum (CR.CTConst (3 # 1)) (CR.CTConst (5 # 1))) 0.
Proof. reflexivity. Qed.

Definition three_plus_five_D : DR.Entity := CauchyDedekind.psi three_plus_five_C.


(* =========================================== *)
(*  INTERACTION PROPAGATES                      *)
(*                                              *)
(*  Two naturals interacting at N correspond   *)
(*  to their Dedekind images interacting.      *)
(* =========================================== *)

Theorem N_interaction_propagates_to_Dedekind :
  forall a b : NT.Entity,
    phi_ND (NT.interact a b) = DR.interact (phi_ND a) (phi_ND b).
Proof. apply phi_ND_preserves_interact. Qed.


(* =========================================== *)
(*  FULL MORPHISM SUITE                         *)
(*                                              *)
(*  Each intermediate morphism is injective,   *)
(*  faithful, and strict preserves_interact.    *)
(*  The chain composes cleanly end-to-end.     *)
(* =========================================== *)

Theorem phi_NZ_faithful : M_NZ.faithful phi_NZ.
Proof. apply M_NZ.preserves_interact_is_faithful. apply phi_NZ_preserves_interact. Qed.

Theorem phi_ZQ_faithful : M_ZQ.faithful phi_ZQ.
Proof. apply M_ZQ.preserves_interact_is_faithful. apply phi_ZQ_preserves_interact. Qed.

Theorem phi_QC_faithful : M_QC.faithful phi_QC.
Proof. apply M_QC.preserves_interact_is_faithful. apply phi_QC_preserves_interact. Qed.
