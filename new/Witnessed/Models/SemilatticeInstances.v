(* ============================================== *)
(*  SemilatticeInstances                            *)
(*                                                  *)
(*  Concrete LatticeTimed instances built from     *)
(*  idempotent binary operations.                  *)
(*                                                  *)
(*    NatMax    (nat, Nat.max)                     *)
(*    NatMin    (nat, Nat.min)                     *)
(*    BoolAnd   (bool, andb)                       *)
(*    BoolOr    (bool, orb)                        *)
(*                                                  *)
(*  Each instance supplies only the three           *)
(*  LatticeSpec obligations — op_idempotent,        *)
(*  eq_dec, exists_distinct — and receives a full   *)
(*  TimedExistenceSig (hence ExistenceSig)          *)
(*  instance from the LatticeTimed functor.         *)
(*                                                  *)
(*  Absorbing-element semi-lattices (NatMin's 0,    *)
(*  BoolAnd's false, BoolOr's true) fit the         *)
(*  framework naturally via the time coord of the   *)
(*  paired entity — the framework's interact_with   *)
(*  is satisfied through time movement even when    *)
(*  the lattice value is stuck at an absorbing      *)
(*  element.                                        *)
(* ============================================== *)

Require Import Existence.
Require Import Witnessed.
Require Import LatticeWitnessed.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.


(* ================================================ *)
(*  NATMAX                                           *)
(* ================================================ *)

Module NatMaxSpec <: LatticeSpec.
  Definition T : Type := nat.
  Definition op : T -> T -> T := Nat.max.
  Theorem op_idempotent : forall a : T, op a a = a.
  Proof. intros a. unfold op. apply Nat.max_id. Qed.
  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof. exact Nat.eq_dec. Qed.
  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists 0, 1. discriminate. Qed.
End NatMaxSpec.

Module NatMax := LatticeWitnessed.Make NatMaxSpec.


(* ================================================ *)
(*  NATMIN                                           *)
(*                                                   *)
(*  Bottom 0 is absorbing in the value coord; the    *)
(*  time coord rescues framework fit.                *)
(* ================================================ *)

Module NatMinSpec <: LatticeSpec.
  Definition T : Type := nat.
  Definition op : T -> T -> T := Nat.min.
  Theorem op_idempotent : forall a : T, op a a = a.
  Proof. intros a. unfold op. apply Nat.min_id. Qed.
  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof. exact Nat.eq_dec. Qed.
  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists 0, 1. discriminate. Qed.
End NatMinSpec.

Module NatMin := LatticeWitnessed.Make NatMinSpec.


(* ================================================ *)
(*  BOOLAND                                          *)
(*                                                   *)
(*  false is absorbing; time coord rescues.          *)
(* ================================================ *)

Module BoolAndSpec <: LatticeSpec.
  Definition T : Type := bool.
  Definition op : T -> T -> T := andb.
  Theorem op_idempotent : forall a : T, op a a = a.
  Proof. intros a. unfold op. destruct a; reflexivity. Qed.
  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof. exact bool_dec. Qed.
  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists true, false. discriminate. Qed.
End BoolAndSpec.

Module BoolAnd := LatticeWitnessed.Make BoolAndSpec.


(* ================================================ *)
(*  BOOLOR                                           *)
(*                                                   *)
(*  true is absorbing; time coord rescues.           *)
(* ================================================ *)

Module BoolOrSpec <: LatticeSpec.
  Definition T : Type := bool.
  Definition op : T -> T -> T := orb.
  Theorem op_idempotent : forall a : T, op a a = a.
  Proof. intros a. unfold op. destruct a; reflexivity. Qed.
  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof. exact bool_dec. Qed.
  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists true, false. discriminate. Qed.
End BoolOrSpec.

Module BoolOr := LatticeWitnessed.Make BoolOrSpec.


(* ================================================ *)
(*  COLORMERGE                                       *)
(*                                                   *)
(*  Pedagogical instance echoing Paper 1's "red      *)
(*  apple projected to fruit dimension". Four basic  *)
(*  colors plus an absorbing Mixed. Merging two      *)
(*  identical colors preserves them; merging any     *)
(*  two distinct colors collapses to Mixed.          *)
(*                                                   *)
(*  Once Mixed, stays Mixed at the value coord —     *)
(*  the time coord of LatticeWitnessed provides  *)
(*  the interact_with witness.                       *)
(* ================================================ *)

Inductive Color : Type := Red | Blue | Yellow | Mixed.

Definition color_eq_dec (a b : Color) : {a = b} + {a <> b}.
Proof.
  destruct a; destruct b;
    solve [ left; reflexivity | right; discriminate ].
Defined.

Definition color_merge (a b : Color) : Color :=
  match color_eq_dec a b with
  | left _  => a
  | right _ => Mixed
  end.

Module ColorMergeSpec <: LatticeSpec.
  Definition T : Type := Color.
  Definition op : T -> T -> T := color_merge.
  Theorem op_idempotent : forall a : T, op a a = a.
  Proof.
    intros a. unfold op, color_merge.
    destruct (color_eq_dec a a) as [H | H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
  Qed.
  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof. exact color_eq_dec. Qed.
  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists Red, Blue. discriminate. Qed.
End ColorMergeSpec.

Module ColorMerge := LatticeWitnessed.Make ColorMergeSpec.


(* ================================================ *)
(*  NATPAIRMAX                                       *)
(*                                                   *)
(*  Two-dimensional natural lattice under coord-     *)
(*  wise max. The entity space is ℕ × ℕ; the         *)
(*  resulting join-semilattice illustrates how       *)
(*  framework structure scales to higher-            *)
(*  dimensional value coords.                        *)
(* ================================================ *)

Module NatPairMaxSpec <: LatticeSpec.
  Definition T : Type := (nat * nat)%type.
  Definition op (a b : T) : T :=
    (Nat.max (fst a) (fst b), Nat.max (snd a) (snd b)).
  Theorem op_idempotent : forall a : T, op a a = a.
  Proof.
    intros [x y]. unfold op. simpl.
    rewrite Nat.max_id. rewrite Nat.max_id. reflexivity.
  Qed.
  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof.
    intros [x1 y1] [x2 y2].
    destruct (Nat.eq_dec x1 x2) as [Hx | Hx].
    - destruct (Nat.eq_dec y1 y2) as [Hy | Hy].
      + left. subst. reflexivity.
      + right. intros H. injection H as _ Hy'. exact (Hy Hy').
    - right. intros H. injection H as Hx' _. exact (Hx Hx').
  Defined.
  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists (0, 0), (1, 0). discriminate. Qed.
End NatPairMaxSpec.

Module NatPairMax := LatticeWitnessed.Make NatPairMaxSpec.


(* ================================================ *)
(*  OPTIONNATMAX                                     *)
(*                                                   *)
(*  option nat with None as bottom and max on        *)
(*  Some's. Mixes the framework's semilattice        *)
(*  pattern with a nullable coord — useful when      *)
(*  an entity may not yet be committed to a value.   *)
(* ================================================ *)

Module OptionNatMaxSpec <: LatticeSpec.
  Definition T : Type := option nat.

  Definition op (a b : T) : T :=
    match a, b with
    | None, x => x
    | x, None => x
    | Some x, Some y => Some (Nat.max x y)
    end.

  Theorem op_idempotent : forall a : T, op a a = a.
  Proof.
    intros [x|].
    - simpl. rewrite Nat.max_id. reflexivity.
    - simpl. reflexivity.
  Qed.

  Theorem eq_dec : forall a b : T, {a = b} + {a <> b}.
  Proof.
    intros [x|] [y|].
    - destruct (Nat.eq_dec x y) as [H | H].
      + left. subst. reflexivity.
      + right. intros Heq. injection Heq as H'. exact (H H').
    - right. discriminate.
    - right. discriminate.
    - left. reflexivity.
  Defined.

  Theorem exists_distinct : exists a b : T, a <> b.
  Proof. exists None, (Some 0). discriminate. Qed.
End OptionNatMaxSpec.

Module OptionNatMax := LatticeWitnessed.Make OptionNatMaxSpec.
