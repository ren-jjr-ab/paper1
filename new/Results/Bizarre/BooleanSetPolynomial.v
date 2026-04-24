(* ============================================== *)
(*  BooleanSetPolynomial                            *)
(*                                                  *)
(*  The compositional explosion from functor       *)
(*  nesting. Taking                                 *)
(*                                                  *)
(*    PolynomialRing ∘ FinSetRing(8) ∘ FinSetRing(3)*)
(*                                                  *)
(*  we obtain a Carrier that literally holds        *)
(*                                                  *)
(*    {{0,1},{2}} + {{0},{1,2}} · x²                *)
(*                                                  *)
(*  — a polynomial whose coefficients are sets of   *)
(*  subsets of {0,1,2}. Every operation and axiom   *)
(*  comes from functor composition; no new          *)
(*  construction is needed.                         *)
(*                                                  *)
(*  ENCODING                                        *)
(*                                                  *)
(*  The 8 subsets of {0,1,2} are indexed as the     *)
(*  universe of FinSet8 via characteristic vectors: *)
(*                                                  *)
(*    index 0  →  ∅       = [F;F;F]                 *)
(*    index 1  →  {0}     = [T;F;F]                 *)
(*    index 2  →  {1}     = [F;T;F]                 *)
(*    index 3  →  {0,1}   = [T;T;F]                 *)
(*    index 4  →  {2}     = [F;F;T]                 *)
(*    index 5  →  {0,2}   = [T;F;T]                 *)
(*    index 6  →  {1,2}   = [F;T;T]                 *)
(*    index 7  →  {0,1,2} = [T;T;T]                 *)
(*                                                  *)
(*  Under this encoding:                            *)
(*                                                  *)
(*    {{0,1},{2}} = set containing indices 3 and 4  *)
(*               → [F;F;F;T;T;F;F;F]  in FinSet8    *)
(*                                                  *)
(*    {{0},{1,2}} = set containing indices 1 and 6  *)
(*               → [F;T;F;F;F;F;T;F]  in FinSet8    *)
(*                                                  *)
(*  The polynomial                                  *)
(*                                                  *)
(*    {{0,1},{2}} + {{0},{1,2}} · x²                *)
(*                                                  *)
(*  becomes the canonicalization of                 *)
(*                                                  *)
(*    [ set_outer_A ; 0 ; set_outer_B ]             *)
(*                                                  *)
(*  where 0 is FinSet8.zero (x¹ coefficient).       *)
(* ============================================== *)

Require Ring.
Require FinSetRing.
Require PolynomialRing.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.


(* =========================================== *)
(*  LEVEL 2 — FinSet8 (universe of 8)           *)
(*                                              *)
(*  The 8-element universe represents the 8     *)
(*  subsets of {0,1,2}. A subset of this        *)
(*  universe is a *set of subsets* of {0,1,2}.  *)
(* =========================================== *)

Module FinSet8Size <: FinSetRing.UniverseSize.
  Definition n : nat := 8.
End FinSet8Size.

Module FinSet8 := FinSetRing.FinSetRing FinSet8Size.


(* =========================================== *)
(*  LEVEL 3 — Polynomials with SetOfSets coeffs *)
(* =========================================== *)

Module FinSet8Poly := PolynomialRing.PolynomialRing FinSet8.


(* =========================================== *)
(*  THE INNER SUBSETS OF {0,1,2} (FinSet3)      *)
(*                                              *)
(*  Shown here for reference; the polynomial    *)
(*  itself lives in FinSet8Poly and indexes     *)
(*  these via characteristic vectors.           *)
(* =========================================== *)

Definition inner_01  : FinSetRing.FinSet3.Carrier.
Proof. exists [true; true; false]. reflexivity. Defined.

Definition inner_2   : FinSetRing.FinSet3.Carrier.
Proof. exists [false; false; true]. reflexivity. Defined.

Definition inner_0   : FinSetRing.FinSet3.Carrier.
Proof. exists [true; false; false]. reflexivity. Defined.

Definition inner_12  : FinSetRing.FinSet3.Carrier.
Proof. exists [false; true; true]. reflexivity. Defined.


(* =========================================== *)
(*  THE OUTER SETS (elements of FinSet8)        *)
(*                                              *)
(*  set_01_2  = {{0,1}, {2}}    — indices 3, 4  *)
(*  set_0_12  = {{0}, {1,2}}    — indices 1, 6  *)
(* =========================================== *)

Definition set_01_2 : FinSet8.Carrier.
Proof.
  exists [false; false; false; true; true; false; false; false].
  reflexivity.
Defined.

Definition set_0_12 : FinSet8.Carrier.
Proof.
  exists [false; true; false; false; false; false; true; false].
  reflexivity.
Defined.


(* =========================================== *)
(*  THE POLYNOMIAL                              *)
(*                                              *)
(*    {{0,1},{2}} + {{0},{1,2}} · x²            *)
(*                                              *)
(*  Constructed as a canonicalized list of      *)
(*  FinSet8 coefficients. The x¹ slot is zero.  *)
(* =========================================== *)

Definition the_polynomial : FinSet8Poly.Carrier :=
  FinSet8Poly.canonicalize [set_01_2; FinSet8.zero; set_0_12].


(* =========================================== *)
(*  RING AXIOMS AT THIS LEVEL                   *)
(*                                              *)
(*  Inherited from PolynomialRing applied to    *)
(*  FinSet8 (itself obtained from FinSetRing).  *)
(*  No new proof effort.                        *)
(* =========================================== *)

Check FinSet8Poly.add_assoc.
Check FinSet8Poly.add_comm.
Check FinSet8Poly.mul_assoc.
Check FinSet8Poly.mul_comm.
Check FinSet8Poly.distrib_l.
Check FinSet8Poly.distrib_r.
Check FinSet8Poly.add_neg_l.
Check FinSet8Poly.mul_one_l.
Check FinSet8Poly.mul_one_r.


(* =========================================== *)
(*  DECIDABLE EQUALITY                          *)
(* =========================================== *)

Check FinSet8Poly.carrier_eq_dec.


(* =========================================== *)
(*  CONCRETE WITNESSES                          *)
(* =========================================== *)

(* The polynomial is closed under ring operations. *)

Example the_polynomial_plus_zero :
  FinSet8Poly.add the_polynomial FinSet8Poly.zero = the_polynomial.
Proof.
  rewrite FinSet8Poly.add_comm. apply FinSet8Poly.add_zero_l.
Qed.

Example the_polynomial_times_one :
  FinSet8Poly.mul the_polynomial FinSet8Poly.one = the_polynomial.
Proof.
  rewrite FinSet8Poly.mul_comm. apply FinSet8Poly.mul_one_l.
Qed.


(* =========================================== *)
(*  BOOLEAN CHARACTER SURVIVES COMPOSITION     *)
(*                                              *)
(*  In FinSet8 every element satisfies a+a = 0. *)
(*  We lift this to polynomials: for every      *)
(*  polynomial p over a Boolean coefficient     *)
(*  ring, p + p = 0. The proof goes through     *)
(*  raw_add and normalization.                  *)
(* =========================================== *)

Lemma finset8_add_self :
  forall a : FinSet8.Carrier, FinSet8.add a a = FinSet8.zero.
Proof. intros. apply FinSet8.add_neg_l. Qed.

Lemma xor_self_all_false :
  forall l : list bool,
    FinSet8.xor_list l l = FinSet8.repeat_bool false (length l).
Proof. exact FinSet8.xor_list_self. Qed.


(* raw_add on equal-length all-false-producing coefficients: the     *)
(* polynomial raw_add of p with itself gives a list of FinSet8.zero. *)

Lemma raw_add_self_all_zero :
  forall p : list FinSet8.Carrier,
    FinSet8Poly.raw_add p p =
    map (fun _ => FinSet8.zero) p.
Proof.
  induction p as [| a p' IH]; simpl.
  - reflexivity.
  - rewrite IH. f_equal. apply finset8_add_self.
Qed.


(* raw_normalize of an all-FinSet8.zero list is []. *)

Lemma raw_normalize_all_zero :
  forall p : list FinSet8.Carrier,
    FinSet8Poly.raw_normalize (map (fun _ => FinSet8.zero) p) = [].
Proof.
  induction p as [| a p' IH].
  - reflexivity.
  - change (map (fun _ : FinSet8.Carrier => FinSet8.zero) (a :: p'))
      with (FinSet8.zero :: map (fun _ : FinSet8.Carrier => FinSet8.zero) p').
    rewrite FinSet8Poly.raw_normalize_cons. rewrite IH.
    destruct (FinSet8.carrier_eq_dec FinSet8.zero FinSet8.zero) as [_ | Hne].
    + reflexivity.
    + contradiction Hne. reflexivity.
Qed.


Theorem finset8poly_add_self :
  forall p : FinSet8Poly.Carrier, FinSet8Poly.add p p = FinSet8Poly.zero.
Proof.
  intros p. apply FinSet8Poly.sig_eq_by_value.
  unfold FinSet8Poly.add.
  rewrite FinSet8Poly.canonicalize_proj.
  rewrite raw_add_self_all_zero.
  rewrite raw_normalize_all_zero.
  reflexivity.
Qed.


(* The signature polynomial inherits the Boolean property. *)

Example the_polynomial_add_self :
  FinSet8Poly.add the_polynomial the_polynomial = FinSet8Poly.zero.
Proof. apply finset8poly_add_self. Qed.


(* =========================================== *)
(*  A GLIMPSE OF THE CARRIER'S SHAPE            *)
(*                                              *)
(*  The raw list of coefficients is exactly     *)
(*  what we wrote: [set_01_2; 0; set_0_12].     *)
(*  Since set_0_12 is nonzero, canonicalization *)
(*  leaves the list unchanged.                  *)
(* =========================================== *)

Example the_polynomial_raw_form :
  proj1_sig the_polynomial = [set_01_2; FinSet8.zero; set_0_12].
Proof.
  unfold the_polynomial.
  rewrite FinSet8Poly.canonicalize_proj.
  simpl.
  destruct (FinSet8.carrier_eq_dec set_0_12 FinSet8.zero) as [Heq | Hne].
  - (* contradiction: set_0_12 ≠ FinSet8.zero *)
    exfalso.
    assert (Hproj : proj1_sig set_0_12 = proj1_sig (FinSet8.zero : FinSet8.Carrier))
      by (rewrite Heq; reflexivity).
    simpl in Hproj. discriminate Hproj.
  - reflexivity.
Qed.


(* =========================================== *)
(*  XOR WITNESS AT THE SET-OF-SETS LEVEL        *)
(*                                              *)
(*  Because "+" in a Boolean ring is symmetric  *)
(*  difference, not union:                      *)
(*                                              *)
(*    {{0,1},{2}} + {{0},{1,2}}                 *)
(*      = {{0},{0,1},{2},{1,2}}                 *)
(*                                              *)
(*  (disjoint inputs; XOR and ∪ happen to       *)
(*  agree here.)                                *)
(*                                              *)
(*    {{0,1},{2}} + {{0,1}}                     *)
(*      = {{2}}                                 *)
(*                                              *)
(*  (overlapping inputs; the shared element     *)
(*  cancels. XOR ≠ ∪.)                          *)
(* =========================================== *)

(* The XOR of our two outer sets: positions 1, 3, 4, 6 become true. *)

Definition set_01_0_2_12 : FinSet8.Carrier.
Proof.
  exists [false; true; false; true; true; false; true; false].
  reflexivity.
Defined.

Example set_xor_literal :
  FinSet8.add set_01_2 set_0_12 = set_01_0_2_12.
Proof. apply FinSet8.sig_eq_by_value. reflexivity. Qed.


(* The "shared element cancels" witness. *)

Definition just_01 : FinSet8.Carrier.
Proof.
  exists [false; false; false; true; false; false; false; false].
  reflexivity.
Defined.

Definition just_2 : FinSet8.Carrier.
Proof.
  exists [false; false; false; false; true; false; false; false].
  reflexivity.
Defined.

Example xor_cancels_shared :
  FinSet8.add set_01_2 just_01 = just_2.
Proof. apply FinSet8.sig_eq_by_value. reflexivity. Qed.
