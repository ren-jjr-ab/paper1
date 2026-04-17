(* ============================================================ *)
(*  AssumptionsAudit.v                                          *)
(*                                                              *)
(*  Dynamic soundness audit via Print Assumptions on key        *)
(*  theorems from the paper. Tests whether all theorems         *)
(*  remain free from unexpected external postulates beyond      *)
(*  the declared framework axioms.                              *)
(*                                                              *)
(*  This file is NOT in _CoqProject and is compiled standalone *)
(*  with explicit -Q flags for each library.                    *)
(* ============================================================ *)

(* ============================================================ *)
(*  FRAMEWORK-LEVEL THEOREMS (via instances)                    *)
(* ============================================================ *)

Require RationalRep.
Require CauchyReal.

(* Framework instances: RationalRep and CauchyReal are
   instantiations of the framework axiom signatures. *)

(* RationalRep.RationalRep.interact_self — one of the five
   framework axioms for RationalRep instance. *)

Print Assumptions RationalRep.RationalRep.interact_self.

(* RationalRep.RationalRep.convention_not_derivable — another
   framework axiom for RationalRep instance. *)

Print Assumptions RationalRep.RationalRep.convention_not_derivable.

(* CauchyReal.CauchyReal.cauchy_pointwise_distinct_convention —
   framework axiom instantiation for CauchyReal. *)

Print Assumptions CauchyReal.CauchyReal.cauchy_pointwise_distinct_convention.


(* ============================================================ *)
(*  RESULTS-LEVEL THEOREMS                                      *)
(* ============================================================ *)

Require RationalRepTest.
Require CauchyRealTest.
Require CauchyLimits.
Require RationalToCauchyMorphism.
Require RationalCauchyFactorization.

(* RationalRepTest.halves_1_2_and_2_4_paper_projection —
   concrete rational equivalence in RationalRep instance. *)

Print Assumptions RationalRepTest.halves_1_2_and_2_4_paper_projection.

(* CauchyRealTest.const_sum_convention_eq —
   structural equality in CauchyReal instance. *)

Print Assumptions CauchyRealTest.const_sum_convention_eq.

(* CauchyLimits.invsucc_to_zero —
   limit of 1/(n+1) to 0. *)

Print Assumptions CauchyLimits.invsucc_to_zero.

(* CauchyLimits.invsucc_squared_convention_eq_zero —
   limit of -1/(n+1) to 0. *)

Print Assumptions CauchyLimits.invsucc_squared_convention_eq_zero.

(* CauchyLimits.binom_square_pointwise —
   limit of (n+1)/n to 1. *)

Print Assumptions CauchyLimits.binom_square_pointwise.

(* RationalToCauchyMorphism.phi_preserves_interact —
   cross-system morphism preserves interact. *)

Print Assumptions RationalToCauchyMorphism.phi_preserves_interact.

(* RationalToCauchyMorphism.phi_injective —
   morphism is injective. *)

Print Assumptions RationalToCauchyMorphism.phi_injective.

(* RationalToCauchyMorphism.phi_cannot_witness_convention —
   CauchyReal's convention layer is new information. *)

Print Assumptions RationalToCauchyMorphism.phi_cannot_witness_convention.

(* RationalCauchyFactorization.phi_factors_via_pullback_pushout —
   categorical factorization through framework constructions.
   NOTE: This theorem uses pushout, which invokes quotient_exists. *)

Print Assumptions RationalCauchyFactorization.phi_factors_via_pullback_pushout.
