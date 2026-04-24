(* ========================================== *)
(*  TrichotomyTest                            *)
(*                                            *)
(*  Apply the Trichotomy.Make functor to      *)
(*  every active instance and re-expose the   *)
(*  paper-trichotomy theorem in concrete      *)
(*  per-instance form.                        *)
(* ========================================== *)

Require Import Existence.
Require Import Trichotomy.

Require Import YouAndMe.
Require Import ConsistencyModelPD.
Require Import LatticeModel.
Require Import HashModel.
Require Import EpsilonDelta.

Module Tri_YouAndMe := Trichotomy.Make YouAndMeSig.
Module Tri_PD       := Trichotomy.Make ConsistencyModelPDSig.
Module Tri_Lattice  := Trichotomy.Make LatticeComputable.
Module Tri_Hash     := Trichotomy.Make HashComputable.
Module Tri_ED       := Trichotomy.Make EpsilonDeltaComputable.

(* ================================================ *)
(*  PAPER-LEVEL TRICHOTOMY                          *)
(*                                                  *)
(*  The three paper relations ≡, =, ≈ are pairwise  *)
(*  disjoint on every instance. EpsilonDelta is the *)
(*  only instance where collapse carries real  *)
(*  content (EDNormal ↔ EDLimit via                 *)
(*  classical_converges); the others set            *)
(*  collapse := False, so their convention     *)
(*  cases are vacuous while pairwise disjointness   *)
(*  still holds.                                    *)
(* ================================================ *)

Theorem paper_trichotomy_YouAndMe :
  forall a b : YouAndMeSig.Entity,
    (~ (Tri_YouAndMe.paper_equiv a b /\
        Tri_YouAndMe.paper_projection a b)) /\
    (~ (Tri_YouAndMe.paper_equiv a b /\
        Tri_YouAndMe.paper_convention a b)) /\
    (~ (Tri_YouAndMe.paper_projection a b /\
        Tri_YouAndMe.paper_convention a b)).
Proof. exact Tri_YouAndMe.paper_trichotomy_pairwise_disjoint. Qed.

Theorem paper_trichotomy_PD :
  forall a b : ConsistencyModelPDSig.Entity,
    (~ (Tri_PD.paper_equiv a b /\ Tri_PD.paper_projection a b)) /\
    (~ (Tri_PD.paper_equiv a b /\ Tri_PD.paper_convention a b)) /\
    (~ (Tri_PD.paper_projection a b /\ Tri_PD.paper_convention a b)).
Proof. exact Tri_PD.paper_trichotomy_pairwise_disjoint. Qed.

Theorem paper_trichotomy_Lattice :
  forall a b : LatticeComputable.Entity,
    (~ (Tri_Lattice.paper_equiv a b /\
        Tri_Lattice.paper_projection a b)) /\
    (~ (Tri_Lattice.paper_equiv a b /\
        Tri_Lattice.paper_convention a b)) /\
    (~ (Tri_Lattice.paper_projection a b /\
        Tri_Lattice.paper_convention a b)).
Proof. exact Tri_Lattice.paper_trichotomy_pairwise_disjoint. Qed.

Theorem paper_trichotomy_Hash :
  forall a b : HashComputable.Entity,
    (~ (Tri_Hash.paper_equiv a b /\ Tri_Hash.paper_projection a b)) /\
    (~ (Tri_Hash.paper_equiv a b /\ Tri_Hash.paper_convention a b)) /\
    (~ (Tri_Hash.paper_projection a b /\ Tri_Hash.paper_convention a b)).
Proof. exact Tri_Hash.paper_trichotomy_pairwise_disjoint. Qed.

Theorem paper_trichotomy_ED :
  forall a b : EpsilonDeltaComputable.Entity,
    (~ (Tri_ED.paper_equiv a b /\ Tri_ED.paper_projection a b)) /\
    (~ (Tri_ED.paper_equiv a b /\ Tri_ED.paper_convention a b)) /\
    (~ (Tri_ED.paper_projection a b /\ Tri_ED.paper_convention a b)).
Proof. exact Tri_ED.paper_trichotomy_pairwise_disjoint. Qed.
