(* ============================================== *)
(*  RationalCauchyPullback                          *)
(*                                                  *)
(*  Pullback of phi : RR → CR against id : CR → CR *)
(*  over Base = CR.                                 *)
(*                                                  *)
(*     RR --- phi ----> CR                          *)
(*                      |                           *)
(*                      id                          *)
(*                      v                           *)
(*                      CR                          *)
(*                                                  *)
(*  Pullback = { (r, c) ∈ RR × CR : phi r = c }.   *)
(*                                                  *)
(*  This is exactly the GRAPH of phi inside the    *)
(*  product — the subsystem of joint states where  *)
(*  rational representation and Cauchy sequence    *)
(*  agree under the embedding.                      *)
(*                                                  *)
(*  Framework's interact_preserves_pullback:       *)
(*  coordinate-wise dynamics keep the meeting       *)
(*  condition. Verified concretely.                 *)
(*                                                  *)
(*  Pullback membership IFF Cauchy shape is a      *)
(*  CTConst (or CEval 0 from CMark). CauchyReal-   *)
(*  specific shapes (CTSum, CTInvSucc, CTScale,    *)
(*  CTNeg) fall outside.                            *)
(* ============================================== *)

Require Existence.
Require ExistenceMorphism.
Require ExistenceProduct.
Require ExistencePullback.
Require RationalRep.
Require CauchyReal.
Require RationalRepTest.
Require CauchyRealTest.
Require RationalToCauchyMorphism.
Require RationalCauchyProduct.
From Stdlib Require Import QArith.


(* =========================================== *)
(*  ALIASES                                    *)
(* =========================================== *)

Module RR := RationalRep.RationalRep.
Module CR := CauchyReal.CauchyReal.


(* =========================================== *)
(*  MORPHISM WRAPPERS                          *)
(*                                             *)
(*  Pullback functor expects MorphismInto      *)
(*  modules. Wrap phi (RR → CR) and the        *)
(*  identity on CR.                            *)
(* =========================================== *)

Module PhiInto <: ExistencePullback.MorphismInto RR CR.
  Definition phi : RR.Entity -> CR.Entity :=
    RationalToCauchyMorphism.phi.
  Theorem preserves_interact :
    forall a b : RR.Entity,
      phi (RR.interact a b) = CR.interact (phi a) (phi b).
  Proof. exact RationalToCauchyMorphism.phi_preserves_interact. Qed.
End PhiInto.

Module IdCR := ExistencePullback.IdentityInto CR.


(* =========================================== *)
(*  PULLBACK FUNCTOR APPLICATION               *)
(* =========================================== *)

Module Pull :=
  ExistencePullback.Pullback RR CR CR PhiInto IdCR.

(* Pull.on_pullback (r, c) :=
     PhiInto.phi r = IdCR.phi c
   i.e., phi r = c.                            *)


(* =========================================== *)
(*  MEMBERSHIP EXAMPLES                        *)
(* =========================================== *)

Example halves_pair_on_pullback :
  Pull.on_pullback (RationalRepTest.half_1_2,
                    CR.REnt (CR.CTConst (1#2)) 0).
Proof. reflexivity. Qed.

Example cmark_and_ceval_on_pullback :
  Pull.on_pullback (RR.CMark 0, CR.CEval 0 0).
Proof. reflexivity. Qed.


(* =========================================== *)
(*  NON-MEMBERSHIP — CauchyReal-specific       *)
(*  shapes outside phi's image                 *)
(*                                             *)
(*  one_plus_invsucc = CTSum (CTConst 1)       *)
(*    CTInvSucc — CTSum shape, never phi's     *)
(*  output.                                    *)
(* =========================================== *)

Example sum_shape_not_on_pullback :
  forall (r : RR.Entity),
    ~ Pull.on_pullback (r, CR.REnt CauchyRealTest.one_plus_invsucc 0).
Proof.
  intros r Hmem.
  unfold Pull.on_pullback in Hmem. simpl in Hmem.
  destruct r as [q t | t]; simpl in Hmem; inversion Hmem.
Qed.


(* =========================================== *)
(*  CONCRETE INTERACT PRESERVATION             *)
(*                                             *)
(*  Two pullback members interact to a         *)
(*  pullback member — framework theorem, but   *)
(*  here we also verify by Compute.            *)
(* =========================================== *)

Compute Pull.P.interact
  (RationalRepTest.half_1_2, CR.REnt (CR.CTConst (1#2)) 0)
  (RR.CMark 0, CR.CEval 0 0).
(* = (RR.REnt (1#2) 1, CR.REnt (CR.CTConst (1#2)) 1)
     — still in pullback, phi-image holds *)

Example interact_result_on_pullback :
  Pull.on_pullback (Pull.P.interact
    (RationalRepTest.half_1_2, CR.REnt (CR.CTConst (1#2)) 0)
    (RR.CMark 0, CR.CEval 0 0)).
Proof. reflexivity. Qed.

Theorem interact_preserves_pullback_halves :
  Pull.on_pullback (RationalRepTest.half_1_2,
                    CR.REnt (CR.CTConst (1#2)) 0) ->
  Pull.on_pullback (RR.CMark 0, CR.CEval 0 0) ->
  Pull.on_pullback (Pull.P.interact
    (RationalRepTest.half_1_2, CR.REnt (CR.CTConst (1#2)) 0)
    (RR.CMark 0, CR.CEval 0 0)).
Proof.
  apply Pull.interact_preserves_pullback.
Qed.


(* =========================================== *)
(*  PULLBACK EQUALS THE phi GRAPH              *)
(*                                             *)
(*  Every pullback element has the form        *)
(*  (r, phi r).                                *)
(* =========================================== *)

Theorem pullback_is_phi_graph :
  forall p : Pull.P.Entity,
    Pull.on_pullback p ->
    snd p = RationalToCauchyMorphism.phi (fst p).
Proof.
  intros [r c] Hmem.
  unfold Pull.on_pullback in Hmem. simpl in Hmem.
  simpl. symmetry. exact Hmem.
Qed.


(* =========================================== *)
(*  DIAGONAL ⊂ PULLBACK                        *)
(*                                             *)
(*  Product's diag_phi r = (r, phi r) always   *)
(*  lands in the pullback. The product's       *)
(*  natural "diagonal" is exactly this slice.  *)
(* =========================================== *)

Theorem diag_phi_image_in_pullback :
  forall r : RR.Entity,
    Pull.on_pullback (RationalCauchyProduct.diag_phi r).
Proof.
  intro r. unfold Pull.on_pullback.
  unfold RationalCauchyProduct.diag_phi.
  unfold RationalCauchyProduct.UP.pair_morphism.
  simpl. reflexivity.
Qed.


(* =========================================== *)
(*  PULLBACK WITNESSES JOINT PAPER_PROJECTION  *)
(*                                             *)
(*  Halves (1/2, 2/4) in RR, embedded as phi   *)
(*  images in CR — their joint representative  *)
(*  pair lies in pullback, and the pullback's  *)
(*  structural closure guarantees any dynamic  *)
(*  stays on the graph.                        *)
(* =========================================== *)

Example halves_trip_stays_on_pullback :
  Pull.on_pullback (Pull.P.interact
    (RationalCauchyProduct.diag_phi RationalRepTest.half_1_2)
    (RationalCauchyProduct.diag_phi (RR.CMark 0))).
Proof. reflexivity. Qed.
