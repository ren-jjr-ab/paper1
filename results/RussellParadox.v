(* ============================================== *)
(*  RussellParadox                                  *)
(*                                                  *)
(*  Russell's paradox as a framework theorem.       *)
(*  Any Type T equipped with                        *)
(*                                                  *)
(*    mem  : T → T → Prop                           *)
(*    comp : (T → Prop) → T                         *)
(*                                                  *)
(*  satisfying the unrestricted comprehension       *)
(*  axiom                                           *)
(*                                                  *)
(*    ∀ P x. mem x (comp P) ↔ P x                   *)
(*                                                  *)
(*  is inconsistent. The diagonal witness is        *)
(*                                                  *)
(*    R := comp (fun x => ¬ mem x x)                *)
(*                                                  *)
(*  yielding mem R R ↔ ¬ mem R R — the P ↔ ¬P       *)
(*  contradiction shared with Cantor.               *)
(*                                                  *)
(*  Framework position — §1-C (absence as design).  *)
(*                                                  *)
(*  In SymbolicSet the grammar supplies no          *)
(*  SComp : (SetExpr → Prop) → SetExpr constructor. *)
(*  That absence is not a convenience gap: Russell  *)
(*  shows the grammar cannot admit such a           *)
(*  constructor with unrestricted semantics without *)
(*  collapsing to False.                            *)
(*                                                  *)
(*  SymbolicSet further protects itself by typing:  *)
(*  member_bool : E.Elem → SetExpr → bool has       *)
(*  asymmetric source and target, so x ∈ x is       *)
(*  ill-typed at x : SetExpr. Even with a           *)
(*  hypothetical comprehension operator one would   *)
(*  first need to identify E.Elem with SetExpr —    *)
(*  another layer the grammar deliberately          *)
(*  withholds.                                      *)
(* ============================================== *)

Require CantorTheorem.
Require SymbolicSet.
Require ElemSig.


(* =========================================== *)
(*  RUSSELL — DIAGONAL WITNESS                  *)
(*                                              *)
(*  Exposes the explicit set R such that        *)
(*  mem R R ↔ ¬ mem R R. This is the            *)
(*  constructive kernel of the paradox.         *)
(* =========================================== *)

Theorem russell_diagonal :
  forall (T : Type)
         (mem : T -> T -> Prop)
         (comp : (T -> Prop) -> T),
    (forall (P : T -> Prop) (x : T), mem x (comp P) <-> P x) ->
    exists R : T, mem R R <-> ~ mem R R.
Proof.
  intros T mem comp Hcomp.
  exists (comp (fun x => ~ mem x x)).
  apply Hcomp.
Qed.


(* =========================================== *)
(*  RUSSELL — INCONSISTENCY                     *)
(*                                              *)
(*  The diagonal gives P ↔ ¬P, which is         *)
(*  intuitionistically False. Reuses            *)
(*  CantorTheorem.P_iff_not_P_False.            *)
(* =========================================== *)

Theorem russell :
  forall (T : Type)
         (mem : T -> T -> Prop)
         (comp : (T -> Prop) -> T),
    (forall (P : T -> Prop) (x : T), mem x (comp P) <-> P x) ->
    False.
Proof.
  intros T mem comp Hcomp.
  destruct (russell_diagonal T mem comp Hcomp) as [R HR].
  exact (CantorTheorem.P_iff_not_P_False _ HR).
Qed.


(* =========================================== *)
(*  REFORMULATION — NO SUCH OPERATOR EXISTS     *)
(*                                              *)
(*  For any fixed T and mem, no comprehension   *)
(*  function satisfying unrestricted membership *)
(*  can exist.                                  *)
(* =========================================== *)

Theorem no_unrestricted_comprehension :
  forall (T : Type) (mem : T -> T -> Prop),
    ~ (exists comp : (T -> Prop) -> T,
         forall (P : T -> Prop) (x : T), mem x (comp P) <-> P x).
Proof.
  intros T mem [comp Hcomp].
  exact (russell T mem comp Hcomp).
Qed.


(* =========================================== *)
(*  INSTANCE — SYMBOLICSET SETEXPR              *)
(*                                              *)
(*  Applied to SymbolicSet.Make(E).SetExpr for  *)
(*  any ElemSig. The lesson: were the grammar   *)
(*  extended with (hypothetical) self-contained *)
(*  mem and comp, SetExpr itself would become   *)
(*  inconsistent. The grammar's current shape   *)
(*  — elements and sets at distinct types,      *)
(*  no SComp constructor — is precisely what    *)
(*  blocks the derivation.                      *)
(* =========================================== *)

Module SymbolicSetRussell (E : ElemSig.ElemSig).
  Module SS := SymbolicSet.Make E.

  Theorem setexpr_rejects_unrestricted_comprehension :
    forall (mem : SS.SetExpr -> SS.SetExpr -> Prop),
      ~ (exists comp : (SS.SetExpr -> Prop) -> SS.SetExpr,
           forall (P : SS.SetExpr -> Prop) (x : SS.SetExpr),
             mem x (comp P) <-> P x).
  Proof.
    intros mem. apply no_unrestricted_comprehension.
  Qed.

  Theorem entity_rejects_unrestricted_comprehension :
    forall (mem : SS.Entity -> SS.Entity -> Prop),
      ~ (exists comp : (SS.Entity -> Prop) -> SS.Entity,
           forall (P : SS.Entity -> Prop) (x : SS.Entity),
             mem x (comp P) <-> P x).
  Proof.
    intros mem. apply no_unrestricted_comprehension.
  Qed.
End SymbolicSetRussell.


(* =========================================== *)
(*  CONCRETE INSTANCE — NAT CARRIER             *)
(* =========================================== *)

Module NatElem <: ElemSig.ElemSig.
  Definition Elem : Type := nat.
  Definition elem_eq_dec : forall x y : nat, {x = y} + {x <> y} := PeanoNat.Nat.eq_dec.
  Definition witness : nat := 0.
End NatElem.

Module NatSetRussell := SymbolicSetRussell NatElem.

Check NatSetRussell.setexpr_rejects_unrestricted_comprehension.
Check NatSetRussell.entity_rejects_unrestricted_comprehension.
