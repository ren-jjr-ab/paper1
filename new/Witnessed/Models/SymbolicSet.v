(* ============================================== *)
(*  SymbolicSet                                     *)
(*                                                  *)
(*  Framework instance for naive set theory over    *)
(*  a parameter element type E : ElemSig.           *)
(*                                                  *)
(*  Grammar (Sprint 1 — decidable-equality clean):  *)
(*    SEmpty                                        *)
(*    SInsert x s      = s ∪ {x}                    *)
(*    SUnion a b        = a ∪ b                     *)
(*    SIntersect a b    = a ∩ b                     *)
(*    SComplement a     = ¬a                        *)
(*    SAll              = universe of E.Elem        *)
(*                                                  *)
(*  These close under finite representation with   *)
(*  fully decidable membership. `SComplement SAll` *)
(*  = SEmpty in extension; `SComplement SEmpty` =   *)
(*  SAll — the framework's = axis captures these    *)
(*  equivalences via paper projection.              *)
(*                                                  *)
(*  Infinite representations that require non-     *)
(*  decidable or higher-order predicates            *)
(*  (SFromDec / SFromProp) are Sprint 2 additive.   *)
(*                                                  *)
(*  Entity / interact (CauchyReal-parallel):        *)
(*    SREnt s t    : set at external time t         *)
(*    SQuery x t   : "is x a member?" viewpoint     *)
(*                                                  *)
(*  interact at SREnt/SQuery collapses the set to   *)
(*  a canonical bool-answer form (singleton {x} or  *)
(*  SEmpty), mirroring CauchyReal's CEval→CTConst   *)
(*  collapse.                                       *)
(*                                                  *)
(*  collapse = False in Sprint 1. Set-level    *)
(*  convention witnesses live in Sprint 2 (where    *)
(*  undecidable membership creates sets that        *)
(*  cannot be distinguished by finite query).       *)
(* ============================================== *)

Require Import Existence.
Require Import Witnessed.
Require Import ElemSig.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.


Module Make (E : ElemSig) <: WitnessedSig.


  (* =========================================== *)
  (*  SETEXPR GRAMMAR                            *)
  (* =========================================== *)

  Inductive _SetExpr : Type :=
    | SEmpty      : _SetExpr
    | SInsert     : E.Elem -> _SetExpr -> _SetExpr
    | SUnion      : _SetExpr -> _SetExpr -> _SetExpr
    | SIntersect  : _SetExpr -> _SetExpr -> _SetExpr
    | SComplement : _SetExpr -> _SetExpr
    | SAll        : _SetExpr.

  Definition SetExpr : Type := _SetExpr.


  (* =========================================== *)
  (*  DECIDABLE MEMBERSHIP                       *)
  (* =========================================== *)

  Fixpoint member_bool (x : E.Elem) (s : SetExpr) : bool :=
    match s with
    | SEmpty           => false
    | SInsert y s'     =>
        if E.elem_eq_dec x y then true else member_bool x s'
    | SUnion a b       => member_bool x a || member_bool x b
    | SIntersect a b   => member_bool x a && member_bool x b
    | SComplement a    => negb (member_bool x a)
    | SAll             => true
    end.


  (* =========================================== *)
  (*  EXTENSIONAL EQUALITY                       *)
  (*                                             *)
  (*  Two sets are extensionally equal if they   *)
  (*  agree on every element's membership bit.   *)
  (*  This is the set-theoretic incarnation of   *)
  (*  the framework's = (paper projection).      *)
  (* =========================================== *)

  Definition ext_eq (s1 s2 : SetExpr) : Prop :=
    forall x : E.Elem, member_bool x s1 = member_bool x s2.


  (* =========================================== *)
  (*  DECIDABLE LEIBNIZ EQUALITY ON SETEXPR      *)
  (* =========================================== *)

  Fixpoint setexpr_eq_dec (s1 s2 : SetExpr) : {s1 = s2} + {s1 <> s2}.
  Proof.
    destruct s1 as [ | x1 s1 | a1 b1 | a1 b1 | s1 | ];
      destruct s2 as [ | x2 s2 | a2 b2 | a2 b2 | s2 | ];
      try (right; intros H; inversion H; fail);
      try (left; reflexivity).
    - (* SInsert *)
      destruct (E.elem_eq_dec x1 x2) as [Hx | Hx].
      + destruct (setexpr_eq_dec s1 s2) as [Hs | Hs].
        * left. subst. reflexivity.
        * right. intros H. inversion H. contradiction.
      + right. intros H. inversion H. contradiction.
    - (* SUnion *)
      destruct (setexpr_eq_dec a1 a2) as [Ha | Ha].
      + destruct (setexpr_eq_dec b1 b2) as [Hb | Hb].
        * left. subst. reflexivity.
        * right. intros H. inversion H. contradiction.
      + right. intros H. inversion H. contradiction.
    - (* SIntersect *)
      destruct (setexpr_eq_dec a1 a2) as [Ha | Ha].
      + destruct (setexpr_eq_dec b1 b2) as [Hb | Hb].
        * left. subst. reflexivity.
        * right. intros H. inversion H. contradiction.
      + right. intros H. inversion H. contradiction.
    - (* SComplement *)
      destruct (setexpr_eq_dec s1 s2) as [Hs | Hs].
      + left. subst. reflexivity.
      + right. intros H. inversion H. contradiction.
  Defined.


  (* =========================================== *)
  (*  ENTITY                                     *)
  (* =========================================== *)

  Inductive _Entity : Type :=
    | SREnt  : SetExpr -> nat -> _Entity
    | SQuery : E.Elem  -> nat -> _Entity.

  Definition Entity : Type := _Entity.

  Definition tm_of (e : Entity) : nat :=
    match e with
    | SREnt _ t  => t
    | SQuery _ t => t
    end.


  (* =========================================== *)
  (*  DECIDABLE ENTITY EQUALITY                  *)
  (* =========================================== *)

  Definition entity_eq_dec (a b : Entity) : {a = b} + {a <> b}.
  Proof.
    destruct a as [s1 t1 | x1 t1]; destruct b as [s2 t2 | x2 t2].
    - destruct (setexpr_eq_dec s1 s2) as [Hs | Hs].
      + destruct (Nat.eq_dec t1 t2) as [Ht | Ht].
        * left. subst. reflexivity.
        * right. intros H. inversion H. contradiction.
      + right. intros H. inversion H. contradiction.
    - right. intros H. inversion H.
    - right. intros H. inversion H.
    - destruct (E.elem_eq_dec x1 x2) as [Hx | Hx].
      + destruct (Nat.eq_dec t1 t2) as [Ht | Ht].
        * left. subst. reflexivity.
        * right. intros H. inversion H. contradiction.
      + right. intros H. inversion H. contradiction.
  Defined.


  (* =========================================== *)
  (*  INTERACT / CONVENTION / EXTERNAL TIME      *)
  (*                                             *)
  (*  At SQuery viewpoint the set collapses to   *)
  (*  a canonical bool-answer form:              *)
  (*    member x s = true  ⟹  {x}                *)
  (*    member x s = false ⟹  ∅                 *)
  (*                                             *)
  (*  Two sets extensionally equal collapse      *)
  (*  identically — that is the = axis witness.  *)
  (* =========================================== *)

  Definition interact (a b : Entity) : Entity :=
    match entity_eq_dec a b with
    | left _ => a
    | right _ =>
        let new_t := S (Nat.max (tm_of a) (tm_of b)) in
        match a, b with
        | SREnt s _, SQuery x _ =>
            if member_bool x s
            then SREnt (SInsert x SEmpty) new_t
            else SREnt SEmpty new_t
        | SREnt s _, SREnt _ _ =>
            SREnt s new_t
        | SQuery x _, _ =>
            SQuery x new_t
        end
    end.

  Definition collapse (_ _ : Entity) : Prop := False.

  Definition witness_time (a : Entity) : nat := tm_of a.


  (* =========================================== *)
  (*  AXIOM PROOFS                               *)
  (* =========================================== *)

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof.
    intros a. unfold interact.
    destruct (entity_eq_dec a a) as [_ | H].
    - reflexivity.
    - exfalso. apply H. reflexivity.
  Qed.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply entity_eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (SREnt SEmpty 0), (SQuery E.witness 0).
    intros H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b : Entity, interact a b <> a.
  Proof.
    intros [s t | x t].
    - exists (SREnt s (S t)).
      unfold interact.
      destruct (entity_eq_dec (SREnt s t) (SREnt s (S t))) as [Heq | _].
      + inversion Heq. lia.
      + intros H. inversion H. lia.
    - exists (SQuery x (S t)).
      unfold interact.
      destruct (entity_eq_dec (SQuery x t) (SQuery x (S t))) as [Heq | _].
      + inversion Heq. lia.
      + intros H. inversion H. lia.
  Qed.

  Theorem interaction_cannot_witness_collapse :
    forall a b : Entity,
      collapse a b ->
      forall c : Entity, interact a c <> interact b c.
  Proof. intros a b H. destruct H. Qed.

  Theorem witness_advances_on_nonself :
    forall a c : Entity,
      interact a c <> a ->
      witness_time (interact a c) > witness_time a.
  Proof.
    intros a c Hne.
    unfold interact in Hne. unfold interact.
    destruct (entity_eq_dec a c) as [_ | _].
    - exfalso. apply Hne. reflexivity.
    - unfold witness_time.
      destruct a as [sa ta | xa ta]; destruct c as [sc tc | xc tc].
      + simpl. lia.
      + simpl. destruct (member_bool xc sa); simpl; lia.
      + simpl. lia.
      + simpl. lia.
  Qed.

End Make.
