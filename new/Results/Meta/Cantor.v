(* ============================================== *)
(*  CantorTheorem                                   *)
(*                                                  *)
(*  No function X → (X → Prop) is surjective.      *)
(*  Equivalently, |P(X)| > |X| for every type X.    *)
(*                                                  *)
(*  This is a canonical instance of the §7-C        *)
(*  principle from our design guide: impossibility  *)
(*  requires a structural proof. The proof is the   *)
(*  diagonal construction:                          *)
(*                                                  *)
(*    D(x) := ¬ f(x)(x)                             *)
(*                                                  *)
(*  For any candidate x with f(x) = D we obtain     *)
(*  f(x)(x) = D(x) = ¬ f(x)(x) — the P ↔ ¬P         *)
(*  contradiction, provable intuitionistically.     *)
(*                                                  *)
(*  Cardinality consequence for SymbolicSet:        *)
(*                                                  *)
(*  The SymbolicSet grammar over any carrier        *)
(*  generates terms in a finite-branching           *)
(*  algebra; for a countable carrier the term       *)
(*  type is countable. Cantor's theorem implies     *)
(*  that the full predicate type X → Prop strictly  *)
(*  exceeds this cardinality, so no enumeration of  *)
(*  SymbolicSet terms can surject onto predicates.  *)
(*  Some predicates are definable but not           *)
(*  constructible in the grammar — an impossibility *)
(*  residing in the grammar's very shape.           *)
(* ============================================== *)

From Stdlib Require Import Bool.


(* =========================================== *)
(*  DIAGONAL LEMMA                              *)
(*                                              *)
(*  A proposition cannot be equivalent to its   *)
(*  own negation. This is the engine behind     *)
(*  every diagonal argument.                    *)
(* =========================================== *)

Lemma P_iff_not_P_False : forall P : Prop, (P <-> ~ P) -> False.
Proof.
  intros P [H1 H2].
  assert (Hnp : ~ P) by (intros Hp; exact (H1 Hp Hp)).
  exact (Hnp (H2 Hnp)).
Qed.


(* =========================================== *)
(*  CANTOR — PROPOSITIONAL VERSION              *)
(*                                              *)
(*  No map f : X → (X → Prop) is surjective.    *)
(*  The explicit witness missed is the          *)
(*  diagonal predicate D(x) := ¬ f(x)(x).       *)
(* =========================================== *)

Theorem cantor :
  forall (X : Type) (f : X -> (X -> Prop)),
    exists P : X -> Prop, forall x : X, f x <> P.
Proof.
  intros X f.
  exists (fun x => ~ f x x).
  intros x Heq.
  assert (Hxx : f x x <-> ~ f x x).
  { split.
    - intros H. rewrite Heq in H. exact H.
    - intros H. rewrite Heq. exact H. }
  exact (P_iff_not_P_False _ Hxx).
Qed.


(* =========================================== *)
(*  CANTOR — BOOLEAN VERSION                    *)
(*                                              *)
(*  The same argument with decidable (boolean)  *)
(*  characteristic functions. Here the          *)
(*  diagonal is simply x ↦ negb (f x x).        *)
(* =========================================== *)

Theorem cantor_bool :
  forall (X : Type) (f : X -> (X -> bool)),
    exists g : X -> bool, forall x : X, f x <> g.
Proof.
  intros X f.
  exists (fun x => negb (f x x)).
  intros x Heq.
  pose proof (f_equal (fun h : X -> bool => h x) Heq) as Hx.
  cbv beta in Hx.
  destruct (f x x); simpl in Hx; discriminate.
Qed.


(* =========================================== *)
(*  CONCRETE INSTANCE — nat                     *)
(*                                              *)
(*  No enumeration of natural numbers covers    *)
(*  all predicates on naturals.                 *)
(* =========================================== *)

Corollary cantor_nat :
  forall f : nat -> (nat -> Prop),
    exists P : nat -> Prop, forall n : nat, f n <> P.
Proof. intros. apply cantor. Qed.

Corollary cantor_nat_bool :
  forall f : nat -> (nat -> bool),
    exists g : nat -> bool, forall n : nat, f n <> g.
Proof. intros. apply cantor_bool. Qed.


(* =========================================== *)
(*  THE DIAGONAL IS CONSTRUCTIVE                *)
(*                                              *)
(*  The witness is given explicitly by the      *)
(*  diagonal, not conjured by excluded middle.  *)
(*  We expose this by packaging the theorem     *)
(*  as a definition.                            *)
(* =========================================== *)

Definition cantor_diagonal {X : Type} (f : X -> (X -> Prop)) : X -> Prop :=
  fun x => ~ f x x.

Theorem cantor_diagonal_missed :
  forall (X : Type) (f : X -> (X -> Prop)) (x : X),
    f x <> cantor_diagonal f.
Proof.
  intros X f x Heq. unfold cantor_diagonal in Heq.
  assert (Hxx : f x x <-> ~ f x x).
  { split.
    - intros H. rewrite Heq in H. exact H.
    - intros H. rewrite Heq. exact H. }
  exact (P_iff_not_P_False _ Hxx).
Qed.


(* =========================================== *)
(*  REFORMULATION — NO SURJECTION               *)
(*                                              *)
(*  "Surjective" spelled out as ∀ P, ∃ x.       *)
(*  The theorem in its negation-of-surjection   *)
(*  form.                                       *)
(* =========================================== *)

Theorem cantor_no_surjection :
  forall (X : Type) (f : X -> (X -> Prop)),
    ~ (forall P : X -> Prop, exists x : X, f x = P).
Proof.
  intros X f Hsurj.
  destruct (cantor X f) as [P HP].
  destruct (Hsurj P) as [x Hx].
  exact (HP x Hx).
Qed.
