(* ================================================ *)
(*  ExistenceHalting.v                              *)
(*                                                  *)
(*  Termination is not a concept of the Existence   *)
(*  layer.                                          *)
(*                                                  *)
(*  Using only Existence primitives, the natural    *)
(*  candidate for "halted" is a fixed point under   *)
(*  every interaction:                              *)
(*                                                  *)
(*    is_terminal a := forall b, interact a b = a   *)
(*                                                  *)
(*  i.e., a is unchanged by interaction with every  *)
(*  viewpoint b. The interact_with axiom refutes    *)
(*  this directly: every entity has at least one    *)
(*  viewpoint under which interaction moves it.     *)
(*                                                  *)
(*  Consequence: no halts-like predicate can live   *)
(*  at the Existence layer. It either reduces to    *)
(*  is_terminal (and is vacuously false), or it     *)
(*  imports structure from a higher layer (such as  *)
(*  Iterable's remaining).                          *)
(*                                                  *)
(*  This is a structural obstruction, not a         *)
(*  computational one. The issue is not that we     *)
(*  cannot decide termination; it is that           *)
(*  termination is not a question at this layer in  *)
(*  the first place.                                *)
(*                                                  *)
(*  Rice-style undecidability (via a collapse       *)
(*  witness) is a separate result, already          *)
(*  captured in results/FrameworkRice.v. The two    *)
(*  are orthogonal: Rice says non-trivial semantic  *)
(*  predicates are undecidable; this file says      *)
(*  termination is not even expressible here.       *)
(* ================================================ *)

Require Import Existence.

Module Make (D : ExistenceSig).

  Import D.
  Module DT := ExistenceTheory D.
  Import DT.

  (* ============================================= *)
  (*  TERMINAL AT THE EXISTENCE LAYER              *)
  (* ============================================= *)

  (* An entity that is unchanged by interaction
     under every viewpoint. *)
  Definition is_terminal (a : Entity) : Prop :=
    forall b : Entity, interact a b = a.

  (* ============================================= *)
  (*  VACUITY                                      *)
  (*                                               *)
  (*  interact_with guarantees, for every entity,  *)
  (*  a viewpoint under which interaction yields   *)
  (*  something other than the entity itself. That *)
  (*  witness directly refutes is_terminal.        *)
  (* ============================================= *)

  Theorem is_terminal_vacuous :
    forall a : Entity, ~ is_terminal a.
  Proof.
    intros a Hterm.
    destruct (interact_with a) as [b Hne].
    apply Hne. apply Hterm.
  Qed.

  (* ============================================= *)
  (*  NO HALTING PREDICATE AT THIS LAYER           *)
  (*                                               *)
  (*  is_terminal has no witnesses. Any halting    *)
  (*  notion defined purely from interaction must  *)
  (*  therefore either collapse into is_terminal   *)
  (*  (and be empty) or borrow structure from a    *)
  (*  higher layer.                                *)
  (* ============================================= *)

  Theorem no_terminal_witness :
    ~ exists a : Entity, is_terminal a.
  Proof.
    intros [a Hterm]. exact (is_terminal_vacuous a Hterm).
  Qed.

End Make.
