(* =========================================== *)
(*  Existence — three primitives, five axioms.  *)
(*                                              *)
(*  Entity is the sole type. interact is the   *)
(*  binary operation. collapse is the binary    *)
(*  relation recording observational            *)
(*  distinctness no interact step can witness.  *)
(*                                              *)
(*  interact_with is a dichotomy: every entity *)
(*  is either an absorber                       *)
(*  (forall b, interact a b = a) or has a      *)
(*  non-self partner. The absorbing branch is   *)
(*  what makes lattice-top, lazy-infinity, and  *)
(*  similar terminal-style entities expressible *)
(*  inside the framework, replacing the         *)
(*  external witness machinery (Witnessed) of   *)
(*  prior iterations.                           *)
(*                                              *)
(*  The derived predicate `frozen` capturing    *)
(*  the absorbing branch lives in Theory.v.    *)
(*  Sig instances only need to provide the      *)
(*  parameters and prove the axioms below.      *)
(*                                              *)
(*  interaction_cannot_witness_collapse         *)
(*  secures the meaning of collapse.            *)
(* =========================================== *)

Module Type ExistenceSig.

  Parameter Entity : Type.

  Parameter interact : Entity -> Entity -> Entity.

  Parameter collapse : Entity -> Entity -> Prop.

  (* --- AXIOMS --- *)

  Axiom interact_self : forall a : Entity, interact a a = a.

  Axiom entity_eq_dec :
    forall a b : Entity, {a = b} + {a <> b}.

  Axiom existence : exists a b : Entity, a <> b.

  (* Every entity is either an absorber (forall b,
     interact a b = a) or has a partner that moves it.
     The absorbing branch is named `frozen` in Theory.v. *)
  Axiom interact_with :
    forall a : Entity,
      (forall b, interact a b = a) \/ exists b, interact a b <> a.

  (* No interaction on a common witness can bring two
     collapse-related entities to the same result. *)
  Axiom interaction_cannot_witness_collapse :
    forall a b : Entity, collapse a b ->
      forall c : Entity, interact a c <> interact b c.

End ExistenceSig.
