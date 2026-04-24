(* =========================================== *)
(*  Existence — three primitives, five axioms. *)
(*                                             *)
(*  Entity is the sole type. interact is the  *)
(*  binary operation. collapse is the binary   *)
(*  relation recording identifications that    *)
(*  interaction cannot witness — structurally  *)
(*  distinct entities that no interact step    *)
(*  can bring into agreement.                  *)
(*                                             *)
(*  interact_with forces motion: every entity  *)
(*  has a non-self partner.                    *)
(*  interaction_cannot_witness_collapse        *)
(*  secures the meaning of collapse.           *)
(*  Irreflexivity of collapse is derived in    *)
(*  ExistenceTheory from these two.            *)
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

  (* Every entity has a partner that moves it. *)
  Axiom interact_with :
    forall a : Entity, exists b, interact a b <> a.

  (* No interaction on a common witness can bring two
     collapse-related entities to the same result. *)
  Axiom interaction_cannot_witness_collapse :
    forall a b : Entity, collapse a b ->
      forall c : Entity, interact a c <> interact b c.

End ExistenceSig.
