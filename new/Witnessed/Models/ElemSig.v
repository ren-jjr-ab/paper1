(* ============================================== *)
(*  ElemSig                                         *)
(*                                                  *)
(*  Module type for the element parameter of       *)
(*  SymbolicSet. Requires a type plus decidable    *)
(*  equality plus a default witness so that        *)
(*  downstream existence and interact_with axioms  *)
(*  can be stated concretely.                      *)
(*                                                  *)
(*  Instances:                                      *)
(*    NatElem : nat-indexed sets                    *)
(*    SetElem : recursive nesting — Elem is itself *)
(*              a SymbolicSet.Entity                *)
(* ============================================== *)


Module Type ElemSig.
  Parameter Elem : Type.
  Parameter elem_eq_dec : forall x y : Elem, {x = y} + {x <> y}.
  Parameter witness : Elem.
End ElemSig.
