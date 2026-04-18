(* ================================================ *)
(*  PolyModel.v                                      *)
(*                                                   *)
(*  Polynomial expressions as a rewrite system.      *)
(*  One rewrite step is one interaction.             *)
(*                                                   *)
(*  Rules:                                           *)
(*    pow_zero:   e^0        -> 1                   *)
(*    pow_one:    e^1        -> e                   *)
(*    pow_unfold: e^(k+2)    -> e * e^(k+1)         *)
(*    distrib_l:  (a+b)*c    -> a*c + b*c           *)
(*    distrib_r:  a*(b+c)    -> a*b + a*c           *)
(*                                                   *)
(*  rewrite_one picks the leftmost-outermost         *)
(*  reducible position. rewrite_chain iterates       *)
(*  with a fuel bound and returns the final term     *)
(*  together with the number of rewrite steps        *)
(*  actually taken.                                  *)
(*                                                   *)
(*  The concrete examples at the bottom compute      *)
(*  the chain length for (a + b)^n at n = 2, 3, 4,   *)
(*  5. The measured lengths are stated as Examples   *)
(*  that typecheck by reflexivity.                   *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.

Require Import Existence.
Require Import Computable.

(* ================================================ *)
(*  EXPRESSIONS                                      *)
(* ================================================ *)

Inductive Expr : Type :=
  | EVar   : nat -> Expr
  | EConst : nat -> Expr
  | EAdd   : Expr -> Expr -> Expr
  | EMul   : Expr -> Expr -> Expr
  | EPow   : Expr -> nat -> Expr.

Fixpoint expr_size (e : Expr) : nat :=
  match e with
  | EVar _       => 1
  | EConst _     => 1
  | EAdd a b     => 1 + expr_size a + expr_size b
  | EMul a b     => 1 + expr_size a + expr_size b
  | EPow base k  => 1 + expr_size base + k
  end.

(* ================================================ *)
(*  ONE REWRITE STEP — OUTERMOST STRATEGY            *)
(*                                                   *)
(*  Leftmost-outermost. The root is tried first;     *)
(*  only if the root has no rule do we recurse into  *)
(*  the children. Returns Some e' if a rewrite was   *)
(*  applied, None if the expression is in normal     *)
(*  form under these rules.                          *)
(* ================================================ *)

Fixpoint rewrite_one (e : Expr) : option Expr :=
  match e with
  | EVar _   => None
  | EConst _ => None
  | EPow base 0        => Some (EConst 1)
  | EPow base 1        => Some base
  | EPow base (S (S k)) =>
      Some (EMul base (EPow base (S k)))
  | EMul (EAdd a b) c =>
      Some (EAdd (EMul a c) (EMul b c))
  | EMul a (EAdd b c) =>
      Some (EAdd (EMul a b) (EMul a c))
  | EMul a b =>
      match rewrite_one a with
      | Some a' => Some (EMul a' b)
      | None =>
          match rewrite_one b with
          | Some b' => Some (EMul a b')
          | None    => None
          end
      end
  | EAdd a b =>
      match rewrite_one a with
      | Some a' => Some (EAdd a' b)
      | None =>
          match rewrite_one b with
          | Some b' => Some (EAdd a b')
          | None    => None
          end
      end
  end.

(* ================================================ *)
(*  ONE REWRITE STEP — INNERMOST STRATEGY            *)
(*                                                   *)
(*  Children are tried first; the root rule fires   *)
(*  only when no child is still reducible. On this  *)
(*  rule set this delays outer power unfolds until  *)
(*  all inner simplifications are done.              *)
(* ================================================ *)

Fixpoint rewrite_one_in (e : Expr) : option Expr :=
  match e with
  | EVar _   => None
  | EConst _ => None
  | EAdd a b =>
      match rewrite_one_in a with
      | Some a' => Some (EAdd a' b)
      | None =>
          match rewrite_one_in b with
          | Some b' => Some (EAdd a b')
          | None    => None
          end
      end
  | EMul a b =>
      match rewrite_one_in a with
      | Some a' => Some (EMul a' b)
      | None =>
          match rewrite_one_in b with
          | Some b' => Some (EMul a b')
          | None =>
              match a, b with
              | EAdd x y, _ => Some (EAdd (EMul x b) (EMul y b))
              | _, EAdd x y => Some (EAdd (EMul a x) (EMul a y))
              | _, _        => None
              end
          end
      end
  | EPow base k =>
      match rewrite_one_in base with
      | Some base' => Some (EPow base' k)
      | None =>
          match k with
          | 0            => Some (EConst 1)
          | 1            => Some base
          | S (S k')     => Some (EMul base (EPow base (S k')))
          end
      end
  end.

(* ================================================ *)
(*  CHAINS                                           *)
(*                                                   *)
(*  rewrite_chain fuel e walks rewrite_one steps     *)
(*  until either no rewrite applies or the fuel is   *)
(*  exhausted. Returns the final expression and the  *)
(*  number of steps taken.                           *)
(*                                                   *)
(*  rewrite_chain_in is the innermost analogue.      *)
(* ================================================ *)

Fixpoint rewrite_chain (fuel : nat) (e : Expr) : Expr * nat :=
  match fuel with
  | 0 => (e, 0)
  | S f =>
      match rewrite_one e with
      | None    => (e, 0)
      | Some e' =>
          let '(final, n) := rewrite_chain f e' in
          (final, S n)
      end
  end.

Fixpoint rewrite_chain_in (fuel : nat) (e : Expr) : Expr * nat :=
  match fuel with
  | 0 => (e, 0)
  | S f =>
      match rewrite_one_in e with
      | None    => (e, 0)
      | Some e' =>
          let '(final, n) := rewrite_chain_in f e' in
          (final, S n)
      end
  end.

Definition chain_final (fuel : nat) (e : Expr) : Expr :=
  fst (rewrite_chain fuel e).

Definition chain_cost (fuel : nat) (e : Expr) : nat :=
  snd (rewrite_chain fuel e).

Definition chain_cost_in (fuel : nat) (e : Expr) : nat :=
  snd (rewrite_chain_in fuel e).

(* ================================================ *)
(*  BINOMIAL EXAMPLES                                *)
(*                                                   *)
(*  a = EVar 0, b = EVar 1.                          *)
(*  ab_pow n = (a + b)^n.                            *)
(* ================================================ *)

Definition a : Expr := EVar 0.
Definition b : Expr := EVar 1.
Definition ab_pow (n : nat) : Expr := EPow (EAdd a b) n.

(* Chain lengths — verified by reflexivity.

   Observed growth:
     n : 2  3   4   5    6
     c : 6  20  56  144  352

   The successive ratios c(n+1) / c(n) are 3.33,
   2.80, 2.57, 2.44 — drifting down but still well
   above 2. These are the concrete step counts this
   specific rewriter takes on (a + b)^n with the
   leftmost-outermost strategy. *)

Example ab_pow_2_cost : chain_cost 100 (ab_pow 2) = 6.
Proof. reflexivity. Qed.

Example ab_pow_3_cost : chain_cost 200 (ab_pow 3) = 20.
Proof. reflexivity. Qed.

Example ab_pow_4_cost : chain_cost 500 (ab_pow 4) = 56.
Proof. reflexivity. Qed.

Example ab_pow_5_cost : chain_cost 2000 (ab_pow 5) = 144.
Proof. reflexivity. Qed.

Example ab_pow_6_cost : chain_cost 5000 (ab_pow 6) = 352.
Proof. reflexivity. Qed.

(* Innermost strategy is strictly cheaper on the
   same inputs. This rule set favours innermost
   because reducing EPow e 1 -> e early, before
   distribution has duplicated its occurrence,
   removes one EPow rather than several. *)

Example ab_pow_2_cost_in : chain_cost_in 100 (ab_pow 2) = 5.
Proof. reflexivity. Qed.

Example ab_pow_3_cost_in : chain_cost_in 200 (ab_pow 3) = 13.
Proof. reflexivity. Qed.

Example ab_pow_4_cost_in : chain_cost_in 500 (ab_pow 4) = 29.
Proof. reflexivity. Qed.

Example ab_pow_5_cost_in : chain_cost_in 2000 (ab_pow 5) = 61.
Proof. reflexivity. Qed.

Example ab_pow_6_cost_in : chain_cost_in 5000 (ab_pow 6) = 125.
Proof. reflexivity. Qed.

(* Side by side:
     n : 2  3   4   5    6
     out: 6  20  56  144  352
     in : 5  13  29  61   125
     save: 1  7   27  83   227

   Both reach the same normal form; only the
   number of atomic steps differs. *)

(* ================================================ *)
(*  FRAMEWORK INSTANCE                               *)
(*                                                   *)
(*  PolyModel lifted to ComputableExistenceSig so    *)
(*  that storage_cost and flip_cost from the         *)
(*  framework apply. Entities wrap an Expr together  *)
(*  with the current category and the two cost       *)
(*  accumulators; pm_step runs rewrite_one once      *)
(*  (if anything is reducible) and updates the       *)
(*  accumulators per storage_pays_capacity and       *)
(*  flip_pays_work.                                  *)
(*                                                   *)
(*  The rewrite strategy baked into pm_step is the   *)
(*  outermost one (rewrite_one, not rewrite_one_in). *)
(*  Swapping strategies means a different instance.  *)
(* ================================================ *)

Fixpoint expr_eq_dec (a b : Expr) : {a = b} + {a <> b}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Inductive PMEnt : Type :=
  | PMNormal  : nat -> Expr -> nat -> nat -> PMEnt
    (* dim, expr, storage, flip *)
  | PMFrozen  : nat -> nat -> nat -> PMEnt -> PMEnt.
    (* dim, storage, flip, inner *)

Fixpoint pm_dim (x : PMEnt) : nat :=
  match x with
  | PMNormal d _ _ _ => d
  | PMFrozen d _ _ _ => d
  end.

Fixpoint pm_info (x : PMEnt) : nat :=
  match x with
  | PMNormal _ e _ _ => expr_size e
  | PMFrozen _ _ _ inner => pm_info inner
  end.

Fixpoint pm_stor (x : PMEnt) : nat :=
  match x with
  | PMNormal _ _ s _ => s
  | PMFrozen _ s _ _ => s
  end.

Fixpoint pm_flip (x : PMEnt) : nat :=
  match x with
  | PMNormal _ _ _ f => f
  | PMFrozen _ _ f _ => f
  end.

Definition dim_as_entity (d : nat) : PMEnt :=
  PMNormal d (EConst 0) 0 0.

(* pm_step: one rewrite attempt. If the current expr
   is already in normal form, only the category is
   updated (the cost accumulators still advance).
   Otherwise apply rewrite_one, add the source
   expr_size to storage, and add max 1 (growth) to
   flip. *)
Definition pm_step (e : PMEnt) (d : nat) : PMEnt :=
  match e with
  | PMNormal _ expr s f =>
      let new_expr :=
        match rewrite_one expr with
        | Some e' => e'
        | None    => expr
        end in
      PMNormal d new_expr
        (s + expr_size expr)
        (f + Nat.max 1 (expr_size new_expr - expr_size expr))
  | PMFrozen _ s f inner =>
      PMFrozen d (s + pm_info inner) (f + 1) inner
  end.

Fixpoint pm_interact_at (x : PMEnt) (d : nat) : PMEnt :=
  match x with
  | PMNormal src_d _ _ _ =>
      if Nat.eq_dec src_d d then x else pm_step x d
  | PMFrozen src_d _ _ _ =>
      if Nat.eq_dec src_d d then x else pm_step x d
  end.

Lemma pm_interact_at_dim : forall x d, pm_dim (pm_interact_at x d) = d.
Proof.
  induction x as [d0 e s f | d0 s f inner IH]; intro d; simpl.
  - destruct (Nat.eq_dec d0 d); simpl; congruence.
  - destruct (Nat.eq_dec d0 d); simpl; congruence.
Qed.

Lemma pm_interact_at_self : forall x, pm_interact_at x (pm_dim x) = x.
Proof.
  induction x as [d e s f | d s f inner IH]; simpl.
  - destruct (Nat.eq_dec d d); [reflexivity | contradiction].
  - destruct (Nat.eq_dec d d); [reflexivity | contradiction].
Qed.

Definition pm_freeze (e : PMEnt) : PMEnt := PMFrozen (pm_dim e) 0 0 e.

Lemma pm_freeze_injective :
  forall a b, pm_freeze a = pm_freeze b -> a = b.
Proof. intros a b H. unfold pm_freeze in H. inversion H. reflexivity. Qed.

Module PolyComputable <: ComputableExistenceSig.

  Definition Entity : Type := PMEnt.

  Definition interact (a b : Entity) : Entity :=
    pm_interact_at a (pm_dim b).

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof. intros. unfold interact. apply pm_interact_at_self. Qed.

  Fixpoint pm_eq_dec (a b : PMEnt) : {a = b} + {a <> b}.
  Proof.
    refine (
      match a, b with
      | PMNormal d1 e1 s1 f1, PMNormal d2 e2 s2 f2 => _
      | PMFrozen d1 s1 f1 i1, PMFrozen d2 s2 f2 i2 => _
      | _, _ => right _
      end); try (intro H; inversion H).
    - destruct (Nat.eq_dec d1 d2); [| right; intro H; inversion H; contradiction].
      destruct (expr_eq_dec e1 e2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec s1 s2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec f1 f2); [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
    - destruct (Nat.eq_dec d1 d2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec s1 s2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec f1 f2); [| right; intro H; inversion H; contradiction].
      destruct (pm_eq_dec i1 i2); [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
  Defined.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply pm_eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (PMNormal 0 (EConst 0) 0 0), (PMNormal 1 (EConst 0) 0 0).
    intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intros a. exists (dim_as_entity (S (pm_dim a))).
    unfold interact, dim_as_entity. simpl pm_dim.
    intro H.
    assert (Hd : pm_dim (pm_interact_at a (S (pm_dim a))) = S (pm_dim a)).
    { apply pm_interact_at_dim. }
    rewrite H in Hd. lia.
  Qed.

  Definition convention_eq : Entity -> Entity -> Prop :=
    fun _ _ => False.

  Theorem convention_not_derivable :
    forall a b, convention_eq a b ->
    forall c, interact a c <> interact b c.
  Proof. intros a b H. exfalso. exact H. Qed.

  (* ---- Computable layer ---- *)

  Definition info_size (e : Entity) : nat := pm_info e.
  Definition storage_cost (e : Entity) : nat := pm_stor e.
  Definition flip_cost (e : Entity) : nat := pm_flip e.

  Lemma pm_interact_at_normal_non_id :
    forall d0 e s f d,
      d0 <> d ->
      pm_interact_at (PMNormal d0 e s f) d = pm_step (PMNormal d0 e s f) d.
  Proof.
    intros. simpl. destruct (Nat.eq_dec d0 d); [contradiction | reflexivity].
  Qed.

  Lemma pm_interact_at_frozen_non_id :
    forall d0 s f inner d,
      d0 <> d ->
      pm_interact_at (PMFrozen d0 s f inner) d = pm_step (PMFrozen d0 s f inner) d.
  Proof.
    intros. simpl. destruct (Nat.eq_dec d0 d); [contradiction | reflexivity].
  Qed.

  Theorem storage_pays_capacity :
    forall (a c : Entity),
      interact a c <> a ->
      storage_cost (interact a c) = storage_cost a + info_size a.
  Proof.
    intros a c Hne.
    unfold storage_cost, info_size, interact in *.
    induction a as [d0 e s f | d0 s f inner _].
    - assert (Hd : d0 <> pm_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (pm_dim c)); [reflexivity | contradiction]. }
      rewrite (pm_interact_at_normal_non_id d0 e s f (pm_dim c) Hd).
      simpl. reflexivity.
    - assert (Hd : d0 <> pm_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (pm_dim c)); [reflexivity | contradiction]. }
      rewrite (pm_interact_at_frozen_non_id d0 s f inner (pm_dim c) Hd).
      simpl. reflexivity.
  Qed.

  Theorem flip_pays_work :
    forall (a c : Entity),
      interact a c <> a ->
      flip_cost (interact a c) =
        flip_cost a + Nat.max 1 (info_size (interact a c) - info_size a).
  Proof.
    intros a c Hne.
    unfold flip_cost, info_size, interact in *.
    induction a as [d0 e s f | d0 s f inner _].
    - assert (Hd : d0 <> pm_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (pm_dim c)); [reflexivity | contradiction]. }
      rewrite (pm_interact_at_normal_non_id d0 e s f (pm_dim c) Hd).
      simpl. destruct (rewrite_one e) as [e'|]; simpl; reflexivity.
    - assert (Hd : d0 <> pm_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (pm_dim c)); [reflexivity | contradiction]. }
      rewrite (pm_interact_at_frozen_non_id d0 s f inner (pm_dim c) Hd).
      simpl.
      assert (H0 : pm_info inner - pm_info inner = 0) by lia.
      rewrite H0. simpl. reflexivity.
  Qed.

End PolyComputable.

(* ================================================ *)
(*  INSTANCE-INTERNAL FREEZE                         *)
(*                                                   *)
(*  Re-exports pm_freeze as the module-level         *)
(*  freeze and restates injectivity and              *)
(*  freeze_preserves_existence at the Entity level.  *)
(* ================================================ *)

Module PMCT := ComputableExistenceTheory PolyComputable.
Import PolyComputable PMCT.

Definition freeze (e : Entity) : Entity := pm_freeze e.

Definition is_frozen (a : Entity) : Prop :=
  exists b, a = freeze b.

Theorem freeze_injective :
  forall a b, freeze a = freeze b -> a = b.
Proof. exact pm_freeze_injective. Qed.

Theorem freeze_preserves_existence :
  forall (a b c : Entity),
    is_frozen a -> is_frozen b ->
    interact a c = interact b c -> a = b.
Proof.
  intros a b c Hfa Hfb Hproj.
  destruct Hfa as [a' Ha]. destruct Hfb as [b' Hb].
  unfold freeze, pm_freeze in Ha, Hb. subst a b.
  unfold interact in Hproj. simpl in Hproj.
  destruct (Nat.eq_dec (pm_dim a') (pm_dim c)) as [Hea | Hea];
    destruct (Nat.eq_dec (pm_dim b') (pm_dim c)) as [Heb | Heb];
    inversion Hproj; try congruence.
Qed.

(* ================================================ *)
(*  FRAMEWORK COST MEASUREMENTS                      *)
(*                                                   *)
(*  Walk a PMNormal entity until its inner Expr is   *)
(*  in rewrite_one normal form and read off the      *)
(*  storage_cost and flip_cost accumulated along the *)
(*  chain.                                           *)
(* ================================================ *)

Fixpoint pm_walk (fuel : nat) (e : PMEnt) : PMEnt :=
  match fuel with
  | 0 => e
  | S f =>
      match e with
      | PMNormal d expr _ _ =>
          match rewrite_one expr with
          | None   => e
          | Some _ => pm_walk f (pm_step e (S d))
          end
      | _ => e
      end
  end.

Definition ab_init (n : nat) : PMEnt := PMNormal 0 (ab_pow n) 0 0.

Definition ab_final_stor (n fuel : nat) : nat := pm_stor (pm_walk fuel (ab_init n)).
Definition ab_final_flip (n fuel : nat) : nat := pm_flip (pm_walk fuel (ab_init n)).

(* Framework storage_cost and flip_cost for the
   (a + b)^n chain using pm_step's outermost rewriter.
   Verified by reflexivity.

   Growth table:
     n  | steps | storage | flip
     2  |   6   |    71   |  15
     3  |  20   |   618   |  52
     4  |  56   |  4181   | 143
     5  | 144   | 25194   | 358

   storage_cost is the sum of info_size (= expr_size
   of the source Expr) across the chain. Because
   distribution enlarges the tree on most steps, the
   source info_size grows through the walk and
   storage_cost grows faster than the step count.

   flip_cost is the sum of max 1 (growth) across
   the chain. Growth is how much info_size grew
   on that step; a shrinking or flat step still pays
   the minimum 1.

   n >= 6 hits Coq's nat reflexivity stack limit,
   so the table stops at n = 5. *)

Example ab_init_2_cost :
  (ab_final_stor 2 100, ab_final_flip 2 100) = (71, 15).
Proof. reflexivity. Qed.

Example ab_init_3_cost :
  (ab_final_stor 3 200, ab_final_flip 3 200) = (618, 52).
Proof. reflexivity. Qed.

Example ab_init_4_cost :
  (ab_final_stor 4 500, ab_final_flip 4 500) = (4181, 143).
Proof. reflexivity. Qed.

Example ab_init_5_cost :
  (ab_final_stor 5 2000, ab_final_flip 5 2000) = (25194, 358).
Proof. reflexivity. Qed.

(* ================================================ *)
(*  FAST STEP                                        *)
(*                                                   *)
(*  A single framework step that jumps from the     *)
(*  source Expr straight to its rewrite_chain        *)
(*  normal form. Storage and flip follow the same    *)
(*  formulas as pm_step (source info_size and        *)
(*  max 1 growth), but there is exactly one step    *)
(*  per walk.                                        *)
(*                                                   *)
(*  This models what a tactic like ring looks like   *)
(*  in the framework's vocabulary: the source state  *)
(*  is held only once (storage is small), and the    *)
(*  single big step pays the growth to the final    *)
(*  form in one flip charge.                         *)
(* ================================================ *)

Definition normalize_expr (fuel : nat) (e : Expr) : Expr :=
  fst (rewrite_chain fuel e).

Definition pm_step_fast (fuel : nat) (e : PMEnt) : PMEnt :=
  match e with
  | PMNormal d expr s f =>
      let new_expr := normalize_expr fuel expr in
      PMNormal (S d) new_expr
        (s + expr_size expr)
        (f + Nat.max 1 (expr_size new_expr - expr_size expr))
  | _ => e
  end.

Definition ab_fast_stor (n fuel : nat) : nat := pm_stor (pm_step_fast fuel (ab_init n)).
Definition ab_fast_flip (n fuel : nat) : nat := pm_flip (pm_step_fast fuel (ab_init n)).

(* Fast-step cost vs pm_walk cost:

              outermost (pm_walk)       fast (pm_step_fast)
    n | steps | storage | flip       | storage | flip
    2 |   6   |    71   |  15        |    6    |   9
    3 |  20   |   618   |  52        |    7    |  40
    4 |  56   |  4181   | 143        |    8    | 119
    5 | 144   | 25194   | 358        |    9    | 310

   storage in the fast column is just the source
   info_size of (a + b)^n, paid once. flip in the
   fast column is max 1 (size (normal) - size (a+b)^n)
   — the same total growth the slow walk pays, minus
   the minimum-1 surcharge at each small step. The
   two cost columns are the framework's honest
   account of the same underlying transformation
   seen at two different step granularities. *)

Example ab_fast_2_cost :
  (ab_fast_stor 2 100, ab_fast_flip 2 100) = (6, 9).
Proof. reflexivity. Qed.

Example ab_fast_3_cost :
  (ab_fast_stor 3 200, ab_fast_flip 3 200) = (7, 40).
Proof. reflexivity. Qed.

Example ab_fast_4_cost :
  (ab_fast_stor 4 500, ab_fast_flip 4 500) = (8, 119).
Proof. reflexivity. Qed.

Example ab_fast_5_cost :
  (ab_fast_stor 5 2000, ab_fast_flip 5 2000) = (9, 310).
Proof. reflexivity. Qed.

(* ================================================ *)
(*  SIMPLIFYING REWRITER                             *)
(*                                                   *)
(*  A second rewriter with an expanded rule set:    *)
(*  constant folding, like-term collection, power    *)
(*  unfold, distributivity. Designed for the        *)
(*  one-line algebraic simplifications used in      *)
(*  elementary math: 2x + 3x, (x+1)*2, and so on.   *)
(*                                                   *)
(*  Traversal is innermost-first so that const_fold *)
(*  applies to inner subterms before distributivity *)
(*  fires at a parent EMul.                          *)
(* ================================================ *)

Fixpoint expr_eqb (a b : Expr) : bool :=
  match a, b with
  | EVar n, EVar m => Nat.eqb n m
  | EConst n, EConst m => Nat.eqb n m
  | EAdd a1 a2, EAdd b1 b2 => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | EMul a1 a2, EMul b1 b2 => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | EPow a k, EPow b l => andb (expr_eqb a b) (Nat.eqb k l)
  | _, _ => false
  end.

Definition try_root_rule (e : Expr) : option Expr :=
  match e with
  | EPow _ 0 => Some (EConst 1)
  | EPow base 1 => Some base
  | EPow base (S (S k)) => Some (EMul base (EPow base (S k)))
  | EAdd (EConst m) (EConst n) => Some (EConst (m + n))
  | EMul (EConst m) (EConst n) => Some (EConst (m * n))
  | EAdd (EMul a1 c1) (EMul a2 c2) =>
      if expr_eqb c1 c2 then Some (EMul (EAdd a1 a2) c1) else None
  | EMul (EAdd a b) c => Some (EAdd (EMul a c) (EMul b c))
  | EMul a (EAdd b c) => Some (EAdd (EMul a b) (EMul a c))
  | _ => None
  end.

Fixpoint rewrite_one_s (e : Expr) : option Expr :=
  match e with
  | EVar _ | EConst _ => try_root_rule e
  | EAdd a b =>
      match rewrite_one_s a with
      | Some a' => Some (EAdd a' b)
      | None =>
          match rewrite_one_s b with
          | Some b' => Some (EAdd a b')
          | None    => try_root_rule (EAdd a b)
          end
      end
  | EMul a b =>
      match rewrite_one_s a with
      | Some a' => Some (EMul a' b)
      | None =>
          match rewrite_one_s b with
          | Some b' => Some (EMul a b')
          | None    => try_root_rule (EMul a b)
          end
      end
  | EPow base k =>
      match rewrite_one_s base with
      | Some b' => Some (EPow b' k)
      | None    => try_root_rule (EPow base k)
      end
  end.

Fixpoint rewrite_chain_s (fuel : nat) (e : Expr) : Expr * nat :=
  match fuel with
  | 0 => (e, 0)
  | S f =>
      match rewrite_one_s e with
      | None    => (e, 0)
      | Some e' =>
          let '(final, n) := rewrite_chain_s f e' in
          (final, S n)
      end
  end.

Definition chain_cost_s (fuel : nat) (e : Expr) : nat :=
  snd (rewrite_chain_s fuel e).

(* ================================================ *)
(*  ONE-LINE IDENTITIES                              *)
(*                                                   *)
(*  Each of the following is a single statement in  *)
(*  elementary algebra. The framework step count    *)
(*  is the number of atomic rewrite applications    *)
(*  rewrite_one_s performs to reach its normal      *)
(*  form for this rule set.                         *)
(*                                                   *)
(*  "one math line" vs "framework steps":           *)
(*                                                   *)
(*    2 * 3                → 6         :  1 step    *)
(*    2x + 3x              → 5x        :  2 steps   *)
(*    (x + 1) * 2          → x*2 + 2   :  2 steps   *)
(*    (x + 1) * (x + 2)                :  4 steps   *)
(*    2(x + 1) + 3(x + 1)              :  4 steps   *)
(*                                                   *)
(*  The final two normal forms are not the         *)
(*  handwritten ones (no commutativity of *, no    *)
(*  final collect after distribution); they are    *)
(*  what this rewriter's rule set reaches.          *)
(*                                                   *)
(*  The (x+1)*(x+2) and 2(x+1)+3(x+1) cases also    *)
(*  show that the step count depends on which rule *)
(*  fires at each position. A factor-first strategy *)
(*  on 2(x+1)+3(x+1) would reach 5(x+1) in fewer   *)
(*  steps; this rewriter distributes first and     *)
(*  cannot recover the common factor afterward.     *)
(* ================================================ *)

Definition var_x : Expr := EVar 0.

Definition id_2mul3       : Expr := EMul (EConst 2) (EConst 3).
Definition id_2x_plus_3x  : Expr := EAdd (EMul (EConst 2) var_x) (EMul (EConst 3) var_x).
Definition id_xp1_times_2 : Expr := EMul (EAdd var_x (EConst 1)) (EConst 2).
Definition id_xp1_xp2     : Expr := EMul (EAdd var_x (EConst 1)) (EAdd var_x (EConst 2)).
Definition id_2xp1_3xp1   : Expr := EAdd (EMul (EConst 2) (EAdd var_x (EConst 1)))
                                         (EMul (EConst 3) (EAdd var_x (EConst 1))).

Example id_2mul3_cost       : chain_cost_s 50  id_2mul3       = 1. Proof. reflexivity. Qed.
Example id_2x_plus_3x_cost  : chain_cost_s 50  id_2x_plus_3x  = 2. Proof. reflexivity. Qed.
Example id_xp1_times_2_cost : chain_cost_s 50  id_xp1_times_2 = 2. Proof. reflexivity. Qed.
Example id_xp1_xp2_cost     : chain_cost_s 100 id_xp1_xp2     = 4. Proof. reflexivity. Qed.
Example id_2xp1_3xp1_cost   : chain_cost_s 100 id_2xp1_3xp1   = 4. Proof. reflexivity. Qed.
