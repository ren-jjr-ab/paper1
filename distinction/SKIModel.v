(* ================================================ *)
(*  SKIModel.v                                       *)
(*                                                   *)
(*  SKI combinator calculus as a framework           *)
(*  instance. Each combinator reduction is one       *)
(*  interact step; storage and flip costs follow     *)
(*  the Computable layer formulas.                   *)
(*                                                   *)
(*  Rules:                                           *)
(*    I x     -> x                                   *)
(*    K x y   -> x                                   *)
(*    S x y z -> (x z) (y z)                         *)
(*                                                   *)
(*  SKI is Turing complete, so halting is            *)
(*  undecidable in general. This instance            *)
(*  implements IterableComputableSig by bounding     *)
(*  reduction with reduce_try under a fuel cap,      *)
(*  and reports a step count only when termination   *)
(*  is witnessed within that budget.                 *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Eqdep_dec.

Require Import Existence.
Require Import Computable.
Require Import Iterable.

(* ================================================ *)
(*  SKI TERMS                                        *)
(* ================================================ *)

Inductive SKITerm : Type :=
  | TS : SKITerm
  | TK : SKITerm
  | TI : SKITerm
  | TApp : SKITerm -> SKITerm -> SKITerm.

Fixpoint term_size (t : SKITerm) : nat :=
  match t with
  | TS | TK | TI => 1
  | TApp l r     => 1 + term_size l + term_size r
  end.

(* Leftmost-outermost single step. *)
Fixpoint reduce_one (t : SKITerm) : option SKITerm :=
  match t with
  | TS | TK | TI => None
  | TApp (TApp (TApp TS x) y) z =>
      Some (TApp (TApp x z) (TApp y z))
  | TApp (TApp TK x) _ =>
      Some x
  | TApp TI x =>
      Some x
  | TApp l r =>
      match reduce_one l with
      | Some l' => Some (TApp l' r)
      | None =>
          match reduce_one r with
          | Some r' => Some (TApp l r')
          | None    => None
          end
      end
  end.

Fixpoint reduce_chain (fuel : nat) (t : SKITerm) : SKITerm * nat :=
  match fuel with
  | 0 => (t, 0)
  | S f =>
      match reduce_one t with
      | None    => (t, 0)
      | Some t' =>
          let '(final, n) := reduce_chain f t' in
          (final, S n)
      end
  end.

Definition chain_cost (fuel : nat) (t : SKITerm) : nat :=
  snd (reduce_chain fuel t).

(* ================================================ *)
(*  CONCRETE REDUCTION EXAMPLES                      *)
(* ================================================ *)

(* SKK x reduces to x in 2 steps: first the S rule
   expands (S K K x) -> (K x (K x)), then the K rule
   contracts (K x (K x)) -> x. *)
Definition skk : SKITerm := TApp (TApp TS TK) TK.

Example skk_ti : chain_cost 10 (TApp skk TI) = 2.
Proof. reflexivity. Qed.

Example skk_tk : chain_cost 10 (TApp skk TK) = 2.
Proof. reflexivity. Qed.

Example skk_ts : chain_cost 10 (TApp skk TS) = 2.
Proof. reflexivity. Qed.

(* K x y -> x in 1 step *)
Example k_apply : chain_cost 10 (TApp (TApp TK TS) TI) = 1.
Proof. reflexivity. Qed.

(* I x -> x in 1 step *)
Example i_apply : chain_cost 10 (TApp TI TS) = 1.
Proof. reflexivity. Qed.

(* ================================================ *)
(*  FRAMEWORK INSTANCE                               *)
(* ================================================ *)

Fixpoint ski_eqb (a b : SKITerm) : bool :=
  match a, b with
  | TS, TS | TK, TK | TI, TI => true
  | TApp a1 a2, TApp b1 b2 => andb (ski_eqb a1 b1) (ski_eqb a2 b2)
  | _, _ => false
  end.

Fixpoint ski_eq_dec (a b : SKITerm) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Inductive SKIEnt : Type :=
  | SKINormal  : nat -> SKITerm -> nat -> nat -> SKIEnt
    (* dim, term, storage, flip *)
  | SKIFrozen  : nat -> nat -> nat -> SKIEnt -> SKIEnt.

Fixpoint ski_dim (x : SKIEnt) : nat :=
  match x with
  | SKINormal d _ _ _ => d
  | SKIFrozen d _ _ _ => d
  end.

Fixpoint ski_info (x : SKIEnt) : nat :=
  match x with
  | SKINormal _ t _ _    => term_size t
  | SKIFrozen _ _ _ inner => ski_info inner
  end.

Fixpoint ski_stor (x : SKIEnt) : nat :=
  match x with
  | SKINormal _ _ s _ => s
  | SKIFrozen _ s _ _ => s
  end.

Fixpoint ski_flip (x : SKIEnt) : nat :=
  match x with
  | SKINormal _ _ _ f => f
  | SKIFrozen _ _ f _ => f
  end.

Definition dim_as_entity (d : nat) : SKIEnt := SKINormal d TI 0 0.

(* One step: applies reduce_one once when the term
   is reducible, or leaves the term unchanged when
   it is already in normal form. Charges storage =
   old term_size and flip = max 1 (size growth). *)
Definition ski_step (e : SKIEnt) (d : nat) : SKIEnt :=
  match e with
  | SKINormal _ t s f =>
      let new_t :=
        match reduce_one t with
        | Some t' => t'
        | None    => t
        end in
      SKINormal d new_t
        (s + term_size t)
        (f + Nat.max 1 (term_size new_t - term_size t))
  | SKIFrozen _ s f inner =>
      SKIFrozen d (s + ski_info inner) (f + 1) inner
  end.

Fixpoint ski_interact_at (x : SKIEnt) (d : nat) : SKIEnt :=
  match x with
  | SKINormal src_d _ _ _ =>
      if Nat.eq_dec src_d d then x else ski_step x d
  | SKIFrozen src_d _ _ _ =>
      if Nat.eq_dec src_d d then x else ski_step x d
  end.

Lemma ski_interact_at_dim : forall x d, ski_dim (ski_interact_at x d) = d.
Proof.
  induction x as [d0 t s f | d0 s f inner IH]; intro d; simpl.
  - destruct (Nat.eq_dec d0 d); simpl; congruence.
  - destruct (Nat.eq_dec d0 d); simpl; congruence.
Qed.

Lemma ski_interact_at_self : forall x, ski_interact_at x (ski_dim x) = x.
Proof.
  induction x as [d t s f | d s f inner IH]; simpl.
  - destruct (Nat.eq_dec d d); [reflexivity | contradiction].
  - destruct (Nat.eq_dec d d); [reflexivity | contradiction].
Qed.

Definition ski_freeze (e : SKIEnt) : SKIEnt := SKIFrozen (ski_dim e) 0 0 e.

Lemma ski_freeze_injective :
  forall a b, ski_freeze a = ski_freeze b -> a = b.
Proof. intros. unfold ski_freeze in H. inversion H. reflexivity. Qed.

(* ================================================ *)
(*  BOUNDED REDUCTION — for Iterable layer           *)
(*                                                   *)
(*  reduce_try runs reduce_one up to `fuel` times.   *)
(*  If the term reaches normal form within fuel,     *)
(*  it returns Some (final, exact_step_count);       *)
(*  otherwise it returns None.                       *)
(*                                                   *)
(*  This is the basis for ski_remaining: a term      *)
(*  reports Some n when termination is witnessed     *)
(*  inside the fuel budget, and None otherwise.      *)
(* ================================================ *)

Definition ski_fuel_cap : nat := 200.

Fixpoint reduce_try (fuel : nat) (t : SKITerm) : option (SKITerm * nat) :=
  match fuel with
  | 0 =>
      match reduce_one t with
      | None   => Some (t, 0)
      | Some _ => None
      end
  | S f =>
      match reduce_one t with
      | None    => Some (t, 0)
      | Some t' =>
          match reduce_try f t' with
          | Some (final, n) => Some (final, S n)
          | None            => None
          end
      end
  end.

Lemma reduce_try_unfold_S :
  forall f t, reduce_try (S f) t =
    match reduce_one t with
    | None => Some (t, 0)
    | Some t' =>
        match reduce_try f t' with
        | Some (final, n) => Some (final, S n)
        | None            => None
        end
    end.
Proof. intros. reflexivity. Qed.

Lemma reduce_try_monotone :
  forall f t r,
    reduce_try f t = Some r ->
    reduce_try (S f) t = Some r.
Proof.
  induction f as [|f' IH]; intros t r H.
  - simpl in H.
    destruct (reduce_one t) as [t'|] eqn:Ht; [discriminate |].
    inversion H; subst.
    rewrite reduce_try_unfold_S. rewrite Ht. reflexivity.
  - rewrite reduce_try_unfold_S in H.
    destruct (reduce_one t) as [t'|] eqn:Ht.
    + destruct (reduce_try f' t') as [p|] eqn:Htt; [|discriminate].
      specialize (IH t' p Htt).
      rewrite reduce_try_unfold_S. rewrite Ht. rewrite IH.
      destruct p. exact H.
    + inversion H; subst.
      rewrite reduce_try_unfold_S. rewrite Ht. reflexivity.
Qed.

Lemma reduce_try_step :
  forall fuel t t' final k,
    reduce_one t = Some t' ->
    reduce_try fuel t = Some (final, S k) ->
    reduce_try fuel t' = Some (final, k).
Proof.
  intros [|f] t t' final k Hred Htry.
  - simpl in Htry. rewrite Hred in Htry. discriminate.
  - rewrite reduce_try_unfold_S in Htry. rewrite Hred in Htry.
    destruct (reduce_try f t') as [p|] eqn:Hrec; [|discriminate].
    destruct p as [x n].
    inversion Htry; subst.
    apply reduce_try_monotone. exact Hrec.
Qed.

Lemma reduce_try_normal :
  forall fuel t, reduce_one t = None -> reduce_try fuel t = Some (t, 0).
Proof.
  intros [|f] t Hred; simpl; rewrite Hred; reflexivity.
Qed.

Lemma reduce_try_some_positive :
  forall fuel t t' final k,
    reduce_one t = Some t' ->
    reduce_try fuel t = Some (final, k) ->
    k > 0.
Proof.
  intros [|f] t t' final k Hred Htry.
  - simpl in Htry. rewrite Hred in Htry. discriminate.
  - rewrite reduce_try_unfold_S in Htry. rewrite Hred in Htry.
    destruct (reduce_try f t') as [p|] eqn:Hrec; [|discriminate].
    destruct p as [x n]. inversion Htry. lia.
Qed.

Definition ski_term_remaining (t : SKITerm) : option nat :=
  match reduce_try ski_fuel_cap t with
  | Some (_, n) => Some n
  | None        => None
  end.

Fixpoint ski_remaining_fn (e : SKIEnt) : option nat :=
  match e with
  | SKINormal _ t _ _   => ski_term_remaining t
  | SKIFrozen _ _ _ _   => Some 0
  end.

Module SKIComputable <: IterableComputableSig.

  Definition Entity : Type := SKIEnt.

  Definition interact (a b : Entity) : Entity :=
    ski_interact_at a (ski_dim b).

  Theorem interact_self : forall a : Entity, interact a a = a.
  Proof. intros. apply ski_interact_at_self. Qed.

  Fixpoint skient_eq_dec (a b : SKIEnt) : {a = b} + {a <> b}.
  Proof.
    refine (
      match a, b with
      | SKINormal d1 t1 s1 f1, SKINormal d2 t2 s2 f2 => _
      | SKIFrozen d1 s1 f1 i1, SKIFrozen d2 s2 f2 i2 => _
      | _, _ => right _
      end); try (intro H; inversion H).
    - destruct (Nat.eq_dec d1 d2); [| right; intro H; inversion H; contradiction].
      destruct (ski_eq_dec t1 t2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec s1 s2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec f1 f2); [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
    - destruct (Nat.eq_dec d1 d2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec s1 s2); [| right; intro H; inversion H; contradiction].
      destruct (Nat.eq_dec f1 f2); [| right; intro H; inversion H; contradiction].
      destruct (skient_eq_dec i1 i2); [| right; intro H; inversion H; contradiction].
      left. subst. reflexivity.
  Defined.

  Theorem interact_decidable :
    forall a b c : Entity,
      {interact a c = interact b c} + {interact a c <> interact b c}.
  Proof. intros. apply skient_eq_dec. Qed.

  Theorem existence : exists a b : Entity, a <> b.
  Proof.
    exists (SKINormal 0 TI 0 0), (SKINormal 1 TI 0 0).
    intro H. inversion H.
  Qed.

  Theorem interact_with :
    forall a : Entity, exists b, interact a b <> a.
  Proof.
    intros a. exists (dim_as_entity (S (ski_dim a))).
    unfold interact, dim_as_entity. simpl ski_dim.
    intro H.
    assert (Hd : ski_dim (ski_interact_at a (S (ski_dim a))) = S (ski_dim a)).
    { apply ski_interact_at_dim. }
    rewrite H in Hd. lia.
  Qed.

  Definition convention_eq : Entity -> Entity -> Prop := fun _ _ => False.

  Theorem convention_not_derivable :
    forall a b, convention_eq a b ->
    forall c, interact a c <> interact b c.
  Proof. intros a b H. exfalso. exact H. Qed.

  Definition info_size (e : Entity) : nat := ski_info e.
  Definition storage_cost (e : Entity) : nat := ski_stor e.
  Definition flip_cost (e : Entity) : nat := ski_flip e.

  Lemma ski_interact_at_normal_non_id :
    forall d0 t s f d,
      d0 <> d ->
      ski_interact_at (SKINormal d0 t s f) d = ski_step (SKINormal d0 t s f) d.
  Proof.
    intros. simpl. destruct (Nat.eq_dec d0 d); [contradiction | reflexivity].
  Qed.

  Lemma ski_interact_at_frozen_non_id :
    forall d0 s f inner d,
      d0 <> d ->
      ski_interact_at (SKIFrozen d0 s f inner) d = ski_step (SKIFrozen d0 s f inner) d.
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
    induction a as [d0 t s f | d0 s f inner _].
    - assert (Hd : d0 <> ski_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ski_dim c)); [reflexivity | contradiction]. }
      rewrite (ski_interact_at_normal_non_id d0 t s f (ski_dim c) Hd).
      simpl. reflexivity.
    - assert (Hd : d0 <> ski_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ski_dim c)); [reflexivity | contradiction]. }
      rewrite (ski_interact_at_frozen_non_id d0 s f inner (ski_dim c) Hd).
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
    induction a as [d0 t s f | d0 s f inner _].
    - assert (Hd : d0 <> ski_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ski_dim c)); [reflexivity | contradiction]. }
      rewrite (ski_interact_at_normal_non_id d0 t s f (ski_dim c) Hd).
      simpl. destruct (reduce_one t) as [t'|]; simpl; reflexivity.
    - assert (Hd : d0 <> ski_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ski_dim c)); [reflexivity | contradiction]. }
      rewrite (ski_interact_at_frozen_non_id d0 s f inner (ski_dim c) Hd).
      simpl.
      assert (H0 : ski_info inner - ski_info inner = 0) by lia.
      rewrite H0. simpl. reflexivity.
  Qed.

  (* ---- Iterable layer ---- *)

  Definition remaining (e : Entity) : option nat := ski_remaining_fn e.

  Theorem project_decrements_remaining :
    forall (a c : Entity) (n : nat),
      interact a c <> a ->
      remaining a = Some n ->
      remaining (interact a c) = Some (n - 1).
  Proof.
    intros a c n Hne Hrem.
    unfold remaining, interact in *.
    induction a as [d0 t s f | d0 s f inner _].
    - assert (Hd : d0 <> ski_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ski_dim c)); [reflexivity | contradiction]. }
      rewrite (ski_interact_at_normal_non_id d0 t s f (ski_dim c) Hd).
      simpl in Hrem |- *. unfold ski_term_remaining in *.
      destruct (reduce_one t) as [t'|] eqn:Ht.
      + destruct (reduce_try ski_fuel_cap t) as [p|] eqn:Htry; [|discriminate].
        destruct p as [final k].
        inversion Hrem as [Hk]. clear Hrem.
        pose proof (reduce_try_some_positive ski_fuel_cap t t' final k Ht Htry) as Hpos.
        destruct k as [|k']; [lia |].
        pose proof (reduce_try_step ski_fuel_cap t t' final k' Ht Htry) as Htr'.
        rewrite Htr'. f_equal. lia.
      + rewrite (reduce_try_normal ski_fuel_cap t Ht) in Hrem.
        inversion Hrem. subst n.
        rewrite (reduce_try_normal ski_fuel_cap t Ht). reflexivity.
    - assert (Hd : d0 <> ski_dim c).
      { intro Heq. apply Hne. simpl.
        destruct (Nat.eq_dec d0 (ski_dim c)); [reflexivity | contradiction]. }
      rewrite (ski_interact_at_frozen_non_id d0 s f inner (ski_dim c) Hd).
      simpl in Hrem |- *.
      inversion Hrem. reflexivity.
  Qed.

  Theorem done_stays_done :
    forall (a c : Entity),
      remaining a = Some 0 ->
      remaining (interact a c) = Some 0.
  Proof.
    intros a c Hrem.
    unfold remaining, interact in *.
    induction a as [d0 t s f | d0 s f inner _].
    - simpl in Hrem |- *.
      destruct (Nat.eq_dec d0 (ski_dim c)) as [Heq | Hne]; simpl.
      + exact Hrem.
      + unfold ski_term_remaining in *.
        destruct (reduce_one t) as [t'|] eqn:Ht.
        * destruct (reduce_try ski_fuel_cap t) as [p|] eqn:Htry; [|discriminate].
          destruct p as [final k].
          pose proof (reduce_try_some_positive ski_fuel_cap t t' final k Ht Htry) as Hpos.
          inversion Hrem. lia.
        * rewrite (reduce_try_normal ski_fuel_cap t Ht). reflexivity.
    - simpl. destruct (Nat.eq_dec d0 (ski_dim c)); reflexivity.
  Qed.

End SKIComputable.

(* ================================================ *)
(*  INSTANCE-INTERNAL FREEZE                         *)
(* ================================================ *)

Module SKICT := ComputableExistenceTheory SKIComputable.
Import SKIComputable SKICT.

Definition freeze (e : Entity) : Entity := ski_freeze e.

Definition is_frozen (a : Entity) : Prop :=
  exists b, a = freeze b.

Theorem freeze_injective :
  forall a b, freeze a = freeze b -> a = b.
Proof. exact ski_freeze_injective. Qed.

Theorem freeze_preserves_existence :
  forall (a b c : Entity),
    is_frozen a -> is_frozen b ->
    interact a c = interact b c -> a = b.
Proof.
  intros a b c Hfa Hfb Hproj.
  destruct Hfa as [a' Ha]. destruct Hfb as [b' Hb].
  unfold freeze, ski_freeze in Ha, Hb. subst a b.
  unfold interact in Hproj. simpl in Hproj.
  destruct (Nat.eq_dec (ski_dim a') (ski_dim c));
    destruct (Nat.eq_dec (ski_dim b') (ski_dim c));
    inversion Hproj; try congruence.
Qed.

(* ================================================ *)
(*  FRAMEWORK COST EXAMPLES                          *)
(* ================================================ *)

Fixpoint ski_walk (fuel : nat) (e : SKIEnt) : SKIEnt :=
  match fuel with
  | 0 => e
  | S f =>
      match e with
      | SKINormal d t _ _ =>
          match reduce_one t with
          | None   => e
          | Some _ => ski_walk f (ski_step e (S d))
          end
      | _ => e
      end
  end.

Definition ski_init (t : SKITerm) : SKIEnt := SKINormal 0 t 0 0.

(* Framework cost of reducing simple terms to normal form.
   chain length vs (storage, flip):

     term                 | steps | storage | flip
     I TS                 |   1   |    3    |   1
     K TS TI              |   1   |    5    |   1
     SKK TI               |   2   |   14    |   2
     SKK TK               |   2   |   14    |   2

   SKK x costs more than the chain length suggests because
   the intermediate form K x (K x) duplicates x, paying
   storage for a larger state. *)

Example i_apply_cost :
  let e := ski_walk 10 (ski_init (TApp TI TS)) in
  (ski_stor e, ski_flip e) = (3, 1).
Proof. reflexivity. Qed.

Example k_apply_cost :
  let e := ski_walk 10 (ski_init (TApp (TApp TK TS) TI)) in
  (ski_stor e, ski_flip e) = (5, 1).
Proof. reflexivity. Qed.

Example skk_ti_cost :
  let e := ski_walk 10 (ski_init (TApp skk TI)) in
  (ski_stor e, ski_flip e) = (14, 2).
Proof. reflexivity. Qed.

Example skk_tk_cost :
  let e := ski_walk 10 (ski_init (TApp skk TK)) in
  (ski_stor e, ski_flip e) = (14, 2).
Proof. reflexivity. Qed.

(* Omega: (S I I) (S I I) does not halt. Walking 10
   steps does not reach a normal form, and storage / flip
   accumulate without bound as fuel grows. *)
Definition sii : SKITerm := TApp (TApp TS TI) TI.
Definition omega : SKITerm := TApp sii sii.

(* ================================================ *)
(*  HALTS / DIVERGES WITNESSES                       *)
(*                                                   *)
(*  Through the Iterable layer, SKI terms report     *)
(*  their halting status via remaining. The report   *)
(*  is honest: a term yields Some n only when        *)
(*  reduce_try with fuel ski_fuel_cap actually       *)
(*  witnesses termination in n steps, and None       *)
(*  otherwise.                                       *)
(* ================================================ *)

(* Halting terms. *)
Example i_ts_halts : ski_remaining_fn (ski_init (TApp TI TS)) = Some 1.
Proof. reflexivity. Qed.

Example k_ts_ti_halts :
  ski_remaining_fn (ski_init (TApp (TApp TK TS) TI)) = Some 1.
Proof. reflexivity. Qed.

Example skk_ti_halts :
  ski_remaining_fn (ski_init (TApp skk TI)) = Some 2.
Proof. reflexivity. Qed.

(* Omega diverges — ski_fuel_cap = 200 is not enough
   to see it terminate, so remaining = None. *)
Example omega_diverges :
  ski_remaining_fn (ski_init omega) = None.
Proof. reflexivity. Qed.
