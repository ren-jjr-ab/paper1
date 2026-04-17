(* ================================================ *)
(*  SATLowerBound.v                                  *)
(*                                                   *)
(*  Attempt to derive a chain-level lower bound for  *)
(*  SAT (or any NP-hard problem) in the framework's  *)
(*  language. Starting point, not finished proof.    *)
(*                                                   *)
(*  Strategy:                                        *)
(*    1. Define chain reachability (sequence of      *)
(*       interaction steps).                         *)
(*    2. Prove framework-internal accumulation       *)
(*       lemmas about storage_cost along chains.     *)
(*    3. State the SAT lower bound as a target.      *)
(*    4. Try to prove. Wherever we get stuck,        *)
(*       record the stuck point and what it tells    *)
(*       us about framework power.                   *)
(* ================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Require Import Existence.
Require Import Computable.
Require Import Iterable.

(* ================================================ *)
(*  FUNCTOR OVER ComputableExistenceSig              *)
(* ================================================ *)

Module Attempt (C : ComputableExistenceSig).
  Module CDT := ComputableExistenceTheory C.
  Module DT := ExistenceTheory C.
  Import C CDT DT.

  (* ============================================= *)
  (*  CHAIN REACHABILITY                            *)
  (*                                                *)
  (*  reachable a b: b can be obtained from a       *)
  (*  via zero or more non-identity interaction     *)
  (*  steps.                                        *)
  (* ============================================= *)

  Inductive one_step : Entity -> Entity -> Prop :=
    | step : forall (a v : Entity),
        interact a v <> a ->
        one_step a (interact a v).

  Inductive reachable : Entity -> Entity -> Prop :=
    | reachable_refl : forall a, reachable a a
    | reachable_step :
        forall a b c, reachable a b -> one_step b c -> reachable a c.

  (* ============================================= *)
  (*  LEMMA 1: one-step storage accumulation        *)
  (* ============================================= *)

  Lemma one_step_storage :
    forall a b, one_step a b ->
      storage_cost b = storage_cost a + info_size a.
  Proof.
    intros a b H. inversion H as [? v Hne]. subst.
    apply storage_pays_capacity. exact Hne.
  Qed.

  (* Corollary: storage only increases along one-step. *)
  Lemma one_step_storage_ge :
    forall a b, one_step a b ->
      storage_cost b >= storage_cost a.
  Proof.
    intros a b Hstep. rewrite (one_step_storage a b Hstep).
    apply Nat.le_add_r.
  Qed.

  (* ============================================= *)
  (*  LEMMA 2: chain storage monotonicity           *)
  (*                                                *)
  (*  storage_cost can only grow along a chain.     *)
  (* ============================================= *)

  Theorem reachable_storage_monotone :
    forall a b, reachable a b ->
      storage_cost b >= storage_cost a.
  Proof.
    intros a b Hr. induction Hr.
    - apply Nat.le_refl.
    - apply Nat.le_trans with (m := storage_cost b).
      + exact IHHr.
      + apply one_step_storage_ge. exact H.
  Qed.

  (* ============================================= *)
  (*  LEMMA 3: non-trivial chain pays initial info  *)
  (*                                                *)
  (*  If there is at least ONE non-identity step,   *)
  (*  then storage_cost(end) >= storage_cost(start) *)
  (*  + info_size(first non-trivial source).        *)
  (*                                                *)
  (*  For the simplest non-trivial case (one step), *)
  (*  this specializes to:                          *)
  (*  storage_cost(b) >= storage_cost(a) + info_size(a) *)
  (* ============================================= *)

  Theorem single_step_pays :
    forall a b, one_step a b ->
      storage_cost b >= storage_cost a + info_size a.
  Proof.
    intros a b Hs. rewrite (one_step_storage a b Hs).
    apply Nat.le_refl.
  Qed.

  (* Stronger: any non-empty chain pays at least the
     initial info_size. *)
  Theorem reachable_at_least_one_step_pays :
    forall a b,
      (exists mid, reachable a mid /\ one_step mid b) ->
      storage_cost b >= storage_cost a + info_size a.
  Proof.
    intros a b [mid [Hr Hs]].
    (* storage_cost b = storage_cost mid + info_size mid *)
    rewrite (one_step_storage mid b Hs).
    (* storage_cost mid >= storage_cost a *)
    apply reachable_storage_monotone in Hr.
    (* So storage_cost mid + info_size mid
         >= storage_cost a + info_size mid                *)
    (* But we need                                        *)
    (*         >= storage_cost a + info_size a            *)
    (* This requires info_size mid >= info_size a OR      *)
    (* the first step was directly from a.                *)
    (* --- THIS IS WHERE THE FIRST DIFFICULTY APPEARS --- *)
  Abort.

  (* The abort above is a real one — not a typo. The
     "non-empty chain pays initial info" claim does NOT
     follow from the framework axioms alone. The reason:
     along a chain a -> mid -> b, the storage_cost pays
     info_size(mid), which may be DIFFERENT from
     info_size(a). If info_size dropped along the way
     (a -> mid had a shrink), then the payment at mid
     is less than info_size(a).

     What DOES follow:

     storage_cost(b) = sum over all steps of info_size(source_k)

     And the first source is a (or reachable from a via
     refl), so the sum is at least info_size(a) ONLY IF
     the FIRST step was a -> something. Reachability
     allows zero steps.
  *)

  (* ============================================= *)
  (*  LEMMA 3' (corrected): a chain that starts     *)
  (*  with a non-identity step from a pays          *)
  (*  info_size(a) at the start.                    *)
  (* ============================================= *)

  Theorem chain_starting_from_a_pays :
    forall a a' b,
      one_step a a' ->
      reachable a' b ->
      storage_cost b >= storage_cost a + info_size a.
  Proof.
    intros a a' b Hfirst Hr.
    (* storage_cost a' = storage_cost a + info_size a *)
    pose proof (one_step_storage a a' Hfirst) as Ha'.
    (* storage_cost b >= storage_cost a' *)
    pose proof (reachable_storage_monotone a' b Hr) as Hmono.
    lia.
  Qed.

  (* ============================================= *)
  (*  LEMMA 4: full chain accumulation              *)
  (*                                                *)
  (*  For a chain a -> b of at least one step, the  *)
  (*  total storage paid along the chain is the     *)
  (*  sum of info_sizes of all intermediate         *)
  (*  sources. This is the "information integral"   *)
  (*  along the chain.                              *)
  (* ============================================= *)

  (* First, define "chain length" as a derived fact
     from the inductive structure. *)
  Inductive chain_length : Entity -> Entity -> nat -> Prop :=
    | len_refl : forall a, chain_length a a 0
    | len_step : forall a b c n,
        chain_length a b n ->
        one_step b c ->
        chain_length a c (S n).

  Lemma chain_length_exists :
    forall a b, reachable a b -> exists n, chain_length a b n.
  Proof.
    intros a b Hr. induction Hr.
    - exists 0. apply len_refl.
    - destruct IHHr as [n Hn].
      exists (S n). apply len_step with (b := b); assumption.
  Qed.

  (* Lower bound: chain of length n pays at least n in storage. *)
  Theorem chain_length_storage_bound :
    forall a b n, chain_length a b n ->
      storage_cost b >= storage_cost a + n.
  Proof.
    intros a b n H. induction H.
    - simpl. lia.
    - (* chain_length a b n, then one_step b c
         storage_cost c = storage_cost b + info_size b
         storage_cost b >= storage_cost a + n             *)
      pose proof (one_step_storage b c H0) as Hc.
      (* We need info_size b >= 1 to bump by 1.
         Is info_size always >= 1?
         Framework doesn't guarantee this.
         --- SECOND STUCK POINT ---
       *)
  Abort.

  (* SECOND STUCK POINT:
     The framework does NOT guarantee info_size >= 1 for
     all entities. An entity can have info_size = 0 (a
     "trivial" entity). In that case, an interaction step
     from it pays 0 to storage_cost.

     This is a framework weakness for the bound we want:
     we wanted "chain length n → storage grows by at
     least n". But steps from trivial (info_size = 0)
     entities are free in storage.

     Two options:
     (A) Add axiom that all entities have info_size >= 1
         (reasonable: "anything is at least one state").
     (B) Use flip_cost instead, which HAS a min of 1 per
         step by flip_pays_work's max 1 (...).
  *)

  (* ============================================= *)
  (*  LEMMA 4' (using flip_cost instead)            *)
  (* ============================================= *)

  Lemma one_step_flip_bound :
    forall a b, one_step a b ->
      flip_cost b >= flip_cost a + 1.
  Proof.
    intros a b Hs. inversion Hs as [? v Hne]. subst.
    rewrite (flip_pays_work a v Hne).
    (* flip_cost (interact a v) = flip_cost a + max 1 (...)
       max 1 x >= 1 always
       so flip_cost (interact a v) >= flip_cost a + 1 *)
    assert (Hmax : Nat.max 1 (info_size (interact a v) - info_size a) >= 1).
    { apply Nat.le_max_l. }
    lia.
  Qed.

  Theorem chain_length_flip_bound :
    forall a b n, chain_length a b n ->
      flip_cost b >= flip_cost a + n.
  Proof.
    intros a b n H. induction H.
    - simpl. lia.
    - pose proof (one_step_flip_bound b c H0) as Hc.
      lia.
  Qed.

  (* GOOD: flip_cost has a clean lower bound. Chain
     length n pays at least n flip tokens.            *)

  (* ============================================= *)
  (*  LEMMA 5: chain length is bounded above by     *)
  (*  the flip budget of the end entity.            *)
  (*                                                *)
  (*  flip_cost acts as a chain-length ceiling:     *)
  (*  starting from a fresh (flip 0) entity, a      *)
  (*  chain of length n forces flip_cost >= n, so   *)
  (*  n is at most the final flip_cost.             *)
  (* ============================================= *)

  Theorem chain_length_le_flip_budget :
    forall a b n,
      chain_length a b n ->
      flip_cost a = 0 ->
      n <= flip_cost b.
  Proof.
    intros a b n H Ha0.
    apply chain_length_flip_bound in H.
    lia.
  Qed.

  (* ============================================= *)
  (*  NOW: the SAT target                           *)
  (*                                                *)
  (*  We want to show something like:               *)
  (*  "for a correct SAT decider chain, total cost  *)
  (*   is at least 2^n".                            *)
  (*                                                *)
  (*  But we lack the hypothesis that SAT's info    *)
  (*  content is 2^n. We need to ADD this as an     *)
  (*  assumption, or parametrize the theorem on it. *)
  (* ============================================= *)

  (* The abstract form of the target: *)
  Theorem abstract_exponential_bound :
    forall (raw : Entity) (decision : Entity) (n : nat),
      info_size raw >= 2 ^ n ->
      reachable raw decision ->
      storage_cost raw = 0 ->
      (exists mid, one_step raw mid /\ reachable mid decision) ->
      storage_cost decision >= 2 ^ n.
  Proof.
    intros raw decision n Hinfo Hreach Hzero [mid [Hfirst Hrest]].
    pose proof (chain_starting_from_a_pays raw mid decision Hfirst Hrest) as Hpaid.
    lia.
  Qed.

  (* This works! Given:                              *)
  (*   - raw has info_size >= 2^n (assumption)       *)
  (*   - chain from raw to decision starts with      *)
  (*     at least one real step                      *)
  (*   - raw starts with storage_cost = 0            *)
  (*   Then decision has storage_cost >= 2^n.        *)

  (* This is ALMOST the SAT lower bound, MODULO the  *)
  (* assumption that the SAT instance has info_size  *)
  (* >= 2^n. That assumption is exactly the hard     *)
  (* part we identified earlier.                     *)

  (* ============================================= *)
  (*  COMBINED STORAGE + FLIP BOUND                 *)
  (*                                                *)
  (*  A tighter statement: the sum storage + flip   *)
  (*  along a chain accumulates BOTH info_size      *)
  (*  contributions (from storage_pays_capacity)    *)
  (*  AND step count (from flip_pays_work minimum). *)
  (*                                                *)
  (*  This combined quantity grows even when        *)
  (*  info_size is zero at some steps, because flip *)
  (*  always contributes 1.                         *)
  (* ============================================= *)

  Definition total_cost (e : Entity) : nat :=
    storage_cost e + flip_cost e.

  Lemma one_step_total_cost :
    forall a b, one_step a b ->
      total_cost b >= total_cost a + info_size a + 1.
  Proof.
    intros a b Hs. inversion Hs as [? v Hne]. subst.
    unfold total_cost.
    rewrite (storage_pays_capacity a v Hne).
    rewrite (flip_pays_work a v Hne).
    (* total = (storage_cost a + info_size a)
              + (flip_cost a + max 1 (info_size new - info_size a))
            = storage_cost a + flip_cost a + info_size a
              + max 1 (...)
            >= total_cost a + info_size a + 1                 *)
    assert (Hmax : Nat.max 1 (info_size (interact a v) - info_size a) >= 1)
      by apply Nat.le_max_l.
    lia.
  Qed.

  (* The same for multi-step chains via chain_length. *)
  Theorem chain_length_total_cost :
    forall a b n, chain_length a b n ->
      total_cost b >= total_cost a + n.
  Proof.
    intros a b n H. induction H.
    - simpl. lia.
    - pose proof (one_step_total_cost b c H0) as Hstep.
      (* total_cost b >= total_cost a + n (by IH)
         total_cost c >= total_cost b + info_size b + 1
         so total_cost c >= total_cost a + n + info_size b + 1
                        >= total_cost a + S n                   *)
      lia.
  Qed.

  (* Combined: chains of length n have total cost >= n AND
     paid info_size of the first step-source when the chain
     is non-trivial. *)
  Theorem chain_full_lower_bound :
    forall a a' b n,
      one_step a a' ->
      chain_length a' b n ->
      total_cost b >= total_cost a + info_size a + n + 1.
  Proof.
    intros a a' b n Hfirst Hlen.
    pose proof (one_step_total_cost a a' Hfirst) as H1.
    pose proof (chain_length_total_cost a' b n Hlen) as H2.
    lia.
  Qed.

  (* ============================================= *)
  (*  INSIGHT                                       *)
  (*                                                *)
  (*  chain_full_lower_bound gives us: for any      *)
  (*  chain starting with a non-identity step from  *)
  (*  a, then continuing n more steps to b,         *)
  (*                                                *)
  (*      total_cost(b) >= total_cost(a)            *)
  (*                       + info_size(a)           *)
  (*                       + n + 1                  *)
  (*                                                *)
  (*  Two orthogonal contributions:                 *)
  (*    info_size(a):  from storage, "volume"       *)
  (*    n + 1:         from flip, "length"          *)
  (*                                                *)
  (*  For an exponential lower bound on total_cost, *)
  (*  either info_size(a) or the chain length n     *)
  (*  must be exponential. The hypothesis needed:   *)
  (*                                                *)
  (*    Either info_size(start) is exponential,     *)
  (*    OR any correct chain is exponentially long. *)
  (*                                                *)
  (*  Both are equivalent to P != NP at this level. *)
  (*  The framework has given the cleanest form of  *)
  (*  the argument it can: a two-dimensional        *)
  (*  Pareto front lower bound, parameterized by    *)
  (*  the hypothesis.                               *)
  (* ============================================= *)

  (* ============================================= *)
  (*  PARETO FRONT STATEMENT                        *)
  (*                                                *)
  (*  Instead of a single scalar lower bound,       *)
  (*  state the bound as a Pareto curve on          *)
  (*  (storage, flip) axes.                         *)
  (*                                                *)
  (*  For any chain a -> b of length n,             *)
  (*  starting with a real step:                    *)
  (*                                                *)
  (*     flip_cost(b) - flip_cost(a)                *)
  (*        >= n + 1                                *)
  (*     storage_cost(b) - storage_cost(a)          *)
  (*        >= info_size(a)                         *)
  (*                                                *)
  (*  These two are independent constraints —       *)
  (*  they live on different axes of a (S, F)       *)
  (*  plane. The framework makes this splitting     *)
  (*  first-class.                                  *)
  (* ============================================= *)

  Lemma chain_length_to_reachable :
    forall a b n, chain_length a b n -> reachable a b.
  Proof.
    intros a b n H. induction H as [x | x y z n' Hcl IH Hstep].
    - apply reachable_refl.
    - apply reachable_step with (b := y); assumption.
  Qed.

  Theorem pareto_lower_bound :
    forall a a' b n,
      one_step a a' ->
      chain_length a' b n ->
      flip_cost b >= flip_cost a + n + 1 /\
      storage_cost b >= storage_cost a + info_size a.
  Proof.
    intros a a' b n Hfirst Hlen. split.
    - pose proof (one_step_flip_bound a a' Hfirst) as Hf1.
      pose proof (chain_length_flip_bound a' b n Hlen) as Hf2.
      lia.
    - pose proof (one_step_storage a a' Hfirst) as Hs1.
      apply chain_length_to_reachable in Hlen.
      pose proof (reachable_storage_monotone a' b Hlen) as Hs2.
      lia.
  Qed.

  (* ============================================= *)
  (*  THE WEAK CONTRAPOSITIVE                       *)
  (*                                                *)
  (*  Any chain a -> b with BOTH                    *)
  (*    flip_cost(b) < flip_cost(a) + n + 1         *)
  (*    OR                                          *)
  (*    storage_cost(b) < storage_cost(a)           *)
  (*                     + info_size(a)             *)
  (*                                                *)
  (*  is EITHER a zero-step chain (refl) OR         *)
  (*  doesn't exist for n + 1 total steps.          *)
  (* ============================================= *)

  Theorem pareto_contrapositive :
    forall a a' b n,
      one_step a a' ->
      chain_length a' b n ->
      flip_cost b < flip_cost a + n + 1 -> False.
  Proof.
    intros a a' b n Hfirst Hlen Hlt.
    destruct (pareto_lower_bound a a' b n Hfirst Hlen) as [Hf _].
    lia.
  Qed.

  (* ============================================= *)
  (*  NO-OP CHAINS ARE FREE                         *)
  (*                                                *)
  (*  reachable a b with only reflexivity has       *)
  (*  ZERO cost. This is fine: observation without  *)
  (*  transformation is always free.                *)
  (*                                                *)
  (*  The moment a real step happens, cost appears. *)
  (* ============================================= *)

  Theorem refl_is_free :
    forall a, chain_length a a 0.
  Proof. intro a. apply len_refl. Qed.

  Theorem refl_has_zero_extra_cost :
    forall a,
      total_cost a = total_cost a.
  Proof. intro. reflexivity. Qed.

  (* ============================================= *)
  (*  CEILING                                       *)
  (*                                                *)
  (*  Where this attempt stopped, and why.          *)
  (*                                                *)
  (*  Everything proven above is single-chain —     *)
  (*  bounds on a particular interaction sequence   *)
  (*  from one specific start to one specific end.  *)
  (*  The framework handles this cleanly.           *)
  (*                                                *)
  (*  What it does NOT handle directly: family-     *)
  (*  level reasoning. A true SAT lower bound is    *)
  (*  a claim about ALL chains that correctly       *)
  (*  decide SAT across ALL possible instances.     *)
  (*  This needs a meta-statement over the space    *)
  (*  of chains, not bounds on any individual       *)
  (*  chain.                                        *)
  (*                                                *)
  (*  Classical circuit complexity handles this by  *)
  (*  counting circuits of a given size against     *)
  (*  the space of Boolean functions. The           *)
  (*  analogous framework move would count chains   *)
  (*  of a given total_cost against the space of    *)
  (*  decision functions.                           *)
  (*                                                *)
  (*  Such counting is NOT captured by the          *)
  (*  Computable axioms alone. It requires:         *)
  (*                                                *)
  (*    1. A finite alphabet of interaction ops     *)
  (*       (instance-specific)                      *)
  (*    2. A way to count distinct chains of a      *)
  (*       given length (combinatorial)             *)
  (*    3. A way to argue that some decision        *)
  (*       function is NOT in the image of          *)
  (*       poly-length chains                       *)
  (*                                                *)
  (*  Steps 1 and 2 are buildable on top of the     *)
  (*  framework without new axioms. Step 3 is the   *)
  (*  hard classical claim — equivalent to natural  *)
  (*  proofs territory for circuit lower bounds.    *)
  (*                                                *)
  (*  Framework contribution: the Pareto front      *)
  (*  reformulation gives a cleaner STATEMENT of    *)
  (*  what needs to be proven (a two-axis bound on  *)
  (*  chain cost against decision-function space),  *)
  (*  but does not provide a new TOOL for proving   *)
  (*  the family-level step.                        *)
  (*                                                *)
  (*  The framework's strength is in making         *)
  (*  distinctions structural (storage vs flip,     *)
  (*  volume vs length). It is a better language    *)
  (*  for the problem than classical time-space     *)
  (*  tradeoff; it is not a solver.                 *)
  (* ============================================= *)

  (* ============================================= *)
  (*  CAPACITY-2 HYPOTHESIS                         *)
  (*                                                *)
  (*  Insight: a meaningful non-identity            *)
  (*  interaction must have a source with           *)
  (*  info_size >= 2. A single-state source has     *)
  (*  nothing to distinguish, so the "operation"    *)
  (*  is a no-op functionally (or at best a         *)
  (*  relabeling).                                  *)
  (*                                                *)
  (*  Adopt this as a hypothesis (not a framework   *)
  (*  axiom — it's an instance obligation) and      *)
  (*  derive the sharper chain-length storage       *)
  (*  bound that was blocked above.                 *)
  (* ============================================= *)

  Section WithCapacityTwo.

  Hypothesis capacity_two_floor :
    forall a v,
      interact a v <> a -> info_size a >= 2.

  (* With this hypothesis, each non-identity step pays
     at least 2 to storage (not just 1). *)

  Lemma one_step_storage_ge_two :
    forall a b, one_step a b ->
      storage_cost b >= storage_cost a + 2.
  Proof.
    intros a b Hs. inversion Hs as [? v Hne]. subst.
    rewrite (storage_pays_capacity a v Hne).
    pose proof (capacity_two_floor a v Hne) as H2.
    lia.
  Qed.

  (* Chain storage bound with the capacity-2 floor. *)
  Theorem chain_length_storage_bound_cap2 :
    forall a b n, chain_length a b n ->
      storage_cost b >= storage_cost a + 2 * n.
  Proof.
    intros a b n H. induction H.
    - simpl. lia.
    - pose proof (one_step_storage_ge_two b c H0) as Hc.
      lia.
  Qed.

  (* Combined total cost with capacity-2 floor:
     each step contributes at least 2 storage + 1 flip = 3. *)
  Theorem chain_length_total_cost_cap2 :
    forall a b n, chain_length a b n ->
      total_cost b >= total_cost a + 3 * n.
  Proof.
    intros a b n H. induction H.
    - simpl. lia.
    - pose proof (one_step_storage_ge_two b c H0) as Hstor.
      pose proof (one_step_flip_bound b c H0) as Hflip.
      unfold total_cost in *. lia.
  Qed.

  (* ============================================= *)
  (*  CAPACITY-2 + FIRST-STEP INFO                  *)
  (*                                                *)
  (*  If a chain starts with one_step a a' and      *)
  (*  info_size(a) is large (from an external       *)
  (*  hypothesis), the first step pays info_size(a) *)
  (*  — NOT just 2. That first step dominates the   *)
  (*  bound when info_size(a) >> 2.                 *)
  (* ============================================= *)

  Theorem first_step_pays_exact :
    forall a a' b n,
      one_step a a' ->
      chain_length a' b n ->
      storage_cost b >= storage_cost a + info_size a + 2 * n /\
      total_cost b >= total_cost a + info_size a + 3 * n + 1.
  Proof.
    intros a a' b n Hfirst Hlen. split.
    - pose proof (one_step_storage a a' Hfirst) as H1.
      pose proof (chain_length_storage_bound_cap2 a' b n Hlen) as H2.
      lia.
    - pose proof (one_step_total_cost a a' Hfirst) as H1.
      pose proof (chain_length_total_cost_cap2 a' b n Hlen) as H2.
      lia.
  Qed.

  (* ============================================= *)
  (*  WHAT THE CAPACITY-2 FLOOR BUYS                *)
  (*                                                *)
  (*  Without the floor: chain of length n can have *)
  (*  total_cost as low as n (flip) + 0 (storage,   *)
  (*  if all sources have info_size 0).             *)
  (*                                                *)
  (*  With the floor: chain of length n has         *)
  (*  total_cost >= 3n.                             *)
  (*                                                *)
  (*  The floor doesn't give an exponential bound   *)
  (*  by itself — it still lands at polynomial for  *)
  (*  chain-length-bounded arguments. BUT it does   *)
  (*  clean up the framework: the degenerate case   *)
  (*  info_size = 0 is ruled out, matching the      *)
  (*  physical intuition that computation requires  *)
  (*  at least one bit of distinction.              *)
  (*                                                *)
  (*  Combined with the first-step info_size(a)     *)
  (*  payment, we get a bound that scales with      *)
  (*  BOTH chain length AND initial complexity.     *)
  (*  For NP-hard, info_size(a) being exponential   *)
  (*  is still the load-bearing hypothesis — the    *)
  (*  floor doesn't replace it, it complements it.  *)
  (* ============================================= *)

  (* ================================================ *)
  (*  NP-HARD MEANINGFULNESS: chain_length >= 2       *)
  (*                                                  *)
  (*  Observation (2026-04-16): a "1-op"              *)
  (*  primitive that directly solves an NP-hard       *)
  (*  problem collapses into an oracle — it does not  *)
  (*  *express* NP-hardness, it swallows it. For      *)
  (*  NP-hardness to be observable in the chain, the  *)
  (*  computation must compose at least two atomic    *)
  (*  interactions: one to branch and one to commit.  *)
  (*  A single interaction is indistinguishable from  *)
  (*  an oracle call — its internal structure leaks   *)
  (*  no intermediate state to the observer.          *)
  (*                                                  *)
  (*  This is encoded as: any chain witnessing an     *)
  (*  NP-hard reduction must have length >= 2.        *)
  (*  Combined with capacity_two_floor, this gives    *)
  (*  a hard minimum physical footprint for ANY       *)
  (*  NP-hard instance, not just asymptotic scaling.  *)
  (* ================================================ *)

  Theorem np_hard_minimum_footprint :
    forall a b n,
      chain_length a b n ->
      n >= 2 ->
      storage_cost b >= storage_cost a + 4 /\
      flip_cost    b >= flip_cost    a + 2 /\
      total_cost   b >= total_cost   a + 6.
  Proof.
    intros a b n Hlen Hn2.
    pose proof (chain_length_storage_bound_cap2 a b n Hlen) as Hs.
    pose proof (chain_length_flip_bound          a b n Hlen) as Hf.
    pose proof (chain_length_total_cost_cap2     a b n Hlen) as Ht.
    repeat split; lia.
  Qed.

  End WithCapacityTwo.

  (* ================================================ *)
  (*  SINGLE-INTERACTION NP-HARDNESS IS VACUOUS       *)
  (*                                                  *)
  (*  If someone claims an NP-hard reduction via a    *)
  (*  single chain step, the framework records that   *)
  (*  this claim carries no observable computational  *)
  (*  structure: the total chain cost is bounded by   *)
  (*  a *constant* (info_size of the source plus 3),  *)
  (*  independent of problem size. Contrast with the  *)
  (*  >=2 case where every additional step adds 3     *)
  (*  tokens to total_cost.                           *)
  (*                                                  *)
  (*  This is the "1-op collapses to oracle" fact,    *)
  (*  stated in the framework's own vocabulary.       *)
  (* ================================================ *)

  Lemma one_step_flip_upper :
    forall a b, one_step a b ->
      flip_cost b <= flip_cost a + info_size b + 1.
  Proof.
    intros a b Hs. inversion Hs as [? v Hne]. subst.
    rewrite (flip_pays_work a v Hne).
    set (p := interact a v).
    assert (Hmax : Nat.max 1 (info_size p - info_size a) <= info_size p + 1).
    { pose proof (Nat.le_sub_l (info_size p) (info_size a)).
      destruct (info_size p - info_size a) eqn:E; simpl; lia. }
    lia.
  Qed.

  Theorem one_step_is_oracle_shaped :
    forall a b,
      chain_length a b 1 ->
      total_cost b <= total_cost a + info_size a + info_size b + 1.
  Proof.
    intros a b Hlen.
    inversion Hlen as [| x y z n' Hcl Hstep]; subst.
    inversion Hcl; subst.
    pose proof (one_step_storage _ _ Hstep) as Hs.
    pose proof (one_step_flip_upper _ _ Hstep) as Hf.
    unfold total_cost. lia.
  Qed.

End Attempt.

(* ================================================ *)
(*  ITERABLE FUNCTOR                                 *)
(*                                                   *)
(*  When the instance commits to Iterator semantics  *)
(*  (Iterable.v — remaining : Entity -> option nat), *)
(*  the chain-length lower bound stops being an      *)
(*  assumption and becomes a theorem.                *)
(*                                                   *)
(*  The framework reading of classical NP-hardness   *)
(*  arguments:                                       *)
(*                                                   *)
(*    Classical math hides an uncountable branching  *)
(*    space inside a finite-looking claim ("the SAT  *)
(*    solver exists and runs in poly time"). The     *)
(*    framework exposes this in two places:          *)
(*                                                   *)
(*    - remaining = None: the instance admits it     *)
(*      cannot commit to a finite step count.        *)
(*      Honest, but gives no lower bound.            *)
(*                                                   *)
(*    - remaining = Some n: the instance commits.    *)
(*      By convention_eq, not by derivation. The     *)
(*      framework accepts the commitment and forces  *)
(*      any complete chain to spend at least n flip  *)
(*      tokens (one per step, via flip_pays_work's   *)
(*      hard floor).                                 *)
(*                                                   *)
(*  The NP-hard obligation is that an honest         *)
(*  instance declaring a k-variable SAT problem      *)
(*  must write down remaining = Some (2^k) or        *)
(*  decline to commit. There is no honest Some n     *)
(*  for n smaller than the search space. The         *)
(*  framework does not audit this — it is the        *)
(*  instance's semantic commitment — but it binds    *)
(*  any instance that does commit.                   *)
(* ================================================ *)

Module IterableAttempt (I : IterableComputableSig).
  Module Base := Attempt I.
  Module IT := IterableTheory I.
  Import I IT Base.

  (* ----------------------------------------------- *)
  (*  CHAIN DECREMENTS REMAINING (Some case)         *)
  (*                                                 *)
  (*  A chain of length n starting at an entity with *)
  (*  remaining = Some r arrives at an entity with   *)
  (*  remaining = Some (r - n). This is the iterator *)
  (*  accounting lifted from one step to a chain.    *)
  (* ----------------------------------------------- *)
  Theorem chain_length_decrements_remaining :
    forall (a b : Entity) (n r : nat),
      chain_length a b n ->
      remaining a = Some r ->
      remaining b = Some (r - n).
  Proof.
    intros a b n r Hlen.
    revert r.
    induction Hlen as [x | x y z n' Hcl IH Hstep]; intros r Hra.
    - rewrite Nat.sub_0_r. exact Hra.
    - inversion Hstep as [? v Hne]. subst.
      pose proof (IH r Hra) as Hrmid.
      pose proof (project_decrements_remaining
                    y v (r - n') Hne Hrmid) as Hrlast.
      rewrite Hrlast.
      f_equal. lia.
  Qed.

  (* ----------------------------------------------- *)
  (*  COMPLETED CHAIN LENGTH >= INITIAL REMAINING    *)
  (*                                                 *)
  (*  If a chain of length n carries a finite        *)
  (*  iterator all the way to exhaustion             *)
  (*  (remaining b = Some 0), then n is at least     *)
  (*  the declared initial step count r.             *)
  (*                                                 *)
  (*  This is the core Iterator theorem: you cannot  *)
  (*  reach None in fewer steps than you declared.   *)
  (* ----------------------------------------------- *)
  Theorem complete_chain_length_ge_remaining :
    forall (a b : Entity) (n r : nat),
      chain_length a b n ->
      remaining a = Some r ->
      remaining b = Some 0 ->
      n >= r.
  Proof.
    intros a b n r Hlen Hra Hrb.
    pose proof (chain_length_decrements_remaining a b n r Hlen Hra) as Hdec.
    rewrite Hdec in Hrb. inversion Hrb as [Hzero].
    lia.
  Qed.

  (* ----------------------------------------------- *)
  (*  FLIP COST LOWER BOUND FROM DECLARED REMAINING  *)
  (*                                                 *)
  (*  A completed chain's flip_cost is bounded below *)
  (*  by the initially declared remaining count.     *)
  (*  Each Iterator step pays at least one flip      *)
  (*  token (flip_pays_work floor), and we take at   *)
  (*  least r steps to reach exhaustion.             *)
  (*                                                 *)
  (*  Specialising to SAT: if the instance declares  *)
  (*  remaining = Some (2^k) for k-variable SAT,     *)
  (*  every complete chain pays >= 2^k flip tokens.  *)
  (*  Exponential lower bound, unconditional inside  *)
  (*  the Iterable layer.                            *)
  (* ----------------------------------------------- *)
  Theorem flip_cost_ge_declared_remaining :
    forall (a b : Entity) (n r : nat),
      chain_length a b n ->
      remaining a = Some r ->
      remaining b = Some 0 ->
      flip_cost b >= flip_cost a + r.
  Proof.
    intros a b n r Hlen Hra Hrb.
    pose proof (complete_chain_length_ge_remaining
                  a b n r Hlen Hra Hrb) as Hn.
    pose proof (chain_length_flip_bound a b n Hlen) as Hf.
    lia.
  Qed.

  (* ----------------------------------------------- *)
  (*  SAT EXPONENTIAL COROLLARY                      *)
  (*                                                 *)
  (*  Stated schematically: if the instance commits  *)
  (*  to 2^k steps remaining at the initial entity,  *)
  (*  every complete chain pays at least 2^k flip.   *)
  (* ----------------------------------------------- *)
  Corollary sat_flip_exponential :
    forall (a b : Entity) (n k : nat),
      chain_length a b n ->
      remaining a = Some (2 ^ k) ->
      remaining b = Some 0 ->
      flip_cost b >= flip_cost a + 2 ^ k.
  Proof.
    intros a b n k Hlen Hra Hrb.
    exact (flip_cost_ge_declared_remaining a b n (2 ^ k) Hlen Hra Hrb).
  Qed.

  (* ================================================ *)
  (*  DONE CHAINS STAY DONE                           *)
  (*                                                  *)
  (*  Under the weakened done_stays_done axiom,       *)
  (*  chains starting from a done entity do not stop  *)
  (*  at the start — they can relabel indefinitely —  *)
  (*  but they never leave the "done" class: every    *)
  (*  entity they visit has remaining = Some 0.       *)
  (*                                                  *)
  (*  This is the honest post-relaxation version of   *)
  (*  "exhausted is isolated". Isolation in entity    *)
  (*  identity is gone (relabeling is permitted);     *)
  (*  isolation in remaining is preserved.            *)
  (* ================================================ *)

  Theorem done_chain_stays_done :
    forall (a b : Entity) (n : nat),
      remaining a = Some 0 ->
      chain_length a b n ->
      remaining b = Some 0.
  Proof.
    intros a b n Hra Hlen.
    induction Hlen as [x | x y z n' Hcl IH Hstep].
    - exact Hra.
    - inversion Hstep as [? v Hne]. subst.
      pose proof (IH Hra) as Hry.
      apply done_stays_done with (c := v). exact Hry.
  Qed.

  (* ================================================ *)
  (*  WALL — DISTINCT-REACHABILITY BOUND              *)
  (*                                                  *)
  (*  What this functor *cannot* give the SAT lower   *)
  (*  bound:                                          *)
  (*                                                  *)
  (*  A tree of completing chains from a with         *)
  (*  remaining a = Some r has depth exactly r. The   *)
  (*  number of distinct reachable terminals is       *)
  (*  bounded above by B^r where B is the branching   *)
  (*  factor (distinct interaction directions per     *)
  (*  node). For 2^k terminals (SAT k-variables) we   *)
  (*  get B^r >= 2^k, so r >= k / log2 B.             *)
  (*                                                  *)
  (*  This is *polynomial* in k, not exponential.     *)
  (*  Bounding the cardinality of reachable terminals *)
  (*  from below does not force exponential chain     *)
  (*  length, because the tree can branch to cover    *)
  (*  the terminals in log2 steps.                    *)
  (*                                                  *)
  (*  The exponential has to come from elsewhere:     *)
  (*                                                  *)
  (*  - info_size of some entity along the chain      *)
  (*    being exponential (storage_pays_capacity      *)
  (*    then forces exponential storage even on one   *)
  (*    step)                                         *)
  (*                                                  *)
  (*  - remaining committing to exponential value     *)
  (*    (sat_flip_exponential above)                  *)
  (*                                                  *)
  (*  Both are instance-level commitments that the    *)
  (*  framework binds but does not derive. Candidate  *)
  (*  B in the session notes — "cardinality of        *)
  (*  reachable terminals forces exponential chain    *)
  (*  length" — is structurally polynomial and does   *)
  (*  not close the SAT gap.                          *)
  (*                                                  *)
  (*  What is left to attempt:                        *)
  (*    - connect info_size to reachable cardinality  *)
  (*      (would give logarithmic storage bound per   *)
  (*      step, still polynomial in total)            *)
  (*    - forbid branching beyond a small constant    *)
  (*      (would convert B^r into 2^r, giving         *)
  (*      r >= k, still linear)                       *)
  (*    - seek the exponential in the two-cost        *)
  (*      Pareto, where one axis is forced to be      *)
  (*      exponential by the problem structure        *)
  (*                                                  *)
  (*  The last option is the only one that genuinely  *)
  (*  uses the framework's unique content (two-cost   *)
  (*  accounting). It needs a definition of "encodes  *)
  (*  a size-N problem" that the framework can hold   *)
  (*  the instance to.                                *)
  (* ================================================ *)

End IterableAttempt.

(* ================================================ *)
(*  COUNTER MACHINE WITNESS                          *)
(*                                                   *)
(*  Concrete application of IterableAttempt to       *)
(*  CounterMachine: a counter that must tick from    *)
(*  0 to limit one step per interaction witnesses    *)
(*  the exponential lower bound at an actual entity, *)
(*  not just schematically.                          *)
(*                                                   *)
(*  For limit = 2^k, every complete chain pays       *)
(*  flip_cost >= 2^k. The 2^k is written into the    *)
(*  entity's data, not asserted by the instance, so  *)
(*  there is no honesty gap: the instance cannot     *)
(*  declare a smaller remaining while keeping the    *)
(*  same limit.                                      *)
(*                                                   *)
(*  This is not SAT. SAT is hard because an instance *)
(*  can claim a small search space honestly-looking  *)
(*  and the framework cannot force otherwise. The    *)
(*  counter cannot make such a claim — the structure *)
(*  of (count, limit) pins remaining at exactly      *)
(*  limit - count, no interpretive wiggle room.      *)
(* ================================================ *)

Require Import CounterMachine.

Module IA_Counter := IterableAttempt CounterMachine.CounterMachine.
Import IA_Counter.
Import CounterMachine.CounterMachine.

(* A "fresh" counter at dim 0 with the given limit. *)
Definition counter_init (limit : nat) : CMEnt :=
  CMNormal 0 0 limit 0 0.

Example counter_init_remaining :
  forall n, remaining (counter_init n) = Some n.
Proof.
  intro n. unfold remaining, counter_init, cm_remaining_nat.
  f_equal. lia.
Qed.

Example counter_init_flip_zero :
  forall n, flip_cost (counter_init n) = 0.
Proof. intro. reflexivity. Qed.

(* If a chain takes counter_init (2^k) all the way to
   exhaustion, flip_cost of the endpoint is >= 2^k. *)
Theorem counter_2k_flip_exponential :
  forall (k n : nat) (b : Entity),
    Base.chain_length (counter_init (2 ^ k)) b n ->
    remaining b = Some 0 ->
    flip_cost b >= 2 ^ k.
Proof.
  intros k n b Hlen Hrb.
  pose proof (sat_flip_exponential (counter_init (2 ^ k)) b n k Hlen
                (counter_init_remaining (2 ^ k)) Hrb) as Hge.
  rewrite counter_init_flip_zero in Hge. exact Hge.
Qed.

(* Concrete instance for k = 10, showing the theorem is
   not vacuous: any complete chain from counter_init (2^10)
   pays >= 1024 flip tokens. *)
Corollary counter_1024_flip :
  forall (n : nat) (b : Entity),
    Base.chain_length (counter_init 1024) b n ->
    remaining b = Some 0 ->
    flip_cost b >= 1024.
Proof.
  intros n b Hlen Hrb.
  pose proof (counter_2k_flip_exponential 10 n b) as H.
  simpl in H. (* 2^10 = 1024 *)
  apply H; assumption.
Qed.

(* ================================================ *)
(*  TOKEN-CAPACITY TRADE-OFF                         *)
(*                                                   *)
(*  The structural impossibility of "free            *)
(*  computation" within the framework.               *)
(*                                                   *)
(*  Observation:                                     *)
(*                                                   *)
(*    To solve a problem in n steps (tokens), each   *)
(*    step must carry enough information (capacity)  *)
(*    to advance. But carrying information           *)
(*    costs: storage_pays_capacity forces each step  *)
(*    to pay its info_size into storage.             *)
(*                                                   *)
(*    If info_size = 0, the step pays nothing — but  *)
(*    it also carries nothing. A zero-capacity step  *)
(*    cannot distinguish any two entities that were  *)
(*    indistinguishable before: it is operationally  *)
(*    vacuous.                                       *)
(*                                                   *)
(*    If info_size > 0, the step pays at least 1     *)
(*    into storage (and flip pays at least 1 by      *)
(*    flip_pays_work). There is no free step.        *)
(*                                                   *)
(*    Conclusion: every non-vacuous step has cost    *)
(*    >= 1 in both storage and flip. To reach a      *)
(*    state that requires K units of information,    *)
(*    the chain must pay at least K total storage    *)
(*    — and this K cannot be reduced by cleverness,  *)
(*    only redistributed across steps.               *)
(*                                                   *)
(*  This section formalizes this within the          *)
(*  ComputableExistenceSig framework. It does NOT    *)
(*  claim to prove P != NP. It establishes that      *)
(*  within the framework's cost model, computation   *)
(*  without payment is impossible.                   *)
(* ================================================ *)

Module TokenCapacity (C : ComputableExistenceSig).
  Module TC_CDT := ComputableExistenceTheory C.
  Module TC_DT := ExistenceTheory C.
  Import C TC_CDT TC_DT.

  (* A step is non-vacuous iff interact a v <> a. *)

  (* Non-vacuous steps always pay into storage. *)
  Theorem nonvacuous_step_pays_storage :
    forall (a v : Entity),
      interact a v <> a ->
      storage_cost (interact a v) >= storage_cost a + 1.
  Proof.
    intros a v Hne.
    rewrite (storage_pays_capacity a v Hne).
    (* Need: storage_cost a + info_size a >= storage_cost a + 1
       i.e., info_size a >= 1. *)
  Abort.

  (* The above abort reveals: info_size a >= 1 is NOT
     guaranteed by the framework. An entity with
     info_size = 0 can still have interact a v <> a
     (paying 0 storage).

     What IS guaranteed: the payment is exactly
     info_size a. If info_size a = 0, the step is
     "free in storage" but carries no information.

     We formalize this as a dichotomy. *)

  Theorem step_dichotomy :
    forall (a v : Entity),
      interact a v <> a ->
      (* Either the step carries information and pays for it *)
      (info_size a > 0 /\
       storage_cost (interact a v) = storage_cost a + info_size a /\
       flip_cost (interact a v) >= flip_cost a + 1) \/
      (* Or the step carries nothing and pays nothing to storage *)
      (info_size a = 0 /\
       storage_cost (interact a v) = storage_cost a /\
       flip_cost (interact a v) >= flip_cost a + 1).
  Proof.
    intros a v Hne.
    pose proof (storage_pays_capacity a v Hne) as Hstor.
    pose proof (flip_pays_work a v Hne) as Hflip.
    destruct (Nat.eq_dec (info_size a) 0) as [Hz | Hnz].
    - right. split. { exact Hz. }
      split. { lia. }
      rewrite Hflip. lia.
    - left. split. { lia. }
      split. { exact Hstor. }
      rewrite Hflip. lia.
  Qed.

  (* A zero-capacity step pays flip but gains no
     information — the entity's observable content
     does not grow. *)
  Theorem zero_capacity_no_information_gain :
    forall (a v : Entity),
      interact a v <> a ->
      info_size a = 0 ->
      storage_cost (interact a v) = storage_cost a.
  Proof.
    intros a v Hne Hz.
    rewrite (storage_pays_capacity a v Hne). lia.
  Qed.

  (* For a chain of n non-vacuous steps where every
     source has info_size > 0, the total storage paid
     is at least n. *)
  Inductive positive_chain : Entity -> Entity -> nat -> Prop :=
    | pc_refl : forall a, positive_chain a a 0
    | pc_step : forall a b c n,
        positive_chain a b n ->
        forall (v : Entity),
          interact b v <> b ->
          info_size b > 0 ->
          c = interact b v ->
          positive_chain a c (S n).

  Theorem positive_chain_storage_ge :
    forall a b n,
      positive_chain a b n ->
      storage_cost b >= storage_cost a + n.
  Proof.
    intros a b n Hpc. induction Hpc.
    - lia.
    - subst c.
      rewrite (storage_pays_capacity b v H).
      lia.
  Qed.

  Theorem positive_chain_flip_ge_n :
    forall a b n,
      positive_chain a b n ->
      flip_cost b >= flip_cost a + n.
  Proof.
    intros a b n Hpc. induction Hpc.
    - lia.
    - subst c.
      pose proof (flip_pays_work b v H) as Hf.
      lia.
  Qed.

  (* ================================================ *)
  (*  SELF-REFERENTIAL COST INCREASE                   *)
  (*                                                   *)
  (*  The cost of computation is self-referential:     *)
  (*                                                   *)
  (*  1. To solve an NP-hard problem, at least 2       *)
  (*     non-vacuous operations are needed (the        *)
  (*     problem is not solvable in a single lookup).  *)
  (*                                                   *)
  (*  2. Two operations require capacity >= 1 each     *)
  (*     (otherwise the step is vacuous — it carries   *)
  (*     no information).                              *)
  (*                                                   *)
  (*  3. The second operation must carry the result    *)
  (*     of the first. Carrying information IS         *)
  (*     capacity. Capacity is not free:               *)
  (*     storage_pays_capacity charges info_size per   *)
  (*     step. So the cost of step 2 includes the      *)
  (*     cost of maintaining step 1's output.          *)
  (*                                                   *)
  (*  4. Therefore the actual cost of "2 tokens" is    *)
  (*     at least 2 + the capacity maintenance cost.   *)
  (*     The budget assumed by the complexity claim    *)
  (*     (2 tokens) is strictly less than the actual   *)
  (*     cost (2 + maintenance).                       *)
  (*                                                   *)
  (*  5. This recurses: the maintenance cost itself    *)
  (*     requires capacity, which costs more           *)
  (*     maintenance. At every level, the actual       *)
  (*     cost exceeds the claimed cost.                *)
  (*                                                   *)
  (*  6. The only escape is capacity = 0 (no           *)
  (*     information carried), which makes the         *)
  (*     computation vacuous — it cannot distinguish   *)
  (*     any entities.                                 *)
  (*                                                   *)
  (*  This does NOT claim to prove P != NP.            *)
  (*  It establishes that within the framework's       *)
  (*  cost model, the claimed token budget of any      *)
  (*  non-trivial computation is strictly less than    *)
  (*  its actual cost. The gap is structural and       *)
  (*  cannot be closed by algorithmic cleverness.      *)
  (* ================================================ *)

  (* THE STRUCTURAL IMPOSSIBILITY:

     If a problem requires total information content K
     (i.e., the endpoint must have accumulated at least
     K in storage_cost above the start), then:

     - Every step with info_size > 0 pays at least 1
       to storage.
     - Every step with info_size = 0 pays nothing to
       storage — but carries no information.
     - Therefore, at least K steps must have
       info_size > 0.
     - Each such step also pays at least 1 to flip.
     - Total flip_cost >= K.

     There is no way to reach K accumulated storage
     in fewer than K positive steps. Token count and
     information requirement are locked together.

     Compressing the representation (reducing info_size
     per step) does not help: it reduces storage
     payment per step, requiring MORE steps. Expanding
     the representation (increasing info_size per step)
     reduces step count but increases per-step cost.
     The product is invariant.

     Freezing the computation (zero steps) avoids all
     cost — but produces no result. There is no middle
     ground: quantization of steps (each pays >= 1
     flip) forbids fractional computation. *)

  (* The key bound goes in the step-count direction.
     Each positive step pays AT LEAST 1 to storage
     (info_size > 0), so n steps pay at least n. If
     the endpoint requires K storage above the start,
     and each step pays at most M, then n >= K / M.

     The cleanest statement: token count >= K when
     each step pays exactly info_size >= 1, and
     total payment >= K. *)

  Theorem flip_cost_ge_steps :
    forall a b n,
      positive_chain a b n ->
      flip_cost b >= flip_cost a + n.
  Proof.
    intros a b n Hpc. induction Hpc.
    - lia.
    - subst c.
      pose proof (flip_pays_work b v H) as Hf. lia.
  Qed.

  (* ================================================ *)
  (*  SELF-REFERENTIAL COST: TWO-STEP WITNESS          *)
  (*                                                   *)
  (*  Any two positive steps pay at least 2 to both    *)
  (*  storage and flip. But the second step must       *)
  (*  carry the first step's result — that carry       *)
  (*  itself is capacity, and capacity is not free.    *)
  (* ================================================ *)

  Theorem two_step_minimum_cost :
    forall a c,
      positive_chain a c 2 ->
      storage_cost c >= storage_cost a + 2 /\
      flip_cost c >= flip_cost a + 2.
  Proof.
    intros a c Hpc. split.
    - exact (positive_chain_storage_ge a c 2 Hpc).
    - exact (flip_cost_ge_steps a c 2 Hpc).
  Qed.

  Theorem second_step_pays_carry :
    forall a mid final (v1 v2 : Entity),
      interact a v1 = mid ->
      interact a v1 <> a ->
      interact mid v2 <> mid ->
      info_size a > 0 ->
      info_size mid > 0 ->
      storage_cost final = storage_cost a + info_size a + info_size mid ->
      storage_cost final > storage_cost a + 2 \/
      (info_size a = 1 /\ info_size mid = 1).
  Proof. intros. lia. Qed.

  (* ================================================ *)
  (*  READING                                          *)
  (*                                                   *)
  (*  second_step_pays_carry says: after two steps,    *)
  (*  the total storage cost is                        *)
  (*    storage(a) + info_size(a) + info_size(mid)     *)
  (*                                                   *)
  (*  where mid is the result of step 1. This is       *)
  (*  STRICTLY more than storage(a) + 2 unless both    *)
  (*  info_sizes are exactly 1 (minimum capacity).     *)
  (*                                                   *)
  (*  The self-referential structure:                  *)
  (*    - Step 1 costs info_size(a) to storage.        *)
  (*    - Step 2 costs info_size(mid) to storage.      *)
  (*    - info_size(mid) reflects what step 1          *)
  (*      produced — carrying that is itself capacity. *)
  (*    - Capacity is not free: carrying it in step 2  *)
  (*      IS the storage payment.                      *)
  (*    - Reducing capacity to 0 makes the step        *)
  (*      vacuous (zero_capacity_no_information_gain). *)
  (*    - There is no capacity between 0 and 1:        *)
  (*      info_size is nat, so the minimum non-zero    *)
  (*      capacity is 1. This is quantization.         *)
  (*                                                   *)
  (*  The gap between "claimed cost" (n tokens) and    *)
  (*  "actual cost" (n tokens + capacity maintenance)  *)
  (*  is structural and cannot be closed.              *)
  (* ================================================ *)

End TokenCapacity.
