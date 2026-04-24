# Existence is difference

An axiom system that separates the single symbol `=` into three relations:
`≡` (native identity), `=` (interaction), `≈` (collapse). Mechanically
verified in Coq, with zero `Admitted`.

- **Paper:** [`paper.typ`](./paper.typ) / `paper.pdf` — core theory, ~12 pages.
- **Mechanization:** 83 `.v` files across four layers, ~22,300 lines of Coq.
- **Demo:** [`scev-demo/`](./scev-demo/) — Rust companion for the
  `lim sin(x)/x` budget experiment (paper §4.1.1).

## Layout

```
framework/   (14)  Primitives, axioms, categorical composition, Ring interface.
existences/  (26)  Concrete Entity types satisfying ExistenceSig or extensions.
results/     (28)  Main theorems and cross-instance mathematics.
tests/       (15)  Functor verification, instance suites, assumption audit.
paper.typ          Typst source for the paper body.
scev-demo/         Rust demo (Section 4.1.1 budget/precision experiment).
```

## Core claim

Three primitives and five axioms generate everything downstream. See
`framework/Existence.v`.

| | |
| --- | --- |
| `Entity : Type` | the sole object type |
| `interact : Entity → Entity → Entity` | binary operation |
| `collapse : Entity → Entity → Prop` | the one named relation |

Axioms: `interact_self`, `entity_eq_dec`, `existence`, `interact_with`,
`interaction_cannot_witness_collapse`.

Every algebraic, set-theoretic, computational, and numeric structure in
`existences/` either directly satisfies `ExistenceSig` or is lifted into
it through a marker-augmented construction. Ring theory, polynomial
rings, Boolean-set rings, and the ℚ→ℝ tower all live inside the
framework on equal footing — the marker pattern mirrors the one
`RationalRep` uses with `CMark`, `CauchyReal` with `CEval`, and
`SymbolicSet` with `SQuery`.

## Observation as primitive

Classical axiomatisations treat observation as pre-axiom — the ability
to inspect a set's elements, a type's terms, or a ring's carrier is
assumed freely and does not appear in any axiom. This framework
promotes that act of inspection (`interact`) to the first primitive.
The five axioms are statements about the *shape of observation*:

- `interact_self` — self-observation returns the entity unchanged.
- `entity_eq_dec` — entity equality is decidable (and hence
  observation agreement is decidable via `interact_decidable`).
- `existence` — at least two entities exist to observe.
- `interact_with` — every entity has a viewpoint that moves it
  (no terminal state).
- `interaction_cannot_witness_collapse` — `≈` marks what no
  observation can witness.

The mechanisation's scale (~22k lines) is the visible cost of paying
for observation explicitly where other axiomatisations inherit it
for free. Ring theory is the cleanest benchmark: its textbook
presentation assumes the reader can inspect elements, so lifting a
ring into `ExistenceSig` requires supplying that inspection structure
through marker entities. Every `DecEqCommRingSig` — including `F₂`
and the trivial ring — becomes an Entity via `existences/RingAsEntity.v`.

---

## Layer 0 — framework/

Primitives, composition operators, and external algebraic interfaces.

### Foundation

- `Existence.v` — 3 primitives + 5 axioms + `ExistenceTheory` (core).
- `Materialized.v` — cost layer: `info_size`, `storage_cost`, `flip_cost`.
- `Witnessed.v` — witness time coordinate, parallel to cost.
- `Iterable.v` — `remaining` primitive (stall-free progress).
- `LatticeWitnessed.v` — lattice value + witness time composition.

### Categorical composition (over `ExistenceSig`)

- `ExistenceMorphism.v` — `interact`-preserving maps.
- `ExistenceProduct.v` — pairwise product.
- `ExistencePullback.v` — pullback along a pair of morphisms.
- `ExistencePushout.v` — pushout (uses `quotient_exists` — the only
  axiom in the repo).
- `ExistenceEqualizer.v` — equalizer of a parallel pair.
- `ExistenceCoequalizer.v` — coequalizer of a parallel pair.
- `ExistenceFactorization.v` — epi/mono factorization.

### Algebraic interface

- `Ring.v` — `RingSig`, `CommRingSig`, `DecEqCommRingSig` + `RingTheory`.
- `RingMorphism.v` — ring homomorphism interface + derived identities.

---

## Layer 1 — existences/

Each file defines a concrete `Entity` inhabiting some `ExistenceSig`-family
or `DecEqCommRingSig`.

### Existence instances

- `YouAndMe.v` — two-entity toy instance (minimal witness).
- `ConsistencyModelPD.v` — memory consistency model (partial order).
- `LatticeModel.v` — semilattice value as Entity.
- `HashModel.v` — hash map as Entity (pullback source).
- `CounterMachine.v` — counter machine state.
- `PolyModel.v` — polynomial model (Existence-level).
- `RealIterator.v` — iterator over a real sequence.
- `SKIModel.v` — SKI combinator calculus.
- `EpsilonDelta.v` — ε–δ convergence witness for collapse.
- `SemilatticeInstances.v` — concrete semilattices.
- `PureMarkerEntity.v` — degenerate instance: `Entity = nat`, pure
  viewpoints without data. The minimal inhabitant of `ExistenceSig`.
- `ObjectMirror.v` — physics-flavoured instance exposing the
  asymmetry of `interact`. Object viewed through Mirror attenuates
  by the mirror's coefficient; Mirror viewed through Object decays
  by a factor of ten. `interact a b ≠ interact b a` (often with
  different constructors on each side).

### Set theory

- `ElemSig.v` — element signature (decidable equality + witness).
- `SymbolicSet.v` — `SEmpty`/`SInsert`/`SUnion`/`SIntersect`/`SComplement`/`SAll`.
- `NatSet.v` — `SymbolicSet` over ℕ.
- `NatSetSet.v` — `SymbolicSet` whose elements are `NatSet.Entity` (nesting).

### Number systems

- `IntegerGrothendieck.v` — ℤ as ℕ²/~ (Grothendieck construction).
- `RationalRep.v` — ℚ with `Qred` canonicalization (= witness).
- `CauchyReal.v` — ℝ via Cauchy-term grammar (≈ witness).
- `DedekindReal.v` — ℝ via Dedekind cut grammar.

### Algebraic structures (rings)

- `IntegerRing.v` — ℤ as `DecEqCommRingSig`.
- `ModularRing.v` — ℤ/nℤ as `DecEqCommRingSig`.
- `PolynomialRing.v` — functor `R ↦ R[x]`; all 10 ring axioms proved
  without `Admitted`.
- `FinSetRing.v` — Boolean ring on subsets of `{0..n−1}` (add = XOR,
  mul = AND).

### Ring → Entity lifting

- `RingAsEntity.v` — functor from any `DecEqCommRingSig` into
  `ExistenceSig`. Entity is the sum `REnt (ring element) | Mark (nat)`;
  marker entities supply the motion partners the ring alone cannot.
  Instantiations across ℤ, ℤ/7ℤ, FinSet3, ℤ[x], and the edge cases
  F₂ and the trivial ring.
- `RingAsEntity_WithConv.v` — same construction with a non-trivial
  `collapse`. The running instance is ℤ with the mod-7 relation
  between non-zero representatives, realising classical `7 ≡ 14 (mod 7)`
  as framework `≈`.

---

## Layer 2 — results/

Main framework theorems and cross-instance math.

### Framework-level

- `Trichotomy.v` — `≡`, `=`, `≈` pairwise disjoint.
- `FrameworkRice.v` — Rice's theorem at framework level.
- `FrameworkRiceCost.v` — cost-parametrized Rice.
- `FrameworkIrreversibility.v` — information loss under interaction.
- `FrameworkHalting.v` — halting problem in framework form.
- `ExistenceHalting.v` — halting instance witness.
- `SATLowerBound.v` — SAT complexity lower bound (contains one
  documented `Abort`: a family-level impossibility claim whose proof
  is itself not formalizable inside the framework, which is the
  paper's assertion).
- `ScaleInvariantCost.v` — cost invariance under scale.

### Foundational meta-theorems (constructive)

- `CantorTheorem.v` — no surjection `X → (X → Prop)`; explicit
  diagonal witness. `Closed under the global context`.
- `RussellParadox.v` — unrestricted comprehension ⇒ False; explicit
  diagonal set `R`. Applied to `SymbolicSet.SetExpr` and `Entity`.
- `NatSetExtensionality.v` — extensional equality in `NatSet`.

### Cross-instance math — rational/cauchy

- `RationalToCauchyMorphism.v` — ℚ → ℝ_Cauchy.
- `RationalCauchyProduct.v` — product of RR and CR.
- `RationalCauchyPullback.v` — pullback along morphism.
- `RationalCauchyPushout.v` — pushout along morphism.
- `RationalCauchyFactorization.v` — epi/mono factorization.

### Cross-instance math — other

- `IntegerGrothendieckFactorization.v` — ℕ² → ℤ factorization.
- `ModularCoequalizer.v` — ℤ/7ℤ as a coequalizer in Existence.
- `DedekindCauchyIsomorphism.v` — ℝ_Dedekind ≅ ℝ_Cauchy (both directions).
- `IntegerToModularRingMorphism.v` — ℤ → ℤ/7ℤ as ring morphism.
- `MultivariatePolynomial.v` — ℤ[x][y][z] via iterated `PolynomialRing`.
- `PolynomialEvaluation.v` — `eval_n : ℤ[x] → ℤ` as ring morphism (Horner).
- `RealTower.v` — ℚ → ℝ_Cauchy ≅ ℝ_Dedekind composition chain.
- `BooleanSetPolynomial.v` — `PolynomialRing ∘ FinSetRing(8)` with literal
  witness `{{0,1},{2}} + {{0},{1,2}}·x²`.

### Ring-as-Entity bridge

- `MarkerUniverseEmbedding.v` — for every `DecEqCommRingSig R`, the
  inclusion `nat → RingAsEntity(R).Entity` that sends `n ↦ Mark n`
  is an injective, interact-preserving morphism. The same pure-marker
  existence sits inside every Ring-Entity identically.
- `BoolPolyAsEntity.v` — the four-layer stack
  `FinSetRing(3) → FinSetRing(8) → PolynomialRing → RingAsEntity`
  compiled as a single `Entity`. Literal
  `{{0,1},{2}} + {{0},{1,2}}·x²` sits inside the `REnt` branch
  and interacts with markers from the universal substructure.

### Analysis

- `CauchyLimits.v` — pointwise-equality witnesses for polynomial
  identities: `(a+b)² = a² + 2ab + b²` etc.

### Programs as Entities

- `SKIComputationalWitnesses.v` — applies `FrameworkHalting` and
  `FrameworkRice` to `SKIComputable`. `interact` is literally one
  reduction step (`reflexivity` witnesses step-by-step execution).
  Collapse witnesses `(KK)S` and `(KK)I` both reduce to `TK`,
  yielding Rice's no-universal-decoder for SKI as a corollary of the
  abstract framework theorem. Divergent witness: `(SII)(SII)`.

---

## Layer 3 — tests/

### Framework functor verification (pedagogical, on Lattice)

- `MorphismTest.v`, `PullbackTest.v`, `PushoutTest.v`,
  `EqualizerTest.v`, `CoequalizerTest.v`, `FactorizationTest.v`.
- `PullbackLatHashTest.v` — mixed Lattice/Hash pullback.

### Instance functor suites

- `HashFunctorTests.v` — equalizer/coequalizer/factorization on Hash.
- `CauchyFunctorTests.v` — same on Cauchy.

### Instance-specific witness tests

- `RationalRepTest.v`, `CauchyRealTest.v`.

### Main theorem tests

- `TrichotomyTest.v`, `FrameworkRiceTest.v`, `FrameworkRiceCostTest.v`.

### Audit (standalone)

- `AssumptionsAudit.v` — `Print Assumptions` across all framework
  theorems. Run separately:
  ```
  coqc -Q framework "" -Q existences "" -Q results "" -Q tests "" tests/AssumptionsAudit.v
  ```

---

## Reading paths

- **First contact:** `paper.typ` → `framework/Existence.v` →
  `results/Trichotomy.v`.
- **Core impossibilities:** `results/CantorTheorem.v` →
  `results/RussellParadox.v` → `results/SATLowerBound.v`.
- **Ring construction:** `framework/Ring.v` → `existences/IntegerRing.v` →
  `existences/PolynomialRing.v` → `results/MultivariatePolynomial.v` →
  `results/PolynomialEvaluation.v`.
- **Ring as Entity:** `framework/Ring.v` → `existences/RingAsEntity.v` →
  `existences/RingAsEntity_WithConv.v` → `existences/PureMarkerEntity.v`
  → `results/MarkerUniverseEmbedding.v` → `results/BoolPolyAsEntity.v`.
- **Number tower:** `existences/RationalRep.v` →
  `existences/CauchyReal.v` ≅ `existences/DedekindReal.v` →
  `results/RealTower.v`.
- **Composition showcase:** `existences/FinSetRing.v` →
  `results/BooleanSetPolynomial.v` (`PolynomialRing ∘ FinSetRing`)
  → `results/BoolPolyAsEntity.v` (same stack promoted to Entity).
- **Categorical composition:** `framework/ExistenceMorphism.v` →
  `ExistencePullback.v` → `ExistencePushout.v` → `ExistenceEqualizer.v`
  → `ExistenceCoequalizer.v` → `ExistenceFactorization.v`.
- **Cross-instance transport:** `results/RationalToCauchyMorphism.v` →
  `results/RationalCauchy{Product,Pullback,Pushout,Factorization}.v`.
- **Programs as Entities:** `existences/SKIModel.v` →
  `results/SKIComputationalWitnesses.v` (`interact` = one-step
  reduction; Rice and Halting applied to SKI).

---

## Theorem highlights

| Result | File | Kind |
| --- | --- | --- |
| Three relations pairwise disjoint | `results/Trichotomy.v` | framework |
| Rice's theorem (framework form) | `results/FrameworkRice.v` | framework |
| Cost-parametrized Rice | `results/FrameworkRiceCost.v` | framework |
| Irreversibility under interaction | `results/FrameworkIrreversibility.v` | framework |
| SAT complexity lower bound | `results/SATLowerBound.v` | framework |
| Cantor's theorem | `results/CantorTheorem.v` | meta (constructive) |
| Russell's paradox (impossibility of unrestricted comp) | `results/RussellParadox.v` | meta (constructive) |
| ℝ_Dedekind ≅ ℝ_Cauchy | `results/DedekindCauchyIsomorphism.v` | cross-instance |
| PolynomialRing all 10 ring axioms | `existences/PolynomialRing.v` | algebraic |
| Boolean ring on subsets | `existences/FinSetRing.v` | algebraic |
| Every `DecEqCommRingSig` is an Entity (inc. F₂, trivial) | `existences/RingAsEntity.v` | bridge |
| Mod-7 equivalence as framework `≈` | `existences/RingAsEntity_WithConv.v` | bridge |
| Marker universe ring-independent | `results/MarkerUniverseEmbedding.v` | bridge |
| 4-layer stack as single Entity | `results/BoolPolyAsEntity.v` | composition |
| Rice + Halting specialised to SKI | `results/SKIComputationalWitnesses.v` | computational |
| `interact` asymmetry made physical | `existences/ObjectMirror.v` | asymmetry witness |

---

## Axiom hygiene

All proofs close under the global context, with two documented exceptions:

- `framework/ExistencePushout.v` uses `quotient_exists` — the only
  non-trivial axiom in the repo. No result in `paper.typ` invokes it.
- `results/SATLowerBound.v` contains one `Abort` that marks a
  family-level impossibility: the proof cannot be formalised inside
  the framework, and that un-formalisability is itself the claim the
  file registers.

Cantor and Russell are both intuitionistic (no classical axioms,
no functional extensionality, no choice).

Audit command:

```
coqc -Q framework "" -Q existences "" -Q results "" -Q tests "" tests/AssumptionsAudit.v
```

---

## Build

```
make            # build everything listed in _CoqProject
make clean
```

Paper:

```
typst compile paper.typ
```

Demo:

```
cd scev-demo && cargo run
```
