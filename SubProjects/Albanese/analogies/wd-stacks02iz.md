# Analogy: open-immersion stalk-bridge for prime divisors (Stacks 02IZ / 005X)

## Mode
api-alignment

## Slug
wd-stacks02iz

## Iteration
200

## Question

The iter-200 Lane WD-A4a-Sub-build-1 prover is asked to build, axiom-clean,
the open-immersion stalk-bridge for prime divisors: given an integral
locally Noetherian scheme `X`, an open `U ⊆ X` with open immersion
`i : U ↪ X`, and a prime divisor `Y ⊆ X` (a point `Y.point ∈ X` with
`Order.coheight Y.point = 1`), if `Y.point ∈ U` then there exists a prime
divisor `Y_U : (↑U).PrimeDivisor` with `i_*(Y_U) = Y` (same underlying
point, lifted along `Subtype.val : ↥U → X`).

The corresponding Stacks tags are 02IZ (open-immersion stalks: the stalk
map of an open immersion is an iso) and 005X (topological coheight ↔
algebraic Krull dim for Noetherian schemes / Hartshorne II.6.1).

The directive treats this as a "Mathlib substrate partially absent"
situation (per iter-199 prover lane + iter-200 progress-critic
`route200` CHURNING verdict).

## Project artifact(s)

- `AlgebraicJacobian/RiemannRoch/WeilDivisor.lean:93-98` — `Scheme.PrimeDivisor`
  structure with `coheight : Order.coheight point = 1` field.
- `AlgebraicJacobian/RiemannRoch/WeilDivisor.lean:153-157` —
  `Scheme.RationalMap.order` consuming
  `[Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]`.
- `AlgebraicJacobian/RiemannRoch/WeilDivisor.lean:357-415` —
  `rationalMap_order_finite_support` with the open `sorry` whose iter-198
  blueprint plan is exactly the "split prime divisors as
  intersect-U / disjoint-from-U" + Hartshorne II.6.1 affine-chart bound.
- **`AlgebraicJacobian/Albanese/CoheightBridge.lean` (237 LOC, axiom-clean,
  iter-183)** — **the existing project-side coheight↔Krull-dim bridge** the
  iter-200 directive did NOT mention. Provides:
  - `Order.coheight_eq_of_isOpenEmbedding` (L51-106) — Stacks 02IZ
    topological side, project-side, axiom-clean.
  - `Order.coheight_spec_eq_height_primeSpectrum` (L115-137) — Spec ↔
    PrimeSpectrum duality.
  - `AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_coheight` (L149-215) —
    Stacks 005X for schemes, axiom-clean.
  - `AlgebraicGeometry.Scheme.ringKrullDimLE_of_coheight_eq_one` (L228-233)
    — codim-1 consumer wrapper.
- `AlgebraicJacobian/Albanese/CodimOneExtension.lean:8` imports
  `AlgebraicJacobian.Albanese.CoheightBridge`; **`WeilDivisor.lean` does
  not**.

## Decisions identified

### Decision 1: Stacks 02IZ stalk iso — does Mathlib provide it?

- **Mathlib idiom (POSITIVE)**: Mathlib provides the open-immersion stalk
  iso in two forms:
  - `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`
    (`Mathlib.AlgebraicGeometry.OpenImmersion`) — for any open immersion
    `f : X ⟶ Y`, `IsIso ((Scheme.Hom.stalkMap f) x)`.
  - `AlgebraicGeometry.Scheme.Opens.stalkIso`
    (`Mathlib.AlgebraicGeometry.Restrict`) — the canonical iso
    `(↑U).presheaf.stalk x ≅ X.presheaf.stalk ↑x` for `U : X.Opens` and
    `x : ↥U`. Drop-in for the open-subscheme case the lane targets.
- **Project's current path**: none in `WeilDivisor.lean`; the iter-199
  prover lane flagged this as a "Mathlib gap" without citing the
  available primitives.
- **Gap**: identical — Mathlib ships exactly what is needed; no
  project-side bridge required.
- **Verdict**: **PROCEED** — consume `Scheme.Opens.stalkIso` directly. No
  Stacks 02IZ stalk-iso build is needed.

### Decision 2: Stacks 02IZ topological-coheight transfer — does the project have it?

- **Mathlib idiom**: pieces present but un-assembled. Mathlib has
  `Order.coheight` (`Mathlib.Order.KrullDimension`),
  `Order.coheight_orderIso` (transports through `OrderIso`),
  `subtype_specializes_iff` (`Mathlib.Topology.Inseparable`:
  `x ⤳ y ↔ ↑x ⤳ ↑y` for `Subtype p`), and `Specializes.mem_open`
  (`x ⤳ y → IsOpen s → y ∈ s → x ∈ s`). The assembly
  `Order.coheight z (in X) = Order.coheight ⟨z, hz⟩ (in U)` for `U : Set X`
  open is NOT shipped.
- **Project's existing path (CRITICAL — directive did not cite this)**:
  the project ALREADY assembled this at iter-183 in
  `AlgebraicJacobian/Albanese/CoheightBridge.lean:51-106`:
  ```lean
  lemma Order.coheight_eq_of_isOpenEmbedding
      {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
      (z : X) (hz : z ∈ U) :
      @Order.coheight X (specializationPreorder X) z
        = @Order.coheight U (specializationPreorder U) ⟨z, hz⟩
  ```
  Axiom-clean per its iter-183 landing record.
- **Gap**: divergent-and-already-resolved — the substrate exists; the
  directive simply did not surface it.
- **Verdict**: **ALIGN_WITH_EXISTING_PROJECT_INFRASTRUCTURE** — import
  `AlgebraicJacobian.Albanese.CoheightBridge` in `WeilDivisor.lean` and
  consume `Order.coheight_eq_of_isOpenEmbedding` directly. No fresh
  build needed for this piece of "Stacks 02IZ".

### Decision 3: Stacks 005X coheight ↔ Krull dim for scheme stalks — does the project have it?

- **Mathlib idiom**: pieces present but the scheme-level bridge is not
  packaged in Mathlib. Available primitives:
  - `IsLocalization.AtPrime.ringKrullDim_eq_height`
    (`Mathlib.RingTheory.Ideal.Height:341`).
  - `Ideal.height_eq_primeHeight` (`Mathlib.RingTheory.Ideal.Height:45`).
  - `IsAffineOpen.isLocalization_stalk`
    (`Mathlib.AlgebraicGeometry.AffineScheme:806`).
  - `AlgebraicGeometry.Scheme.le_iff_specializes`
    (`Mathlib.AlgebraicGeometry.Scheme`) — scheme preorder is the spec
    preorder.
- **Project's existing path**: assembled at iter-183 in
  `CoheightBridge.lean:149-215`:
  ```lean
  theorem Scheme.ringKrullDim_stalk_eq_coheight
      (X : Scheme.{u}) (z : X) :
      ringKrullDim (X.presheaf.stalk z) = Order.coheight z
  ```
  Axiom-clean. The proof picks an affine open via
  `exists_isAffineOpen_mem_and_subset`, names the prime via
  `IsAffineOpen.primeIdealOf`, applies `IsLocalization.AtPrime.
  ringKrullDim_eq_height`, then assembles
  `coheight_eq_of_isOpenEmbedding` (decl 1) +
  `coheight_spec_eq_height_primeSpectrum` (decl 2).
- **Gap**: divergent-and-already-resolved — the substrate exists.
- **Verdict**: **ALIGN_WITH_EXISTING_PROJECT_INFRASTRUCTURE** — import
  `CoheightBridge.lean` and use `Scheme.ringKrullDim_stalk_eq_coheight`
  /`Scheme.ringKrullDimLE_of_coheight_eq_one`. No fresh build needed
  for Stacks 005X at the scheme-stalk level either.

### Decision 4: prime-divisor pushforward / cycle map along an open immersion — Mathlib status

- **Mathlib idiom (NEGATIVE)**: Mathlib at commit `b80f227` ships
  - no `Scheme.PrimeDivisor` (the project's structure is bespoke);
  - no `Scheme.WeilDivisor` / cycle group on schemes;
  - no `Scheme.Cycle.pushforward` or analogous prime-divisor
    pushforward along scheme morphisms.
  The closest neighbours are `IsDedekindDomain.HeightOneSpectrum` (for
  Dedekind domains only), `MeromorphicOn.divisor` (analysis/complex
  geometry), and `Mathlib.Algebra.MvPolynomial.Cycle` (unrelated).
- **Gap**: divergent-and-unavoidable — the cycle pushforward IS a
  project-side build, but only a thin one: it reduces to the
  point-bijection `{Y : X.PrimeDivisor | Y.point ∈ U} ≃
  (↑U).PrimeDivisor`, which is a direct corollary of Decision 2.
- **Verdict**: **NEEDS_PROJECT_BUILD** — but a small one (~20-40 LOC),
  because the topological bridge does all the heavy lifting.

### Decision 5: `Ring.ordFrac` transport across the stalk iso (Sub-build 2 preview)

- **Mathlib idiom (NEGATIVE for naturality, POSITIVE for definition)**:
  Mathlib has `Ring.ordFrac` (`Mathlib.RingTheory.OrderOfVanishing`) for
  a Noetherian local domain of Krull dim ≤ 1. The naturality lemma
  "for `R ≃+* R'` (and induced `K ≃+* K'`),
  `(Ring.ordFrac R')(φ x) = (Ring.ordFrac R)(x)`" is NOT shipped.
- **Gap**: divergent — Mathlib has the per-ring object but no
  ring-iso transport. This is iter-201+ Sub-build 2 scope.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (project-side ~30-50 LOC,
  upstream PR-able) — but **NOT in this iter's WD Sub-build 1 scope**.

## Recommendation

### The bottom line: the iter-200 lane scope is OVER-ESTIMATED by ~50%.

The directive estimates ~150-250 LOC for WD-A4a-Sub-build-1 ("Build
open-immersion stalk-bridge for prime divisors"). The actual remaining
work, after consuming `CoheightBridge.lean` and `Scheme.Opens.stalkIso`,
is **~50-100 LOC of thin glue**:

1. **Add `import AlgebraicJacobian.Albanese.CoheightBridge` to
   `WeilDivisor.lean`** (1 LOC). Without this import the bridge is
   invisible to the prover.

2. **Build `Scheme.PrimeDivisor.restrictToOpen`** (~10 LOC). Given
   `Y : X.PrimeDivisor` and a proof `hYU : Y.point ∈ U`, construct
   `Y_U : (↑U).PrimeDivisor`:
   ```lean
   def Scheme.PrimeDivisor.restrictToOpen
       {X : Scheme.{u}} (U : X.Opens)
       (Y : X.PrimeDivisor) (hYU : Y.point ∈ U) :
       U.toScheme.PrimeDivisor where
     point := ⟨Y.point, hYU⟩
     coheight := by
       -- Use Order.coheight_eq_of_isOpenEmbedding (already in project)
       -- to transport Y.coheight = 1 from X to U.
       rw [← Y.coheight]
       exact (Order.coheight_eq_of_isOpenEmbedding U.isOpen Y.point hYU).symm
   ```
   (The defeq between `U.toScheme` carrier and `↥U.1` may require a
   `change` or `show` to align preorders — that's the principal
   friction. Worst-case +5 LOC.)

3. **Build `Scheme.PrimeDivisor.ofOpen`** (~10 LOC). Inverse direction
   — push a prime divisor of the open subscheme to a prime divisor of
   the parent:
   ```lean
   def Scheme.PrimeDivisor.ofOpen
       {X : Scheme.{u}} (U : X.Opens)
       (Y_U : U.toScheme.PrimeDivisor) :
       X.PrimeDivisor where
     point := Y_U.point.1
     coheight := by
       rw [Order.coheight_eq_of_isOpenEmbedding U.isOpen Y_U.point.1
             Y_U.point.2]
       exact Y_U.coheight
   ```

4. **Build the equivalence**
   `{Y : X.PrimeDivisor | Y.point ∈ U} ≃ U.toScheme.PrimeDivisor`
   (~20-30 LOC) — package the two as a `Set.BijOn` /`Equiv`. The
   roundtrip lemmas are `Subtype.ext` + `Scheme.PrimeDivisor.ext` (if
   it exists; otherwise `cases`).

5. **Stalk identification** (~5-15 LOC). The directive's "stalk-bridge"
   piece: provide the project-facing helper
   ```lean
   def Scheme.PrimeDivisor.stalkIso
       {X : Scheme.{u}} (U : X.Opens)
       (Y : X.PrimeDivisor) (hYU : Y.point ∈ U) :
       (U.toScheme).presheaf.stalk (Y.restrictToOpen U hYU).point ≅
         X.presheaf.stalk Y.point :=
     Scheme.Opens.stalkIso U ⟨Y.point, hYU⟩
   ```
   This is a one-liner — Mathlib's `Scheme.Opens.stalkIso` IS the
   bridge.

6. **(Optional, PUSH-BEYOND)** Strengthen `Scheme.IsRegularInCodimensionOne`
   transport across the bijection (~10-20 LOC): `[Scheme.IsRegularInCodimensionOne X] →
   [IsIntegral (↑U)] → Scheme.IsRegularInCodimensionOne (↑U)` via the
   stalk iso. Useful for both Sub-build 1 consumers and for
   shrinking the rest of `WeilDivisor.lean`'s `[Scheme.IsRegularInCodimensionOne X]`
   bookkeeping.

### Concrete 3-step recipe with LOC estimates

| Step | What | LOC | Key Mathlib / project helpers |
|---|---|---|---|
| 1 | `import AlgebraicJacobian.Albanese.CoheightBridge` in `WeilDivisor.lean` | 1 | — |
| 2 | `Scheme.PrimeDivisor.restrictToOpen` + `ofOpen` + `Equiv` | 30-50 | `Order.coheight_eq_of_isOpenEmbedding` (project) |
| 3 | `Scheme.PrimeDivisor.stalkIso` + downstream `Ring.KrullDimLE 1` transport | 10-20 | `Scheme.Opens.stalkIso` (Mathlib) |
| 4 (PB) | `IsRegularInCodimensionOne` open-immersion descent | 10-20 | combine steps 1-3 |

**Total realistic LOC**: 50-90 substrate-only; 50-110 with PUSH-BEYOND.

The ~150-250 LOC directive budget is achievable and comfortably leaves
slack for tactic friction and the iter-201 Sub-build 2 priming
(`Ring.ordFrac` naturality, ~30-50 LOC).

### Critical planner correction

**The directive (and PROGRESS.md L101-122) describes Stacks 02IZ/005X
as a "Mathlib substrate partially absent" gap, but the project ALREADY
HAS the substrate in `AlgebraicJacobian/Albanese/CoheightBridge.lean`,
landed axiom-clean iter-183 and used in
`Albanese/CodimOneExtension.lean`.** The progress-critic's CHURNING
diagnosis on Lane WD-A4a (8 helpers added, 0 sorries closed in 2 active
iters) is consistent with this: helpers proliferate when the available
substrate is not surfaced into the prover's directive. The corrective
is informational + structural — point the next prover at
`CoheightBridge.lean`, then the work shrinks from "build a 02IZ/005X
bridge" to "consume the project's existing bridge through the
prime-divisor structure".

### Final verdict for Lane WD-A4a-Sub-build-1

- **PROCEED** with budget reduced from ~150-250 LOC to ~50-110 LOC.
- **ALIGN_WITH_EXISTING_PROJECT_INFRASTRUCTURE** for the topological
  / Krull-dim sides (Decisions 2 + 3).
- **PROCEED** on the prime-divisor bijection (Decision 4) and the
  stalk identification (Decision 1, consume `Scheme.Opens.stalkIso`).
- **DEFER** the `Ring.ordFrac` naturality (Decision 5) to Sub-build 2.

### Mathlib upstream opportunities (parallel to the loop)

Two small PRs the mathematician could submit (neither blocks the loop):

1. `Order.coheight_eq_of_isOpenEmbedding` — generic topology lemma
   currently project-side in `CoheightBridge.lean:51-106`. Natural
   home: `Mathlib.Order.KrullDimension` or
   `Mathlib.Topology.SpectralSpace.Basic`.
2. `AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_coheight` — currently
   project-side in `CoheightBridge.lean:149-215`. Natural home:
   `Mathlib.AlgebraicGeometry.Stalk` or a new
   `Mathlib.AlgebraicGeometry.Coheight`. This is Stacks 005X for
   schemes and would be a clean upstream contribution.

Both PRs would also retire `CoheightBridge.lean` itself eventually.
