# Strategy

## Goal

Formalize the main theorem of MR4258055, *A refined Brill-Noether theory over Hurwitz spaces*: for a general degree-\(k\) cover \(f : C \to \mathbb{P}^1\), the Brill-Noether splitting loci \(\Sigma_{\vec e}(C,f)\) are smooth of the expected dimension when \(u(\vec e) \le g\) and empty otherwise, and deduce the corollary describing the dimensions of the components of \(W^r_d(C)\) for a general \(k\)-gonal curve. The formalization is conditional on three named axioms (Larson's degeneracy-class theorem, the theta-class on Pic, and the smoothness of the splitting loci) flagged explicitly in the Lean files.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
| --- | --- | --- | --- | --- | --- |
| 0: Hypothesis skeleton | ACTIVE | 1 | ~100-200 | none (all sorry'd/axiom'd) | design decisions must be fixed before writing types |
| 1: Splitting types & combinatorics | ACTIVE | 3-5 | ~400-700 | `Fin k → ℤ` with partial-sum order (project-side), cohomology of O_{P^1}(n) (MISSING—build project-side) | majorization order and O_{P^1}(n) cohomology both absent from Mathlib |
| 2a: Elliptic pushforward & order-preserving endomorphisms | ACTIVE | 3-5 | ~300-600 | pushforward along finite maps on elliptic curves, Riemann-Roch on elliptic curves | direct-sum splitting on P¹ not confirmed in Mathlib |
| 2b: Node conditions & dimension bound | ACTIVE | 4-7 | ~700-1500 | local completed-ring endomorphisms, upper semi-continuity for flat families (MISSING) | compact-type degeneration absent from Mathlib; must build locally |
| 3: Smoothness via deformation theory | PAUSED | — | — | geometric Serre duality MISSING; Def¹(L) proxy unresolved | axiomatized as named axiom—see Mathlib gaps |
| 4: Existence via universal classes | ACTIVE | 3-6 | ~300-700 | Chern-class formulas (project-local), theta class (axiom anchor) | Jacobian/theta absent from Mathlib; Larson theorem classified as axiom |

## Routes

### Main route: paper order with phases 2a and 4 in parallel after phase 1

Build the development in the paper's logical order, with three design decisions:

**Design decision 1 (generic cover):** The "general degree-\(k\) cover" is modeled as a *parameterized hypothesis*: a degree-\(k\) morphism \(f : C \to \mathbb P^1\) carrying exactly the properties the paper uses (no Hurwitz-space stack machinery). This makes all lemma signatures durable from phase 0 onward.

**Design decision 2 (axiom set):** Three lemmas are classified as named `axiom`s in Lean:
1. Larson's universal degeneracy-class theorem (`thm:mine`) — required for existence;
2. Theta-class computation on Pic (`lem:cE` input) — required for genus-independence;
3. Smoothness of splitting loci (`lem:sm`) — required for the smooth-of-expected-dimension conclusion.

Geometric Serre duality, the Def¹(L) proxy, and upper semi-continuity for flat families are all missing from Mathlib and together make phase 3 too costly to build honestly relative to other phases. Axiomatizing `lem:sm` is mathematically honest: the paper's deformation-theoretic computation is a specialized lower/upper-triangular independence argument that has no direct Lean reduction to existing Mathlib infrastructure. The main theorem is clearly conditional on all three axioms in the Lean source.

**Design decision 3 (parallelism):** Phase 4 (existence via universal classes) depends only on `def:expected-codim` from phase 1 and the two axioms (`thm:mine`, `lem:cE`); it is independent of all phase 2a output. Therefore phases 2a and 4 run in parallel after phase 1; phase 2b runs after phase 2a closes. Phase 3 is PAUSED (its core lemma is axiomatized). The deformation-theory declarations `def:deformation-map` and `lem:nz` are in phase 3 scope (PAUSED): phase 0 creates sorry'd stubs for them; they remain sorry'd until phase 3 is unpaused.

**Phase order:** Phase 0 → Phase 1 → Phases 2a and 4 in parallel → Phase 2b → Main theorem assembly.

## Open strategic questions

- **DECIDED** — Phase 2a API: use abstract finitely-generated `O_{P^1}`-modules rather than `Curve.EllipticCurve`. This avoids importing heavy EllipticCurve machinery and keeps declarations type-stable from phase 0 onward.
- Is computed cohomology of \(\mathcal O_{\mathbb P^1}(n)\) (H^0 and H^1 as explicit modules) available anywhere in Mathlib, or must it be built project-side? (Current status: MISSING per loogle—build in phase 1.)

## Mathlib gaps & new material

- **Majorization order on `Fin k → ℤ`** (partial-sum condition for splitting types): MISSING; build project-side in phase 1.
- **Computed cohomology of \(\mathcal O_{\mathbb P^1}(n)\)** (H^0 and H^1 as explicit modules): MISSING per prerequisite verification; build project-side in phase 1 (adds ~100–200 LOC to phase 1 scope).
- **Grothendieck splitting theorem** (every rank-k vector bundle on P^1 is a direct sum of line bundles): not confirmed in Mathlib's `AlgebraicGeometry.VectorBundle`; required by `def:splitting-locus` and `def:bn-splitting-locus`. Disposition: axiomatize as a named axiom for phase 1 unless confirmed present with a specific Mathlib name before phase 0 skeleton is finalized.
- **Compact-type degeneration** (families of nodal curves, compatibility at nodes): MISSING; phases 2a–2b build this locally.
- **Upper semi-continuity for coherent sheaves in flat families**: MISSING; required by phase 2b (degeneration comparison); add to phase 2b scope.
- **Geometric Serre duality** (trace pairing on curves): MISSING; required by `lem:sm`; phase 3 PAUSED pending decision; current plan: `lem:sm` classified as named `axiom`.
- **Def¹(L) proxy** (H¹(C, End(f_\*L)) on projective curve): no valid Mathlib analog found (`Algebra.H1Cotangent` is ring-theoretic, not geometric); phase 3 PAUSED; `lem:sm` axiomatized.
- **Larson's universal degeneracy-class theorem**: named `axiom`; no project-local proof planned.
- **Jacobian as abelian variety with theta divisor**: MISSING; `lem:cE`'s theta-class input classified as named `axiom`.
