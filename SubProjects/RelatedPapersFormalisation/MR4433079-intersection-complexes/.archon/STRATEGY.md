# Strategy

## Goal

Formalize the main results of Sakellaridis–Wang (2020), "Intersection complexes and unramified $L$-factors" (arXiv:2009.03943, MR4433079): the crystal structure theorem (Thm 1.6 = primary near-term target), the stratified semi-smallness theorem (Thm 1.4), and the IC function formula (Thms 1.1–1.2). The IC function theorems depend on sheaf-theoretic infrastructure declared axiomatically in a dedicated `Axioms.lean` file (axiom-first approach — see Routes).

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Parallel with |
|-------|--------|------------|-----|-------------------|---------------|
| Blueprint (all 21 declarations written and wired) | ACTIVE | 1 | ~0 | — | — |
| Combinatorial foundations (cocharacter lattice, spherical variety combinatorics, monoid $\mathfrak{c}_X$, colors, type-T condition) | NEXT | 5–10 | ~300–600 | `RootSystem`, `RootPairing` | Crystal axioms (below) |
| Crystal axioms (abstract `Crystal` typeclass, operators $e_i, f_i$, $\varepsilon_i, \varphi_i$, semi-normality, self-duality, crystal morphisms) | NEXT | 25–50 | ~2000–5000 | None in Mathlib | Combinatorial foundations |
| Arc spaces / loop spaces (`L^+X` as pro-scheme: universal property, functoriality, GKD theorem) | NEXT | 8–15 | ~500–1000 | Pro-schemes not in Mathlib | Crystal operators (below) |
| Zastava and global models (mapping stacks $\mathcal{Y}_X$, $\mathcal{M}_X$, $\mathcal{A}$; maps $\pi$, $\bar\pi$; stratifications) | NEXT | 10–20 | ~800–2000 | Mapping stacks not in Mathlib | Crystal on fibers (below) |
| Compactification and MV cycles (compactified Zastava $\overline{\mathcal{Y}}_X$; semi-infinite orbits; Mirković–Vilonen cycles; their crystal structure) | NEXT | 8–15 | ~500–1000 | Affine Grassmannian not in Mathlib | Above two |
| Axiom layer (`Axioms.lean`: perverse sheaves, IC-complex existence, decomposition theorem, nearby cycles base-change — as named `axiom` declarations) | NEXT | 3–8 | ~200–500 | None (all axiomatic) | Crystal on fibers |
| Crystal theorem (Thm 1.6: semi-normal self-dual crystal structure on $\mathfrak{B}_{X^\bullet}$; proof using SL₂ actions and Thm 1.8) | NEXT | 15–25 | ~1000–2000 | Above crystal + combinatorial phases | — |
| Semi-smallness theorem (Thm 1.4: $\bar\pi$ proper and stratified semi-small; using Thm 1.8 + factorization) | NEXT | 10–20 | ~800–1500 | Axiom layer + Zastava phase | — |
| IC formula (Thms 1.1–1.2: IC function formula via semi-smallness + decomposition theorem axiom) | NEXT | 15–25 | ~1000–2000 | Axiom layer + all geometric phases | — |
| Asymptotics + Plancherel (Cor 1.3: via nearby cycles axiom + Satake isomorphism) | NEXT | 5–10 | ~300–600 | Nearby cycles axiom | After IC formula |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|-------|----------------------|-----|-------|-------------|---------------------|---------|
| Init | 001 · 1 | 0 | Basic.lean | Empty scaffold | — | — |
| DAG blueprint | 001 · 1 | 0 | Overview.tex | 21-block blueprint, wired DAG | Blueprint-writer directive format | Need macros in common.tex |

## Routes

**Axiom-first route (adopted).** Key infrastructure that cannot feasibly be built from scratch in this project (perverse sheaves, decomposition theorem, IC-complex existence and properties, nearby cycles base-change) will be declared as named Lean `axiom` declarations in `Axioms.lean` with explicit type signatures. The main theorems (Thms 1.1, 1.2, 1.4) reference these axioms. This immediately enables formal theorem statements and allows the combinatorial and algebraic work (crystal theory, dimension estimates) to be verified against correct statement shapes. Axioms can be discharged incrementally as upstream Mathlib infrastructure matures.

**Primary near-term target: Crystal theorem (Thm 1.6).** This is the most tractable of the three main results — it requires only combinatorial foundations and the crystal axioms, not arc spaces or IC complexes. Route the first active prover work here.

**Parallelism.** Two independent lanes can run concurrently:
- Lane A: combinatorial foundations → crystal operators → crystal on central fibers → Thm 1.6
- Lane B: axiom layer → arc spaces → Zastava/global models → compactification/MV cycles → Thms 1.1, 1.2, 1.4

## Open strategic questions

- **Crystal upstream contribution**: Invest 2–5 iters to contribute the abstract `Crystal` typeclass to Mathlib as a standalone PR, vs. build locally? (Minor risk trade-off; revisit after local design is stable.)
- **Axiom signature design**: How should IC-complex existence be axiomatized (as a functor from schemes to sheaves, or as a predicate on sheaves)? Needs a mathematician decision before `Axioms.lean` is written.
- **Characteristic assumptions**: The paper works over algebraically closed fields; track where characteristic zero is needed vs. positive characteristic (with type-T condition).

## Mathlib gaps & new material

**Gaps to fill:**
- Kashiwara crystal typeclass and all axioms (no Lean 4 Mathlib formalisation exists)
- Pro-schemes / arc spaces `L^+X` (not in Mathlib)
- Mapping stacks (Zastava model as algebraic stack)
- Perverse sheaves, IC complexes, decomposition theorem (declared axiomatically)
- Affine Grassmannian, semi-infinite orbits, MV cycles

**New project material:**
- Spherical variety combinatorics (type-T, dual group, colors $\mathcal{D}$, monoid $\mathfrak{c}_X$)
- Crystal $\mathcal{B}_{X^\bullet}$ on irreducible components of Zastava central fibers
- Dimension formula $\frac{1}{2}(\mathrm{len}(\check\lambda)-1)$ for critical dimension
- IC function formula as a ratio of $\mathrm{Sym}^\bullet$ traces (Thms 1.1, 1.2)
