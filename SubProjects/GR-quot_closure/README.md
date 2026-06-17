# AlgebraicJacobian — Grassmannian-quotient representability (GR-quot closure subproject)

<!-- archon:readme -->

## Project

A formalization in Lean 4 + Mathlib of the **representability of the relative Grassmannian**
— the Čech-independent (H⁰) leg that constructs the rank-`d` Grassmannian `Grass(V, d)` of
quotients of a locally free sheaf as a scheme, glued from affine charts via the `GL_d`
cocycle, and proves it represents the rank-`d`-quotient functor.

This project was **extracted** from the parent *Quot-Foundations* project (itself carved from
Christian Merten's *Algebraic-Jacobian-Challenge*). It is one work package in the
decomposition of the dependency cone of `thm:fga_pic_representability`; a sibling subproject
`FBC-B_SNAP-chain` covers the flat-base-change (FBC-B) leg and shares the section-graded-ring
(SNAP) foundation with this one. All Lean names, file paths and blueprint labels are unchanged
from the parent, so finished proofs merge back as a three-way merge.

**Targets — the 9 sorry-bearing nodes in this cone (seeds + their transitive dependencies):**

| Group | Blueprint node | Lean declaration | Status |
|---|---|---|---|
| GR-quot (seed) | `thm:grassmannian_representable` | `…Scheme.Grassmannian.representable` | closable here |
| GR-quot (seed) | `def:grassmannian_scheme` | `…Scheme.Grassmannian` | closable here |
| GR-quot (seed) | `lem:tautologicalQuotient_epi` | `…tautologicalQuotient_epi` | closable here |
| SNAP (shared) | `def:sectionsCast` | `…Modules.sectionsCast` | keep as sorry / import from sibling |
| SNAP (shared) | `lem:sectionsCast_refl` | `…Modules.sectionsCast_refl` | keep as sorry / import from sibling |
| SNAP (shared) | `lem:gradedMonoid_eq_of_cast` | `…Modules.gradedMonoid_eq_of_cast` | keep as sorry / import from sibling |
| SNAP (shared) | `lem:sectionMul_coherent` | `…Modules.sectionsMul_*` (4 decls) | keep as sorry / import from sibling |
| χ-blocked | `def:quot_functor` | `…Scheme.QuotFunctor` | fill from cohomology leg |
| χ-blocked | `def:hilbert_polynomial` | `…Scheme.hilbertPolynomial` | fill from cohomology leg |

The two **χ-blocked** nodes are χ-semantic (`Φ(m)=χ=Σᵢ(-1)ⁱ dim Hⁱ`) and need a
higher-cohomology engine this i=0 leg does not have; they stay as `sorry` and are sourced from
the cohomology leg at merge. The **SNAP** nodes are shared with the sibling `FBC-B_SNAP-chain`
(see `.archon/USER_HINTS.md`). See the full arc in `.archon/STRATEGY.md`.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

- `AlgebraicJacobian/Picard/GrassmannianCells.lean` — affine charts, cocycle, `Grassmannian` scheme, separatedness, properness
- `AlgebraicJacobian/Picard/GlueDescent.lean` — effective descent for `SheafOfModules` over `Scheme.GlueData`
- `AlgebraicJacobian/Picard/GrassmannianQuot.lean` — tautological quotient, `represents`, representability endgame
- `AlgebraicJacobian/Picard/QuotScheme.lean` — Quot functor, Hilbert polynomial (χ-blocked), QUOT support/localization infra
- `AlgebraicJacobian/Picard/SectionGradedRing.lean` — H⁰ section graded ring `Γ_*(X,L)` (SNAP, shared with sibling)
- `AlgebraicJacobian/Picard/GradedHilbertSerre.lean` — graded Hilbert–Serre rationality engine
- `AlgebraicJacobian/Picard/RelativeSpec.lean` — relative Spec (existence, universal property, affine base)
- `blueprint/` — leanblueprint source (build with `leanblueprint pdf` and `leanblueprint web`)
- `references/` — informal sources backing the formalization
- `archon-protected.yaml` — declarations agents must not modify
- `.archon/` — agent state (not committed)

## How to build

```bash
lake exe cache get   # download Mathlib olean cache
lake build           # compile the project
```

## How to run the formalization loop

```bash
archon loop .
```

This launches the plan → prove → review loop and opens a dashboard.
