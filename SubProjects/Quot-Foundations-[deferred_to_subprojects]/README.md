# AlgebraicJacobian — Quot & flat-base-change foundations (Picard-representability subproject)

<!-- archon:readme -->

## Project

A formalization in Lean 4 + Mathlib of the **Čech-independent foundations of the FGA
representability of the Picard scheme**: flat base change for the pushforward of a
quasi-coherent sheaf (degree 0), generic flatness, and the Quot-scheme foundations
(Hilbert polynomial, Quot functor, Grassmannian and its representability).

This project was **extracted** from the parent *Algebraic-Jacobian-Challenge* project
(Christian Merten's Jacobian challenge). It is one of the work packages into which the
dependency cone of `thm:fga_pic_representability` is decomposed; a sibling subproject
covers the Čech-cohomology leg (`lem:cech_computes_cohomology`). The two legs are
disjoint and can be worked in parallel; both merge back into the parent (all Lean names,
file paths and blueprint labels are unchanged from the parent).

**Targets (the extraction seeds — 7 sorry-bearing nodes):**

| Blueprint node | Lean declaration |
|---|---|
| `thm:flat_base_change_pushforward` | `AlgebraicGeometry.flatBaseChange_pushforward_isIso` |
| `lem:affine_base_change_pushforward` | `AlgebraicGeometry.affineBaseChange_pushforward_iso` |
| `thm:generic_flatness` | `AlgebraicGeometry.genericFlatness` |
| `def:hilbert_polynomial` | `AlgebraicGeometry.Scheme.hilbertPolynomial` |
| `def:quot_functor` | `AlgebraicGeometry.Scheme.QuotFunctor` |
| `def:grassmannian_scheme` | `AlgebraicGeometry.Scheme.Grassmannian` |
| `thm:grassmannian_representable` | `AlgebraicGeometry.Scheme.Grassmannian.representable` |

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean` — flat base change for `f₊` (i = 0)
- `AlgebraicJacobian/Picard/RelativeSpec.lean` — relative Spec (existence, universal property, affine base)
- `AlgebraicJacobian/Picard/QuotScheme.lean` — Hilbert polynomial, Quot functor, Grassmannian
- `AlgebraicJacobian/Picard/FlatteningStratification.lean` — generic flatness
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
