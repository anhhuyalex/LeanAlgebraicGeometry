# AlgebraicJacobian — Čech computation of higher direct images (Cech-Cohomology subproject)

<!-- archon:readme -->

## Project

A formalization in Lean 4 + Mathlib of the **Čech computation of higher direct images**
of a quasi-coherent sheaf. The headline result is
`AlgebraicGeometry.cech_computes_higherDirectImage`: for a separated, quasi-compact morphism
`f : X ⟶ S` of schemes, a quasi-coherent `O_X`-module `F`, and a finite affine open cover `𝒰`
of `X` (so all intersections are again affine), the cohomology sheaves of the relative Čech
complex `Č•(𝒰, F)` are canonically isomorphic to the higher direct images `Rⁱ f_* F` wherever
the derived functor is defined.

The point of the construction is that it is **unconditional**: it computes `Rⁱ f_*` as the
cohomology of an explicit complex of quasi-coherent sheaves built from pushforwards over the
finite intersections of the cover, without appealing to enough injectives in the category of
sheaves of modules. The development supplies the Čech nerve and complex of an affine cover, the
`pushPull` transport machinery, affine acyclicity (Serre vanishing), and the comparison theorem.

This subproject was **extracted** (via `archon extract`) from the larger Algebraic-Jacobian
challenge, where this Čech engine is the cohomological substrate underneath the FGA
representability of the relative Picard scheme. Lean module names and blueprint labels are kept
identical to the parent so proved results can be merged back.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean` — the Čech nerve/complex, the
  `pushPull` machinery, affine acyclicity, and `cech_computes_higherDirectImage`
- `AlgebraicJacobian/Cohomology/HigherDirectImage.lean` — the derived-functor `Rⁱ f_*`
  (compile-time dependency of the comparison theorem)
- `blueprint/` — leanblueprint source (build with `leanblueprint pdf` and `leanblueprint web`)
- `references/` — Stacks Project source (Cohomology of Schemes) backing the formalization
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
