# Mr2223407 Construction Hilbert Quot

<!-- archon:readme -->
<!-- Claude fills in the prose sections below. Keep the section headers. -->

## Project

This project formalizes, in Lean 4 / Mathlib, Nitin Nitsure's lecture notes
*Construction of Hilbert and Quot Schemes* (MR2223407, arXiv:math/0504590). The
terminal goal is the representability of the projective Quot functor
`Quot_{E/X/S}^{Φ,L}` by a projective `S`-scheme (Grothendieck's theorem, in the
Altman–Kleiman form), together with its corollaries: the Hilbert scheme, the
scheme of morphisms, and quotients by flat projective equivalence relations. The
construction passes through Castelnuovo–Mumford regularity, cohomology and base
change, and the flattening stratification. Much of the underlying machinery is at
or beyond the current Mathlib frontier and is tracked as cited foundational
anchors; see `.archon/STRATEGY.md` and the `blueprint/` roadmap.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

- `MR2223407ConstructionHilbertQuot/` — main Lean source
- `blueprint/` — leanblueprint source (build with `leanblueprint pdf` and `leanblueprint web`)
- `references/` — PDFs, papers, and informal notes backing the formalization
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
