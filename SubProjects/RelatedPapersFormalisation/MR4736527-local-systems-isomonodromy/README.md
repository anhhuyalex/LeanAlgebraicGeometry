# Mr4736527 Local Systems Isomonodromy

<!-- archon:readme -->
<!-- Claude fills in the prose sections below. Keep the section headers. -->

## Project

This project formalizes results from "Geometric local systems on very general curves
and isomonodromy" by Aaron Landesman and Daniel Litt (MR4736527, arXiv:2202.00039).
The paper proves that the minimum rank of a non-isotrivial local system of geometric
origin on a suitably general $n$-pointed curve of genus $g$ is at least $2\sqrt{g+1}$,
resolving conjectures of Esnault–Kerz and Budur–Wang. The main technical input is an
analysis of the stability properties (Harder–Narasimhan filtration) of flat vector
bundles with regular singularities under isomonodromic deformation, which also answers
questions of Biswas, Heu, and Hurtubise. The formalization target spans the
Hodge-theoretic main results (constraints on variations of Hodge structure on very
general curves) and the underlying isomonodromy/semistability machinery.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

- `MR4736527GeometricLocalSystemsOnVeryGeneralCurvesAndIsomonodromy/` — main Lean source
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
