# Project Progress

## Current Stage
autoformalize

## Stages
- [x] init
- [x] dag
- [ ] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives

The blueprint is COMPLETE (iter-001). The `archon loop` should begin formalizing from the combinatorial foundations. Primary near-term target: crystal theorem (Thm 1.6 = `thm:crystal`).

Lane A (combinatorial + crystal):
- **`MR4433079IntersectionComplexesAndUnramifiedLFactors/Basic.lean`** — Blueprint: `chapters/Overview.tex` — Start with `def:reductive-group-data`, `def:spherical-variety`, `def:colors-monoid`, `def:type-T-condition` (combinatorial foundations, no sheaf theory required). Use Mathlib's `RootSystem` (`Mathlib.LinearAlgebra.RootSystem.Basic`) for the cocharacter lattice.

## Blueprint

- `blueprint/src/chapters/Overview.tex` — consolidated chapter covering both Lean files (21 declarations)
- Strategy: axiom-first for sheaf infrastructure; crystal theorem as primary near-term target
