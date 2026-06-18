# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] dag (iter-001 complete — 24 nodes, 55 edges, 0 ∞-effort, gate cleared 2026-06-18)
- [ ] prover
- [ ] polish

## Current Objectives

Blueprint phase complete. Prover phase begins at iter-002.

### Priority lanes (parallel — independent)

**Lane A: Combinatorial foundations** (~300–600 LOC, ~4 iters)
- `def:delta-n` → `EigenvalueSimplex` (Mathlib: `YoungDiagram`, `Finset`, `Matrix`)
- `def:gromov-witten-number` → `GromovWittenNumber` (introduce abstractly)
- `thm:abw` → `abw_inequalities` (**sorry-bounded**)
- `lem:pinky` → `vertices_lie_on_regular_faces` (combinatorial — prove fully)
- `def:f-vertex` → `IsFVertex`
- `def:multiplicative-eigenvalue-polytope` → `MultiplicativeEigenvaluePolytope`

**Lane B: Local systems definitions** (~200–400 LOC, ~3 iters)
- `def:local-system` → `LocalSystem`
- `def:irreducible-local-system` → `IsIrreducible`
- `def:rigid-local-system` → `IsRigid`
- `def:unitary-local-system` → `IsUnitary`
- `def:monodromy-data` → `MonodromyData`

After both lanes complete: Strange duality map, Main bijection (sorry-bounded), KatzQ.

### Sorry-axiom set (Route B — do NOT prove these)
- `abw_inequalities`
- `IsFLineBundle`
- `strangeDuality_mem_polytope`
- `egregium` proof body
- `propertyP` proof body

### Key Mathlib names to verify before prover dispatch
- `YoungDiagram.transpose` vs `Partition.conjugate` — check via LSP before Strange duality phase
- `GL (Fin n) R` = `Units (Matrix (Fin n) (Fin n) R)` for local system matrices
