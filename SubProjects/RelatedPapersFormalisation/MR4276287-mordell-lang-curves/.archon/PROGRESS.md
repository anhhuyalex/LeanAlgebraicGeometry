# Project Progress

## Current Stage
dag

## Stages
- [x] init
- [ ] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives

Blueprint DAG is complete through iter-016:
- 56 blueprint nodes, 101 edges, 0 ∞-effort nodes
- 1 Mathlib-backed (`thm:weil_height_mathlib`)
- 6 declarations ready to formalize (no Lean dependencies):

| Label | Chapter | Impact |
|-------|---------|--------|
| `def:level_structure` | ModuliSpace | 41 downstream |
| `def:jacobian_av` | Jacobian | 42 downstream |
| `def:Ag_level` | Torelli | 38 downstream |
| `def:isNef` | Positivity | 13 downstream |
| `def:isBig` | Positivity | 9 downstream |
| `lem:northcott_ht` | WeilHeight | 0 downstream |

Next step: create Lean source skeleton files for the 6 ready declarations,
starting with highest-impact (`def:jacobian_av` and `def:level_structure`).
The Jacobian chapter is the largest single risk — allocate 8-14 iters per STRATEGY.md.
