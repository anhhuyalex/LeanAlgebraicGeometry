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

**`MR4419629SquarefreeValuesOfPolynomialDiscriminantsI/Basic.lean`** — Blueprint: `chapters/Overview.tex` (all 47 declarations)

Phase 1 (statements-first). The prover should:

1. Define `naturalDensity` using `Filter.Tendsto atTop` on the ratio sequence for height-ordered polynomial families.
2. Write sorry-bodied `theorem squarefreeDiscDensity` (Thm 1.1) and `theorem maximalOrderDensity` (Thm 1.2) with correct types that typecheck.
3. Write sorry-bodied `corollary monogenicFields` (Cor 1.3) and `corollary shortestVector` (Cor 1.4).
4. Define the height function `height : (Polynomial ℤ) → ℝ`.
5. State the two sorry-axioms: `axiom ekedahlSieve` and `axiom geometryOfNumbersCount`.

The main goal is for all theorem statement types to typecheck (even with sorry bodies). Definitions may use sorry initially.

**Blueprint:** `blueprint/src/chapters/Overview.tex`
**Goal nodes:** `thm:squarefree_disc_density`, `thm:maximal_order_density` (and via them: `cor:monogenic_fields`, `cor:shortest_vector`)
**Density type decision:** `Filter.Tendsto atTop` on `fun X ↦ (Finset.card {f ∈ S | height f < X} : ℝ) / (Finset.card {f ∈ monicPolySpace n | height f < X} : ℝ)`.

## Per-file state

| File | State | Chapter | Key declarations |
|------|-------|---------|------------------|
| `Basic.lean` | EMPTY — ready for Phase 1 | `Overview.tex` | all 47 blueprint decls |
