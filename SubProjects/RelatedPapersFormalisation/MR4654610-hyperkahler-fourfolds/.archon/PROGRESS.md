# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] dag
- [ ] prover
- [ ] polish

## DAG Iteration 001 — COMPLETE

Blueprint: 29 declarations, 48 edges, 0 ∞-effort nodes, 0 isolated.
Strategy: Route A (parameterized modules), 5-phase plan, axiom-first for deep geometry.
See `.archon/DAG_STATUS.md` and `.archon/iter/iter-001/dag.md` for full record.

## Current Objectives (Phase 1: Foundations)

Scaffold the Lean files with the Route A variable context and named `axiom` declarations:

1. **Create `Basic.lean`** — open namespace `HK`, declare the variable context:
   ```
   variable (V : Type*) [AddCommGroup V] [Module ℤ V]
     (q : QuadraticForm ℤ V) (c_X : ℚ)
     (integrate4 : V →ₗ[ℤ] V →ₗ[ℤ] V →ₗ[ℤ] V →ₗ[ℤ] ℤ)
   ```

2. **Declare foundational axioms** (not `sorry`):
   - `axiom HK.fujiki_rel` — Fujiki relation
   - `axiom HK.hrr_exists` — HRR polynomial existence
   - `axiom HK.period_map_surj` — period map surjectivity
   - `axiom HK.guan_betti` — Guan Betti number classification
   - `axiom HK.deformation_type_k3sq` — K3[2] deformation type predicate

3. **Verify Mathlib anchor** — before Phase 2a: `#check Polynomial.eval_intCast_map` in LSP.

4. **Target**: `lake build` succeeds (no sorries, no type errors) with ~200 LOC.

## Phase 2 (after Phase 1 builds)

Dispatch 5 parallel prover lanes for independent algebraic/combinatorial lemmas:
`HK.hrr_integral`, `HK.a_is_integer`, `HK.polynomial_parity`, `HK.sqrt_rationality`,
`HK.topologicalConstant`. Then Phase 2b: `HK.conjecture14_fourfold` (needs Guan axiom).

## Phase 3 (after Phase 2)

Main theorems: `HK.hrr_formula_fourfold`, `HK.k3_deformation_type`, `HK.ogrady_conjecture`,
`HK.lagrangian_fibration`.
