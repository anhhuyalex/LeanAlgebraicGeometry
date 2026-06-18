# Project Progress

## Current Stage
autoformalize

## Stages
- [x] init
- [x] dag (iter-001 COMPLETE — 50 nodes, 136 edges, 0 isolated, 0 gaps)
- [ ] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives
- P0 prover: formalize `def:base-curve` (HSW.BaseCurve) first — impact 49, deps 0.
- P0 prover: proceed along dependency frontier (`def:etale-cover`, `def:serre-dual-vb`, etc.)
- When P0 types committed: run **P1 ∥ P2 ∥ P3a** provers in parallel (none depends on the others).
- P1 note: after Cho–Yamauchi, define `Ẽ_a` constructively as `∏_v Den(T, L_v, s)` to discharge P0 sorry-body.
- Reference needed: Kudla 1997 §4 for `lem:fourier-coeff-factorization` (P1).

## DAG Status (iter-001)
- 50 blueprint nodes across 6 chapters (Overview, Geometric_Side, Hermitian_Springer, Perverse_Sheaves_K, Wd_Representations, Assembly)
- 136 dependency edges
- 0 gaps, 0 isolated, 0 ∞-effort, 0 broken \uses{}, 0 missing \lean{} labels
- Ready to formalize: `def:base-curve` (impact 49)

## Phase Status
| Phase | Blueprint | Lean |
|-------|-----------|------|
| P0: Setup & statement | ✅ complete (25 nodes in Overview.tex) | 0% |
| P1: Local density theory | ✅ complete (embedded in Overview.tex) | 0% |
| P2: Geometric side | ✅ complete (7 nodes in Geometric_Side.tex) | 0% |
| P3a: Herm Springer | ✅ complete (4 nodes in Hermitian_Springer.tex) | 0% |
| P3b: Perverse sheaves 𝒦 | ✅ complete (6 nodes in Perverse_Sheaves_K.tex) | 0% |
| P3c: W_d representations | ✅ complete (7 nodes in Wd_Representations.tex) | 0% |
| P3d: Assembly | ✅ complete (2 nodes in Assembly.tex) | 0% |
