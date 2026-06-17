# DAG Elaboration — Iteration 016

**Date:** 2026-06-17  
**Project:** MR4276287-mordell-lang-curves (Uniformity in Mordell-Lang for curves)  
**Agent:** dag-elaboration

---

## Summary

Iteration 016 was a major expansion round. Starting from 25 blueprint nodes and 43 edges
with 20 ∞-effort (proof-missing) nodes, this iteration ended with 56 blueprint nodes,
101 edges, 0 ∞-effort nodes, and 0 isolated nodes. All mandatory targets were met.

---

## Starting state (after iter-015)

| metric | value |
|--------|-------|
| Blueprint nodes | 25 |
| Edges | 43 |
| ∞-effort nodes | 20 |
| Isolated nodes | 0 |
| Mathlib-backed | 0 |
| Ready to formalize | 1 |

---

## Work performed

### Phase 1 — Strategy review and proof-block dispatch (within iter)

**Strategy-critic** (subagent) reviewed STRATEGY.md and returned CHALLENGE verdict with one
REJECT-severity finding: Jacobian variety was listed as a Mathlib item but is CONFIRMED MISSING
from Mathlib (Mathlib's `WeierstrassCurve.Jacobian` is Jacobian coordinates for genus-1, not the
Jacobian abelian variety of a higher-genus curve). Four CHALLENGE findings on infrastructure
deferral were also reported.

**Response:** STRATEGY.md was completely rewritten:
- 15 phases (up from 7), with a dedicated Jacobian phase (est. 8-14 iters, 800-1400 LOC)
- Route 2 (sorry-first) contingency added
- Confirmed Mathlib gaps list expanded
- All four challenge findings addressed with explicit phase decomposition

**Blueprint-writer (basic)** added 16 `\begin{proof}...\end{proof}` blocks to
`MR4276287UniformityInMordellLangForCurves_Basic.tex`, covering all 16 non-definition
declarations that had ∞ effort.

**Blueprint-writer (main)** added 4 proof blocks to
`MR4276287UniformityInMordellLangForCurves.tex`, covering the 4 main theorem declarations.
An "External inputs" section was also added with 3 stub declarations
(`lem:northcott`, `lem:remond`, `thm:raynaud_mm`) to ground the proof-level `\uses{}` edges
for `thm:bd_rat_intro` and `thm:bd_tor_intro_nf`.

**Blueprint-reviewer** (subagent) audited the full blueprint and returned 14 findings, the
most critical being: 6 unstarted strategy phases had zero blueprint coverage. Four rendering
bugs (undefined macros) were also found and fixed immediately in `macros/common.tex`.

### Phase 2 — Six new chapter dispatch

Six blueprint-writer subagents were dispatched in parallel, each creating a new chapter:

| Chapter | Declarations | Lean target file |
|---------|-------------|-----------------|
| `ModuliSpace.tex` | 5 (`def:level_structure`, `def:Mg_level`, `def:universal_curve`, `prop:Mg_quasiprojective`, `lem:torelli_quasi_finite`) | `ModuliSpace.lean` |
| `Jacobian.tex` | 6 (`def:jacobian_av`, `lem:jacobian_ppav`, `def:abel_jacobi`, `thm:abel_jacobi_closed_immersion`, `def:faltings_zhang`, `lem:curve_generates_jacobian`) | `Jacobian.lean` |
| `Torelli.tex` | 5 (`def:Ag_level`, `def:universal_av`, `def:torelli_map`, `thm:torelli_injective`, `lem:universal_jacobian_fib`) | `Torelli.lean` |
| `WeilHeight.tex` | 6 (`thm:weil_height_mathlib` [\mathlibok], `lem:northcott_ht`, `def:height_fib`, `def:nt_height`, `prop:nt_quadratic`, `prop:nt_nonneg`) | `WeilHeight.lean` |
| `Positivity.tex` | 5 (`def:isNef`, `def:isBig`, `lem:nefIntersection`, `thm:siuCriterion`, `lem:nefFromBetti`) | `Positivity.lean` |
| `ArithBezout.tex` | 4 (`thm:arith_bezout`, `lem:bihomog_degree`, `lem:siu_intersection_lower`, `lem:siu_intersection_upper`) | `ArithBezout.lean` |

Total: **31 new declarations** across 6 chapters.

### Phase 3 — DAG wiring and content.tex update

Post-writer repairs performed by plan agent:

1. `blueprint/src/content.tex`: added `\input{}` for all 6 new chapters in topological order
   (ModuliSpace → Jacobian → Torelli → WeilHeight → Positivity → ArithBezout → Basic → Main).

2. `ArithBezout.tex`: fixed broken `\uses{..., def:nef}` references → `\uses{..., def:isNef}`
   (the Positivity writer used camelCase labels; ArithBezout directive used snake_case).

3. `ArithBezout.tex`: added proof block to `thm:arith_bezout` (writer left it without one,
   causing the single remaining ∞-effort node; fixed with a sorry-stub proof citing Autissier).

4. `MR4276287UniformityInMordellLangForCurves_Basic.tex`: 5 cross-chapter `\uses{}` wiring
   additions:
   - `def:ambient_setup`: added `def:Mg_level, def:universal_curve, def:Ag_level, def:universal_av, def:torelli_map, def:nt_height, def:height_fib`
   - `lem:moduli_height_comparison`: added `def:torelli_map`
   - `thm:silverman_tate`: added `def:nt_height, def:height_fib`
   - `prop:aux_ht_ineq`: added `thm:siuCriterion, lem:nefFromBetti, lem:siu_intersection_lower, lem:siu_intersection_upper, thm:arith_bezout`
   - `thm:nondeg_for_bd`: added `lem:curve_generates_jacobian, def:faltings_zhang`

---

## Ending state

| metric | value |
|--------|-------|
| Blueprint nodes | 56 |
| Edges | 101 |
| ∞-effort nodes | **0** |
| Isolated nodes | **0** |
| Broken uses edges | **0** |
| Mathlib-backed | 1 (`thm:weil_height_mathlib`) |
| Ready to formalize | 6 |
| Effort remaining (finite) | 56,101 chars |

---

## Key findings and decisions

- **Jacobian variety (CONFIRMED MISSING from Mathlib):** This is the largest risk item.
  `Mathlib.WeierstrassCurve.Jacobian` provides Jacobian *coordinates* for genus-1 curves
  only. The Jacobian as a g-dimensional abelian variety is project-specific. STRATEGY.md
  now reflects this with a dedicated phase (8-14 iters, 800-1400 LOC).

- **`\mathlibok` node:** `thm:weil_height_mathlib` in WeilHeight.tex was marked `\mathlibok`
  because Mathlib does have some Weil height infrastructure in `Mathlib.NumberTheory.Heights`.
  The exact declaration name needs verification against the current Mathlib API before use.

- **Positivity label convention:** The Positivity chapter writer used camelCase blueprint labels
  (`def:isNef`, `thm:siuCriterion`, `lem:nefFromBetti`) instead of snake_case as in the
  directive. This was left as-is; cross-chapter references updated to match.

---

## Blocker for iter-017

The Lean files do not yet exist (0 `\leanok` nodes, 56 unmatched `\lean{}`). The next
prover step is to create the Lean source skeletons for the 6 ready-to-formalize axioms:

```
leandag show ready
```

These are the declarations with no remaining dependencies — exactly the leaves of the DAG
that a prover can target immediately.
