# Strategy Critic Report

## Slug
iter-012-strategy-critic

## Iteration
012

## Routes audited

### Route: appendix-first height route

- **Goal-alignment**: PASS — The route reaches the three named final theorem families and keeps the shared intermediate height/geometry inputs the goal explicitly asks for.
- **Mathematical soundness**: PASS — The dependency chain is coherent: universal geometry -> Betti/height package -> Néron-Tate distance -> counting.
- **Sunk-cost reasoning detected**: no
- **Infrastructure-deferral detected**: no
- **Phantom prerequisites**: `CanonicalHeight` / Néron-Tate canonical-height API; `IsNef` / `IsBig` positivity API. Mathlib does have projective-space and number-field heights plus pullback/analytic basics, but not these abstractions.
- **Effort honesty**: under-counted — the setup, Betti, and height phases are far larger than 2-4 iters each if the moduli/Jacobian stack is not already present; the plan looks optimistic by at least a factor of 2.
- **Parallelism under-exploited**: yes — rational-point counting and torsion-packet counting are bundled into one final lane even though they look separable after the shared height/distance lemmas.
- **Verdict**: CHALLENGE

## Format compliance

- **Size**: 41 lines / 3558 bytes — within budget.
- **Headings**: PASS — `Goal`, `Phases & estimations`, `Routes`, `Open strategic questions`, `Mathlib gaps & new material`.
- **Per-iter narrative detected**: no
- **Accumulation detected**: no
- **Table discipline**: PASS — both tables match the canonical column sets and stay one-line-per-cell.
- **Format verdict**: COMPLIANT

## Prerequisite verification

- `NumberTheory.Height.Projectivization.logHeight`: VERIFIED
- `NumberTheory.Height.NumberField.logHeight`: VERIFIED
- `Scheme.Pullback` / `pullback`: VERIFIED
- `AnalyticOnNhd` / `AnalyticAt`: VERIFIED
- `CanonicalHeight`: MISSING
- `IsNef`: MISSING
- `IsBig`: MISSING

## Alternative routes

### Alternative: abstract counting-first interface

- **What it looks like**: Formalize the quantitative Vojta/Mumford counting and height decomposition on a black-box Jacobian/abelian-scheme interface first, with the Betti-map and universal-family internals hidden behind narrow wrappers.
- **Why it might be cheaper or sounder**: It isolates the combinatorial counting core from the fragile geometry and could validate the final bounds earlier.
- **What the current strategy may have rejected**: Probably the desire to follow the paper's appendix order and reuse the same geometry for all final theorem families.
- **Severity of the omission**: major

## Must-fix-this-iter

- Route appendix-first height route: CHALLENGE — raise the effort estimates and split out the missing canonical-height / positivity infrastructure explicitly, or explain why the current scope is still credible.
- Route appendix-first height route: CHALLENGE — split the final rational-point and torsion-packet counting work into separate lanes, or justify the serialization.
