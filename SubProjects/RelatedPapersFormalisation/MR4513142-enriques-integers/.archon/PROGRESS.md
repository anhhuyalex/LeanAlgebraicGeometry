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

The blueprint is complete (DAG_STATUS: COMPLETE). The prover loop should begin by scaffolding Lean declarations for the blueprint's 15 nodes.

**Priority order** (by impact, ready-to-formalize first):

1. **`Basic.lean`** — Blueprint: `chapters/Overview.tex`
   - `def:picard-scheme` (impact 12, ready) — `MR4513142ThereIsNoEnriquesSurfaceOverTheIntegers.PicardScheme`
   - `def:pic-tau` (impact 11, ready after picard-scheme) — `MR4513142ThereIsNoEnriquesSurfaceOverTheIntegers.PicTau`
   - `def:num-local-system` (impact 10) — `MR4513142ThereIsNoEnriquesSurfaceOverTheIntegers.NumLocalSystem`
   - `lem:spec-Z-simply-connected` (impact 2, ready) — `TODO.minkowskiSimplyConnected`
   - `lem:br-Z-vanishes` (impact 2, ready) — `TODO.brauerZVanishes`
   - `def:enriques-surface` (impact 9) — `IsEnriquesSurface`
   - `def:family-enriques-surfaces` (impact 7) — `IsFamilyOfEnriquesSurfaces`
   - `def:exceptional-enriques` (impact 3) — `IsExceptionalEnriquesSurface`
   - `def:constant-picard` (impact 5) — `HasConstantPicardScheme`
   - `prop:constant-picard-over-Z` (impact 1) — `constantPicardScheme`
   - `thm:no-exceptional-over-Z4` (impact 1) — `noExceptionalOverZ4` (**sorry-axiom A1**: cite [Schröer 2021b])
   - `thm:family-with-constant-pic` (impact 2) — `hasGenusOneFibration`
   - `thm:classification-weierstrass` (impact 2) — `classificationWeierstrassEqns`
   - `thm:no-non-exceptional-over-F2` (impact 1) — `noNonExceptionalOverF2`
   - `thm:no-enriques-over-integers` (impact 0, goal) — `noEnriquesSurfaceOverIntegers`

## Key sorry-axioms to track

- **[A1]** `noExceptionalOverZ4`: cites [Schröer 2021b], Thm 7.2. External; accept as axiom.
- **[A2]** Fontaine/Abrashkin Hodge-number restriction: used in proof of `constantPicardScheme`; not in Mathlib.
- **[A3]** Picard scheme representability (Artin 1969): foundational; candidate for Mathlib PR.
- **[A4]** Galois cohomology H¹(k, P) for group schemes: needed for local-system lemmas.
