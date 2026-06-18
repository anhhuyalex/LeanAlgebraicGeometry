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

### MR4792069ThePwConjectureForGln/Basic.lean

**Goal:** Create sorry-gated Lean stubs for all 8 declarations in the blueprint (Overview chapter).

Priority order:
1. **P3 (main theorem sorry-skeleton):** Introduce an opaque ℚ-module `CohomologyGroup (m : ℕ)` and a `Filtration` structure (`ℤ → Submodule ℚ V`, monotone). State `PEqualsW` as an equality of `Submodule ℚ (CohomologyGroup m)` terms (sorry body).
2. **Sorry-gated definitions:** `SmoothProjectiveCurve`, `CharacterVariety`, `DolbeaultModuli`, `HitchinFibration`, `PerverseFiltration`, `WeightFiltration`, `StrongPerversity` — all sorry-gated opaque definitions. `PerverseFiltration` and `WeightFiltration` are permanent sorry-axioms (perverse sheaves / mixed Hodge theory are not Mathlib-plausible near-term).
3. **P1 (filtration framework, sorry-free):** Implement `structure Filtration` building on `Mathlib.RingTheory.FilteredAlgebra.Basic` (`IsModuleFiltration`). This is the only P1 content that should be sorry-free in this file.

Blueprint chapter: `blueprint/src/chapters/Overview.tex`

Lean names to create (matching blueprint \lean{} annotations):
- `MR4792069ThePwConjectureForGln.SmoothProjectiveCurve`
- `MR4792069ThePwConjectureForGln.CharacterVariety`
- `MR4792069ThePwConjectureForGln.DolbeaultModuli`
- `MR4792069ThePwConjectureForGln.HitchinFibration`
- `MR4792069ThePwConjectureForGln.PerverseFiltration`
- `MR4792069ThePwConjectureForGln.WeightFiltration`
- `MR4792069ThePwConjectureForGln.StrongPerversity`
- `MR4792069ThePwConjectureForGln.PEqualsW`

Key Mathlib: `Mathlib.RingTheory.FilteredAlgebra.Basic` (IsModuleFiltration), `Mathlib.LinearAlgebra.Submodule.*`

## Per-file State

### MR4792069ThePwConjectureForGln/Basic.lean
- Blueprint: blueprint/src/chapters/Overview.tex (complete, 8 declarations)
- Lean declarations: 0 (stubs to be created)
- Sorry count: 0 (stubs not yet created)
- Status: READY — blueprint gate cleared (complete + correct per iter-001 writer report)
