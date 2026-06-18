# Project Progress

## Current Stage
autoformalize

## Stages
- [x] init
- [x] dag (blueprint complete — see DAG_STATUS.md)
- [ ] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives

Scaffold all Lean declarations in `MR4433080HitchinFibrationsAbelianSurfacesAndThePwConjecture/Basic.lean`.

**Blueprint:** `chapters/Overview.tex` (all 22 declarations: `def:PervFiltration` through `lem:taut_weight`)

**Priority order** (by leandag impact ranking):
1. `HitchinPW.HitchinModuliDol` — Blueprint: `def:HitchinModuliDol` (impact 11; root dependency for Hitchin fibration and non-abelian Hodge)
2. `HitchinPW.PerverseFiltration` — Blueprint: `def:PervFiltration` (impact 8; root dependency for all theorems)
3. `HitchinPW.CharacterVariety` — Blueprint: `def:CharacterVariety` (impact 7; needed for weight filtration and non-abelian Hodge)
4. All remaining 19 declarations in dependency order (see Overview.tex)

**Scaffolding notes:**
- All 9 root-type stubs (`HitchinModuliDol`, `CharacterVariety`, `PerverseFiltration`, `WeightFiltration`, `NonabelianHodgeDiffeo`, `HodgeTateDecomp`, `ModuliSheaves`, `PervSplitting`, `TwistedUniversalFamily`) must be introduced as `noncomputable def ... := sorry` — these involve infrastructure not in Mathlib.
- The four main theorems (`PW_genus2`, `PW_even`, `oddTautPerversity`, `PW_iff_multiplicativity`) require all type stubs in place before their signatures can be written.
- After common scaffold is complete, the four theorem lanes are **independent and parallelizable**.
