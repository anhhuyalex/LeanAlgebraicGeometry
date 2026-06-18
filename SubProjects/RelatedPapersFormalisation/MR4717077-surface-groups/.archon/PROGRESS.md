# Project Progress

## Current Stage
autoformalize

## Stages
- [x] init
- [x] dag (blueprint complete — DAG_STATUS.md: COMPLETE)
- [ ] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives

### Foundations phase — set up base definitions in Lean

**`MR4717077CanonicalRepresentationsOfSurfaceGroups/Basic.lean`** — Blueprint: `chapters/Overview.tex`

Priority order (foundations first, then elementary results, then axioms):

1. **Foundations** (formalize first — unblock everything else):
   - `def:surface-group` (`SurfaceGroup`) — finitely-presented group presentation
   - `def:mapping-class-group` (`MappingClassGroup`) — as a group acting outerly on surface group
   - `def:mcg-finite` (`MCGFinite`) — predicate on representations

2. **Elementary algebraic results** (provable from definitions):
   - `prop:mcg-finite-basic` (`mcgFinite_directSum`) — direct sums/tensor products/subquotients
   - `lem:birman-exact-sequence` (`BirmanExactSequence`) — state the exact sequence as an axiom initially
   - `cor:free-groups` (`freeGroup_finiteImage`) — prove from `thm:finite-image` once available

3. **Deep analytic axioms** (introduce as Lean `axiom` declarations):
   - `thm:period-map` (`periodMap_derivative`) — axiom, Hodge theory
   - `thm:rank-bound-subsystem` (`rankBound_subsystem`) — axiom
   - `thm:cohomologically-rigid-integral` (`cohomRigid_isIntegral`) — axiom (EG18/KP20b)
   - `thm:nah-unitarity` (`nah_unitarity`) — axiom ([LL22] Thm 1.2.12)
   - `prop:mcg-finite-family` (`mcgFinite_of_localSystem`) — axiom (étale homotopy)

4. **Main theorem scaffold** (sorry-bodies connecting axioms):
   - `thm:cohomological-vanishing`, `lem:tensor-product-unitary`
   - `lem:isomonodromy-rigidity`, `prop:unitary-case`, `thm:semisimple-case`
   - `thm:putman-wieland-asymptotic`, `lem:semisimplicity`
   - `thm:finite-image` (main goal, sorry until all dependencies are closed)
