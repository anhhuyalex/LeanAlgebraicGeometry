# To the User

## Status after iter-002

**Blueprint phase COMPLETE.** All 6 DAG completion criteria are satisfied. The `archon loop` prover phase can begin once the blueprint-reviewer's HARD GATE items below are cleared.

## What was done in iter-002

- Fixed all 12 empty `\uses{}` annotations that were crashing the blueprint builder
- Added proof sketches for the two missing corollaries (`cor:morph-tbirl`, `cor:cusp-bl2`)
- Found and corrected wrong arXiv IDs for the Bresciani-Vistoli reference papers
- Retrieved 4 reference papers now in `references/`:
  - `bv15-nori-gerbe` (arXiv:1204.1260) — étale fundamental gerbe
  - `bv19-fund-gerbes` (arXiv:1610.07341) — fundamental gerbes, Prop 3.9
  - `bv23-valuative` (arXiv:2210.03406) — valuative criterion (Theorem 3.1 for `ProrootValCrit`)
  - `tv18-rootstack` (arXiv:1410.1164) — infinite root stacks

## Before provers start: 3 mechanical items

The blueprint-reviewer flagged these as blocking the HARD GATE for prover dispatch:

1. **Citation format** (low effort): All 39 `% SOURCE:` lines in Overview.tex need a `(read from references/MR4688702-birational-section.tex)` parenthetical appended. One writer pass.

2. **3 missing references**: Papers needed to verify proof sketches for `prop:nffg`, `lem:nf-lift`, `thm:main-C`:
   - Bresciani "Sections of families of curves" arXiv:2003.04649 (cite key `[scfg]`)
   - Stix 2013 "Rational Points and Arithmetic of Fundamental Groups" (cite key `[sti15]`)
   - Saidí-Tyler arXiv:2109.05276 (cite key `[saty21]`)

3. **example:gm-loop** (minor): The `GmLoop` example should be converted to a `lemma` environment so it is properly tracked in the dependency graph.

The `archon loop` plan phase (iter-003) will handle items 1–3 automatically before dispatching any prover.
