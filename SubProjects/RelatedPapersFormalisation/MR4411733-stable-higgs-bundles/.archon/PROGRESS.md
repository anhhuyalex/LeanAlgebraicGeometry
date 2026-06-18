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

No prover dispatch this iter — blueprint phase complete, entering autoformalize stage.
See iter/iter-001/dag.md for rationale.

The loop should next scaffold Lean declarations for the following parallel lanes:

### Lane A — Bialynicki-Birula theory
**`MR4411733VeryStableHiggsBundlesEquivariantMultiplicityAndMirrorSymmetry/Basic.lean`**
— Blueprint: `chapters/Overview.tex` (declarations: `def:semi_proj_variety`, `def:upward_flow`,
`def:downward_flow`, `def:attractor`, `def:weight_decomp`, `prop:BB_theory`)
Strategy: introduce abstract `SemiProjectiveVariety` structure with C*-action axioms, weight-space
decomposition of tangent spaces at fixed points, and statement of Prop 2.1 (BB isomorphism).

### Lane B — Character formula (independent of geometry)
**`MR4411733VeryStableHiggsBundlesEquivariantMultiplicityAndMirrorSymmetry/Basic.lean`**
— Blueprint: `chapters/Overview.tex` (declarations: `def:T_pos_module`, `def:T_char_sym`,
`lem:T_char_product`, `def:virtual_multiplicity`, `def:equivariant_multiplicity`)
Strategy: define positive T-modules as finitely-supported weight-indexed families, the character
of the symmetric algebra as a formal power series product, and prove the product formula
lem:T_char_product purely in `PowerSeries ℤ`.

### Lane C — Moduli space axioms
**`MR4411733VeryStableHiggsBundlesEquivariantMultiplicityAndMirrorSymmetry/Basic.lean`**
— Blueprint: `chapters/Overview.tex` (declarations: `def:Higgs_bundle`, `def:moduli_Higgs`,
`def:T_action_moduli`, `def:T_fixed_type`, `def:very_stable_Higgs`, `def:Hitchin_map`,
`def:nilpotent_cone`, `def:component_multiplicity`)
Strategy: axiom-first — declare M, h, N, m_F as `axiom` stubs with stated properties; no
construction attempt until the geometric realization phase.

## Per-file state

### MR4411733VeryStableHiggsBundlesEquivariantMultiplicityAndMirrorSymmetry/Basic.lean
- Status: stub (imports Mathlib only)
- Blueprint chapter: Overview.tex (all 33 declarations)
- Blueprint gate: PASS (complete + correct per iter-001 blueprint-writer + leandag)
- Next action: scaffold Lane A + Lane B + Lane C declarations (see above)
