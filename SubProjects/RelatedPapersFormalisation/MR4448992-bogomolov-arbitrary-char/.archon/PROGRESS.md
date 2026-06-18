# Project Progress

## Current Stage
autoformalize

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives

Begin Phase 1: Definitions and setup. The blueprint is complete (DAG_STATUS: COMPLETE).
The prover loop should start with the 11 root nodes (deps = 0), which are all ready to formalize:

- `def:ProjectiveModel` — projective model of K/k (impact 15, highest priority)
- `def:ChowGroup` — Chow group with Q-coefficients (impact 10, parallel to Phase 1)
- `def:KkTrace` — K/k-trace of an abelian variety (impact 9)
- `def:TorsionSubvariety` — torsion subvariety a + C (impact 8)
- `def:MultiSection` — multi-section of an abelian scheme (impact 8)
- `def:RigidifiedLineBundle` — rigidified line bundle (impact 7)
- `def:ExcessLocus` — excess locus for a morphism (impact 6)
- `lem:isoBaseChange` — isogeny descends from K to k (impact 6)
- `pro:bertini` — Bertini-type result (impact 5)
- `lem:subvarDef` — descent of subvariety via two subfields (impact 5)
- `def:AdditionMap` — image of the addition map (impact 5)

The Lean file to work on:
`MR4448992GeometricBogomolovConjectureInArbitraryCharacteristics/Basic.lean`

Note: Since Mathlib has no abelian-scheme API, canonical-height theory, or Chow groups,
all Phase 1 and Phase 2 work is new infrastructure. Prover work should start with
`def:ProjectiveModel` and `def:ChowGroup` in parallel lanes (they are independent).

## File Status

| File | Blueprint | Sorries | Notes |
|------|-----------|---------|-------|
| `MR4448992GeometricBogomolovConjectureInArbitraryCharacteristics/Basic.lean` | Overview.tex | 0 | Empty; needs all declarations scaffolded |
| `MR4448992GeometricBogomolovConjectureInArbitraryCharacteristics.lean` | Overview.tex | 0 | Entry point; imports Basic |
