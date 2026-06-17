# Project Progress

## Current Stage
dag

## Stages
- [x] init
- [ ] autoformalize
- [ ] prover
- [ ] polish

## Current Objectives

The blueprint (one consolidated chapter) is now mathematically complete:
- 0 nodes with ∞ effort
- 0 broken `\uses{}` references
- 0 isolated blueprint nodes
- All 21 blueprint declarations have `\lean{}` annotations

One structural issue remains before the DAG can declare COMPLETE:
- `Basic.lean` contains a placeholder stub `def hello := "world"` (1 lean_aux node with no blueprint entry).
  This stub has 0 impact and will be replaced when phase 0 prover work begins.

**Next prover task (Phase 0 — hypothesis skeleton):**
Replace `def hello := "world"` in `MR4258055BrillNoetherHurwitz/Basic.lean` with correctly-typed, sorry'd declarations for all 21 blueprint items in `MR4258055BrillNoetherHurwitz.lean`, matching the `\lean{}` names in the blueprint chapter. The three named axioms (Larson: `universalDegeneracyClasses`, theta-class: `thetaChernClasses`, smoothness: `smoothness`) should be declared as `axiom` rather than `sorry`. Once phase 0 is complete, all 21 blueprint `\lean{}` references will be matched and the blueprint will be fully 1-to-1.

See STRATEGY.md for the full phase roadmap (phase 0 → 1 → 2a → 2b+4 parallel → main theorem assembly).
