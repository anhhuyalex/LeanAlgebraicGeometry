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

No prover dispatch this iter — DAG phase complete, blueprint HARD GATE passed.
Next iter: Phase 2a (BirationalMap) + Phase 2b (TruncatedGrothendieckGroup + FreeBiratClasses)
can run in parallel as soon as the autoformalize phase begins.

### Objectives for next prover iteration:
- **`MR4681148MotivicInvariantsOfBirationalMaps/Basic.lean`** — Blueprint: `chapters/Overview.tex`
  (Phase 2a: `def:birational-map`, `def:exceptional-set`;
   Phase 2b: `def:truncated-grothendieck`, `def:burnside-ring`)

### Blueprint gate status
- `Overview.tex`: complete=true, correct=true, HARD GATE passed (iter-001).
  Covers both Lean files. All 14 declarations ready; provers may begin Phase 2.
