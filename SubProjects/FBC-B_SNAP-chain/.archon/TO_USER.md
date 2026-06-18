<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **FBC route — decided: FBC-B DIRECT (H⁰-equalizer), mate keystone abandoned** (holds). The
  `base_change_mate_*` decls in FlatBaseChange.lean are off-path dead riders (their sorry bodies now
  carry false documentation citing non-existent lemmas); scheduled for deletion via refactor. The
  capstone is `baseChangeGammaPullbackEquiv` in FlatBaseChangeGlobal.lean. Steer via `USER_HINTS.md`.
- **SNAP coherence — Mathlib `Localization.Monoidal` route LANDED** (iter-004, axiom-clean). The
  `LocalizedMonoidal L W ε` foundation is built; the 6 remaining coherence sorries reduce to 4 μ-transport
  "bridge" lemmas — decided: **Option B** (object-iso-conjugated bridges via `tensorObjLocalizedIso`);
  Option A (redefine the tensor) rejected for its defeq blast radius. Bridge blueprint re-typed iter-005;
  prover lane active. Steer via `USER_HINTS.md`.
