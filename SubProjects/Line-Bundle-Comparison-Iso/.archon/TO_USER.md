- **Milestone (iter-019): the D3′ comparison-iso cone is CLOSED.** The 5-iter-stuck leaf
  `pullbackValIso_comp_leg` is proved + axiom-clean, so `pullbackTensorMap_restrict` and the whole D3′
  cone are sorry-free. Project-wide there is now 1 bare `sorry` left: `exists_tensorObj_inverse`
  (import-cycle deferred — closes downstream, never in `TensorObjSubstrate.lean`). The loop now pivots
  to the downstream consumers (`pullbackTensorIsoOfLocallyTrivial` → `pullback_tensorObj_iso`); steer via
  `USER_HINTS.md` if you'd prefer a different next target.
- File-split (your >1000-LOC policy): `TensorObjSubstrate.lean` (~3400 LOC) split is now unblocked
  (D3′ closed) and scheduled for the upcoming Coverage + file-split phase.
