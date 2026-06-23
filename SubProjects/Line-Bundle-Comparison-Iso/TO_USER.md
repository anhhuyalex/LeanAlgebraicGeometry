<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **Terminal cone advancing, S4b crux narrowing (iter-057).** `TensorObjInverse.lean` is `lake build` EXIT 0,
  4 sorries. The S4b tensor flank rides ONE lemma `pullbackTensorMap_left_unitality`; iter-057 closed 3 of its
  4 sub-links (3 new proven lemmas + the sheafified coherence wired in), leaving a single B1-scale residual
  (the η-whisker + λ legs). Sorry count held at 4 — genuine structural progress but not yet closure; next iter
  effort-breaks the residual into two smaller pieces. **Decision held:** do NOT register `pullback` as a
  monoidal functor (globally false + useless for duals); use the bespoke Cone A (tensor) / Cone B (dual) routes.
- The dual flank S3/S4a (Cone B) is now effort-broken + prover-ready (a SEPARATE internal-hom base-change
  construction); queued for the iter after S4b closes (same file, so the lanes run sequentially). The
  trivialisation telescope follows. Seed-1 + Seed-2 remain delivered. No user action needed — steer via
  `USER_HINTS.md` if desired.
