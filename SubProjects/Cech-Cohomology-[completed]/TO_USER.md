<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **`lake build` now SUCCEEDS — whole project, 0 sorries** (`Build completed successfully (8343 jobs)`,
  `✔ Built AlgebraicJacobian`). Two blockers fixed: (1) `CechSectionIdentificationLegTop` —
  `pushPull_interLegHom_resid`/`_sections` hit a `(kernel) deterministic timeout` (the kernel
  symbolically unfolds `coverInterOpen = ⨅ coverOpen` over the variable-length face, ~1.9M heartbeats
  measured) — bumped `maxHeartbeats 1.6M → 4M` on those two lemmas. (2) `CechToHigherDirectImage`
  (capstone, never built before) — the `F ≅ cycles 0` iso proof had real `rw`-matching bugs (def-eq
  `≫`/`lift`-arg casts) plus a `whnf` grind; fixed with `set hom/inv` + term-mode `Eq.trans`/`congrArg`.
- **Note (not done):** LegTop's `resid`/`sections` still take ~10 min each in the kernel — intrinsic to
  the section-identification routing through module-level adjunction units over `coverInterOpen`.
  Genuinely speeding that up needs a multi-file presheaf-level redesign; flagged, not attempted, to
  avoid destabilizing the broader Čech development.
