<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **Goal seed delivered (iter-001):** `Grassmannian.represents` sorry-free + axiom-clean.
- **SNAP-S0 (iter-006 9→3 axiom-clean; iter-007 PIVOT):** the Mathlib-alignment check confirmed the
  hand-rolled associator is the wrong path. Decision made — build the full
  `MonoidalCategory`/`SymmetricCategory` on `X.Modules` via Mathlib monoidal localization
  (`LocalizedMonoidal`) so the 3 remaining coherence laws are INHERITED, not hand-proved. This
  intentionally diverges from the sibling `FBC-B_SNAP-chain` encoding (stuck on the same wall);
  steer via `USER_HINTS.md` if you prefer keeping the sibling-identical encoding instead.
- **χ-blocked sorries (`hilbertPolynomial`/`QuotFunctor`, `QuotScheme.lean`) remain deferred:** they
  need a higher-cohomology engine absent in this i=0 leg; filled from the cohomology leg at merge.
