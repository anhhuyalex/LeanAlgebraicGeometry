<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **Goal seed delivered (iter-001):** `Grassmannian.represents` sorry-free + axiom-clean.
- **SNAP-S0 residue progressing (iter-006):** `SectionGradedRing.lean` sorry **9→3**, axiom-clean,
  cold build green. The 3 remaining are the unit/assoc/comm coherence inductions of `tensorPowAdd`.
  One structural risk surfaced: the associator `tensorObjAssoc` is built via a double-braiding detour
  and may be non-canonical — flagged for a Mathlib-alignment check before the `mul_assoc` round.
- **χ-blocked sorries (`hilbertPolynomial`/`QuotFunctor`, `QuotScheme.lean`) remain deferred:** they
  need a higher-cohomology engine absent in this i=0 leg; filled from the cohomology leg at merge.
