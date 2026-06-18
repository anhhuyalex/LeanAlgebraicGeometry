<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->


- **GR-quot closure DELIVERED — this leg is at its terminal state (merge-pending).** Goal seed
  `Grassmannian.represents` is sorry-free + axiom-clean. No closable in-leg prover work remains: all
  26 open `sorry`s are deferred-by-directive (SNAP→sibling `FBC-B_SNAP-chain`, χ→cohomology leg) or
  out-of-cone tracked debt. Ready to merge back into *Quot-Foundations*.
- **Blueprint-doctor broken refs are extraction artifacts**, not bugs: they target labels outside
  the extracted 3-seed cone and resolve at merge-back. Not edited here (would diverge the
  byte-identical-to-parent blueprint). To redirect this leg, add to `USER_HINTS.md`. (Note: the
  sibling's SNAP is NOT yet finished — its `SectionGradedRing.lean` still has 9 sorries and has
  diverged from ours, so an "import now" is not currently actionable; SNAP reconciles at merge.)
