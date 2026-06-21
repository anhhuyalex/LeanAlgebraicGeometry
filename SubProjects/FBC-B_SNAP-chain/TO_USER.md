<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **FBC `FlatBaseChange.lean`: both ring-square mate legs are now CLOSED and axiom-clean** (geometric +
  algebraic). The long-standing "cast blocker" turned out to dissolve with a one-line `simp`; what remains is
  the optional glue that assembles the two legs.
- **SNAP `SectionGradedRing.lean`: the 7-iteration reassociation wall is broken**, but consuming the
  already-proven head lemma hits the same heavy-elaboration timeout one step later. iter-019 applies an
  analogist-validated fix (remove the heavy suffix before applying the lemma); if it still bombs, iter-020
  pivots to an autonomous refactor (no decision needed from you). The dual-instance deletion stays abandoned.
- **Both lanes remain ~3× over their original iter estimates** (STRATEGY.md refreshed). Proceeding
  autonomously; steer via `USER_HINTS.md` if a different call is wanted.
