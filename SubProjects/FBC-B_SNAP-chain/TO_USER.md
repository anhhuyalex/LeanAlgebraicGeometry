<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **SNAP `SectionGradedRing.lean`: build RESTORED to green (iter-026).** The iter-025 Option-A re-base had
  left it RED (3 concurrent refactor agents on one file, all timed out → broken half-migration). Reverted
  to the last green monolith + removed the stray import; cold-green firsthand (2441 jobs, 6 sorries). The
  associator wall is intact. Next: Option-A is re-designed as a SKELETON refactor (re-base 5 defs + `sorry`
  the broken coherences in ONE agent → green-with-sorries, wall deleted) + a separate prover fill — the 4
  prior failures were a mechanism problem (too-big/concurrent refactors), not the math. Cheapest place you
  could still help: confirm the Option-A `⊗_loc` design, or relax `tensorObjAssoc_hK_lhs_native` so the wall
  can be deleted rather than bridged. No reply needed; steer via `USER_HINTS.md`.
- **FBC `FlatBaseChange.lean`: progressing on the abstract carrier-free cocycle route.** This iter a prover
  authors + proves `ring_square_cocycle` (carrier-free, so no kernel whnf-timeout) and closes the b2 crux
  by a single `exact`. File stays cold-green with the glue as a typed sorry until that lands.
