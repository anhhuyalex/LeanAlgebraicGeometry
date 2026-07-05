All consistent — the remaining `0AVF`/`cor:regular_cohen_macaulay` mentions are in my rewritten remark, which now correctly disclaims that route for Milne 3.1 and points to where AB legitimately enters (Milne 3.3). The `\uses` edge is gone; proof blocks balanced.

## Summary

Reconcile of the latest Horizon work (`0022-horizon-T9`, the function-field pullback bridge) plus a blueprint honesty/DAG fix. The T9 additions are sound and axiom-clean; I closed a long-standing blueprint drift that had carried a phantom dependency edge, and flagged uncommitted concurrent-run work on the Picard leaf.

## Progress
- RationalMapFunctionField.lean: no change; Ground-verified `functionFieldPullback` axiom-clean `[propext, Classical.choice, Quot.sound]` via `lean_verify`; blueprint pins are 1-to-1.
- Albanese_CodimOneExtension.tex: `thm:codim_one_extension` proof rewritten to valuative-only (matches Lean); dropped phantom `\uses{cor:regular_cohen_macaulay}`; retargeted `rmk:codim1_role_of_ab`; committed `899e4d2e`.
- CodimOneExtension.lean: no change; verified `indeterminacy_codimGe2_of_smooth_of_complete` axiom-clean, so the new proof `\leanok` is honest.
- roadmap ALB.codim1: added key-advance comment (function-field bridge + blueprint reconcile).
- memory/t9-albanese-endgame-unblock-map.md: marked the blueprint-debt bullet resolved.
- recommendation.md: written (Albanese bridge, Milne-3.3 frontier, blueprint fix, concurrent picrep WIP).

## Issues
- **Uncommitted concurrent drift:** `Picard/GrassmannianRepresentability.lean` + new `GrassmannianZariskiSheaf.lean` (`grassmannian_isZariskiSheafOver`, sorry-free on disk) were modified ~12:52 UTC by another run and are **unbuilt (oleans missing) → unverified**. Left untouched (racing it would be wrong); noted in `recommendation.md`. "0 sorries" here ≠ proved.
- Inbox has 12 open `memory` items + 1 issue (slightly over the ~10 target); each maps to a live open frontier (FBC, picrep, A.3, Albanese), so I did not force-prune. Did not add to it.
- leandag cache is stale w.r.t. the removed `cor:regular_cohen_macaulay → thm:codim_one_extension` edge; a `horizon leandag` refresh next run will drop it.
- No full `lake build` run this session (blueprint + memory edits only; the two Albanese theorems verified via `lean_verify`).

## Why I stopped
Task complete: the opening/reconcile pass is done — latest Horizon work verified and blueprint/roadmap/memory reconciled to the real state, with the one integrity finding (concurrent picrep drift) surfaced rather than absorbed.
- The T9 leaf was already axiom-clean and needed only verification, not repair.
- The Grassmannian drift is another run's live, unbuilt working tree; committing or building it is not mine to do and would race their edits.

## Next
- After the concurrent picrep run commits, verify whether `Grassmannian.representable` closes (build + `#print axioms`) and update `AJC.picrep`.
- Albanese: the Milne 3.3 leaf (`CodimOneExtension.lean:1721`) still needs new `RationalMap` primitives (products + open-dominant precomposition + germ criterion) — multi-session greenfield.
