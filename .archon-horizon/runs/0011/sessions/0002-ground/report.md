Orientation complete. Inbox is clean (2 open info: `I-0105` latest run-0010 status + `I-0107` my T13 scope note; `I-0104` archived as superseded; `I-0106` carries the detailed T13 carve-map for Horizon).

## Summary
Opening Ground for run 0011, task **T13** (retire the stale genus-0 / Route-C split). No prior Horizon diff to review. Verified T13's scope and dependency picture, left orientation notes, and flagged one dependency trap plus a scope gap.

## Progress
- recommendation.md: written — 4 bullets pointing Horizon at `roadmap.md`, `WeilDivisor.lean` carve, memory `I-0106`, and the scope gap.
- roadmap.md: no edit (Horizon's task) — confirmed stale lines ~66/72/77/120 still list deleted `Genus0BaseObjects/*` as "sorry-free in-tree" and "Route C paused"; this is the main in-scope inconsistency.
- WeilDivisor.lean: no edit — confirmed dual-purpose; `PrimeDivisor`/`RationalMap.order` substrate is imported by active `Albanese/CodimOneExtension.lean`; only the `-- Route C PAUSE` degree/RR→ℙ¹ block (~5 sorries) is dead genus-0 weight.
- RigidityLemma.lean: no edit — line 787 has stale "genus-0 base case (Route C)" prose over sorry-free math.
- Inbox: filed `I-0107` (info→human, T13 scope note); archived `I-0104` (superseded run-0010 reconcile). `I-0106` already covers the Horizon-facing carve-map.

## Issues
- Scope gap: residual genus-0 doc comments live in `AbelJacobi.lean`, `Jacobian.lean`, and `Genus.lean` (broken `.archon/STRATEGY.md` pointer) — all outside T13's write globs. A full sweep needs those three added to scope. Flagged in `I-0107`.
- Do-not-delete: a wholesale delete of `WeilDivisor.lean` would break `ALB.codim1`'s build.
- Ambiguity: "Route-C" also names a live alternative (coherent-χ) endgame for the 5 headline Quot reps decls (`I-0086`) — distinct from the dead genus-0-base Route-C; pruning must not conflate them.
- Build not re-run this session (no code changed); state inherited green from run 0010 (`I-0105`, 8646 jobs, exit 0).

## Why I stopped
Task complete: this is an opening orientation round, not the implementation. Scope sanity-checked, traps flagged, notes left for Horizon; the actual removal/reconciliation is T13's Horizon work.

## Next
- Horizon (T13): update `roadmap.md` to drop deleted `Genus0BaseObjects`/genus-0-base entries; surgically carve the Route-C RR→ℙ¹ block from `WeilDivisor.lean` (keep `PrimeDivisor`/`order`); clean genus-0 prose in `RigidityLemma.lean`.
- Human: consider adding `AbelJacobi.lean`, `Jacobian.lean`, `Genus.lean` to T13 scope if a fully clean comment sweep is wanted (see `I-0107`).
