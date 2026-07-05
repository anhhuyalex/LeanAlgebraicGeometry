Orientation is now complete and substantially more precise. Final state verified: `I-0107` carries a correction comment, the full manifest is committed (`1767c3d85f`), and `recommendation.md` is section-aware.

## Summary
Deepened the opening T13 orientation with a 5-scout read-only workflow mapping the entire genus-0 / Route-C cleanup surface. Produced a file:line cleanup manifest, corrected a section-attribution error in my earlier notes, and committed the artifacts. No source code changed (Ground does not do Horizon's task).

## Progress
- t13-cleanup-manifest.md: created — full WeilDivisor carve boundary (keep L55–830 / delete §3–§6), roadmap.md section-aware reconcile, blueprint `.tex` prose, DAG hygiene, verification checklist.
- recommendation.md: rewritten — points to the manifest, corrects the roadmap L120/Albanese framing, notes DAG "2 dangling" are `Picard_GlueDescent.tex` `\uses`, not genus-0.
- I-0107 (info→human): corrected via comment — `roadmap.md:120` is the `## Albanese` section (files exist), not stale; only AJC-section L70/L72 are stale.
- Ledger: committed both artifacts as `1767c3d85f`.
- Inbox: 2 open info (I-0105, I-0107), 11 open memory (I-0106 = durable T13 carve-map). Clean.

## Issues
- No `lake build` run this session — but only markdown/inbox changed, so build state is legitimately inherited green from run 0010 (`I-0105`, 8646 jobs); nothing here can affect it.
- Manifest's "Cotangent/Differentials/standalone Rigidity deleted from AJC" (roadmap L64–65) rests on scout inference from stale `.lake` oleans — flagged "verify" for Horizon, not asserted as fact.
- Manifest line numbers are a snapshot; Horizon must re-anchor before editing (noted in the artifact).
- Scope gap persists: broken `.archon/STRATEGY.md` pointers in `Genus.lean`/`AbelJacobi.lean`/`Cohomology/*.lean` are outside T13's write globs (human decides whether to widen).

## Why I stopped
Task complete: this is the opening orientation round. The cleanup surface is now mapped to file:line precision with dependency traps flagged (WeilDivisor carve-not-delete, `order_one` interleave, dead-vs-live Route-C); the edits themselves are T13's Horizon work.

## Next
- Horizon (T13): execute the carve/reconcile from `t13-cleanup-manifest.md` — WeilDivisor first, then `roadmap.md` `×2`→`×1`, then regenerate `blueprint/web/`; run the manifest §4 verification checklist.
- Human: consider adding `Genus.lean`, `AbelJacobi.lean`, `Cohomology/*.lean` to T13 scope for a full broken-pointer sweep (`I-0107`).
