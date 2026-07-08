The AJC project ledger is at the run-0005 checkpoint (HEAD `6e7f7ae`), so runs 0006–0013 show as uncommitted in the project tree — but the workspace ledger captured the T9 integration commit `3dcc5991b2`, so the work is durably recorded. The new file is a legitimate leaf; the only deletions (`RationalCurveIso.*`) are removals of old scratch bodies. Reconcile is complete.

## Summary

Reconcile of the latest Horizon work (`0027-horizon-T9`), which landed **Milne 3.3 brick (a)** — `RationalMap.precomp`, the left-precomposition primitive missing from Mathlib's rational-map API. The work is sound, axiom-clean, and its blueprint pins are 1-to-1 with the Lean. Recorded the advance on the roadmap and left orientation for the next Horizon.

## Progress
- RationalMapPrecomp.lean: verified sorry-free, `precomp_compHom` axiom-clean `[propext, Classical.choice, Quot.sound]` via `lean_verify`; olean built, imported in `AlgebraicJacobian.lean:105`.
- Albanese_CodimOneExtension.tex: verified `def:rationalMap_precomp` + `lem:rationalMap_precomp_compHom` are pure-math with complete proofs, `\lean` pins correct, `\uses` edge present, wired into `sec:milne_lem33` sub-step 1 — no fix needed.
- CodimOneExtension.lean: no change; Milne 3.3 sorry (`:1721`) still open, per Horizon report (brick (a) alone does not close it).
- roadmap ALB.codim1: added Ground key-advance comment (brick (a) landed + verified; next = brick (b) pairing + sub-steps 2/4b).
- recommendation.md: written (T9 frontier, next primitives, build note, I-0118 cross-cone consistency note).

## Issues
- Milne 3.3 (`CodimOneExtension.lean:1721`) remains the sole open Albanese extension-leg sorry; multi-session, needs brick (b) `RationalMap.prod` via `equivFunctionFieldOver` next.
- AJC project ledger HEAD is at run-0005 (`6e7f7ae`); runs 0006–0013 are uncommitted in the project tree but captured in the workspace ledger (`3dcc5991b2`). Not a data-loss risk — flagged for awareness, project checkpoint is Horizon/orchestrator's job.
- Inbox at 13 open (1 issue + 12 memory), slightly over the ~10 target; each maps to a live frontier (T9/Albanese, FBC, picrep, A.3), so left intact per prior ground's documented judgment.
- No full `lake build` run: the new file is a Mathlib-only leaf already olean-built and axiom-verified; a root build risks rebuilding concurrently-modified Picard modules.

## Why I stopped
Task complete: the reconcile pass is done — the latest Horizon work (brick (a)) is verified clean and blueprint/roadmap/memory reflect the real state, with the ledger-lag and inbox-size observations surfaced rather than absorbed.
- The T9 leaf was already axiom-clean and needed verification, not repair.
- Blueprint nodes were already correct and 1-to-1; no drift to fix this round.

## Next
- After brick (b) lands, verify `RationalMap.prod` axiom-cleanliness and update ALB.codim1/ALB.up.
- Watch the Picard cone (`AJC.picrep`/T12): `I-0118` `QuotScheme` false-as-pinned statement still needs a faithful restatement once very-ampleness vocabulary exists.
