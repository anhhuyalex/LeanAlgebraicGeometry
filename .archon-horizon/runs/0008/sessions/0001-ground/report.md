Opening Ground for run 0008 (focus T5) complete. Direction is set.

## Summary

This was the **opening Ground** — no prior Horizon diff. I read the T5 lineage, roadmap, blueprints, and inbox, then set direction for the picrep spine.

**The chosen target: the FGA `picSharp` relative-functor rewire.** This is the single FBC-free gate blocking the whole `AJC.picrep` → `AJC.pic0av` → `AJC.jacobian` spine:
- `picSharp` is still **7 `⟨sorry⟩`** typed instances — an opaque `Classical.choice` of a `⟨sorry⟩ Nonempty` with no defining property, so IdentityComponent's 6 sorries and `tangentSpaceIso` all inherit the taint.
- The substrate is ready: `PicSharp.relPresheaf` is real and axiom-clean; the missing layer is `relEtSheaf`.
- The one real blocker is the étale-topology decision (Kleiman §2 `k`-rational-section route looks most pragmatic).

## Actions taken
- **`recommendation.md`** written with the concrete next-step chain and the FALSE-rewire trap.
- **Roadmap:** evidence comment on `AJC.picrep` (status kept active/high — correct).
- **Inbox:** kept guiding issue `I-0062` open (with a run-0008 tie-in comment), archived superseded `I-0041`, completed 5 absorbed progress notes, filed `I-0070` (info→human) proposing `horizon run AJC.picrep`.
- **Blueprint:** verified it's in the correct state — the honest relative subsection exists and the headline drift is documented; the fix is a coordinated Horizon step, not a piecemeal Ground edit, so no blueprint edit was warranted.

## Flagged
- No build run (direction-only session); no green-build claim. Standing concern that no full green AJC build has been confirmed under concurrent load.
- `SubProjects/Picard-IdentityComponent` mirror is stale (out of scope).
- Inbox backlog ~49 open (mostly durable memory + human notices) — broader janitor pass deferred.
