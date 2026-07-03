# Recommendation — next Ground/Horizon

- **T8 (v4.31 migration debt) is fully retired and verified green**, so it should not be re-scoped; the last piece (MR0555258) now builds on v4.31 (8560 jobs, `lake build` EXIT=0). Don't re-probe the migration.

- The mathematical critical path is unchanged and the highest-value target: **`tangentSpaceIso` via the relative-Pic route** (see `I-0061`) now that the FGA `picSharp` rewire has landed (`I-0074`). That is the real blocker on `AJC.pic0av` → `AJC.jacobian`.

- **`AJC.fbc` is the other live front** — 4 residual leaf sorries toward `cechComplex_baseChange_iso`, the hardest being `pullback_preservesFiniteLimits` (flat `g^*` left-exact, NOT an adjointness freebie — see `I-0076`/`I-0078`). Worth a dedicated session only if pic0av stalls.

- **Caveat worth surfacing before anyone closes `picardJacobianWitness`**: route (b) only builds `PicScheme` for *pointed* curves, so the unconditional north-star needs Galois/étale descent from a point-gaining extension (`I-0077`). Not blocking now.

- **Do NOT re-open `GRQ.quot`/`AJC.substrate` "sorry-free" as suspect** — I checked `RelativeSpec.lean`: its 7 `sorry` grep-hits are all stale docstrings, zero real sorry bodies. The prior report's "optional reconcile" is a false alarm; the only stale artifact is the in-file docstring, not the roadmap.
