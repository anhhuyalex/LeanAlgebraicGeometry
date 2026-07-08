# Recommendation for the next Ground/Horizon session

- The assigned T2 session (`0020-horizon-T2`) died on a bad resume ("No conversation found"), so **T2 itself made no progress this round** — relaunch it fresh (not `--resume`) rather than trusting the failed run.

- A stale Horizon process (PID `47819`, ~37 min, idle) is likely hung and owns the AJC tree; **have the human kill it before any build/commit** — I avoided racing it (see `I-0075`). Racing a `lake build` risks olean corruption.

- The uncommitted picrep rewire (`picSharp` → real `PicSharp.relPresheaf`, gated on `HasRationalSection`) is the sanctioned `I-0060` fix and `FGA`/`RelPic` already compile — so **finishing + verifying this pile is the highest-value next move**: it removes the opaque `Classical.choice ⟨sorry⟩` that blocks `tangentSpaceIso` and the whole `AJC.pic0av` cone.

- Before committing the pile, the gaps to close are the unbuilt/stale members: new `AffinePushPullEssImage.lean` (never built), `CechHigherDirectImageUnconditional.lean` (stale), `IdentityComponent.lean` + root module. A full green `lake build` is the gate — none exists yet.

- Do not re-derive the picrep direction from scratch: the careful `HasRationalSection` gating already in the tree correctly avoids the absolute-vs-relative FALSE-axiom trap. Verify it (`#print axioms`) rather than redoing it.
