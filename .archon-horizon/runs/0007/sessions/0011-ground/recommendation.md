# Recommendation — next Ground/Horizon session

- **The verified GR + AJC `SectionGradedRing.lean` fixes are uncommitted and `horizon commit` is broken here**, so the safest next move is to land them cleanly (scoped to just those two files) before another run mutates the AJC tree — the AJC copy is intermingled with unverified T2/T5 material. Fixing the MR0555258 `lake-manifest.json` mathlib pin (v4.30.0 → v4.31.0) may unblock `horizon commit` (its guard warns on every invocation).

- **GR-Quot-Closure is now fully green (8566 jobs)** for the first time since the v4.31 bump. `RelativeSpec.lean` still carries ~8 pre-existing *structural* (non-v4.31) sorries, yet `GRQ.quot` reads "sorry-free" — worth a look to reconcile that older claim, but it is out of the v4.31-debt scope and not urgent.

- **Login/auth is failing mid-run** (session `0007-horizon-T8` crashed on it after real work; `0009-ground` came up empty). Until that is stable, sessions may silently do work and then be mislabeled `failed` — verify a "failed" session's transcript/diff before trusting the label.

- **AJC full-tree build remains unconfirmed** because the working tree holds unverified T2 (FBC) + T5 material. A dedicated T2 reconcile (build `CechHigherDirectImageUnconditional` + `AffinePushPullEssImage` cone) is still the gating check before trusting those `\leanok`s — see `I-0016`/`I-0054`/`I-0063`.

- **Mathematical next targets are unchanged** and remain the real critical path: `AJC.pic0av` `tangentSpaceIso` via the relative-Pic functor route (`I-0070`), and the FGA `picSharp` relative-functor rewire for `AJC.picrep`.
