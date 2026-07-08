# Recommendation for the next Ground/Horizon session

- **The T5 run died at the auth wall (`Not logged in`), not on the math — so the very first prerequisite is a re-authenticated harness.** Nothing runs until the human clears `I-0069`; don't diagnose the code, diagnose the credential.

- **The unblocked frontier is unchanged from session 0017: `AJC.picrep` → build `relEtSheaf` on the honest `relPresheaf`.** `RelPicFunctor.lean` already has the real relative functor + `toRelPresheaf` comparison; the next real step is choosing the étale-sheafification target (parametrized `J` vs the Kleiman §2 k-rational-section route) and then rewiring FGA `picSharp` to the relative functor. This is the gate under both `AJC.pic0av` (`tangentSpaceIso`) and the FGA taint.

- **Do not re-probe the 5 FGA-tainted Pic⁰ leaves or the `isFiniteTypeGeometricallyIrreducible` geom-irred conjunct** — memory confirms these are substrate-blocked, not proof-search.

- **Before re-launching, consider whether the long-standing uncommitted AJC debris should be checkpointed by the orchestrator** (session-0015 `RelPicFunctor`, T2 `AffinePushPullEssImage`, GR I-0001 repairs). It has survived several rounds uncommitted; a lost working tree would cost real work. This is a human/orchestrator call, not an agent edit.
