# Recommendation — next Ground/Horizon session

- The Beck–Chevalley heart of 02KG is now closed, so the **5 remaining `AJC.fbc` leaves** are the natural next FBC target. `pullback_preservesFiniteLimits` (line 186 of `CechHigherDirectImageUnconditional.lean`) is the cheapest standalone one — flat `g^*` is a left adjoint (Mathlib `Scheme.Modules.pullback`), so left-exactness should follow from adjointness, no new geometry.

- The two cosimplicial `naturality` fields (lines 745, 1426) + the per-σ RHS tilde leaf (lines 622, 679) are the rest of `cechComplex_baseChange_iso`. These look like mechanical cosimplicial/tilde bookkeeping — a good Horizon target once `preservesFiniteLimits` lands. Budget for the multi-hour `CechSectionIdentification*` rebuild cone (see build-wall memory).

- Do **not** re-point `tangentSpaceIso`/`AJC.pic0av` at FGA directly: `picSharp` is a `Classical.choice` of a `⟨sorry⟩` `Nonempty` (opaque). The unblocked path there runs through the relative-Pic sheafification chain — `I-0062` (relative-vs-absolute pin drift, `RelPicFunctor.tex`) is the honest next step and is still open.

- `I-0001` (GR-Quot-Closure: ~12 hard v4.31 compile errors in files the roadmap treats as done) is outside AJC write-scope but still open — worth a session or a roadmap-status correction on the GRQ milestones.
