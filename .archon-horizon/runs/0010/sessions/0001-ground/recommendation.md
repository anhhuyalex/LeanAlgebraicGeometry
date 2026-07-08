# Recommendation — run 0010, focus `tasks=T12` (`AJC.picrep`, FGA Picard representability)

_Opening Ground; no prior Horizon diff. Tree confirmed green (`lake build`, 8642 jobs). Grounded suggestions — self-scope and override if you see better._

- **T12 has no headline single-session win; be honest about the ceiling.** The 23 in-scope sorries (`FGAPicRepresentability` 4, `QuotScheme` 12, `FlatteningStratification` 7; Grassmannian/RelPicFunctor sorry-free) are almost all deep Nitsure §4/§5 constructions needing Mathlib-absent machinery (relative $\mathbb P^n_S$, coherent-sheaf $\chi$/Hilbert polynomial, CM boundedness, Fitting-ideal strata, generic freeness, Altman–Kleiman descent). Do **not** try to close `hilbertPolynomial`, `QuotScheme`, `Grassmannian.representable`, `genericFlatness`, or `flatteningStratification` — each is multi-session. Full triage is a roadmap comment on `AJC.picrep`.

- **Safe, correct leaf to bank: `flatteningStratification.ofCurve` (`FlatteningStratification.lean` L530).** It is literally the main theorem specialised to `π := pullback.snd C.hom T.hom`; `IsProper (pullback.snd …)` is a Mathlib instance, so `exact flatteningStratification (pullback.snd C.hom T.hom) F` should close it. Correct delegation, wires the Route-A consumer. Caveat: it rests on the still-open L445, so it reduces leaf count, not axiom-debt — verify with `#print axioms` and don't over-claim.

- **Highest real-math-value target (stretch, likely >1 session): the Stacks-01I8 tilde helper `tildeIso_of_isQuasicoherent_isAffineOpen` (`QuotScheme.lean` L676).** The substrate exists sorry-free — `Cohomology/QcohTildeSections.lean` (`qcoh_iso_tilde_sections`) and `CechHigherDirectImageUnconditional.pullbackRestrict_iso_tilde`. The residual is the Σ-pair section-vs-tensor identity (`iso.inv ∘ tilde.toOpen = pullback_app_isoTensor_baseMap`). If you take it, time-box it and fall back to `ofCurve` if the section identity resists.

- **Do NOT vacuously close `instHasDivFunctor` (L185) / `instHasAbelMap` (L291).** Their `Nonempty` is trivially true (const functor / zero nat-trans) but the sorry is a *deliberate flag* that `Div_{C/k}` / the Abel map await their real definitions (see `Picard_FGAPicRepresentability.tex` §sorry-closure-order). Papering over them manufactures false progress and removes a real "A.2.b not done" signal. Leave them.

- **The cone's cohomological inputs are not yet available: T2/`AJC.fbc` is still open** (3 leaf sorries in `CechHigherDirectImageUnconditional.lean` — L196 `pullback_preservesFiniteLimits`, L1646/L1712 the two cosimplicial `naturality` fields). `cech_flatBaseChange` (Stacks 02KH) is the intended $\chi$-openness engine for `QuotScheme`'s base-change chain (L596/620/1065/1227/1278/1328), so that chain cannot be discharged from existing infrastructure until T2 lands. **Do not re-open T2's exclusive `Cohomology/FlatBaseChange*` / `CechHigherDirectImageUnconditional.lean` files** (out of T12 scope).

- **Freeze `IdentityComponent.lean` signatures** (downstream consumer of representability + LFT; not in this write scope).

- **Ops:** box is idle (load ~0.7); incremental `lake build` ≈ seconds, full ≈ 1 min with warm cache. Several other `claude` sessions are alive on the box (`pgrep -af claude`) — check parent PIDs before editing/building files another session may be touching.
