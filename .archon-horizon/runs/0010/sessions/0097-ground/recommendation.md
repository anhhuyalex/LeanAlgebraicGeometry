# Orientation — run 0010 T12 (Picard representability cone)

- Useful context: run 0010's final T12 Horizon session (`0095-horizon-T12`) failed at harness startup with an empty diff — the productive T12 output landed earlier. Real, verified work this run: `Grassmannian.representable` (`Picard/GrassmannianRepresentability.lean`, modulo two descent leaves) and `Scheme.Modules.pushforward_isQuasicoherent` (`Picard/QuotScheme.lean`, axiom-clean). Durable recipes in memory `I-0109` / `I-0113` / `I-0120`.

- Relevant files for the open frontier: `Picard/QuotFunctorDef.lean` (`Scheme.QuotFunctor`, `Scheme.Grassmannian` are real functors), `Picard/HilbertPolynomial.lean` (`Scheme.hilbertPolynomial` real, axiom-clean), `Picard/QuotScheme.lean` (residual sorries are the FBC-gated base-change leaves plus the `QuotScheme`/`Grassmannian.representable` endgames). Blueprint chapter: `Picard_QuotScheme.tex`.

- Consistency concern to keep in view: `I-0118` — the pinned `Scheme.QuotScheme` hypothesizes only `IsProper`+`LocallyOfFiniteType`, but Nitsure Sec. 5 needs projective / relatively very ample / coherent; the statement is false-or-open as pinned (Hironaka-type counterexample), not the cited theorem. Same trap genus as the old `Grassmannian.representable` skeleton that was corrected this run.

- Adjacent live legs: `AJC.fbc` still has 3 leaf sorries in `CechHigherDirectImageUnconditional.lean` (two cosimplicial `naturality` fields + `pullback_preservesFiniteLimits`, route analysis in `I-0076`/`I-0083`); `AJC.albanese` T9 port is fully scoped but unstarted (`I-0112`/`I-0115`), with the SUB-ahead support files (`PolePurity`, `SmoothPrimeRegularity`, `StandardSmoothDimension`) already present under AJC `Albanese/`.
