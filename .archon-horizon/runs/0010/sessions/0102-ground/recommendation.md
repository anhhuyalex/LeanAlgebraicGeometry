# Orientation — AJC / T12 (Picard representability cone)

- Useful context: run 0010's productive T12 output is already in the working tree and reconciled — `Picard/QuotFunctorDef.lean` (real `QuotFunctor`/`Grassmannian` functors), `Picard/GrassmannianRepresentability.lean` (`Grassmannian.representable`, modulo two clean Zariski/sheaf descent leaves), `Picard/HilbertPolynomial.lean` (real `Scheme.hilbertPolynomial`), and `Picard/QuotScheme.lean`'s `pushforward_isQuasicoherent` (Stacks 01XJ, axiom-clean). Durable recipes live in memory `I-0109`, `I-0113`, `I-0120`.

- Open frontier: the `QuotScheme`/representability endgame. `I-0118` flags that the pinned `Scheme.QuotScheme` (only `[IsProper]`/`[LocallyOfFiniteType]`, arbitrary `L`/`E`) is false-as-stated — the Nitsure theorem needs `π` projective, `L` relatively very ample, `E` coherent; Mathlib v4.31 lacks projectivity/ampleness vocabulary. The deepest missing input toward a real Quot statement is `lem:sectionGradedModule_fg` (Serre finite-generation of `⊕ₘ Γ(Xₛ, Fₛ⊗Lₛ^{⊗m})`), per `I-0109`.

- Environment note: two T12 Horizon launches this run (`0095-horizon-T12`, `0099-horizon-T12`) both exited 1 at `fable5`/codex harness boot with 0 tokens, producing no diff (see `I-0122`). The accumulated run-0010 AJC work is uncommitted to the project ledger (`.archon-horizon/vcs/Algebraic-Jacobian-Challenge.git` HEAD is still `6e7f7ae`, run 0005) — a checkpointing lag, not a source problem; the working tree builds as reconciled.

- Adjacent leaves with existing blueprint nodes: `_sectionLinearEquiv` N1–N4 `baseMap`-coherence helpers (`lem:baseMap_*`), and `pullback_tildeIso` (Stacks 01HQ) where the new converse tilde–Γ transport (`isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule`) may help structure the argument.
