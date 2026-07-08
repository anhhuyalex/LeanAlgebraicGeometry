# Orientation for Horizon (run 0013)

- **Active frontier — Milne Lemma 3.3.** Useful context: the sole open Albanese extension-leg sorry is `indeterminacy_pure_codim_one_into_grpScheme` (`AlgebraicJacobian/Albanese/CodimOneExtension.lean:1721`), gating `Thm32RationalMapExtension` and thence `ALB.up`. Brick (a) just landed: `RationalMap.precomp` (`Albanese/RationalMapPrecomp.lean`, Mathlib-only leaf, sorry-free, axiom-clean) — left-precomposition of a rational map with an open morphism. Blueprint pins `def:rationalMap_precomp` / `lem:rationalMap_precomp_compHom` in `Albanese_CodimOneExtension.tex` (sec `sec:milne_lem33`).

- **Next primitives.** The difference-map assembly `Φ = m∘(f×f)` still needs brick (b) — the over-`k̄` pairing `RationalMap.prod` via the function-field correspondence `equivFunctionFieldOver` — then sub-steps 2 (slice `(x,x)∈DomΦ ↔ x∈Domf`) and 4b (diagonal codim-1 Krull bound). Recipe and the `IsOver`-of-`pullback.lift` trap are in memory `t9-albanese-endgame-unblock-map`; the function-field bridge `functionFieldPullback` (`RationalMapFunctionField.lean`, axiom-clean) is already in place.

- **Build note.** A root `lake build` risks rebuilding concurrently-modified Picard modules; the new Albanese work is a self-contained Mathlib-only leaf that kernel-builds standalone. `AlbaneseUP.lean` (6 sorries) is blocked on a missing `Sym^g` scheme substrate, not on the extension leg.

- **Consistency note (separate cone).** `I-0118` records that the pinned `Scheme.QuotScheme` statement is false-as-written (properness ≠ Nitsure's projective hypothesis; Mathlib v4.31 lacks very-ampleness vocabulary). This is a Picard-representability (`AJC.picrep`/T12) concern, not on the T9 path; blueprint node `thm:quot_representable` is now `\notready`.
