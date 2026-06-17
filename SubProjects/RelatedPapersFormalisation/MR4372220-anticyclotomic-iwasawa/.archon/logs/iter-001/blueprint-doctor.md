# Blueprint Doctor

## Chapter coverage problems (`% archon:covers`)

A chapter's `% archon:covers <file> ...` declaration tells the prover-dispatch gate which Lean files that chapter blueprints. The issues below would route the gate to the wrong chapter — fix the declaration (correct the path, or make exactly one chapter own each file).

- chapter `Algebraic_Iwasawa_Comparison.tex` covers `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Algebraic.lean`, which does not exist
- chapter `Local_Iwasawa_Selmer.tex` covers `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Local.lean`, which does not exist

## Orphan chapters

These `.tex` files exist under `blueprint/src/chapters/` but are NOT reachable from `content.tex` via `\input` (directly or transitively). They contribute nothing to the rendered blueprint and likely indicate either a forgotten `\input{...}` line in `content.tex` or stale chapter files left behind by a refactor.

- `blueprint/src/chapters/Algebraic_Iwasawa_Comparison.tex`
- `blueprint/src/chapters/Local_Iwasawa_Selmer.tex`

