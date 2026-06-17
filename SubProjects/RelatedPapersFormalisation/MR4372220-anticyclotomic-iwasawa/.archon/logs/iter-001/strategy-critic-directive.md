# Strategy Critic Directive

## Slug
iter-001

## Project goal
Formalize the theorem chain of MR4372220: the anticyclotomic Iwasawa main conjecture for rational elliptic curves at Eisenstein primes, Perrin-Riou’s Heegner-point main conjecture, the $p$-converse to Gross--Zagier--Kolyvagin, and the $p$-part of BSD in analytic rank $1$, together with the comparison theorems that drive the route.

## Strategy under review

# Strategy

## Goal

Formalize the theorem chain of MR4372220: the anticyclotomic Iwasawa main conjecture for rational elliptic curves at Eisenstein primes (`thm:thmA`), Perrin-Riou’s Heegner-point main conjecture (`cor:PR`), the $p$-converse to Gross--Zagier--Kolyvagin (`thm:thmB` and `cor:thmB`), and the $p$-part of BSD in analytic rank $1$ (`thm:thmC`), together with the comparison theorems that drive the route (`MAINalgside`, `cor:Kriz`, `thm:howard`, `thm:howard-HP`).

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---:|---:|---|---|
| Local Iwasawa and Selmer foundations | ACTIVE | 2 | ~320-480 | `PowerSeries`, module/ideal bookkeeping, exact sequences, Galois cohomology wrappers, finite-generation lemmas | The modified Selmer conditions and local cohomology comparisons are project-specific and must be stated once, cleanly, and reused everywhere |
| Algebraic Iwasawa invariant comparison | ACTIVE | 1-2 | ~220-340 | torsion module structure, characteristic ideals, λ/μ invariant wrappers, split-prime Euler-factor algebra | The local-to-global λ bookkeeping depends on the full Selmer setup and on external Rubin/Hida inputs being stated precisely |
| Analytic p-adic L-function comparison | ACTIVE | 1-2 | ~240-360 | involution on `Λ`, evaluation of characters on power series, algebra of Euler factors, abstract p-adic L-function interfaces | The BDP/Katz/Kriz statements are source-heavy; the blueprint must keep the exact hypotheses visible and avoid a parallel API for the same anticyclotomic objects |
| Howard/Kolyvagin system argument | ACTIVE | 2-3 | ~360-560 | finitely generated modules over local rings, length/exponent inequalities, specialization at height-one primes, global duality | This is the technical bottleneck; the main theorem will fail if the rank-one and length bounds are not decomposed into small lemmas |
| Main conjecture and arithmetic applications | ACTIVE | 1-2 | ~180-280 | control theorem input, Gross--Zagier style height/regulator bookkeeping, quadratic twist arithmetic, Tamagawa and Sha bookkeeping | Downstream deductions must stay downstream; if this phase starts re-proving the comparison theorems, the route has drifted |

## Routes

### Greenberg-Vatsal style comparison route

Single route. Build the anticyclotomic Selmer/Iwasawa formalism, compare algebraic and analytic λ-invariants through the residual decomposition `E[p]^{ss} \cong \mathbb{F}_p(\phi)\oplus\mathbb{F}_p(\psi)`, prove the divisibility from a Howard-style Kolyvagin system argument, then upgrade the divisibility to the main anticyclotomic conjecture and its arithmetic applications.

Parallel substructure inside the route: the algebraic comparison and the analytic comparison are independent once the local Selmer foundation is in place, so they should advance in parallel; the Kolyvagin-system phase is the deepest sequential dependency and should be broken into bridge lemmas before any prover work.

## Open strategic questions

- How much of the external arithmetic should remain as source-backed theorem blocks versus being re-expressed as project-specific interfaces? Current preference: keep the exact statements from the paper, because the λ/μ and divisibility arguments need those hypotheses verbatim.
- Should the blueprint stay as one consolidated chapter while the Lean surface is still tiny, or should it be split once the actual Lean namespace split becomes clearer? Current preference: keep one consolidated chapter for now.
- Which pieces of the local Selmer formalism should be promoted to reusable project infrastructure versus introduced only where needed? The answer affects how much of the blueprint can be shared across the algebraic, analytic, and Kolyvagin routes.

## Mathlib gaps & new material

- Anticyclotomic Iwasawa algebra `\Lambda = \mathbf{Z}_p\llbracket\Gamma\rrbracket` and its module theory.
- Selmer structures, modified local conditions, and the dual Selmer groups for characters and elliptic curves.
- Characteristic ideals, Iwasawa invariants, and the finite-length bookkeeping for torsion modules.
- Source-backed arithmetic inputs: Rubin, Hida, BDP, Katz, Kriz, Howard, Gross--Zagier, and Greenberg--Vatsal.
- Kolyvagin systems, Heegner-point classes, and the height-one-prime specialization argument.

## References index

# References

<!-- archon:references-summary -->

## File inventory

| File | Description | How to read (confirmed working) |
| ---- | ----------- | ------------------------------- |
| `MR4372220-anticyclotomic-iwasawa.pdf` | PDF of On the anticyclotomic Iwasawa theory of rational elliptic curves at Eisenstein primes (MR4372220, arXiv:2008.02571). | `Read` directly or use a page range for long pulls. |
| `MR4372220-anticyclotomic-iwasawa.tex` | Extracted TeX source for the same paper. | `Read` directly. |
| `MR4372220-anticyclotomic-iwasawa-source/` | Extracted source directory. | Browse the extracted arXiv source files directly. |
| `retrieval-notes.md` | Retrieval metadata for the paper. | `Read` directly. |
| `MR4372220-anticyclotomic-iwasawa-source.tar.gz` | Raw arXiv source archive. | Keep for provenance; extract with `tar -xzf`. |

## Blueprint summary

- `blueprint/src/chapters/Overview.tex` — consolidated chapter for the whole paper; currently only a stub overview covering both Lean files.

## Prior critique status

no prior critique
