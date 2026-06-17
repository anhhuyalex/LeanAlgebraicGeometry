# Strategy Critic Directive

## Slug
iter-004-strategy

## Project goal
Formalize the theorem chain of MR4372220 (Castella--Grossi--Lee--Skinner): the anticyclotomic Iwasawa main conjecture for rational elliptic curves at Eisenstein primes (`thm:thmA`), Perrin-Riou's Heegner-point main conjecture (`cor:PR`), the p-converse to Gross--Zagier--Kolyvagin (`thm:thmB` and `cor:thmB`), and the p-part of BSD in analytic rank 1 (`thm:thmC`), together with the comparison theorems that drive the route (`MAINalgside`, `cor:Kriz`, `thm:howard`, `thm:howard-HP`).

## Strategy under review

# Strategy

## Goal

Formalize the theorem chain of MR4372220: the anticyclotomic Iwasawa main conjecture for rational elliptic curves at Eisenstein primes (`thm:thmA`), Perrin-Riou's Heegner-point main conjecture (`cor:PR`), the $p$-converse to Gross--Zagier--Kolyvagin (`thm:thmB` and `cor:thmB`), and the $p$-part of BSD in analytic rank $1$ (`thm:thmC`), together with the comparison theorems that drive the route (`MAINalgside`, `cor:Kriz`, `thm:howard`, `thm:howard-HP`).

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---:|---:|---|---|
| Local Iwasawa and Selmer foundations | ACTIVE | 2 | ~320-480 | `PowerSeries`, `Submodule`, `LinearMap.ker`, exact sequences, Galois cohomology wrappers, finite-generation lemmas | The modified Selmer conditions and local cohomology comparisons are project-specific and must be stated once, cleanly, and reused everywhere |
| Algebraic Iwasawa invariant comparison | ACTIVE | 1-2 | ~220-340 | torsion module structure, characteristic ideals, λ/μ invariant wrappers, split-prime Euler-factor algebra | The local-to-global λ bookkeeping depends on the full Selmer setup and on external Rubin/Hida inputs being stated precisely |
| Analytic p-adic L-function comparison | ACTIVE | 1-2 | ~240-360 | involution on `Λ`, evaluation of characters on power series, algebra of Euler factors, abstract p-adic L-function interfaces | The BDP/Katz/Kriz statements are source-heavy; the blueprint must keep the exact hypotheses visible and avoid a parallel API for the same anticyclotomic objects |
| Howard abstract Selmer-group bound | ACTIVE | 2 | ~160-260 | finitely generated modules over local rings, length/exponent inequalities, specialization at height-one primes | Sub-phase 1 of Howard/Kolyvagin: prove the abstract Zp-twisted length bound and its Lambda-adic specialization. Blueprint labels: `def:selmer-triple`, `thm:Zp-twisted`, `thm:howard`. |
| Heegner-point Kolyvagin system construction | ACTIVE | 2 | ~160-260 | Kolyvagin systems, norm relations, Heegner-point descent, residual exactness, specialization of classes | Sub-phase 2 of Howard/Kolyvagin: construct the nonzero Kolyvagin system from Heegner points (Cornut--Vatsal nonvanishing) and combine with `thm:howard`. Blueprint labels: `thm:howard-HPKS`, `thm:howard-HP`. |
| Main anticyclotomic conjecture / Perrin-Riou | ACTIVE | 1-2 | ~120-200 | equivalence of the two conjectural formulations, `char`-ideal divisibility, source-backed comparison lemmas | Combine Howard + mu/lambda comparisons to prove `thm:thmA` and `cor:PR`; must not re-prove comparison theorems. Blueprint labels: `prop:equiv-imc`, `thm:thmA`, `cor:PR`. |
| `p`-converse to Gross--Zagier--Kolyvagin | ACTIVE | 1-2 | ~120-200 | control theorem input, twist selection, rank/parity bookkeeping, Sha finiteness, Gross--Zagier transport | Independent downstream lane once `thm:thmA` and `cor:PR` are in hand; must not be serialized with BSD. Blueprint labels: `thm:thmB`, `cor:thmB`. |
| BSD rank-one formula | ACTIVE | 1-2 | ~140-240 | control theorem input, Gross--Zagier height/regulator bookkeeping, quadratic twist arithmetic, Tamagawa and Sha bookkeeping | Independent downstream lane; separate consumer of `thm:thmA`. Must not be blocked by p-converse lane. Blueprint label: `thm:thmC`. |

## Routes

### Greenberg-Vatsal style comparison route

Single route. Build the anticyclotomic Selmer/Iwasawa formalism, compare algebraic and analytic λ-invariants through the residual decomposition `E[p]^{ss} \cong \mathbb{F}_p(\phi)\oplus\mathbb{F}_p(\psi)`, prove the divisibility from a Howard-style Kolyvagin argument, then upgrade the divisibility to the main anticyclotomic conjecture and its arithmetic applications.

Parallel substructure inside the route: the algebraic comparison and the analytic comparison are independent once the local Selmer foundation is in place, and the two downstream applications (`thm:thmB` / `cor:thmB` and `thm:thmC`) are independent once `thm:thmA` is proved. The Howard branch is decomposed into two named sub-phases: (1) the abstract Selmer-group bound with concrete blueprint declarations `def:selmer-triple`, `thm:Zp-twisted`, `thm:howard`; and (2) the Heegner-point Kolyvagin system with `thm:howard-HPKS`, `thm:howard-HP`.

## Open strategic questions

- How much of the external arithmetic should remain as source-backed theorem blocks versus being re-expressed as project-specific interfaces? Current preference: keep the exact statements from the paper, because the λ/μ and divisibility arguments need those hypotheses verbatim.
- Which pieces of the local Selmer formalism should be promoted to reusable project infrastructure versus introduced only where needed? The answer affects how much of the blueprint can be shared across the algebraic, analytic, and Howard/Kolyvagin routes.

## Mathlib gaps & new material

- Anticyclotomic Iwasawa algebra `\Lambda = \mathbf{Z}_p\llbracket\Gamma\rrbracket` and its module theory.
- Selmer structures, modified local conditions, and the dual Selmer groups for characters and elliptic curves.
- Characteristic ideals, Iwasawa invariants, and the finite-length bookkeeping for torsion modules.
- Source-backed arithmetic inputs: Rubin, Hida, BDP, Katz, Kriz, Howard, Gross--Zagier, and Greenberg--Vatsal.
- Kolyvagin systems, Heegner-point classes, and the height-one-prime specialization argument.

## References index

# References

## File inventory

| File | Description | How to read (confirmed working) |
| ---- | ----------- | ------------------------------- |
| `MR4372220-anticyclotomic-iwasawa.pdf` | PDF of On the anticyclotomic Iwasawa theory of rational elliptic curves at Eisenstein primes (MR4372220, arXiv:2008.02571). | `Read` directly or use a page range for long pulls. |
| `MR4372220-anticyclotomic-iwasawa.tex` | Extracted TeX source for the same paper. | `Read` directly. |
| `MR4372220-anticyclotomic-iwasawa-source/` | Extracted source directory. | Browse the extracted arXiv source files directly. |
| `retrieval-notes.md` | Retrieval metadata for the paper. | `Read` directly. |
| `MR4372220-anticyclotomic-iwasawa-source.tar.gz` | Raw arXiv source archive. | Keep for provenance; extract with `tar -xzf`. |

## Blueprint summary

- `Overview.tex` — placeholder chapter, no declarations yet; covers both existing Lean root files
- `Local_Iwasawa_Selmer.tex` — Iwasawa algebra Lambda, character Selmer groups M_theta/M_E, local cohomology at split and p-adic places, Rubin-Hida mu=0, imprimitive lambda-formula, residual exactness (7 declarations: def:iwasawa-algebra, lem:commalg, lem:local-char-wneqp, lem:local-char-wp, thm:mu-zero-theta, prop:lambda-theta, cor:characters)
- `Algebraic_Iwasawa_Comparison.tex` — residual comparison for E[p], mu=0 for X_E, no finite submodules, algebraic comparison theorem MAINalgside (4 declarations: prop:modp-E, prop:modp-E-tors, cor:lambda-E, MAINalgside)
- `Analytic_Iwasawa_Comparison.tex` — (being written this iter) BDP L-function, Katz L-function, Kriz congruence, cor:Kriz, mulambda
- `Howard_Kolyvagin.tex` — (being written this iter) def:selmer-triple, thm:Zp-twisted, thm:howard, thm:howard-HPKS, thm:howard-HP
- `Main_Conjecture_Applications.tex` — (being written this iter) prop:equiv-imc, thm:thmA, cor:PR, thm:thmB, cor:thmB, thm:thmC

## Prior critique status

- iter-001: Howard/Kolyvagin branch not decomposed into named sub-phases with concrete timelines — addressed (STRATEGY.md now has two sub-phases with concrete blueprint labels and iter estimates)
- iter-001: thm:thmB/cor:thmB and thm:thmC not separated into distinct parallel lanes — addressed (now in separate phase rows with explicit independence note)
