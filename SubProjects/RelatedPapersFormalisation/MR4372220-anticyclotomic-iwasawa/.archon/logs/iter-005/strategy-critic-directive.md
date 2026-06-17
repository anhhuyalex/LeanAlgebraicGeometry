# Strategy Critic Directive

## Slug
iter-005-strategy

## Project goal
Formalize the theorem chain of MR4372220 (Castella–Grossi–Lee–Skinner, "On the anticyclotomic Iwasawa theory of rational elliptic curves at Eisenstein primes"): the anticyclotomic Iwasawa main conjecture for rational elliptic curves at Eisenstein primes (thm:thmA), Perrin-Riou's Heegner-point main conjecture (cor:PR), the p-converse to Gross–Zagier–Kolyvagin (thm:thmB and cor:thmB), and the p-part of BSD in analytic rank 1 (thm:thmC), together with the comparison theorems that drive the route (MAINalgside, cor:Kriz, thm:howard, thm:howard-HP).

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
| Howard abstract Selmer-group bound | ACTIVE | 3 | ~220-360 | finitely generated modules over local rings, length/exponent inequalities, specialization at height-one primes; `def:selmer-triple` postulate | Sub-phase 1: abstract Zp-twisted length bound + Lambda-adic specialization. `def:selmer-triple` is sorry-backed initially; `thm:Zp-twisted` multi-page proof requires sub-splitting. Blueprint labels: `def:selmer-triple`, `thm:Zp-twisted`, `thm:howard`. |
| Heegner-point Kolyvagin system construction | ACTIVE | 2-3 | ~200-320 | Kolyvagin systems, norm relations, Heegner-point descent, residual exactness, Cornut-Vatsal nonvanishing | Sub-phase 2: nonzero KS from Heegner points + combined Howard divisibility. Blueprint labels: `thm:howard-HPKS`, `thm:howard-HP`. Cornut-Vatsal is treated as an opaque input postulate. |
| Main anticyclotomic conjecture / Perrin-Riou | ACTIVE | 1-2 | ~120-200 | equivalence of the two conjectural formulations, `char`-ideal divisibility, source-backed comparison lemmas | Combine Howard + mu/lambda comparisons to prove `thm:thmA` and `cor:PR`; must not re-prove comparison theorems. Blueprint labels: `prop:equiv-imc`, `thm:thmA`, `cor:PR`. |
| `p`-converse to Gross--Zagier--Kolyvagin | ACTIVE | 1-2 | ~120-200 | control theorem input, twist selection, rank/parity bookkeeping, Sha finiteness, Gross--Zagier transport | Independent downstream lane once `thm:thmA` and `cor:PR` are in hand; must not be serialized with BSD. Blueprint labels: `thm:thmB`, `cor:thmB`. |
| BSD rank-one formula | ACTIVE | 1-2 | ~140-240 | control theorem input, Gross--Zagier height/regulator bookkeeping, quadratic twist arithmetic, Tamagawa and Sha bookkeeping | Independent downstream lane; separate consumer of `thm:thmA`. Must not be blocked by p-converse lane. Blueprint label: `thm:thmC`. |

## Routes

### Greenberg-Vatsal style comparison route

Single route. Build the anticyclotomic Selmer/Iwasawa formalism, compare algebraic and analytic λ-invariants through the residual decomposition `E[p]^{ss} \cong \mathbb{F}_p(\phi)\oplus\mathbb{F}_p(\psi)`, prove the divisibility from a Howard-style Kolyvagin argument, then upgrade the divisibility to the main anticyclotomic conjecture and its arithmetic applications.

Parallel substructure inside the route: the algebraic comparison and the analytic comparison are independent once the local Selmer foundation is in place, and the two downstream applications (`thm:thmB` / `cor:thmB` and `thm:thmC`) are independent once `thm:thmA` is proved. The Howard branch itself must be decomposed into named bridge lemmas and a separate Heegner-point construction.

## Open strategic questions

- How much of the external arithmetic should remain as source-backed theorem blocks versus being re-expressed as project-specific interfaces? Current preference: keep the exact statements from the paper, because the λ/μ and divisibility arguments need those hypotheses verbatim.
- Which pieces of the local Selmer formalism should be promoted to reusable project infrastructure versus introduced only where needed? The answer affects how much of the blueprint can be shared across the algebraic, analytic, and Howard/Kolyvagin routes.

## Mathlib gaps & new material

- Anticyclotomic Iwasawa algebra `\Lambda = \mathbf{Z}_p\llbracket\Gamma\rrbracket` and its module theory.
- Selmer structures, modified local conditions, and the dual Selmer groups for characters and elliptic curves.
- **Characteristic ideals** (`def:char-ideal`): absent from Mathlib. Decision: treat as a `sorry`-backed postulate block in the Local Iwasawa chapter (blueprint anchor `def:char-ideal` with `\lean{MR4372220.Local.charIdeal}`), stating the characteristic ideal of a finitely generated torsion Λ-module and its key properties (multiplicativity, μ/λ-invariant extraction). Formalization debt is explicit; a future iter will lift the sorry when needed.
- **Kolyvagin systems formalism**: absent from Mathlib. Covered in the Howard chapter under `def:selmer-triple`, which includes norm-relation axioms and the abstract Kolyvagin-system structure. A separate `def:kolyvaginSystem` block will be split off in the next Howard iter if the prover finds `def:selmer-triple` too large. Current single-block approach is a pragmatic postulate decision: the whole abstract structure is sorry-backed at first; LOC estimate for the Howard abstract bound phase is revised upward to ~220-360 to account for this.
- **BDP/Katz p-adic L-functions**: absent from Mathlib. Decision: treat both L-function constructions (`thm:BDP`, `thm:Katz`) as source-backed sorry-backed theorem blocks in the Analytic chapter. The Kriz congruence and mu/lambda comparison build on these as opaque inputs. Formalization debt is explicit.
- Source-backed arithmetic inputs: Rubin, Hida, BDP, Katz, Kriz, Howard, Gross--Zagier, and Greenberg--Vatsal.
- Heegner-point classes and the height-one-prime specialization argument.

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

- `Overview.tex` — Project overview and top-level structure (no covers declaration)
- `Local_Iwasawa_Selmer.tex` — Local Iwasawa algebra, Selmer structures for characters and elliptic curves, μ=0 and λ-formula for character Selmer groups (8 declarations)
- `Algebraic_Iwasawa_Comparison.tex` — Residual decomposition E[p]^ss ≅ F_p(φ)⊕F_p(ψ) and algebraic Iwasawa invariant comparison for X_E (4 declarations)
- `Analytic_Iwasawa_Comparison.tex` — BDP and Katz p-adic L-functions, Kriz Eisenstein congruence, analytic μ/λ comparison (5 declarations)
- `Howard_Kolyvagin.tex` — Selmer triples, Kolyvagin systems, abstract Zp-twisted bound, Lambda-adic Howard bound, Heegner-point Kolyvagin system construction (7 declarations)
- `Main_Conjecture_Applications.tex` — BDP Heegner class, anticyclotomic control theorem, p-adic Gross-Zagier formula, equivalence of main conjecture formulations, Theorem A (anticyclotomic IMC), Corollary (Perrin-Riou), Theorem B (p-converse), Theorem C (BSD rank-1 formula) (9 declarations)

## Prior critique status

- iter-004: Characteristic ideal theory for torsion Λ-modules — no project-side plan in STRATEGY.md — addressed (def:char-ideal postulate added to Mathlib gaps section and Local chapter)
- iter-004: Kolyvagin systems formalism — no blueprint declaration — addressed (def:selmer-triple, lem:cebotarev-kolyvagin, lem:kolyvagin-inductive-step added to Howard chapter; STRATEGY.md documents the postulate decision)
- iter-004: BDP/Katz p-adic L-functions — no project-side plan — addressed (thm:BDP, thm:Katz treated as sorry-backed postulates in Analytic chapter; documented in Mathlib gaps section)
- iter-004: Effort estimate for Howard/Heegner phase under-counted — addressed (LOC revised upward to ~220-360 in STRATEGY.md)
