# The Picard Scheme (Kleiman)

## Citation
Steven L. Kleiman, "The Picard scheme", in *Fundamental Algebraic Geometry:
Grothendieck's FGA Explained*, Math. Surveys Monogr. 123, AMS, 2005, pp.
235–321. arXiv:math/0504020 (v1, 1 Apr 2005). The arXiv preprint is the
"Trieste lectures, July 2003" version and is self-paginated 1–81.

## Slug
kleiman-picard

## Retrieval status
RETRIEVED — 2026-05-20

## Local source files
- `references/kleiman-picard.pdf` — PDF, VERIFIED (`%PDF-1` … `%%EOF`, 974453
  bytes, 83 physical pages; printed page = physical page, offset 0) — retrieved
  from `https://arxiv.org/pdf/math/0504020`
- `references/kleiman-picard.tar.gz` — arXiv e-print, VERIFIED gzip — retrieved
  from `https://arxiv.org/e-print/math/0504020`
- `references/kleiman-picard-src/kleiman-picard.tex` — decompressed LaTeX source
  (single file, 6613 lines; the e-print is a gzipped single `.tex`, not a tar).
  Quote statements from here (exact macros) and cite PDF pages from the map below.

## Why this source
The plan agent will read this map to decide whether **Route A** (Jacobian =
`Pic^0` via FGA) in `Jacobian.tex` can be re-scoped to "only the pieces needed
for the Jacobian of a smooth proper curve over `k`" instead of the full
Picard-representability machinery. The flagged sections below are the ones that
matter for `Pic^0` of a curve.

## Contents map (PDF pages from the on-page TOC, physical = printed)

| § | Title | Page | Source `\section` line | Relevance to Jacobian of a smooth proper curve |
| --- | --- | --- | --- | --- |
| 1 | Introduction | 1 | L295 | Historical; **abelian-variety / Jacobian discussion pp.6–12** (Abel, Jacobi, genus, Pic⁰ as abelian variety). Orientation, not load-bearing. |
| 2 | The several Picard functors | 16 | L1266 | **INPUT.** Defines `Pic_{X/S}`, étale/fppf sheafifications; needed to even state the representing object. |
| 3 | Relative effective divisors | 22 | L1694 | **INPUT.** Relative effective divisors → the divisorial/Abel-map route to constructing `Pic` for curves. |
| 4 | The Picard scheme | 26 | L2043 | **CORE.** Existence/representability `\begin{thm}[Main] th:main` (L2155); `lm:qt` (L2368); `cor:algsch` `\label{cor:algsch}` (L2686, algebraic-scheme case). |
| 5 | The connected component of the identity | 36 | L2836 | **THE SECTION FOR Pic⁰ / THE JACOBIAN.** See result list below. Smooth-curve / abelian-variety material lands pp.49–51. |
| 6 | The torsion component of the identity | 52 | L4043 | **CORE (finiteness).** `Pic^τ`; for a smooth proper curve `Pic⁰ = Pic^τ`. Finiteness `th:Ptaufin` (L4519); `rmk:curves` (L4682). |
| App. A | Answers to all the exercises | 62 | L4808 | Solutions; skip unless an exercise is cited. |
| App. B | Basic intersection theory | 73 | L5708 | Intersection-theory background used in §6. |
| — | References | 81 | — | Bibliography. |

### §5 "The connected component of the identity" — labelled results (deep)
(source line numbers in `kleiman-picard-src/kleiman-picard.tex`; all on PDF pp.36–51)

- `lem:agps` (L2851) — group scheme l.f.t. over a field: separated; smooth if it
  has a geom-reduced open; `G^0` open-closed finite-type geom-irreducible subgroup,
  commutes with field extension. **Key structural input for `Pic⁰`.**
- `th:qpp&p` (L2935) — quasi-projectivity / projectivity of `Pic⁰`.
- `cor:Poincare` (L2986) — Poincaré-type corollary.
- `thm:tgtsp` (L3265) — tangent space of the Picard scheme (→ dimension of `Pic⁰`).
- `cor:sm` (L3421) — **smoothness over a field** (assumes `S = Spec` field).
- `cor:ch0` (L3442) — char-0 smoothness/reducedness.
- `rmk:Ablsch` (L3920) — **abelian-scheme** remark.
- `rmk:Alb` (L3960) — Albanese.
- `rmk:Jac` (L3990) — **the Jacobian** (Pic⁰ of a curve as abelian variety).
- `rmk:Jacsp` (L4019) — Jacobian, further remark.

### §6 labelled results (finiteness; pp.52–61)
- `thm:numeq` (L4085); `lem:Gtauk` (L4380); `th:Ptaufin` (L4519, **`Pic^τ`
  finiteness**); `cor:torgp` (L4589); `thm:Pphifin` (L4643); `rmk:curves`
  (L4682, **the curve case**); `cor:cc`/`cor:phin` (L4736/L4759).

### §4 labelled results (existence; pp.26–35)
- `th:main` (L2155, **Main existence theorem for `Pic_{X/S}`**); `eq:phi` (L2190);
  `lm:qt` (L2368); `rk:exist` (L2628); `cor:algsch` (L2686).

## Keyword → PDF page index (for re-scoping)
- "Jacobian" → pp. 6, 7, 10, 11, 12, 50, 81
- "abelian variety" → pp. 7, 9, 10, 11, 12, 51
- "abelian scheme" → p. 51
- "smooth curve" → pp. 49, 51
- "genus" → pp. 3, 4, 5, 7, 9, 10, 31, 45, 50, 51, 67, 78, 82

## Caveats
- The arXiv self-pagination (1–81) differs from the AMS book pagination (235–321);
  this map uses the arXiv PDF pages, which equal the on-page printed numbers.
- The e-print is a single gzipped `.tex` whose internal gzip name is
  `kleiman-picard.tar`, but the content is plain LaTeX, not a tar archive.
- Theorem/lemma cross-references inside the source use `\cite{EGAI}`, `\cite{EGAIV2}`
  etc. — those EGA references are not bundled here.

## Quality / provenance
Definitive modern exposition of Grothendieck's Picard-scheme theory; the standard
citation. PDF + LaTeX source both straight from arXiv (math/0504020 v1) and
verified. Section→page map taken from the document's own table of contents
(PDF p.1) and corroborated by per-page text extraction (ghostscript txtwrite).
