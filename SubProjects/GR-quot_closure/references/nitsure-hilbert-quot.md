# Construction of Hilbert and Quot Schemes (Nitsure)

## Citation
Nitin Nitsure, "Construction of Hilbert and Quot Schemes", in *Fundamental
Algebraic Geometry: Grothendieck's FGA Explained*, Math. Surveys Monogr. 123,
AMS, 2005, pp. 105–137. arXiv:math/0504590 (v1, 29 Apr 2005). Notes from six
lectures, ICTP Trieste summer school, July 2003.

## Slug
nitsure-hilbert-quot

## Retrieval status
RETRIEVED — 2026-05-20

## Local source files
- `references/nitsure-hilbert-quot.pdf` — PDF, VERIFIED (`%PDF-1` … `%%EOF`,
  379533 bytes, 36 physical pages; printed page = physical page, offset 0) —
  retrieved from `https://arxiv.org/pdf/math/0504590`
- `references/nitsure-hilbert-quot.tar.gz` — arXiv e-print, VERIFIED gzip —
  retrieved from `https://arxiv.org/e-print/math/0504590`
- `references/nitsure-hilbert-quot-src/nitsure-hilbert-quot.tex` — decompressed
  LaTeX source (single file, 3390 lines; e-print is a gzipped single `.tex`).

## Why this source
Backs the Hilbert/Quot-scheme machinery cited by `Jacobian.tex` (Route A). The
Quot-scheme construction (and its semicontinuity / flattening-stratification
inputs) is the existence engine behind the relative Picard functor; this is the
companion reference to Kleiman for the FGA construction.

## Contents map (PDF pages, physical = printed, no on-page TOC)

| § | Title | Page | Source `\section` line | Relevance |
| --- | --- | --- | --- | --- |
| — | Introduction (representability, fpqc descent) | 1 | L1+ | Functor-of-points framing; Yoneda; descent. |
| 1 | The Hilbert and Quot Functors | 2 | L287 | **Definitions** of `Hilb` and `Quot` functors. |
| 2 | Castelnuovo-Mumford Regularity | 9 | L949 | Regularity tools used to bound/produce the embedding into a Grassmannian. |
| 3 | Semi-Continuity and Base-Change | 13 | L1267 | Cohomology-and-base-change inputs. |
| 4 | Generic Flatness and Flattening Stratification | 18 | L1698 | **Flattening stratification** — the technical heart enabling representability. |
| 5 | Construction of Quot Schemes | 23 | L2154 | **CORE.** The actual construction of `Quot` (hence `Hilb`) as a scheme. |
| 6 | Some Variants and Applications | 28 | L2604 | Variants (incl. Picard/relative applications). |
| — | References | 36 | — | Bibliography. |

## Caveats
- arXiv self-pagination (1–35/36) differs from AMS book pagination (105–137);
  this map uses arXiv PDF pages (= on-page printed numbers).
- The e-print is a single gzipped `.tex` (internal gzip name
  `nitsure-hilbert-quot.tar`, but content is plain LaTeX, not a tar).

## Quality / provenance
Standard modern exposition of Grothendieck's Hilbert/Quot construction (Séminaire
Bourbaki 221) with Mumford and Altman–Kleiman developments. PDF + LaTeX source
straight from arXiv (math/0504590 v1), both verified; section→page map from
per-page text extraction (ghostscript txtwrite).
