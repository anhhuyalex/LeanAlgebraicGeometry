---
name: bv19-fund-gerbes
description: Borne–Vistoli "Fundamental gerbes" (arXiv:1610.07341, ANT 2019) — defines pro-C gerbes, locally full morphisms (Def 3.4), canonical factorization (Prop 3.9), and conditions for locally full (Prop 3.10); cited as [bv19] in MR4688702.
metadata:
  type: reference
---

# Fundamental gerbes

## Citation
Niels Borne and Angelo Vistoli, "Fundamental gerbes", Algebra & Number Theory **13** (2019), no. 3, pp. 531–576. arXiv:1610.07341 [math.AG].

## Slug
bv19-fund-gerbes

## Retrieval status
RETRIEVED — 2026-06-18

## Local source files
- `references/bv19-fund-gerbes.pdf` — PDF, 43 pages, VERIFIED via `file` — retrieved from https://arxiv.org/pdf/1610.07341
- `references/bv19-fund-gerbes.tar.gz` — LaTeX e-print, VERIFIED via `file` — retrieved from https://arxiv.org/e-print/1610.07341
- `references/bv19-fund-gerbes-src/fundamental-gerbes_16.tex` — extracted LaTeX source (ISO-8859-1 encoding; use `iconv -f ISO-8859-1 -t UTF-8` to read cleanly)

## Why this source
Cited as `[bv19]` in MR4688702 §2.  The main paper uses `\cite[Definition 3.4, Proposition 3.9]{bv19}` when writing the pro-finite étale fundamental gerbes Π_{X/k} and Π_{C/k} as projective limits of finite étale gerbes with locally full transition maps; and `\cite[Proposition 3.10]{bv19}` for the fact that a morphism being locally full is equivalent to making the source a relative gerbe over the target. These entries back the blueprint blocks `def:etale-fund-gerbe`, `lem:rel-gerbe-limit`, and `def:rel-fund-gerbe`.

## Contents map

| § | Title | Pages | Relevance |
|---|-------|-------|-----------|
| 1 | Introduction | pp. 1–5 | overview; defines pro-C gerbe universally |
| 2 | Notations and conventions | p. 5 | — |
| **3** | **Generalities on affine gerbes** | **pp. 5–11** | **key section** |
| — | Proposition 3.1 (finite-type gerbes) | p. 6 | — |
| — | Corollary 3.2 | p. 7 | — |
| — | Lemma 3.3 | p. 7 | — |
| — | **Definition 3.4** (locally full morphism of gerbes) | **p. 8** | cited in MR4688702 §2 |
| — | Remarks 3.5–3.7 | p. 8 | — |
| — | Definition 3.8 (canonical factorization) | p. 8 | — |
| — | **Proposition 3.9** (canonical factorization exists and is essentially unique) | **p. 8** | cited in MR4688702 §2 |
| — | **Proposition 3.10** (characterizations of locally full = relative gerbe) | **p. 9** | cited in MR4688702 §2 |
| — | Proposition 3.11 (projective limit and locally full) | p. 10 | — |
| 4 | Fibered categories | pp. 10–11 | — |
| 5 | Fundamental gerbes | pp. 11–13 | universal property of C-fundamental gerbe |
| 6 | Well-founded classes | pp. 13–17 | — |
| 7 | Existence of fundamental gerbes | pp. 17–21 | main existence theorem |
| 8 | Change of class | p. 21 | — |
| 9 | Weil restriction and change of base | pp. 22–26 | — |
| 10–12 | Tannakian interpretations / Unipotent saturations | pp. 27–33 | — |
| 13 | Gerbes of multiplicative type and Picard stacks | pp. 34–42 | — |
| — | References | p. 43 | [5] = bv15 (arXiv:1204.1260) |

## Caveats
- The LaTeX source uses `\call{...}` as a label macro (equivalent to `\label`); it does not affect theorem numbering.
- The LaTeX source is ISO-8859-1 encoded; plain `grep` and `sed` may mis-handle non-ASCII characters. Use `iconv -f ISO-8859-1 -t UTF-8` before piping.
- The directive for this retrieval incorrectly attributed this paper to "Bresciani–Vistoli" and listed arXiv:1404.7475 as the seed; the correct authors are **Borne–Vistoli** and the correct arXiv ID is **1610.07341**. See Notes for Dispatcher in the retrieval report.

## Quality / provenance
This is the definitive published version of the paper (v3, 2017 on arXiv; ANT 2019). The PDF and source were retrieved directly from arxiv.org. The same paper is cited as reference [5] in bv15 (arXiv:1204.1260), which is the Borne–Vistoli "Nori fundamental gerbe" paper.
