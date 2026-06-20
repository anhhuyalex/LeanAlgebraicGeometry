# Stacks Project — Sheaves on Spaces

## Citation
The Stacks Project Authors, "Sheaves on Spaces" (Chapter 6 of the Stacks Project),
https://stacks.math.columbia.edu/tag/006A.

## Slug
stacks-sheaves

## Retrieval status
RETRIEVED — 2026-06-07

## Local source files
- `references/stacks-sheaves.tex` — LaTeX source, VERIFIED (opens with `\input{preamble}` + `\begin{document}`), 5337 lines — retrieved from
  https://raw.githubusercontent.com/stacks/stacks-project/master/sheaves.tex

## Why this source
The 02KG affine-instantiation lane needs a `BasisCovSystem` for an affine scheme whose
cofinality field is discharged by Lemma **009L**
(`lemma-cofinal-systems-coverings-standard-case`), which lives in this chapter.
The Schemes chapter (`stacks-schemes.tex`) and Cohomology chapter (`stacks-cohomology.tex`)
both *reference* this lemma but do not contain it; this file is the primary source.

## Contents map

| Line range | Tag | Label / Title |
|------------|-----|---------------|
| 17–38 | — | §6.1 Introduction |
| 40–68 | — | §6.2 Basic notions |
| 69–135 | — | §6.3 Presheaves |
| 136–286 | — | §6.4 Abelian presheaves |
| 287–381 | — | §6.5 Presheaves of algebraic structures |
| 382–499 | — | §6.6 Presheaves of modules |
| 500–642 | — | §6.7 Sheaves |
| 643–678 | — | §6.8 Abelian sheaves |
| 679–855 | — | §6.9 Sheaves of algebraic structures |
| 856–892 | — | §6.10 Sheaves of modules |
| 893–1049 | — | §6.11 Stalks |
| 1050–1088 | — | §6.12 Stalks of abelian presheaves |
| 1089–1136 | — | §6.13 Stalks of presheaves of algebraic structures |
| 1137–1176 | — | §6.14 Stalks of presheaves of modules |
| 1177–1332 | — | §6.15 Algebraic structures |
| 1333–1457 | — | §6.16 Exactness and points |
| 1458–1663 | — | §6.17 Sheafification |
| 1664–1777 | — | §6.18 Sheafification of abelian presheaves |
| 1778–1820 | — | §6.19 Sheafification of presheaves of algebraic structures |
| 1821–1983 | — | §6.20 Sheafification of presheaves of modules |
| 1984–2399 | — | §6.21 Continuous maps and sheaves |
| 2400–2544 | — | §6.22 Continuous maps and abelian sheaves |
| 2545–2681 | — | §6.23 Continuous maps and sheaves of algebraic structures |
| 2682–3029 | — | §6.24 Continuous maps and sheaves of modules |
| 3030–3107 | — | §6.25 Ringed spaces |
| 3108–3268 | — | §6.26 Morphisms of ringed spaces and modules |
| 3269–3366 | — | §6.27 Skyscraper sheaves and stalks |
| 3367–3399 | — | §6.28 Limits and colimits of presheaves |
| 3400–3684 | — | §6.29 Limits and colimits of sheaves |
| **3685–4438** | **009H** | **§6.30 Bases and sheaves** ← *relevant section* |
| 4439–4924 | — | §6.31 Open immersions and (pre)sheaves |
| 4925–5069 | — | §6.32 Closed immersions and (pre)sheaves |
| 5070–5337 | — | §6.33 Glueing sheaves |

### Key declarations in §6.30 (Bases and sheaves, lines 3685–4438)

| Line | Tag | Label |
|------|-----|-------|
| 3695–3731 | 009I | `definition-presheaf-basis` |
| 3733–3770 | 009J | `definition-sheaf-basis` |
| 3772–3859 | 009K | `lemma-cofinal-systems-coverings` (general cofinal-coverings lemma) |
| **3861–3887** | **009L** | **`lemma-cofinal-systems-coverings-standard-case`** ← *target lemma* |
| 3889–3931 | — | `lemma-condition-star-sections` |
| 3933–3966 | 009N | `lemma-extend-off-basis` |
| 3968–3994 | — | `lemma-restrict-basis-equivalence` |
| 3996–4045 | — | `definition-sheaf-structures-basis` |
| 4047–4103 | 009Q | `lemma-extend-off-basis-structures` |
| 4179–4222 | 009T | `lemma-extend-off-basis-module` |

## Caveats
The Stacks Project TeX source embeds no tag numbers directly; tags are assigned in the
separate `tags/tags` file on GitHub. Tag **009L** was confirmed via that file:
`009L,sheaves-lemma-cofinal-systems-coverings-standard-case`. The verbatim statement and
proof are at lines 3861–3887 of `references/stacks-sheaves.tex`.

## Quality / provenance
This is the canonical Stacks Project source, fetched directly from the master branch of
`https://github.com/stacks/stacks-project`. Tag 009L verified against both the tags file
and the Stacks website (https://stacks.math.columbia.edu/tag/009L).
