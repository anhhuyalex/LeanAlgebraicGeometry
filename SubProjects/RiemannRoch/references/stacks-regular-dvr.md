# Stacks Project — Tag 00PD (Lemma 10.119.7) and Tag 0AVT (Section 31.13)

## Citation
The Stacks Project Authors, "The Stacks Project", 2024. https://stacks.math.columbia.edu

## Slug
stacks-regular-dvr

## Retrieval status
RETRIEVED — 2026-06-20

## Local source files
- `references/stacks-regular-dvr-algebra.tex` — LaTeX source of Chapter 10 (Commutative Algebra), VERIFIED via `file` — retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex
- `references/stacks-regular-dvr-divisors.tex` — LaTeX source of Chapter 31 (Divisors), VERIFIED via `file` — retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/divisors.tex

## Why this source
A blueprint chapter (`RiemannRoch_OcOfD.tex`) needs to cite the step "a regular local ring of dimension one is a discrete valuation ring" inside the proof that a smooth-of-relative-dimension-one curve over a field is regular in codimension one. Mathlib (snapshot b80f227) has no bridge from `IsRegularLocalRing` to `IsDiscreteValuationRing`, so the step must be grounded here.

## Tag resolution (from `tags/tags`)
- `00PD` → `algebra-lemma-characterize-dvr` (Chapter 10, algebra.tex)
- `0AVT` → `divisors-section-reflexive` (Chapter 31, divisors.tex)

## Contents map

### Tag 00PD — Lemma 10.119.7 — `stacks-regular-dvr-algebra.tex`

**Chapter:** 10 (Commutative Algebra)  
**Section:** 10.119 "Around Krull-Akizuki" — `\label{section-krull-akizuki}` — algebra.tex line 28881  
**Lemma:** `\label{lemma-characterize-dvr}` — algebra.tex lines 29107–29162  
**Online:** https://stacks.math.columbia.edu/tag/00PD

The lemma (`\begin{lemma}` at line 29107, `\label{lemma-characterize-dvr}` at line 29108, `\end{proof}` at line 29162) is the key statement. **Quote the statement verbatim from the downloaded .tex at lines 29107–29121.** Do NOT paraphrase from this pointer.

Section outline of 10.119 "Around Krull-Akizuki" (relevant lemmas only, all in algebra.tex):
- `lemma-characterize-dvr` (tag 00PD) — lines 29107–29162 — THE key DVR characterisation
- `definition-uniformizer` — lines 29164–29168 — definition of uniformizer
- `lemma-finite-length` — lines 29174–29184 — follows immediately after

### Tag 0AVT — Section 31.13 "Reflexive modules" — `stacks-regular-dvr-divisors.tex`

**Chapter:** 31 (Divisors)  
**Section:** 31.13 "Reflexive modules" — `\label{section-reflexive}` — divisors.tex line 1992–1993  
**Online:** https://stacks.math.columbia.edu/tag/0AVT

Tag 0AVT is the **section-level** tag for all of Section 31.13. It is NOT a single lemma. The section begins at divisors.tex line 1992. Its first item is `definition-reflexive` (tag 0AVU, line 2004): definition of reflexive hull and reflexive coherent sheaf.

⚠ **Dispatcher note:** Tag 0AVT does NOT directly state the regular-local-dim-1 ↔ DVR equivalence. It is the sheaf-theoretic section on reflexive coherent modules on integral locally Noetherian schemes. The DVR characterisation cited in the directive lives entirely in tag 00PD (algebra.tex). If the blueprint needs reflexive-module machinery from Chapter 31, this section is the right place; but for the single proof step "regular local dim 1 ⟹ DVR", only tag 00PD is needed.

## Caveats
- Tag 0AVT is a section-level tag (covers all of Section 31.13, not a single lemma). Its opening definition tag is 0AVU, not 0AVT.
- algebra.tex is 1.7 MB (≈ 46 000 lines). Use the line offsets above to navigate directly rather than searching the whole file.

## Quality / provenance
The Stacks Project is the definitive online reference for algebraic geometry in this style. Both files are fetched directly from the official GitHub mirror (`stacks/stacks-project`, master branch, 2026-06-20). The tag-to-label mapping was verified against `tags/tags` in the same repository.
