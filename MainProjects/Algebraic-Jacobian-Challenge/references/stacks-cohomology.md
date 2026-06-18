---
name: stacks-cohomology
description: Stacks Project Chapter "Cohomology" (cohomology.tex) — abstract sheaf cohomology on ringed spaces, Čech cohomology, higher direct images.
metadata:
  type: reference
---

# Stacks Project — Cohomology (cohomology.tex)

## Citation
The Stacks Project Authors, "Cohomology", in *Stacks Project*, 2024.
https://stacks.math.columbia.edu/chapter/cohomology

## Slug
stacks-cohomology

## Retrieval status
RETRIEVED — 2026-06-05

## Local source files
- `references/stacks-cohomology.tex` — LaTeX source, 14535 lines, VERIFIED (opens as valid TeX with `\input{preamble}` header and `\begin{document}` — not HTML) — retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex

## Why this source
The blueprint chapter `Cohomology_CechHigherDirectImage.tex` cites two results from the
Stacks "Cohomology" chapter (not "Cohomology of Schemes", which is already local as
`stacks-coherent.tex`):
- `lemma-cech-vanish-basis`: Čech-to-cohomology comparison via a basis (three conditions).
- `lemma-describe-higher-direct-images`: $R^if_*\mathcal{F}$ is the sheafification of
  $V \mapsto H^i(f^{-1}(V), \mathcal{F})$.

## Contents map

Section structure (line numbers in `stacks-cohomology.tex`):

| Line | Section |
|------|---------|
| 17   | Introduction |
| 32   | Cohomology of sheaves |
| 92   | Derived functors |
| 223  | First cohomology and torsors |
| 344  | First cohomology and extensions |
| 398  | First cohomology and invertible sheaves |
| 488  | **Locality of cohomology** ← `lemma-describe-higher-direct-images` |
| 704  | Mayer-Vietoris |
| 868  | The Čech complex and Čech cohomology |
| 1011 | Čech cohomology as a functor on presheaves |
| 1404 | **Čech cohomology and cohomology** ← `lemma-cech-vanish-basis` |
| 1881 | Flasque sheaves |
| 2088 | The Leray spectral sequence |
| 2327 | Functoriality of cohomology |
| 2438 | Refinements and Čech cohomology |
| 2636 | Cohomology on Hausdorff quasi-compact spaces |
| 2955 | The base change map |
| 3050 | Proper base change in topology |
| 3170 | Cohomology and colimits |
| 3439 | Vanishing on Noetherian topological spaces |
| 3739 | Cohomology with support in a closed subset |
| 3857 | Cohomology on spectral spaces |
| 4071 | The alternating Čech complex |
| 4564 | Alternative view of the Čech complex |
| 4742 | Čech cohomology of complexes |
| 5792 | Flat resolutions |
| 6308 | Derived pullback |
| 6545 | Cohomology of unbounded complexes |
| 7156 | Cup product |
| 7813 | Some properties of K-injective complexes |

### Directive-specific lemma locations (deep map)

| Label | Line | Section | Likely Stacks tag (from directive seeds) |
|-------|------|---------|------------------------------------------|
| `lemma-describe-higher-direct-images` | 592 | §Locality of cohomology (l.488) | 01XJ |
| `lemma-cech-vanish-basis` | 1696 | §Čech cohomology and cohomology (l.1404) | 01EO |

**`lemma-describe-higher-direct-images` (line 592):**
Full lemma block: lines 591–603 (`\begin{lemma}` … `\end{lemma}`).
Statement reads: Let $f : X \to Y$ be a morphism of ringed spaces, $\mathcal{F}$ an
$\mathcal{O}_X$-module. The sheaves $R^if_*\mathcal{F}$ are the sheaves associated to
the presheaves $V \mapsto H^i(f^{-1}(V), \mathcal{F})$ with restriction mappings as in
Equation (cohomology-equation-restriction-mapping). (Proof: lines 605–627.)

**`lemma-cech-vanish-basis` (line 1696):**
Full lemma block: lines 1695–1714 (`\begin{lemma}` … `\end{lemma}`).
Statement reads: Let $X$ be a ringed space, $\mathcal{B}$ a basis, $\mathcal{F}$ an
$\mathcal{O}_X$-module. Given a set of open coverings $\text{Cov}$ satisfying:
(1) every $\mathcal{U} \in \text{Cov}$ has $U, U_i, U_{i_0\ldots i_p} \in \mathcal{B}$;
(2) for every $U \in \mathcal{B}$ the coverings from $\text{Cov}$ are cofinal;
(3) $\check{H}^p(\mathcal{U}, \mathcal{F}) = 0$ for all $p > 0$ and all
$\mathcal{U} \in \text{Cov}$;
then $H^p(U, \mathcal{F}) = 0$ for all $p > 0$ and $U \in \mathcal{B}$.
(Proof: lines 1716–1776.)

## Caveats
- The source file uses chapter-local label names (e.g. `\label{lemma-cech-vanish-basis}`
  without the `cohomology-` prefix seen in cross-chapter references). When referencing
  from another chapter in the Stacks Project, labels are prefixed with the chapter tag
  (`cohomology-lemma-cech-vanish-basis`).
- The Stacks tag numbers given above (01EO, 01XJ) are from the directive seeds; they
  have not been independently fetched and verified against the live tag server.
- "Cohomology of Schemes" (`coherent.tex`) is already local as `stacks-coherent.tex` —
  do not re-fetch.

## Quality / provenance
This is the authoritative verbatim source downloaded directly from the Stacks Project
GitHub repository (master branch, 2026-06-05). The Stacks Project is the definitive
reference for this material in algebraic geometry.
