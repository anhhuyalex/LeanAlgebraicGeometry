# Stacks Project — Divisors (divisors.tex)

## Citation
The Stacks Project Authors, "Stacks Project", https://stacks.math.columbia.edu, Chapter 31 "Divisors".
https://raw.githubusercontent.com/stacks/stacks-project/master/divisors.tex

## Slug
stacks-divisors

## Retrieval status
RETRIEVED — 2026-05-30

## Local source files
- references/stacks-divisors.tex — LaTeX source, VERIFIED (starts with `\input{preamble}`, 366 KB) — retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/divisors.tex

## Why this source
Downloaded as a seed for slug `stacks-pic-invertible` (Picard group / invertible
modules references).  Tag 01CR ("Picard groups of schemes") is NOT in this file
(see Caveats); but divisors.tex is useful for the Cartier divisor / Weil divisor
comparison sections (tags 01E8 §eff-Cartier, 0EKM §Weil, 0BE0 §cl-group-vs-Pic)
that may be needed by adjacent blueprint chapters.

## Contents map

Stacks Project Chapter 31 "Divisors".

- §31.1   Introduction — line 17
- §31.2   Associated points — line 26
- §31.3   Morphisms and associated points — line 291
- §31.4   Embedded points — line 347
- §31.5   Weakly associated points — line 548
- §31.6   Morphisms and weakly associated points — line 810
- §31.7   Relative assassin — line 1044
- §31.8   Relative weak assassin — line 1194
- §31.9   Fitting ideals — line 1246
- §31.10  The singular locus of a morphism — line 1529
- §31.11  Torsion free modules — line 1641
- §31.12  Ranks of modules — line 1869
- §31.13  Reflexive modules — line 1992
- §31.14  Effective Cartier divisors — line 2376
- §31.15  Effective Cartier divisors and invertible sheaves — line 2651
  (Discusses $\mathcal{L} \cong \mathcal{O}_X(D)$ for effective Cartier divisors $D$;
  mentions Picard group in passing at line 2686 but does NOT define it.)
- §31.16  Effective Cartier divisors on Noetherian schemes — line 2917
- §31.17  Complements of affine opens — line 3341
- §31.18  Norms — line 3586
  (Norm map $\text{Norm}_\pi : \Pic(X) \to \Pic(Y)$ at line 3660.)
- §31.19  Relative effective Cartier divisors — line 3938
- §31.20  The normal cone of an immersion — line 4295
- §31.21  Regular ideal sheaves — line 4513
- §31.22  Regular immersions — line 4889
- §31.23  Relative regular immersions — line 5246
- §31.24  Meromorphic functions and sections — line 5855
- §31.25  Meromorphic functions and sections; Noetherian case — line 6232
- §31.26  Meromorphic functions and sections; reduced case — line 6417
- §31.27  Weil divisors — line 6549
- **§31.28  The Weil divisor class associated to an invertible module** — line 6707
  (Map $c_1 : \Pic(X) \to \text{Cl}(X)$, line 6713.)
- §31.29  More on invertible modules — line 6961
  (UFD Picard groups, $\Pic(\mathbf{P}^n_R)$.)
- §31.30  Weil divisors on normal schemes — line 7308
- §31.31  Relative Proj — line 7637
- §31.32  Closed subschemes of relative proj — line 7897
- §31.33  Blowing up — line 8277
- §31.34  Strict transform — line 8747
- §31.35  Admissible blowups — line 9081
- §31.36  Blowing up and flatness — line 9292
- §31.37  Modifications — line 9403

## Caveats

**Tag 01CR is NOT in this file.**  The directive for slug `stacks-pic-invertible`
suggested that 01CR ("Picard groups of schemes") lives in the Divisors chapter.
This is incorrect.  The Stacks tags file gives `01CR → modules-section-invertible`,
meaning tag 01CR is Section 17.25 of the "Modules on Ringed Spaces" chapter
(references/stacks-modules.tex, lines 4038–4411).  This file (divisors.tex)
discusses Picard groups only incidentally (as the target of the $c_1$ map, norm
maps, etc.); it does not define $\Pic(X)$.

## Quality / provenance
Authoritative: fetched verbatim from the master branch of the official Stacks Project
GitHub repository (stacks/stacks-project).
