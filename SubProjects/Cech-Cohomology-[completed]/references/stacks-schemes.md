# Stacks Project — "Schemes" chapter

## Citation
The Stacks Project Authors, "Schemes", in *The Stacks Project*, 2024.
https://stacks.math.columbia.edu/tag/01HR (chapter entry point)
https://github.com/stacks/stacks-project/blob/master/schemes.tex (TeX source)

## Slug
stacks-schemes

## Retrieval status
RETRIEVED — 2026-06-06

## Local source files
- `references/stacks-schemes.tex` — LaTeX source, VERIFIED (opens with `\input{preamble}`, 4914 lines) — retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/schemes.tex

## Why this source
Provides the foundational construction of the quasi-coherent sheaf $\widetilde{M}$
on $\operatorname{Spec} R$ and the key lemma that $\Gamma(\operatorname{Spec} R, \widetilde{M}) = M$
and $\Gamma(D(f), \widetilde{M}) = M_f$. This backs the formalization of
`lem:sections_of_tildeM` / `lem:spec_sheaves` in the Čech-cohomology blueprint.

## Contents map

| Line | Label / tag | Title / description |
|------|-------------|---------------------|
| 17   | §1 | Introduction |
| 32   | §2 | Locally ringed spaces |
| 93   |  `definition-locally-ringed-space` | Definition of locally ringed space |
| 202  | §3 | Open immersions of locally ringed spaces |
| 336  | §4 | Closed immersions of locally ringed spaces |
| 502  | **§5 "Affine schemes"** | ← **relevant section** |
| 520  | `lemma-standard-open` | $D(f) = D(g) \Leftrightarrow \sqrt{(f)} = \sqrt{(g)}$; canonical isomorphism $R_f \cong R_g$ |
| 580  | `definition-standard-covering` | Standard open coverings of $\operatorname{Spec}(R)$ |
| 593–652 | *(prose)* | **Construction of $\widetilde{M}$**: presheaf on basis of standard opens, $\widetilde{M}(D(f)) := M_f$; stalk $= M_\mathfrak{p}$; sheaf condition verified (lines 633–652) |
| 671  | `definition-structure-sheaf` | Structure sheaf $\mathcal{O}_{\operatorname{Spec}(R)}$; definition of $\widetilde{M}$ as sheaf |
| **692** | **`lemma-spec-sheaves` (tag 01HV)** | **KEY LEMMA** — $\Gamma(\operatorname{Spec}(R), \widetilde{M}) = M$; $\Gamma(D(f), \widetilde{M}) = M_f$; stalks $= M_\mathfrak{p}$; exactness of $M \mapsto \widetilde{M}$ |
| 731  | `definition-affine-scheme` | Affine scheme |
| 760  | §6 | The category of affine schemes |
| 841  | `lemma-morphism-into-affine` | Morphisms to affines via ring maps |
| 954  | `lemma-category-affine-schemes` | Equivalence: affine schemes ↔ opposite of Rings |
| 1067 | §7 "Quasi-coherent sheaves on affines" | ← secondary relevant section |
| 1078 | `lemma-compare-constructions` | Comparison of two sheaf constructions ($\mathcal{F}_M$ vs $\widetilde{M}$) |
| 1113 | `lemma-widetilde-constructions` | $\widetilde{M \otimes_R N} \cong \widetilde{M} \otimes \widetilde{N}$; Sym, Ext, Hom analogues |
| 1279 | `lemma-quasi-coherent-affine` | $\widetilde{M}$ is quasi-coherent; $\Gamma(X, -)$ is quasi-inverse |
| 1390 | `lemma-equivalence-quasi-coherent` | Equivalence: $R$-mod $\simeq$ QCoh($\operatorname{Spec} R$) |
| 1644 | §9 "Schemes" | General schemes (gluing) |
| 2509 | §15 | Glueing schemes |
| 2999 | §17 | Existence of fibre products |
| 3131 | §18 | Fibre products of schemes |
| 4716 | §28 | Functoriality for quasi-coherent modules |

## Key lemma verbatim location

**`lemma-spec-sheaves`**, tag **01HV**, lines **692–728** of `stacks-schemes.tex`:
- Item (2): $\Gamma(\operatorname{Spec}(R), \widetilde{M}) = M$ — line 698
- Item (4): $\Gamma(D(f), \widetilde{M}) = M_f$ — lines 701–702

Construction prose (definition of $\widetilde{M}(D(f)) := M_f$): lines 593–603.

## Caveats
The file uses `\input{preamble}` — macros (`\Spec`, `\colim`, `\SheafHom`, etc.) are defined
in `preamble.tex`, not in this file. The tag 01HV is the canonical Stacks tag for
`lemma-spec-sheaves`; Stacks tags are stable identifiers.

## Quality / provenance
Definitive reference — the Stacks Project is the canonical open-access textbook for
algebraic geometry used by the Mathlib/Lean4 community. Retrieved directly from the
official GitHub mirror at commit HEAD of `master` branch on 2026-06-06.
