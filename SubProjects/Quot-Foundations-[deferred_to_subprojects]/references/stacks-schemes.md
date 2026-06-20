# Stacks Project — Schemes (Chapter tag 020J)

## Citation
The Stacks Project Authors, "Stacks Project", https://stacks.math.columbia.edu, chapter "Schemes" (tag 020J, file `schemes.tex`).

## Slug
stacks-schemes

## Retrieval status
RETRIEVED — 2026-06-01

## Local source files
- `references/stacks-schemes.tex` — LaTeX source, VERIFIED (starts with `\input{preamble}`, 171 KB), retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/schemes.tex

## Why this source
A blueprint-writer is adding `lem:pullback_spec_tilde_iso` to `blueprint/src/chapters/Cohomology_FlatBaseChange.tex`. The block needs a verbatim `% SOURCE QUOTE:` citing `schemes-lemma-widetilde-pullback` (tag **01I9**), the Stacks lemma that `ψ* M̃ = (S ⊗_R M)~` for an affine morphism `Spec(S) → Spec(R)` induced by a ring map `R → S`.

## Contents map

### Sections (by line number in fetched .tex)

- §1 Introduction — line 17
- §2 Locally ringed spaces — line 32
- §3 Open immersions of locally ringed spaces — line 202
- §4 Closed immersions of locally ringed spaces — line 336
- §5 Affine schemes — line 502 (`section-affine-schemes`)
- §6 The category of affine schemes — line 760 (`section-category-affine-schemes`)
- **§7 Quasi-coherent sheaves on affines — line 1067** (`section-quasi-coherent-affine`) ← **TARGET SECTION**
- §8 Closed subspaces of affine schemes — line 1573
- §9 Schemes — line 1644
- §10 Immersions of schemes — line 1728
- §11 Zariski topology of schemes — line 1921
- §12 Reduced schemes — line 2144
- §13 Points of schemes — line 2301
- §14 Glueing schemes — line 2509
- §15 A representability criterion — line 2756
- §16 Existence of fibre products of schemes — line 2999
- §17 Fibre products of schemes — line 3131
- §18 Base change in algebraic geometry — line 3381
- §19 Quasi-compact morphisms — line 3568
- §20 Valuative criterion for universal closedness — line 3727
- §21 Separation axioms — line 4004
- §22 Valuative criterion of separatedness — line 4477
- §23 Monomorphisms — line 4537
- §24 Functoriality for quasi-coherent modules — line 4716 (`section-quasi-coherent`)

### Target lemma (deep map)

- **`lemma-widetilde-pullback`** — Stacks tag **01I9**, line **1242** of `stacks-schemes.tex`
  - Section: §7 "Quasi-coherent sheaves on affines" (line 1067)
  - `\begin{lemma}` at line 1241, `\label{lemma-widetilde-pullback}` at line 1242
  - Statement: two parts — (1) `ψ* M̃ = (S ⊗_R M)~` for the R-module M; (2) `ψ_* Ñ = (N_R)~` for the S-module N.
  - `\end{lemma}` at line 1256; proof lines 1258–1269.
  - Cross-references inside proof: `lemma-compare-constructions`, `modules-lemma-restrict-quasi-coherent`.

## Caveats
- This is the TeX source as of the GitHub master branch on 2026-06-01. Tags are stable by Stacks policy, but section structure may shift as new lemmas are added; always verify by label `lemma-widetilde-pullback` rather than line number in a future re-fetch.
- The companion pushforward part (2) `ψ_* Ñ = (N_R)~` is in the SAME lemma body at line 1253.

## Quality / provenance
The Stacks Project is the definitive open reference for algebraic geometry in the style used here. The file was fetched directly from the canonical GitHub repository (`stacks/stacks-project`), which is the authoritative source used to generate the website.
