# Stacks Project — Derived Functors, Acyclic Objects, Leray's Acyclicity Lemma

## Citation
The Stacks Project Authors, "Stacks Project", online, continuously updated.
https://stacks.math.columbia.edu  (GitHub source: https://github.com/stacks/stacks-project)

## Slug
homological-acyclic

## Retrieval status
RETRIEVED — 2026-06-05

## Local source files
- `references/homological-acyclic-derived.tex` — LaTeX source, VERIFIED (starts with `\input{preamble}`, 12580 lines, 438K) — retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex
- `references/homological-acyclic-homology.tex` — LaTeX source, VERIFIED (starts with `\input{preamble}`, LaTeX confirmed, 262K) — retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/homology.tex

No PDFs retrieved (the Stacks Project does not publish per-chapter PDFs from GitHub raw; the TeX sources are the authoritative open form).

## Why this source
Needed by the blueprint-writer for a new chapter `Cohomology_AcyclicResolution.tex` which states the abstract homological-algebra theorem that an F-acyclic resolution computes the right derived functor. The exact tag numbers, statement text, and proof text will be pasted verbatim into `% SOURCE QUOTE:` / `% SOURCE QUOTE PROOF:` LaTeX comments. This is the primary open-access source for the definition of a right-F-acyclic object and for Leray's acyclicity lemma (Tag 015E).

## Contents map — `homological-acyclic-derived.tex` (derived.tex)

The file is `derived.tex`, the Stacks Project chapter on derived categories and derived functors.

Relevant section structure (line numbers in the downloaded file):

| Line | Label / Tag | Content |
|------|-------------|---------|
| 5161 | `section-derived-functors-classical` | §"Derived functors on derived categories" — sets up the classical situation |
| **5253–5271** | **Tag 0157** `definition-derived-functor` | **Definition**: right derived functors $RF$, left derived functors $LF$; items 3–4 define *"right acyclic for $F$"* (= *"acyclic for $RF$"*) and *"left acyclic for $F$"*. This is the primary definition of F-acyclic objects. |
| 5384 | Tag 05T8 `lemma-subcategory-right-acyclics` | Lemma: if $\mathcal{I}$ is closed under extensions and direct summands and $F$ exact on SES from $\mathcal{I}$, every object of $\mathcal{I}$ is acyclic for $RF$ |
| 5439 | Tag 05T9 `lemma-subcategory-left-acyclics` | Dual for left derived functors |
| 5465 | `section-higher-derived` | §"Higher derived functors" — higher derived functors $R^iF$, criterion for acyclics, Leray lemma |
| **5594–5617** | **Tag 015C** `lemma-F-acyclic` | **Lemma**: $A$ is right acyclic for $F$ iff ($F(A)\cong R^0F(A)$ and $R^iF(A)=0$ for $i>0$); if $F$ is left exact, iff $R^iF(A)=0$ for all $i>0$. Statement lines 5594–5606; proof lines 5608–5617. |
| 5619–5657 | Tag 015D `lemma-F-acyclic-ses` | Lemma: SES behaviour of right acyclics; if two of three terms are acyclic so is the third (under appropriate surjectivity) |
| 5658–5691 | Tag 015E-predecessor `lemma-right-derived-delta-functor` | Lemma: $\{R^iF,\delta\}$ is a $\delta$-functor; universal when enough acyclics exist |
| **5692–5783** | **Tag 015E** `lemma-leray-acyclicity` | **Leray's acyclicity lemma (THE KEY THEOREM)**: If $A^\bullet$ is a bounded below complex of right $F$-acyclic objects and $RF$ is defined at $A^\bullet$, then $F(A^\bullet) \to RF(A^\bullet)$ is an isomorphism in $D^+(\mathcal{B})$, i.e., $A^\bullet$ *computes* $RF$. Statement lines 5692–5705; proof (by truncation/induction) lines 5707–5783. |
| **5785–5876** | **Tag 05TA** `proposition-enough-acyclics` | **Proposition**: If every object of $\mathcal{A}$ embeds into an $RF$-acyclic, then $RF : D^+(\mathcal{A}) \to D^+(\mathcal{B})$ is everywhere defined, and any bounded below complex whose terms are acyclic for $RF$ computes $RF$. Statement lines 5785–5811; proof lines 5813–5876. |
| 6915 | `section-right-derived-functor` | §"Right derived functors and injective resolutions" — classical setup via injective resolutions |
| 6924 | `lemma-injective-acyclic` | Lemma: injective objects (and bounded below complexes of injectives) are acyclic for any additive functor |

## Contents map — `homological-acyclic-homology.tex` (homology.tex)

Relevant section (background on delta-functors, referenced from derived.tex):

| Line | Label / Tag | Content |
|------|-------------|---------|
| 2621 | `section-cohomological-delta-functor` | §"Cohomological delta-functors" |
| 2625 | **Tag 010Q** `definition-cohomological-delta-functor` | Definition of cohomological $\delta$-functor $\{T^i,\delta\}$ |
| 2674 | Tag 010R `definition-morphism-delta-functors` | Morphism of delta-functors |
| ~2693 | **Tag 010S** `definition-universal-delta-functor` | Definition of *universal* delta-functor (effaceable implies universal) |
| **2705** | **Tag 010T** `lemma-efface-implies-universal` | Lemma: an effaceable $\delta$-functor is universal |
| 2754 | Tag 010U `lemma-uniqueness-universal-delta-functor` | Lemma: uniqueness of universal $\delta$-functor |

## Caveats
- The Stacks Project uses the bounded-below derived category $D^+(\mathcal{A})$ throughout, so statements are in that generality. For the blueprint's purposes (computing cohomology via acyclic resolutions) this is strictly more general than the classical textbook formulation over abelian categories with enough injectives.
- The proof of Tag 015E (Leray's acyclicity lemma) proceeds by truncation of bounded-below complexes rather than the explicit "dimension-shifting / short exact sequence of cosyzygies" argument. The short-exact-sequence induction is implicit (each truncation step isolates a SES), but the Stacks proof is phrased in terms of distinguished triangles.
- Weibel *An Introduction to Homological Algebra* (CUP 1994) was searched. The only accessible copy found is at `https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/weibel-homv2.pdf` (HTTP 200, 17.7 MB) on a University of Rochester faculty page, but as this is not the author's own page and authorization cannot be confirmed, it was not downloaded. The Stacks Project source fully covers the needed content.
- No piracy channels were used.

## Quality / provenance
The Stacks Project is the definitive open-access reference for algebraic geometry and homological algebra. The `.tex` files are fetched directly from the master branch on GitHub (`stacks/stacks-project`), which is the canonical source used to generate `https://stacks.math.columbia.edu`. Tags are permanent and citable.
