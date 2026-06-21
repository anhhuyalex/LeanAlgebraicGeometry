# Stacks Project — varieties.tex (smooth implies regular, Tag 056S)

## Citation
The Stacks Project Authors, "The Stacks Project", stacks.math.columbia.edu, 2024.
Tag 056S: https://stacks.math.columbia.edu/tag/056S
Raw source: https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex

## Slug
stacks-smooth-regular-varieties

## Retrieval status
RETRIEVED — 2026-06-20

## Local source files
- `references/stacks-smooth-regular-varieties.tex` — LaTeX source, VERIFIED via `file` (reports "LaTeX document, ASCII text") — retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex

## Why this source
Blueprint sub-lemma 1 for `RiemannRoch_OcOfD.tex`: a smooth-of-relative-dimension-one curve over a field is regular in codimension one. This requires the verbatim Stacks statement+proof that a smooth morphism (over a field) implies the scheme is regular. Tag 056S is the canonical Stacks reference for this fact.

## Contents map (selected; this chapter has 11343 lines total)

### Resolved tags in this chapter

| Tag | Label | Section | Lines |
|-----|-------|---------|-------|
| **056S** | `varieties-lemma-smooth-regular` | §"Schemes smooth over fields" (`\label{section-smooth}`, l.4524) | `\begin{lemma}` l.4596 – `\end{proof}` l.4614 |
| (no tag given) | `varieties-lemma-geometrically-regular-smooth` | §"Varieties over fields" | `\begin{lemma}` l.2543 – `\end{proof}` l.2592 |

### Tag 056S — `lemma-smooth-regular` — lines 4596–4614

```latex
\begin{lemma}
\label{lemma-smooth-regular}
\begin{slogan}
Smooth over a field implies regular
\end{slogan}
Let $X \to \Spec(k)$ be a smooth morphism where $k$ is a field.
Then $X$ is a regular scheme.
\end{lemma}

\begin{proof}
(See also
Lemma \ref{lemma-geometrically-regular-smooth}.)
By
Algebra, Lemma \ref{algebra-lemma-characterize-smooth-over-field}
every local ring $\mathcal{O}_{X, x}$ is regular.
And because $X$ is locally of finite type over $k$ it is locally
Noetherian. Hence $X$ is regular by
Properties, Lemma \ref{properties-lemma-characterize-regular}.
\end{proof}
```

Dependencies cited in the proof:
- `algebra-lemma-characterize-smooth-over-field` = Tag **00TT** — in `references/stacks-regular-dvr-algebra.tex` lines 38612–38684 (see caveats below).
- `properties-lemma-characterize-regular` — in `references/stacks-coheight-properties.tex`.

### Section outline (§ "Schemes smooth over fields", lines 4524–end)

- l.4524 `\section{Schemes smooth over fields}` — `\label{section-smooth}`
- l.~4530–4595 Earlier lemmas in the section (smooth + dimension of fibres)
- l.4596 **`lemma-smooth-regular`** (Tag 056S) ← TARGET
- l.4616 `lemma-smooth-geometrically-normal`
- …

## Caveats

- Tag **02G1** (`morphisms-lemma-smooth-omega-finite-locally-free`) is in `morphisms.tex`, NOT in `varieties.tex`. It concerns the sheaf of differentials being locally free for a smooth morphism — it is a structural fact used to characterise smoothness, but is NOT the "smooth ⟹ regular" statement.
- The related lemma `lemma-geometrically-regular-smooth` (lines 2543–2592) gives the equivalence "geometrically regular at $x$" ↔ "smooth at $x$" for locally finite type $k$-schemes; it is more general than Tag 056S but subsumes it.
- Tag 00TT (`algebra-lemma-characterize-smooth-over-field`) is the key algebra-level fact cited in the proof of 056S. It already resides in `references/stacks-regular-dvr-algebra.tex` at lines 38612–38684 (full `algebra.tex` chapter, previously downloaded for Tag 00PD). **No separate download needed.**

## Quality / provenance
This is the authoritative Stacks Project source, fetched verbatim from the GitHub master branch. Tag 056S is the canonical reference for "smooth over a field ⟹ regular" in the Stacks Project.
