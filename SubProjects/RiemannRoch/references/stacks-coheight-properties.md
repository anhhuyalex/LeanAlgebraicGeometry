# Stacks Project — properties.tex (codimension = dim of local ring, Tag 02IZ)

## Citation
The Stacks Project Authors, "The Stacks Project", stacks.math.columbia.edu, 2024.
Tag 02IZ: https://stacks.math.columbia.edu/tag/02IZ
Raw source: https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex

## Slug
stacks-coheight-properties

## Retrieval status
RETRIEVED — 2026-06-20

## Local source files
- `references/stacks-coheight-properties.tex` — LaTeX source, VERIFIED via `file` (reports "LaTeX document, ASCII text") — retrieved from https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex

## Why this source
Blueprint sub-lemma 2 for `RiemannRoch_OcOfD.tex`: to prove a smooth curve is regular *in codimension one*, one needs the bridge between the topological notion of coheight (codimension of the closure of a point) and the algebraic notion of Krull dimension of the local ring. Tag 02IZ is the verbatim Stacks statement of `codim({x}^{cl}, X) = dim(𝒪_{X,x})`. Combined with Tag 056S (smooth ⟹ regular stalks), it reduces "regular in codimension one" to "local ring at a codimension-one point has Krull dimension 1 and is regular".

## Contents map (selected; this chapter has 5424 lines total)

### Resolved tags in this chapter

| Tag | Label | Section | Lines |
|-----|-------|---------|-------|
| **02IZ** | `properties-lemma-codimension-local-ring` | §"Dimension" (`\section{Dimension}`, l.1196) | `\begin{lemma}` l.1258 – `\end{proof}` l.1274 |

### Tag 02IZ — `lemma-codimension-local-ring` — lines 1258–1274

```latex
\begin{lemma}
\label{lemma-codimension-local-ring}
Let $X$ be a scheme. Let $Y \subset X$ be an irreducible closed
subset. Let $\xi \in Y$ be the generic point. Then
$$
\text{codim}(Y, X) = \dim(\mathcal{O}_{X, \xi})
$$
where the codimension is as defined in
Topology, Definition \ref{topology-definition-codimension}.
\end{lemma}

\begin{proof}
By Topology, Lemma \ref{topology-lemma-codimension-at-generic-point}
we may replace $X$ by an affine open neighbourhood of $\xi$. In this
case the result follows easily from
Algebra, Lemma \ref{algebra-lemma-irreducible-components-containing-x}.
\end{proof}
```

Dependencies cited in the proof:
- `topology-lemma-codimension-at-generic-point` — in `topology.tex` (not separately downloaded; standard Stacks topology chapter).
- `algebra-lemma-irreducible-components-containing-x` — in `references/stacks-regular-dvr-algebra.tex`.

### Section outline (§ "Dimension", lines 1196–~1320)

- l.1196 `\section{Dimension}` — `\section{Dimension}`
- l.~1200–1257 Earlier lemmas (dimension definition, open subsets)
- l.1258 **`lemma-codimension-local-ring`** (Tag 02IZ) ← TARGET
- l.1276 `lemma-generic-point` (corollary: $x$ generic point of component iff $\dim\mathcal{O}_{X,x} = 0$)
- l.1283 `lemma-locally-Noetherian-dimension-0`
- …

## Caveats

- Tag **005X** (`topology-lemma-jacobson-inherited`) is in `topology.tex`, NOT `properties.tex`, and concerns Jacobson spaces — it is NOT the codimension ↔ local ring dimension statement. The dispatcher's candidate was correct: **02IZ** (not 005X) is the right tag for the coheight bridge.
- The codimension on the left-hand side of the identity is the *topological* codimension of the irreducible closed subset $Y = \overline{\{x\}}$ in $X$ (lengths of chains of irreducible closed subsets); the right-hand side is the Krull dimension of the local ring at the generic point $\xi$ of $Y$, which for a point $x \in X$ is $\dim\mathcal{O}_{X,x}$ (taking $Y = \overline{\{x\}}$, $\xi = x$).

## Quality / provenance
This is the authoritative Stacks Project source, fetched verbatim from the GitHub master branch. Tag 02IZ is the canonical reference for the codimension-local-ring dimension bridge in the Stacks Project.
