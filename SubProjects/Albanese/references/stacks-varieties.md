# Stacks Project — Chapter 33 "Varieties" (varieties.tex)

## Citation
The Stacks Project authors, "Varieties", Chapter 33 of *The Stacks Project*,
https://stacks.math.columbia.edu/. Chapter source `varieties.tex` retrieved
from the GitHub mirror.

## Slug
stacks-varieties

## Retrieval status
RETRIEVED — 2026-05-20

## Local source files
- `references/stacks-varieties.tex` — LaTeX chapter source, VERIFIED (447330 bytes,
  11342 lines, plain `.tex`) — retrieved from
  `https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex`

Tag→label map cross-checked against
`https://raw.githubusercontent.com/stacks/stacks-project/master/tags/tags`.

## Why this source
Backs the chart-algebra separability chain (S3.*) in `RigidityKbar.tex`.
Three of the four tags here (035U, 04QM/056T, 0BUG) underpin (S3.sep.1) and
(S3.sep.2) and the whole (S3.*) decomposition. Writers must quote the lemma
statements verbatim via `% SOURCE QUOTE:`.

## Tags covered (locations in the fetched file — quote from these lines)

| Tag | Stacks label | Kind | Stacks no. | Line in fetched .tex | Backs |
| --- | --- | --- | --- | --- | --- |
| **035U** | `section-geometrically-reduced` | Section | §33.6 "Geometrically reduced schemes" | `\section{...}` **L322–323** | (S3.sep.1) |
| **04QM** | `section-smooth` | Section | §33.25 "Schemes smooth over fields" | `\section{...}` **L4524–4525** | (S3.sep.1) |
| **056T** | `lemma-smooth-geometrically-normal` | Lemma | Lemma 33.25.4 | `\begin{lemma}\label{...}` **L4616–4617** | (S3.sep.1) |
| **0BUG** | `lemma-proper-geometrically-reduced-global-sections` | Lemma | Lemma 33.9.3 | `\begin{lemma}\label{...}` **L1932–1933** | (S3.sep.2), whole (S3.*) chain |

Details:

- **035U** (`\label{section-geometrically-reduced}`, L323): section opening the
  geometrically-reduced theory; contains `\begin{definition}` of geometrically
  reduced just below (L330+). Section spans L322 → next `\section` at L679.
- **04QM** (`\label{section-smooth}`, L4525): "Schemes smooth over fields";
  section spans L4524 → next `\section{Types of varieties}` at L4837.
- **056T** (`\label{lemma-smooth-geometrically-normal}`, L4617): statement at
  L4617–4624 — "Let `X → Spec(k)` be a smooth morphism … Then `X` is
  geometrically regular, geometrically normal, and geometrically reduced over
  `k`." (This is the Lemma 33.25.4 the directive names as tag 056T.) Proof L4626+.
- **0BUG** (`\label{lemma-proper-geometrically-reduced-global-sections}`, L1933):
  the eight-part lemma on `A = H^0(X, 𝒪_X)` for `X/k` proper, statement L1933–1957.
  **Part (4)** (L1944–1945): "if `X` is geometrically reduced, then `k_i` is
  finite separable over `k`." Proof of (4) at L1980+ (uses 02KH = flat base
  change and Algebra lemmas `characterize-separable-field-extensions` +
  `geometrically-reduced-finite-purely-inseparable-extension`). Lives in
  §33.9 "Geometrically integral schemes" (section starts L1890).

## Section map (top level, for orientation)
- §33.1 Introduction (L17) · §33.2 Notation (L31) · §33.3 Varieties (L46)
- §33.6 Geometrically reduced schemes — **L322** ← 035U
- §33.7 Geometrically connected (L679) · §33.8 Geometrically irreducible (L1329)
- §33.9 Geometrically integral schemes — L1890 (contains 0BUG at **L1933**)
- §33.10 Geometrically normal (L2093) · §33.12 Geometrically regular (L2341)
- §33.25 Schemes smooth over fields — **L4524** ← 04QM, contains 056T at **L4617**

## Caveats
Stacks **tag** numbers (035U etc.) are permanent and the authoritative citation
key. The decimal **section/lemma** numbers (33.25.4 etc.) are auto-generated and
can shift between snapshots — the directive's numbers matched this snapshot, but
cite by tag + label, not by decimal number. Line numbers above are exact for
*this* fetched copy only (master as of 2026-05-20).

## Quality / provenance
Authoritative: verbatim chapter source from the official stacks/stacks-project
GitHub master. Tag↔label correspondence confirmed against the repo's `tags/tags`
database; each statement read and confirmed in the fetched file.
