# Stacks Project — Chapter 10 "Commutative Algebra" (algebra.tex)

## Citation
The Stacks Project authors, "Commutative Algebra", Chapter 10 of *The Stacks
Project*, https://stacks.math.columbia.edu/. Chapter source `algebra.tex`
retrieved from the GitHub mirror.

## Slug
stacks-algebra

## Retrieval status
RETRIEVED — 2026-05-20

## Local source files
- `references/stacks-algebra.tex` — LaTeX chapter source, VERIFIED (1770321 bytes,
  47870 lines, plain `.tex`; **large file — jump straight to the line below**) —
  retrieved from
  `https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex`

Tag→label map cross-checked against the repo's `tags/tags`.

## Why this source
Backs (BR.2)–(BR.5) in `RigidityKbar.tex` — the (BR.*) basis-of-differentials
decomposition. Tag 00T7 gives the explicit free basis `dx_{c+1},…,dx_n` for
`Ω_{S/R}` of a standard smooth algebra.

## Tag covered (location in the fetched file)

| Tag | Stacks label | Kind | Stacks no. | Line in fetched .tex | Backs |
| --- | --- | --- | --- | --- | --- |
| **00T7** | `lemma-standard-smooth` | Lemma | Lemma 10.137.6 | `\begin{lemma}\label{...}` **L37258–37259** | (BR.2)–(BR.5) |

Details:

- **00T7** (`\label{lemma-standard-smooth}`, L37259): in §10.137 "Smooth ring
  maps". The `\begin{definition}` of *standard smooth algebra* sits just above
  (L37248+). Statement of the lemma L37259–37287, a seven-part list for a
  standard smooth `S = R[x_1,…,x_n]/(f_1,…,f_c) = R[x_1,…,x_n]/I`:
  - **part (1)** `R → S` is smooth;
  - **part (2)** (the one the directive needs) "the `S`-module `Ω_{S/R}` is free
    on `dx_{c+1}, …, dx_n`";
  - part (3) `I/I^2` free on classes of `f_1,…,f_c`;
  - parts (4)–(7) localisation / base-change / global complete intersection.
  Proof begins L37290 (via the naive cotangent complex of the presentation).

## Caveats
Tag 00T7 is the permanent citation key; "Lemma 10.137.6" is auto-generated and
snapshot-dependent (matched this snapshot). `algebra.tex` is ~48k lines —
use the line numbers above, do not scroll. Exact for master as of 2026-05-20.

## Quality / provenance
Authoritative verbatim source from stacks/stacks-project GitHub master; tag↔label
confirmed against `tags/tags`; statement read and confirmed in-file (the 7-part
list with part (2) giving the free basis `dx_{c+1},…,dx_n`).
