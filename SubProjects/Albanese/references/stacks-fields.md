# Stacks Project — Chapter 9 "Fields" (fields.tex)

## Citation
The Stacks Project authors, "Fields", Chapter 9 of *The Stacks Project*,
https://stacks.math.columbia.edu/. Chapter source `fields.tex` retrieved from
the GitHub mirror.

## Slug
stacks-fields

## Retrieval status
RETRIEVED — 2026-05-20

## Local source files
- `references/stacks-fields.tex` — LaTeX chapter source, VERIFIED (144442 bytes,
  3792 lines, plain `.tex`) — retrieved from
  `https://raw.githubusercontent.com/stacks/stacks-project/master/fields.tex`

Tag→label map cross-checked against the repo's `tags/tags`.

## Why this source
Backs (S3.pi.2) in `RigidityKbar.tex` — the purely-inseparable-extension step
of the separability chain. Quote the decomposition lemma verbatim.

## Tags covered (locations in the fetched file)

| Tag | Stacks label | Kind | Stacks no. | Line in fetched .tex | Backs |
| --- | --- | --- | --- | --- | --- |
| **09HD** | `section-purely-inseparable` | Section | §9.14 "Purely inseparable extensions" | `\section{...}` **L1572–1573** | (S3.pi.2) |
| **030K** | `lemma-separable-first` | Lemma | Lemma 9.14.6 | `\begin{lemma}\label{...}` **L1703–1704** | (S3.pi.2) |

Details:

- **09HD** (`\label{section-purely-inseparable}`, L1573): "Purely inseparable
  extensions" — section opening + `\begin{definition}` `definition-purely-inseparable`
  at L1580+. Section spans L1572 → next section.
- **030K** (`\label{lemma-separable-first}`, L1704): the separable-then-inseparable
  factorisation. Statement L1704–1714, with `\begin{slogan}` "Any algebraic field
  extension is uniquely a separable field extension followed by a purely
  inseparable one." and the precise claim: "Let `E/F` be an algebraic field
  extension. There exists a unique subextension `E/E_sep/F` such that `E_sep/F`
  is separable and `E/E_sep` is purely inseparable." Proof L1717+. The very next
  block `definition-insep-degree` (L1729+) defines inseparable degree via this lemma.

## Caveats
Tag numbers (09HD, 030K) are the permanent citation key; the decimal numbers
(9.14, 9.14.6) are auto-generated and snapshot-dependent — they matched this
snapshot. Line numbers exact for this fetched copy (master, 2026-05-20).

## Quality / provenance
Authoritative verbatim source from stacks/stacks-project GitHub master; tag↔label
confirmed against `tags/tags`; both statements read and confirmed in-file.
