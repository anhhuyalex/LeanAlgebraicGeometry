# Stacks Project — Chapter 30 "Cohomology of Schemes" (coherent.tex)

## Citation
The Stacks Project authors, "Cohomology of Schemes", Chapter 30 of *The Stacks
Project*, https://stacks.math.columbia.edu/. Chapter source `coherent.tex`
retrieved from the GitHub mirror.

## Slug
stacks-coherent

## Retrieval status
RETRIEVED — 2026-05-20

## Local source files
- `references/stacks-coherent.tex` — LaTeX chapter source, VERIFIED (313116 bytes,
  8138 lines, plain `.tex`) — retrieved from
  `https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex`

Tag→label map cross-checked against the repo's `tags/tags`.

## Why this source
The `H^0` specialisation of this flat-base-change lemma is (S3.pi.1) in
`RigidityKbar.tex`. (It is also the lemma 0BUG's proof invokes for part (4) —
see `stacks-varieties.md`.)

## Tag covered (location in the fetched file)

| Tag | Stacks label | Kind | Stacks no. | Line in fetched .tex | Backs |
| --- | --- | --- | --- | --- | --- |
| **02KH** | `lemma-flat-base-change-cohomology` | Lemma `[Flat base change]` | Lemma 30.5.2 | `\begin{lemma}[Flat base change]\label{...}` **L947–948** | (S3.pi.1) |

Details:

- **02KH** (`\label{lemma-flat-base-change-cohomology}`, L948): titled
  `[Flat base change]`. Statement L948–971. For a cartesian square with `g` flat
  and `f` quasi-compact + quasi-separated, and `𝓕` quasi-coherent with pullback
  `𝓕' = (g')^*𝓕`, for all `i ≥ 0`:
  - **(1)** the base-change map `g^* R^i f_* 𝓕 → R^i f'_* 𝓕'` is an isomorphism;
  - **(2)** (the `H^0` / affine specialisation = (S3.pi.1)) if `S = Spec(A)` and
    `S' = Spec(B)`, then `H^i(X, 𝓕) ⊗_A B = H^i(X', 𝓕')`.
  Proof begins L973+.

## Caveats
Tag 02KH is the permanent citation key; "Lemma 30.5.2" is auto-generated and
snapshot-dependent (matched this snapshot). Line numbers exact for master as of
2026-05-20.

## Quality / provenance
Authoritative verbatim source from stacks/stacks-project GitHub master; tag↔label
confirmed against `tags/tags`; statement read and confirmed in-file (two-part
lemma; part (2) is the `H^0`-with-base-change form the blueprint needs).
