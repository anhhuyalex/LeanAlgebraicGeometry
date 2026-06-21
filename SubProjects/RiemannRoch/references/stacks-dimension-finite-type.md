# Stacks Project — dimension theory of finite-type algebras and integral extensions

## Citation
The Stacks Project, Chapter "Commutative Algebra" (`algebra.tex`). Tags 00OH, 00OJ,
00OK, 00OY, 00P0. https://stacks.math.columbia.edu/

## Slug
stacks-dimension-finite-type

## Retrieval status
RETRIEVED — 2026-06-21. The relevant chapter `algebra.tex` is already present locally
as `references/stacks-regular-dvr-algebra.tex` (the same file used for Tags 00TT/00PD);
this pointer indexes the dimension-theory tags inside it. Tag numbers were confirmed
against the Stacks `tags/tags` label→tag database
(https://raw.githubusercontent.com/stacks/stacks-project/master/tags/tags).

## Local source files
- `references/stacks-regular-dvr-algebra.tex` — LaTeX source of Stacks `algebra.tex`
  (already downloaded for the regular/DVR chapter; quote verbatim from here).

## Why this source
Grounds the new chapter `RiemannRoch_CurveKrullDim.tex`: the bound
`ringKrullDim C.left ≤ 1` for a smooth relative-dimension-one curve over an
algebraically closed field. Provides (i) the Cohen–Seidenberg dimension inequality
for integral/module-finite extensions and (ii) the equality dim = transcendence
degree for finite-type domains over a field.

## Contents map (label — Stacks Tag — line in stacks-regular-dvr-algebra.tex)
- §"Homomorphisms and dimension" — l.27309
  - `lemma-dimension-going-up` — **Tag 00OH** — l.27317 (going up/down + surjective ⇒ dim R ≤ dim S)
  - `lemma-integral-dim-up` — **Tag 00OJ** — l.27352 (S integral over R ⇒ dim R ≥ dim S)
  - `lemma-integral-sub-dim-equal` — **Tag 00OK** — l.27365 (R ⊂ S integral ⇒ dim R = dim S)
- §"Noether normalization" — l.27924
  - `lemma-Noether-normalization` — **Tag 00OY** — l.28029 (finite injective k[y_1..y_r] → S, r = dim S)
- §"Dimension of finite type algebras over fields, reprise" — l.28171
  - `lemma-dimension-prime-polynomial-ring` — **Tag 00P0** — l.28182
    (finite-type domain S over a field k: dim S = trdeg(Frac S / k))

## Caveats
The file is the full `algebra.tex` (~48k lines); navigate by the line numbers above.
The `r` of Noether normalization (00OY) is identified with `dim S` inside the lemma
itself, and with `trdeg(Frac S / k)` by 00P0. NONE of these tags supplies the bridge
`r = relative dimension of a smooth morphism`; that identification is the chapter's
flagged deep residual, not covered by any tag here.

## Quality / provenance
Definitive. The Stacks Project is the canonical open reference; tag numbers
cross-checked against the official label→tag database.
