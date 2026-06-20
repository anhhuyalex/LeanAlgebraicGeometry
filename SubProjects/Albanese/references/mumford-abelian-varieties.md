# Abelian Varieties (Mumford)

## Citation
David Mumford, "Abelian Varieties", Tata Institute of Fundamental Research
Studies in Mathematics 5, Oxford University Press, 1970 (TIFR, Bombay).
The canonical reference for the theorem of the cube + rigidity lemma circle.

## Slug
mumford-abelian-varieties

## Retrieval status
RETRIEVED — 2026-05-20 (file placed in `references/` by the project user this iter;
this card only registers + maps it — it was NOT re-downloaded).

## Local source files
- `references/mumford-abelian-varieties.pdf` — PDF, VERIFIED (`%PDF-1.5` header,
  `%%EOF` trailer, 290 pages, ~13.6 MB; verified by byte inspection + pypdf parse
  since `file`/`pdftotext`/`pdftoppm` are not installed on this host). This is a
  **scanned-image** PDF: pages carry no text layer, so locations below were read by
  rendering page images (pypdf `page.images` → PIL) and inspecting them visually.
  Quote from the rendered PDF, not from text extraction (there is none).

(No LaTeX source — this is a 1970 scan.)

## Why this source
THE canonical reference for project route (c) (the genus-0 Jacobian arm): the
characteristic-free abelian-variety **rigidity lemma** + **theorem of the cube** stack
that proves "a morphism from a genus-0 curve (≅ ℙ¹) into an abelian variety is
constant" without Serre duality / `df=0` / Pic⁰ representability. Milne's notes
(`references/abelian-varieties.pdf`) reproduce these same results; Mumford is the
primary source they cite. Compare hypotheses across the two (see Caveats).

## Page offset
Document (book) page **N** ↦ PDF/reader page **N + 11** for the Arabic body
(verified: book p.1 = PDF p.12; book p.41 = PDF p.52; book p.57 = PDF p.68).
The Contents pages are PDF p.10–11.

## Contents map
Book page numbers are Mumford's own; PDF page = book + 11 (body).

**Front matter**
- Contents — PDF p.10–11. Introduction — book p.v.

**Chapter I — Analytic Theory** (book p.1, PDF p.12)
- §1 Complex Tori — p.1 · §2 Line bundles on a complex torus — p.13 · §3 Algebraizability of tori — p.24

**Chapter II — Algebraic Theory via Varieties** (book p.39, PDF p.50)
- **§4 Definition of abelian varieties — p.39 (PDF p.50)**   ← directive: conventions + rigidity lemma + no-rational-curves
  - **Definition** of abelian variety ("a *complete* algebraic variety† over `k`
    with a group law `m : X×X→X` such that `m` and inverse are morphisms"; footnote †
    = "irreducible") — p.39 (PDF p.50).   ← standing conventions/hypotheses
  - "(ii) As a group, `X` is commutative" (first proof, via invariant differentials /
    `Aut` is affine) — p.41 (PDF p.52).
  - **RIGIDITY LEMMA (Form I.)** "Let `X` be a *complete* variety, `Y` and `Z` any
    varieties, and `f : X×Y→Z` a morphism such that for some `y₀∈Y`, `f(X×{y₀})` is a
    single point `z₀`. Then there is a morphism `g : Y→Z` such that `f = g∘p₂`
    (`p₂ : X×Y→Y` the projection)." — **p.43 (PDF p.54)**, proof immediately after.
    ← directive: the rigidity lemma. The "(Form I.)" tag signals a later scheme-
    theoretic Form II in the cube-theorem circle (Ch III).
  - **Corollary 1** (a morphism `f : X→Y` of abelian varieties has `f(x)=h(x)+a`,
    `h` a homomorphism, `a∈Y`) — p.43 (PDF p.54).
  - **Corollary 2** (`X` is a commutative group — second proof, via rigidity) — p.44 (PDF p.55).
  - **Corollary 3** (linearity of `Hom(−,X)` on complete pointed varieties:
    `Hom(S,X)×Hom(T,X) ≅ Hom(S×T,X)`, proved "from the rigidity lemma") — p.44 (PDF p.55).
  - Appendix to §4 (a complete variety with a unital morphism `m` is an abelian
    variety; group law + identity exist) — p.44– (PDF p.55–).
- §5 Cohomology and base change — p.46 (PDF p.57)
- **§6 The theorem of the cube: I — p.55 (PDF p.66)**   ← directive: the theorem of the cube
  - **THEOREM (of the cube)** "Let `X,Y` be *complete* varieties, `Z` any variety,
    and `x₀,y₀,z₀` base points. If `L` is a line bundle on `X×Y×Z` whose restrictions
    to each of `{x₀}×Y×Z`, `X×{y₀}×Z`, `X×Y×{z₀}` are trivial, then `L` is trivial."
    — p.55 (PDF p.66); proof structure = the splitting `T(X₀×…×Xₙ)=Im α⊕Ker β`
    ("quadratic functor `Pic`") + seesaw, p.55–64.
- §7 Dividing varieties by finite groups — p.65 · §8 The dual abelian variety: char 0 — p.74 · §9 The case k=ℂ — p.82

**Chapter III — Algebraic Theory via Schemes** (book p.89, PDF p.100)
- **§10 The theorem of the cube: II — p.89 (PDF p.100)**   ← scheme-theoretic cube theorem (char-free)
- §11 Basic theory of group schemes — p.93 · §12 Quotients by finite group schemes — p.108
- §13 The dual abelian variety in any characteristic — p.123 · §14 Duality of finite commutative group schemes — p.132
- §15 Applications to abelian varieties — p.143 · §16 Cohomology of line bundles — p.150 · §17 Very ample line bundles — p.163

**Chapter IV — Hom(X,X̂) and the ℓ-adic representation** (book p.167, PDF p.178)
- §18 Étale coverings p.167 · §19 Structure of Hom(X,X̂) p.172 · §20 Riemann forms p.183
- §21 Positivity of the Rosati involution p.192 · §22 Examples p.210 · §23 The group 𝒢(L) p.221 · §24 The case k=ℂ p.235

**Appendices** Appendix I: The Theorem of Tate (C.P. Ramanujam) — p.240 · Appendix II:
Mordell–Weil Theorem (Yuri Manin) — p.261 · Bibliography — p.276 · Index — p.278.

## Caveats
- **Scanned-image PDF — no text layer.** Verbatim quotes must be read off the rendered
  page image; copy/paste / `pdftotext` will return nothing.
- **"An abelian variety contains no rational curves" / "every morphism ℙ¹→A is
  constant" is NOT a separately-labeled result in §4** of this book. Mumford's §4
  corollaries stop at Corollaries 1–3 (above). The constancy of `ℙ¹→A` is a
  *consequence* of the **Rigidity Lemma (Form I, p.43)** but is left to the reader; the
  explicit "`Mor(ℙ¹,A)` constant / unirational ⇒ constant" statement that the project
  wants to quote verbatim lives in **Milne, Prop 3.10** (`references/abelian-varieties.md`),
  not here. Use Mumford for the rigidity lemma primitive; use Milne for the packaged
  ℙ¹-constancy corollary.
- **Hypothesis comparison with Milne** (load-bearing for the planner):
  - Mumford's Rigidity Lemma (Form I) requires `X` **complete** and (since his
    "variety" = irreducible, p.39 footnote) `X` **irreducible**, over an
    **algebraically closed** field `k`. Only `X` need be complete; `Y,Z` arbitrary.
  - Milne's Rigidity Theorem 1.1 requires `V` **complete** and `V×W`
    **geometrically irreducible** (he allows non-closed base fields, working
    geometrically). Both pin **completeness of the first factor** as the load-bearing
    hypothesis; Mumford additionally bakes in irreducibility + algebraically-closed `k`
    via his global conventions, where Milne states geometric irreducibility explicitly.
- Edition note: this is the 1970 TIFR/Oxford text (later corrected reprints exist with
  Appendices by Ramanujam and Manin, as here). Section numbering 1–24 is continuous
  across chapters.

## Quality / provenance
The definitive primary reference for the theorem of the cube and the rigidity lemma in
arbitrary characteristic; every later treatment (incl. Milne's notes) cites it. File
supplied by the project user; verified as a genuine 290-page scanned PDF of the TIFR
edition by header/trailer inspection and page rendering.
