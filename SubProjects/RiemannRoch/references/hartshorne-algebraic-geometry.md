# Algebraic Geometry (Hartshorne)

## Citation
Robin Hartshorne, "Algebraic Geometry", Graduate Texts in Mathematics 52,
Springer-Verlag, 1977.

## Slug
hartshorne-algebraic-geometry

## Retrieval status
RETRIEVED — 2026-05-20 (file placed in `references/` by the project user this iter;
this card only registers + maps it — it was NOT re-downloaded).

## Local source files
- `references/hartshorne-algebraic-geometry.pdf` — PDF, VERIFIED (`%PDF-1.3` header,
  `%%EOF` trailer, 514 pages, ~41 MB; verified by byte inspection + pypdf parse since
  `file`/`pdftotext`/`pdftoppm` are absent on this host). **Scanned-image** PDF: no
  text layer; locations below read by rendering page images and inspecting visually.

(No LaTeX source.)

## Why this source
Backs the genus-0 arm: (1) a complete nonsingular curve of genus 0 over an
algebraically closed field (with a rational point — automatic over `k=k̄`) is
isomorphic to ℙ¹; (2) `Ω_{ℙ¹}≅O(−2)` and `H⁰(ℙ¹,Ω)=0`, feeding the off-path
differential/`df=0` fallback (route (a)); (3) the genus definition and the
`genus 0 ⟺ H¹(O_X)=0` connection.

## Page offset
Two regimes:
- **Arabic body**: document page **N** ↦ PDF page **N + 17**
  (verified: doc p.172 = PDF p.189; doc p.225 = PDF p.242; doc p.294 = PDF p.311).
- **Roman front matter**: e.g. Contents "ix" = PDF p.10 (offset ≈ +1).

## Contents map
Document (printed) page numbers are Hartshorne's own; PDF page = doc + 17 (body).

- Contents — PDF p.10–11 (doc p.ix–xi). Introduction — doc p.xiii.

**Chapter I — Varieties** (doc p.1)
- §6 Nonsingular Curves — doc p.39 (PDF p.56). (Contains I.6.12: a curve is rational ⟺ ≅ ℙ¹.)

**Chapter II — Schemes** (doc p.60)
- §6 Divisors — doc p.129 · §7 Projective Morphisms — doc p.149
- **§8 Differentials — doc p.172 (PDF p.189)**   ← directive: ℙ¹ differentials
  - **Theorem II.8.13 (Euler / cotangent exact sequence)** for `X=ℙⁿ_A`:
    `0 → Ω_{X/A} → O_X(−1)^{n+1} → O_X → 0` — doc p.176 (PDF p.193).  For `n=1` this
    gives `Ω_{ℙ¹}≅O(−2)` by degree count.   ← `Ω_{ℙ¹}≅O(−2)`
  - **Example II.8.20.1 (canonical sheaf of ℙⁿ)** computes `ω_{ℙⁿ}≅O(−n−1)` (highest
    exterior power of 8.13) and notes `p_g(ℙⁿ)=0`; for `n=1`, `ω_{ℙ¹}=Ω_{ℙ¹}≅O(−2)`
    — doc p.182 (PDF p.199).   ← `Ω_{ℙ¹}≅O(−2)` (explicit), `H⁰` vanishing context

**Chapter III — Cohomology** (doc p.201)
- §4 Čech Cohomology — doc p.218
- **§5 The Cohomology of Projective Space — doc p.225 (PDF p.242)**   ← directive: `H⁰(ℙ¹,O(−2))=0`
  - **Theorem III.5.1** computes `H^*(ℙʳ_A, O(n))`: part (a) `⊕_n H⁰(X,O_X(n)) ≅
    S = A[x₀,…,xᵣ]` (graded), so `H⁰(ℙ¹,O(d))=0` for `d<0`, in particular
    `H⁰(ℙ¹,Ω)=H⁰(ℙ¹,O(−2))=0`; (b) `H^i=0` for `0<i<r`; (d) `H^r(O(−r−1))≅A`; plus
    Serre duality pairing — doc p.225 (PDF p.242).   ← `H⁰(ℙ¹,Ω)=0`
- §7 The Serre Duality Theorem — doc p.239

**Chapter IV — Curves** (doc p.293, PDF p.310)
- **§1 Riemann–Roch Theorem — doc p.294 (PDF p.311)**   ← directive: genus def + genus-0 classification
  - **Proposition IV.1.1**: `p_a(X)=p_g(X)=dim_k H¹(X,O_X)` for a (complete nonsingular)
    curve `X`; "we call this number the genus `g`" — doc p.294 (PDF p.311). With
    **Remark IV.1.1.1** (`g≥0`). This is the **genus definition + `g=dim H¹(O_X)`** link,
    i.e. `genus 0 ⟺ H¹(O_X)=0`.   ← genus def / `g=dim H¹(O)`
  - **Example IV.1.3.5**: "`X` is rational ⟺ `g=0`"; since `X` rational ⟺ `X≅ℙ¹`
    (I.6.12), a complete nonsingular curve of genus 0 (over `k=k̄`) is `≅ℙ¹`. (Proof:
    `p_a(ℙ¹)=0`; conversely take a point `Q`, Riemann–Roch on `D=P−Q` gives `l(D)≥1`,
    so `D∼` an effective degree-0 divisor `⟹ P∼Q ⟹ X≅ℙ¹` via II.6.10.1.)
    — **doc p.297 (PDF p.314)**.   ← genus-0 curve ≅ ℙ¹
  - **Exercise IV.1.3**: an integral, separated, regular, 1-dimensional finite-type
    scheme of genus 0 over `k=k̄` with a `k`-rational point `≅ ℙ¹` — doc p.297 (PDF p.314).
    (Spells out the explicit "rational point" hypothesis; over `k=k̄` it is automatic.)
  - §2 Hurwitz p.299 · §3 Embeddings in ℙⁿ p.307 · §4 Elliptic Curves p.316 · §5 Canonical Embedding p.340 · §6 Classification of Curves in ℙ³ p.349

**Chapter V — Surfaces** doc p.356. **Appendices A** (Intersection Theory) p.424,
**B** (Transcendental Methods) p.438, **C** (Weil Conjectures) p.449. Bibliography
p.459, Results from Algebra p.470, Glossary p.472, Index p.478.

## Caveats
- **Scanned-image PDF — no text layer.** Verbatim quotes must be read off the rendered
  page image; `pdftotext`/copy-paste returns nothing.
- The genus-0 classification (Example IV.1.3.5) is stated over an **algebraically
  closed** base field `k` (Hartshorne's standing convention for "curve" in Ch. IV:
  complete nonsingular over `k=k̄`, I.6.7). Over `k=k̄` every closed point is rational,
  so the "rational point" hypothesis the directive names is automatic; Exercise IV.1.3
  is where the explicit rational-point form is spelled out.
- `Ω_{ℙ¹}≅O(−2)`: Hartshorne states the general `ω_{ℙⁿ}≅O(−n−1)` (Example II.8.20.1)
  and the Euler sequence (Theorem II.8.13); the `n=1` case `Ω_{ℙ¹}≅O(−2)` is the
  immediate specialisation, not a separately numbered statement.

## Quality / provenance
The standard graduate AG textbook; definitive for the genus-0/ℙ¹ classification and
projective-space cohomology at the level the project needs. File supplied by the
project user; verified as a genuine 514-page scanned PDF of GTM 52 by header/trailer
inspection and page rendering of the Contents + each cited location.
