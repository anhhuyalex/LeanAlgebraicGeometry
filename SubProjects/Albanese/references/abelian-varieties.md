# Abelian Varieties (Milne)

## Citation
J.S. Milne, "Abelian Varieties" (course notes), version 2.00, 2008.
Open-access at https://www.jmilne.org/math/CourseNotes/av.html.

## Slug
abelian-varieties

## Retrieval status
RETRIEVED — 2026-05-20

## Local source files
- `references/abelian-varieties.pdf` — PDF, VERIFIED (`%PDF-` header, `%%EOF` trailer, 172 pages, 1.26 MB; verified by byte inspection + pypdf parse since `file`/`pdftotext`/`pdftoppm` are not installed on this host) — retrieved from https://www.jmilne.org/math/CourseNotes/AV.pdf

(No openly-available LaTeX source: Milne distributes these notes as PDF only.)

## Why this source
Backs two project decisions: (1) whether "every morphism `ℙ¹ → A` to an abelian
variety is constant" (no rational curves on an abelian variety) can be proved from the
bare **Rigidity Lemma** / theorem-of-the-cube circle WITHOUT Serre duality
(`H⁰(Ω)=0`) or the Albanese/Picard construction — relevant to `rigidity_over_kbar`
and `genusZeroWitness`; (2) the **Albanese universal property of `Pic⁰`/Jacobian**
(Abel–Jacobi functoriality) backing the project's Route A positive-genus arm.

## Contents map
Page numbers are the notes' own (document) page numbers. The PDF is offset by +6
(document page N ↦ PDF/reader page N+6; Introduction p.1 = PDF page 7).

**Chapter I — Abelian Varieties: Geometry** (p.7)
- §1 Definitions; Basic Properties — p.7
  - **Theorem 1.1 (RIGIDITY THEOREM)** — p.8 (PDF p.14), proof p.8–9.   ← directive item (1), the rigidity lemma
  - Corollary 1.2 (regular map of AVs = homomorphism ∘ translation) — immediately after Thm 1.1, p.9.
- §2 Abelian Varieties over the Complex Numbers — p.10
- **§3 Rational Maps Into Abelian Varieties** — p.15   ← directive item (1), the ℙ¹/no-rational-curves corollary
  - Theorem 3.1 / **Theorem 3.2** (a rational map from a *nonsingular* variety to an AV is defined on the whole variety) — p.15–16 (PDF p.21–23); Lemma 3.3 (indeterminacy locus is pure codim 1).
  - Lemma 3.5 (smooth curve ↪ complete smooth curve; normalization), Lemma 3.6, and the dimension-1 case showing the extended map `C̄ × W → A` is constant **via the Rigidity Theorem 1.1** — p.18–19 (PDF p.24–25).
  - Corollary 3.7 (rational map group-variety → AV = homomorphism + translation) — p.19 (PDF p.25).
  - **Proposition 3.10** (every rational map from a **unirational** variety — in particular ℙⁿ, ℙ¹ — to an abelian variety is **constant**); proof reduces to `ℙ¹ × ⋯ × ℙ¹ → A` and inducts from the curve case + Rigidity — p.20 (PDF p.26).   ← the verbatim "Mor(ℙ¹,A) constant" statement
- §4 Review of cohomology — p.20
- **§5 The Theorem of the Cube** — p.21   ← the cube-theorem machinery underpinning rigidity
- §6 Abelian Varieties are Projective — p.27
- §7 Isogenies — p.32 … §18 Abel and Jacobi — p.71

**Chapter II — Abelian Varieties: Arithmetic** (p.75): §1 Zeta function p.75; §2 over finite fields p.78; §3 complex multiplication p.83.

**Chapter III — Jacobian Varieties** (p.85)
- §1 Overview and definitions — p.85
- §2 The canonical maps from C to its Jacobian variety — p.91
- §3 The symmetric powers of a curve — p.94
- §4 The construction of the Jacobian variety — p.98
- §5 The canonical maps from the symmetric powers of C to its Jacobian — p.101
- **§6 The Jacobian variety as Albanese variety; autoduality** — p.104   ← directive item (2), Albanese universal property
  - **Proposition 6.1** (`f_P : C → J` universal property: any `φ : C → A` to an AV with `φ(P)=0` factors uniquely as `ψ ∘ f_P`, `ψ : J → A` a homomorphism) — p.104 (PDF p.110).
  - **Proposition 6.4** (universal property for `F : C×C → A`) + **Remark 6.5** (this says `(J,F)` is the Albanese variety of `C` in the sense of Lang 1959) — p.105 (PDF p.111).
  - Theorem 6.6 (autoduality `J ≅ J^∨`) — p.105 (PDF p.111).
- §7 Weil's construction — p.108 … §9 Coverings from the Jacobian — p.113.

**Chapter IV — Finiteness Theorems** (p.129). Bibliography p.161, Index p.165.

## Caveats
- Open-access lecture notes (definitive author's copy on Milne's site), PDF-only — no
  LaTeX source published, so exact statements must be quoted from the PDF.
- Default standing hypothesis in §III.6: `C` is a complete nonsingular curve of
  **genus g > 0** with a k-rational point `P`. The Albanese universal property
  (Prop 6.1/6.4) is stated under those hypotheses.
- Conventions (§"Conventions concerning algebraic geometry", p.v): "variety" =
  geometrically reduced separated scheme of finite type, nonclosed points omitted.
  The Rigidity Theorem 1.1 requires `V` **complete** and `V × W` geometrically
  irreducible.
- Mojibake note: pypdf text extraction mangles some glyphs (e.g. `×` → `/STX`,
  `Pic⁰` → `Pic0`); the rendered PDF is clean. Read the PDF for verbatim quotes.

## Quality / provenance
Authoritative open-access source for the rigidity lemma and the Albanese property at
the level the project needs. Milne himself flags Mumford's "Abelian Varieties" (1970)
as the canonical reference (Intro NOTES, p.5); these notes reproduce the same results
with full proofs and are freely citable. Downloaded directly from the author's site.
