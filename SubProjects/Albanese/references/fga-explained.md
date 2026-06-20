# Fundamental Algebraic Geometry: Grothendieck's FGA Explained

## Citation
B. Fantechi, L. Göttsche, L. Illusie, S.L. Kleiman, N. Nitsure, A. Vistoli,
"Fundamental Algebraic Geometry: Grothendieck's FGA Explained",
Mathematical Surveys and Monographs 123, American Mathematical Society, 2005.

## Slug
fga-explained

## Retrieval status
RETRIEVED — 2026-05-20 (file placed in `references/` by the project user this iter;
this card only registers + maps it — it was NOT re-downloaded).

## Local source files
- `references/fga-explained.pdf` — PDF, VERIFIED (`%PDF-1.5` header, `%%EOF` trailer,
  352 pages, ~17 MB; verified by byte inspection + pypdf parse since `file` is absent
  on this host). This PDF **has an extractable text layer** (OCR/born-digital), so
  `pypdf` text extraction works (locations below cross-checked against extracted text).

(No LaTeX source — collected AMS volume.)

## Why this source
Route A (positive-genus object) reference engine, as a single collected volume:
**Kleiman's "The Picard scheme"** (Pic⁰ / Jacobian existence + finiteness) and
**Nitsure's "Construction of Hilbert and Quot schemes"** (representability), plus
**Vistoli's descent / representable-functors** foundations and **Illusie's
Grothendieck existence theorem**. The project already holds the standalone arXiv
versions (`references/kleiman-picard.*`, `references/nitsure-hilbert-quot.*`); this
book uses **different section numbering** — record both so the planner can cite either.

## Page offset
Document (book) page **N** ↦ PDF/reader page **N + 10**
(verified: book p.107 = PDF p.117; book p.204 = PDF p.214; book p.237 = PDF p.247;
book p.262 = PDF p.272; book p.275 = PDF p.285). Contents = PDF p.3–5.

## Contents map
Book page numbers are the volume's own; PDF page = book + 10.

**Part 1 — Grothendieck topologies, fibered categories and descent theory**
(Angelo Vistoli) — book p.1   ← directive: descent / representable functors
- Ch.1 Preliminary notions — p.7 (§1.1 Algebraic geometry p.7; §1.2 Category theory p.10)
- **Ch.2 Contravariant functors — p.13** (PDF p.23)
  - **§2.1 Representable functors and the Yoneda Lemma — p.13**   ← representable functors
  - §2.2 Group objects — p.18 · §2.3 Sheaves in Grothendieck topologies — p.25
- Ch.3 Fibered categories — p.41 (§§3.1–3.8)
- **Ch.4 Stacks — p.67** (§4.1 Descent of objects of fibered categories p.67;
  §4.2 Descent for quasi-coherent sheaves p.79; §4.3 Descent for morphisms of schemes
  p.88; §4.4 Descent along torsors p.99)   ← descent theory (fppf/faithfully-flat)

**Part 2 — Construction of Hilbert and Quot schemes** (Nitin Nitsure) — book p.105
   ← directive: Nitsure Hilbert/Quot
- **Ch.5 Construction of Hilbert and Quot schemes — book p.107 (PDF p.117)**
  - Introduction — p.107
  - §5.1 The Hilbert and Quot functors — p.108
  - §5.2 Castelnuovo–Mumford regularity — p.114
  - §5.3 Semi-continuity and base-change — p.118
  - §5.4 Generic flatness and flattening stratification — p.122
  - **§5.5 Construction of Quot schemes — p.126**   ← representability/existence of Quot (hence Hilbert)
  - §5.6 Some variants and applications — p.130
  - **Standalone-arXiv cross-ref**: this is `references/nitsure-hilbert-quot.*`
    (arXiv:math/0504590); arXiv section numbers there are 1–5 (no "Ch.5" prefix).

**Part 3 — Local properties and Hilbert schemes of points** (Fantechi & Göttsche) — book p.139
- Ch.6 Elementary Deformation Theory — p.143 (§§6.1–6.5) · Ch.7 Hilbert Schemes of Points — p.159 (§§7.1–7.6)

**Part 4 — Grothendieck's existence theorem in formal geometry** (Luc Illusie,
with a letter of J.-P. Serre) — book p.179   ← directive: Grothendieck existence/formal
- **Ch.8 Grothendieck's existence theorem in formal geometry — book p.181 (PDF p.191)**
  - §8.1 Locally noetherian formal schemes — p.181 · §8.2 The comparison theorem — p.187
  - §8.3 Cohomological flatness — p.196 · **§8.4 The existence theorem — p.204 (PDF p.214)**
  - §8.5 Applications to lifting problems — p.208 · §8.6 Serre's examples — p.228 · §8.7 A letter of Serre — p.231

**Part 5 — The Picard scheme** (Steven L. Kleiman) — book p.235   ← directive: Kleiman Picard
- **Ch.9 The Picard scheme — book p.237 (PDF p.247)**
  - §9.1 Introduction — p.237 · §9.2 The several Picard functors — p.252
  - §9.3 Relative effective divisors — p.257
  - **§9.4 The Picard scheme — p.262 (PDF p.272)**   ← directive "§4": existence of Picⱼₐ꜀
  - **§9.5 The connected component of the identity — p.275 (PDF p.285)**   ← directive "§5": Pic⁰ (Jacobian)
  - **§9.6 The torsion component of the identity — p.291**   ← Pic^τ finiteness
  - **Standalone-arXiv cross-ref**: this is `references/kleiman-picard.*`
    (arXiv:math/0504020); arXiv section numbers there are 1–9 / "§4 existence, §5 Pic⁰"
    as recorded in `references/kleiman-picard.md`. In the BOOK they are §9.4 / §9.5.

**Appendices** A: Answers to all the exercises — book p.301 · B: Basic intersection
theory — p.313 · Bibliography — p.323 · Index — p.333.

## Caveats
- **Book vs arXiv numbering differs.** Cite the book as Ch.9 §9.4/§9.5 (Kleiman),
  Ch.5 §5.5 (Nitsure); the standalone arXiv preprints already in `references/` number
  the same material §4/§5 (Kleiman) and §§1–5 (Nitsure). The two cards
  (`kleiman-picard.md`, `nitsure-hilbert-quot.md`) carry the arXiv numbering; this card
  carries the book numbering. Statements are the same content.
- The volume's stated prerequisite is Hartshorne [Har77]
  (`references/hartshorne-algebraic-geometry.pdf`), and finiteness of the Hilbert /
  Picard schemes is proved via Castelnuovo–Mumford regularity (Preface, PDF p.8), not
  Chow coordinates.
- Text layer present but lightly OCR-mangled in places (e.g. ligatures, "Pic⁰"→"Pic0");
  prefer the rendered PDF for verbatim quotes of displayed formulas.

## Quality / provenance
The standard modern exposition with full proofs of Grothendieck's FGA themes (descent,
Hilbert/Quot, formal existence, Picard scheme); authoritative for Route A. File
supplied by the project user; verified as a genuine 352-page AMS-volume PDF by
header/trailer inspection and text/Contents extraction.
