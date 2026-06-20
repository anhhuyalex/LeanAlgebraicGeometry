# Stacks Project — Algebra, §"Noetherian graded rings": Hilbert–Serre rationality

## Citation
The Stacks Project (many authors), "Stacks Project", Columbia University, ongoing.
https://stacks.math.columbia.edu — chapter "Algebra", section "Noetherian graded rings" (tag 00JV).

## Slug
hilbert-serre

## Retrieval status
RETRIEVED — 2026-06-05

## Local source files
- `references/hilbert-serre-algebra.tex` — LaTeX source of the full Stacks Project Algebra chapter,
  VERIFIED (starts with `\input{preamble}`, size 1.7 MB) — retrieved from
  https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex

  (No standalone PDF for this chapter. The TeX source is authoritative and machine-readable.)

## Why this source
This is the verbatim quote source for blueprint block `lem:gradedHilbertSerre_rational` in
`Picard_QuotScheme.tex`. The Stacks Project formulates the Hilbert–Serre rationality as
Proposition 00K1 (`algebra-proposition-graded-hilbert-polynomial`), stating that the
Hilbert function $n \mapsto [M_n] \in K'_0(S_0)$ of a finitely generated graded module
over a Noetherian graded ring generated in degree 1 is a numerical polynomial — exactly
the rationality statement needed for the Hilbert polynomial of a coherent sheaf.

## Contents map — exact tag locations in `algebra.tex`

Section: **"Noetherian graded rings"** — `\label{section-noetherian-graded}` — line 13778.

| Stacks tag | Label in algebra.tex | Line(s) | Content |
|---|---|---|---|
| **00JV** | `section-noetherian-graded` | 13778–13779 | Section start: "Noetherian graded rings" |
| **00JW** | `lemma-graded-Noetherian` | 13806–13822 | S graded Noetherian ↔ S₀ Noetherian and S₊ f.g. as ideal |
| **00JX** | `definition-numerical-polynomial` | 13824–13835 | Definition: numerical polynomial (binomial-coefficient form) |
| **00JY** | `lemma-numerical-polynomial-functorial` | 13845–13854 | Functoriality of numerical polynomials |
| **00JZ** | `lemma-numerical-polynomial` | 13856–13874 | **Key induction lemma**: if n↦f(n)−f(n−1) is numerical polynomial, so is f |
| **00K0** | `lemma-graded-module-fg` | 13876–13891 | If M f.g. graded S-module, S f.g. over S₀, then each Mₙ is finite S₀-module |
| **00K1** | `proposition-graded-hilbert-polynomial` | 13893–13948 | **THE HILBERT–SERRE THEOREM**: n↦[Mₙ]∈K'₀(S₀) is numerical polynomial when S₊ generated in degree 1. Proof by induction on #generators of S₁, with inner induction using the SES 0→Mₐ→Mₐ₊₁→M̄ₐ₊₁→0 (multiplication by x∈S₁). |
| **02CD** | `remark-period-polynomial` | 13950–13956 | Remark: without degree-1 generation, get periodic polynomial instead |
| **00K2** | `example-hilbert-function` | 13958–13966 | Example: S=k[X₁,…,Xd], Mₙ↦dim_k(Mₙ) is numerical polynomial |
| **00K3** | `lemma-quotient-smaller-d` | 13968–13986 | Degree bound: for 0≠I⊂k[X₁,…,Xd] graded, deg(Hilbert poly of k[X₁,…,Xd]/I)<d−1 |

### Proof structure of 00K1 (lines 13907–13948)
The proof is by double induction:
1. **Outer induction** on the minimal number of generators of S₁.
   - Base case (0 generators): Mₙ=0 for n≫0. Done.
   - Induction step: pick x∈S₁; apply hypothesis to the graded ring S/(x).
2. **Inner case 1** (x nilpotent on M): induction on min r with xʳM=0; uses SES to reduce.
3. **Inner case 2** (x not nilpotent): pass to M/M' where M'={m: xⁿm=0 for some n}, so multiplication by x on M/M' is injective. Then the key SES (line 13943–13944):
   $$0 \to M_d \xrightarrow{x} M_{d+1} \to \overline{M}_{d+1} \to 0$$
   gives [M_{d+1}] − [M_d] = [M̄_{d+1}], and 00JZ closes the induction.

### Note on formulation
The Stacks Project does NOT use the language "Poincaré series" or "rational function" for
the generating series ∑[Mₙ]tⁿ. Instead it states that the function n↦[Mₙ] is eventually
a **numerical polynomial**. This is equivalent: if the graded pieces have lengths in ℤ,
the rationality of ∑ℓ(Mₙ)tⁿ as (1−t)⁻ᵈ·f(t) with f∈ℤ[t] follows from — and is
equivalent to — the Hilbert function being eventually polynomial of degree d−1.
When S₀=k (a field), K'₀(k)=ℤ and Example 00K2 gives exactly the classical setting.

## Caveats
- The seed tags 00JW and 00P4 in the directive correspond to `lemma-graded-Noetherian` and
  `lemma-dimension-at-a-point-preserved-field-extension` respectively; 00P4 is NOT in the
  Hilbert-function section — it is a separate dimension lemma. The actual rationality content
  lives at 00K1 (not near 00P4).
- The algebra.tex file is the full Algebra chapter (~1.7 MB). The Hilbert-function material
  spans lines 13778–13986.
- No separate PDF was downloaded. Use `Read` on `hilbert-serre-algebra.tex` with
  `offset: 13778, limit: 210` to ingest the full section in one call.

## Quality / provenance
The Stacks Project is the definitive community reference for commutative algebra in the
context of algebraic geometry. The TeX was fetched directly from the master branch of
https://github.com/stacks/stacks-project and is the canonical source.
