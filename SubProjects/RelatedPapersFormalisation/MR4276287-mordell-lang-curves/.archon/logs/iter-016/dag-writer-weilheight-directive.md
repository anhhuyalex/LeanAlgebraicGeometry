# Blueprint Writer Directive

## Slug
weil-height

## Target chapter
blueprint/src/chapters/WeilHeight.tex

## Strategy context
This chapter sets up the height theory needed by the rest of the project: the Weil height
on projective varieties (available from Mathlib), the naive height on the total space,
the Néron-Tate (canonical) height on abelian varieties, and its key properties
(quadraticity, non-negativity). These are needed by thm:silverman_tate, lem:vojtamumford,
and all the counting theorems.

Mathlib has some height infrastructure in Mathlib.NumberTheory.Heights. The project needs
to extend this to the abelian-variety setting.

This is a new chapter; create the file from scratch with:
  \chapter{Height theory for abelian varieties}
  \label{chap:weilheight}
  % archon:covers MR4276287UniformityInMordellLangForCurves/WeilHeight.lean

## Required content

1. **thm:weil_height_mathlib** (`Mathlib.NumberTheory.Heights.weilHeight`) — Weil height
   h: P^n(K̄) → ℝ_{≥0} for a number field K̄. It satisfies: finite above any bound
   (Northcott), functorial under morphisms of projective varieties (height machine),
   and equals the logarithmic Mahler measure modulo boundedness. Mark this \mathlibok
   since Weil heights ARE in Mathlib (Mathlib.NumberTheory.Heights). Choose an existing
   Mathlib name or note [verify Mathlib name].

2. **def:height_fib** (`def:fiberwiseHeight`) — The naive height of a point P ∈ A(K̄)
   in the universal abelian family: h(P) := the Weil height of ι(P) in projective space
   via the chosen projective embedding ι: Ā → P^n of the compactified family. Depends
   on the ambient setup choices. Source: silvermantate.tex Appendix A.

3. **def:nt_height** (`def:neronTateHeight`) — The Néron-Tate (canonical) height:
   \hat{h}_A(P) := lim_{N→∞} h([2^N]P)/4^N. This is the quadratic form associated
   to the projective height via the duplication bound from thm:silverman_tate.
   Source: silvermantate.tex.

4. **prop:nt_quadratic** (`prop:ntQuadratic`) — NT height is a quadratic form:
   \hat{h}([N]P) = N^2 \hat{h}(P) for all N ∈ ℤ. Source: silvermantate.tex.

5. **prop:nt_nonneg** (`prop:ntNonneg`) — NT height satisfies: (a) \hat{h}(P) ≥ 0,
   (b) \hat{h}(P) = 0 if and only if P is a torsion point. Source: silvermantate.tex.

6. **lem:northcott_ht** (`lem:northcottHeight`) — For any bound B > 0 and degree bound
   D, there are only finitely many points P in a projective variety over K̄ of degree
   [K(P):K] ≤ D and h(P) ≤ B. This is the Northcott property of Weil heights.
   If this is available from Mathlib as a specific declaration, mark \mathlibok with the
   correct name; otherwise write as a project stub.

\uses skeleton:
- def:height_fib uses thm:weil_height_mathlib, def:ambient_setup
- def:nt_height uses def:height_fib, def:ambient_setup
- prop:nt_quadratic uses def:nt_height
- prop:nt_nonneg uses def:nt_height
- thm:silverman_tate (in Basic.tex) uses def:nt_height, def:height_fib (to be wired up)
- lem:northcott_ht uses thm:weil_height_mathlib

## Out of scope
- Do NOT add IsNef/IsBig positivity (those go in Positivity.tex).
- Do NOT add Siu criterion (that goes in ArithBezout.tex).
- Do NOT edit any other chapter.
- Do NOT add \leanok markers.

## References
- references/MR4276287-mordell-lang-curves-source/silvermantate.tex: Appendix A — Silverman-Tate comparison, NT height definition
- references/MR4276287-mordell-lang-curves-source/NTbase.tex: Section 5 — quadraticity of NT height

## Expected outcome
New chapter with 6 declaration blocks. thm:weil_height_mathlib marked \mathlibok (if
Mathlib has it) or as a project stub. All proof blocks grounded in verbatim source quotes
from silvermantate.tex and NTbase.tex. Lean targets named consistently with the rest of
the project namespace.
