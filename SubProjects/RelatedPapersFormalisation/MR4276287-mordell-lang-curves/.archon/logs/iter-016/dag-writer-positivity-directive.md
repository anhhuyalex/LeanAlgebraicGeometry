# Blueprint Writer Directive

## Slug
positivity

## Target chapter
blueprint/src/chapters/Positivity.tex

## Strategy context
This chapter sets up the IsNef and IsBig notions for line bundles and the Siu bigness
criterion. These are needed in the proof of prop:aux_ht_ineq (auxiliary height inequality).
IsNef and IsBig are CONFIRMED MISSING from Mathlib and must be project-specific definitions.

The chapter should treat these as self-contained algebraic geometry concepts, stated
precisely so that a prover can define them in Lean and verify that the graph construction
produces nef line bundles. The Siu criterion (Theorem 2.2.15 from Lazarsfeld's "Positivity
in Algebraic Geometry I") is the main external input.

This is a new chapter; create the file from scratch with:
  \chapter{Positivity of line bundles}
  \label{chap:positivity}
  % archon:covers MR4276287UniformityInMordellLangForCurves/Positivity.lean

## Required content

1. **def:nef** (`def:isNef`) — A line bundle L on a projective variety X over a field k
   is nef (numerically effective) if deg(L|_C) ≥ 0 for every irreducible curve C ⊂ X.
   Equivalently, for every ε > 0 and every ample H, L + εH is ample. Source: HtIneq.tex
   (where nef is used without definition) / Lazarsfeld §1.4.

2. **def:big** (`def:isBig`) — A line bundle L on an n-dimensional projective variety X
   is big if h⁰(X, L^⊗m) ~ c·m^n for some c > 0 as m → ∞. Equivalently (Kodaira),
   L is big iff it is the sum of an ample and an effective line bundle. Source: HtIneq.tex
   / Lazarsfeld §2.2.

3. **lem:nef_intersection** (`lem:nefIntersection`) — If L₁, ..., L_d are nef line bundles
   on an n-dimensional X and d ≤ n, their intersection number (L₁ · L₂ · ... · L_d · H^{n-d})
   is well-defined and non-negative for any ample H. Source: Lazarsfeld §1.6.

4. **thm:siu_criterion** (`thm:siuCriterion`) — (Siu's theorem on bigness, Lazarsfeld
   Theorem 2.2.15). Let L and M be nef line bundles on an n-dimensional projective X.
   If (L^n) > n·(M·L^{n-1}), then L^q ⊗ M^{-1} is big for some positive integer q.
   In particular, there is an effective divisor in the linear system of L^q ⊗ M^{-1}.
   Source: HtIneq.tex citing [Theorem 2.2.15]{PosAlgGeom} (Lazarsfeld).

5. **lem:nef_from_betti** (`lem:nefFromBetti`) — The line bundles F and M on the
   projective closure X̄_N (from lem:graph_construction) are nef. This is the key
   geometric input: F = O(0,1,1)|_{X̄_N} restricts to a nef bundle because it is a
   pullback of the tautological bundle on projective space, and similarly for M.
   Source: HtIneq.tex §4.

\uses skeleton:
- lem:nef_intersection uses def:nef
- thm:siu_criterion uses def:nef, def:big, lem:nef_intersection
- lem:nef_from_betti uses def:nef, lem:graph_construction (from Basic.tex)
- prop:aux_ht_ineq (in Basic.tex) uses thm:siu_criterion, lem:nef_from_betti (to be wired up)

## Out of scope
- Do NOT add arithmetic Bézout or intersection number estimates (those go in ArithBezout.tex).
- Do NOT edit any other chapter.
- Do NOT add \leanok markers.
- If Lazarsfeld's "Positivity in Algebraic Geometry I" is not in references/, you may
  cite the statement as it appears in HtIneq.tex (which cites it verbatim); use that
  local file for the source quote.

## References
- references/MR4276287-mordell-lang-curves-source/HtIneq.tex: Section 4, Siu criterion reference and usage, nef/big definitions as used in paper

## Expected outcome
New chapter with 5 declaration blocks. def:nef and def:big are pure definitions (no proof).
thm:siu_criterion is stated precisely with the intersection-number hypothesis. All source
quotes from locally-read HtIneq.tex (which cites Lazarsfeld). lem:nef_from_betti bridges
the abstract positivity notion to the specific graph construction.
