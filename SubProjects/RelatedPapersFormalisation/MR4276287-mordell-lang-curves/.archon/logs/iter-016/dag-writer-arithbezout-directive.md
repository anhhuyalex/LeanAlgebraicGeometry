# Blueprint Writer Directive

## Slug
arith-bezout

## Target chapter
blueprint/src/chapters/ArithBezout.tex

## Strategy context
This chapter provides the intersection-theoretic input to prop:aux_ht_ineq: the arithmetic
Bézout theorem, the bihomogeneous degree bound for [N], and the two intersection-number
estimates (lower bound from Betti-form positivity and upper bound from degree control).
These lemmas are cited in HtIneq.tex but never declared as standalone blueprint entries.

The arithmetic Bézout theorem is cited as "[Théorème 3]{HauteursAlt3}" (Autissier),
not in Mathlib. The other lemmas follow from explicit computation.

This is a new chapter; create the file from scratch with:
  \chapter{Arithmetic Bézout and intersection estimates}
  \label{chap:arithbezout}
  % archon:covers MR4276287UniformityInMordellLangForCurves/ArithBezout.lean

## Required content

1. **thm:arith_bezout** (`thm:arithBezout`) — Arithmetic Bézout theorem (Autissier,
   [Théorème 3]{HauteursAlt3}): for cycles Z₁, Z₂ on P^n_ℤ of complementary codimension,
   their arithmetic intersection ĥ(Z₁·Z₂) satisfies
   ĥ(Z₁·Z₂) ≤ deg(Z₁)·ĥ(Z₂) + deg(Z₂)·ĥ(Z₁) + c·deg(Z₁)·deg(Z₂).
   This is cited as a black box from Autissier; stated as a sorry stub.
   Source: SettingUp.tex (Bézout reference), HtIneq.tex.

2. **lem:bihomog_degree** (`lem:bihomogDegree`) — The graph of multiplication-by-N,
   closed in P^n × P^n × P^m, is defined by bihomogeneous equations of degree
   polynomial in N (specifically degree ≤ c·N^2 in each block). The key computation:
   [2^l] is expressed by polynomials of degree 4^l in each coordinate block, so the
   degree of the graph of [N] in each block is O(N^2). Source: HtIneq.tex §4.

3. **lem:siu_intersection_lower** (`lem:siuIntersectionLower`) — Lower bound on (F^d):
   using the Betti-form positivity (prop:betti_form) and the fact that F_s^d = (ι_s^*F)^d
   is controlled by the Betti form on X, we get (F_s^d) ≥ κ·N^{2d} for some κ > 0
   independent of N. Source: HtIneq.tex §4.

4. **lem:siu_intersection_upper** (`lem:siuIntersectionUpper`) — Upper bound on
   (M^{N^2}·F^{d-1}): by multilinearity of intersection numbers and the bihomogeneous
   degree bound, (M^{N^2}·F^{d-1}) = N^2·(M·F^{d-1}) ≤ c·N^2 for a constant c
   depending only on d and the ambient setup. Source: HtIneq.tex §4.

\uses skeleton:
- thm:arith_bezout uses def:ambient_setup
- lem:bihomog_degree uses lem:graph_construction (from Basic.tex)
- lem:siu_intersection_lower uses prop:betti_form, lem:graph_construction, def:nef (from Positivity.tex)
- lem:siu_intersection_upper uses lem:bihomog_degree, lem:graph_construction, def:nef (from Positivity.tex)
- prop:aux_ht_ineq (in Basic.tex) should \uses{lem:siu_intersection_lower, lem:siu_intersection_upper, thm:siu_criterion, thm:arith_bezout} (to be wired up)

## Out of scope
- Do NOT redefine IsNef/IsBig (those are in Positivity.tex).
- Do NOT edit any other chapter.
- Do NOT add \leanok markers.

## References
- references/MR4276287-mordell-lang-curves-source/HtIneq.tex: Section 4, full proof including intersection estimate computation
- references/MR4276287-mordell-lang-curves-source/SettingUp.tex: Arithmetic Bézout citation

## Expected outcome
New chapter with 4 declaration blocks. thm:arith_bezout stated as a sorry stub (citing
Autissier verbatim from HtIneq.tex). lem:bihomog_degree has an explicit computation-based
proof sketch. lem:siu_intersection_lower and lem:siu_intersection_upper have concise
proof sketches derived from HtIneq.tex. All source quotes verbatim from locally-read files.
