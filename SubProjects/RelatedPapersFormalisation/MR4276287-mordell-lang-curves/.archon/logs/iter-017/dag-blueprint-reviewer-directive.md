# Blueprint Reviewer Directive

## Slug
iter017-full

## Strategy snapshot

### Goal

Formalize the paper route to the uniform Mordell--Lang bounds for curves:

- `ThmBdRatIntro`: a bound of the form `#C(F) ≤ c(g,d)^(1+ρ)` for smooth curves of genus `g ≥ 2` over number fields of degree `≤ d`.
- `ThmBdFinRank`: a finite-rank Mordell--Lang bound for a curve in its Jacobian, with the height threshold on the Jacobian as input.
- `thm:BdTorIntroNF`: the corresponding uniform bound for torsion packets.
- The intermediate height and geometry inputs: Betti map / Betti form, non-degenerate height inequality, Néron--Tate distance proposition, and the Vojta/Mumford counting step.

### Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---:|---:|---|---|
| Setup: moduli space M_g with level structure | ACTIVE | 5-8 | ~400-600 | `AlgebraicGeometry.IsProper`, fiber products | M_g with level structure and universal curve are project-specific |
| Setup: Jacobian variety of genus-g curve | ACTIVE | 8-14 | ~800-1400 | `AlgebraicGeometry.IsProper`, abelian varieties | CONFIRMED MISSING from Mathlib; largest single risk |
| Setup: Torelli map and universal Jacobian family | ACTIVE | 4-6 | ~360-540 | depends on Jacobian phase above, fiber products | must follow Jacobian phase |
| Betti map: analytification and local trivializations | ACTIVE | 3-5 | ~280-420 | basic complex geometry, real-analytic maps | analytification API thin in Mathlib |
| Betti map: Betti map and Betti form existence | ACTIVE | 3-5 | ~260-400 | depends on above | period-lattice data project-specific |
| Betti map: general-base variant and étale reduction | ACTIVE | 2-4 | ~180-280 | étale morphisms, finite étale covers | descent argument delicate |
| Betti map: Betti-rank Zariski-openness | ACTIVE | 1-2 | ~80-140 | real-analytic open-set arguments | likely quick once Betti map done |
| Canonical-height: Weil heights on abelian varieties | ACTIVE | 2-4 | ~180-280 | `Height.logHeight` (VERIFIED) | fiber-by-fiber height accounting |
| Canonical-height: Néron--Tate limit and properties | ACTIVE | 3-5 | ~280-420 | builds on Weil heights | quadratic-limit construction project-specific |
| Canonical-height: IsNef / IsBig positivity wrappers | ACTIVE | 3-5 | ~280-420 | MISSING in Mathlib | must be built from scratch |
| Canonical-height: arithmetic Bézout and Siu positivity | ACTIVE | 4-7 | ~400-620 | depends on IsNef/IsBig | intersection-theoretic Siu criterion project-specific |
| Height inequality | ACTIVE | 4-6 | ~380-560 | depends on canonical-height phases | graph/intersection argument delicate |
| Néron--Tate distance on curves | ACTIVE | 3-4 | ~240-360 | Faltings--Zhang morphism, combinatorial lemmas | induction and packet bounds careful |
| Rational-point counting | ACTIVE | 2-3 | ~180-260 | Vojta/Mumford bounds, rank bookkeeping | can run parallel with torsion lane |
| Torsion-packet counting | ACTIVE | 2-3 | ~180-260 | shared height/distance lemmas | can run parallel with rational-point lane |

## Routes

Route 1 (appendix-first height route): Build analytic geometry (Betti map/form) and canonical-height/positivity first, then the height inequality (Appendix B), then curve-specific setup (universal Jacobian, Faltings–Zhang, counting lemmas), then main theorems.

Route 2 (sorry-first / analytic-black-box, secondary): State `prop:betti_map`, `prop:betti_form`, `prop:betti_map_app`, and analytification assumptions as axiom stubs. Formalize the algebraic height-inequality and counting argument first; return to analytic layer later.

## References

- `references/MR4276287-mordell-lang-curves.pdf`: Full paper PDF (arXiv:2001.10276).
- `references/MR4276287-mordell-lang-curves.tex`: Full paper TeX source.
- `references/MR4276287-mordell-lang-curves-source/`: Extracted arXiv source directory (individual section files).

## Focus areas

- Check all 9 chapters for completeness of informal proof sketches.
- Flag any declarations whose `\uses{}` references do not match the mathematical dependencies.
- The Torelli.tex chapter was edited this iter (replaced \xymatrix commutative diagram with array representation) — verify the fix is correct.
- Check if all strategy phases have adequate blueprint coverage (key concern for iter-017).
- Note: the Betti map phases (analytification, Betti map existence, general-base variant, Betti-rank Zariski-openness) are currently covered by `MR4276287UniformityInMordellLangForCurves_Basic.tex` — check if coverage is adequate.

## Known issues

- The 6 chapters (ArithBezout, Jacobian, ModuliSpace, Positivity, Torelli, WeilHeight) have `archon:covers` pointing to Lean files that do not yet exist (`MR4276287UniformityInMordellLangForCurves/ArithBezout.lean` etc.). This is expected in the blueprint-first workflow; the Lean skeleton files will be created by lean-scaffolder in the prover phase.
- `thm:weil_height_mathlib` is marked `\mathlibok` pointing to `Mathlib.NumberTheory.Heights.weilHeight` — verify this name is correct.
