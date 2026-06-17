# Strategy

## Goal

Formalize the paper route to the uniform Mordell--Lang bounds for curves:

- `ThmBdRatIntro`: a bound of the form `#C(F) ≤ c(g,d)^(1+ρ)` for smooth curves of genus `g ≥ 2` over number fields of degree `≤ d`.
- `ThmBdFinRank`: a finite-rank Mordell--Lang bound for a curve in its Jacobian, with the height threshold on the Jacobian as input.
- `thm:BdTorIntroNF`: the corresponding uniform bound for torsion packets.
- The intermediate height and geometry inputs the paper uses: Betti map / Betti form, the non-degenerate height inequality, the Néron--Tate distance proposition for curves, and the Vojta/Mumford counting step.

The project is complete when the blueprint and Lean route cover these results with a dependency-correct chain from the geometric setup to the final counting theorems.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---:|---:|---|---|
| Setup: moduli space M_g with level structure | ACTIVE | 5-8 | ~400-600 | `AlgebraicGeometry.IsProper`, fiber products | M_g with level structure and universal curve are project-specific; must be built from scratch |
| Setup: Jacobian variety of genus-g curve | ACTIVE | 8-14 | ~800-1400 | `AlgebraicGeometry.IsProper`, abelian varieties | CONFIRMED MISSING from Mathlib (Mathlib's `WeierstrassCurve.Jacobian` = genus-1 Jacobian coordinates only); full abelian-variety Jacobian must be built; largest single risk in the project |
| Setup: Torelli map and universal Jacobian family | ACTIVE | 4-6 | ~360-540 | depends on Jacobian phase above, fiber products | must follow Jacobian phase; moduli-family structure is project-specific |
| Betti map: analytification and local trivializations | ACTIVE | 3-5 | ~280-420 | basic complex geometry, real-analytic maps | analytification API for algebraic varieties over ℂ is thin in Mathlib |
| Betti map: Betti map and Betti form existence | ACTIVE | 3-5 | ~260-400 | depends on above | period-lattice data and Hodge structure are project-specific |
| Betti map: general-base variant and étale reduction | ACTIVE | 2-4 | ~180-280 | étale morphisms, finite étale covers | descent argument is delicate |
| Betti map: Betti-rank Zariski-openness | ACTIVE | 1-2 | ~80-140 | real-analytic open-set arguments | likely quick once Betti map is done |
| Canonical-height: Weil heights on abelian varieties | ACTIVE | 2-4 | ~180-280 | `Height.logHeight` (VERIFIED) | need fiber-by-fiber height accounting |
| Canonical-height: Néron--Tate limit and properties | ACTIVE | 3-5 | ~280-420 | builds on Weil heights | quadratic-limit construction is project-specific |
| Canonical-height: IsNef / IsBig positivity wrappers | ACTIVE | 3-5 | ~280-420 | MISSING in Mathlib | these must be built from scratch |
| Canonical-height: arithmetic Bézout and Siu positivity | ACTIVE | 4-7 | ~400-620 | depends on IsNef/IsBig | intersection-theoretic Siu criterion is project-specific |
| Height inequality | ACTIVE | 4-6 | ~380-560 | depends on canonical-height phases | graph/intersection argument is delicate |
| Néron--Tate distance on curves | ACTIVE | 3-4 | ~240-360 | Faltings--Zhang morphism, combinatorial lemmas | induction and packet bounds need careful wiring |
| Rational-point counting | ACTIVE | 2-3 | ~180-260 | Vojta/Mumford bounds, rank bookkeeping | can run in parallel with torsion lane |
| Torsion-packet counting | ACTIVE | 2-3 | ~180-260 | shared height/distance lemmas | can run in parallel with rational-point lane |

## Routes

### Route 1: appendix-first height route

Build the analytic geometry (Betti map/form) and canonical-height/positivity infrastructure
first, then the general height inequality (Appendix B), then the curve-specific setup
(universal Jacobian, Faltings--Zhang, counting lemmas), and finally the main theorems.
The dependency order follows the paper exactly: universal geometry → analytic rank criteria
→ height inequalities → counting. Rational-point and torsion-packet lanes parallelise once
the shared height and distance lemmas are in place.

**Critical prerequisite for Route 1**: The Jacobian variety of a smooth curve of genus g ≥ 2
must be built as an abelian variety (confirmed MISSING from Mathlib). This is the largest
single prerequisite and must be prioritised in the Setup phases.

### Route 2: sorry-first / analytic-black-box (secondary lane)

State `prop:betti_map`, `prop:betti_form`, `prop:betti_map_app`, and all analytification
assumptions as axiom stubs in a dedicated `Analytic.lean` layer. Formalize the algebraic
height-inequality and counting argument (paper sections 6--8) against this interface first,
establishing the final theorem skeletons. Return to the analytic layer to fill stubs once the
algebraic core is verified. This route is kept as a contingency: if the Betti-map
formalization blocks downstream progress, switch to Route 2 to confirm the algebraic argument
end-to-end first.

## Open strategic questions

- Whether to front-load the Jacobian-variety construction or defer it by axiomatizing the
  existence of the Jacobian and its Neron model (this is the Route 2 analytic-black-box
  applied to algebra).
- How much of the Neron model / Torelli map can share infrastructure with the Jacobian
  abelian-variety construction.
- Whether `IsNef` / `IsBig` should target the existing Mathlib positivity API
  (`Mathlib.Analysis.InnerProductSpace` direction) or use a bespoke AG positivity library.

## Mathlib gaps & new material

- **Confirmed MISSING**: Jacobian abelian variety of genus-g curve; canonical-height
  (Néron--Tate) API for abelian varieties; `IsNef` / `IsBig` line-bundle positivity;
  Siu's positivity criterion; fine moduli space M_g with level structure; Betti-map
  analytification and real-analytic period data; Faltings--Zhang morphism.
- **Confirmed PRESENT**: `Height.logHeight` / `Height.mulHeight` (Weil height basics,
  `Mathlib.NumberTheory.Height.Basic`); `AlgebraicGeometry.IsProper`; fiber products;
  pullback; basic étale morphisms.
- The project must build all MISSING items from scratch. Each MISSING item corresponds to
  one or more ACTIVE phases in the table above.
