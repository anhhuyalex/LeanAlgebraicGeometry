# Strategy Critic Directive

## Slug
iter-012-strategy-critic-r2

## Project goal

\newcommand{\pullback}[1][dr]{\save*!/#1-1.2pc/#1:(-1,1)@^{|-}\restore}
\newcommand{\bigpullback}[1][dr]{\save*!/#1-2.2pc/#1:(-2,2)@^{|-}\restore}
\newcommand{\leftpullbak}[1][dl]{\save*!/#1-1.2pc/#1:(-1,1)@^{|-}\restore}



\newcommand{\pushoutcorner}[1][dr]{\save*!/#1+1.7pc/#1:(1,-1)@^{|-}\restore}
\newcommand{\pullbackcorner}[1][dr]{\save*!/#1-1.7pc/#1:(-1.5,1.5)@^{|-}\restore}


\usepackage{color}
\newcommand{\Pcomment}[1]{\textcolor{red}{(PH)}\marginpar{\tiny\textcolor{red}{#1}}}
\newcommand{\Pinlinecomment}[1]{\textcolor{red}{(PH)  {#1}}}

\newcommand{\Gcomment}[1]{\textcolor{blue}{(ZG)}\marginpar{\tiny\textcolor{blue}{#1}}}
\newcommand{\Ginlinecomment}[1]{\textcolor{blue}{(ZG)  {#1}}}


\newcommand{\bestlevel}{3} %%% The minimal level structure that makes
%%% the argument work

%\makeindex  %%% Generates the index. Remove for final version.

## Strategy under review

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
| Setup and universal family | ACTIVE | 3-5 | ~320-480 | projective varieties, fiber products, curves/Jacobians API, basic height machine statements | moduli-level objects are mostly project-specific; keep the API lean |
| Betti map and Betti form | ACTIVE | 3-5 | ~360-540 | analytic trivializations, real-analytic maps, differential rank language, basic complex geometry wrappers | likely needs substantial project-specific infrastructure for Siegel/moduli data |
| Canonical-height and positivity infrastructure | ACTIVE | 2-4 | ~220-340 | `CanonicalHeight`-style API, `IsNef` / `IsBig` wrappers, arithmetic Bézout / Siu positivity, pullback/graph formalism | this layer is currently missing from Mathlib and should be isolated explicitly |
| Height inequality | ACTIVE | 4-6 | ~380-560 | the above positivity API, graph construction, intersection-theoretic inequalities | the graph/intersection argument is delicate and easy to understate |
| Néron--Tate distance on curves | ACTIVE | 3-4 | ~240-360 | Faltings--Zhang morphism, uniform degree bounds, combinatorial curve lemmas | induction on the base and packet bounds need careful dependency wiring |
| Rational-point counting | ACTIVE | 2-3 | ~180-260 | quantitative Vojta/Mumford-style bounds, rank bookkeeping, height decomposition | constant-chasing and the small/large point split can drift if the blueprint is too terse |
| Torsion-packet counting | ACTIVE | 2-3 | ~180-260 | the same shared height/distance lemmas, plus the torsion specialization | should stay parallel to the rational-point lane once the shared lemmas are in place |

## Routes

### Route 1: appendix-first height route

Build the appendix-level general height inequality and Betti-map package first, then specialize to the curve family and derive the Néron--Tate distance proposition, the finite-rank bound, and the rational/torsion uniformity theorems.

This is the route actually used by the paper and it gives the cleanest dependency order: universal geometry and analytic rank criteria first, then the canonical-height / positivity layer, then height inequalities, then curve counting. After the shared height and distance lemmas are in place, the rational-point and torsion-packet counting lanes can proceed in parallel.

## Open strategic questions

- How much of the moduli / abelian-scheme infrastructure can be expressed in existing Mathlib terms versus needing project-specific wrappers?
- Whether the Lean route should keep the appendix generality as a single reusable layer, or split it into smaller theorem blocks before the curve-specific counting argument.

## Mathlib gaps & new material

- Standard Mathlib support is expected for basic algebraic geometry, projective space, fiber products, and generic height bookkeeping where available.
- The project will need new formal material for the moduli of curves and principally polarized abelian varieties with level structure, the universal Jacobian / Torelli map package, the Betti map and Betti form, the Faltings--Zhang morphism, and the paper-specific non-degeneracy criterion.
- The height inequality and counting arguments depend on project-specific lemmas about the graph construction, canonical heights, positivity (`IsNef` / `IsBig`-style statements), intersection bounds, and the quantitative Vojta/Mumford package.

## References index

# References

<!-- archon:references-summary -->

## File inventory

| File | Description | How to read (confirmed working) |
| ---- | ----------- | ------------------------------- |
| `MR4276287-mordell-lang-curves.pdf` | PDF of Uniformity in Mordell-Lang for curves (MR4276287, arXiv:2001.10276). | `Read` directly or use a page range for long pulls. |
| `MR4276287-mordell-lang-curves.tex` | Extracted TeX source for the same paper. | `Read` directly. |
| `MR4276287-mordell-lang-curves-source/` | Extracted source directory. | Browse the extracted arXiv source files directly. |
| `retrieval-notes.md` | Retrieval metadata for the paper. | `Read` directly. |
| `MR4276287-mordell-lang-curves-source.tar.gz` | Raw arXiv source archive. | Keep for provenance; extract with `tar -xzf`. |

## Blueprint summary

blueprint/src/chapters/Overview.tex — \chapter{Overview} \label{chap:overview}  % archon:covers MR4276287UniformityInMordellLangForCurves.lean MR4276287UniformityInMordellLangForCurves/Basic.lean  This is the auto-bootstrapped blueprint for MR4276287: Uniformity in Mordell-Lang for curves.

## Prior critique status

- iter-012: effort under-count + counting split — addressed
