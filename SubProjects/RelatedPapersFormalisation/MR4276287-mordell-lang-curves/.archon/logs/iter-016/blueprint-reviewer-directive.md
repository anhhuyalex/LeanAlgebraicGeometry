# Blueprint Reviewer Directive

## Slug
iter-016

## Strategy snapshot
Goal: Formalize the uniform Mordell-Lang bounds for curves (arXiv:2001.10276, MR4276287).
Three main theorems: ThmBdRatIntro, ThmBdFinRank, thm:BdTorIntroNF.

Route 1 (appendix-first): Betti map → canonical height/positivity → height inequality →
curve-specific setup → counting theorems.
Route 2 (secondary/contingency): sorry-first analytic-black-box — state Betti-map
propositions as axiom stubs and formalize the algebraic core first.

Phases & estimations (active, from STRATEGY.md):
- Setup: M_g with level structure (ACTIVE, 5-8 iters, ~400-600 LOC)
- Setup: Jacobian variety of genus-g curve (ACTIVE, 8-14 iters, ~800-1400 LOC) — CONFIRMED MISSING from Mathlib
- Setup: Torelli map and universal Jacobian family (ACTIVE, 4-6 iters, ~360-540 LOC)
- Betti map: analytification and local trivializations (ACTIVE, 3-5 iters, ~280-420 LOC)
- Betti map: Betti map and Betti form existence (ACTIVE, 3-5 iters, ~260-400 LOC)
- Betti map: general-base variant and étale reduction (ACTIVE, 2-4 iters, ~180-280 LOC)
- Betti map: Betti-rank Zariski-openness (ACTIVE, 1-2 iters, ~80-140 LOC)
- Canonical-height: Weil heights on abelian varieties (ACTIVE, 2-4 iters, ~180-280 LOC)
- Canonical-height: Néron-Tate limit and properties (ACTIVE, 3-5 iters, ~280-420 LOC)
- Canonical-height: IsNef/IsBig positivity wrappers (ACTIVE, 3-5 iters, ~280-420 LOC) — MISSING from Mathlib
- Canonical-height: arithmetic Bézout and Siu positivity (ACTIVE, 4-7 iters, ~400-620 LOC)
- Height inequality (ACTIVE, 4-6 iters, ~380-560 LOC)
- Néron-Tate distance on curves (ACTIVE, 3-4 iters, ~240-360 LOC)
- Rational-point counting (ACTIVE, 2-3 iters, ~180-260 LOC) — can parallel with torsion
- Torsion-packet counting (ACTIVE, 2-3 iters, ~180-260 LOC) — can parallel with rational

## Routes
- Route 1: appendix-first (primary) — all phases above
- Route 2: sorry-first analytic-black-box (contingency) — state Betti-map props as axiom
  stubs in Analytic.lean, formalize algebraic core first

## References
- references/summary.md — full reference index
- references/MR4276287-mordell-lang-curves-source/BettiMapForm.tex — Betti map/form
- references/MR4276287-mordell-lang-curves-source/HtIneqFinalVer.tex — Appendix B
- references/MR4276287-mordell-lang-curves-source/HtIneq.tex — height inequality
- references/MR4276287-mordell-lang-curves-source/NTbase.tex — Section 5
- references/MR4276287-mordell-lang-curves-source/SettingUp.tex — Section 6
- references/MR4276287-mordell-lang-curves-source/DistanceCurve.tex — Section 7
- references/MR4276287-mordell-lang-curves-source/RatPt.tex — Section 8
- references/MR4276287-mordell-lang-curves-source/silvermantate.tex — Appendix A
- references/MR4276287-mordell-lang-curves-source/intro.tex — Introduction

## Focus areas
This is the first blueprint-reviewer run. The blueprint was just extended with proof blocks
for ALL 20 previously infinity-source declarations in this iteration. Please focus on:
1. Whether the proof sketches are detailed enough for a prover
2. Whether the \uses{} in proof blocks are accurate
3. Whether the source quotes are properly verbatim
4. Whether any declarations are missing \begin{proof} blocks

## Known issues
- All Lean declarations are unmatched (Basic.lean has no declarations yet — only `import Mathlib`)
- The 22 unmatched \lean{} references are expected and not errors
- def:ambient_setup and def:nondegenerate_app are definitions and have no proof block by design
