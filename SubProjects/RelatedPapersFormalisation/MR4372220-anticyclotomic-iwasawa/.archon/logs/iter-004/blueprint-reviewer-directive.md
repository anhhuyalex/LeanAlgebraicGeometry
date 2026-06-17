# Blueprint Reviewer Directive

## Slug
iter-004-blueprint

## Iteration
004

## Scope
Full blueprint audit — all chapters under `blueprint/src/chapters/`. Do NOT scope-limit. This is the whole-blueprint completeness and correctness audit for iteration 004.

## What to check

Standard whole-blueprint audit:
1. Per-chapter: complete | partial, correct | incorrect, notes.
2. Dependency & isolation findings: broken \uses{}, isolated nodes.
3. Unstarted-phase proposals (if any STRATEGY.md phase has no blueprint coverage).
4. HARD GATE per chapter: complete + correct + no must-fix = gate cleared.

The blueprint now has 27 declarations across 5 substantive chapters:
- `Local_Iwasawa_Selmer.tex`: 7 declarations (def:iwasawa-algebra, lem:commalg, lem:local-char-wneqp, lem:local-char-wp, thm:mu-zero-theta, prop:lambda-theta, cor:characters)
- `Algebraic_Iwasawa_Comparison.tex`: 4 declarations (prop:modp-E, prop:modp-E-tors, cor:lambda-E, MAINalgside)
- `Analytic_Iwasawa_Comparison.tex`: 5 declarations (thm:BDP, thm:Katz, thm:kriz, cor:Kriz, mulambda)
- `Howard_Kolyvagin.tex`: 5 declarations (def:selmer-triple, thm:Zp-twisted, thm:howard, thm:howard-HPKS, thm:howard-HP)
- `Main_Conjecture_Applications.tex`: 6 declarations (prop:equiv-imc, thm:thmA, cor:PR, thm:thmB, cor:thmB, thm:thmC)

Pay special attention to:
- Whether proof sketches are detailed enough for formalization (not just one-liners)
- Whether \uses{} edges are mathematically accurate
- Whether the analytic chapter (new this iter) correctly expresses the Kriz congruence
- Whether the Howard chapter (new this iter) correctly expresses the abstract Kolyvagin bound
- Whether the Applications chapter (new this iter) correctly separates the p-converse and BSD branches
