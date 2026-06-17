# Blueprint Writer Directive

## Slug
iter-001-local-selmer

## Target chapter
blueprint/src/chapters/Local_Iwasawa_Selmer.tex

## Strategy context
This chapter is the shared local foundation for every later phase. It should introduce the anticyclotomic Iwasawa algebra, the character Selmer groups, the elliptic-curve Selmer groups, and the local cohomology lemmas that feed both the algebraic and Howard/Kolyvagin branches. Keep the API thin and Mathlib-shaped around `Submodule`, `LinearMap.ker`, `Exact`, and `Ideal`, with the Selmer objects as project-specific submodules/predicates rather than bespoke containers.

## Required content
- Definition `\label{def:iwasawa-algebra}`: introduce `\Lambda`, `\Lambda^{\mathrm{ur}}`, the character modules `M_\theta`, the elliptic-curve module `M_E`, and the primitive/imprimitive Selmer structures for both characters and `E`.
- Lemma `\label{lem:commalg}`: the commutative algebra criterion showing a finitely generated `\Lambda`-module with `X[T]=0` and free quotient `X/TX` is free.
- Lemma `\label{lem:local-char-wneqp}`: split local cohomology at `w\nmid p`, including the characteristic ideal formula and `\mu=0`.
- Proposition `\label{lem:local-char-wp}` or equivalent theorem block: local cohomology at `w\mid p`, cofree rank-one statement under the `\theta|_{G_w}\neq 1,\omega` hypothesis.
- Theorem `\label{thm:mu-zero-theta}`: Rubin/Hida `\mu=0` theorem for the Selmer group of a character.
- Proposition `\label{prop:lambda-theta}`: the imprimitive Selmer `\lambda` formula and finiteness of the residual Selmer group.
- Corollary `\label{cor:characters}`: exactness for the residual Selmer group and vanishing of the second cohomology group.

## Out of scope
- Any `E`-specific residual comparison (`M_E[p]`, `\mathfrak X_E`).
- Any p-adic L-function statements or analytic comparison.
- Any Kolyvagin system construction or Howard specialization.
- Main conjecture / Perrin-Riou / BSD applications.

## References
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`: §Algebraic side, subsections `Local cohomology groups of characters` and `Selmer groups of characters`.
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`: §Algebraic side, the `Local cohomology groups of E` and `Selmer groups of E` subsections for the shared notation.
- `references/MR4372220-anticyclotomic-iwasawa.tex`: Introduction, `Statement of the main results` and `Method of proof and outline of the paper`.

## Expected outcome
A chapter that fixes the local notation once, proves the split and `p`-adic local cohomology facts, and packages the character Selmer theory so the algebraic, analytic, and Howard branches can all reuse the same foundation without reintroducing the objects.
