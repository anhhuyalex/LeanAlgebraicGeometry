# Blueprint Writer Directive

## Slug
iter-004-main-applications

## Target chapter
blueprint/src/chapters/Main_Conjecture_Applications.tex

## Strategy context
This chapter covers the final downstream arc of the Greenberg-Vatsal comparison route: the proof of the anticyclotomic Iwasawa main conjecture (thm:thmA), Perrin-Riou's Heegner-point main conjecture (cor:PR), the p-converse to Gross--Zagier--Kolyvagin (thm:thmB / cor:thmB), and the p-part of BSD in analytic rank 1 (thm:thmC).

The structure is:
- First, prove the equivalence of the two formulations of the main conjecture (prop:equiv-imc), then derive thm:thmA and cor:PR from Howard + mu/lambda comparisons.
- Second, independently (parallel lane), derive thm:thmB / cor:thmB from cor:PR plus Gross--Zagier/Kolyvagin input.
- Third, independently (parallel lane), derive thm:thmC from thm:thmA using the BSD control-theorem and Gross--Zagier bookkeeping.

IMPORTANT: thm:thmB/cor:thmB and thm:thmC must be kept as separate downstream consumers of thm:thmA. Do not interleave their proofs.

## Required content

The chapter header must include:
```
% archon:covers MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Applications.lean
```

Required declarations (in dependency order), each with `\label{}`, `\lean{}`, `\uses{}`, citation blocks, and `\begin{proof}...\end{proof}`:

1. **Proposition `prop:equiv-imc`** (`\lean{MR4372220.Applications.equivImc}`): The Heegner-point main conjecture (char(X_E) = char(L_E) as ideals of Lambda) is equivalent to the BDP main conjecture (char(X_E^BDP) = char(L_E^BDP)). The equivalence uses the involution on Lambda and the relation between the two L-function constructions. `\uses{thm:howard-HP, mulambda, def:iwasawa-algebra}`. Source: Eisenstein.tex §Proof of the Iwasawa main conjectures.

2. **Theorem `thm:thmA`** (`\lean{MR4372220.Applications.mainConjectureA}`): The anticyclotomic Iwasawa main conjecture: char(X_E) = char(L_E) as ideals of Lambda. This follows from the Howard divisibility (thm:howard-HP) and the mu/lambda equality (mulambda). `\uses{prop:equiv-imc, thm:howard-HP, mulambda}`. Source: Eisenstein.tex §Proof of the Iwasawa main conjectures, Theorem A.

3. **Corollary `cor:PR`** (`\lean{MR4372220.Applications.perrinRiou}`): Perrin-Riou's Heegner-point main conjecture follows from thm:thmA and the relation between the two main-conjecture formulations. `\uses{thm:thmA, prop:equiv-imc}`. Source: Eisenstein.tex §Proof of the Iwasawa main conjectures, Corollary (Perrin-Riou).

4. **Theorem `thm:thmB`** (`\lean{MR4372220.Applications.pConverse}`): The p-converse to Gross--Zagier--Kolyvagin: if ord_{s=1} L(E/Q, s) = 1 and the Heegner hypothesis holds, then rank_Z E(Q) = 1 and Sha(E/Q)[p^infty] is finite. This uses cor:PR, the control theorem for the anticyclotomic Selmer group, and Gross--Zagier/Kolyvagin. `\uses{cor:PR, def:iwasawa-algebra}`. Source: Eisenstein.tex §Proof of Theorem B (or the relevant application section).

5. **Corollary `cor:thmB`** (`\lean{MR4372220.Applications.pConverseCor}`): The mod-p corollary: if Sha(E/Q)[p] = 0 and the analytic rank is 1, then rank E(Q) = 1. `\uses{thm:thmB}`. Source: Eisenstein.tex (follows from thm:thmB by the structure of the argument).

6. **Theorem `thm:thmC`** (`\lean{MR4372220.Applications.bsdPPart}`): The p-part of the BSD formula in analytic rank 1: |Sha(E/Q)[p^infty]| = (product of Tamagawa factors at p) / (index of Heegner point in E(Q))^2, with the appropriate Gross--Zagier height formula. This uses thm:thmA, the Gross--Zagier formula, and the control theorem. `\uses{thm:thmA, thm:thmB, def:iwasawa-algebra}`. Source: Eisenstein.tex §Proof of Theorem C (BSD rank-one formula).

Each declaration must have a `\begin{proof}...\end{proof}` block (not inline proof text) with a proof sketch sufficient for formalization. Cross-references via `\cref{...}` to blueprint labels.

## Out of scope
- Re-proving the mu/lambda comparisons (those are in the analytic and algebraic chapters).
- Re-proving the Howard bound (that is in Howard_Kolyvagin.tex).
- The local cohomology setup.

## References
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`: §Proof of the Iwasawa main conjectures, §Proof of Theorem B, §Proof of Theorem C. READ these sections verbatim before writing citation blocks.
- `references/MR4372220-anticyclotomic-iwasawa.tex`: Introduction "Statement of the main results" for the exact statement of Theorems A, B, C and Corollary (Perrin-Riou).

## Expected outcome
A complete `Main_Conjecture_Applications.tex` chapter with 6 declaration blocks (prop:equiv-imc, thm:thmA, cor:PR, thm:thmB, cor:thmB, thm:thmC), each with source-backed citations from Eisenstein.tex, proper `\begin{proof}...\end{proof}` blocks, and accurate `\uses{}` edges. The p-converse and BSD branches must be visibly separate consumers of thm:thmA. The chapter does NOT include content.tex changes.
