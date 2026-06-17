# Blueprint Writer Directive

## Slug
iter-001-applications

## Target chapter
blueprint/src/chapters/Main_Conjecture_Applications.tex

## Strategy context
This chapter is the downstream application lane. It should have three clearly separated sections: the main anticyclotomic main conjecture / Perrin-Riou equivalence, the `p`-converse to Gross--Zagier--Kolyvagin, and the BSD rank-one formula. The p-converse and BSD branches should be separate consumers of `thm:thmA`, not a single serialized block.

## Required content
- Proposition `\label{prop:equiv-imc}`: equivalence between the Heegner-point main conjecture and the BDP main conjecture.
- Theorem `\label{thm:thmA}`: the main anticyclotomic Iwasawa main conjecture at Eisenstein primes.
- Corollary `\label{cor:PR}`: Perrin-Riou’s Heegner-point main conjecture.
- Theorem `\label{controlthm}`: the anticyclotomic control theorem needed for the BSD deduction.
- Theorem `\label{thmGZ}` and Theorem `\label{thmpadicGZ}`: the Gross--Zagier and p-adic Gross--Zagier formulas used in the BSD lane.
- Theorem `\label{thmGV}`: the Greenberg--Vatsal analytic-rank-zero input used for the quadratic twist.
- Theorem `\label{thm:thmB}` and Corollary `\label{cor:thmB}`: the `p`-converse to Gross--Zagier--Kolyvagin and its mod-`p` version.
- Theorem `\label{thm:thmC}`: the `p`-part of BSD in analytic rank `1`.

## Out of scope
- The local Selmer foundation, analytic `p`-adic `L`-function comparison, or Howard/Kolyvagin arguments.
- Any attempt to re-prove the comparison theorems inside this chapter; this chapter should only consume them.

## References
- `references/MR4372220-anticyclotomic-iwasawa.tex`: Introduction `Statement of the main results`, `Method of proof and outline of the paper`, and the later proof sections for `thm:E` and `thm:F`.
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`: `Proof of Theorem~\ref{thm:C} and Corollary~\ref{cor:D}` and `Proof of Theorem~\ref{thm:E} and Theorem~\ref{thm:F}`.

## Expected outcome
A downstream chapter that cleanly deduces the main conjecture and both arithmetic applications from the comparison theorems, with separate theorem blocks and dependency edges for the main-conjecture, `p`-converse, and BSD branches.
