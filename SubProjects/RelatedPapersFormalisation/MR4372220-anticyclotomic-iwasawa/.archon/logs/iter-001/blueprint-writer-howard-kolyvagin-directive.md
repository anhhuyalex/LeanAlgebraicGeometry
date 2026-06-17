# Blueprint Writer Directive

## Slug
iter-001-howard-kolyvagin

## Target chapter
blueprint/src/chapters/Howard_Kolyvagin.tex

## Strategy context
This chapter is the technical bottleneck. It must be explicitly decomposed into a bridge-lemma stack and a separate Heegner-point Kolyvagin construction, rather than a single monolithic `Howard` block. Keep the abstract Selmer-system inequalities reusable for downstream chapters, and keep the Heegner-point source-heavy construction visibly separate from the abstract specialization lemmas.

## Required content
- Definition `\label{def:selmer-triple}`: Selmer structures, Selmer triples, modified local conditions, and the finite-singular comparison isomorphism.
- Lemma `\label{lemmamod}`: comparison of `T^{(k)}/\mathfrak m^i` and `T^{(k)}[\mathfrak m^i]`.
- Proposition `\label{propstructure}`: the `R^{(k)}\oplus M^{(k)}(n)\oplus M^{(k)}(n)` structure theorem for the relevant Selmer groups.
- Proposition `\label{prop:prime2}` and Corollary `\label{cor:prime2}`: the Cebotarev/error-term prime selection lemmas.
- Lemmas `\label{lem:key0}`, `\label{lem:key}`, and Proposition `\label{prop:key}`: the torsion-module bookkeeping needed to drive the rank-one argument.
- Theorem `\label{thm:rank1}`: the rank-one conclusion from a nonzero Kolyvagin class.
- Theorem `\label{thm:Zp-twisted}`: the twisted Selmer bound with explicit error term `E_\alpha`.
- Theorem `\label{thm:howard}`: the `\Lambda`-adic specialization/divisibility theorem.
- Theorem `\label{thm:howard-HPKS}`: construction of the nontrivial Heegner-point Kolyvagin system.
- Theorem `\label{thm:howard-HP}`: the Heegner-point input to the later main-conjecture deduction.

## Out of scope
- The local character Selmer theory and the algebraic `M_E` comparison.
- BDP/Katz/Kriz analytic comparisons.
- Main conjecture / Perrin-Riou / BSD applications.

## References
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`: §A Kolyvagin system argument, especially `Selmer structures and Kolyvagin systems`, `Bounding Selmer groups`, `Proof of Theorem~\ref{thm:Zp-twisted}`, `Proof of Theorem~\ref{thm:howard-HPKS}`, and `Proof of the Iwasawa main conjectures`.
- `references/MR4372220-anticyclotomic-iwasawa.tex`: `Method of proof and outline of the paper`.

## Expected outcome
A chapter split into an abstract Howard bridge-lemma section and a Heegner-point Kolyvagin section, so the specialization theorem and the Heegner construction can be reused independently by the main-conjecture chapter and the arithmetic applications.
