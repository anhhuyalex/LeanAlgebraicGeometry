# Blueprint Writer Directive

## Slug
iter-001-analytic-comparison

## Target chapter
blueprint/src/chapters/Analytic_Iwasawa_Comparison.tex

## Strategy context
This chapter is the analytic comparison lane. It should define the anticyclotomic BDP and Katz `p`-adic `L`-functions, state the Kriz congruence, and derive the analytic `\mu/\lambda` comparison. Keep the anticyclotomic `\Lambda` interface shared with the local chapter, but do not mix in Selmer or Howard arguments.

## Required content
- Theorem `\label{thm:BDP}`: construction and interpolation property of the BDP `p`-adic `L`-function `\mathcal L_E`.
- Theorem `\label{thm:Katz}`: construction and interpolation property of the Katz `p`-adic `L`-function `\mathcal L_\theta`.
- Theorem `\label{thm:kriz}`: Kriz’s congruence comparing `\mathcal L_E` with the squared Katz factors and the Euler correction term `\mathcal E_{\phi,\psi}`.
- Theorem or corollary `\label{cor:Kriz}`: the vanishing of `\mu(\mathcal L_E)` and the `\lambda` formula for `\mathcal L_E`.
- Theorem `\label{mulambda}`: the final analytic comparison `\lambda(\mathcal L_E)=\lambda(\mathfrak X_E)`.
- If needed for a clean proof chain, include the definition of `\mathcal E_{\phi,\psi}` and the involution `\iota` on `\Lambda`.

## Out of scope
- Selmer groups, local cohomology, and the algebraic invariant comparison.
- Howard/Kolyvagin, Heegner points, or the main conjecture applications.

## References
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`: §Analytic side, subsections `p-adic L-functions`, `Katz p-adic L-functions`, and `Comparison II: Analytic Iwasawa invariants`.
- `references/MR4372220-anticyclotomic-iwasawa.tex`: Introduction, `Method of proof and outline of the paper`.

## Expected outcome
A chapter that cleanly packages the two anticyclotomic `p`-adic `L`-functions, the Eisenstein congruence, and the resulting `\mu/\lambda` identities, so the later main-conjecture chapter can cite the analytic side as a finished input.
