# Blueprint Writer Directive

## Slug
iter-001-algebraic-comparison

## Target chapter
blueprint/src/chapters/Algebraic_Iwasawa_Comparison.tex

## Strategy context
This chapter is the algebraic comparison lane. It should take the local Selmer foundation as given, compare the `E`-Selmer groups to the character Selmer groups through the residual decomposition `E[p]^{ss}\cong \mathbb F_p(\phi)\oplus\mathbb F_p(\psi)`, and isolate the local Euler-factor bookkeeping that produces the algebraic `\lambda` formula. Keep this strictly separate from the analytic `p`-adic `L`-function comparison and from the Howard/Kolyvagin branch.

## Required content
- Proposition `\label{prop:modp-E}`: exact sequence comparing `M_E[p]` with `M_\phi[p]` and `M_\psi[p]`, including the induced exact sequence on imprimitive residual Selmer groups.
- Proposition `\label{prop:modp-E-tors}`: `\mathfrak X_E^S` and `\mathfrak X_E` are `\Lambda`-torsion with `\mu=0`, together with the `M[p]` versus `M` comparison.
- Corollary `\label{cor:lambda-E}`: no non-trivial finite `\Lambda`-submodules and `\lambda(\mathfrak X_E^S)=\dim_{\mathbb F_p} H^1_{\Fcal_{\rm Gr}^S}(K,M_E[p])`.
- Theorem `\label{MAINalgside}`: the algebraic Iwasawa invariant comparison theorem for `\mathfrak X_E`, including the local Euler-factor correction terms.
- Optional supporting blocks if needed for the proof chain: the residual exact sequence for `M_E[p]`, the definition of `\mathfrak X_E^S` and `\mathfrak X_E`, and the split-prime Euler factor statements for `\mathcal P_w(E)`, `\mathcal P_w(\phi)`, `\mathcal P_w(\psi)`.

## Out of scope
- Local cohomology of characters and the proof of `\mu=0` for `\theta`-Selmer groups.
- Any p-adic L-function or Kriz congruence material.
- Howard/Kolyvagin arguments or Heegner-point constructions.
- The final main conjecture and arithmetic applications.

## References
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`: §Algebraic side, subsections `Local cohomology groups of E`, `Selmer groups of E`, and `Comparison I: Algebraic Iwasawa invariants`.
- `references/MR4372220-anticyclotomic-iwasawa.tex`: Introduction, `Method of proof and outline of the paper`.

## Expected outcome
A chapter that proves the algebraic comparison theorem cleanly from the local foundation and the character Selmer formulas, with the `E`-specific residual exact sequence and local Euler factors made explicit so later chapters can quote them without re-deriving the algebra.
