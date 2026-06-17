# Blueprint Writer Directive

## Slug
iter-004-analytic-comparison

## Target chapter
blueprint/src/chapters/Analytic_Iwasawa_Comparison.tex

## Strategy context
This chapter covers the analytic p-adic L-function comparison lane of the project. The project is formalizing MR4372220 (Castella--Grossi--Lee--Skinner), which proves the anticyclotomic Iwasawa main conjecture for rational elliptic curves at Eisenstein primes. The analytic lane is independent of the algebraic lane once the local Selmer notation (iwasawa algebra, M_theta, M_E) is established. The key goal is to:
1. Construct the two anticyclotomic p-adic L-functions: BDP (L_E) and Katz (L_theta).
2. State the Kriz Eisenstein congruence relating them mod p.
3. Derive the mu/lambda comparison for L_E.
4. Connect the analytic lambda to the algebraic lambda (mulambda theorem), which feeds into the main conjecture.

The chapter must supply the source-backed blueprint declarations for `cor:Kriz` and `mulambda` which are needed downstream by the main conjecture chapter.

## Required content

The chapter header must include:
```
% archon:covers MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Analytic.lean
```

Required declarations (in dependency order), each with `\label{}`, `\lean{}`, `\uses{}`, citation blocks, and `\begin{proof}...\end{proof}`:

1. **Theorem `thm:BDP`** (`\lean{MR4372220.Analytic.bdpLFunction}`): State the BDP anticyclotomic p-adic L-function construction. The function L_E in Lambda (or its localization) interpolates the central values of L(E/K, chi, 1) for ring-class characters chi. Include the interpolation formula and the nonvanishing of the Euler factor. Source: Eisenstein.tex §Analytic side, subsection "p-adic L-functions" (BDP construction). `\uses{def:iwasawa-algebra}`.

2. **Theorem `thm:Katz`** (`\lean{MR4372220.Analytic.katzLFunction}`): State the Katz p-adic L-function L_theta for a character theta. This element of Lambda^ur interpolates Hecke L-values for theta twisted by ring-class characters. Include the mu=0 statement (Hida's theorem). Source: Eisenstein.tex §Analytic side, subsection "Katz p-adic L-functions". `\uses{def:iwasawa-algebra}`.

3. **Theorem `thm:kriz`** (`\lean{MR4372220.Analytic.krizCongruence}`): The Kriz Eisenstein congruence: L_E is congruent modulo p to (E_{phi,psi}^iota)^2 (L_phi)^2 (L_psi)^2 in an appropriate sense (mod p relation on lambda-invariants). This is the key source-heavy result that compares the two p-adic L-functions. Source: Eisenstein.tex §Analytic side, Kriz's congruence theorem. `\uses{thm:BDP, thm:Katz}`.

4. **Corollary `cor:Kriz`** (`\lean{MR4372220.Analytic.krizLambda}`): From the Kriz congruence, derive: mu(L_E) = 0 and lambda(L_E) = lambda(L_phi) + lambda(L_psi) + sum_{w in S} (lambda(P_w(phi)) + lambda(P_w(psi)) - lambda(P_w(E))). This is the analytic-side mu/lambda formula. Source: Eisenstein.tex §Comparison II: Analytic Iwasawa invariants. `\uses{thm:kriz, def:iwasawa-algebra}`.

5. **Theorem `mulambda`** (`\lean{MR4372220.Analytic.mulambda}`): The comparison between the analytic and algebraic lambda-invariants: lambda(L_E) = lambda(X_E), combining cor:Kriz with the algebraic comparison MAINalgside. This is the bridge between the two sides of the main conjecture. Source: Eisenstein.tex §Comparison II or §Proof of the Iwasawa main conjectures. `\uses{cor:Kriz, MAINalgside}`.

Each theorem/corollary must have a `\begin{proof}...\end{proof}` block (not inline proof text) with a proof sketch sufficient for formalization. The proof sketch must include cross-references via `\cref{...}` to blueprint labels.

## Out of scope
- The Selmer group definitions (those are in Local_Iwasawa_Selmer.tex).
- The residual comparison for E[p] (that is in Algebraic_Iwasawa_Comparison.tex).
- The Howard/Kolyvagin argument.
- The main conjecture proof and downstream applications.

## References
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`: §Analytic side (subsections "p-adic L-functions", "Katz p-adic L-functions", "The Kriz congruence"), §Comparison II: Analytic Iwasawa invariants. READ these sections verbatim before writing the citation blocks.
- `references/MR4372220-anticyclotomic-iwasawa.tex`: Introduction "Method of proof and outline of the paper" for the role of the analytic comparison.

## Expected outcome
A complete `Analytic_Iwasawa_Comparison.tex` chapter with 5 declaration blocks (thm:BDP, thm:Katz, thm:kriz, cor:Kriz, mulambda), each with source-backed citations from Eisenstein.tex, proper `\begin{proof}...\end{proof}` blocks, and accurate `\uses{}` edges. The chapter does NOT include content.tex changes; the plan agent manages that.
