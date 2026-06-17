# Blueprint Writer Report: iter-004-analytic-comparison
**Status:** COMPLETE

## Changes
- Create `blueprint/src/chapters/Analytic_Iwasawa_Comparison.tex` (new chapter).
- Add `thm:BDP` (`MR4372220.Analytic.bdpLFunction`): BDP p-adic L-function interpolating central L-values; `\uses{def:iwasawa-algebra}`.
- Add `thm:Katz` (`MR4372220.Analytic.katzLFunction`): Katz p-adic L-function with interpolation formula + Hida mu=0 note; `\uses{def:iwasawa-algebra}`.
- Add `thm:kriz` (`MR4372220.Analytic.krizCongruence`): Kriz congruence L_E ≡ (E_{phi,psi}^iota)^2 (L_phi)^2 mod p; `\uses{thm:BDP, thm:Katz}`.
- Add `cor:Kriz` (`MR4372220.Analytic.krizLambda`): mu(L_E)=0 and lambda formula; `\uses{thm:kriz, def:iwasawa-algebra}`.
- Add `mulambda` (`MR4372220.Analytic.mulambda`): lambda(L_E)=lambda(X_E) bridge; `\uses{cor:Kriz, MAINalgside}`.

## References consulted
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`: lines 933–1169 (§Analytic side, §p-adic L-functions, §Katz p-adic L-functions, §Comparison II: Analytic Iwasawa invariants).
