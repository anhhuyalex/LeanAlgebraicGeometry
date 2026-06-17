# Blueprint Doctor

## Chapter coverage problems (`% archon:covers`)

A chapter's `% archon:covers <file> ...` declaration tells the prover-dispatch gate which Lean files that chapter blueprints. The issues below would route the gate to the wrong chapter — fix the declaration (correct the path, or make exactly one chapter own each file).

- chapter `Algebraic_Iwasawa_Comparison.tex` covers `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Algebraic.lean`, which does not exist
- chapter `Analytic_Iwasawa_Comparison.tex` covers `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Analytic.lean`, which does not exist
- chapter `Howard_Kolyvagin.tex` covers `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Howard.lean`, which does not exist
- chapter `Local_Iwasawa_Selmer.tex` covers `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Local.lean`, which does not exist
- chapter `Main_Conjecture_Applications.tex` covers `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Applications.lean`, which does not exist

