# Blueprint Writer Report: iter-004-howard-kolyvagin
**Status:** COMPLETE

## Changes
- Create `blueprint/src/chapters/Howard_Kolyvagin.tex` (new file, ~230 lines).
- Add `def:selmer-triple` (`MR4372220.Howard.selmerTriple`): Selmer structures, finite-singular iso, Selmer triples, modified Selmer groups, Kolyvagin systems, ordinary/Lambda-adic Selmer structures. `\uses{def:iwasawa-algebra}`.
- Add `thm:Zp-twisted` (`MR4372220.Howard.zpTwistedBound`): length bound for `M_alpha` via nonzero Kolyvagin system with error term `E_alpha`. `\uses{def:selmer-triple, def:iwasawa-algebra}`.
- Add `thm:howard` (`MR4372220.Howard.howardBound`): Lambda-adic specialization; `char(M)` divides `char(H^1_F(K,T)/Lambda*kappa_1)` in `Lambda[1/p,1/(gamma-1)]`. `\uses{thm:Zp-twisted, def:selmer-triple, def:iwasawa-algebra}`.
- Add `thm:howard-HPKS` (`MR4372220.Howard.heegnerKolyvaginSystem`): Heegner KS with nonzero `kappa_1^Hg`. `\uses{def:selmer-triple, cor:characters}`.
- Add `thm:howard-HP` (`MR4372220.Howard.heegnerHoward`): combined divisibility. `\uses{thm:howard, thm:howard-HPKS, def:iwasawa-algebra}`.
- leandag: 0 isolated nodes, 0 unknown_uses.

## References consulted
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex` (lines 1173–2260, verbatim quotes from source).

## Notes / Strategy
- `thm:Zp-twisted` proof is multi-page (~700 lines in source); sub-splitting into the Čebotarev lemma and inductive Kolyvagin step is recommended before a prover targets this theorem.
- `cor:howard` (source: Corollary after `thm:howard`, removing the `1/(gamma-1)` denominator under corank-one hypothesis) is not yet a blueprint declaration; its content is absorbed into the `thm:howard` statement and the proof of `thm:howard-HP`. Consider adding a `cor:howard` block in a future iteration.
