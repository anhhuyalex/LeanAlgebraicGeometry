# Blueprint Writer Report: iter-004-main-applications
**Status:** COMPLETE

## Changes
- Created `blueprint/src/chapters/Main_Conjecture_Applications.tex` with 6 declaration blocks.
- `prop:equiv-imc` (`MR4372220.Applications.equivImc`): Equivalence of BDP and Perrin-Riou formulations; `\uses{thm:howard-HP, mulambda, def:iwasawa-algebra}`.
- `thm:thmA` (`MR4372220.Applications.mainConjectureA`): Anticyclotomic IMC equality; `\uses{prop:equiv-imc, thm:howard-HP, mulambda}`.
- `cor:PR` (`MR4372220.Applications.perrinRiou`): Perrin-Riou Heegner-point IMC; `\uses{thm:thmA, prop:equiv-imc}`.
- `thm:thmB` (`MR4372220.Applications.pConverse`): p-converse to GZK; `\uses{cor:PR, def:iwasawa-algebra}`.
- `cor:thmB` (`MR4372220.Applications.pConverseCor`): mod-p corollary; `\uses{thm:thmB}`.
- `thm:thmC` (`MR4372220.Applications.bsdPPart`): p-part of BSD formula; `\uses{thm:thmA, thm:thmB, def:iwasawa-algebra}`.
- All blocks carry `% SOURCE:`, `% SOURCE QUOTE:`, `% SOURCE QUOTE PROOF:` citations from `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex`.
- Local macros defined via `\providecommand`: `\rH`, `\Fcal`, `\bQ`, `\bZ`, `\sha`, `\Lcal`.

## References consulted
- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex` (lines 2296–2374 for IMC section; 2384–2565 for p-converse; 2597–2663 for BSD; 207–384 for intro statements).

## Notes / Strategy
- `thm:howard-HP` and `mulambda` do not yet exist as blueprint labels (future chapters); leandag will report them as `unknown_uses` once `content.tex` is updated — expected, not a blocker.
- The chapter is NOT yet included in `content.tex` (per directive: content.tex changes are out of scope); plan agent must add `\input{chapters/Main_Conjecture_Applications}` to `content.tex`.
