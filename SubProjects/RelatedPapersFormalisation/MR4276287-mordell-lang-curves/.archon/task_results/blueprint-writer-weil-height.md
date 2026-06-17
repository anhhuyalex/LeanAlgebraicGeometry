# Blueprint Writer Report: weil-height
**Status:** COMPLETE

## Changes
- Created `blueprint/src/chapters/WeilHeight.tex` with 6 declaration blocks.
- Add `thm:weil_height_mathlib` (`Mathlib.NumberTheory.Heights.weilHeight`): Mathlib anchor, `\mathlibok`; Weil height on \PP^n with Northcott + height machine. Comment `% [verify Mathlib name]` added.
- Add `lem:northcott_ht` (`WeilHeight.northcottHeight`): project stub; Northcott finiteness; `\uses{thm:weil_height_mathlib}`; cited from SetUpHtIneq.tex.
- Add `def:height_fib` (`WeilHeight.fiberwiseHeight`): naive height h(P)+h(π(P)); `\uses{thm:weil_height_mathlib, def:ambient_setup}`; cited from SetUpHtIneq.tex.
- Add `def:nt_height` (`WeilHeight.neronTateHeight`): limit h([N]P)/N²; `\uses{def:height_fib, def:ambient_setup}`; cited from silvermantate.tex.
- Add `prop:nt_quadratic` (`WeilHeight.ntQuadratic`): h([N]P)=N²h(P); `\uses{def:nt_height}`; cited from SetUpHtIneq.tex + NTbase.tex.
- Add `prop:nt_nonneg` (`WeilHeight.ntNonneg`): ≥0, =0 iff torsion; `\uses{def:nt_height}`; proof uses `prop:nt_quadratic, lem:northcott_ht, thm:silverman_tate`; cited from SetUpHtIneq.tex.

## Notes / Strategy
- **content.tex must be updated**: add `\input{chapters/WeilHeight}` after `\input{chapters/MR4276287UniformityInMordellLangForCurves_Basic}`; leandag will not see the new nodes until then (0 isolated, 0 unknown_uses in current graph — correct since the file is not yet `\input{}`'d).
- `thm:silverman_tate` in Basic.tex should gain `\uses{def:nt_height, def:height_fib}` (directive says "to be wired up" — outside this chapter's write-domain).

## References consulted
- `references/MR4276287-mordell-lang-curves-source/silvermantate.tex`
- `references/MR4276287-mordell-lang-curves-source/SetUpHtIneq.tex`
- `references/MR4276287-mordell-lang-curves-source/NTbase.tex`
- `blueprint/src/chapters/MR4276287UniformityInMordellLangForCurves_Basic.tex`
