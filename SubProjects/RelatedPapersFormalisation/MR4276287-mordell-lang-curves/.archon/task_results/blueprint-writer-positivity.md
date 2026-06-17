# Blueprint Writer Report: positivity
**Status:** COMPLETE (with notes below)

## Changes
- Created `blueprint/src/chapters/Positivity.tex` (new file, 5 declarations).
- Add `def:isNef` (`MR4276287UniformityInMordellLangForCurves.Positivity.isNef`): nef line bundle via deg(L|_C) ≥ 0. Project-bespoke (no source quote; HtIneq.tex uses the notion without defining it).
- Add `def:isBig` (`...Positivity.isBig`): big via h⁰ ~ c·m^n growth, Kodaira equivalence noted. Project-bespoke.
- Add `lem:nefIntersection` (`...Positivity.nefIntersection`): (L₁·…·L_d·H^{n-d}) ≥ 0 for nef bundles. `\uses{def:isNef}`. Project-bespoke with proof sketch.
- Add `thm:siuCriterion` (`...Positivity.siuCriterion`): Siu Theorem 2.2.15. `\uses{def:isNef, def:isBig, lem:nefIntersection}`. Source: HtIneq.tex §4 verbatim quote included.
- Add `lem:nefFromBetti` (`...Positivity.nefFromBetti`): F = O(0,1,1)|_{X̄_N} and M = O(0,0,1)|_{X̄_N} are nef. `\uses{def:isNef, lem:graph_construction}`. Source: HtIneq.tex §4 verbatim quotes included.
- `leandag build`: 0 unknown_uses, 0 isolated (existing blueprint unaffected).

## References consulted
- `references/MR4276287-mordell-lang-curves-source/HtIneq.tex` (opened, verbatim quotes for thm:siuCriterion and lem:nefFromBetti).

## Notes / Strategy
- **content.tex must be updated** to `\input{chapters/Positivity}` (plan agent; I cannot edit content.tex per directive).
- **Basic.tex prop:aux_ht_ineq** needs `\uses{thm:siuCriterion, lem:nefFromBetti}` added (plan agent; out of my write-domain).
- `thm:siuCriterion` proof verbatim (`% SOURCE QUOTE PROOF:`) unavailable: Lazarsfeld "Positivity in Algebraic Geometry I" not in `references/`; marked as citing the source with explanation. INCOMPLETE for verbatim proof only.
