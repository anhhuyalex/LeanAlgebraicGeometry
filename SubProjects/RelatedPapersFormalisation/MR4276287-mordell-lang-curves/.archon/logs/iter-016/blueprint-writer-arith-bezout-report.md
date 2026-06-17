# Blueprint Writer Report: arith-bezout
**Status:** COMPLETE (with two known open citations noted below)

## Changes
- Created `blueprint/src/chapters/ArithBezout.tex` (new file, 4 declaration blocks):
  - `thm:arith_bezout` (`...ArithBezout.arithBezout`): Autissier arithmetic Bézout, sorry stub; `\uses{def:ambient_setup}`.
  - `lem:bihomog_degree` (`...ArithBezout.bihomogDegree`): Bihomogeneous degree bound for `[N]`; `\uses{lem:graph_construction}`; proof sketch with recurrence computation from HtIneq.tex.
  - `lem:siu_intersection_lower` (`...ArithBezout.siuIntersectionLower`): lower bound `(F^d) ≥ κN^{2d}`; `\uses{prop:betti_form, lem:graph_construction, def:nef}`; proof sketch from prop:intersectionlb in HtIneq.tex.
  - `lem:siu_intersection_upper` (`...ArithBezout.siuIntersectionUpper`): upper bound `(M·F^{d-1}) ≤ cN^{2(d-1)}`; `\uses{lem:bihomog_degree, lem:graph_construction, def:nef}`; proof sketch from prop:intersectionub in HtIneq.tex.

## References consulted
- `references/MR4276287-mordell-lang-curves-source/HtIneq.tex` (prop:intersectionlb + prop:intersectionub, degree computation)
- `references/MR4276287-mordell-lang-curves-source/SettingUp.tex` (Arithmetic Bézout citation locus)

## Notes / Strategy
- **`content.tex` must be updated**: add `\input{chapters/ArithBezout}` — cannot edit it per write-domain rules.
- **`thm:arith_bezout` verbatim not retrieved**: `[Théorème 3]{HauteursAlt3}` (Autissier) is not in `references/`; block marked `(verbatim text not yet retrieved)`. Dispatch `reference-retriever` for Autissier's paper if the exact statement is needed.
- **`def:nef` undefined**: `lem:siu_intersection_lower` and `lem:siu_intersection_upper` declare `\uses{def:nef}`, which belongs in a `Positivity.tex` chapter that does not yet exist. Once `ArithBezout.tex` is `\input`-ed, leandag will report these as `unknown_uses`. Create `def:nef` in `Positivity.tex` before next prover work.
- **`prop:aux_ht_ineq` in Basic.tex** should have its `\uses{}` extended to include `lem:siu_intersection_lower, lem:siu_intersection_upper, thm:siu_criterion, thm:arith_bezout`. Cannot edit Basic.tex; plan agent must wire this up.
- **`thm:siu_criterion`** is referenced in the `prop:aux_ht_ineq` update note but is not defined anywhere; plan agent should create it (likely in a Positivity or SiuCriterion chapter).
- leandag currently sees 0 unknown_uses / 0 isolated because `ArithBezout.tex` is not yet `\input`-ed into `web.tex`/`content.tex`.
