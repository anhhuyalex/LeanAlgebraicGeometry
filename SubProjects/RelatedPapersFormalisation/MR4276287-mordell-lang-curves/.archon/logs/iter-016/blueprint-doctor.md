# Blueprint Doctor

## Chapter coverage problems (`% archon:covers`)

A chapter's `% archon:covers <file> ...` declaration tells the prover-dispatch gate which Lean files that chapter blueprints. The issues below would route the gate to the wrong chapter — fix the declaration (correct the path, or make exactly one chapter own each file).

- chapter `ArithBezout.tex` covers `MR4276287UniformityInMordellLangForCurves/ArithBezout.lean`, which does not exist
- chapter `Jacobian.tex` covers `MR4276287UniformityInMordellLangForCurves/Jacobian.lean`, which does not exist
- chapter `ModuliSpace.tex` covers `MR4276287UniformityInMordellLangForCurves/ModuliSpace.lean`, which does not exist
- chapter `Positivity.tex` covers `MR4276287UniformityInMordellLangForCurves/Positivity.lean`, which does not exist
- chapter `Torelli.tex` covers `MR4276287UniformityInMordellLangForCurves/Torelli.lean`, which does not exist
- chapter `WeilHeight.tex` covers `MR4276287UniformityInMordellLangForCurves/WeilHeight.lean`, which does not exist

## Malformed annotations

Annotations with an empty argument (`\uses{}`, `\proves{}`, `\label{}`, `\ref{}`, ...) or an empty list item (`\uses{a,,b}`, `\uses{a,}`). plastex emits `Label '' could not be resolved` for each of these and then the leanblueprint depgraph builder enters infinite recursion (`RecursionError`), so the blueprint never finishes building. Fix each one by either filling in the intended label or deleting the empty annotation. Do NOT defer — the next `leanblueprint web` run will crash until these are resolved.

### `blueprint/src/chapters/Torelli.tex`
- `\undefined-macro{...}` — \xymatrix is used but defined nowhere (macros/*.tex or a chapter-local \providecommand) — define it or fix the typo

