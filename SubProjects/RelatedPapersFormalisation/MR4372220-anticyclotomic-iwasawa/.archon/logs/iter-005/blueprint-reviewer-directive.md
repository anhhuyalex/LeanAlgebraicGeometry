# Blueprint Reviewer Directive

## Slug
iter-005-blueprint

## Strategy snapshot

The project formalizes MR4372220 (Castella–Grossi–Lee–Skinner). The final goals are: thm:thmA (anticyclotomic Iwasawa main conjecture), cor:PR (Perrin-Riou), thm:thmB/cor:thmB (p-converse to GZK), thm:thmC (p-part of BSD formula).

### Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---:|---:|---|---|
| Local Iwasawa and Selmer foundations | ACTIVE | 2 | ~320-480 | PowerSeries, Submodule, exact sequences | Selmer conditions project-specific |
| Algebraic Iwasawa invariant comparison | ACTIVE | 1-2 | ~220-340 | torsion modules, char ideals, λ/μ wrappers | Depends on full Selmer setup |
| Analytic p-adic L-function comparison | ACTIVE | 1-2 | ~240-360 | involution on Λ, power series evaluation | BDP/Katz/Kriz source-heavy |
| Howard abstract Selmer-group bound | ACTIVE | 3 | ~220-360 | fg modules over local rings, length inequalities | def:selmer-triple sorry-backed; thm:Zp-twisted sub-split needed |
| Heegner-point Kolyvagin system construction | ACTIVE | 2-3 | ~200-320 | Kolyvagin systems, norm relations, Cornut-Vatsal | thm:howard-HPKS, thm:howard-HP |
| Main anticyclotomic conjecture / Perrin-Riou | ACTIVE | 1-2 | ~120-200 | char-ideal divisibility | prop:equiv-imc, thm:thmA, cor:PR |
| p-converse to Gross-Zagier-Kolyvagin | ACTIVE | 1-2 | ~120-200 | control theorem, rank/parity | thm:thmB, cor:thmB — independent lane |
| BSD rank-one formula | ACTIVE | 1-2 | ~140-240 | control theorem, GZ height/regulator | thm:thmC — independent lane |

## Routes

Single route: Greenberg-Vatsal style comparison route. Algebraic and analytic comparison lanes are independent once Local foundations are in place. BSD and p-converse are independent downstream lanes once thm:thmA is proved.

## References

- `references/MR4372220-anticyclotomic-iwasawa-source/Eisenstein.tex` — main source for all chapters (all % SOURCE: citations point here)
- `references/MR4372220-anticyclotomic-iwasawa.pdf` — PDF backup

## Focus areas

Pay extra attention to:
1. Whether the iter-004 must-fix items were properly resolved: def:char-ideal (Local), lem:cebotarev-kolyvagin + lem:kolyvagin-inductive-step (Howard), def:bdp-class + thm:control-jsw + thm:padic-gz (Applications), \uses{} fixes for prop:equiv-imc and thm:thmC, cor:lambda-E \uses{lem:local-char-wp}, cor:Kriz \uses{thm:Katz}
2. The \uses{} dependency graph correctness — especially the cross-chapter edge from thm:mu-zero-theta to thm:Katz (Hida μ=0)
3. Undefined macros: \llbracket, \rrbracket, \mathds — were they added to macros/common.tex?

## Known issues

- % archon:covers references point to Lean files that do not yet exist (Local.lean, Algebraic.lean, Analytic.lean, Howard.lean, Applications.lean). This is expected — those files will be created in the autoformalize phase. Do NOT flag as a must-fix unless there is a structural/routing issue beyond the missing files.
- All 33 \lean{} references are currently unmatched (no Lean declarations exist yet). This is expected at the pre-autoformalize stage. Not a blueprint defect.
