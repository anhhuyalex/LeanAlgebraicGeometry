# Blueprint Writer Report: main-proofs
**Status:** COMPLETE

## Changes
- Added `\begin{proof}...\end{proof}` to `prop:premazur`: 4-step informal proof (auxiliary bounds, large points via `lem:vojtamumford`, small points via `prop:alg_pt_far` + ball-packing, general base point); `\uses{thm:ht_inequality_full,thm:nondeg_for_bd,lem:vojtamumford,prop:alg_pt_far}`.
- Added `\begin{proof}...\end{proof}` to `thm:bd_rat_intro`: Abel–Jacobi embedding, moduli-height comparison via `lem:moduli_height_comparison`, applies `thm:bd_fin_rank`; Northcott + Rémond handles low-height case; `\uses{thm:bd_fin_rank,lem:moduli_height_comparison}`.
- Added `\begin{proof}...\end{proof}` to `thm:bd_fin_rank`: lifts to fine moduli via Torelli, applies `prop:premazur` when height ≥ c₁, uses `lem:moduli_height_comparison` to convert `h(ι([Jac(C)]))` threshold; `\uses{prop:premazur,lem:moduli_height_comparison}`.
- Added `\begin{proof}...\end{proof}` to `thm:bd_tor_intro_nf`: rank-0 specialization of `thm:bd_fin_rank` with `Γ = Jac(C)(Q̄)_tors`, Northcott + Raynaud (Manin–Mumford) handles low-height case; `\uses{thm:bd_fin_rank,lem:moduli_height_comparison}`.
- Each proof preceded by `% SOURCE QUOTE PROOF:` verbatim from `RatPt.tex`.

## References consulted
- `references/MR4276287-mordell-lang-curves-source/RatPt.tex` — proofs of prop:premazur (lines 107–310), thm:bd_rat_intro (lines 314–392), thm:bd_fin_rank (lines 460–516), thm:bd_tor_intro_nf (lines 548–560).
- `references/MR4276287-mordell-lang-curves-source/intro.tex` — statement quotes for all four declarations.
- `references/MR4276287-mordell-lang-curves-source/DistanceCurve.tex` — prop:alg_pt_far structure used in premazur proof.
- `blueprint/src/chapters/MR4276287UniformityInMordellLangForCurves_Basic.tex` — verified all `\uses{}` labels exist.
