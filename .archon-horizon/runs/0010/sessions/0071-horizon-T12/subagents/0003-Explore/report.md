You are scouting an in-project Lean 4 codebase. Working directory: /home/Axel/LeanAlgebraicGeometry-Horizon/MainProjects/Algebraic-Jacobian-Challenge.

Report verbatim source (with line numbers) from AlgebraicJacobian/Picard/GenericFlatnessGeometric.lean and AlgebraicJacobian/Picard/FlatteningStratification.lean for:

1. GenericFlatnessGeometric.lean lines ~90–200: the helper lemmas at the top of the file, especially anything about `appLE` module structures "agreeing definitionally", `Module.Flat.of_isLocalizedModule_algebra`, and any lemma bridging `Module.compHom` structures (e.g. transporting Module.Flat across an equality of ring homs or across `𝟙`-appLE). Copy the declarations.
2. `coherentSheafFlat_of_iso` (line ~1077) — the FULL proof body: how does it transport `Module.Flat` across an isomorphism of modules `G ≅ G'`? What bridging lemmas does it use (names)?
3. `coherentSheafFlat_of_comp_isIso` (line ~1434) — full statement and the key transport steps in its body.
4. `flat_section_pullback_piece` (line ~748) and `isPushout_appLE_pullback_piece` (line ~733) — full statements only (not bodies).
5. Any use in the project of `pullback_app_isoTensor_baseMap_sectionLinearEquiv` or `pullback_app_isoTensor_baseMap_isBaseChange` OUTSIDE QuotScheme.lean (grep the whole AlgebraicJacobian/ tree): report each call site with ~30 lines of surrounding context showing exactly how the letI instances are set up when consuming it.
6. In QuotScheme.lean: the final public statement `pullback_app_isoTensor` (a def/theorem near the end of the file, approximately lines 5090–5200, possibly private `pullback_app_isoTensor_baseMap_isBaseChange` then a public wrapper). Copy verbatim the statements (not proofs) of `pullback_app_isoTensor_baseMap_isBaseChange` and any public `pullback_app_isoTensor` wrapper, plus `pullback_app_isoTensor_baseMap` (line ~508) and `pullback_app_isoTensor_baseMap_sectionLinearEquiv` (line ~4800).
7. Grep for `IsQuasicoherent` instances for pullback: `pullback_isQuasicoherent_hom` in AlgebraicJacobian/Cohomology/PullbackQuasicoherent.lean — exact statement, and whether it is an instance or a lemma (how consumers register it, find one example use).
8. Grep GenericFlatnessGeometric.lean for how `CoherentSheafFlat (𝟙 _)` hypotheses/conclusions are MANIPULATED: find every place where the compHom module structure of `(𝟙 X).appLE` is bridged to a natural module structure or to restriction maps; copy those proof fragments.
9. In `AlgebraicJacobian/Picard/EntryIdeal.lean` lines 406–634: the Nakayama prolongation section — copy verbatim ALL declarations (statements only) from line 406 to end of file, especially `exists_matrixPresentation_of_isLocalizedModule` (line ~470).

Return raw data organized by item number, verbatim code blocks with line numbers.
