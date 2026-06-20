# Analogy: how to prove a complex in `X.Modules` is exact (Čech resolution)

## Mode
api-alignment

## Slug
stalkwise

## Iteration
052

## Question
What is the Mathlib-aligned way to prove `cechAugmentedComplex 𝒰 F` is exact (the Čech
nerve is a resolution of a quasi-coherent `F`) in `X.Modules = SheafOfModules X.ringCatSheaf`?
Stalk-reflection (forget to abelian sheaves → stalkwise) vs a sections-on-affines / basis detour.
Mathlib has **no** `SheafOfModules.stalk` functor and **no** "complex exact iff stalkwise exact".

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean:745` — `cechAugmentedComplex` (frozen-area; the complex whose exactness is needed).
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean:773` — `cech_computes_higherDirectImage` (FROZEN; Route A needs the resolution = exactness).
- `AlgebraicJacobian/Cohomology/CechAcyclic.lean:1848` — `sectionCech_affine_vanishing` (section homology = 0 over `D(f)`, p ≥ 1).
- `AlgebraicJacobian/Cohomology/CechAcyclic.lean:1868` — `sectionCech_homology_exact_of_localizationAway` (same for a subcover of a proper `D(f)`).
- `AlgebraicJacobian/Cohomology/HigherDirectImagePresheaf.lean:112` — `PresheafOfModules.homologyIsoSheafify` (**the keystone bridge**: module-sheaf homology = sheafify of presheaf homology).
- `AlgebraicJacobian/Cohomology/AffineSerreVanishing.lean:119/151/233/373` — `toSheaf_preservesFiniteColimits`, `toSheaf_preservesEpimorphisms`, `affine_surj_of_vanishing`, `affineCoverSystem` (the already-built `toSheaf`→AddCommGrp local-surjectivity + basis cover system).

## Decisions identified

### Decision A: the reflection backbone — `toSheaf` faithful, NOT a bespoke `SheafOfModules.stalk`

- **Mathlib idiom**: `CategoryTheory.Functor.reflects_exact_of_faithful`
  (`Mathlib.CategoryTheory.Abelian.Exact`):
  for abelian `C, D` and `F : C ⥤ D` with `[F.PreservesZeroMorphisms] [F.Faithful]`,
  `(S.map F).Exact → S.Exact` for any `S : ShortComplex C`. **Only faithfulness + zero-preservation
  are required** — no need for `F` to be exact. `SheafOfModules.toSheaf R` is `Faithful`
  (`SheafOfModules.instFaithfulSheafAddCommGrpCatToSheaf`) and `Additive`
  (`SheafOfModules.instAdditiveSheafAddCommGrpCatToSheaf` ⟹ `PreservesZeroMorphisms`). It is also
  `ReflectsIsomorphisms` and `ReflectsFiniteLimits`
  (`PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf`,
  `…instReflectsFiniteLimits…`). So `toSheaf` reflects exactness, isos, and zero objects for free.
- **Why Mathlib's shape works**: `toSheaf` lands in `TopCat.Sheaf AddCommGrp`, a *fixed* concrete
  abelian category — the varying-stalk-ring obstruction of `X.Modules` evaporates the moment you
  forget the module structure. You never construct a `SheafOfModules` stalk functor.
- **Project's path**: directive's sketch step (1) is correct and already partly used
  (`affine_surj_of_vanishing` forgets via `toSheaf`). The project's `toSheaf_preservesFiniteColimits`
  is NOT needed for the *reflection* (it was built for the epi/local-surjectivity argument).
- **Gap**: identical to Mathlib idiom.
- **Verdict**: ALIGN_WITH_MATHLIB — reflect through faithful `toSheaf`; do **not** build a
  `SheafOfModules.stalk` functor.

### Decision B: how to discharge exactness of the *underlying* complex — sections/sheafification, NOT stalks

- **Mathlib idiom (recommended)**: a sheaf-complex's homology is the **sheafification of the
  presheaf (section-level) homology**, and sheafification annihilates a presheaf that is **zero on a
  basis**. The two ingredients:
  1. `PresheafOfModules.homologyIsoSheafify` (PROJECT, `HigherDirectImagePresheaf.lean:112`):
     `K.homology i ≅ (sheafification α).obj ((forget K).homology i)`. Built from Mathlib's
     `Functor.mapHomologyIso'` + sheafification-is-exact. **This already does the reflection in the
     module category** — no `toSheaf`/stalk needed at this step.
  2. The W-equivalence / locally-bijective theory (`Mathlib.CategoryTheory.Sites.LocallyBijective`,
     `…/LocallySurjective`): `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`,
     `Presheaf.isLocallySurjective_presheafToSheaf_map_iff`,
     `GrothendieckTopology.WEqualsLocallyBijective` (instance available for `AddCommGrp` via
     `instWEqualsLocallyBijectiveOfHasWeakSheafify…`). A presheaf `P` whose sections vanish on a
     basis makes `0 ⟶ P` locally injective (trivially) and locally surjective (P locally zero), i.e.
     a `J.W` (W-equivalence), so `presheafToSheaf.map (0 ⟶ P)` is iso ⟹ `sheafify P ≅ sheafify 0 = 0`.
  3. The basis vanishing is **already proved**: `sectionCech_affine_vanishing`
     (+ `…_of_localizationAway`) gives presheaf-homology = 0 over every distinguished open `D(f)`
     (degrees ≥ 1); the distinguished opens are a basis (`affineCoverSystem`, `standard_cover_cofinal`).
- **Why this beats stalks here**: "sections are not exact in general" is irrelevant — sheafification
  only needs *local* vanishing, and the section Čech homology genuinely *does* vanish on the affine
  basis. The whole computation reuses the project's existing localization homotopies
  (`combHomotopy`/`depHomotopy`) at the section level; nothing new about stalks.
- **The stalk alternative (NOT recommended)**: would require building (i) "`stalkFunctor AddCommGrp x`
  is exact / preserves homology" (Mathlib has only the AB5/filtered-colimit ingredients, no packaged
  instance), (ii) "abelian sheaf = 0 iff all stalks = 0" (Mathlib has `mono_iff_stalk_mono`,
  `isIso_iff_stalkFunctor_map_iso`, `section_ext` — but **not** an exactness-of-complex criterion),
  and (iii) the explicit stalk contracting homotopy of the Čech complex. (i)+(ii) are a genuine
  gap-fill; (iii) is the same homotopy as the section one, only re-derived via colimit. Strictly more
  to build, with no reuse advantage.
- **Gap**: divergent-with-cost if the prover takes the stalk route (re-derives infrastructure the
  sheafification route already has); aligned if it takes the sections route.
- **Verdict**: PROCEED (sections/sheafification detour) — and AVOID the stalk route as a
  NEEDS_MATHLIB_GAP_FILL it doesn't have to incur.

## Recommendation

Prove `cechAugmented_exact` via **homology-sheaf-is-sheafify-of-presheaf-homology, zero on the affine
basis** — never build a `SheafOfModules` stalk functor and never fill the "exact iff stalkwise" gap.

Decomposition for a `mathlib-build` prover (rough LOC, lower-risk first):

1. **`cechAugmented_exact`** (the target): `∀ i, IsZero ((cechAugmentedComplex 𝒰 F).homology i)`
   ⟹ exact/`HomologicalComplex.Exact` (or the "is a resolution" packaging the frozen target consumes).
   Use `HomologicalComplex.exactAt_iff_isZero_homology` family. ~30–50 LOC.

2. **Sheafification kills basis-locally-zero homology**: from
   `homologyIsoSheafify`, `K.homology i ≅ sheafify((forget K).homology i)`. Show
   `0 ⟶ (forget K).homology i` is a `J.W` because each section over `D(f)` is `0`
   (locally surjective via the distinguished-open cover; locally injective trivially); conclude
   `sheafify(...) ≅ 0`. Lean on `Sheaf.isLocallyBijective_iff_isIso`,
   `isLocallySurjective_presheafToSheaf_map_iff`, the `WEqualsLocallyBijective AddCommGrp` instance,
   and the project's `affineCoverSystem`/`standard_cover_cofinal` for the covering. Reflect
   `IsZero` back to `X.Modules` with `toSheaf` faithful (`reflects_exact_of_faithful` family /
   `Faithful` reflects zero objects). ~80–120 LOC. **Highest-risk piece** (sheafification plumbing).

3. **Presheaf-homology = section Čech homology** over each open: identify
   `((forget (cechAugmentedComplex 𝒰 F))).homology i` evaluated on `U` with the
   `sectionCechComplex`-style homology, so step 2's input is exactly `sectionCech_affine_vanishing`.
   This is `mapHomologicalComplex`-vs-concrete-section plumbing — same diamond-prone flavor flagged in
   `[[keystone-tile-reconciliation-not-rfl]]` / `[[rR-semiring-diamond-change-workaround]]`. ~80–150 LOC.

4. **Augmentation node (degree 0)**: `sectionCech_affine_vanishing` covers degrees ≥ 1; the
   augmented complex also needs exactness at `F→C⁰` and at `C⁰` (`H⁰ = M_f`, the sheaf/equalizer
   condition) over `D(f)`. Build the `Function.Exact` for the first two nodes via
   `exact_of_isLocalized_span` (same engine as `combDifferential_exact`/`depDiff_exact`, applied to
   the augmentation row). ~60–100 LOC.

Total ≈ 250–420 LOC. Mathlib backbone: `reflects_exact_of_faithful`
(`Mathlib.CategoryTheory.Abelian.Exact`); `Sheaf.isLocallyBijective_iff_isIso`,
`isLocallySurjective_presheafToSheaf_map_iff`, `GrothendieckTopology.WEqualsLocallyBijective`
(`Mathlib.CategoryTheory.Sites.LocallyBijective` / `…/LocallySurjective`); `Functor.mapHomologyIso'`.
Project backbone: `PresheafOfModules.homologyIsoSheafify`, `sectionCech_affine_vanishing`,
`sectionCech_homology_exact_of_localizationAway`, `affineCoverSystem`, `standard_cover_cofinal`,
`toSheaf_preservesEpimorphisms`.
