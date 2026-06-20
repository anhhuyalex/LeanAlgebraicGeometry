# Analogy: does `SheafOfModules.toSheaf` preserve epimorphisms (and does Mathlib supply it)?

## Mode
api-alignment

## Slug
tosheaf-epi

## Iteration
033

## Question
We need `AlgebraicGeometry.toSheaf_preservesEpimorphisms`: the forgetful functor
`SheafOfModules.toSheaf R : SheafOfModules R ⥤ Sheaf J AddCommGrpCat` preserves epis, so that
`Epi g` in `X.Modules` yields local section surjectivity via `Sheaf.isLocallySurjective_iff_epi'`.
Resolve whether Mathlib already supplies this (or a near-equivalent) and the cleanest aligned route.

## Project artifact(s)
- Target name `AlgebraicGeometry.toSheaf_preservesEpimorphisms` (not yet built); consumer is the
  `Epi g ⟹ IsLocallySurjective (toSheaf g)` step feeding `surj_of_vanishing` / `ses_cech`.

## What Mathlib ships (verified)

`SheafOfModules.toSheaf R` lives in `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean`. Instances:

- `Faithful`, `Additive`  (`…/ModuleCat/Sheaf.lean`).
- `PreservesFiniteLimits (toSheaf R)`  (`…/ModuleCat/Sheaf/Limits.lean:118`).
- `ReflectsFiniteLimits (toSheaf R)`, `ReflectsIsomorphisms (toSheaf R)`
  (`…/ModuleCat/Presheaf/Sheafification.lean`).
- `Abelian (SheafOfModules R)`  (`…/ModuleCat/Sheaf/Abelian.lean:40`, under
  `HasSheafify J AddCommGrpCat` + `J.WEqualsLocallyBijective AddCommGrpCat`) — so it is **balanced**.
- `HasColimitsOfShape K (SheafOfModules R)` from the presheaf side
  (`…/ModuleCat/Sheaf/Colimits.lean:32`).

**NOT shipped (confirmed by exhaustive grep of `Mathlib/Algebra/Category/ModuleCat/`):**
no `PreservesEpimorphisms`, no `PreservesColimit(sOfShape/OfSize)`, no `PreservesFiniteColimits`,
no exactness/`PreservesHomology` for `toSheaf R`. The colimit/epi side is a genuine Mathlib gap.

## The crux: why the limit-side proof does NOT dualize

`PreservesFiniteLimits (toSheaf R)` is proved (`Limits.lean:118-119`) by

```
preservesFiniteLimits_of_reflects_of_preserves (toSheaf R) (sheafToPresheaf _ _)
```

using `toSheaf ⋙ sheafToPresheaf ≅ forget ⋙ toPresheaf` (`toSheafCompSheafToPresheafIso`) and the
fact that **`forget : SheafOfModules R ⥤ PresheafOfModules R.obj` is a RIGHT adjoint** (right
adjoint of `sheafification (𝟙 R.obj)`), hence preserves *limits*. The colimit dual is dead at
exactly this spot: `forget` is a right adjoint and does **not** preserve colimits/epis. This is
the same wall the prover hit (failed approach 4: `toSheaf ≅ (forget ⋙ toPresheaf) ⋙ presheafToSheaf`
exists but `forget` kills epi-preservation). **Epimorphisms in `SheafOfModules R` are "local"
(locally surjective) and are NOT preserved by `forget` into presheaves — that is the entire
mathematical content, and no factorization through `forget` can capture it.**

## Decisions identified

### Decision: Is `toSheaf_preservesEpimorphisms` a missed instance or a real build?

- **Mathlib idiom**: epi-preservation for a functor out of an abelian category is obtained either
  (a) from `PreservesColimitsOfShape WalkingSpan` via
  `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`
  (`…/Limits/Constructions/EpiMono.lean:62`), or (b) from exactness via
  `CategoryTheory.Abelian.preservesEpimorphisms_of_map_exact` (`…/Abelian/Exact.lean:255`). The
  Mathlib-aligned object is therefore `PreservesFiniteColimits (toSheaf R)` (the missing dual of
  `Limits.lean`), from which epi-preservation is a one-liner.
- **Project's path**: none yet; prover tried only to *derive* epi-preservation from existing
  instances (all circular or blocked).
- **Gap**: `NEEDS_MATHLIB_GAP_FILL`. Mathlib does not have it; it must be built. It is **not** a
  one-instance miss — all four prover attempts correctly fail for structural reasons.
- **Cost of divergence**: n/a (no parallel API exists); the cost is the build itself (one lemma,
  ~80–150 LOC), all of whose dependencies are already in Mathlib.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

## Recommended build (Route A) — `PreservesFiniteColimits (toSheaf R)` then epi

Mirror `Colimits.lean`/`Limits.lean` but route through the **sheafification square**, not through
`forget`. Set `L := PresheafOfModules.sheafification (𝟙 R.obj) : PresheafOfModules R.obj ⥤ SheafOfModules R`
(a **left** adjoint and a localization). All ingredients exist:

1. Square iso `PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)`:
   `L ⋙ toSheaf R ≅ toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat`
   (`…/ModuleCat/Presheaf/Sheafification.lean`, see also `sheafificationCompToSheaf`).
2. `PreservesFiniteColimits (toPresheaf R.obj)` (`…/ModuleCat/Presheaf/Colimits.lean:157`;
   `PreservesColimitsOfSize` at :171).
3. `presheafToSheaf J AddCommGrpCat` is left adjoint (`sheafificationAdjunction`), so
   `PreservesColimitsOfSize` via `Adjunction.leftAdjoint_preservesColimits`
   (`…/Adjunction/Limits.lean:88`). ⇒ `L ⋙ toSheaf` preserves finite colimits (1+2+3).
4. `L` is left adjoint ⇒ `PreservesColimits L` (same `leftAdjoint_preservesColimits`); and its
   counit is an iso (used in `Abelian.lean:42`, `Colimits.lean:37`).
5. Per-diagram computation from `Colimits.lean:34-38`: for `F : K ⥤ SheafOfModules R`,
   `F ≅ (F ⋙ forget R) ⋙ L`. So `colimit F ≅ L (colimit (F ⋙ forget R))`, and applying the
   colimit-preserving `L ⋙ toSheaf` (step 3) shows `toSheaf` carries the colimit cocone of `F`
   to a colimit cocone. Package with `preservesColimit_of_natIso`
   (`…/Limits/Preserves/Basic.lean:280`) / `preservesFiniteColimits_of_natIso`
   (`…/Limits/Preserves/Finite.lean:248`).
6. `instance : PreservesEpimorphisms (toSheaf R)` from step-5 result via
   `preservesEpimorphisms_of_preservesColimitsOfShape` (WalkingSpan is finite).

Hypotheses needed (same as `Abelian.lean`/`Colimits.lean`, all available in the scheme setting):
`HasWeakSheafify J AddCommGrpCat` (or `HasSheafify`) and `J.WEqualsLocallyBijective AddCommGrpCat`.

Then the downstream consumer: `Epi g` ⟹ `Epi (toSheaf g)` (the new instance) ⟹
`IsLocallySurjective (toSheaf g)` via `Sheaf.isLocallySurjective_iff_epi'.mpr`
(`…/Sites/EpiMono.lean:123`). NB its `[Balanced (Sheaf J A)]` arg comes from `Sheaf J AddCommGrpCat`
being abelian; supply it in **term mode** (`(isLocallySurjective_iff_epi' _).mpr inferInstance`) to
dodge the `rw`-time synthesis failure the prover saw (failed approach 2).

### Secondary routes
- **Route B (exactness)**: prove `toSheaf` maps short exact → exact, then
  `Abelian.preservesEpimorphisms_of_map_exact` (`…/Abelian/Exact.lean:255`). Equivalent content to
  Route A's cokernel preservation; no savings, and less reusable than `PreservesFiniteColimits`.
- **Route C (localization transfer)**: `L.IsLocalization (J.W.inverseImage (toPresheaf R₀))` exists
  (`…/ModuleCat/Sheaf/Localization.lean:48`), but `Mathlib/CategoryTheory/Localization/` has **no**
  colimit-preservation transfer lemma. No shortcut today; would itself be a Mathlib gap-fill.

## Recommendation
Build `PreservesFiniteColimits (SheafOfModules.toSheaf R)` via Route A (the missing dual of
`Limits.lean`, routed through `sheafificationCompToSheaf` + the left-adjoint reflector `L`, never
through `forget`), then get `toSheaf_preservesEpimorphisms` as a one-line corollary. This is a
genuine but bounded single-lemma project build with every dependency already in Mathlib; it is
also a clean upstreamable contribution. Do **not** keep hunting for an existing instance or a
`forget`-based factorization — both are structurally impossible.
