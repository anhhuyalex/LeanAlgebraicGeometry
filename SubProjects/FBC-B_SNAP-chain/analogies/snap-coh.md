# Analogy: Mac Lane coherence for the sheaf tensor product by monoidal-localization transfer

## Mode
api-alignment

## Slug
snap-coh

## Iteration
004

## Question
Is there a Mathlib idiom to obtain triangle/pentagon/hexagon/`β_{𝟙,𝟙}=𝟙` for the hand-built
`tensorObjAssoc`/`tensorObjUnitIso`/`tensorObjRightUnitor`/`tensorBraiding` on `X.Modules` by
TRANSFER from `PresheafOfModules.monoidalCategory` through sheafification (a reflective/monoidal
localization), rather than hand-proving each Mac Lane law? And what is the Mathlib name for
`β_{𝟙_C,𝟙_C} = 𝟙`?

## Project artifact(s)
- SectionGradedRing.lean:78 — `sheafification := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)`
- SectionGradedRing.lean:87 — `MonoidalPresheaf X := X.PresheafOfModules` (carries `PresheafOfModules.monoidalCategory`, real symmetric monoidal)
- SectionGradedRing.lean:142/155/168/1317 — hand-built unitor/braiding/right-unitor/associator
- SectionGradedRing.lean:1123 — `ztensor_whisker_localIso` (whiskering preserves `J.W`)
- SectionGradedRing.lean:1248 — `isIso_sheafification_whiskerRight_unit` (strong-monoidality μ comparison)
- SectionGradedRing.lean:1814/1843/1864/1878/1937 — the 5 SNAP coherence sorries

## Decisions identified

### Decision: how to obtain Mac Lane coherence on the localized (sheaf) tensor product

- **Mathlib idiom**: `CategoryTheory.Localization.Monoidal` (Joël Riou, Dagur Asgeirsson).
  Cite:
  - `Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean`:
    - `MorphismProperty.IsMonoidal` (L44) — `W` multiplicative + `whiskerLeft`/`whiskerRight`-stable; `.mk'` (L50) from tensorHom-stability.
    - `LocalizedMonoidal L W ε` (L86) — **type synonym** of the localized category `D`, given `[W.IsMonoidal] [L.IsLocalization W] (ε : L.obj (𝟙_ C) ≅ unit)`.
    - `instance MonoidalCategoryStruct (LocalizedMonoidal L W ε)` (L172) + `pentagon` (L329), `triangle` (L412), `leftUnitor`/`rightUnitor`/`associator` (L150/157/164) ⇒ a **full `MonoidalCategory` instance** on the synonym.
    - `μ X Y : L'.obj X ⊗ L'.obj Y ≅ L'.obj (X ⊗ Y)` (L184) — the strong-monoidality comparison iso, = the project's `isIso_sheafification_whiskerRight_unit`-based comparison, packaged. `associator_hom_app` (L234), `leftUnitor_hom_app` (L212), `rightUnitor_hom_app` (L223), `μ_natural_left/right` (L188/200).
  - `Mathlib/CategoryTheory/Localization/Monoidal/Braided.lean`:
    - `instance BraidedCategory (LocalizedMonoidal L W ε)` (L118, hexagon from `map_hexagon_forward/reverse`); `SymmetricCategory` (L141) when `C` symmetric; `(toMonoidalCategory L W ε).Braided` (L132); `β_hom_app` (L125).
  - `Mathlib/CategoryTheory/Localization/Monoidal/Functor.lean`: `functorMonoidalOfComp` (L130) — the localization functor is monoidal.
  Why Mathlib chose it: a localization at a monoidal-compatible class is monoidal and the localization
  functor is (strong) monoidal; pentagon/triangle/hexagon are proved ONCE generically. Crucially the
  structure lives on the **type synonym** `LocalizedMonoidal L W ε`, NOT on `D` itself — this is the
  deliberate Mathlib dodge of the very instance/diamond clash the project hit putting `MonoidalCategory`
  on `X.Modules` directly.

- **Project's current path**: hand-built `tensorObjAssoc` as a 5-segment composite of `μ`-comparison
  isos + sheafified presheaf associator/braiding, with the intent of HAND-PROVING triangle/pentagon/
  hexagon/`β_{𝟙𝟙}=𝟙` for it (estimated multi-hundred LOC).

- **Gap**: divergent-with-cost. Re-derives, by hand, exactly what `Localization.Monoidal.Basic.pentagon`
  / `.triangle` / `Braided.hexagon_forward` prove generically for every monoidal localization.

- **All preconditions are present or already proven in-project**:
  - `[L.IsLocalization W]` for `L = sheafification`, `W = J.W.inverseImage (toPresheaf R₀)`: **already a
    Mathlib instance** — `Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean`:48
    (`(sheafification α).IsLocalization (J.W.inverseImage (toPresheaf R₀))`); the project's
    `isIso_sheafification_map_iff` is a specialization of L39 in that file. `sheafification` here is
    literally `PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)`.
  - `C = X.PresheafOfModules` symmetric monoidal: `PresheafOfModules.monoidalCategory` (Mathlib).
  - `[W.IsMonoidal]`: **content already proven in-project.** `whiskerRight` field IS
    `ztensor_whisker_localIso` (SectionGradedRing.lean:1123) rephrased through `inverseImage_iff`
    (`W f ↔ J.W ((toPresheaf).map f)`, and the lemma gives `W f → W (f ▷ R)`). `whiskerLeft` follows by
    braiding-conjugation (C symmetric) or the symmetric coequalizer argument. Multiplicative: `J.W`
    multiplicative + `inverseImage` preserves it.
  - `ε : sheafification.obj (𝟙_ C) ≅ unitModule X`: trivial (unit comparison).

- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision: Mathlib name for `β_{𝟙,𝟙} = 𝟙`

- **Mathlib idiom**: no single named lemma, but a two-step one-liner.
  `braiding_tensorUnit_left (X) : (β_ (𝟙_C) X).hom = (λ_ X).hom ≫ (ρ_ X).inv`
  (`Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean`:333; also `braiding_tensorUnit_right` L352).
  At `X = 𝟙_C`, compose with `unitors_equal : (λ_ (𝟙_C)).hom = (ρ_ (𝟙_C)).hom`
  (`Mathlib/CategoryTheory/Monoidal/CoherenceLemmas.lean`:58) ⇒ `(β_ 𝟙 𝟙).hom = 𝟙`.
  Related: `braiding_leftUnitor` (L301), `braiding_rightUnitor` (L329).
- **Verdict**: PROCEED (use `braiding_tensorUnit_left` + `unitors_equal`; in `LocalizedMonoidal`,
  derived from the synonym's `SymmetricCategory` instance).

## Recommendation
Switch the next SNAP prover round to **`mathlib-build`**: instantiate `LocalizedMonoidal sheafification
W ε` (a type synonym of `X.Modules`), discharging the one new precondition `(J.W.inverseImage (toPresheaf
R₀)).IsMonoidal` from `ztensor_whisker_localIso` (whiskerRight) + braiding (whiskerLeft) + `J.W`
multiplicativity. Then the synonym is `SymmetricCategory` and the localization functor is symmetric
monoidal, so triangle/pentagon/hexagon/`β_{𝟙𝟙}=𝟙` are `MonoidalCategory.pentagon`/`triangle`,
`BraidedCategory.hexagon_forward`, `braiding_tensorUnit_left`+`unitors_equal` — NOT hand-proved.
Two integration options for the 5 sorries: (A, cleanest) redefine `tensorObj`/`tensorObjAssoc`/
`tensorBraiding`/unitors AS the synonym's `⊗`/`α`/`β`/`λ`/`ρ` so coherences are literally Mathlib
lemmas; (B, less invasive) keep the hand-built defs and prove each equals the synonym's structure map
via `associator_hom_app`/`leftUnitor_hom_app`/`β_hom_app` + `μ_natural_left/right`, then transfer. Either
is far below the multi-hundred-LOC hand-proof. NOTE: this SUPERSEDES the iter-050 `snap-route.md`
dismissal of `LocalizedMonoidal` ("needs `W.IsMonoidal` ⇒ wants `MonoidalClosed (PresheafOfModules)` —
ABSENT") — that blocker was discharged by the project's own iter-066 `ztensor_whisker_localIso`, which
proves whiskering-preserves-`W` WITHOUT `MonoidalClosed` (via the abelian coequalizer-presentation
route). See [[snap-route]], [[snap-assoc]], [[snap-gcomm]].
