# Analogy: monoidal structure / associator on `X.Modules` via sheafification

## Mode
api-alignment

## Slug
tensorobjassoc

## Iteration
007

## Question
Is the double-braiding `tensorObjAssoc` the right idiom, or does Mathlib provide a
monoidal-transport / monoidal-localization API giving (a) a *canonical* sheaf-level
associator with pentagon+triangle inherited from the presheaf level, and/or (b) a
transport of the entire monoidal structure from `MonoidalPresheaf X` onto `X.Modules`?

## Project artifact(s)
- `SectionGradedRing.lean:1610–1653` — `tensorObjAssoc`: seg1 `(η▷)⁻¹ ≫ α^# ≫` **double-braiding detour** `β^# ≫ (η▷)^# ≫ β^#`.
- `SectionGradedRing.lean:1541–1546` — `isIso_sheafification_whiskerRight_unit` (only whisker-crux, axiom-clean).
- `SectionGradedRing.lean:1416–1494` — `ztensor_whisker_localIso` (the reusable brick: arbitrary `f` with `(toPresheaf).map f ∈ J.W` ⇒ `f ▷ R` likewise).
- `SectionGradedRing.lean:149–177` — clean single-segment unitors/braiding.

## Decisions identified

### Decision: build coherent monoidal structure on `X.Modules` iso-by-iso vs. transport it via monoidal localization

- **Mathlib idiom**: **monoidal localization.** A monoidal category `C` with a morphism
  class `W` satisfying `MorphismProperty.IsMonoidal` (multiplicative + stable under
  left/right whiskering) and a localization functor `L : C ⥤ D` for `W` yields a FULL
  monoidal structure on `D` — associator, unitors, **pentagon, triangle** — with `L`
  strong-monoidal, all inherited.
  Cite:
  - `MorphismProperty.IsMonoidal` (class, two fields `whiskerLeft`/`whiskerRight`) —
    `Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean:44`; builder `IsMonoidal.mk'` L50.
  - `LocalizedMonoidal` type synonym + `associator` L165, `leftUnitor` L151,
    `rightUnitor` L158, `monoidalCategoryStruct` L172, strong-monoidal comparison
    `μ (X Y) : L.obj X ⊗ L.obj Y ≅ L.obj (X ⊗ Y)` L184 — same file.
  - Braided/symmetric transport: `Mathlib/CategoryTheory/Localization/Monoidal/Braided.lean`
    (gives `BraidedCategory`/`SymmetricCategory` ⇒ **hexagon** inherited).
  - End-to-end precedent for SHEAVES: `Sheaf.monoidalCategory`
    `Mathlib/CategoryTheory/Sites/Monoidal.lean:165` (`= LocalizedMonoidal (presheafToSheaf J A) J.W (Iso.refl _)`),
    `Sheaf.braidedCategory` L174, `Sheaf.symmetricCategory` L182,
    `presheafToSheaf … .Monoidal` instance L189.
  - **The module case is already a localization**:
    `(PresheafOfModules.sheafification α).IsLocalization (J.W.inverseImage (toPresheaf R₀))`
    — `Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean:48`
    (with `inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` L38). The project's
    `sheafification` is exactly this with `α = 𝟙 X.ringCatSheaf.obj`.
  - `MonoidalPresheaf X` is **symmetric monoidal**:
    `PresheafOfModules.symmetricCategory` `…/Presheaf/Monoidal.lean:144` (`monoidalCategory` L125).

- **Project's current path**: hand-rolls `tensorObj`, then `tensorObjUnitIso`/`tensorObjRightUnitor`/
  `tensorBraiding`/`tensorObjAssoc` iso-by-iso, and intends to prove pentagon/triangle/hexagon
  by induction for three SNAP sorries. `tensorObjAssoc` inserts a **double-braiding detour**
  to convert a needed `whiskerLeft` into the available `whiskerRight` crux.

- **Gap**: **divergent-with-cost.** The needed transport machinery exists and module
  sheafification is *already proven* to be the localization functor; the ONLY missing input
  is the typeclass `(J.W.inverseImage (toPresheaf R₀)).IsMonoidal`. The hand-rolled associator
  is non-canonical (auditor's worry is real: the double braiding `β_{a,b⊗c}^# ≫ (η▷)^# ≫ β_{(b⊗c)^#,a}^#`
  need not equal the Mac Lane associator on the nose — the unit sits *between* two braidings on
  *different* objects so they do not collapse), so the planned coherence inductions are both
  expensive and at risk of being unprovable as built.

- **Cost of divergence**: the three SNAP coherences (`tensorPowAdd_zero_right` succ,
  `sectionsMul_mul_assoc`, `sectionsMul_mul_comm`) become hand inductions over a possibly
  non-canonical associator; if the auditor is right, unprovable ⇒ wasted prover budget.
  Under the idiom they are *inherited* from the `MonoidalCategory`/`SymmetricCategory` instance.

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (small, well-scoped) → then **ALIGN_WITH_MATHLIB**.

### Decision: braiding-free associator via a `whiskerLeft` crux lemma (the directive's fix candidate)

- **Mathlib idiom**: the `whiskerLeft` field is a first-class citizen.
  - At the SHEAF level Mathlib proves it directly: `GrothendieckTopology.W.whiskerLeft`
    `…/Sites/Monoidal.lean:132` (`J.W g ⇒ J.W (F ◁ g)`, via `functorEnrichedHom`, needs
    `MonoidalClosed A`), and *derives* `whiskerRight` from it by braiding conjugation
    `…/Sites/Monoidal.lean:144` (`arrow_mk_iso_iff (Arrow.isoMk (β_ ..) (β_ ..))`).
- **Project's current path**: only `whiskerRight` exists; `whiskerLeft` is faked by two braidings.
- **Gap**: divergent-with-cost, but the fix is cheap. The project already has the *general*
  `whiskerRight` field (`ztensor_whisker_localIso`, arbitrary `f ∈ W'`, NOT just units).
  Since `MonoidalPresheaf X` is **symmetric**, the `whiskerLeft` field follows by braiding
  conjugation — exactly the trick Mathlib uses in the *opposite* direction at `Sites/Monoidal.lean:147`.
  This yields a braiding-free associator `seg1⁻¹ ≫ α^# ≫ seg3` (`seg3` = `whiskerLeft`-unit iso) —
  but better, it yields the whole `IsMonoidal` instance, so don't stop at the associator.
- **Verdict**: **ALIGN_WITH_MATHLIB** — build `W'.IsMonoidal`, not a one-off `whiskerLeft` iso.

## Recommendation

Stop hand-rolling. Build the single instance
`(J.W.inverseImage (toPresheaf R₀)).IsMonoidal` for `R₀ = X.ringCatSheaf.obj` via
`MorphismProperty.IsMonoidal.mk'` (multiplicativity is free for an `inverseImage`):
- `whiskerRight` field = `ztensor_whisker_localIso` (already proven, fully general; just
  bridge `W' f ⟺ (toPresheaf).map f ∈ J.W` through `isIso_sheafification_map_iff`);
- `whiskerLeft` field = braiding-conjugate the above using `PresheafOfModules.symmetricCategory`.
Then instantiate `LocalizedMonoidal (sheafification) W' ε` (choose `ε` so the unit is
`unitModule X`) to get `MonoidalCategory X.Modules` (Mac Lane associator + pentagon + triangle)
and `Localization/Monoidal/Braided` to get `SymmetricCategory X.Modules` (hexagon) — all FREE.
The strong-monoidal `μ : sheafification.obj P ⊗ sheafification.obj Q ≅ sheafification.obj (P ⊗ Q)`
matches the project's objectwise `tensorObj` formula, so `sectionsMul` is preserved.
This makes the three SNAP coherences inherited rather than hand-proved, and dissolves the
auditor's non-canonicity flag (associator is canonical by construction).

NOTE on what is NOT free: `(J.W (A:=AddCommGrpCat)).IsMonoidal` from `Sites/Monoidal.lean:149`
does **not** transfer, and the `inverseImage`-along-a-monoidal-functor instance
(`…/Localization/Monoidal/Basic.lean:71`) does **not** fire, because `toPresheaf`
(modules→abelian) is only *oplax* monoidal (relative tensor is a quotient of `⊗_ℤ`), not strong.
Hence `W'.IsMonoidal` must be proven in-project — but it is two small fields, one already done.
