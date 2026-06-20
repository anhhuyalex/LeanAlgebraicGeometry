# Analogy: Can the scheme-module tensor `tensorObj` get an UNCONDITIONAL associator by anchoring on Mathlib's monoidal-sheafification machinery?

## Mode
api-alignment

## Slug
monoidal-transport

## Iteration
233

## Question
Can the project obtain the associator/unitors/braiding for `tensorObj` (sheafified
presheaf-of-modules tensor on `X.Modules = SheafOfModules X.ringCatSheaf`)
**unconditionally** by reading them off Mathlib's `Sheaf.monoidalCategory` /
`J.W.IsMonoidal` machinery, instead of the hand-built whiskering transport whose
residual is the `sorry` `isLocallyInjective_whiskerLeft_of_W`?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:340-383` — `tensorObj_assoc_iso`, the
  three-step sheafification-transport associator. Calls the sorry-dependent
  `W_whiskerRight_of_W` / `W_whiskerLeft_of_W` (lines 371/374) even though it takes
  `IsLocallyTrivial M/N/P` hypotheses it never uses.
- `AlgebraicJacobian/Picard/TensorObjSubstrate/Vestigial.lean:267-299` —
  `isLocallyInjective_whiskerLeft_of_W`, the single open `sorry` (line 299), the
  unconditional whiskering-preserves-W lemma; its docstring (232-236, 252-264) asserts
  the "enough points gives `J.W.IsMonoidal` for free / `Sites.Point.IsMonoidalW`" claim.
- `AlgebraicJacobian/Picard/TensorObjSubstrate/Vestigial.lean:111-219` — the FLAT
  whiskering lemmas `isLocallyInjective_whiskerLeft_of_flat`, `W_whiskerLeft_of_flat`,
  `W_whiskerRight_of_flat`, **axiom-clean / sorry-free**, needing only
  `∀ X, Module.Flat (R.obj X) (F.obj X)`.

## Decisions identified

### Decision: Does the Mathlib `Sheaf.monoidalCategory` / `J.W.IsMonoidal` chain apply to `SheafOfModules`?

- **Mathlib idiom**: `CategoryTheory.Sheaf.monoidalCategory`
  (`Mathlib.CategoryTheory.Sites.Monoidal`) gives
  `MonoidalCategory (Sheaf J A)` for a **fixed** monoidal value category `A`, gated on
  `[J.W.IsMonoidal]` + `[HasWeakSheafify J A]`. The monoidal structure transported is
  the **pointwise** monoidal structure on the functor category `Cᵒᵖ ⥤ A`.
- **Project's setting**: `X.Modules = SheafOfModules X.ringCatSheaf` — sheaves of
  modules over a *varying* sheaf of rings. Its monoidal structure is
  `PresheafOfModules.monoidalCategory`
  (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`), i.e. tensor **over the
  varying ring** `R = X.presheaf ⋙ forget₂ CommRingCat RingCat`. This is NOT the
  pointwise monoidal structure on any `Cᵒᵖ ⥤ A`.
- **Gap**: divergent-and-the-idiom-does-not-apply. Confirmed by search:
  - NO `MonoidalCategory (SheafOfModules _)` instance (loogle: no results).
  - NO `SheafOfModules.Monoidal` namespace, NO "sheafification of `PresheafOfModules`
    is monoidal" lemma (leansearch: only `sheafification`/`sheafify`/`toSheafify`, none
    monoidal).
  - `presheafToSheaf` is monoidal ONLY for `Sheaf J A`
    (`Sheaf.instMonoidalFunctorOppositePresheafToSheaf`), again fixed `A`.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL — the chain is for fixed-`A` sheaf categories;
  `SheafOfModules` over a varying ring is genuinely outside it. A transport step (the
  sheafification of the presheaf-of-modules tensor) is REQUIRED — exactly what the
  project already does. The proposed "read it off `Sheaf.monoidalCategory`" shortcut
  does not exist.

### Decision: Is `J.W.IsMonoidal` obtainable "for free from enough points"?

- **Mathlib idiom**: `J.W.IsMonoidal` is `CategoryTheory.MorphismProperty.IsMonoidal`
  (`Mathlib.CategoryTheory.Localization.Monoidal.Basic`). Its constructor fields ARE
  `whiskerLeft : ∀ X {Y₁ Y₂} (g), W g → W (X ◁ g)` and the `whiskerRight` dual; the
  smart constructor `IsMonoidal.mk'` instead asks for `W` closed under `tensorHom`.
  The ONLY instance providing it for a topology is
  `CategoryTheory.GrothendieckTopology.W.monoidal`
  (`Mathlib.CategoryTheory.Sites.Monoidal`), whose hypotheses are
  `[MonoidalCategory A]`, **`[MonoidalClosed A]`**,
  `[∀ F₁ F₂, HasFunctorEnrichedHom A F₁ F₂]`, `[∀ F₁ F₂, HasEnrichedHom A F₁ F₂]`.
  (Also `W.transport_isMonoidal` — transfers `IsMonoidal` along a cover-dense full
  continuous functor; not points-based.) Mathlib's proof that whiskering preserves
  `J.W` (`GrothendieckTopology.W.whiskerLeft`) is the internal-hom adjoint argument:
  `X ◁ -` is a left adjoint (via `MonoidalClosed`), hence commutes with sheafification.
- **The cited `Sites.Point.IsMonoidalW`**: DOES NOT EXIST. No search hit anywhere
  (`lean_leansearch`, `lean_loogle`). `TopCat.hasEnoughPoints` likewise did not
  surface; even if it ships, it is NOT load-bearing because no points-based
  `IsMonoidal` instance consumes it. The project's own comment (Vestigial.lean:232-236,
  252-264) asserting "Mathlib blesses the flatness-free technique for `J.W.IsMonoidal`
  via enough points / `Sites.Point.IsMonoidalW`" is **unsubstantiated** — that
  declaration is not in Mathlib at the pinned commit.
- **Gap**: divergent-and-wrong (the premise that `IsMonoidal` is free is false). The
  `IsMonoidal` typeclass does not eliminate the whiskering obligation — its
  `whiskerLeft` field IS the obligation (`isLocallyInjective_whiskerLeft_of_W` is
  exactly that field for `W = inverseImage toPresheaf J.W` on `PresheafOfModules`).
  Mathlib discharges it only via `MonoidalClosed`, which the project does not have for
  `PresheafOfModules`.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL — to use route (a) one must first build
  `MonoidalClosed (PresheafOfModules R)` (the tensor-hom adjunction; the project's
  ts219 internal-hom is only the value object, NOT the adjunction) AND a
  `W.monoidal`-analog stated for `PresheafOfModules` (Mathlib's is for `Cᵒᵖ ⥤ A`).
  Strictly MORE work than the stalk route, because the MonoidalClosed adjoint argument
  reproduces precisely the whiskering-preserves-W content after the extra closed-structure build.

### Decision: cheapest path that actually retires `isLocallyInjective_whiskerLeft_of_W`?

- **Route (a) Mathlib monoidal sheafification**: NOT viable off-the-shelf (above two
  decisions). Cost: build `MonoidalClosed (PresheafOfModules R)` + enriched-hom infra +
  a PresheafOfModules-level `W.monoidal`. High; ≥ the stalk port and adds prerequisites.
- **Route (b) prove `isLocallyInjective_whiskerLeft_of_W` directly via the stalk (d.2)**:
  the genuine unconditional residual. ~200-400 LOC; needs the Mathlib-absent stalk-⊗
  commutation `(F ⊗ᵖ M)_x ≅ F_x ⊗_{R_x} M_x` at the `PresheafOfModules` level. d.1
  (`stalkLinearMap`) is already built project-side.
- **Route (b′) flat / locally-trivial restriction — ALREADY SORRY-FREE in the project**:
  `W_whiskerLeft_of_flat` / `W_whiskerRight_of_flat` (Vestigial.lean:188/204) are
  axiom-clean from `∀ X, Module.Flat (R.obj X) (F.obj X)`. `tensorObj_assoc_iso`
  already carries `IsLocallyTrivial M/N/P` but discards them. CAVEAT (project's own
  iter-212 finding, TensorObjSubstrate.lean:322-335): local triviality does NOT give
  *global* sectionwise flatness — global sections over a NON-affine open are not flat,
  so `_of_flat` cannot be fed for a line bundle globally. The correct realization is the
  **local-triviality whiskering**: on the trivializing cover where `P ≅ 𝒪`,
  `η ▷ P ≅ η ∈ J.W` directly; no stalk port, no MonoidalClosed, no false flatness.
- **Verdict**: route (b′ local) ALIGN with the project's iter-232 pivot; route (a)
  NEEDS_MATHLIB_GAP_FILL (do not pursue).

## Recommendation

Do **not** pursue route (a). The Mathlib monoidal-sheafification machinery
(`Sheaf.monoidalCategory`, `J.W.IsMonoidal`, `presheafToSheaf.Monoidal`) is stated for
`Sheaf J A` over a FIXED monoidal value category `A` with the pointwise functor-category
monoidal structure; `SheafOfModules` over the varying ring `X.ringCatSheaf` is not an
instance of it, there is no `MonoidalCategory (SheafOfModules _)`, and the only
`J.W.IsMonoidal` instance (`GrothendieckTopology.W.monoidal`) requires
`MonoidalClosed A` + enriched-hom infrastructure that the project does not have for
`PresheafOfModules`. The cited `Sites.Point.IsMonoidalW` does not exist; the
"enough points makes `J.W.IsMonoidal` free" claim in the project's own comments is
false at the pinned commit. The `IsMonoidal` typeclass does not remove the whiskering
obligation — its `whiskerLeft` field IS `isLocallyInjective_whiskerLeft_of_W`. Either
(b) port the d.2 stalk-⊗ commutation for the truly unconditional lemma (~200-400 LOC,
genuinely Mathlib-absent), or — matching the iter-232 carrier-pivot and the only objects
the group law consumes — **drop "unconditional" and realize the associator on the
trivializing cover** (`IsLocallyTrivial`: where `P ≅ 𝒪`, the whiskered unit lies in
`J.W` for free), which needs neither the stalk port nor MonoidalClosed. Switch
`tensorObj_assoc_iso`'s `_of_W` calls to a local-triviality-scoped whisker rather than
trying to read the associator off a non-existent `MonoidalCategory (SheafOfModules _)`.
