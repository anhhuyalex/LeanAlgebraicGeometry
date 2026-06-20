# `affineBaseChange_pushforward_iso` (and `flatBaseChange_pushforward_isIso`)

File: `AlgebraicJacobian/Cohomology/FlatBaseChange.lean`
Blueprint: `blueprint/src/chapters/Cohomology_FlatBaseChange.tex`
Source: Stacks Project, Cohomology of Schemes, §"Cohomology and base change, I", Tag 02KH.

## What is DONE (iter-232)

- `AlgebraicGeometry.pushforwardBaseChangeMap` — **fully constructed, axiom-clean**
  (axioms = `propext, Classical.choice, Quot.sound` only). It is the adjoint mate
  of `(pushforward f).map (unit)` under the `(pullback g ⊣ pushforward g)`
  adjunction, using the pseudofunctor coherences `pushforwardComp` /
  `pushforwardCongr`. Type:
  `(pullback g).obj ((pushforward f).obj F) ⟶ (pushforward f').obj ((pullback g').obj F)`.
- `affineBaseChange_pushforward_iso` — proof body contains the genuine first
  reduction `rw [Scheme.Modules.Hom.isIso_iff_isIso_app]; intro U`, leaving
  `IsIso (Hom.app (pushforwardBaseChangeMap …) U)` for each open `U : S'.Opens`.
  `sorry` at that point.
- `flatBaseChange_pushforward_isIso` — `sorry`, with the full Čech reduction
  strategy documented in-file (explicitly deferred by the planner directive).

## The precise missing Mathlib ingredients

The reduction to sections (`Hom.isIso_iff_isIso_app`) is available, but closing the
remaining goal needs an **affine dictionary** that Mathlib does not currently have.
Confirmed absent by source grep over `Mathlib/Algebra/Category/ModuleCat/Sheaf/`
and `Mathlib/AlgebraicGeometry/Modules/`:

1. **Locality of `IsIso` on an affine cover for `SheafOfModules` maps.** We have
   `Scheme.Modules.Hom.isIso_iff_isIso_app` (iso ⟺ iso on *every* open) and a
   module-sheaf stalk (`Mathlib/.../ModuleCat/Sheaf/Stalk.lean`), but no packaged
   "iso ⟺ iso after restricting to each member of an open/affine cover" criterion
   tailored to reduce to affine opens.

2. **Affine description of `pushforward` / `pullback` of `tilde` modules.** No lemma
   relating `Scheme.Modules.pushforward (Spec.map φ)` to `ModuleCat.restrictScalars`
   nor `Scheme.Modules.pullback (Spec.map φ)` to `- ⊗ -` (base change of
   `ModuleCat`). `Mathlib/AlgebraicGeometry/Modules/Tilde.lean` has `tilde`,
   `modulesSpecToSheaf`, `moduleSpecΓFunctor`, `SpecModulesToSheafFullyFaithful`,
   but **no** `pullback`/`pushforward` translation.

3. **Identification of the base-change map components** with the ring-level map.
   Once (1)+(2) exist, the section-level map over `Spec R' ⊆ S'` (with affine
   `f`, so `X = Spec A`, `X' = Spec (R' ⊗_R A)`, `F = M^~`) becomes the
   cancellation isomorphism
   `(R' ⊗[R] A) ⊗[A] M ≃ R' ⊗[R] M`, which **is** in Mathlib:
   `TensorProduct.AlgebraTensorModule.cancelBaseChange`
   (`Mathlib/LinearAlgebra/TensorProduct/Tower.lean:433`). No flatness needed for
   the affine case.

## Suggested follow-up plan (mathlib-build mode)

Build the affine dictionary as a separate engine sub-lane:
- `Scheme.Modules.pushforward_spec_iso` : pushforward along `Spec.map φ` ≃
  `ModuleCat.restrictScalars φ` transported through `moduleSpecΓFunctor` / `tilde`.
- `Scheme.Modules.pullback_spec_iso` : pullback along `Spec.map φ` ≃ `- ⊗ B`.
- `Scheme.Modules.isIso_of_isIso_over_affineCover` : locality of iso on an affine
  open cover of the base (or via the existing module stalk).
Then `affineBaseChange_pushforward_iso` closes by `cancelBaseChange`, and
`flatBaseChange_pushforward_isIso` closes via the Čech complex + exactness of
`- ⊗_A B` for `A → B` flat (`Module.Flat`).

## Informal-agent note

The informal agent could not be consulted: the only env key (`MOONSHOT_API_KEY`,
pointed at `https://api.kimi.com/coding/`) returns HTTP 401 "Invalid
Authentication" against the script's `api.moonshot.cn` endpoint. No other provider
key (`DEEPSEEK/OPENROUTER/OPENAI/GEMINI`) is set.
