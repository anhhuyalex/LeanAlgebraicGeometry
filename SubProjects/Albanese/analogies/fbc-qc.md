# Analogy: affine pushforward of a tilde-module = tilde of restrict-scalars (the FBC `hloc` carrier wall)

## Mode
api-alignment

## Slug
fbc-qc

## Iteration
240

## Question
Does Mathlib already have a direct, idiomatic statement that the pushforward of a
quasi-coherent sheaf along an AFFINE morphism is quasi-coherent (equivalently
`(Spec φ)_* (M^~) ≅ (restrictScalars φ M)^~`), letting `FlatBaseChange.lean` conclude
the localization/quasi-coherence of the pushforward WITHOUT the manual per-`D(a)`
`IsLocalizedModule` (`hloc`) transport that keeps hitting the `Module.compHom` carrier wall?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:428` — `pushforward_spec_tilde_iso_of_isLocalizedModule` (conditional, axiom-clean).
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:535` — `pushforward_spec_tilde_iso` / the `hloc` sorry (the carrier-wall residual, line 572).
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:452` — `IsLocalizedModule.powers_restrictScalars` (= upstream `IsLocalizedModule.restrictScalars_powers`).
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:328` — `gammaPushforwardIsoAt` (per-open version of upstream `pushforwardCompModulesSpecToSheafIso`).
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:480` — `tildeRestriction_isLocalizedModule`.

## Decisions identified

### Decision 1: the whole route — manual `hloc` per-`D(a)` transport vs Mathlib's `isIso_fromTildeΓ_pushforward`

- **Mathlib idiom**: `AlgebraicGeometry.isIso_fromTildeΓ_pushforward` in
  `Mathlib.AlgebraicGeometry.Modules.Tilde`:
  ```
  theorem isIso_fromTildeΓ_pushforward (M : (Spec S).Modules) [h : IsIso M.fromTildeΓ] :
      IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj M).fromTildeΓ := by
    simp_all only [isIso_fromTildeΓ_iff_isLocalizing]
    exact isLocalizing_pushforward_of_isLocalizing φ h
  ```
  This is EXACTLY the affine-pushforward-preserves-quasi-coherence dictionary the project
  needs. Combined with the project's existing `gammaPushforwardTildeIso`, it collapses
  `pushforward_spec_tilde_iso` to ~3 lines (get `IsIso (tilde M).fromTildeΓ` from
  `isIso_fromTildeΓ_iff` + `essImage`, push it forward, then `asIso (...).symm ≪≫ tilde.mapIso (gammaPushforwardTildeIso φ M)`).
  Added upstream **2026-05-31, PR #37189** ("The pushforward of a quasi-coherent sheaf
  between affines is quasi-coherent").

- **Why Mathlib chose it**: Mathlib's quasi-coherence on `Spec R` is `IsIso M.fromTildeΓ`
  (counit of the `tilde ⊣ Γ` adjunction is iso ⇔ `M ∈ essImage tilde`,
  `isIso_fromTildeΓ_iff`), and it proves it via the `IsLocalizing` predicate
  `∀ f : R, IsLocalizedModule (.powers f) (M.obj.map (basicOpen f).leTop.op).hom`
  (= the project's `hloc`!) plus `isIso_fromTildeΓ_iff_isLocalizing`. The pushforward
  step `isLocalizing_pushforward_of_isLocalizing` is the only nontrivial input.

- **Project's current path**: re-derives `IsLocalizing → IsIso fromTildeΓ`
  (`fromTildeΓ_app_isIso_of_isLocalizedModule` + `pushforward_spec_tilde_iso_of_isLocalizedModule`,
  axiom-clean) and is stuck proving the pushforward's `hloc` by hand (open sorry, line 572).

- **Gap**: divergent-with-cost. The project has independently rebuilt ~80% of the upstream
  chain (`powers_restrictScalars` = `restrictScalars_powers`; `gammaPushforwardIsoAt` ≈
  per-open `pushforwardCompModulesSpecToSheafIso`; the `IsLocalizing → IsIso` direction).
  The pin `b80f227` (between 2026-03-04 and 2026-05-31) has `isIso_fromTildeΓ_iff` and
  `isIso_fromTildeΓ_of_presentation` (#36124) but NOT `IsLocalizing`,
  `isIso_fromTildeΓ_iff_isLocalizing`, `isLocalizing_pushforward_of_isLocalizing`, or
  `isIso_fromTildeΓ_pushforward` (all from #37189).

- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision 2: the scalar-restriction mechanism — `Module.compHom _ φ.hom` letI vs `algebraize [φ.hom]`

- **Mathlib idiom**: `isLocalizing_pushforward_of_isLocalizing` discharges the localization
  with **`algebraize [φ.hom]`**, which installs an honest `Algebra ↑R ↑R'` (= `φ.hom.toAlgebra`)
  + `IsScalarTower` instances, then applies `IsLocalizedModule.restrictScalars_powers f _ (h := h (φ f))`:
  ```
  rw [← Functor.comp_obj, isLocalizing_iff_of_iso ((pushforwardCompModulesSpecToSheafIso φ).app M)]
  algebraize [φ.hom]
  exact fun f => IsLocalizedModule.restrictScalars_powers f _ (h := h (φ f))
  ```
- **Project's current path**: views `R'`-sections as `R`-modules via `Module.compHom _ φ.hom`
  in a `letI`, which is NOT picked up by `LinearMap.restrictScalars R` and clashes with the
  `modulesSpecToSheaf`-supplied `R`-action — the documented 4-iter carrier wall.
- **Gap**: divergent-and-wrong (the chosen mechanism cannot be made to typecheck).
- **VERIFIED FIX**: `algebraize [φ.hom]` runs cleanly at the sorry (line 572) in the project's
  own pin, producing `algInst : Algebra ↑R ↑R' := (CommRingCat.Hom.hom φ).toAlgebra`. The
  project's `IsLocalizedModule.powers_restrictScalars` is stated against exactly these
  `[Algebra R A] [IsScalarTower R A M]` instances — so once the action is supplied by
  `algebraize` (not `Module.compHom`), it applies.
- **Verdict**: ALIGN_WITH_MATHLIB.

## Recommendation

**Pivot the lane; stop grinding the carrier wall.** Mathlib has the precise idiom
(`isIso_fromTildeΓ_pushforward`), and it dissolves both the route and the carrier wall.
Two ways to land it:

1. **PREFERRED — bump Mathlib** past 2026-05-31 (PR #37189). Then `pushforward_spec_tilde_iso`
   becomes:
   ```
   haveI : IsIso (tilde M).fromTildeΓ := isIso_fromTildeΓ_iff.mpr ((tilde.functor R').obj_mem_essImage M)
   haveI := isIso_fromTildeΓ_pushforward (φ := φ) (tilde M)
   exact (asIso (Scheme.Modules.fromTildeΓ _)).symm ≪≫ (tilde.functor R).mapIso (gammaPushforwardTildeIso φ M)
   ```
   (first line type-verified in the pin; second needs the bump). `affineBaseChange_pushforward_iso`
   then consumes `pushforward_spec_tilde_iso` as planned. The cost is a project-wide Mathlib
   bump from `b80f227`; assess blast radius first.

2. **If the bump is infeasible — port the short chain** into a project-local supplement:
   `IsLocalizing` (abbrev = the `hloc` predicate already in use), `isLocalizing_iff_of_iso`,
   `isLocalizing_pushforward_of_isLocalizing`, `isIso_fromTildeΓ_iff_isLocalizing`. The project
   already owns `powers_restrictScalars` and the per-open `gammaPushforwardIsoAt`; the genuinely
   missing pieces are (a) **swap `Module.compHom` for `algebraize [φ.hom]`** (verified to work),
   and (b) upgrade `gammaPushforwardIsoAt` to a **natural-in-the-open** iso so it can drive
   `isLocalizing_iff_of_iso` (the memory note "gammaPushforwardIsoAt-naturality-in-open" — this
   is the same naturality upstream packages as `pushforwardCompModulesSpecToSheafIso`).

Either way the carrier wall is a dead mechanism: the fix is `algebraize`/`Algebra`/`IsScalarTower`,
which the directive's hint explicitly suspected and which is confirmed here.
