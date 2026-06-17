# Analogy: ring-localization `Localization.Away (algebraMap A C g)` ↔ module-localization `LocalizedModule (powers g) C`

## Mode
api-alignment

## Slug
gf-localizedmodule-localization-away-bridge

## Iteration
022

## Question
For a commutative ring `C` that is an `A`-algebra and `g : A`, identify the localized MODULE
`LocalizedModule (Submonoid.powers g) C` with the localized RING
`Localization.Away (algebraMap A C g)`. Find the canonical Mathlib idiom (a named iso, or the
`IsLocalizedModule`/`IsLocalization`-uniqueness route) the GF prover should use to discharge
step (4) of the `genericFlatnessAlgebraic` cascade.

## Project artifact(s)
- `AlgebraicJacobian/Picard/FlatteningStratification.lean:1996-2021` — the `B/𝔭` residual branch of
  `genericFlatnessAlgebraic`; the open `sorry` at line 2021. Step (4) is the ring↔module bridge.
- `AlgebraicJacobian/Picard/FlatteningStratification.lean:1701-1707` — `free_localizationAway_of_away_tower`,
  the DESCENT consumer of the bridge. Its `hfree` hypothesis is stated on
  `LocalizedModule (Submonoid.powers h) (LocalizedModule (Submonoid.powers g) T)` — i.e. it expects the
  **module-localization** `LocalizedModule (powers g) C`, NOT the ring `C_g`. This is exactly why a
  bridge is needed: L4/L5 produce freeness over the RING `C_g = Localization.Away (algebraMap A C g)`,
  but `away_tower` (and the final goal) speak of the MODULE `LocalizedModule (powers g) C`.

## The bridge — VERIFIED, one-step, canonical

### The IsLocalizedModule instance (the load-bearing fact)

`Mathlib.Algebra.Module.LocalizedModule.IsLocalization` exports the **instance**

```
instance instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmonoid
    {R} [CommSemiring R] (S : Submonoid R) {A Aₛ} [CommSemiring A] [Algebra R A]
    [CommSemiring Aₛ] [Algebra A Aₛ] [Algebra R Aₛ] [IsScalarTower R A Aₛ]
    [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ] :
  IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap
```

Instantiate with `R := A`, `A := C`, `Aₛ := Localization.Away (algebraMap A C g)`, `S := Submonoid.powers g`.
It states that the structure map `C →ₗ[A] C_g` (the `A`-linear underlying map of
`IsScalarTower.toAlgHom A C C_g : C →ₐ[A] C_g`) **is** a localization of the `A`-module `C` at `powers g`.

### The named iso (the actual bridge the prover writes)

`Mathlib.Algebra.Module.LocalizedModule.Basic`:

```
IsLocalizedModule.iso (S : Submonoid R) (f : M →ₗ[R] M') [IsLocalizedModule S f] :
  LocalizedModule S M ≃ₗ[R] M'
```

So
```
IsLocalizedModule.iso (Submonoid.powers g)
    (IsScalarTower.toAlgHom A C (Localization.Away (algebraMap A C g))).toLinearMap
  : LocalizedModule (Submonoid.powers g) C ≃ₗ[A] Localization.Away (algebraMap A C g)
```
is **exactly** the requested iso, produced in one step. There is NO need for a hand-built
`LocalizedModule.lift` uniqueness argument. (`IsLocalizedModule.linearEquiv` is not a separate API —
`.iso` is the name. `IsLocalization.algEquiv` is ring↔ring and does NOT apply: the LHS
`LocalizedModule (powers g) C` is carried as a bare module, not a ring-localization object.)

## Two obligations the prover must discharge (the only fiddly bits)

The instance above is NOT found by `inferInstance` out of the box, because it needs two side-inputs:

### (1) The submonoid-identity-transported `IsLocalization` instance

The instance hypothesis is `[IsLocalization (Algebra.algebraMapSubmonoid C (powers g)) C_g]`, but the
ambient instance on `C_g = Localization.Away (algebraMap A C g) = Localization (powers (algebraMap A C g))`
is `IsLocalization (powers (algebraMap A C g)) C_g` (`Localization.isLocalization`). The two submonoids
are **propositionally** equal but not syntactically, via:

```
Submonoid.map_powers (f) (m) : Submonoid.map f (Submonoid.powers m) = Submonoid.powers (f m)
  -- Mathlib.Algebra.Group.Submonoid.Membership
Algebra.algebraMapSubmonoid C M  -- = M.map (algebraMap A C)  (Mathlib.Algebra.Algebra.Basic:138, a plain def)
```

So `Algebra.algebraMapSubmonoid C (powers g)` unfolds (by `rfl`/`show`) to `(powers g).map (algebraMap A C)`,
which `Submonoid.map_powers (algebraMap A C) g` rewrites to `powers (algebraMap A C g)`. Prover snippet:

```
haveI : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers g))
    (Localization.Away (algebraMap A C g)) := by
  show IsLocalization (Submonoid.map (algebraMap A C) (Submonoid.powers g)) _
  rw [Submonoid.map_powers]; infer_instance
```

### (2) The base scalar tower / algebra
`[Algebra A C_g]` and `[IsScalarTower A C C_g]`. `C_g` is a `C`-algebra (`Localization`), `C` is an
`A`-algebra; the composite `Algebra A C_g` + `IsScalarTower A C C_g` is standard
(`IsScalarTower.of_algebraMap_eq` / the composite-algebra instance). The file already builds the sibling
tower `A_g → C_g` (`algAgBg`, line 681), so this scaffolding pattern is in-repo.

## Base-ring linearity: upgrade `≃ₗ[A]` to `≃ₗ[A_g]` (REQUIRED for the freeness transfer)

`IsLocalizedModule.iso` gives only an **`A`-linear** equiv. But `free_localizationAway_of_away_tower`
needs freeness over `Localization.Away h` of `LocalizedModule (powers h) (LocalizedModule (powers g) C)`,
i.e. the bridge must respect the `A_g = Localization.Away g`-module structure (both sides are canonically
`A_g`-modules). Upgrade with:

```
LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers g) (Localization.Away g)
    (IsLocalizedModule.iso (Submonoid.powers g) (IsScalarTower.toAlgHom A C C_g).toLinearMap)
  : LocalizedModule (Submonoid.powers g) C ≃ₗ[Localization.Away g] Localization.Away (algebraMap A C g)
```
`LinearEquiv.extendScalarsOfIsLocalization (S) (A) (f : M ≃ₗ[R] N) : M ≃ₗ[A] N`
(`Mathlib.RingTheory.Localization.Module`) requires `[IsLocalization S A]`, both `M`,`N` to be
`A`-modules with `IsScalarTower R A M/N`. Here `R := A`, `S := powers g`, `A := Localization.Away g`;
`LocalizedModule (powers g) C` is an `A_g`-module canonically, and `C_g` is an `A_g`-module via the
`A_g → C_g` algebra (`algAgBg` in-file). With the `A_g`-linear equiv, `Module.Free` transfers across the
further `LocalizedModule (powers h) (·)` and `Localization.Away h`-base, feeding `away_tower` directly.

## Decisions identified

### Decision: named iso vs uniqueness route for the ring↔module bridge

- **Mathlib idiom**: `IsLocalizedModule.iso (powers g) (IsScalarTower.toAlgHom A C C_g).toLinearMap`,
  with the `IsLocalizedModule` instance auto-supplied by
  `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmonoid` once the two
  obligations above are met. Cite:
  `Mathlib.Algebra.Module.LocalizedModule.IsLocalization` (instance),
  `Mathlib.Algebra.Module.LocalizedModule.Basic` (`IsLocalizedModule.iso`),
  `Mathlib.RingTheory.Localization.Module` (`LinearEquiv.extendScalarsOfIsLocalization`),
  `Mathlib.Algebra.Group.Submonoid.Membership` (`Submonoid.map_powers`).
- **Project's current path**: step (4) is an open `sorry` described as "an `IsLocalizedModule`-uniqueness
  iso" — which is precisely the `.iso` route. The project's instinct is correct; it just needs the
  exact names + the two side-obligations pinned.
- **Gap**: divergent-equivalent collapsing to identical — Mathlib has the whole bridge; nothing must be
  built project-side. The only project glue is the submonoid-identity `haveI` and the scalar-tower
  scaffolding (both one-liners, both already patterned in-file).
- **Verdict**: ALIGN_WITH_MATHLIB — consume `IsLocalizedModule.iso` + the named instance +
  `extendScalarsOfIsLocalization`; do NOT hand-roll a `LocalizedModule.lift` uniqueness proof.

## Recommendation
Discharge step (4) in three moves: (i) supply
`haveI : IsLocalization (Algebra.algebraMapSubmonoid C (powers g)) (Localization.Away (algebraMap A C g))`
by `show … (Submonoid.map (algebraMap A C) (powers g)) …; rw [Submonoid.map_powers]; infer_instance`,
plus the `Algebra A C_g` / `IsScalarTower A C C_g` composite; (ii) form the bridge
`e := IsLocalizedModule.iso (powers g) (IsScalarTower.toAlgHom A C C_g).toLinearMap`
(`: LocalizedModule (powers g) C ≃ₗ[A] C_g`), free from the now-resolvable
`instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmonoid`; (iii) upgrade to
`A_g`-linear via `LinearEquiv.extendScalarsOfIsLocalization (powers g) (Localization.Away g) e`, then
transport the L5 freeness witness across it into the `LocalizedModule (powers g) C` form that
`free_localizationAway_of_away_tower` consumes. No new Mathlib gap; the bridge is fully stocked.
