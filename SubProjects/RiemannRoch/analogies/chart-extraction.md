# Analogy: standard-smooth affine chart + base-field algebra at a scheme stalk

## Mode
api-alignment

## Slug
chart-extraction

## Iteration
009

## Question
From `SmoothOfRelativeDimension 1 (C.hom : C.left ⟶ Spec k̄)` and a point `x : C.left`,
produce an affine chart `S = Γ(C.left, V)` with `[IsStandardSmoothOfRelativeDimension 1 k̄ S]`,
the stalk `T` as a localization of `S`, and `[Algebra k̄ S] [Algebra k̄ T] [Algebra S T]
[IsScalarTower k̄ S T]`. Is the planned hand-rolled `letI`-threaded construction Mathlib-aligned,
or does Mathlib package this? What is the canonical idiom?

## Project artifact(s)
- `AlgebraicJacobian/RiemannRoch/SmoothStalkDVR.lean:140-178` — handoff comment describing the
  planned `HasRingHomProperty.appLE` + `letI`-threaded chart extraction.
- `AlgebraicJacobian/RiemannRoch/SmoothRegular.lean:254-266` — Route-C consumer
  `Algebra.isDiscreteValuationRing_of_smooth_dim_one`.

## Decisions identified

### Decision: how to extract the standard-smooth affine chart at `x`

- **Mathlib idiom**: The class **is** the chart. `SmoothOfRelativeDimension n f` is DEFINED
  (`@[mk_iff] class`) so that its sole field is exactly the chart existential:
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth` (Smooth.lean:134-138):
  ```
  class SmoothOfRelativeDimension : Prop where
    exists_isStandardSmoothOfRelativeDimension : ∀ (x : X), ∃ (U : Y.Opens) (_ : IsAffineOpen U)
      (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
      IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom
  ```
  So `‹SmoothOfRelativeDimension 1 C.hom›.exists_isStandardSmoothOfRelativeDimension x`
  yields `⟨U, hU, V, hV, hx, e, hss⟩` with
  `hss : RingHom.IsStandardSmoothOfRelativeDimension 1 (C.hom.appLE U V e).hom` — DIRECTLY.
- **Project's planned path**: peel `HasRingHomProperty.appLE` (RingHomProperties.lean) on the
  morphism property.
- **Gap**: **divergent-and-wrong**. The `HasRingHomProperty` instance for `SmoothOfRelativeDimension n`
  is `HasRingHomProperty (@SmoothOfRelativeDimension n) (Locally (IsStandardSmoothOfRelativeDimension n))`
  (Smooth.lean:154) — the associated ring-hom property is `Locally (IsStandardSmooth…)`, a
  cover/localization-wrapped predicate, NOT the plain `IsStandardSmoothOfRelativeDimension n`.
  So `HasRingHomProperty.appLE` returns `Locally (…)`, forcing an extra de-`Locally` cover argument.
  The class field gives the plain property with zero extra work.
- **Verdict**: ALIGN_WITH_MATHLIB — use the class field, not `HasRingHomProperty.appLE`.

### Decision: equip `S`/`T` with the `k̄`-algebra + scalar-tower instances

- **Mathlib idiom**: the **`algebraize`** tactic (`Mathlib.Tactic.Algebraize`). It is Mathlib's own
  idiom in the AG morphism files for exactly this stalk/appLE situation:
  `Smooth.lean:271,294,314,345`, `Flat.lean:153`, `FormallyUnramified.lean:160` all do
  `algebraize [(f.appLE …).hom]` / `algebraize [(f.stalkMap x).hom]`.
  Three relevant behaviours (from its docstring):
  1. `algebraize [f]` for `f : A →+* B` adds `Algebra A B` (= `f.toAlgebra`).
  2. `algebraize [g.comp f]` ALSO adds `IsScalarTower A B C` automatically.
  3. it converts any in-context `RingHom`-property hypothesis tagged `@[algebraize …]` into the
     corresponding `Algebra` property. `RingHom.IsStandardSmoothOfRelativeDimension` carries
     `@[algebraize RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra]`
     (StandardSmooth.lean:60-62, where the def literally is
     `RingHom.IsStandardSmoothOfRelativeDimension n f := @Algebra.IsStandardSmoothOfRelativeDimension n _ _ _ _ f.toAlgebra`).
  So `algebraize [ψ]` with `hψ : RingHom.IsStandardSmoothOfRelativeDimension 1 ψ` in context emits
  the instance `Algebra.IsStandardSmoothOfRelativeDimension 1 k̄ S` for free.
- **Project's planned path**: hand-rolled `letI`/explicit-binder threading.
- **Gap**: divergent-equivalent. The hand-roll WORKS and is unavoidable for *pinning the base to
  `k̄`* (see next decision), but `algebraize` is the shorter, Mathlib-idiomatic sugar for the
  tower + property transport. Use it where the base is already a ring-hom; fall back to manual
  `RingHom.toAlgebra` + `IsScalarTower.of_algebraMap_eq (fun _ => rfl)` only to graft the `k̄` base.
- **Verdict**: PROCEED (manual threading is legitimate) but prefer `algebraize` for the tower.

### Decision: identify the base `Γ(Spec k̄, U)` with `k̄`

- **Mathlib idiom**: `Spec` of a field is a single point: `instance {K} [Field K] : Unique (Spec (.of K))`
  (Scheme.lean:629). Hence the obtained `U` (open, contains `C.hom.base x`) is forced `= ⊤`, and
  `ΓSpecIso k̄ : Γ(Spec k̄, ⊤) ≅ k̄` (Scheme.lean:606) gives the iso `R₀ := Γ(Spec k̄, U) ≅ k̄`.
  Transport the standard-smoothness across this iso with
  `isStandardSmoothOfRelativeDimension_respectsIso` (StandardSmooth.lean:118) — same relative
  dimension, no `comp`/dimension arithmetic. Then `ψ := (appLE).hom.comp (ΓSpecIso k̄).inv.hom : k̄ →+* S`.
  (Cf. the field-stalk identification `IsLocalization.atUnits` in
  `genericPoint_mem_smoothLocus_of_perfectField`, Smooth.lean:340-353, for the stalk-side analogue.)
- **Gap**: NEEDS_MATHLIB_GAP_FILL for the *packaging* only — no single lemma turns
  "point on scheme over Spec(field)" into "base-field-algebra standard-smooth chart". But every
  ingredient is present; the assembly is ~15 lines.
- **Verdict**: PROCEED.

## Recommendation
Redirect the chart-extraction entry point: replace the planned `HasRingHomProperty.appLE` route
(which yields the wrong `Locally (…)` shape) with the class field
`SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension x`, which hands back the
plain `IsStandardSmoothOfRelativeDimension 1 (appLE).hom` and collapses the directive's steps 1+3
into one `obtain`. Then: prove `U = ⊤` from `Unique (Spec (.of k̄))`, transport along
`ΓSpecIso k̄` via `isStandardSmoothOfRelativeDimension_respectsIso` to get
`ψ : k̄ →+* S = Γ(C.left, V)` with the standard-smooth property; `have := hV.isLocalization_stalk ⟨x,hx⟩`
for the localization; finish the instances with `algebraize [ψ, (algebraMap S T).comp ψ]`
(auto-emits `Algebra k̄ S`, `Algebra k̄ T`, `IsScalarTower k̄ S T`, and — via the `@[algebraize]`
attribute — `Algebra.IsStandardSmoothOfRelativeDimension 1 k̄ S`), with the `Algebra S T` coming
from `isLocalization_stalk`. The `letI`-threaded construction is Mathlib-aligned; the only real
correction is the chart entry point. NB: `IsSmoothOfRelativeDimension` is a DEPRECATED alias
(since 2026-02-09) of `SmoothOfRelativeDimension` — migrate the names.
