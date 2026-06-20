# Analogy: installing `GrpObj Gm`, the chartwise `gmScalingP1`, and the product-stability instances on `ProjectiveLineBar ⊗ Gm`

## Mode
api-alignment

## Slug
gm-grpobj

## Iteration
167

## Question

Four sub-questions, all in service of closing the iter-166 carry-over `gm_grpObj`
scaffold sorry at `AlgebraicJacobian/Genus0BaseObjects.lean:400` and the four product /
Proj-integrality sorries in the iter-166 helper `morphism_P1_to_grpScheme_const_aux`
(`AlgebraicJacobian/AbelianVarietyRigidity.lean:944,949,953,1029`):

- **Q1** — Does Mathlib already define `𝔾_m` (or anything else the project should
  consume instead of building parallel infrastructure)?
- **Q2** — Is `GrpObj.ofRepresentableBy` the right Mathlib idiom for installing the
  multiplicative group-object structure on `Spec (Localization.Away t)`? If so, what's
  the cleanest path to the `RepresentableBy` witness?
- **Q3** — For the chartwise `gmScalingP1 : ℙ¹ ⊗ Gm ⟶ ℙ¹` body, what's the standard
  Mathlib pattern for the 2-chart cover of `ℙ¹ = Proj k̄[X₀, X₁]` × `Gm` and the
  pullback-of-Specs ring-side bridge?
- **Q4** — For the 4 product/Proj-integrality instances on
  `ProjectiveLineBar ⊗ Gm`, what's the Mathlib idiom?

## Project artifact(s)

- `AlgebraicJacobian/Genus0BaseObjects.lean:400` — `instance gm_grpObj : GrpObj (Gm kbar) := sorry`
  (and the parallel `ga_grpObj` at L335 — same shape, off-path, lower priority)
- `AlgebraicJacobian/Genus0BaseObjects.lean:437-456` — `gmScalingP1` body sorry + companion
  `gmScalingP1_collapse_at_zero` proof sorry
- `AlgebraicJacobian/AbelianVarietyRigidity.lean:944,949,953,1029` — 4 product / Proj
  instance sorries inside `morphism_P1_to_grpScheme_const_aux`
- `AlgebraicJacobian/AbelianVarietyRigidity.lean:1033-1037` — Lane 2 follow-up
  `IsDominant iotaGm.left` (gated on the `gmScalingP1` body; off the main path of
  THIS analogist call but on the same critical path)

## Mathlib state (verified by `lean_local_search` + on-disk `lake env`)

- **`AlgebraicGeometry.AffineSpace`** (`Mathlib.AlgebraicGeometry.AffineSpace`) ships
  the affine `n`-space `𝔸(n; S) := pullback (terminal.from S) (terminal.from (Spec ℤ[n]))`
  plus `AffineSpace.homOverEquiv : { f : X ⟶ 𝔸(n; S) // f.IsOver S } ≃ (n → Γ(X, ⊤))`
  at `AffineSpace.lean:155`. **`Ga` (𝔾_a) is NOT defined.** The project's chosen
  encoding `Ga = (AffineSpace (Fin 1) (Spec k̄)).asOver _` is sound.
- **`AlgebraicGeometry.Proj 𝒜`** (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.*`)
  ships `Proj.toSpecZero`, `Proj.awayι : Spec (HomogeneousLocalization.Away 𝒜 f) ⟶ Proj 𝒜`
  (`Basic.lean:196`), and `Proj.affineOpenCover : (Proj 𝒜).AffineOpenCover`
  (`Basic.lean:339`). `IsProper (Proj.toSpecZero 𝒜)` is shipped at `Proper.lean:?`.
  **`ℙ¹`, `ProjectiveSpace`, etc. are NOT defined.** The project's encoding
  `ProjectiveLineBar = Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k̄)` is sound.
- **`GrpObj.ofRepresentableBy`** (`Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_.lean:35`)
  is Mathlib's Yoneda installer for `GrpObj`. Signature:
  `(F : Cᵒᵖ ⥤ GrpCat.{w}) (α : (F ⋙ forget _).RepresentableBy X) → GrpObj X`.
  The 6 uses across Mathlib are the abstract `yonedaGrpObjRepresentableBy` companion
  proof and 3 hooks in `CommGrp_`/`CommMon_`/`Mon_` — **no concrete-scheme uses**.
- **`Mathlib.AlgebraicGeometry.Group.Smooth`** (62 lines, A. Yang, 2026) ships
  `smooth_of_grpObj_of_isAlgClosed` (`L38`): `[GrpObj (Over.mk f)] +
  [LocallyOfFinitePresentation f] + [IsReduced G] + [IsAlgClosed K] → Smooth f`.
  The project's `gm_smooth`/`ga_smooth` instances consume this directly. **There is
  NO scheme-level `Gm`/`Ga`/group-scheme namespace in Mathlib.**
- **`IsLocalization.Away`** (`Mathlib.RingTheory.Localization.Away.Basic.lean`):
  - `IsLocalization.Away.lift (x : R) (hg : IsUnit (g x)) : S →+* P` (`L471`) —
    factor a ring map `R →+* P` through `Localization.Away x` when `x` lands in
    the units.
  - `IsLocalization.Away.lift_comp` — naturality.
  - `IsLocalization.Away.algebraMap_isUnit` (`L82`) — `algebraMap R S x` is a unit.
- **`ΓSpec.adjunction`** + **`Scheme.ΓSpecIso`** (`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`)
  — `(X ⟶ Spec R) ≃ (R ⟶ Γ(X, ⊤))` (the global-sections / Spec adjunction).
- **`pullbackSpecIso`** (`Mathlib.AlgebraicGeometry.Pullbacks.lean:703`):
  `pullback (Spec.map (algebraMap R S)) (Spec.map (algebraMap R T)) ≅ Spec (S ⊗[R] T)`.
  Plus `pullbackSpecIso_inv_fst` / `_snd` — the chart's pullback is computed by an
  ordinary ring-tensor.
- **`AlgebraicGeometry.Scheme.Cover.glueMorphisms`** (`Gluing.lean:436`) — glue
  chartwise morphisms once they agree on pairwise pullbacks. The agreement hypothesis is
  `pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd _ _ ≫ f y` (NOT `f x = f y` on
  the chart intersection — it's the proper pullback formulation).
- **`Proj.affineOpenCover 𝒜 : (Proj 𝒜).AffineOpenCover`** (`Basic.lean:339`) — the
  standard `Spec (HomogeneousLocalization.Away 𝒜 f)` cover. For our standard ℕ-graded
  `k̄[X₀, X₁]` it specialises to a 2-element cover by `Spec (Away 𝒜 X₀)` and
  `Spec (Away 𝒜 X₁)`. The companion `affineOpenCoverOfIrrelevantLESpan` (`Basic.lean:324`)
  is the explicit "give the 2 generators" form we actually want.
- **`GeometricallyIrreducible`** (`Mathlib.AlgebraicGeometry.Geometrically.Irreducible.lean`):
  - `IsStableUnderBaseChange @GeometricallyIrreducible` (`L49`) — pullback.fst/snd is GI.
  - `GeometricallyIrreducible.comp` (`L121`): `[GI f] [GI g] [UniversallyOpen f]
    [UniversallyOpen g] → GI (f ≫ g)`.
- **`UniversallyOpen.of_flat`** (`Morphisms/UniversallyOpen.lean:145`): `[Flat f]
  [LocallyOfFinitePresentation f] → UniversallyOpen f`. And `[Smooth f] → [Flat f]`
  (`Morphisms/Smooth.lean:113`), so `Smooth ⟹ UniversallyOpen` via `Smooth ⟹
  LocallyOfFinitePresentation ⟹ Flat + LocallyOfFinitePresentation`.
- **`LocallyOfFiniteType`** (`Morphisms/FiniteType.lean`): `IsStableUnderComposition`
  (`L63`) AND `IsStableUnderBaseChange` (`L79`). So `(X ⊗ Y).hom = pullback.fst X.hom
  Y.hom ≫ X.hom` (or `.snd ≫ Y.hom`) is LOFT whenever both factors are.
- **`GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`**
  (`Geometrically/Reduced.lean:106`): `[GeometricallyReduced f] [Flat f] [IsReduced Y]
  [IsLocallyNoetherian Y] → IsReduced X`. The companion `instance` (`L121`/`L125`) gives
  `IsReduced (pullback f g)` from this for either factor having the GR+Flat hypothesis
  and the other having Reduced+LocallyNoetherian.
- **Smooth → GeometricallyReduced**: **NOT shipped at scheme level**. (At ring level:
  `Algebra.IsGeometricallyReduced` exists but is not bridged to `AlgebraicGeometry.GeometricallyReduced`.) This is a real gap for the project.
- **`Proj` is reduced of a reduced graded ring**: NOT shipped. Mathlib has neither
  `IsReduced (Proj 𝒜)` for `𝒜` over a domain nor `IsIntegral (Proj 𝒜)`. The standard
  technique is `IsReduced.of_openCover` over `Proj.affineOpenCover` (each chart is a
  `Spec` of `HomogeneousLocalization.Away 𝒜 X_i` — a localization of an integral graded
  ring, hence reduced).

## Decisions identified

### Decision Q1: realization of `Gm` / `Ga`

- **Mathlib idiom**: Mathlib has no `𝔾_m` / `𝔾_a` / `GroupScheme.Gm` etc. The closest
  existing pieces are (i) `AlgebraicGeometry.AffineSpace` (used by the project for `Ga`),
  (ii) `Mathlib.AlgebraicGeometry.Group.Smooth` (which CONSUMES an arbitrary `GrpObj`),
  and (iii) `Mathlib.AlgebraicGeometry.Pullbacks.Scheme.GrpObjAsOverPullback`
  (`Pullbacks.lean:808`) which transports a `GrpObj` along a pullback. The project's
  encoding `Gm = (Spec (.of (Localization.Away (X : MvPolynomial Unit k̄)))).asOver _`
  is the natural "affine `Spec` of `k̄[t, t⁻¹]`" path.
- **Project's current path**: as above; landed iter-165 (see `gm-scaling-p1` analogy).
- **Gap**: identical-where-Mathlib-has-it, NEEDS_MATHLIB_GAP_FILL where it doesn't.
  The project is NOT building a parallel `GroupScheme.Gm` namespace; it's building one
  concrete `GrpObj` instance using Mathlib's `GrpObj`/`ofRepresentableBy` mechanism.
- **Verdict**: **PROCEED**. The project's encoding is the right shape. Future
  upstream-able as `Mathlib.AlgebraicGeometry.Group.Gm` (single file, ~80 LOC), but the
  *encoding* is identical to what such an upstream file would land.

### Decision Q2: installing `GrpObj Gm` via `ofRepresentableBy`

- **Mathlib idiom**: `GrpObj.ofRepresentableBy X F α` (`Cartesian.Grp_.lean:35`) is THE
  idiom for installing `GrpObj` on an object that represents a presheaf of groups.
  `F : Cᵒᵖ ⥤ GrpCat` and `α : (F ⋙ forget _).RepresentableBy X` are the two inputs.
  This is the canonical and ONLY idiom: the alternative "construct `μ`, `η`, `ι` by
  hand and prove the 5 axioms" is the explicit `GrpObj.mk` path; `ofRepresentableBy`
  packages it. No Mathlib code uses `GrpObj.mk` directly for a non-trivial group
  scheme.
- **Project's current path**: planned to use `ofRepresentableBy`; body is `sorry`.
- **The witness — concrete recipe**:
  - **The functor** `F : (Over (Spec k̄))ᵒᵖ ⥤ GrpCat.{?}` is `T ↦ GrpCat.of Γ(T.left, ⊤)ˣ`.
    The morphism action: an `Over (Spec k̄)`-morphism `φ : T → T'` induces a ring map
    `Γ(T'.left, ⊤) → Γ(T.left, ⊤)` (via `φ.1.appTop`), which restricts to a group hom
    on units. (Use `Units.map` on the comap.)
  - **The representable-by witness** `α : (F ⋙ forget _).RepresentableBy (Gm kbar)`
    constructs `homEquiv : (T ⟶ Gm) ≃ Γ(T.left, ⊤)ˣ`. Built in three steps:
    1. `T ⟶ Gm` (in `Over (Spec k̄)`) ≃ `T.left ⟶ Spec (k̄[t, t⁻¹])` over `Spec k̄`
       (the over-category encoding).
    2. `T.left ⟶ Spec (k̄[t, t⁻¹])` over `Spec k̄` ≃ `k̄[t, t⁻¹] →+* Γ(T.left, ⊤)` as
       `k̄`-algebra maps (the `Spec` adjunction `ΓSpec.adjunction` restricted to the
       over-category). Specifically: a morphism `T.left ⟶ Spec R` over `Spec k̄` is
       (by `ΓSpec.adjunction.homEquiv`) a ring map `R →+* Γ(T.left, ⊤)`; the "over
       `Spec k̄`" condition makes it a `k̄`-algebra map.
    3. `k̄[t, t⁻¹] →ₐ[k̄] Γ(T.left, ⊤)` ≃ `{u : Γ(T.left, ⊤) // IsUnit u}`
       (i.e. `Γ(T.left, ⊤)ˣ`). This is the `IsLocalization.Away.lift` API:
       a `k̄`-algebra map `k̄[t] →ₐ[k̄] Γ(T.left, ⊤)` is the choice of an element
       `u = (f X) ∈ Γ(T.left, ⊤)` (`MvPolynomial.aeval u`), and it factors through
       `Localization.Away X = k̄[t, t⁻¹]` iff `u` is a unit (`IsLocalization.Away.lift`
       gives the factorisation; `IsLocalization.Away.algebraMap_isUnit_iff` is the
       reverse direction).
  - **The `homEquiv_comp` field**: naturality. Reduces to checking that pre-composing
    `T → Gm` with a morphism `φ : T'' → T` produces the comap of the unit. This is
    immediate from `Spec.map`-naturality + `Spec` adjunction + `Units.map`.
- **Gap**: in-proposal. The path is well-defined and uses canonical Mathlib pieces; the
  reason iter-166 deferred was the multi-step bijection composition (one needs the
  over-category Spec-adjunction + Localization.Away.lift bridge, which is not a single
  Mathlib lemma).
- **Verdict**: **PROCEED with `ofRepresentableBy`**. The chain is:
  `(T ⟶ Gm)_{/Spec k̄}` 
  $\xrightarrow{\text{over-cat unfold}}$ `{f : T.left ⟶ Spec(k̄[t,t⁻¹]) // f ≫ struct = T.hom}`
  $\xrightarrow{\Gamma\text{Spec}}$ `{φ : k̄[t,t⁻¹] →+* Γ(T,⊤) // φ ∘ algebraMap k̄ _ = ...}`
  $\xrightarrow{\text{IsLocalization.Away.lift}}$ `{u : Γ(T,⊤) // IsUnit u}` = `Γ(T,⊤)ˣ`.
  No parallel API, no custom `GroupScheme.Hom` infrastructure. Bonus: the same recipe
  (with the additive functor `AddGrpCat.of Γ(T,⊤)`, using `AffineSpace.homOverEquiv`
  directly in step 2-3) closes `ga_grpObj` — see `gm-scaling-p1.md` D2.a.

### Decision Q3: `gmScalingP1` chartwise glue

- **Mathlib idiom**: `Scheme.Cover.glueMorphisms` over a 2-chart `Proj.affineOpenCover`
  (specialised to the irrelevant ideal's 2 generators `X₀, X₁`), each chart's morphism
  given by `Spec.map` of a polynomial ring map. The cross-chart agreement is checked
  using `pullbackSpecIso` to identify each chart's intersection with the other as `Spec`
  of a ring tensor, then proving a ring-level equation.
- **Concrete recipe**:
  - Two-chart cover: `affineOpenCoverOfIrrelevantLESpan 𝒜 (f := ![X₀, X₁]) ...` —
    explicitly the 2-element cover indexed by `Fin 2`. (`Proj.affineOpenCover` is the
    "all positive-degree elements" cover; we want the 2-element specialisation.)
    Each chart is `Spec (HomogeneousLocalization.Away 𝒜 X_i)` — for the standard
    ℕ-graded `k̄[X₀, X₁]`, this homogeneous localization is `k̄[X_{1-i} / X_i]` (single
    variable in degree-0 = polynomial ring in `t = X_{1-i}/X_i`). Mathlib has the
    iso witness via `HomogeneousLocalization.Away.algebraMap` etc., but the
    project-side bridge "Spec(HomogeneousLocalization.Away X_i) ≅ Spec(k̄[t])"
    is needed (NOT shipped for `MvPolynomial`-specific gradings; project owes this
    iso, ~30 LOC).
  - Chart-side morphism `(σ_×)_i : Spec(k̄[t_i]) ⊗_{Spec k̄} Spec(k̄[λ, λ⁻¹]) ⟶
    Spec(k̄[t_i])`: use `pullbackSpecIso` to identify the product as
    `Spec(k̄[t_i, λ, λ⁻¹])`; then `(σ_×)_0 = Spec.map (k̄[t] →+* k̄[t, λ, λ⁻¹], t ↦ λ·t)`
    on chart 0 (affine), and `(σ_×)_1 = Spec.map (k̄[u] →+* k̄[u, λ, λ⁻¹], u ↦ u/λ)`
    on chart 1 (near ∞). Both are ring-level definitions.
  - Cross-chart agreement: on the intersection `Spec(k̄[t, t⁻¹]) ⊗ Spec(k̄[λ, λ⁻¹])
    ≅ Spec(k̄[t, t⁻¹, λ, λ⁻¹])`, both chart maps reduce to `t ↦ λ·t = (λ·t⁻¹)⁻¹`;
    `pullbackSpecIso` + ring-level computation closes this in `ext + simp + ring`.
- **Project's current path**: `gmScalingP1 := sorry` (iter-165 deferred to iter-166;
  iter-166 closed the consumer via sorryAx-propagation, so the body is still owed).
- **Gap**: in-proposal. The path is clear; the iter-166 hold-up was the
  Mathlib-orchestration weight (3-4 sub-lemmas worth: HomogeneousLocalization.Away iso,
  pullbackSpecIso bridge, polynomial ring-map definition, glue agreement).
- **Verdict**: **PROCEED with `glueMorphisms` + `pullbackSpecIso`**. NO custom `Cover`
  / `MulAction` typeclass; bare morphism only. The companion lemma
  `gmScalingP1_collapse_at_zero` follows from a chart-level direct computation (on
  chart 0, `(0, λ) ↦ λ·0 = 0` is a `Spec.map` of a ring map sending `t ↦ 0`, which is
  exactly the structure map of `zeroPt = Proj.fromOfGlobalSections of (X₀ ↦ 0, X₁ ↦ 1)`).

### Decision Q4: the four product / Proj-integrality instances

#### Q4(a) — `GeometricallyIrreducible ((ℙ¹) ⊗ (Gm)).hom`

- **Mathlib idiom**: composition via `GeometricallyIrreducible.comp`
  (`Geometrically/Irreducible.lean:121`). `(X ⊗ Y).hom = (pullback X.hom Y.hom).hom =
  pullback.fst X.hom Y.hom ≫ X.hom`. Both factors are GI (the `pullback.fst` from
  `GeometricallyIrreducible.IsStableUnderBaseChange`, the `X.hom` from the project's
  `projectiveLineBar_geomIrred` instance). The composition lemma requires
  `UniversallyOpen` on both — supplied for free by smoothness via
  `UniversallyOpen.of_flat` (`Morphisms/UniversallyOpen.lean:145`) + `Smooth → Flat`
  (`Morphisms/Smooth.lean:113`).
- **Verdict**: **PROCEED**. Code shape:
  ```lean
  haveI : GeometricallyIrreducible ((P¹) ⊗ (Gm)).hom :=
    GeometricallyIrreducible.comp (pullback.fst P¹.hom Gm.hom) P¹.hom
  ```
  (with `UniversallyOpen.of_flat` instances inferred from smoothness). Sub-prerequisite:
  `[GeometricallyIrreducible (Gm kbar).hom]` — currently NOT installed on `Gm`. This is
  the next gap; for `Spec (integral k̄-algebra)` over `Spec k̄`, `GeometricallyIrreducible`
  is automatic since base-change to `Spec k̄` is identity, hence reduces to
  `IrreducibleSpace (Spec (Localization.Away X))` which is automatic from
  `Localization.Away X` being a domain (localization of integral domain). The Mathlib
  bridge is `irreducibleSpace_of_isDomain` (or directly via
  `PrimeSpectrum.irreducibleSpace_iff_isDomain`).

#### Q4(b) — `LocallyOfFiniteType ((ℙ¹) ⊗ (Gm)).hom`

- **Mathlib idiom**: TRIVIAL. `LocallyOfFiniteType` is `IsStableUnderComposition` AND
  `IsStableUnderBaseChange` (`Morphisms/FiniteType.lean:63,79`). `(X ⊗ Y).hom =
  pullback.fst ≫ X.hom`. Both pieces LOFT, composition LOFT. `LocallyOfFinitePresentation
  → LocallyOfFiniteType` is also free for both factors (and for ℙ¹ specifically: `Proj`
  of finite-type-over-k̄ is LOFT via `Proj.awayι_toSpecZero` + `HasRingHomProperty.Spec_iff`
  + `RingHom.FiniteType`; not auto-instanced, but the project can install it on
  `ProjectiveLineBar`).
- **Verdict**: **PROCEED**. `infer_instance` should close it once a
  `[LocallyOfFiniteType (ProjectiveLineBar kbar).hom]` instance is installed (currently
  missing — derivable from `IsProper` is actually not direct; need explicit `Proj.toSpecZero`
  LOFT instance which is shipped by the `Proper.lean` chain at L143). The `Gm` side is
  free (`LocallyOfFinitePresentation → LocallyOfFiniteType` instance shipped).

#### Q4(c) — `IsReduced ((ℙ¹) ⊗ (Gm)).left`

- **Mathlib idiom**: The shipped lemma is `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian` (`Geometrically/Reduced.lean:106`):
  `[GeometricallyReduced f] [Flat f] [IsReduced Y] [IsLocallyNoetherian Y] →
  IsReduced X`, with the companion `instance` (`L121`/`L125`) giving the product
  version. **For the project's setting** (`Y = Spec k̄`, both factors reduced + smooth):
  - `IsLocallyNoetherian (Spec k̄)` — free (`k̄` is Noetherian as a field).
  - `IsReduced (Spec k̄)` — free.
  - `Flat (ProjectiveLineBar).hom` — from `Smooth → Flat`.
  - `GeometricallyReduced (ProjectiveLineBar).hom` — **NOT free**. Mathlib does NOT
    ship `Smooth → GeometricallyReduced` at scheme level. Standard math fact (smooth
    morphisms are geometrically regular hence geometrically reduced), but the bridge
    `Smooth ⟹ Algebra.IsGeometricallyReduced ⟹ AlgebraicGeometry.GeometricallyReduced`
    is missing.
- **Gap**: GAP_EXISTS — Mathlib gap, not project gap. The project should either:
  - (i) install a one-off project-side instance `Smooth f → GeometricallyReduced f`
    (~30 LOC, scheme-level extension of `Algebra.IsGeometricallyReduced`), or
  - (ii) bypass `GeometricallyReduced` entirely by noting that `(ℙ¹ ⊗ Gm)` is
    explicitly the pullback `Proj 𝒜 ×_{Spec k̄} Spec(k̄[t, t⁻¹])`, locally affine, and
    reduce to a tensor-product-of-domains argument on each affine chart of `ℙ¹`. Each
    chart is `Spec (k̄[t]) ⊗_{Spec k̄} Spec(k̄[λ, λ⁻¹]) = Spec(k̄[t, λ, λ⁻¹])`, which is a
    domain over k̄ (algebraically closed), hence reduced; `IsReduced.of_openCover`
    closes (`Geometrically/Reduced.lean:?` shipped).
- **Verdict**: **PROCEED via path (ii)** (chart-local), NOT path (i). Reason:
  - The "install `Smooth → GeometricallyReduced`" instance is genuine Mathlib
    infrastructure work and may be 100+ LOC; out of scope for an iter-167 prover lane.
  - The chart-local path uses ONLY `IsReduced.of_openCover` + the fact that
    `Spec(domain over k̄)` is reduced — both routine. The hard part (which 2 charts)
    is already done by `Proj.affineOpenCover`, and the same pullbackSpecIso bridge
    from Q3 supplies the chart description.
  - **Bonus**: this same chart-local technique handles Q4(d), so the project's
    reduction is double-leveraged. Project owes ~40 LOC for one helper lemma
    `isReduced_of_affineCover_isDomain` (or `IsReduced.of_isOpenCover_isDomain`)
    that takes a cover with each chart's global-sections-ring a domain over an
    integral base.

#### Q4(d) — `IsReduced (ProjectiveLineBar).left`

- **Mathlib idiom**: NOT shipped. The standard technique is
  `IsReduced.of_openCover` (`AlgebraicGeometry.IsReduced.of_openCover` or via
  `IsReduced.of_isOpenImmersion` composed with `Cover`-decomposition). For the project's
  case, the open cover is `Proj.affineOpenCover 𝒜` specialised to the 2-element form
  `{D₊(X₀), D₊(X₁)}`. Each `D₊(X_i)` is `Spec (HomogeneousLocalization.Away 𝒜 X_i)`,
  which is `Spec` of an integral domain (a localisation of the integral graded ring
  `k̄[X₀, X₁]`'s degree-0 piece in chart 0 = `k̄[X₁/X₀]`, which is a polynomial ring
  in one variable, hence a domain). Domain ⟹ Reduced ⟹ `IsReduced (Spec _)`.
- **Verdict**: **PROCEED via `IsReduced.of_openCover` over `Proj.affineOpenCover`**.
  Same helper as Q4(c) discharges; the missing piece is
  `HomogeneousLocalization.Away 𝒜 X_i` is a domain for the standard ℕ-grading on
  `MvPolynomial (Fin 2) k̄`. This is a ring-level fact: it's a localization of
  `k̄[X₀, X₁]` at the powers of `X_i`, restricted to degree-0. Mathlib has
  `HomogeneousLocalization.isDomain` for `Proj` of an integral domain (file
  `RingTheory.GradedAlgebra.HomogeneousLocalization`); the project then uses
  `IsReduced.of_isDomain`.

## Recommendation

**For Q2 (gm_grpObj):** Use `GrpObj.ofRepresentableBy` with the 3-step bijection chain.
Sketch:
```lean
instance gm_grpObj (kbar : Type u) [Field kbar] : GrpObj (Gm kbar) := by
  refine GrpObj.ofRepresentableBy (Gm kbar)
    { obj := fun T => GrpCat.of (Γ(T.unop.left, ⊤))ˣ
      map := fun {T T'} φ => GrpCat.ofHom (Units.map (φ.unop.1.appTop).hom.toMonoidHom)
      map_id := …
      map_comp := … }
    ?_
  refine
    { homEquiv := fun {T} => ?_
      homEquiv_comp := ?_ }
  -- Build the Equiv (T ⟶ Gm) ≃ Γ(T.left, ⊤)ˣ via:
  -- 1. Over-cat unfold: (T ⟶ Gm)_{/Spec k̄} ≃ {f : T.left ⟶ Spec(k̄[t,t⁻¹]) // IsOver Spec k̄}
  -- 2. ΓSpec.adjunction restricted to the over-cat: ≃ k̄[t,t⁻¹] →ₐ[k̄] Γ(T.left, ⊤)
  -- 3. IsLocalization.Away.lift + IsLocalization.Away.algebraMap_isUnit_iff:
  --    ≃ {u : Γ(T.left, ⊤) // IsUnit u} = Γ(T.left, ⊤)ˣ
  sorry  -- the 3-step bijection composition (carry from iter-167 lane)
```

**For Q3 (gmScalingP1):** Build the helper `def homogeneousLocalizationAwayIso :
HomogeneousLocalization.Away (projectiveLineBarGrading kbar) (MvPolynomial.X i) ≃+*
MvPolynomial Unit kbar` (the "degree-0 of localization at X_i = polynomial in
X_{1-i}/X_i" iso); use it to identify each chart of `ProjectiveLineBar` with
`Spec(k̄[t])`; build `(σ_×)_0`, `(σ_×)_1` as `Spec.map` of polynomial ring maps;
glue via `Scheme.Cover.glueMorphisms` over a 2-element cover constructed from
`affineOpenCoverOfIrrelevantLESpan`; verify cross-chart agreement using
`pullbackSpecIso` to identify the intersection as `Spec(k̄[t, t⁻¹, λ, λ⁻¹])` and a
direct ring-level check.

**For Q4 (product / Proj instances in AVR):**
- Q4(b) — close immediately via `infer_instance` after installing
  `LocallyOfFiniteType (ProjectiveLineBar kbar).hom` on the `Proj` side (free via
  `Proj.toSpecZero` LOFT instance).
- Q4(a) — close via `GeometricallyIrreducible.comp` after installing
  `[UniversallyOpen ProjectiveLineBar.hom]` (free from smoothness, which is itself a
  scaffold sorry — but the chain is well-typed) AND `[GeometricallyIrreducible (Gm kbar).hom]`
  (free from `Localization.Away X` being a domain + `Spec k̄` base = identity base change).
- Q4(c), Q4(d) — close via one shared helper:
  ```lean
  lemma isReduced_of_affineCover_each_isDomain {X : Scheme}
      (𝒰 : X.AffineOpenCover) (h : ∀ i, IsDomain (𝒰.obj i)) : IsReduced X
  ```
  (or the more general `IsReduced.of_openCover` if shipped, applied with each chart
  affine + global-sections ring a domain). For Q4(d), instantiate with
  `Proj.affineOpenCover` + `HomogeneousLocalization.Away.isDomain`. For Q4(c),
  instantiate with the cover of `ℙ¹ ⊗ Gm` obtained by pulling back
  `Proj.affineOpenCover` along the `Gm`-projection + `pullbackSpecIso` + 
  `(k̄[t] ⊗_{k̄} k̄[λ, λ⁻¹]).isDomain`.

**Risk on the Smooth → GeometricallyReduced gap (Q4c).** If the chart-local path
proves harder than estimated (unlikely — each piece is ≤30 LOC), revisit upstreaming
the `Smooth → GeometricallyReduced` instance, which would unlock Q4(c) in one line.
This is genuine Mathlib infrastructure and could be a future-iter contribution.

**No parallel-API risks identified.** The project's `GrpObj`, `ofRepresentableBy`,
`Scheme.Cover.glueMorphisms`, `pullbackSpecIso`, `GeometricallyIrreducible.comp`,
and `IsReduced.of_openCover` paths all consume Mathlib's existing API. The single gap
is the missing `Smooth → GeometricallyReduced` scheme-level bridge — and even there
the project has a clean workaround via `IsReduced.of_openCover` that avoids
introducing a parallel typeclass or shadow lemma.

**Bonus — `ga_grpObj` (out-of-scope per directive, but FREE here):** The same Q2
recipe with `AffineSpace.homOverEquiv` *as a single Mathlib lemma* discharging the
3-step bijection chain (since `Ga` = `𝔸(Fin 1, Spec k̄)` is exactly the affine space
that `AffineSpace.homOverEquiv` is built for; the bijection is `(Hom T (𝔸(Fin 1) S) //
IsOver) ≃ (Fin 1 → Γ(T, ⊤)) ≃ Γ(T, ⊤)`). So `ga_grpObj` is genuinely a 2-3 line proof
in `ofRepresentableBy` style; `gm_grpObj` is the harder of the two because Mathlib
does NOT ship a "homOverEquiv for `Spec (Localization.Away _)`" lemma.
