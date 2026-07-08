/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Genus
import AlgebraicJacobian.Picard.Pic0AbelianVariety
import AlgebraicJacobian.Albanese.CodimOneExtension

/-!
# The Albanese universal property of `Pic⁰_{C/k}` (A.4.d)

This file is the **A.4.d** file-skeleton sub-build chapter for the project's
positive-genus arm of `nonempty_jacobianWitness`. It packages Milne's
*Abelian Varieties* §III.6 Proposition 6.1: for a complete nonsingular curve
`C` of genus `g > 0` over an algebraically closed field `k̄` and a marked
`k̄`-point `P₀ ∈ C(k̄)`, the Abel–Jacobi morphism
`ι_{P₀} : C ⟶ Pic⁰_{C/k̄}` is the **Albanese morphism** of the pointed curve
`(C, P₀)`: any pointed morphism `φ : C ⟶ A` into an abelian variety with
`φ(P₀) = η_A` factors uniquely as `φ = ψ ∘ ι_{P₀}` for a homomorphism of
group schemes `ψ : Pic⁰_{C/k̄} ⟶ A`.

The chapter commits to the **symmetric-power route** (cube-free): the
symmetric assignment `(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)` factors through
`Sym^g C`, the resulting morphism `Sym^g φ : Sym^g C ⟶ A` descends through
the birational morphism `f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}` to a rational map
`Pic⁰_{C/k̄} ⇢ A`, and Milne's Theorem I.3.2 (`extend_to_av` in the sibling
`Albanese/Thm32RationalMapExtension.lean`, A.4.c) promotes it to a regular
morphism `ψ : Pic⁰_{C/k̄} ⟶ A`. The group-homomorphism property of `ψ` then
follows from `ψ(η_J) = η_A` together with Milne Corollary I.1.2 (a
consequence of `thm:rigidity_lemma`).

## Status (iter-177 Lane 7 file-skeleton)

This file is the **iter-177 Lane 7** file-skeleton. Each of the six
blueprint-pinned declarations carries the *intended* substantive type
signature (matching the `\lean{...}` pin in
`blueprint/src/chapters/Albanese_AlbaneseUP.tex`) with a `sorry` body.

The 6 pinned declarations are:

1. `AlgebraicGeometry.Pic0.abelJacobi` (noncomputable def, ~6 LOC) — the
   regular morphism `ι_{P₀} : C ⟶ Pic⁰_{C/k̄}` of
   `lem:abel_jacobi_morphism`. Encoded against the file-internal
   placeholder `Pic0.jacobianScheme` for `Pic⁰_{C/k̄}` (the A.3 upstream
   has not yet been split out; see §0 below).
2. `AlgebraicGeometry.Pic0.SymmetricPower` (noncomputable def, ~3 LOC) —
   the `g`-th symmetric power `Sym^g C` of the curve `C`, as a `k̄`-scheme.
   Body gated on iter-178+ `SymmetricPower.lean` substrate (Milne III.3
   Proposition 3.1; Mumford 1970 II.7 / III.11 affine-and-glue recipe).
3. `AlgebraicGeometry.Pic0.symmetricPowerAVMap` (noncomputable def, ~5 LOC) —
   the symmetrised morphism `Sym^g φ : Sym^g C ⟶ A` produced by
   `lem:symmetric_product_av_map` from an input `φ : C ⟶ A`.
4. `AlgebraicGeometry.Pic0.symmetricPowerToJacobian` (noncomputable def,
   ~5 LOC) — the birational morphism `f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}` of
   `lem:symmetric_product_to_jacobian`.
5. `AlgebraicGeometry.Pic0.descentThroughBirationalSigma` (theorem,
   ~10 LOC) — the descent of `Sym^g φ` to a regular morphism
   `ψ : Pic⁰_{C/k̄} ⟶ A` via Milne Theorem 3.2.
6. `AlgebraicGeometry.Pic0.albanese_universal_property` (theorem, ~12 LOC) —
   the headline UP theorem (Milne Proposition III.6.1).

## File-internal placeholder for `Pic⁰_{C/k̄}`

The A.3 row of Route A (the identity-component refinement of the Picard
scheme together with its degree map) is now split out in
`Picard/Pic0AbelianVariety.lean`. We keep a thin `Pic0.Bundle` structure
here bundling the underlying scheme together with its four abelian-variety
instances (`GrpObj`, `IsProper`, `Smooth`, `GeometricallyIrreducible`),
plus the carrier `Pic0.bundle C` and a derived definition
`Pic0.jacobianScheme C := (bundle C).scheme`. The four instances on
`jacobianScheme C` are derived from the bundle's fields. Once the A.3
chapter's own `smooth`/`proper` gaps close, this placeholder collapses to a
one-line re-export.

Bundle wiring (this iter): `bundle C` is **no longer a typed `sorry`**. Its
underlying scheme is `Scheme.Pic0Scheme C` and its four attributes are the
tracked upstream theorems `Scheme.Pic0.{grpObj, proper, smooth,
geometricallyIrreducible}`. The upstream hypotheses
`[GeometricallyIntegral C.hom] [HasPicScheme C]
[PicScheme.PicSchemeLocallyOfFiniteType C]` are discharged honestly over the
algebraically closed base by the three axiom-clean bridges of §0.0
(`geometricallyReduced_of_smooth`, `GeometricallyIntegral.of_…`,
`hasRationalPoint_of_isAlgClosed`). Any residual `sorryAx` in `bundle` is
inherited **only** from the still-open upstream `Scheme.Pic0.smooth` /
`Scheme.Pic0.proper` and the FGA `instHasPicScheme`; no `sorry` is
introduced here.

## Note on type expressivity

Following the project rule "Never weaken the type to dodge the proof",
each pinned declaration carries a substantive, non-tautological type:

- `abelJacobi C P₀ : C ⟶ jacobianScheme C` — a genuine morphism into the
  Pic⁰ scheme (not `𝟙 C` or any tautology).
- `SymmetricPower C g : Over (Spec (.of k̄))` — a `k̄`-scheme, not `C`
  itself or `𝟙_`.
- `symmetricPowerAVMap C g φ : SymmetricPower C g ⟶ A` — a morphism into
  the abelian variety `A`.
- `symmetricPowerToJacobian C P₀ g : SymmetricPower C g ⟶ jacobianScheme C`
  — a morphism into Pic⁰.
- `descentThroughBirationalSigma` — `∃!` existence-and-uniqueness of
  `ψ : jacobianScheme C ⟶ A` satisfying
  `symmetricPowerAVMap C g φ = symmetricPowerToJacobian C P₀ g ≫ ψ`.
- `albanese_universal_property` — `∃!` existence-and-uniqueness of
  `ψ : jacobianScheme C ⟶ A` satisfying `φ = abelJacobi C P₀ ≫ ψ`.

Unfolding any pinned declaration exposes the named substantive content
(a morphism into the Pic⁰ scheme, a unique factorisation through the
Abel–Jacobi map, …); no `Iso.refl _` / `Classical.choice ⟨witness⟩` /
empty-content `proof_wanted` placeholders are used.

## Abelian-variety conventions

Following the project (cf. `AbelianVarietyRigidity.lean`, `Jacobian.lean`),
an **abelian variety over `k̄`** is encoded as an object
`A : Over (Spec (.of k̄))` carrying the four instances:

- `[GrpObj A]` (group-object structure on the over-category),
- `[IsProper A.hom]` (complete),
- `[Smooth A.hom]` (nonsingular),
- `[GeometricallyIrreducible A.hom]` (geometrically irreducible).

A **smooth proper geometrically irreducible curve over `k̄`** carries:

- `[SmoothOfRelativeDimension 1 C.hom]`,
- `[IsProper C.hom]`,
- `[GeometricallyIrreducible C.hom]`.

These instances are supplied by `inferInstance` at the call site.

## References

Blueprint: `blueprint/src/chapters/Albanese_AlbaneseUP.tex` (~830 LOC,
6 pins). Source: Milne, *Abelian Varieties*, §III.6 Proposition 6.1, p. 104;
§III.3 Proposition 3.1 (symmetric power), p. 94; §III.5 Theorem 5.1(a)
(birationality of `f^{(g)}`), p. 101 (`references/abelian-varieties.pdf`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-! ## §0.0. Substrate bridges: geometric integrality and rational points

The A.3 upstream (`Picard/Pic0AbelianVariety.lean`) states `Pic⁰_{C/k}` smooth,
proper and geometrically irreducible under the hypotheses
`[GeometricallyIntegral C.hom] [HasPicScheme C]
[PicScheme.PicSchemeLocallyOfFiniteType C]`, whereas the Albanese curve `C`
enters here carrying only `[SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
[GeometricallyIrreducible C.hom]` over an algebraically closed field `k̄`. The
three bridging facts below discharge the missing hypotheses honestly, so that
`Pic0.bundle` can be assembled from the tracked upstream declarations rather than
from a typed `sorry`. -/

/-- **Reducedness descends along a faithfully flat morphism.** If `π : Y ⟶ X` is
flat and surjective (i.e. faithfully flat) and `Y` is reduced, then `X` is
reduced: each stalk map `𝒪_{X,π(y)} → 𝒪_{Y,y}` is a flat local homomorphism of
local rings, hence faithfully flat and in particular injective, so `𝒪_{X,π(y)}`
embeds into the reduced ring `𝒪_{Y,y}`. -/
theorem isReduced_of_flat_of_surjective {X Y : Scheme.{u}} (π : Y ⟶ X)
    [Flat π] [Surjective π] [IsReduced Y] : IsReduced X := by
  haveI hst : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨y, rfl⟩ := π.surjective x
    have hlocal : IsLocalHom (π.stalkMap y).hom := inferInstance
    have hflat : (π.stalkMap y).hom.Flat := Flat.stalkMap π y
    have hinj : Function.Injective (π.stalkMap y).hom := by
      algebraize [(π.stalkMap y).hom]
      haveI : Module.Flat (X.presheaf.stalk (π.base y)) (Y.presheaf.stalk y) := hflat
      haveI : IsLocalHom (algebraMap (X.presheaf.stalk (π.base y)) (Y.presheaf.stalk y)) := hlocal
      haveI : Module.FaithfullyFlat (X.presheaf.stalk (π.base y)) (Y.presheaf.stalk y) :=
        Module.FaithfullyFlat.of_flat_of_isLocalHom
      exact FaithfulSMul.algebraMap_injective _ _
    exact isReduced_of_injective (π.stalkMap y).hom hinj
  exact isReduced_of_isReduced_stalk X

/-- **A scheme smooth over an algebraically closed field is geometrically
reduced.** For each test field `K/k̄`, the base change `X ×_{k̄} K` is smooth
over `K`; its further base change to `K̄ = AlgebraicClosure K` is smooth over an
algebraically closed field, hence reduced
(`Scheme.isReduced_of_smooth_of_isAlgClosed`), and reducedness descends along the
faithfully flat projection `X_{K̄} → X_K` (`isReduced_of_flat_of_surjective`). -/
theorem geometricallyReduced_of_smooth {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of kbar)) [Smooth f] :
    GeometricallyReduced f := by
  refine ⟨?_⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  have hfsurj : (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hFS := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))).mpr hfsurj
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) := hFS.1
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) := hFS.2
  haveI hsm1 : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K)))) :=
    inferInstance
  haveI hsm2 : Smooth (pullback.snd
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) := inferInstance
  haveI : Smooth (Over.mk (pullback.snd
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))).hom := hsm2
  haveI : IsReduced (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) :=
    Scheme.isReduced_of_smooth_of_isAlgClosed (kbar := AlgebraicClosure K) (Over.mk (pullback.snd
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))))
  exact isReduced_of_flat_of_surjective
    (pullback.fst (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap kbar K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))

/-- **A smooth, geometrically irreducible curve over an algebraically closed
field has a rational point.** `C.left` is nonempty (geometric irreducibility over
the one-point base `Spec k̄`), locally of finite type over `k̄` (smoothness) and
therefore a Jacobson space, so it has a closed point `x`; over the algebraically
closed field `k̄`, `pointOfClosedPoint`/`pointEquivClosedPoint` promote `x` to a
`k̄`-rational section of `C.hom`. This discharges `[HasRationalPoint C]`. -/
theorem hasRationalPoint_of_isAlgClosed {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (C : Over (Spec (.of kbar))) [Smooth C.hom] [GeometricallyIrreducible C.hom] :
    Scheme.HasRationalPoint C := by
  haveI : LocallyOfFiniteType C.hom := inferInstance
  haveI : IrreducibleSpace C.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton C.hom
  haveI : JacobsonSpace C.left := LocallyOfFiniteType.jacobsonSpace C.hom
  obtain ⟨x, hx⟩ := nonempty_inter_closedPoints (X := C.left) (Z := Set.univ)
    Set.univ_nonempty isClosed_univ.isLocallyClosed
  exact ⟨⟨(pointEquivClosedPoint C.hom).symm ⟨x, hx.2⟩⟩⟩

namespace Pic0

/-! ## §0. File-internal placeholder for `Pic⁰_{C/k̄}`

The A.3 row of Route A (identity component of the Picard scheme together
with its degree map) is split out in `Picard/Pic0AbelianVariety.lean`. The
helper below — a bundled structure carrying the Pic⁰ scheme together with
its four abelian-variety instances, plus the carrier `bundle` — supplies
the interface. `bundle` is wired to the tracked upstream declarations
(`Scheme.Pic0Scheme`, `Scheme.Pic0.{grpObj, proper, smooth,
geometricallyIrreducible}`) via the axiom-clean §0.0 bridges, so it consumes
**no** `sorry` of its own; the derived `jacobianScheme` def and the four
typeclass carriers below are projections from `bundle`. Residual `sorryAx`
in this section is inherited only from the still-open upstream
`Scheme.Pic0.smooth` / `Scheme.Pic0.proper` and the FGA `instHasPicScheme`. -/

/-- File-internal placeholder for `Pic⁰_{C/k̄}`: bundles the underlying
`k̄`-scheme together with the four abelian-variety structural instances
(group object, proper, smooth, geometrically irreducible) supplied at the
A.3 row of Route A.

Collapses to a re-export of the A.3 chapter once that materialises. -/
structure Bundle {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (C : Over (Spec (.of kbar)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom] where
  /-- The underlying scheme `Pic⁰_{C/k̄}`. -/
  scheme : Over (Spec (.of kbar))
  /-- Group-object structure on `Pic⁰_{C/k̄}`. -/
  grpObj : GrpObj scheme
  /-- Properness of `Pic⁰_{C/k̄}` over `k̄`. -/
  proper : IsProper scheme.hom
  /-- Smoothness of `Pic⁰_{C/k̄}` over `k̄`. -/
  smooth : Smooth scheme.hom
  /-- Geometric irreducibility of `Pic⁰_{C/k̄}` over `k̄`. -/
  geomIrred : GeometricallyIrreducible scheme.hom

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]

variable (C : Over (Spec (.of kbar)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]

/-- **The `Pic⁰_{C/k̄}` bundle, wired to the tracked A.3 upstream.** For a smooth
proper geometrically irreducible curve `C` over an algebraically closed field
`k̄`, the underlying scheme is `Scheme.Pic0Scheme C` and its four
abelian-variety attributes are the identity-component theorems of
`Picard/Pic0AbelianVariety.lean` (`Scheme.Pic0.{grpObj, proper, smooth,
geometricallyIrreducible}`).

The upstream declarations run under `[GeometricallyIntegral C.hom]`,
`[HasPicScheme C]` and `[PicScheme.PicSchemeLocallyOfFiniteType C]`; over `k̄`
these are discharged honestly here:
`geometricallyReduced_of_smooth` + `GeometricallyIrreducible C.hom` give
`GeometricallyIntegral C.hom`; `hasRationalPoint_of_isAlgClosed` gives
`[HasRationalPoint C]`, whence `instHasPicScheme` supplies `[HasPicScheme C]` and
`instPicSchemeLocallyOfFiniteType` the local-finiteness carrier.

This removes the former opaque `sorry` token and makes the Albanese-cone DAG
honest: any residual `sorryAx` taint is inherited only from the still-open
upstream `Scheme.Pic0.smooth` / `Scheme.Pic0.proper` (and the FGA
`instHasPicScheme`), never introduced here. -/
noncomputable def bundle : Bundle C := by
  haveI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  haveI : GeometricallyReduced C.hom := geometricallyReduced_of_smooth C.hom
  haveI : GeometricallyIntegral C.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible C.hom
  haveI : Scheme.HasRationalPoint C := hasRationalPoint_of_isAlgClosed C
  exact
    { scheme := Scheme.Pic0Scheme C
      grpObj := (Scheme.Pic0.grpObj C).some
      proper := Scheme.Pic0.proper C
      smooth := Scheme.Pic0.smooth C
      geomIrred := Scheme.Pic0.geometricallyIrreducible C }

/-- The underlying `k̄`-scheme `Pic⁰_{C/k̄}` of a smooth proper
geometrically irreducible curve `C` over an algebraically closed field
`k̄`. Read off from the `Bundle` placeholder. -/
noncomputable def jacobianScheme : Over (Spec (.of kbar)) := (bundle C).scheme

/-- Group-object structure on `Pic⁰_{C/k̄}`. **Demoted from
`instance` per lean-auditor iter-196 must-fix**: the silent
propagation of `sorryAx` through `GrpObj`-typeclass synthesis is
a soundness exposure until the `bundle` carrier closes.
Consumers thread via `letI := jacobianScheme_grpObj C`. -/
noncomputable def jacobianScheme_grpObj : GrpObj (jacobianScheme C) :=
  (bundle C).grpObj

/-- (Demoted from `instance`; see `jacobianScheme_grpObj`.) -/
theorem jacobianScheme_isProper : IsProper (jacobianScheme C).hom :=
  (bundle C).proper

/-- (Demoted from `instance`; see `jacobianScheme_grpObj`.) -/
theorem jacobianScheme_smooth : Smooth (jacobianScheme C).hom :=
  (bundle C).smooth

/-- (Demoted from `instance`; see `jacobianScheme_grpObj`.) -/
theorem jacobianScheme_geomIrred :
    GeometricallyIrreducible (jacobianScheme C).hom :=
  (bundle C).geomIrred

/-! ## §1. The Abel–Jacobi morphism at a marked point

The first sub-lemma packages the construction and elementary regularity
of the Abel–Jacobi morphism `ι_{P₀} : C ⟶ Pic⁰_{C/k̄}` at the basepoint
`P₀ ∈ C(k̄)`. On `k̄`-points,
`ι_{P₀}(Q) = [𝓞_C(Q − P₀)] ∈ Pic⁰_{C/k̄}(k̄)`; at the basepoint
itself `ι_{P₀}(P₀) = η_J`.

This is the content gated on A.3 (existence of `Pic⁰_{C/k̄}` as a
representable group scheme); the morphism is the moduli classifier of
the rigidified diagonal correspondence
`𝓛^{P₀} = 𝓞_{C × C}(Δ − {P₀} × C − C × {P₀})` on `C × C`, taken as a
relative degree-zero line bundle on `C × C` over the second factor.

Blueprint reference: `lem:abel_jacobi_morphism` (Milne, *Abelian
Varieties*, Proposition III.6.1 and Summary III.6.11). -/

/-- **The Abel–Jacobi morphism at the marked basepoint `P₀`.**

For a smooth proper geometrically irreducible curve `C` over an
algebraically closed field `k̄` and a marked `k̄`-point
`P₀ : 𝟙_ ⟶ C`, the **Abel–Jacobi morphism** is the unique regular
morphism `ι_{P₀} : C ⟶ Pic⁰_{C/k̄}` characterised on `T`-points by the
formula `(1 × ι_{P₀})^* 𝓜^{P₀} ≈ 𝓛^{P₀}`, where `𝓜^{P₀}` is the
Poincaré–Picard correspondence on `C × Pic⁰_{C/k̄}` and
`𝓛^{P₀} = 𝓞_{C × C}(Δ − {P₀} × C − C × {P₀})`.

iter-178+: body constructed by applying the moduli interpretation of
`Pic⁰_{C/k̄}` (`def:pic_scheme` together with the identity-component
refinement A.3) to the relative degree-zero line bundle `𝓛^{P₀}` on
`C × C → C` along the second projection. Yoneda then produces the
unique classifying morphism `C ⟶ Pic⁰_{C/k̄}`. The basepoint
condition `P₀ ≫ abelJacobi C P₀ = η[Pic⁰_{C/k̄}]` (`lem:abel_jacobi_morphism`)
holds because restriction of `𝓛^{P₀}` to `C × {P₀}` is the trivial
line bundle `𝓞_C(P₀ − P₀) ≅ 𝓞_C` whose moduli class is `η_J`.

For the iter-177 file-skeleton the body is a typed `sorry`. -/
noncomputable def abelJacobi (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C) :
    C ⟶ jacobianScheme C :=
  sorry

/-! ## §2. The `g`-th symmetric power `Sym^g C`

The `g`-th symmetric power of `C` is the quotient of the `g`-fold
Cartesian power `C^g` by the natural permutation action of the
symmetric group `S_g`. Mathlib `b80f227` has no formalised symmetric
power of a scheme — only `Sym` / `SymmetricPower` for types and
modules — so the scheme-theoretic construction must be supplied
project-side, following Milne's recipe of §III.3 Proposition 3.1: on
each open affine `U = Spec A ⊆ C` form `Spec(A^{⊗ g})^{S_g}`, then glue
along the standard open-cover patching (Mumford 1970 §II.7 / §III.11).

This sub-build is a non-trivial dependency of A.4.d that the prover
must absorb before the body of `symmetricPowerAVMap` /
`symmetricPowerToJacobian` closes; the carrier here records the
substantive *target* `Sym^g C : Over (Spec k̄)` with a typed `sorry`
body, deferring the affine-and-glue construction to iter-178+
`Albanese/SymmetricPower.lean`.

Blueprint reference: `def:symmetric_power_curve` (Milne, *Abelian
Varieties*, §III.3, Proposition 3.1, p. 94). -/

/-- **The `g`-th symmetric power `Sym^g C`** of a complete nonsingular
curve `C` over an algebraically closed field `k̄`, as a `k̄`-scheme.

Milne III.3 Proposition 3.1 constructs `Sym^g C` as the quotient of
`C^g` by the natural permutation action of the symmetric group `S_g`:
on each open affine `U = Spec A ⊆ C`, form `Spec(A^{⊗ g})^{S_g}`, then
glue along the standard open-cover patching. The construction comes
equipped with a canonical finite surjective symmetric morphism
`π : C^g ⟶ Sym^g C` characterised by the universal property that
every `S_g`-symmetric morphism `C^g ⟶ T` factors uniquely through `π`.

This pin records the substantive *target* scheme `Sym^g C`; the
projection `π` and its universal property are recorded as helper API
in the iter-178+ `Albanese/SymmetricPower.lean` substrate file.

iter-178+: body is the gluing-of-affines `Spec(A^{⊗ g})^{S_g}`
construction over an open affine cover of `C`. For the iter-177
file-skeleton the body is a typed `sorry`.

The signature mentions `C` explicitly (not via the file's `variable`
block) so that the declaration's first explicit argument is the curve
`C`, matching the call sites `SymmetricPower C g`. -/
noncomputable def SymmetricPower
    (C : Over (Spec (.of kbar)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIrreducible C.hom]
    (_g : ℕ) : Over (Spec (.of kbar)) :=
  sorry

/-! ## §3. The morphism `Sym^g φ : Sym^g C ⟶ A`

The second sub-lemma is the elementary fact that the symmetric
assignment `(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)` from `C^g` to `A`
descends through `π : C^g ⟶ Sym^g C`. The key point is that the
`g`-fold addition morphism `add_A : A^g ⟶ A` is itself `S_g`-symmetric
because the underlying group object `A` is commutative as a group
scheme; combined with the universal property of `Sym^g C`, this yields
the unique factorisation.

Blueprint reference: `lem:symmetric_product_av_map` (Milne's proof of
III.6.1, p. 104, "Clearly this is symmetric, and so it factors through
`C^{(g)}`"). -/

/-- **The symmetrised morphism `Sym^g φ : Sym^g C ⟶ A`.**

Let `φ : C ⟶ A` be a morphism into an abelian variety `A` over `k̄`.
The composition `add_A ∘ φ^{×g} : C^g ⟶ A^g ⟶ A` sending
`(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)` is `S_g`-equivariant (where `S_g`
permutes the factors of `C^g` and acts trivially on `A`), because
addition in a commutative group object is order-independent. By the
universal property of `Sym^g C` (`def:symmetric_power_curve`) it
factors uniquely as `Sym^g φ ∘ π = add_A ∘ φ^{×g}`.

iter-178+: body is the universal-property invocation on the
symmetric composition `add_A ∘ φ^{×g}` once the iter-178+
`Albanese/SymmetricPower.lean` substrate exposes the projection `π`
and its UP. For the iter-177 file-skeleton the body is a typed `sorry`. -/
noncomputable def symmetricPowerAVMap (g : ℕ)
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (_φ : C ⟶ A) :
    SymmetricPower C g ⟶ A :=
  sorry

/-! ## §4. The birational morphism `Sym^g C ⟶ Pic⁰_{C/k̄}`

The third sub-lemma is the birational identification of `Sym^g C` with
`Pic⁰_{C/k̄}`. After choosing the basepoint `P₀ ∈ C(k̄)`, the cycle
map `(P₁,…,P_g) ↦ [𝓞_C(P₁ + ⋯ + P_g − g P₀)]` defines a regular
morphism `f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}` which is birational by
Milne III Theorem 5.1(a) (the proof uses dimension count plus the
Riemann–Roch identification of the generic fibre as a single point on
a curve of genus `g`).

Blueprint reference: `lem:symmetric_product_to_jacobian` (Milne,
*Abelian Varieties*, Theorem III.5.1(a), p. 101). -/

/-- **The birational morphism `f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}`.**

Given a basepoint `P₀ : 𝟙_ ⟶ C`, the symmetrisation of the Abel–Jacobi
morphism `add_J ∘ ι_{P₀}^{×g} : C^g ⟶ J^g ⟶ J` descends through
`π : C^g ⟶ Sym^g C` to a regular morphism
`f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}` sending an effective divisor class
`[P₁ + ⋯ + P_g]` to `[𝓞_C(P₁ + ⋯ + P_g − g P₀)] ∈ Pic⁰_{C/k̄}(k̄)`.
By Milne III Theorem 5.1(a) this morphism is *birational*: it is
dominant with one-dimensional fibres, and its generic fibre is a single
`k̄`-point (the linear system `|D|` of a general degree-`g` divisor `D`
on a curve of genus `g` is `0`-dimensional by Riemann–Roch).

The birationality data (a dense open subset `U ⊆ Sym^g C` mapping
isomorphically onto a dense open `V ⊆ Pic⁰_{C/k̄}`) is recorded as
helper API in the iter-178+ proof body of
`descentThroughBirationalSigma`.

iter-178+: body is the specialisation of `symmetricPowerAVMap` to
`A := jacobianScheme C` and `φ := abelJacobi C P₀`. For the iter-177
file-skeleton the body is a typed `sorry`. -/
noncomputable def symmetricPowerToJacobian
    (_P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C) (g : ℕ) :
    SymmetricPower C g ⟶ jacobianScheme C :=
  sorry

/-! ## §5. Descent through the birational quotient

The final auxiliary lemma packages the two-step descent that promotes
`Sym^g φ : Sym^g C ⟶ A` (after passing through the birational morphism
`f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}`) to a regular morphism
`ψ : Pic⁰_{C/k̄} ⟶ A`. The descent is a rational map
`Pic⁰_{C/k̄} ⇢ A` on the dense open of `Pic⁰_{C/k̄}` on which
`f^{(g)}` is an isomorphism, then promoted to a regular morphism via
Milne's Theorem I.3.2 (the sibling `Albanese/Thm32RationalMapExtension.lean`).
This is the unique step of the proof that consumes A.4.c.

Blueprint reference: `lem:descent_through_birational_sigma` (Milne's
proof of III.6.1, p. 104, "It therefore defines a rational map
`ψ : J → A`, which (I 3.2) shows to be a regular map"). -/

/-- **Descent of `Sym^g φ` to a regular morphism `ψ : Pic⁰_{C/k̄} ⟶ A`.**

There is a *unique* regular morphism `ψ : Pic⁰_{C/k̄} ⟶ A` such that
`symmetricPowerAVMap C (genus C) φ = symmetricPowerToJacobian C P₀ (genus C) ≫ ψ`
(equivalently, `ψ` is the unique regular extension of the rational map
`Sym^g φ ∘ (f^{(g)})^{-1} : Pic⁰_{C/k̄} ⇢ A`).

The rational map is constructed on the dense open `V ⊆ Pic⁰_{C/k̄}`
where `f^{(g)}` is an isomorphism, then promoted to a regular morphism
on all of `Pic⁰_{C/k̄}` via Milne's Theorem I.3.2 (sibling
`Scheme.RationalMap.extend_to_av` in
`Albanese/Thm32RationalMapExtension.lean`, A.4.c). Uniqueness is the
standard reduced-and-separated agreement principle: two regular
morphisms `Pic⁰_{C/k̄} ⟶ A` agreeing on a dense open are equal.

iter-178+: body invokes `Scheme.RationalMap.extend_to_av` on the
rational map produced by inverting `f^{(g)}` on its dense open of
isomorphism. For the iter-177 file-skeleton the body is a typed
`sorry`. -/
theorem descentThroughBirationalSigma
    (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C)
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (φ : C ⟶ A) (_hφ : P0 ≫ φ = η[A]) :
    ∃! (ψ : jacobianScheme C ⟶ A),
      symmetricPowerAVMap C (genus C) φ
        = symmetricPowerToJacobian C P0 (genus C) ≫ ψ := by
  sorry

/-! ## §5.5. Albanese ⇔ symmetric-power equation (connecting biconditional)

The iter-182 structural decomposition extracts the precise *connecting
identity* between the Albanese-form factorisation
`φ = abelJacobi C P₀ ≫ ψ` and the symmetric-power-form factorisation
`symmetricPowerAVMap C (genus C) φ = symmetricPowerToJacobian C P₀
(genus C) ≫ ψ` as a named typed-`sorry` biconditional helper. With this
biconditional in hand the body of `albanese_universal_property` reduces
to sorry-free assembly from `descentThroughBirationalSigma`. -/

/-- **Connecting biconditional: Albanese-form equation ⇔ symmetric-power-form
equation.**

For every candidate descent morphism `ψ : Pic⁰_{C/k̄} ⟶ A`, the Albanese-form
factorisation `φ = abelJacobi C P₀ ≫ ψ` holds iff the symmetric-power-form
factorisation `symmetricPowerAVMap C (genus C) φ = symmetricPowerToJacobian
C P₀ (genus C) ≫ ψ` holds. The forward direction precomposes both sides of
the Albanese equation with the symmetric `g`-fold sum, then descends through
`π : C^g ⟶ Sym^g C` and uses the additivity of `ψ` (a homomorphism of group
schemes). The reverse direction restricts the symmetric-power-form equation
along the diagonal embedding `Q ↦ (Q, P₀, …, P₀)` and uses
`φ(P₀) = η_A`.

iter-200+: body uses the `Sym^g` projection π and its UP from
`Albanese/SymmetricPower.lean` (substrate file not yet opened),
together with the explicit Milne III §6 identification of `ι_{P₀}` with
the composite of `Q ↦ Q + (g - 1) P₀` followed by `f^{(g)}`. For the
iter-182 file-skeleton the body is a typed `sorry` — but the named
substantive helper exposes the precise connecting identity, allowing
`albanese_universal_property` to be assembled sorry-free from it. -/
theorem albanese_eq_iff_symmetricPower_eq
    (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C)
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (φ : C ⟶ A) (_hφ : P0 ≫ φ = η[A]) :
    ∀ (ψ : jacobianScheme C ⟶ A),
      (φ = abelJacobi C P0 ≫ ψ) ↔
      (symmetricPowerAVMap C (genus C) φ
        = symmetricPowerToJacobian C P0 (genus C) ≫ ψ) :=
  sorry

/-! ## §6. The Albanese universal property — headline theorem

The headline result of the chapter: for every pointed morphism
`φ : C ⟶ A` into an abelian variety `A` with `φ(P₀) = η_A`, there
exists a unique regular morphism `ψ : Pic⁰_{C/k̄} ⟶ A` such that
`φ = ψ ∘ ι_{P₀}`. The proof follows Milne Proposition III.6.1
verbatim, using the four sub-lemmas above plus Milne Theorem I.3.2
(`extend_to_av`) and Corollary I.1.2 (a `thm:rigidity_lemma`
consequence).

Blueprint reference: `thm:albanese_universal_property` (Milne,
*Abelian Varieties*, Proposition III.6.1, p. 104). -/

/-- **Albanese universal property of `Pic⁰_{C/k̄}` — Milne III §6
Proposition 6.1.**

For a complete nonsingular curve `C` of genus `g > 0` over an
algebraically closed field `k̄`, a marked `k̄`-point `P₀ ∈ C(k̄)`, and
every pointed morphism `φ : C ⟶ A` into an abelian variety `A` with
`φ(P₀) = η_A`, there exists a *unique* regular morphism
`ψ : Pic⁰_{C/k̄} ⟶ A` such that `φ = ι_{P₀} ≫ ψ`.

Proof sketch (Milne III.6.1):
1. **Symmetrisation.** `(P₁,…,P_g) ↦ φ(P₁) + ⋯ + φ(P_g)` is
   `S_g`-symmetric (`A` commutative), so factors through
   `Sym^g C` as `Sym^g φ` (`lem:symmetric_product_av_map`).
2. **Descent to a regular morphism on `J`.** The birational morphism
   `f^{(g)} : Sym^g C ⟶ Pic⁰_{C/k̄}` (`lem:symmetric_product_to_jacobian`)
   exhibits `Sym^g φ ∘ (f^{(g)})^{-1}` as a rational map
   `Pic⁰_{C/k̄} ⇢ A`, which by Milne Theorem I.3.2 extends uniquely to
   a regular morphism `ψ : Pic⁰_{C/k̄} ⟶ A`
   (`lem:descent_through_birational_sigma`).
3. **Factorisation `ψ ∘ ι_{P₀} = φ`.** Use Milne's identification of
   `ι_{P₀}` with the composite `Q ↦ Q + (g − 1) P₀` followed by
   `f^{(g)}`; together with `φ(P₀) = η_A` and the additive structure
   of `A`, this gives `ψ(ι_{P₀}(Q)) = φ(Q)` on `k̄`-points, hence
   globally by the reduced-and-separated agreement principle.
4. **Homomorphism property.** `ψ` sends `η_J = ι_{P₀}(P₀)` to
   `φ(P₀) = η_A`, so by Milne Corollary I.1.2 (a `thm:rigidity_lemma`
   consequence) it is a homomorphism of group schemes.
5. **Uniqueness.** Two homomorphisms `Pic⁰_{C/k̄} ⟶ A` with the same
   restriction to `ι_{P₀}(C)` agree on the `g`-fold sum
   `ι_{P₀}(C) + ⋯ + ι_{P₀}(C) = Pic⁰_{C/k̄}` (since `f^{(g)}` is
   surjective), hence are equal.

The iter-177 file-skeleton encodes only the existence-and-uniqueness
of the factoring morphism `ψ : Pic⁰_{C/k̄} ⟶ A` (matching the
project's `IsAlbanese` precedent in `Jacobian.lean`); the
group-homomorphism property is implicit in the construction. The body
consumes its four sub-lemma exports plus
`Scheme.RationalMap.extend_to_av` (A.4.c) and Milne Corollary I.1.2
(registered in `chap:AbelianVarietyRigidity`).

iter-182 update: structural decomposition lands the body as
sorry-free assembly from `descentThroughBirationalSigma` (§5)
combined with the named typed-`sorry` biconditional helper
`albanese_eq_iff_symmetricPower_eq` (§5.5). The remaining substantive
gaps (substrate files `Pic⁰` representability, `Sym^g C` construction,
`extend_to_av` rational-map extension, and the connecting biconditional
body itself) remain blocking and are deferred to iter-200+. -/
theorem albanese_universal_property
    (_hg : 0 < genus C)
    (P0 : 𝟙_ (Over (Spec (.of kbar))) ⟶ C)
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]
    (φ : C ⟶ A) (_hφ : P0 ≫ φ = η[A]) :
    ∃! (ψ : jacobianScheme C ⟶ A), φ = abelJacobi C P0 ≫ ψ := by
  -- Structural decomposition (iter-182): reduce to the symmetric-power
  -- descent `descentThroughBirationalSigma` plus the connecting
  -- biconditional `albanese_eq_iff_symmetricPower_eq`. The remaining
  -- substantive gap is the biconditional helper (named typed-sorry); the
  -- proof body below is sorry-free assembly.
  have key := albanese_eq_iff_symmetricPower_eq C P0 φ _hφ
  obtain ⟨ψ, hψ_sym, huniq_sym⟩ := descentThroughBirationalSigma C P0 φ _hφ
  exact ⟨ψ, (key ψ).mpr hψ_sym,
    fun ψ' hψ' => huniq_sym ψ' ((key ψ').mp hψ')⟩

end Pic0

end AlgebraicGeometry
