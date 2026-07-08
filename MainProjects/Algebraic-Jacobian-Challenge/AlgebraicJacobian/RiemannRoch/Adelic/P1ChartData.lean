/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.RiemannRoch.Adelic.FinitenessP1

/-!
# The `ℙ¹` chart-ring computation: discharging `P1HasLaurentChartData` (node `N11b`)

**STATUS: WORK-IN-PROGRESS — NOT YET REGISTERED in `AlgebraicJacobian.lean`.**
This module is not imported by the library root, so the default `lake build` target
does not compile it; it therefore cannot break the fleet baseline.  Declarations here
are checked with the lean-LSP loop (`lean_diagnostic_messages` + `lean_verify`, clean
axioms `[propext, Classical.choice, Quot.sound]`); a final faithful
`lake build AlgebraicJacobian.RiemannRoch.Adelic.P1ChartData` was not run to completion
because the build host was catastrophically oversubscribed during authoring
(load average > 200 on 16 cores, cross-tenant workloads).

This file is intended to compute the standard-chart Laurent data of the concrete
projective line `ℙ¹ = ℙ(ULift (Fin 2); Spec k)` (the `Proj`-pullback model of
`Picard/ProjectiveSpace.lean`), the datum consumed by the adelic keystone
`Adelic.LaurentChartData.module_finite_H1Cok` (`FinitenessP1.lean`), and thereby to
discharge the gate `Adelic.P1HasLaurentChartData`.

## The reduction (route map for a future wave)

The geometric substrate — the two affine charts `Vᵢ = D₊(Xᵢ)` (pulled back to the
model), their affineness, and the covering property — is already assembled as
`Adelic.p1CoverSquare` (`FinitenessP1.lean`).  What remains is the chart-ring content
of `Adelic.LaurentChartData`:

1. **Coordinate sections.**  `x = X₁/X₀ ∈ Γ(V₀)`, `y = X₀/X₁ ∈ Γ(V₁)`, defined as
   pullbacks along `ProjectiveSpace.toProjInt` of the away-section fractions:
   `x := (toProjInt.app D₊(X₀)).hom ((Proj.awayToSection 𝒜 (X ⟨0⟩)).hom (p1CoordAway ⟨0⟩ ⟨1⟩))`,
   and symmetrically `y` at `⟨1⟩`.  (`p1CoordAway i j = Xⱼ/Xᵢ ∈ Away 𝒜 (Xᵢ)` below.)

2. **Overlap identities** `V₀ ⊓ V₁ = D(x) = D(y)` and `x · y = 1`.  On the overlap
   `D₊(X₀X₁)` the pullbacks of `x, y` restrict, by naturality of `Scheme.Hom.app`
   and `Proj.awayMap_awayToSection`, to the images of `awayFraction ⟨1⟩ ⟨0⟩ = X₁/X₀`
   and `awayFraction ⟨0⟩ ⟨1⟩ = X₀/X₁` in `Away 𝒜 (X₀X₁)`, whose product is `1`
   (`ProjTwist.awayFraction_mul_inv`).  The basic-open identities follow from
   `Scheme.preimage_basicOpen` together with the `Proj`-side computation of the basic
   open of the away fraction (its non-vanishing locus inside `D₊(Xᵢ)` is `D₊(XᵢXⱼ)`).

3. **Chart spanning** `Γ(V₀) = k[x]`, `Γ(V₁) = k[y]` (the fields `span_pow_x/y`).
   The mathematical heart.  Two routes:
   * (Route A, char-restricted) Flat base change `02KE`
     (`QuotScheme.pullback_baseMap_sectionLinearEquiv_of_quasiCompact`, CLOSED) gives
     `Γ(V₀) ≃ₗ[k] k ⊗_ℤ Away 𝒜 (X₀)`.  It requires `[Flat (Spec k ↘ ⊤)]`, i.e. `k`
     flat over `ℤ`, i.e. `k` torsion-free — TRUE only in characteristic `0`.  So this
     route discharges the gate only for `[CharZero k]`.
   * (Route B, char-free — preferred) The chart preimage is the pullback
     `Spec k ×_{⊤} D₊(Xᵢ) = Spec (k ⊗_ℤ Away 𝒜 (Xᵢ))` (restrict the defining pullback
     square `ProjectiveSpace.isPullback_map`/`of_hasPullback` over the affine `D₊(Xᵢ)`;
     product of affines over the terminal `⊤ = Spec (ULift ℤ)` is `Spec` of the tensor —
     no flatness needed).  Read off `Γ(V₀) ≅ k ⊗_ℤ Away 𝒜 (X₀)` directly.
   In either case the span reduces, by `k ⊗_ℤ (−)` base change of `Submodule.span`, to
   the **`ℤ`-span core**: `Away 𝒜 (Xᵢ)` is `(𝒜 0)`-spanned by the powers of the
   coordinate fraction `p1CoordAway ⟨0⟩ ⟨1⟩`.  Proof by `HomogeneousLocalization`
   induction: an away element is `Away.mk 𝒜 hX₀ n p hp` with `p ∈ 𝒜 n` homogeneous of
   degree `n` in two variables, hence `p = Σ_{b≤n} c_b · X₀^{n-b} X₁^b`
   (`MvPolynomial.as_sum` + homogeneity forcing `d₀ + d₁ = n` on the support), so
   `p / X₀^n = Σ_b c_b · (X₁/X₀)^b` in the localization.

## Assembly

With 1–3 in hand, `Adelic.LaurentChartData (Over.mk (ℙ¹ ↘ Spec k))` is populated from
`p1CoverSquare`'s fields plus the above, and
`instance : P1HasLaurentChartData k := ⟨⟨…⟩⟩` discharges the gate (for `[CharZero k]`
via Route A, or for every field via Route B).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.Adelic

/-! ## The single-chart coordinate fractions `Xⱼ/Xᵢ ∈ (ℤ[X]_{Xᵢ})₀` -/

section CoordAway

variable (n : Type u)

/-- The coordinate fraction `Xⱼ/Xᵢ` as an element of the degree-zero away ring
`(ℤ[X]_{Xᵢ})₀ = Away 𝒫[n] Xᵢ` of the integral model (numerator `Xⱼ`, denominator
`Xᵢ`, both homogeneous of degree `1`).  On the chart `V₀` the coordinate is
`X₁/X₀ = p1CoordAway ⟨0⟩ ⟨1⟩`; on `V₁` it is `X₀/X₁ = p1CoordAway ⟨1⟩ ⟨0⟩`.

UNVERIFIED (see the module header): the `1 • 1 = 1` grading obligation is discharged
by `simpa`, but no elaboration/kernel check has been run under the current host load. -/
noncomputable def p1CoordAway (i j : n) :
    Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) :=
  Away.mk _ (ProjTwist.X_mem_deg_one n i) 1 (X j)
    (by simpa using ProjTwist.X_mem_deg_one n j)

end CoordAway

/-! ## The coordinate sections on the `ℙ¹` model

The coordinates `x, y` of `Adelic.LaurentChartData` on the concrete model
`ℙ¹ = ℙ(ULift (Fin 2); Spec k)` are the pullbacks along `ProjectiveSpace.toProjInt`
of the away-section fractions `X₁/X₀`, `X₀/X₁`.  Restriction target opens are
`p1Chart k ⟨0⟩ = toProjInt ⁻¹ᵁ D₊(X₀)` and `p1Chart k ⟨1⟩ = toProjInt ⁻¹ᵁ D₊(X₁)`
(definitionally, from `FinitenessP1.p1Chart`). -/

section CoordSection

variable (k : Type u) [Field k]

/-- The coordinate `x = X₁/X₀ ∈ Γ(V₀)` on the first chart of the `ℙ¹` model,
pulled back from the away section `X₁/X₀ ∈ Away 𝒫 X₀` along `toProjInt`. -/
noncomputable def p1XSection :
    Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨0⟩) :=
  ((ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).app
      (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨0⟩))).hom
    ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X ⟨0⟩)).hom (p1CoordAway (ULift.{u} (Fin 2)) ⟨0⟩ ⟨1⟩))

/-- The coordinate `y = X₀/X₁ ∈ Γ(V₁)` on the second chart of the `ℙ¹` model,
pulled back from the away section `X₀/X₁ ∈ Away 𝒫 X₁` along `toProjInt`. -/
noncomputable def p1YSection :
    Γ(ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), p1Chart k ⟨1⟩) :=
  ((ProjectiveSpace.toProjInt (ULift.{u} (Fin 2)) (Spec (CommRingCat.of k))).app
      (Proj.basicOpen (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)) (X ⟨1⟩))).hom
    ((Proj.awayToSection (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
        (X ⟨1⟩)).hom (p1CoordAway (ULift.{u} (Fin 2)) ⟨1⟩ ⟨0⟩))

end CoordSection

end AlgebraicGeometry.Adelic
