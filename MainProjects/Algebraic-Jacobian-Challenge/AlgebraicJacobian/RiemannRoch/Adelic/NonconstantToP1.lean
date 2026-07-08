/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.RiemannRoch.Adelic.FiniteMapToP1
import AlgebraicJacobian.Picard.ProjectiveSpace

/-!
# Reducing the nonconstant-map gate to the integral `Proj` model (node `N9a`)

This file peels the *base-change / over-`k` layer* off the last open gate of the
adelic finite-map chain, `Adelic.ExistsNonconstantMapToP1` (`FiniteMapToP1.lean`,
node `N9a`).  That gate asks for a nonconstant `k`-morphism into the concrete
projective line
`ℙ¹_k = ℙ(ULift (Fin 2); Spec k)`, which by construction
(`Picard/ProjectiveSpace.lean`) is the base change of the **integral model**
`Proj ℤ[X₀, X₁] = Proj (homogeneousSubmodule (ULift (Fin 2)) (ULift ℤ))` along the
terminal map `Spec k ⟶ ⊤_ Scheme`:
```
ℙ¹_k  =  Spec k  ×_{⊤}  Proj ℤ[X₀, X₁].
```

Because `ℙ¹_k` is a fibre product over the *terminal* object, the pullback
compatibility square is discharged automatically (any two morphisms into `⊤_
Scheme` agree), so the universal property of the pullback turns a bare scheme
morphism `C ⟶ Proj ℤ[X₀, X₁]` — with **no** over-`k` or terminal bookkeeping —
together with the ambient structure map `C ⟶ Spec k` into a genuine `k`-morphism
`C ⟶ ℙ¹_k`.  Nonconstancy transfers verbatim: the projection
`ℙ¹_k ⟶ Proj ℤ[X₀, X₁]` (`ProjectiveSpace.toProjInt`) sends the built morphism
back to the given one, so two distinct point-images upstairs force two distinct
point-images downstairs.

## Main results

* `Adelic.ExistsNonconstantMapToProjInt C` — the **cleaner residual gate**: a
  nonconstant scheme morphism `C.left ⟶ Proj ℤ[X₀, X₁]` (two distinct
  point-images), phrased entirely inside the concrete integral `Proj` model where
  `P1ChartData.lean` already computes the standard chart coordinates
  `x = X₁/X₀`, `y = X₀/X₁`.
* `Adelic.existsNonconstantMapToP1_of_nonconstantMapToProjInt` — the **bridge
  theorem** (reusable constructor): any nonconstant `C.left ⟶ Proj ℤ[X₀, X₁]`
  yields `ExistsNonconstantMapToP1 C`, via `pullback.lift` + terminal
  uniqueness.
* `Adelic.existsNonconstantMapToP1_of_existsNonconstantMapToProjInt` — the
  derived instance discharging `ExistsNonconstantMapToP1 C` from the cleaner gate,
  so the whole finite-map chain now bottoms out at `ExistsNonconstantMapToProjInt`.

## The remaining honest crux (why the `Proj` gate is not yet an instance)

`ExistsNonconstantMapToProjInt C` is the genuine one-dimensional curve theory:
a smooth proper geometrically integral curve `C/k` carries a nonconstant rational
function (`k(C)/k` has transcendence degree one), which spreads out
(`RationalMap.ofFunctionField`) to a rational map `C ⤏ Proj ℤ[X₀, X₁]` and then
extends to an everywhere-defined morphism by the valuative criterion applied at
the codimension-one DVR stalks (`Albanese/CodimOneExtension.lean`,
`indeterminacy_codimGe2_of_smooth_of_complete` +
`existsUnique_hom_of_indeterminacyLocus_eq_empty`, with the curve input
`coheight_le_one_of_curve` of `FiniteMapToP1.lean`).  The obstruction to landing
this as an instance *right now* is that both the DVR-stalk step
(`localRing_dvr_of_codim_one`) and the codim-≥2 extension are currently proved
only over an **algebraically closed** base field (the smooth ⟹ regular pipeline of
`SmoothPrimeRegularity.lean` lands the perfect / algebraically-closed cases), and
the concrete `K(C)`-point of `Proj ℤ[X₀, X₁]` needs the chart-ring identification
`Away 𝒜 X₀ = ℤ[X₁/X₀]` that `P1ChartData.lean` (Route B) has not yet landed.  This
file isolates exactly that residual content in the `Proj`-model gate above.

Blueprint node: `thm:adelic_exists_finiteMorphismToP1` (gate `N9a`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry.Adelic

variable {k : Type u} [Field k]

/-- **The residual nonconstant-map gate at the integral `Proj` model (node `N9a`).**
A single-field `Prop` class asserting the existence of a nonconstant scheme
morphism from the curve `C` to the integral model of the projective line
`Proj ℤ[X₀, X₁] = Proj (homogeneousSubmodule (ULift (Fin 2)) (ULift ℤ))`
(nonconstant = two distinct point-images).

This is the base-change-free heart of `ExistsNonconstantMapToP1`: the over-`k`
structure and the fibre-product-over-terminal bookkeeping have been discharged in
`existsNonconstantMapToP1_of_nonconstantMapToProjInt`, so what remains is the
genuine curve theory (a nonconstant rational function that extends by the
valuative criterion — see the module header).  The class carries **no
instance**. -/
class ExistsNonconstantMapToProjInt (C : Over (Spec (CommRingCat.of k))) : Prop where
  /-- There exists a nonconstant scheme morphism `C ⟶ Proj ℤ[X₀, X₁]`. -/
  exists_nonconstant_map :
    ∃ f : C.left ⟶ Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)),
      ∃ x₁ x₂ : C.left, f x₁ ≠ f x₂

/-- **The base-change bridge (node `N9a` discharge, reusable constructor).**
Any nonconstant scheme morphism `f : C.left ⟶ Proj ℤ[X₀, X₁]` into the integral
model of the projective line yields the finite-map gate input
`ExistsNonconstantMapToP1 C`.

`ℙ¹_k = Spec k ×_{⊤} Proj ℤ[X₀, X₁]` is a fibre product over the terminal object,
so the compatibility square for `pullback.lift` collapses to the uniqueness of
morphisms into `⊤_ Scheme`; the lift of the ambient structure map `C ↘ Spec k`
and of `f` is a `k`-morphism `C ⟶ ℙ¹_k` whose composite with the projection
`ProjectiveSpace.toProjInt` back to `Proj ℤ[X₀, X₁]` is `f` again, so the two
distinct point-images of `f` are preserved. -/
theorem existsNonconstantMapToP1_of_nonconstantMapToProjInt
    (C : Over (Spec (CommRingCat.of k)))
    (f : C.left ⟶ Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ)))
    (hf : ∃ x₁ x₂ : C.left, f x₁ ≠ f x₂) :
    ExistsNonconstantMapToP1 C := by
  obtain ⟨x₁, x₂, hx⟩ := hf
  -- The compatibility square lives over the terminal object, hence is automatic.
  have hcomm : C.hom ≫ terminal.from (Spec (CommRingCat.of k))
      = f ≫ terminal.from (Proj (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))) :=
    Subsingleton.elim _ _
  -- The lift into `ℙ¹_k = Spec k ×_{⊤} Proj ℤ[X₀, X₁]`.
  let g : C.left ⟶ ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) :=
    pullback.lift C.hom f hcomm
  have hfst : g ≫ (ℙ(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)) = C.hom := by
    rw [ProjectiveSpace.over_eq_fst]; exact pullback.lift_fst _ _ _
  have hsnd : g ≫ ProjectiveSpace.toProjInt (ULift.{u} (Fin 2))
      (Spec (CommRingCat.of k)) = f := by
    rw [ProjectiveSpace.toProjInt_eq_snd]; exact pullback.lift_snd _ _ _
  -- Package as a `k`-morphism and transfer nonconstancy through `toProjInt`.
  refine ⟨⟨Over.homMk g hfst, x₁, x₂, ?_⟩⟩
  simp only [Over.homMk_left]
  intro hg
  apply hx
  rw [← hsnd, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact congrArg _ hg

/-- **The finite-map gate through the cleaner `Proj`-model gate (node `N9a`).**
`ExistsNonconstantMapToP1 C` follows from the base-change-free gate
`ExistsNonconstantMapToProjInt C`, so the adelic finite-map chain now bottoms out
at the concrete integral `Proj` model. -/
instance (priority := 100) existsNonconstantMapToP1_of_existsNonconstantMapToProjInt
    (C : Over (Spec (CommRingCat.of k))) [ExistsNonconstantMapToProjInt C] :
    ExistsNonconstantMapToP1 C := by
  obtain ⟨f, hf⟩ := ExistsNonconstantMapToProjInt.exists_nonconstant_map (C := C)
  exact existsNonconstantMapToP1_of_nonconstantMapToProjInt C f hf

end AlgebraicGeometry.Adelic
