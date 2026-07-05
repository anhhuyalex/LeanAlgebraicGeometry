/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.RationalMapPrecomp
import AlgebraicJacobian.Albanese.RationalMapProd

/-!
# Milne's difference rational map `Φ = (x, y) ↦ f(x) · f(y)⁻¹`

This file assembles **Sub-step 1** of Milne's Lemma 3.3
(`indeterminacy_pure_codim_one_into_grpScheme`, `Albanese/CodimOneExtension.lean`):
from a rational map `f : X ⤏ G` into a group variety over an algebraically closed
field `k̄`, build the *difference rational map*

  `Φ : X ×_{k̄} X ⤏ G`,   `Φ(x, y) = f(x) · f(y)⁻¹`,

which is the vehicle for reducing the indeterminacy of `f` to a pole-divisor
computation on the nonsingular surface `X ×_{k̄} X`.

The construction glues the two rational-map bricks already in the project:

* `Scheme.RationalMap.precomp` (`Albanese/RationalMapPrecomp.lean`) — precompose
  `f` with the two projections `prᵢ : X ×_{k̄} X ⟶ X`, which are open because
  `X.hom` is smooth (hence its base change `prᵢ` is smooth, flat, locally of finite
  presentation, universally open, an open map);
* `Scheme.RationalMap.prod` (`Albanese/RationalMapProd.lean`) — pair
  `f ∘ pr₁` and `f ∘ pr₂` into `X ×_{k̄} X ⤏ G ×_{k̄} G`;

and then composes on the right with the **group-object difference morphism**
`GrpObj.diff G = (g, h) ↦ g · h⁻¹ : G ⊗ G ⟶ G`, whose underlying scheme morphism
`(GrpObj.diff G).left : G ×_{k̄} G ⟶ G` is the honest group law `m ∘ (id × inv)`.

The pairing `prod` requires the source `X ×_{k̄} X` to be integral; this is passed
as the hypothesis `[IsIntegral (pullback X.hom X.hom)]`. The caller supplies it via
the project lemma `isReduced_of_smooth_of_isAlgClosed` (self-product is smooth over
`k̄`, hence reduced) together with `GeometricallyIrreducible.irreducibleSpace` — the
`isIntegral_pullback_self` recipe is spelled out in the module note below and lives
in `CodimOneExtension.lean`'s cone (it depends on the standard-smooth chart machinery
there, so it is not restated here to keep this file a Mathlib-only leaf).

## Main definitions

* `CategoryTheory.GrpObj.diff` — the division morphism `G ⊗ G ⟶ G` of a group
  object in any cartesian-monoidal category.
* `AlgebraicGeometry.grpObjDiffLeft` — its underlying scheme morphism, typed as
  `pullback G.hom G.hom ⟶ G.left`.
* `AlgebraicGeometry.Scheme.RationalMap.differenceRationalMap` — Milne's
  `Φ : X ×_{k̄} X ⤏ G`.

## Main results

* `AlgebraicGeometry.isOpenMap_pullback_fst_self` / `..._snd_self` — the two
  projections of the self-product are open maps.
* `AlgebraicGeometry.Scheme.RationalMap.differenceRationalMap_compHom_over` — the
  difference map is a `k̄`-rational map (`Φ.compHom G.hom = (pr₁ ≫ X.hom).toRat`).

Sub-steps 2 (`(x, x) ∈ Dom Φ ↔ x ∈ Dom f`) and 4b (diagonal codim-1 Krull bound)
remain; they consume `differenceRationalMap` built here.
-/

set_option autoImplicit false

universe u

open CategoryTheory CartesianMonoidalCategory MonoidalCategory Limits TopologicalSpace
open scoped CategoryTheory.MonObj

namespace CategoryTheory.GrpObj

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

/-- **Difference / division morphism of a group object.** For a group object `G`
in a cartesian-monoidal category, `GrpObj.diff G = fst / snd : G ⊗ G ⟶ G` is the
morphism `(g, h) ↦ g · h⁻¹`, i.e. the group law composed with inversion on the
second factor. There is no ready-made such morphism in mathlib (`GrpObj.conj` and
`GrpObj.commutator` are the only prebuilt `G ⊗ G ⟶ G` maps), so we build it from
the hom-set group structure `CategoryTheory.MonObj.Hom.group`. -/
noncomputable def diff (G : C) [GrpObj G] : G ⊗ G ⟶ G :=
  fst G G / snd G G

end CategoryTheory.GrpObj

namespace AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

/-- The underlying scheme morphism `(GrpObj.diff G).left : G ×_{k̄} G ⟶ G` of the
group-object difference morphism, typed directly against `pullback G.hom G.hom`
(definitionally `(G ⊗ G).left` via `Over.tensorObj_left`). This coercion avoids the
`(G ⊗ G).left` vs `pullback G.hom G.hom` transparency wall when right-composing a
rational map with target `pullback G.hom G.hom`. -/
noncomputable def grpObjDiffLeft (G : Over (Spec (.of kbar))) [GrpObj G] :
    pullback G.hom G.hom ⟶ G.left :=
  (GrpObj.diff G).left

/-- The difference morphism sits over `Spec k̄`: `grpObjDiffLeft G ≫ G.hom =
pr₁ ≫ G.hom`. This is the reduction that turns `Φ.compHom G.hom` into the structure
morphism of `X ×_{k̄} X`; it is `Over.w` of `GrpObj.diff G`. -/
lemma grpObjDiffLeft_comp_hom (G : Over (Spec (.of kbar))) [GrpObj G] :
    grpObjDiffLeft G ≫ G.hom = pullback.fst G.hom G.hom ≫ G.hom :=
  Over.w (GrpObj.diff G)

/-- The first projection `X ×_{k̄} X ⟶ X` is an open map (it is smooth, being a
base change of the smooth structure morphism, hence universally open). -/
theorem isOpenMap_pullback_fst_self (X : Over (Spec (.of kbar))) [Smooth X.hom] :
    IsOpenMap (pullback.fst X.hom X.hom).base :=
  (pullback.fst X.hom X.hom).isOpenMap

/-- The second projection `X ×_{k̄} X ⟶ X` is an open map. -/
theorem isOpenMap_pullback_snd_self (X : Over (Spec (.of kbar))) [Smooth X.hom] :
    IsOpenMap (pullback.snd X.hom X.hom).base :=
  (pullback.snd X.hom X.hom).isOpenMap

namespace Scheme.RationalMap

variable {X G : Over (Spec (.of kbar))}
  [Smooth X.hom]
  [GrpObj G] [LocallyOfFiniteType G.hom]

/-- **Milne's difference rational map** `Φ = (x, y) ↦ f(x) · f(y)⁻¹`.

For a rational map `f : X ⤏ G` into a group variety over `k̄`, with `f` defined
over `k̄` (`f.compHom G.hom = X.hom.toRationalMap`), the difference map
`Φ : X ×_{k̄} X ⤏ G` is `((f ∘ pr₁) ×_{k̄} (f ∘ pr₂)) ∘ (g, h ↦ g · h⁻¹)`.

The self-product must be integral for the pairing `prod` to be well-defined; this
is the hypothesis `[IsIntegral (pullback X.hom X.hom)]`. -/
noncomputable def differenceRationalMap
    (f : X.left.RationalMap G.left)
    (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] :
    (pullback X.hom X.hom).RationalMap G.left :=
  (RationalMap.prod (pullback.fst X.hom X.hom ≫ X.hom) G.hom G.hom
      (f.precomp (pullback.fst X.hom X.hom) (isOpenMap_pullback_fst_self X))
      (f.precomp (pullback.snd X.hom X.hom) (isOpenMap_pullback_snd_self X))
      (by rw [RationalMap.precomp_compHom, hover, RationalMap.precomp_hom_toRationalMap])
      (by rw [RationalMap.precomp_compHom, hover, RationalMap.precomp_hom_toRationalMap,
        pullback.condition])).compHom (grpObjDiffLeft G)

/-- **The difference map is a `k̄`-rational map.** Right-composing `Φ` with the
structure morphism `G.hom` recovers the structure morphism `pr₁ ≫ X.hom` of
`X ×_{k̄} X`. -/
theorem differenceRationalMap_compHom_over
    (f : X.left.RationalMap G.left)
    (hover : f.compHom G.hom = X.hom.toRationalMap)
    [IsIntegral (pullback X.hom X.hom)] :
    (differenceRationalMap f hover).compHom G.hom
      = (pullback.fst X.hom X.hom ≫ X.hom).toRationalMap := by
  simp only [differenceRationalMap]
  rw [RationalMap.compHom_compHom, grpObjDiffLeft_comp_hom]
  exact RationalMap.prod_compHom_over _ _ _ _ _ _ _

end Scheme.RationalMap

end AlgebraicGeometry
