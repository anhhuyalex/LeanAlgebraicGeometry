/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Function-field pullback of a rational map

For a rational map `f : X ⤏ Y` out of an integral scheme `X`, Mathlib's
`AlgebraicGeometry.Scheme.RationalMap.fromFunctionField` gives a morphism
`Spec K(X) ⟶ Y` (the restriction of `f` to the generic point). Composing it with
`AlgebraicGeometry.Scheme.stalkClosedPointTo` produces the pullback of germs
`𝒪_{Y, f(η_X)} ⟶ K(X)` at the image of the generic point of `X`.

When `f` is **dominant** and `Y` is irreducible, that image point is the generic
point of `Y`, so the germ pullback becomes a field homomorphism
`K(Y) ⟶ K(X)` — the function-field functoriality `K(Y) → K(X)` that Milne's
rational-map extension leg (`Albanese/CodimOneExtension.lean`) and the
Weil-divisor obstruction (`thm:weil_divisor_obstruction`) both require.

## Main definitions

* `Scheme.RationalMap.stalkPullback` — the germ pullback
  `𝒪_{Y, f(η_X)} ⟶ K(X)` (no dominance needed).
* `Scheme.RationalMap.fromFunctionField_base_eq_genericPoint` — for a dominant
  rational map into an irreducible target, `f(η_X) = η_Y`.
* `Scheme.RationalMap.functionFieldPullback` — the induced field homomorphism
  `K(Y) ⟶ K(X)` for a dominant rational map.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

variable {X Y : Scheme.{u}}

/-- **Germ pullback along a rational map.** For a rational map `f : X ⤏ Y` out of
an integral scheme `X`, the associated morphism `f.fromFunctionField : Spec K(X) ⟶ Y`
induces, by `Scheme.stalkClosedPointTo`, a local ring homomorphism from the germ
of `Y` at the image `f(η_X)` of the generic point of `X` into the function field
`K(X)`. -/
noncomputable def stalkPullback [IsIntegral X] (f : X.RationalMap Y) :
    Y.presheaf.stalk (f.fromFunctionField (closedPoint X.functionField)) ⟶ X.functionField :=
  Scheme.stalkClosedPointTo f.fromFunctionField

/-!
## Dominant refinement (planned)

When `f` is **dominant** and `Y` is irreducible, the base point
`f.fromFunctionField (closedPoint K(X))` equals `genericPoint Y`, so `stalkPullback`
becomes a field homomorphism `K(Y) ⟶ K(X)`:

* `fromFunctionField_base_eq_genericPoint`: reduce to a representative `g` via
  `RationalMap.exists_rep` (`hdom : IsDominant g.hom` from
  `PartialMap.isDominant_toRationalMap_iff`); the composite
  `g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom`
  sends `closedPoint` to `genericPoint g.domain.toScheme` (identify the inner
  point via `Opens.fromSpecStalkOfMem_ι` + `Scheme.fromSpecStalk_closedPoint`,
  `g.domain.ι` injective; the domain's generic point via
  `genericPoint_eq_of_isOpenImmersion g.domain.ι`); then
  `(genericPoint_spec _).image g.hom.continuous` with `hdom.denseRange.closure_range`
  and `IsGenericPoint.eq` (schemes are T0) give `= genericPoint Y`.
* `functionFieldPullback := (Y.presheaf.stalkCongr (Inseparable.of_eq …)).hom ≫ f.stalkPullback`.

Two support obligations block a one-shot close and are the concrete remaining
work: `IrreducibleSpace g.domain.toScheme` (dense open of an integral scheme —
does not auto-synthesise; prove `Nonempty` from `dense_domain` and
`PreirreducibleSpace` from the ambient irreducibility) and the `↥g.domain` vs
`↥↑g.domain` Opens-carrier coercion when feeding `⟨genericPoint X, hx⟩` to
`g.hom`.
-/

end RationalMap

end Scheme

end AlgebraicGeometry
