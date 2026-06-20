/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.Genus
import AlgebraicJacobian.Genus0BaseObjects
import AlgebraicJacobian.RigidityLemma

/-!
# The genus-`0` curve / `ℙ¹` isomorphism

This file hosts `genusZero_curve_iso_P1`: a smooth proper geometrically irreducible genus-`0`
curve `C` over an algebraically closed field `k̄` is isomorphic — in `Over (Spec (.of kbar))` —
to the concrete projective line `ProjectiveLineBar kbar`
(see `AlgebraicJacobian.Genus0BaseObjects.ProjectiveLineBar`). This is Hartshorne's
Example IV.1.3.5 and is the Riemann–Roch target consumed by the rational-curve chapter
(`AlgebraicJacobian.RiemannRoch.RationalCurveIso`).

## Encoding notes

Mathlib `b80f227` packages no `ℙ¹` as a `Scheme`, so the projective line is encoded by its
abstract characterisation: a smooth proper geometrically irreducible `Over (Spec (.of kbar))` of
relative dimension `1` with `genus = 0`. The signature is **provisional** (the body remains a
Riemann–Roch `sorry`); the prover may refine the encoding when the body is filled.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {kbar : Type u} [Field kbar]

/-- **A genus-`0` curve over `k̄` is isomorphic to `ℙ¹`.** Over an algebraically closed field
`k̄`, a smooth proper geometrically irreducible curve `C` with `genus C = 0` is isomorphic — in
`Over (Spec (.of kbar))` — to the concrete projective line `ProjectiveLineBar kbar`.

Hartshorne's Example IV.1.3.5 (Riemann–Roch). Its formalisation is a genuine sub-build:
Mathlib has no Riemann–Roch for curves; this is the dominant long pole flagged by the
iter-164 progress-critic.

See blueprint `prop:genusZero_curve_iso_P1`
(Hartshorne, *Algebraic Geometry*, Example IV.1.3.5).

**Status (iter-166):** signature refactored to the concrete `ProjectiveLineBar kbar`; body
remains `sorry` (RR bridge — iter-167+). -/
theorem genusZero_curve_iso_P1
    [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))}
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom] [GeometricallyIrreducible C.hom]
    (_hgenus : genus C = 0) :
    Nonempty (C ≅ ProjectiveLineBar kbar) :=
  sorry

end AlgebraicGeometry
