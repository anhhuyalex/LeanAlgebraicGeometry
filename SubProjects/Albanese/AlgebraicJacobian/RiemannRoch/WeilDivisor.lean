/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Genus
import AlgebraicJacobian.Genus0BaseObjects
import AlgebraicJacobian.Albanese.CoheightBridge

/-!
# Weil divisors on a smooth proper curve (RR.1)

This file is the **RR.1** sub-build chapter for the project's headline
`genusZero_curve_iso_P1` (the "smooth proper geom-irred genus-`0` curve over `k̄` is
isomorphic to `ℙ¹`" lemma in `AlgebraicJacobian.AbelianVarietyRigidity`).

Mathlib `b80f227` ships no `WeilDivisor` on a scheme; adjacent pieces
(`MeromorphicOn.divisor`, `CommRing.Pic`, `Scheme.RationalMap`) cover different
ground. This file is therefore **project-bespoke**, scaffolding the formal-sum data
type `Div(X) = ⨁_{Y ⊂ X codim 1} ℤ` on a Noetherian integral scheme `X` satisfying
Hartshorne's condition `(*)`, the principal-divisor homomorphism
`div : K(X)^× → Div(X)` on a curve, the degree map `deg : Div(C) → ℤ` on a smooth
proper curve over an algebraically closed field, the degree-zero of principal divisors
on a complete nonsingular curve (Hartshorne Cor. II.6.10), and the linear-equivalence
relation `D ~ D'`.

## Status (iter-172 file-skeleton)

This file is the **iter-172 Lane C** file-skeleton: each declaration carries the
intended signature (matching the blueprint `\lean{...}` pin) with a `sorry` body.
The bodies are iter-173+ work after the sibling chapters `RR.2`
(`RiemannRoch_RRFormula.tex`), `RR.3` (`RiemannRoch_OcOfD.tex`), and `RR.4`
(`RiemannRoch_RationalIsoP1.tex`) land.

The 9 pinned declarations are:

1. `Scheme.WeilDivisor` — free abelian group on prime divisors (Definition).
2. `Scheme.RationalMap.order` — order of a rational function along a prime divisor.
3. `Scheme.WeilDivisor.ofClosedPoint` — Weil divisor associated to a closed point.
4. `Scheme.WeilDivisor.degree` — degree map over an algebraically closed base.
5. `Scheme.WeilDivisor.degree_hom` — degree is a group homomorphism (Theorem).
6. `Scheme.WeilDivisor.principal` — principal divisor of a rational function.
7. `Scheme.WeilDivisor.principal_hom` — `div` is a group homomorphism (Theorem).
8. `Scheme.WeilDivisor.principal_degree_zero` — `deg ∘ div = 0` on a complete curve.
9. `Scheme.WeilDivisor.LinearEquivalence` — linear equivalence of Weil divisors.

## References

Blueprint: `blueprint/src/chapters/RiemannRoch_WeilDivisor.tex` (445 LOC, 9 pins).
Hartshorne, *Algebraic Geometry*, II §6 (pp. 130–137 + IV.1 pp. 294–296).
Stacks Project, tags 02RW (divisors), 02ME (order at a point), 0BE0 (degree),
0BE3 (principal divisors have degree zero on a complete nonsingular curve).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## §1. Codim-1 cycle group / Weil divisor group

Hartshorne's condition `(*)` (II §6, p. 130) is: `X` is a Noetherian integral
separated scheme that is regular in codimension one. Under `(*)`, prime divisors
are closed integral subschemes of codimension one, and the local ring at the
generic point of a prime divisor is a DVR with quotient field the function field
`K(X)`.

A prime divisor is encoded by its **generic point** together with the
codimension-one witness `Order.coheight point = 1`: the data field `point : X`
selects the generic point of the closed integral subscheme, and the predicate
field `coheight` enforces codimension one in the specialisation preorder
(Hartshorne II §6 p. 130; blueprint pin `def:prime_divisor`). Integrality of the
closure is automatic, so no separate integrality witness is needed.
-/

/-- A **prime divisor** on a scheme `X`: a closed integral subscheme of codimension
one, encoded (for a scheme satisfying Hartshorne's condition `(*)`) by its generic
point. On a curve, prime divisors correspond bijectively to closed points.

The codimension-one witness is the predicate `Order.coheight point = 1` on the
specialisation preorder of `X.carrier` (Mathlib's convention is
`x ≤ y ↔ y ⤳ x`, so the generic point is the unique maximal element and a
generic point of a codim-1 closed integral subscheme has a length-one chain
above it). The closure `{point}̄` is automatically irreducible (so the reduced
induced subscheme structure is automatically integral); hence no separate
integrality field is needed.

Blueprint reference: `def:prime_divisor` / `def:codim1_cycles` (Hartshorne II §6
p. 130; Stacks 02RW). -/
structure Scheme.PrimeDivisor (X : Scheme.{u}) where
  /-- The generic point of the closed integral subscheme. -/
  point : X
  /-- Codimension-1 witness: `point` has coheight `1` in the specialisation
  preorder on `X.carrier`. Per iter-173 `wd-spec-refine` (`def:prime_divisor`). -/
  coheight : Order.coheight point = 1

/-- The **Weil divisor group** of a scheme `X` satisfying Hartshorne's condition
`(*)`: the free abelian group on the set of prime divisors of `X`,
`Div(X) = ⨁_{Y prime divisor of X} ℤ · Y`. An element `D = Σ nᵢ · Yᵢ` with finitely
many nonzero coefficients is a **Weil divisor**; if all `nᵢ ≥ 0` it is **effective**.

Blueprint reference: `def:codim1_cycles` (Hartshorne II §6 p. 130). -/
def Scheme.WeilDivisor (X : Scheme.{u}) : Type u := X.PrimeDivisor →₀ ℤ

namespace Scheme.WeilDivisor

noncomputable instance (X : Scheme.{u}) : AddCommGroup X.WeilDivisor :=
  inferInstanceAs (AddCommGroup (X.PrimeDivisor →₀ ℤ))

instance (X : Scheme.{u}) : Inhabited X.WeilDivisor :=
  inferInstanceAs (Inhabited (X.PrimeDivisor →₀ ℤ))

end Scheme.WeilDivisor

/-! ## Project-local Mathlib supplement — PrimeDivisor open-immersion bridge

Iter-200 Lane WD-A4a Sub-build 1 substrate (per `analogies/wd-stacks02iz.md`
and `task_results/mathlib-analogist-wd-stacks02iz.md`): on top of the existing
project-side `AlgebraicJacobian.Albanese.CoheightBridge`
(`Order.coheight_eq_of_isOpenEmbedding`, axiom-clean iter-183) we package the
PrimeDivisor-level open-immersion bijection used by future RR.1 / A.4.a
substrate work.

The four declarations are:
- `Scheme.PrimeDivisor.restrictToOpen` — given a prime divisor `Y` of `X` and
  `Y.point ∈ U`, the corresponding prime divisor of the open subscheme `U`.
- `Scheme.PrimeDivisor.ofOpen` — push a prime divisor of an open subscheme `U`
  back to a prime divisor of the ambient scheme `X`.
- `Scheme.PrimeDivisor.equivOpen` — the bijection
  `{ Y : X.PrimeDivisor // Y.point ∈ U } ≃ U.toScheme.PrimeDivisor`.
- `Scheme.PrimeDivisor.stalkIso` — the stalk identification along the
  open immersion `U.ι : U.toScheme ⟶ X`, a thin wrapper around Mathlib's
  `AlgebraicGeometry.Scheme.Opens.stalkIso`.

References: Stacks 02IZ (open-immersion stalks), Stacks 005X (coheight ↔ Krull
dim on Noetherian schemes); iter-183 substrate at
`AlgebraicJacobian/Albanese/CoheightBridge.lean`.
-/

namespace Scheme.PrimeDivisor

variable {X : Scheme.{u}}

/-- **Extensionality for `Scheme.PrimeDivisor`.** Two prime divisors with
the same underlying point are equal (the coheight witness is a `Prop`-valued
field, so it carries no data). Useful for the round-trip lemmas of the
`equivOpen` bijection below. -/
@[ext]
lemma ext {Y Y' : X.PrimeDivisor} (h : Y.point = Y'.point) : Y = Y' := by
  cases Y; cases Y'
  congr

end Scheme.PrimeDivisor

end AlgebraicGeometry

/-! ## Project-local Mathlib supplement — `Ring.ordFrac` naturality

Iter-201 Lane WD-A4a Sub-build 2 (HARD BAR + extras). Naturality of
`Ring.ord`, `Ring.ordMonoidWithZeroHom`, and `Ring.ordFrac` (Mathlib's
`K →*₀ ℤᵐ⁰` from `Mathlib.RingTheory.OrderOfVanishing.Basic`) across a ring
isomorphism `e : R ≃+* S` between commutative rings, lifted to a compatible
fraction-field isomorphism `e_K : Frac R ≃+* Frac S`.

This is the algebraic substrate consumed by iter-202+ Sub-build 3
(scheme-level `Scheme.RationalMap.order` naturality across the iter-200
`Scheme.PrimeDivisor.stalkIso` open-immersion bridge), which in turn closes
the non-zero branch of `rationalMap_order_finite_support` (the L535 sorry).

References: Stacks 02RV (Hartshorne II.6.1), Stacks 02ME (DVR-of-stalk
characterisation at codim-1 points), Stacks 02IZ (stalk under open
immersion), Stacks 02MD (Mathlib's `Ring.ordFrac` / `Ring.ord` API).
-/

namespace Ring

end Ring

namespace AlgebraicGeometry

/-! ## Project-local Mathlib supplement — Function field iso for open immersions

Iter-201 Lane WD-A4a Sub-build 2 PUSH-BEYOND (step (2) per PROGRESS.md
L122--L138): canonical iso `U.toScheme.functionField ≅ X.functionField` for
integral `X` and nonempty open `U ⊆ X`, obtained by composing Mathlib's
`Scheme.Opens.stalkIso U (genericPoint U.toScheme)` with the transport across
the genericPoint equality `(U.ι (genericPoint U.toScheme)) = genericPoint X`
delivered by `genericPoint_eq_of_isOpenImmersion`.

This iso is the bridge that lets `Ring.ordFrac_ringEquiv` apply at the
scheme level (with `e_K = Scheme.Opens.functionFieldIso U` and `e =
Scheme.PrimeDivisor.stalkIso U Y hYU` for a prime divisor `Y` of `X` with
`Y.point ∈ U`). The full IsFractionRing-compatibility lemma chaining the
two isos is iter-202+ Sub-build 3 scope.

Reference: Mathlib `AlgebraicGeometry.FunctionField.genericPoint_eq_of_isOpenImmersion`
+ iter-200 `Scheme.PrimeDivisor.stalkIso` wrapper. -/

namespace Scheme.RationalMap

/-- **Order of a nonzero rational function `f ∈ K(X)^×` along a prime divisor `Y`.**

For `X` satisfying Hartshorne's `(*)`, the local ring `O_{X,η}` at the generic
point `η` of `Y` is a discrete valuation ring with quotient field the function
field `K(X)`, and `ord_Y(f) = v_Y(f) ∈ ℤ` is the value of the associated normalised
discrete valuation on `f`.

On a smooth proper curve `C` over `k̄`, every closed point `P ∈ C` is a prime
divisor and `ord_P(f) = v_P(f)` is the standard DVR valuation at `P`.

Blueprint reference: `def:order_at_point` (Hartshorne II §6 pp. 130–131; Stacks 02ME).

iter-176 body (per analogist `dvr-rationalmap-order`): the body uses Mathlib's
`Ring.ordFrac` (the canonical `K →*₀ ℤᵐ⁰` monoid-with-zero hom from
`Mathlib.RingTheory.OrderOfVanishing.Basic`, Stacks `02MD`) on the stalk
`X.presheaf.stalk Y.point`, then projects through `WithZero.log : ℤᵐ⁰ → ℤ`
(the canonical projection with junk-on-zero, `Mathlib.Algebra.GroupWithZero.WithZero`).
On `f = 0` this gives `order Y 0 = 0` (junk convention from `WithZero.log_zero`).

The required Mathlib typeclasses on the stalk are:
- `IsNoetherianRing` — from `[IsLocallyNoetherian X]`.
- `IsDomain` ⟹ `Nontrivial` — from `[IsIntegral X]`.
- `IsFractionRing (X.presheaf.stalk Y.point) X.functionField` — from `[IsIntegral X]`.
- `Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)` — threaded explicitly (the
  topological-coheight-to-Krull-dim bridge `Order.coheight Y.point = 1 ⟹
  Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)` is a Mathlib-upstream-pending
  gap; see Stacks `02IZ` / `005X`). -/
noncomputable def order {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    (f : X.functionField) : ℤ :=
  WithZero.log (Ring.ordFrac (X.presheaf.stalk Y.point) f)

end Scheme.RationalMap

/-! ### Regular-in-codimension-one bridge class

Hartshorne's condition `(*)` includes "regular in codimension one", i.e.\ every
prime divisor `Y` of `X` has a DVR stalk `O_{X,Y.point}`. Mathlib has no direct
typeclass for this; we package it as the project-bespoke class
`Scheme.IsRegularInCodimensionOne`, with an instance synthesising the per-`Y`
Krull-dim-≤-1 condition required by `Scheme.RationalMap.order`. Blueprint pin
("Iter-173+ may introduce a `Scheme.IsRegularInCodimensionOne` predicate to
abbreviate this"; chapter `RiemannRoch_WeilDivisor.tex` §2 "Standing hypothesis
`(*)` in the Lean encoding"). -/

/-- Project-bespoke class encoding Hartshorne's "regular in codimension one"
clause of `(*)`: every prime divisor `Y` of `X` has a DVR stalk
`O_{X,Y.point}`. The `[IsIntegral X]` precondition makes
`IsDomain (X.presheaf.stalk Y.point)` available so that the
`IsDiscreteValuationRing` predicate is well-formed
(`AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegral`). -/
class Scheme.IsRegularInCodimensionOne (X : Scheme.{u}) [IsIntegral X] : Prop where
  /-- The defining content: every prime divisor's stalk is a discrete valuation
  ring. (This is the precise content of Hartshorne's `(*)`; the weaker
  `Ring.KrullDimLE 1` derives via the `IsDiscreteValuationRing` ⟹
  `IsPrincipalIdealRing` ⟹ `Ring.KrullDimLE 1` chain via the bridge
  instance below.) -/
  out : ∀ Y : Scheme.PrimeDivisor X, IsDiscreteValuationRing (X.presheaf.stalk Y.point)

/-- Bridge instance: from `[Scheme.IsRegularInCodimensionOne X]`, typeclass
synthesis can derive `IsDiscreteValuationRing (X.presheaf.stalk Y.point)` for
every prime divisor `Y`. -/
instance Scheme.IsRegularInCodimensionOne.instIsDiscreteValuationRingStalk
    {X : Scheme.{u}} [IsIntegral X] [Scheme.IsRegularInCodimensionOne X]
    (Y : Scheme.PrimeDivisor X) :
    IsDiscreteValuationRing (X.presheaf.stalk Y.point) :=
  Scheme.IsRegularInCodimensionOne.out Y

/-- Bridge instance: from `[Scheme.IsRegularInCodimensionOne X]`, typeclass
synthesis can derive `Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)` for every
prime divisor `Y`, via the `IsDiscreteValuationRing` ⟹ `IsPrincipalIdealRing`
⟹ `Ring.KrullDimLE 1` chain (Mathlib's `IsDiscreteValuationRing.toIsPrincipalIdealRing`
+ `IsPrincipalIdealRing.krullDimLE_one`). -/
instance Scheme.IsRegularInCodimensionOne.instKrullDimLEStalk
    {X : Scheme.{u}} [IsIntegral X] [Scheme.IsRegularInCodimensionOne X]
    (Y : Scheme.PrimeDivisor X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk Y.point) :=
  haveI : IsDiscreteValuationRing (X.presheaf.stalk Y.point) :=
    Scheme.IsRegularInCodimensionOne.out Y
  haveI : IsPrincipalIdealRing (X.presheaf.stalk Y.point) :=
    IsDiscreteValuationRing.toIsPrincipalIdealRing
  IsPrincipalIdealRing.krullDimLE_one _

/-- `ord_Y 0 = 0` by the junk-on-zero convention.

Direct from `Ring.ordFrac _` being a monoid-with-zero hom (`map_zero`)
and `WithZero.log_zero`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_zero
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)] :
    Scheme.RationalMap.order Y (0 : X.functionField) = 0 := by
  unfold Scheme.RationalMap.order
  rw [map_zero, WithZero.log_zero]

/-- **Hartshorne II.6.1**: for a nonzero rational function `f` on a Noetherian
integral scheme `X` satisfying `(*)`, the order function `Y ↦ ord_Y(f)` is
nonzero at only finitely many prime divisors `Y`. This is the well-definedness
side condition for `Scheme.WeilDivisor.principal`.

iter-177 status: this packages Hartshorne's Lemma 6.1, which Mathlib does not
ship. The body is a Mathlib-upstream-pending gap (Stacks tag `02RV` — for a
nonzero element `f ∈ K(X)^×` of a Noetherian integral scheme, only finitely
many height-one primes can divide either numerator or denominator); the proof
factors through `IsLocallyNoetherian X` + the principal-ideal generation of
height-1 primes + the finite irreducible-component decomposition of
`V(f₀) ∪ V(f∞)`. The chapter pins this as a separate sub-build deferral
(`RiemannRoch_WeilDivisor.tex` §5).

The statement is generic in `f` (no `f ≠ 0` hypothesis is threaded): on
`f = 0` the function `Y ↦ ord_Y(0) = WithZero.log 0 = 0` has empty support,
which is finite, so the conclusion holds vacuously. -/
private theorem rationalMap_order_finite_support {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    (f : X.functionField) :
    (Function.support (fun Y : X.PrimeDivisor =>
      Scheme.RationalMap.order Y f)).Finite := by
  -- **iter-192 case split + f = 0 branch closed axiom-clean.**
  --
  -- Case 1 (f = 0): the order function evaluates to
  -- `WithZero.log (Ring.ordFrac _ 0) = WithZero.log 0 = 0` at every
  -- prime divisor, so the support is empty (finite vacuously).
  -- iter-198 cleanup: use `Scheme.RationalMap.order_zero` for clarity.
  by_cases hf : f = 0
  · subst hf
    convert Set.finite_empty
    ext Y
    simp only [Function.mem_support, ne_eq, Set.mem_empty_iff_false, iff_false,
      Decidable.not_not, Scheme.RationalMap.order_zero]
  -- Case 2 (f ≠ 0): genuinely needs Hartshorne II.6.1 (Stacks 02RV).
  --
  -- **iter-198 structural-blocker note (Lane WD-A4a HARD BAR pause).**
  -- The mathematical proof (Stacks 02RV / Hartshorne II.6.1 / Bourbaki AC VII.1)
  -- requires **global** Noetherian-ness of `X` as a topological space, NOT only
  -- locally Noetherian. The argument:
  --   (a) Pick a nonempty affine open `U ⊂ X`. Then `R := Γ(U, O_X)` is a
  --       Noetherian integral domain (by `[IsLocallyNoetherian X]` +
  --       `[IsIntegral X]`); `K(X) = Frac(R)`; write `f = a/b`.
  --   (b) Prime divisors `Y` with `Y.point ∈ U` and `ord_Y f ≠ 0` are bounded
  --       by minimal primes of the ideal `(a·b) ⊂ R`, which is FINITE by
  --       `Ideal.finite_minimalPrimes_of_isNoetherianRing`.
  --   (c) Prime divisors `Y` with `Y.point ∉ U` correspond to irreducible
  --       components of the closed set `X \ U` of codimension 1 in `X`. For
  --       this to be finite, `X \ U` must be a Noetherian topological space —
  --       which holds iff `X` is itself globally Noetherian (= locally
  --       Noetherian + quasi-compact via `AlgebraicGeometry.isNoetherian_iff`).
  --
  -- The current signature has only `[IsLocallyNoetherian X]`; without
  -- `[CompactSpace X]` (equivalently `[IsNoetherian X]`), case (c) cannot be
  -- bounded — a counter-example is any non-quasi-compact integral locally
  -- Noetherian scheme with infinitely many codim-1 irreducible components
  -- disjoint from `U`.
  --
  -- The Mathlib analogue for the Dedekind-domain case is
  -- `IsDedekindDomain.HeightOneSpectrum.Support.finite` (for `k ∈ Frac(R)`,
  -- the height-1 primes with nonzero adic valuation form a finite set).
  -- Adapting it to schemes requires the affine-chart bridge `ord_Y(f) ≠ 0
  -- iff height-1 prime `(asIdeal Y) ⊂ R` is in the divisor of `(a·b)`'.
  --
  -- **Resolution path** (iter-199+): strengthen the typeclass to
  -- `[IsNoetherian X]` (propagating to `principal`, `principal_apply`,
  -- `principal_hom`, `LinearEquivalence`, `principal_degree_zero`,
  -- `degree_positivePart_principal_eq_finrank`) and close (a)+(b)+(c) via
  -- the affine-chart + Dedekind bridge above. The propagation is mechanical
  -- — `Over.left` of a proper morphism is automatically `CompactSpace`, so
  -- the curve-side consumers `principal_degree_zero` and
  -- `degree_positivePart_principal_eq_finrank` derive `[IsNoetherian C.left]`
  -- for free from `[IsProper C.hom]`. This pathway is gated by USER directive
  -- Route C PAUSE on those declarations; the actual signature strengthening
  -- is iter-199+ work after USER approval.
  · sorry

namespace Scheme.WeilDivisor

variable {X : Scheme.{u}}

/-! ## §3. Divisor of a closed point on a curve

On a smooth proper curve `C` over a field, every closed point `P ∈ C` is a prime
divisor (it is closed, integral, of codimension one in the one-dimensional integral
scheme `C`). The associated Weil divisor is `[P] = 1 · P ∈ Div(C)`. -/

/-- **The principal divisor of a nonzero rational function `f ∈ K(X)^×`.**

By Hartshorne's Lemma 6.1, `ord_Y(f) = 0` for all but finitely many prime
divisors `Y`, so the formal sum
`div(f) := Σ_{Y prime divisor} ord_Y(f) · Y ∈ Div(X)`
has finite support and is a well-defined Weil divisor.

On a smooth proper curve `C` over `k̄`, this specialises to
`div(f) = Σ_{P closed point} ord_P(f) · [P]`.

Blueprint reference: `def:principal_divisor` (Hartshorne II §6 Lemma 6.1 +
following definition, p. 131).

iter-177 body: the construction uses `Finsupp.ofSupportFinite` with the
finite-support witness `rationalMap_order_finite_support`. The latter is a
private theorem packaging Hartshorne 6.1; its body is a Mathlib-pending gap
(see chapter `RiemannRoch_WeilDivisor.tex` §5 sub-build note) and is left as
a `sorry` for an iter-178+ Mathlib-upstream PR. -/
noncomputable def principal [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X] (f : X.functionField)
    (_hf : f ≠ 0) : X.WeilDivisor :=
  Finsupp.ofSupportFinite
    (fun Y : X.PrimeDivisor => Scheme.RationalMap.order Y f)
    (rationalMap_order_finite_support f)

end Scheme.WeilDivisor

end AlgebraicGeometry
