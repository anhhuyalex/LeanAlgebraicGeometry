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

/-- **PrimeDivisor restriction along an open immersion.** Given a prime
divisor `Y` of `X` whose generic point lies in an open `U ⊆ X`, the
corresponding prime divisor of the open subscheme `U.toScheme`. The
codimension-one witness transports via `Order.coheight_eq_of_isOpenEmbedding`
(iter-183 project substrate, Stacks 02IZ topological side). -/
def restrictToOpen (U : X.Opens) (Y : X.PrimeDivisor)
    (hYU : Y.point ∈ U) : U.toScheme.PrimeDivisor where
  point := ⟨Y.point, hYU⟩
  coheight := by
    rw [← Y.coheight]
    exact (Order.coheight_eq_of_isOpenEmbedding U.isOpen Y.point hYU).symm

/-- **PrimeDivisor extension from an open subscheme.** A prime divisor of an
open subscheme `U.toScheme` lifts to a prime divisor of the ambient `X` along
the open immersion `U.ι`. Codimension-one is preserved via the same
`Order.coheight_eq_of_isOpenEmbedding` bridge, this time in the forward
direction. -/
def ofOpen (U : X.Opens) (YU : U.toScheme.PrimeDivisor) :
    X.PrimeDivisor where
  point := YU.point.1
  coheight := by
    rw [Order.coheight_eq_of_isOpenEmbedding U.isOpen YU.point.1 YU.point.2]
    exact YU.coheight

@[simp]
lemma restrictToOpen_point (U : X.Opens) (Y : X.PrimeDivisor)
    (hYU : Y.point ∈ U) :
    (restrictToOpen U Y hYU).point = ⟨Y.point, hYU⟩ := rfl

@[simp]
lemma ofOpen_point (U : X.Opens) (YU : U.toScheme.PrimeDivisor) :
    (ofOpen U YU).point = YU.point.1 := rfl

/-- **Bijection between prime divisors of `X` lying inside `U` and prime
divisors of `U.toScheme`.** The forward map is
`Y ↦ Scheme.PrimeDivisor.restrictToOpen U Y.val Y.property`; the inverse is
`Scheme.PrimeDivisor.ofOpen U`. Both maps are coheight-preserving by
`Order.coheight_eq_of_isOpenEmbedding`. -/
def equivOpen (U : X.Opens) :
    { Y : X.PrimeDivisor // Y.point ∈ U } ≃ U.toScheme.PrimeDivisor where
  toFun Y := restrictToOpen U Y.1 Y.2
  invFun YU := ⟨ofOpen U YU, YU.point.2⟩
  left_inv := by
    rintro ⟨Y, hY⟩
    rfl
  right_inv := by
    intro YU
    rfl

/-- **Stalk identification along an open immersion at a prime divisor.** A
thin wrapper around Mathlib's `AlgebraicGeometry.Scheme.Opens.stalkIso`
specialised to the underlying carrier of a prime divisor `Y` lifted from
the open subscheme. Stacks 02IZ stalk side. -/
noncomputable def stalkIso (U : X.Opens) (Y : X.PrimeDivisor)
    (hYU : Y.point ∈ U) :
    U.toScheme.presheaf.stalk (restrictToOpen U Y hYU).point ≅
      X.presheaf.stalk Y.point :=
  AlgebraicGeometry.Scheme.Opens.stalkIso U ⟨Y.point, hYU⟩

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

/-- **`Ring.ord` naturality under a ring isomorphism.**
`ord R x = ord S (e x)`. The length of `R/(x)` as `R`-module equals the
length of `S/(e x)` as `S`-module: the `R`-linear equivalence
`R/(x) ≃ₗ[R] S/(e x)` (with the `S`-side equipped with `R`-module structure
via `e`) transports length across rings using `Module.length_eq_of_surjective`.

Project-local because Mathlib `b80f227` ships no `ord` naturality lemma. -/
private lemma ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : R) : Ring.ord R x = Ring.ord S (e x) := by
  have heq : Ideal.span ({e x} : Set S) = Ideal.map (e : R →+* S) (Ideal.span {x}) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  letI alg : Algebra R S := e.toRingHom.toAlgebra
  haveI : IsScalarTower R S (S ⧸ Ideal.span ({e x} : Set S)) := by
    refine ⟨fun r s m => ?_⟩
    change (algebraMap R S r * s) • m = (algebraMap R S r) • (s • m)
    rw [mul_smul]
  let φ_ring : (R ⧸ Ideal.span ({x} : Set R)) ≃+* (S ⧸ Ideal.span ({e x} : Set S)) :=
    Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e heq
  let φ : (R ⧸ Ideal.span ({x} : Set R)) ≃ₗ[R] (S ⧸ Ideal.span ({e x} : Set S)) := by
    refine { φ_ring.toAddEquiv with map_smul' := ?_ }
    intro r m
    induction m using Quotient.inductionOn with
    | h y =>
      change Ideal.Quotient.mk _ (e (r * y)) = e r • Ideal.Quotient.mk _ (e y)
      rw [map_mul]; rfl
  unfold Ring.ord
  rw [φ.length_eq]
  exact Module.length_eq_of_surjective (S := R) (R := S) (M := S ⧸ Ideal.span {e x})
    e.surjective

/-- **`nonZeroDivisors` is preserved by a ring isomorphism.** Direct from
Mathlib's `MulEquivClass.map_nonZeroDivisors`. Project-local convenience
wrapper to phrase the result as an `Iff` instead of a `Submonoid.map` equality. -/
private lemma nonZeroDivisors_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (r : R) :
    r ∈ nonZeroDivisors R ↔ e r ∈ nonZeroDivisors S := by
  rw [← MulEquivClass.map_nonZeroDivisors (e : R ≃* S)]
  refine ⟨fun h => ⟨r, h, rfl⟩, fun h => ?_⟩
  obtain ⟨r', hr', heq⟩ := h
  have : r = r' := e.injective heq.symm
  rw [this]; exact hr'

/-- **`Ring.ordMonoidWithZeroHom` naturality under a ring isomorphism.**
`ordMonoidWithZeroHom S (e r) = ordMonoidWithZeroHom R r`. Reduces to
`ord_ringEquiv` after splitting on `r ∈ nonZeroDivisors R`. -/
private lemma ordMonoidWithZeroHom_ringEquiv {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [Nontrivial S] (e : R ≃+* S) (r : R) :
    Ring.ordMonoidWithZeroHom S (e r) = Ring.ordMonoidWithZeroHom R r := by
  unfold Ring.ordMonoidWithZeroHom
  simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  by_cases hr : r ∈ nonZeroDivisors R
  · have her : e r ∈ nonZeroDivisors S := (nonZeroDivisors_ringEquiv e r).mp hr
    simp [hr, her, ord_ringEquiv e r]
  · have her : e r ∉ nonZeroDivisors S := fun h =>
      hr ((nonZeroDivisors_ringEquiv e r).mpr h)
    simp [hr, her]

/-- **`Ring.ordFrac` naturality** — iter-201 Lane WD-A4a Sub-build 2 HARD BAR
(per PROGRESS.md L108--L122 recipe step (1)).

Given a ring iso `e : R ≃+* S` between Noetherian Krull-dim-`≤ 1` integral
domains and a compatible fraction-field iso `e_K : K_R ≃+* K_S` (compatibility
`e_K (algebraMap R K_R r) = algebraMap S K_S (e r)` for `r : R`), the
order-of-vanishing function on the fraction fields is invariant:
`ordFrac S (e_K x) = ordFrac R x` for any `x : K_R`.

Proof: `x = 0` is the junk-zero branch. For `x ≠ 0`, write `x = mk' K_R a b`
with `a, b ∈ nonZeroDivisors R` via `IsLocalization.surj`. Then
`e_K x = mk' K_S (e a) (e b)` via the compatibility hypothesis, and both
sides reduce via Mathlib's `ordFrac_eq_div` to a quotient of
`ordMonoidWithZeroHom`-values, which agree by `ordMonoidWithZeroHom_ringEquiv`. -/
private lemma ordFrac_ringEquiv {R S : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    {K_R K_S : Type*} [Field K_R] [Field K_S]
    [Algebra R K_R] [IsFractionRing R K_R]
    [Algebra S K_S] [IsFractionRing S K_S]
    (e : R ≃+* S) (e_K : K_R ≃+* K_S)
    (h_compat : ∀ r : R, e_K (algebraMap R K_R r) = algebraMap S K_S (e r))
    (x : K_R) :
    Ring.ordFrac S (e_K x) = Ring.ordFrac R x := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero, map_zero, map_zero]
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hb_nzd : (b : R) ∈ nonZeroDivisors R := b.2
  have hb_ne : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_nzd
  have h_inj_R : Function.Injective (algebraMap R K_R) := IsFractionRing.injective R K_R
  have hb_K_ne : algebraMap R K_R (b : R) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K_R), h_inj_R.eq_iff]
    exact hb_ne
  have ha_ne : a ≠ 0 := by
    intro ha
    subst ha
    rw [map_zero] at hab
    rcases mul_eq_zero.mp hab with hx' | hb_ne'
    · exact hx hx'
    · exact hb_K_ne hb_ne'
  have ha_nzd : a ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero ha_ne
  have he_b_nzd : e b ∈ nonZeroDivisors S := (nonZeroDivisors_ringEquiv e b).mp hb_nzd
  have he_a_nzd : e a ∈ nonZeroDivisors S := (nonZeroDivisors_ringEquiv e a).mp ha_nzd
  have hx_mk : x = IsLocalization.mk' K_R a ⟨b, hb_nzd⟩ := by
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, hab]
  have he_K_x : e_K x = IsLocalization.mk' K_S (e a) ⟨e b, he_b_nzd⟩ := by
    rw [eq_comm]
    refine (IsLocalization.mk'_eq_iff_eq_mul).mpr ?_
    rw [← h_compat a, ← h_compat b, ← map_mul]
    exact congrArg e_K hab.symm
  rw [he_K_x, hx_mk]
  rw [Ring.ordFrac_eq_div S ⟨e a, he_a_nzd⟩ ⟨e b, he_b_nzd⟩]
  rw [Ring.ordFrac_eq_div R ⟨a, ha_nzd⟩ ⟨b, hb_nzd⟩]
  congr 1
  · exact ordMonoidWithZeroHom_ringEquiv e a
  · exact ordMonoidWithZeroHom_ringEquiv e b

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

/-- **Function field isomorphism along an open immersion** (iter-201 Lane
WD-A4a Sub-build 2 PUSH-BEYOND). For an integral scheme `X` and a nonempty
open subscheme `U ⊆ X`, the function fields of `U.toScheme` and `X` are
canonically isomorphic. -/
noncomputable def Scheme.Opens.functionFieldIso {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    (U.toScheme).functionField ≅ X.functionField :=
  (Scheme.Opens.stalkIso U (genericPoint U.toScheme)).trans
    (X.presheaf.stalkCongr (by
      have heq : ((genericPoint U.toScheme : U.toScheme.carrier).val : X.carrier) =
          genericPoint X :=
        genericPoint_eq_of_isOpenImmersion U.ι
      rw [heq]
      exact Inseparable.refl _))

/-! ## §2. Order of a rational function at a prime divisor

For a scheme `X` satisfying `(*)`, every prime divisor `Y` carries a discrete
valuation `v_Y` on the function field `K(X)`. The order of a nonzero rational
function `f ∈ K(X)^×` along `Y` is the integer `ord_Y(f) := v_Y(f)`. -/

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

/-- **Open-immersion descent for `IsRegularInCodimensionOne`** (iter-200 Lane
WD-A4a Sub-build 1 PUSH-BEYOND). The codim-1 regularity hypothesis transports
along the open immersion `U.ι : U.toScheme ⟶ X`: prime divisors of `U.toScheme`
push to prime divisors of `X` via `Scheme.PrimeDivisor.ofOpen`, and Mathlib's
`Scheme.Opens.stalkIso` gives the ring iso between stalks. We then transport
the `IsDiscreteValuationRing` property via
`IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`.

References: Stacks 02IZ (open-immersion stalks), iter-183 project substrate
in `AlgebraicJacobian/Albanese/CoheightBridge.lean`. -/
instance Scheme.IsRegularInCodimensionOne.instOpen
    {X : Scheme.{u}} [IsIntegral X] [Scheme.IsRegularInCodimensionOne X]
    (U : X.Opens) [IsIntegral U.toScheme] :
    Scheme.IsRegularInCodimensionOne U.toScheme := by
  refine ⟨fun YU => ?_⟩
  haveI hY : IsDiscreteValuationRing (X.presheaf.stalk YU.point.1) :=
    Scheme.IsRegularInCodimensionOne.out (Scheme.PrimeDivisor.ofOpen U YU)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (AlgebraicGeometry.Scheme.Opens.stalkIso U YU.point).symm.commRingCatIsoToRingEquiv

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

/-- **Compactness of the total space of a proper `S`-scheme over a compact base**
(iter-002 Lane WD-A4a M1 substrate, PROGRESS.md objective 2). For a proper
morphism `C.hom : C.left ⟶ S` over a compact base `S`, the total space `C.left`
is a compact topological space: a proper morphism is quasi-compact, and a
quasi-compact morphism to a compact space has compact source
(`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`).

This is the instance that lets the curve-side consumers (`principal`,
`principal_degree_zero`, `degree_positivePart_principal_eq_finrank`) and their
cross-file callers discharge the new `[CompactSpace C.left]` hypothesis of
`rationalMap_order_finite_support` for free from `[IsProper C.hom]` over the
compact base `Spec k̄`. -/
instance instCompactSpaceLeftOfIsProper {S : Scheme.{u}} [CompactSpace S]
    {C : CategoryTheory.Over S} [IsProper C.hom] : CompactSpace C.left :=
  QuasiCompact.compactSpace_of_compactSpace C.hom

/-- **Scheme-side packaging of `Ring.ordFrac_ringEquiv` for the open-immersion
PrimeDivisor stalk iso** (iter-201 Lane WD-A4a Sub-build 2 PUSH-BEYOND
packaging).

This is the iter-202+ Sub-build 3 entry point: it pipes the iter-200
`Scheme.PrimeDivisor.stalkIso U Y hYU` ring iso plus a user-supplied
function-field iso `e_K` (typically the `Scheme.Opens.functionFieldIso U`)
and a compatibility hypothesis `h_compat` into the algebraic naturality
`Ring.ordFrac_ringEquiv`.

The full Sub-build 3 closure replaces `e_K` with `Scheme.Opens.functionFieldIso U`
and discharges `h_compat` from the naturality of `Scheme.Opens.stalkIso` w.r.t.
`stalkSpecializes` to the generic point. That naturality lemma is iter-202
scope (it requires either a `Scheme.Hom.stalkSpecializes_stalkMap` analogue or a
direct germ-universal chase via Mathlib's
`AlgebraicGeometry.Scheme.Opens.germ_stalkIso_hom_assoc`). -/
private theorem Scheme.PrimeDivisor.ordFrac_stalkIso_naturality
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [Scheme.IsRegularInCodimensionOne X]
    (U : X.Opens) [Nonempty U] [IsIntegral U.toScheme]
    [Scheme.IsRegularInCodimensionOne U.toScheme]
    (Y : X.PrimeDivisor) (hYU : Y.point ∈ U)
    (e_K : U.toScheme.functionField ≃+* X.functionField)
    (h_compat : ∀ r : U.toScheme.presheaf.stalk
        (Scheme.PrimeDivisor.restrictToOpen U Y hYU).point,
      e_K (algebraMap _ U.toScheme.functionField r) =
        algebraMap _ X.functionField
          ((Scheme.PrimeDivisor.stalkIso U Y hYU).commRingCatIsoToRingEquiv r))
    (f : U.toScheme.functionField) :
    Ring.ordFrac (X.presheaf.stalk Y.point) (e_K f) =
      Ring.ordFrac (U.toScheme.presheaf.stalk
        (Scheme.PrimeDivisor.restrictToOpen U Y hYU).point) f :=
  Ring.ordFrac_ringEquiv
    (Scheme.PrimeDivisor.stalkIso U Y hYU).commRingCatIsoToRingEquiv
    e_K h_compat f

/-! ## Project-local Mathlib supplement — Sub-build 3 closure of `h_compat`

Iter-202 Lane WD-A4a Sub-build 3 (HARD BAR, both steps). We discharge the
`h_compat` hypothesis of `Scheme.PrimeDivisor.ordFrac_stalkIso_naturality`
with `e_K := Scheme.Opens.functionFieldIso U`, producing the user-facing
naturality `Scheme.PrimeDivisor.order_eq_order_restrict`:
`order Y (functionFieldIso U f) = order (restrictToOpen U Y hYU) f`.

Step 1 is the morphism-level commutativity in `CommRingCat`
(`Scheme.PrimeDivisor.functionFieldIso_compat`): the two ways of mapping the
stalk of `U.toScheme` at `Y` into `X.functionField` — first specialise to the
generic point of `U` then apply `functionFieldIso`, vs. first apply the
open-immersion `stalkIso` then specialise to the generic point of `X` —
agree. The proof is a germ-chase via `TopCat.Presheaf.stalk_hom_ext`,
`germ_stalkSpecializes`, and `Scheme.Opens.germ_stalkIso_hom`.

Reference: Stacks 02IZ (open-immersion stalks) + Mathlib's
`TopCat.Presheaf.germ_stalkSpecializes` + `Scheme.Opens.germ_stalkIso_hom`.
-/

/-- **Morphism-level compatibility for the function-field iso** (iter-202 Lane
WD-A4a Sub-build 3, step 1). For an integral scheme `X`, a nonempty integral
open `U`, and a prime divisor `Y` of `X` with `Y.point ∈ U`, the square
```
  stalk_U Y  --stalkSpec_U-->  functionField U
      |                              |
   stalkIso                     functionFieldIso
      v                              v
  stalk_X Y  --stalkSpec_X-->  functionField X
```
commutes in `CommRingCat`, where the horizontal maps are the canonical
`stalkSpecializes` maps to the respective generic points (i.e. the algebra
maps `O_{·,Y} → K(·)`). -/
theorem Scheme.PrimeDivisor.functionFieldIso_compat {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] [IsIntegral U.toScheme]
    (Y : X.PrimeDivisor) (hYU : Y.point ∈ U) :
    U.toScheme.presheaf.stalkSpecializes
        ((genericPoint_spec U.toScheme).specializes (Set.mem_univ
          (Scheme.PrimeDivisor.restrictToOpen U Y hYU).point)) ≫
        (Scheme.Opens.functionFieldIso U).hom =
      (Scheme.PrimeDivisor.stalkIso U Y hYU).hom ≫
        X.presheaf.stalkSpecializes
          ((genericPoint_spec X).specializes (Set.mem_univ Y.point)) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hxV
  have hcongr : ∀ {a b : X} (e : Inseparable a b),
      (X.presheaf.stalkCongr e).hom = X.presheaf.stalkSpecializes e.ge := by
    intros; rfl
  simp only [Scheme.PrimeDivisor.stalkIso, Scheme.Opens.functionFieldIso, Iso.trans_hom,
    restrictToOpen_point, hcongr]
  simp only [TopCat.Presheaf.germ_stalkSpecializes_assoc,
    Scheme.Opens.germ_stalkIso_hom_assoc]
  exact (TopCat.Presheaf.germ_stalkSpecializes _ _ _).trans
    (TopCat.Presheaf.germ_stalkSpecializes _ _ _).symm

/-- **Naturality of `Scheme.RationalMap.order` across the function-field iso**
(iter-202 Lane WD-A4a Sub-build 3, step 2 — the HARD BAR endpoint). For an
integral locally-Noetherian scheme `X` regular in codimension one, a nonempty
integral open `U`, a prime divisor `Y` of `X` with `Y.point ∈ U`, and a
rational function `f` of `U.toScheme`, the order of the transported function
`functionFieldIso U f` along `Y` equals the order of `f` along the restricted
prime divisor `restrictToOpen U Y hYU`. This is the user-facing closure
consumer of Sub-build 2's `ordFrac_stalkIso_naturality`, with `h_compat`
discharged by the morphism-level `functionFieldIso_compat`. -/
theorem Scheme.PrimeDivisor.order_eq_order_restrict {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    (U : X.Opens) [Nonempty U] [IsIntegral U.toScheme]
    (Y : X.PrimeDivisor) (hYU : Y.point ∈ U)
    (f : U.toScheme.functionField) :
    Scheme.RationalMap.order Y
        ((Scheme.Opens.functionFieldIso U).commRingCatIsoToRingEquiv f) =
      Scheme.RationalMap.order (Scheme.PrimeDivisor.restrictToOpen U Y hYU) f := by
  have hcompat : ∀ r : U.toScheme.presheaf.stalk
      (Scheme.PrimeDivisor.restrictToOpen U Y hYU).point,
      (Scheme.Opens.functionFieldIso U).commRingCatIsoToRingEquiv
          (algebraMap _ U.toScheme.functionField r) =
        algebraMap _ X.functionField
          ((Scheme.PrimeDivisor.stalkIso U Y hYU).commRingCatIsoToRingEquiv r) := by
    intro r
    have hM := Scheme.PrimeDivisor.functionFieldIso_compat U Y hYU
    have happ := congrArg (fun φ => (CommRingCat.Hom.hom φ) r) hM
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at happ
    exact happ
  unfold Scheme.RationalMap.order
  rw [Scheme.PrimeDivisor.ordFrac_stalkIso_naturality U Y hYU
      (Scheme.Opens.functionFieldIso U).commRingCatIsoToRingEquiv hcompat f]

/-! ### Order-on-curve algebraic identities

iter-198 §2 substrate lemmas (Lane WD-A4a PUSH-BEYOND). These are
axiom-clean per-prime-divisor algebraic identities on
`Scheme.RationalMap.order` — direct consequences of `Ring.ordFrac` being
a `K →*₀ ℤᵐ⁰` monoid-with-zero hom composed with `WithZero.log : ℤᵐ⁰ → ℤ`
(which is additive on nonzero arguments, junk-zero on `0`).

The lemmas:

- `Scheme.RationalMap.order_zero`: `ord_Y 0 = 0` (junk convention).
- `Scheme.RationalMap.order_mul_of_ne_zero`: `ord_Y (f·g) = ord_Y f +
  ord_Y g` when both `f, g ≠ 0`.
- `Scheme.RationalMap.order_units_inv`: `ord_Y u⁻¹ = -ord_Y u` for a
  unit `u : K(X)ˣ`.

Blueprint reference: `def:order_at_point` §2 (Hartshorne II §6 valuation
identities `v_Y(fg) = v_Y(f)+v_Y(g)`, `v_Y(f⁻¹) = -v_Y(f)`, `v_Y(1) = 0`). -/

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

/-- `ord_Y (f · g) = ord_Y f + ord_Y g` when `f, g ≠ 0`.

Direct from `Ring.ordFrac _` being a monoid-with-zero hom (`map_mul`)
and `WithZero.log_mul` (which requires both factors nonzero). -/
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_mul_of_ne_zero
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    Scheme.RationalMap.order Y (f * g) =
      Scheme.RationalMap.order Y f + Scheme.RationalMap.order Y g := by
  unfold Scheme.RationalMap.order
  rw [map_mul]
  exact WithZero.log_mul ((map_ne_zero _).mpr hf) ((map_ne_zero _).mpr hg)

/-- `ord_Y f⁻¹ = -ord_Y f` for any `f : K(X)`.

The `f = 0` case is junk-vacuous (`f⁻¹ = 0` in a `GroupWithZero`, both sides
are zero). For `f ≠ 0` this is the DVR-valuation identity `v(f⁻¹) = -v(f)`.

Direct from `Ring.ordFrac _` being a monoid-with-zero hom (`map_inv₀`)
and `WithZero.log_inv` (which holds for all `WithZero (Multiplicative G)`
elements including zero, by the junk-on-zero convention). -/
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_inv
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    (f : X.functionField) :
    Scheme.RationalMap.order Y f⁻¹ = -Scheme.RationalMap.order Y f := by
  unfold Scheme.RationalMap.order
  rw [map_inv₀, WithZero.log_inv]

/-- `ord_Y u⁻¹ = -ord_Y u` for a unit `u : K(X)ˣ`.

A specialisation of `order_inv` to the unit form
`((u⁻¹ : K(X)ˣ) : K(X)) = (u : K(X))⁻¹`, useful at call sites that thread
`Units` (e.g. the `principal_hom : K(X)ˣ →* Multiplicative Div(X)` body). -/
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_units_inv
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    (u : (X.functionField)ˣ) :
    Scheme.RationalMap.order Y ((u⁻¹ : (X.functionField)ˣ) : X.functionField) =
      -Scheme.RationalMap.order Y (u : X.functionField) := by
  rw [show ((u⁻¹ : (X.functionField)ˣ) : X.functionField) =
        (u : X.functionField)⁻¹ from by simp]
  exact Scheme.RationalMap.order_inv Y _

/-- **`ord_Y (-f) = ord_Y f`** for any rational function `f`.

The argument: `(-f)^2 = f^2`, so taking `ordFrac` (a monoid-with-zero hom) and
then `WithZero.log_pow` gives `2 • ord_Y (-f) = 2 • ord_Y f` in `ℤ`. The free
action `(· • ·) : ℕ → ℤ → ℤ` cancels `2 ≠ 0`, giving the equality.

iter-199 §2 substrate sharpening (Lane WD-A4a PUSH-BEYOND). Foundational
sign-flip identity for downstream consumers (Hartshorne II.6.10 non-constant
branch, ramification-inertia chase). -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_neg
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    (f : X.functionField) :
    Scheme.RationalMap.order Y (-f) = Scheme.RationalMap.order Y f := by
  unfold Scheme.RationalMap.order
  have h : ((-f) ^ 2) = (f ^ 2) := by ring
  have h1 : (Ring.ordFrac (X.presheaf.stalk Y.point) (-f)) ^ 2 =
      (Ring.ordFrac (X.presheaf.stalk Y.point) f) ^ 2 := by
    rw [← map_pow, ← map_pow, h]
  have h2 : ((Ring.ordFrac (X.presheaf.stalk Y.point) (-f)) ^ 2).log =
      ((Ring.ordFrac (X.presheaf.stalk Y.point) f) ^ 2).log := by rw [h1]
  rw [WithZero.log_pow, WithZero.log_pow] at h2
  exact (smul_right_injective ℤ (by norm_num : (2 : ℕ) ≠ 0)) h2

/-- **`ord_Y (f^n) = n · ord_Y f`** for a nonzero rational function `f` and
natural number exponent `n`.

By induction on `n` from `order_mul_of_ne_zero` + `order_one`. The `f = 0`
hypothesis is necessary because the multiplicativity of `order` requires both
factors nonzero (otherwise `WithZero.log_mul` does not apply).

iter-199 §2 substrate sharpening (Lane WD-A4a PUSH-BEYOND). Powers-of-`f`
identity used in the Hartshorne II.6.9 ramification-inertia chase
(`degree_positivePart_principal_eq_finrank` body) and in classical
divisor-of-power computations `div(f^n) = n · div(f)`. -/
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_pow_of_ne_zero
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    {f : X.functionField} (hf : f ≠ 0) (n : ℕ) :
    Scheme.RationalMap.order Y (f ^ n) = n * Scheme.RationalMap.order Y f := by
  induction n with
  | zero => simp [Scheme.RationalMap.order]
  | succ k ih =>
    rw [pow_succ, Scheme.RationalMap.order_mul_of_ne_zero Y (pow_ne_zero k hf) hf, ih]
    push_cast
    ring

/-! ## Project-local Mathlib supplement — finiteness of height-one primes dividing
a fixed element (Hartshorne II.6.1 / Stacks 02RV ring core)

iter-003 Lane WD-A4a M1 substrate. These two `Ideal`-level lemmas are the
**ring-theoretic heart** of the affine finiteness `finite_order_support_affine`:
in a Noetherian integral domain `R`, only finitely many height-one primes can
contain a fixed nonzero element (resp. one of two nonzero elements `a, b` — the
numerator and denominator of `g = a/b`).

Proof idea: every height-one prime `p` containing a nonzero `a` is a *minimal*
prime over the principal ideal `(a)`. Indeed, by `Ideal.exists_minimalPrimes_le`
there is a minimal prime `q ⊆ p` over `(a)`; `q ≠ ⊥` because `a ≠ 0`, and if
`q < p` then `Ideal.height_le_iff` (applied to `p.height ≤ 1` and then to
`q.height ≤ 0`) forces a nonzero prime `⊥ < q` to have height `< 0`, impossible;
hence `q = p`. Minimal primes of an ideal in a Noetherian ring are finite
(`Ideal.finite_minimalPrimes_of_isNoetherianRing`).

These are axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only) and stand
ready for the scheme→ring assembler: the residual gap in
`finite_order_support_affine` is *only* the AG bridge
(`V.PrimeDivisor`-point ↔ height-one prime of `R = Γ(V,𝒪)`; `order Z g ≠ 0`
⟹ the prime contains the numerator or denominator of `g`), not this
finiteness. -/

/-- **Finiteness of height-one primes containing a fixed nonzero element.**
In a Noetherian integral domain `R`, the set of prime ideals of height one
containing a fixed `a ≠ 0` is finite. Each such prime is a minimal prime over
`(a)` (Krull principal-ideal-theorem direction via `Ideal.height_le_iff`), and
minimal primes of an ideal in a Noetherian ring are finite. Project-local
ring core of Hartshorne II.6.1 / Stacks 02RV; see the section docstring. -/
theorem _root_.Ideal.finite_setOf_isPrime_height_one_mem
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {a : R} (ha : a ≠ 0) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ a ∈ p}.Finite := by
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {a}))
  rintro p ⟨hp, hh, hmem⟩
  haveI := hp
  have hsp : Ideal.span {a} ≤ p := (Ideal.span_singleton_le_iff_mem p).mpr hmem
  obtain ⟨q, hq_mem, hqp⟩ := Ideal.exists_minimalPrimes_le (J := p) hsp
  have hqprime : q.IsPrime := hq_mem.1.1
  haveI := hqprime
  have hsq : Ideal.span {a} ≤ q := hq_mem.1.2
  have haq : a ∈ q := (Ideal.span_singleton_le_iff_mem q).mp hsq
  have hqbot : q ≠ ⊥ := fun h => ha (Ideal.mem_bot.mp (h ▸ haq))
  rcases lt_or_eq_of_le hqp with hlt | heq
  · exfalso
    have hle1 : p.height ≤ (1 : ℕ) := le_of_eq hh
    have hq1 : q.height < ((1 : ℕ) : ℕ∞) := (Ideal.height_le_iff).mp hle1 q hqprime hlt
    have hq0 : q.height ≤ ((0 : ℕ) : ℕ∞) := by
      rw [Nat.cast_one] at hq1; rw [Nat.cast_zero]; exact Order.lt_one_iff_nonpos.mp hq1
    have hbot : (⊥ : Ideal R).height < ((0 : ℕ) : ℕ∞) :=
      (Ideal.height_le_iff).mp hq0 ⊥ Ideal.isPrime_bot (bot_lt_iff_ne_bot.mpr hqbot)
    simp at hbot
  · rw [← heq]; exact hq_mem

/-- **Finiteness of height-one primes containing one of two fixed nonzero
elements.** The two-element (`g = a/b`) form of
`Ideal.finite_setOf_isPrime_height_one_mem`: in a Noetherian integral domain,
only finitely many height-one primes contain `a` or `b` (both nonzero). This is
the shape the affine order-finiteness argument consumes (`ord_Z(g) ≠ 0` forces
the prime to contain the numerator or denominator of `g`). Project-local. -/
theorem _root_.Ideal.finite_setOf_isPrime_height_one_mem_or
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {a b : R}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ (a ∈ p ∨ b ∈ p)}.Finite := by
  apply Set.Finite.subset
    ((Ideal.finite_setOf_isPrime_height_one_mem ha).union
     (Ideal.finite_setOf_isPrime_height_one_mem hb))
  rintro p ⟨hp, hh, hmem⟩
  rcases hmem with h | h
  · exact Set.mem_union_left _ ⟨hp, hh, h⟩
  · exact Set.mem_union_right _ ⟨hp, hh, h⟩

/-- **Order-of-vanishing is trivial at a prime away from both numerator and
denominator** (ring-theoretic core of step (iii) of the affine bridge,
Hartshorne II.6.1). Let `A` be an abstract localization of a Noetherian integral
domain `R` at a prime `pp` (`IsLocalization.AtPrime A pp`), with common fraction
field `K`. If neither `a` nor `b` lies in `pp`, then both are units in `A`, so
the order of vanishing of `a/b ∈ K` at `A` is trivial:
`Ring.ordFrac A (a/b) = 1`.

This is the axiom-clean heart of `finite_order_support_affine`: contrapositively,
`ordFrac A (a/b) ≠ 1 ⟹ a ∈ pp ∨ b ∈ pp`, which injects the nonzero-order locus
into the (finite) set of height-one primes containing `a` or `b`
(`Ideal.finite_setOf_isPrime_height_one_mem_or`). Stated for an abstract
`IsLocalization.AtPrime` so it applies directly to the structure-sheaf stalk
`𝒪_{V,Z.point}` (which is `IsLocalization.AtPrime` at the corresponding prime by
`IsAffineOpen.isLocalization_stalk`). Project-local: Mathlib `b80f227` ships no
order-support finiteness lemma. -/
theorem _root_.Ring.ordFrac_eq_one_of_notMem
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {pp : Ideal R} [pp.IsPrime]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra R A] [IsLocalization.AtPrime A pp]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra A K] [IsScalarTower R A K] [IsFractionRing A K]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    {a b : R} (ha : a ∉ pp) (hb : b ∉ pp) :
    Ring.ordFrac A (algebraMap R K a / algebraMap R K b) = 1 := by
  have hua : IsUnit (algebraMap R A a) :=
    IsLocalization.map_units A (⟨a, ha⟩ : pp.primeCompl)
  have hub : IsUnit (algebraMap R A b) :=
    IsLocalization.map_units A (⟨b, hb⟩ : pp.primeCompl)
  rw [map_div₀, IsScalarTower.algebraMap_apply R A K a,
    IsScalarTower.algebraMap_apply R A K b, Ring.ordFrac_of_isUnit hua,
    Ring.ordFrac_of_isUnit hub, div_one]

/-- **Affine Spec core of Hartshorne II.6.1 / Stacks 02RV.** On an affine integral
locally-Noetherian scheme `V = Spec R` regular in codimension one, the prime
divisors `Z` with nonzero order along a fixed rational function `g` are finite.

Mathematically: prime divisors of `Spec R` are the height-1 primes of the
Noetherian integral domain `R`; writing `g = a/b` with `a, b ∈ R` nonzero,
`ord_Z(g) ≠ 0` forces the corresponding prime to contain `a` or `b`, hence to be
a minimal prime of `(a·b)`, of which there are finitely many (Krull's
Hauptidealsatz / `Ideal.finite_minimalPrimes_of_isNoetherianRing`).

iter-002 Lane WD-A4a M1: this is the residual ring-theoretic substrate. Closing
it requires the affine bridge `V.PrimeDivisor ↔ height-1 PrimeSpectrum R`
together with `order Z g = v_p(g)` (stalk `O_{V,p} = Localization.AtPrime R p`,
`Ring.ordFrac` `=` the adic valuation at `p`), which is not yet packaged in
Mathlib `b80f227`. -/
private theorem finite_order_support_affine {V : Scheme.{u}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsAffine V] [Scheme.IsRegularInCodimensionOne V]
    (g : V.functionField) :
    {Z : V.PrimeDivisor | Scheme.RationalMap.order Z g ≠ 0}.Finite := by
  -- **iter-004 closure.** Set `R := Γ(V, ⊤)`, a Noetherian integral domain
  -- (`V` integral, locally Noetherian, affine) with `IsFractionRing R K(V)`.
  -- We inject the support `{Z | ord_Z g ≠ 0}` into the height-1 primes of `R`
  -- containing the numerator or denominator of `g = a/b`, which is finite by
  -- `Ideal.finite_setOf_isPrime_height_one_mem_or`. The injection sends `Z` to
  -- the prime `p_Z := (hV.primeIdealOf ⟨Z.point, _⟩).asIdeal`.
  classical
  have hV : IsAffineOpen (⊤ : V.Opens) := isAffineOpen_top V
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨Classical.arbitrary V, trivial⟩⟩
  haveI hRnoeth : IsNoetherianRing Γ(V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, hV⟩
  haveI hFRRK : IsFractionRing Γ(V, ⊤) V.functionField :=
    functionField_isFractionRing_of_isAffineOpen V ⊤ hV
  by_cases hg : g = 0
  · -- `g = 0`: order vanishes at every prime divisor, support is empty.
    subst hg
    apply Set.Finite.subset Set.finite_empty
    intro Z hZ
    exact (hZ (Scheme.RationalMap.order_zero Z)).elim
  -- `g ≠ 0`: write `g = a/b` with `a, b ∈ R` nonzero.
  obtain ⟨a, b, hb_mem, hab⟩ := IsFractionRing.div_surjective (A := Γ(V, ⊤)) g
  have hb_ne : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_mem
  have ha_ne : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact hg hab.symm
  -- The injection `Z ↦ p_Z` of the support into the finite height-1-prime set.
  apply Set.Finite.of_finite_image
    (f := fun Z : V.PrimeDivisor => (hV.primeIdealOf ⟨Z.point, trivial⟩).asIdeal)
  · -- The image lands in `{p | p prime ∧ height 1 ∧ (a ∈ p ∨ b ∈ p)}`.
    apply Set.Finite.subset (Ideal.finite_setOf_isPrime_height_one_mem_or ha_ne hb_ne)
    rintro _ ⟨Z, hZ, rfl⟩
    simp only [Set.mem_setOf_eq] at hZ
    -- Per-`Z` localization data: the stalk is `IsLocalization.AtPrime` at `p_Z`.
    set x : (⊤ : V.Opens) := ⟨Z.point, trivial⟩ with hx
    letI : Algebra Γ(V, ⊤) (V.presheaf.stalk Z.point) :=
      TopCat.Presheaf.algebra_section_stalk V.presheaf x
    haveI hloc : IsLocalization.AtPrime (V.presheaf.stalk Z.point)
        (hV.primeIdealOf x).asIdeal := hV.isLocalization_stalk x
    haveI hST : IsScalarTower Γ(V, ⊤) (V.presheaf.stalk Z.point) V.functionField :=
      functionField_isScalarTower V ⊤ x
    refine ⟨inferInstance, ?_, ?_⟩
    · -- `p_Z.height = 1` from `Order.coheight Z.point = 1` via the stalk
      -- Krull-dimension bridge `ringKrullDim_stalk_eq_coheight`.
      have e2 : ringKrullDim (V.presheaf.stalk Z.point)
          = ((hV.primeIdealOf x).asIdeal.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf x).asIdeal _
      have e1 : ringKrullDim (V.presheaf.stalk Z.point)
          = (Order.coheight Z.point : WithBot ℕ∞) :=
        Scheme.ringKrullDim_stalk_eq_coheight V Z.point
      rw [e2, Z.coheight] at e1
      exact_mod_cast e1
    · -- `a ∈ p_Z ∨ b ∈ p_Z`, contrapositive of `Ring.ordFrac_eq_one_of_notMem`.
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨hca, hcb⟩ := hcon
      apply hZ
      have hord1 : Ring.ordFrac (V.presheaf.stalk Z.point)
          (algebraMap Γ(V, ⊤) V.functionField a
            / algebraMap Γ(V, ⊤) V.functionField b) = 1 :=
        Ring.ordFrac_eq_one_of_notMem (R := Γ(V, ⊤))
          (A := V.presheaf.stalk Z.point) (K := V.functionField) hca hcb
      unfold Scheme.RationalMap.order
      rw [← hab, hord1, WithZero.log_one]
  · -- Injectivity: `p_Z = p_{Z'} ⟹ Z.point = Z'.point` via
    -- `fromSpec ∘ primeIdealOf = id` on points.
    intro Z _ Z' _ h
    apply Scheme.PrimeDivisor.ext
    have h' : hV.primeIdealOf ⟨Z.point, trivial⟩
        = hV.primeIdealOf ⟨Z'.point, trivial⟩ := PrimeSpectrum.ext h
    have hpt := congrArg (fun q => hV.fromSpec q) h'
    simpa only [hV.fromSpec_primeIdealOf] using hpt

/-- **Affine-chart core of Hartshorne II.6.1 / Stacks 02RV.** On a single affine
open `U = Spec R` of an integral scheme `X` regular in codimension one, only
finitely many prime divisors `Y` with generic point in `U` have nonzero order
along a fixed rational function `f`.

Mathematically: prime divisors `Y` with `Y.point ∈ U` correspond (via
`Scheme.PrimeDivisor.equivOpen`) to the height-1 primes of the Noetherian
integral domain `R := Γ(U, 𝒪_X)`; writing `f = a/b` with `a, b ∈ R` nonzero,
`ord_Y(f) ≠ 0` forces the corresponding prime to contain `a` or `b`, hence to
be a minimal prime of `(a·b)`, of which there are finitely many
(`Ideal.finite_minimalPrimes_of_isNoetherianRing`).

iter-002 Lane WD-A4a M1: this isolates the affine ring-theoretic core; the
global statement `rationalMap_order_finite_support` reduces to a finite union of
copies of this lemma over a finite affine cover (available since `[CompactSpace
X]`). -/
private theorem finite_order_support_on_affineOpen {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [Scheme.IsRegularInCodimensionOne X]
    (U : X.Opens) (hU : U ∈ X.affineOpens) (f : X.functionField) :
    {Y : X.PrimeDivisor | Y.point ∈ U ∧
      Scheme.RationalMap.order Y f ≠ 0}.Finite := by
  rcases Set.eq_empty_or_nonempty (U : Set X) with hE | hNe
  · -- `U` empty: no prime divisor has its generic point in `U`.
    apply Set.Finite.subset Set.finite_empty
    rintro Y ⟨hYU, -⟩
    rw [Set.eq_empty_iff_forall_notMem] at hE
    exact (hE Y.point hYU).elim
  · -- `U` nonempty: an integral affine chart `U.toScheme`.
    haveI : Nonempty U.toScheme := hNe.to_subtype
    haveI : IsAffine U.toScheme := hU
    haveI : IsIntegral U.toScheme := inferInstance
    haveI : Scheme.IsRegularInCodimensionOne U.toScheme := inferInstance
    -- The map `Scheme.PrimeDivisor.ofOpen U` sends the nonzero-order locus of
    -- the pulled-back rational function `g := (functionFieldIso U)⁻¹ f` on the
    -- chart onto a superset of our set; that chart locus is finite by
    -- `finite_order_support_affine`, so the image is finite.
    apply Set.Finite.subset
      ((finite_order_support_affine (V := U.toScheme)
        ((Scheme.Opens.functionFieldIso U).commRingCatIsoToRingEquiv.symm f)).image
        (Scheme.PrimeDivisor.ofOpen U))
    rintro Y ⟨hYU, hord⟩
    refine ⟨Scheme.PrimeDivisor.restrictToOpen U Y hYU, ?_, ?_⟩
    · -- `order (restrictToOpen U Y hYU) g ≠ 0`, transported from `order Y f ≠ 0`
      -- via `order_eq_order_restrict` (`order Y (functionFieldIso U g) =
      -- order (restrictToOpen U Y hYU) g`, with `functionFieldIso U g = f`).
      have key := Scheme.PrimeDivisor.order_eq_order_restrict U Y hYU
        ((Scheme.Opens.functionFieldIso U).commRingCatIsoToRingEquiv.symm f)
      rw [RingEquiv.apply_symm_apply] at key
      rw [Set.mem_setOf_eq, ← key]
      exact hord
    · -- `ofOpen U (restrictToOpen U Y hYU) = Y` (same underlying point).
      exact Scheme.PrimeDivisor.ext rfl

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
    [IsLocallyNoetherian X] [CompactSpace X] [Scheme.IsRegularInCodimensionOne X]
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
  -- Case 2 (f ≠ 0): Hartshorne II.6.1 / Stacks 02RV. Now that the signature
  -- carries `[CompactSpace X]`, `X` is quasi-compact, so its underlying space
  -- `⊤` is a *finite* union of affine opens (`isCompact_iff_finite_and_eq_
  -- biUnion_affineOpens`). Every prime divisor's generic point lies in one of
  -- these affine opens, and on each affine chart the nonzero-order locus is
  -- finite (`finite_order_support_on_affineOpen`, the affine ring-theoretic
  -- core). Hence the support is contained in a finite union of finite sets.
  · classical
    obtain ⟨s, hs_fin, hs_cover⟩ :=
      (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp
        (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
    refine Set.Finite.subset
      (hs_fin.biUnion (fun i _ =>
        finite_order_support_on_affineOpen (X := X) i.1 i.2 f)) ?_
    intro Y hY
    rw [Function.mem_support] at hY
    have hmem : Y.point ∈ (⊤ : X.Opens) := trivial
    rw [hs_cover] at hmem
    simp only [TopologicalSpace.Opens.mem_iSup] at hmem
    obtain ⟨i, hi, hYi⟩ := hmem
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨i, hi, hYi, hY⟩

namespace Scheme.WeilDivisor

variable {X : Scheme.{u}}

/-! ## §3. Divisor of a closed point on a curve

On a smooth proper curve `C` over a field, every closed point `P ∈ C` is a prime
divisor (it is closed, integral, of codimension one in the one-dimensional integral
scheme `C`). The associated Weil divisor is `[P] = 1 · P ∈ Div(C)`. -/

/-- **The Weil divisor associated to a closed point `P` on a curve.** The element
`[P] := 1 · P ∈ Div(C)`, i.e. the prime divisor `P` with multiplicity one.

For a smooth proper curve every closed point is automatically a prime divisor (it
is a codimension-one integral closed subscheme of the one-dimensional integral
scheme `C`); conversely every prime divisor on a curve is of this form, so an
arbitrary divisor on `C` is a finite formal `ℤ`-linear combination
`Σ nᵢ · [Pᵢ]` of closed points.

Blueprint reference: `def:divisor_closed_point` (Hartshorne II §6 p. 137).

iter-174 body: the function is junk-defined outside its intended scope. We
case-split on `Order.coheight P = 1` (the codimension-one witness of
`PrimeDivisor`). On the branch where the equality holds — automatic for a
closed point on a one-dimensional integral scheme — we promote `P` to a
`PrimeDivisor` via the witness and return `Finsupp.single ⟨P, h⟩ 1`, i.e.
the prime divisor `P` with multiplicity one. On the off-branch (junk regime)
we return the zero divisor. The blueprint pins the well-definedness argument
"`IsClosed {P}` on a one-dimensional integral scheme ⟹ `coheight P = 1`" as a
separate threadable hypothesis at the call site (chapter L330–L340 "Lean
signature scope"); see `ofClosedPoint_eq_single` for the equation in the
hypothesised regime. -/
noncomputable def ofClosedPoint {C : Scheme.{u}} (P : C)
    (_hP : IsClosed ({P} : Set C)) : C.WeilDivisor :=
  if h : Order.coheight P = 1 then Finsupp.single ⟨P, h⟩ 1 else 0

/-- In the hypothesised regime where the closed point `P` has coheight one
(the codim-1 condition automatic for a closed point of a one-dimensional
integral scheme), `ofClosedPoint P hP` is the prime divisor `P` with
multiplicity one. -/
lemma ofClosedPoint_eq_single {C : Scheme.{u}} (P : C)
    (hP : IsClosed ({P} : Set C)) (h : Order.coheight P = 1) :
    ofClosedPoint P hP = Finsupp.single ⟨P, h⟩ 1 := by
  simp [ofClosedPoint, h]

/-- Off-branch: outside the codim-1 regime, `ofClosedPoint` is junk-defined as
the zero divisor. (Only relevant when the user supplies a "closed point" that
does not have coheight one in the ambient scheme — e.g. a generic point or a
codim-≥2 point on a higher-dimensional scheme.) -/
lemma ofClosedPoint_eq_zero {C : Scheme.{u}} (P : C)
    (hP : IsClosed ({P} : Set C)) (h : Order.coheight P ≠ 1) :
    ofClosedPoint P hP = 0 := by
  simp [ofClosedPoint, h]

/-! ## §4. Degree of a divisor over an algebraically closed base -/

/-- **Degree of a Weil divisor on a smooth proper curve over `k̄`.**

Over an algebraically closed field `k̄`, every closed point of a smooth proper
curve `C` has residue field `k̄`, so each prime divisor `[P]` contributes degree
one to the sum, and `deg(D) := Σᵢ nᵢ` is the sum of the integer coefficients of
the formal sum `D = Σ nᵢ · [Pᵢ]`.

(Over a general field `k` one weights by the residue-field degrees
`Σᵢ nᵢ · [κ(Pᵢ) : k]` to recover the geometric degree; the project's RR bridge
needs only the `k̄` specialisation.)

Blueprint reference: `def:divisor_degree` (Hartshorne II §6 p. 137; Stacks 0BE0).

Implementation: `Finsupp.sum D (fun _ n => n)` is the sum of all coefficients of
the finitely supported function representing `D`. -/
noncomputable def degree (D : X.WeilDivisor) : ℤ :=
  (D : X.PrimeDivisor →₀ ℤ).sum (fun _ n => n)

/-- **The degree map is a group homomorphism `Div(C) → ℤ`.**

`deg(D₁ + D₂) = deg(D₁) + deg(D₂)`, `deg(-D) = -deg(D)`, `deg(0) = 0`. Bundled
as an `AddMonoidHom` for downstream use (the linear-equivalence quotient
`Cl(C) := Div(C) / im(div)` will inherit a `deg : Cl(C) → ℤ` from this).

Blueprint reference: `thm:divisor_degree_hom` (immediate from `def:divisor_degree`).

Implementation: built from `Finsupp.liftAddHom (fun _ ↦ AddMonoidHom.id ℤ)`, the
generic Mathlib packaging that lifts a family of `AddMonoidHom`s indexed by the
support into a single `AddMonoidHom` on the finsupp. Unfolds to
`D.sum (fun _ z ↦ z) = degree D` (see `degree_hom_apply` below). -/
noncomputable def degree_hom : X.WeilDivisor →+ ℤ :=
  Finsupp.liftAddHom (fun _ ↦ AddMonoidHom.id ℤ)

@[simp]
lemma degree_hom_apply (D : X.WeilDivisor) : degree_hom D = degree D :=
  Finsupp.liftAddHom_apply (α := X.PrimeDivisor) (M := ℤ) (N := ℤ)
    (fun _ ↦ AddMonoidHom.id ℤ) D

/-- **Degree of the zero divisor is zero.** A direct consequence of
`degree_hom` being an `AddMonoidHom`. -/
@[simp]
lemma degree_zero : degree (0 : X.WeilDivisor) = 0 := by
  rw [← degree_hom_apply]; exact map_zero _

/-- **Degree is additive.** A direct consequence of `degree_hom` being an
`AddMonoidHom`. -/
lemma degree_add (D₁ D₂ : X.WeilDivisor) :
    degree (D₁ + D₂) = degree D₁ + degree D₂ := by
  rw [← degree_hom_apply, ← degree_hom_apply, ← degree_hom_apply]
  exact map_add _ _ _

/-- **Degree of the negation.** `deg(-D) = -deg D`. A direct consequence of
`degree_hom` being an `AddMonoidHom`.

iter-198 §4 substrate sharpening (Lane WD-A4a PUSH-BEYOND). -/
@[simp]
lemma degree_neg (D : X.WeilDivisor) :
    degree (-D) = -degree D := by
  rw [← degree_hom_apply, ← degree_hom_apply]
  exact map_neg _ _

/-- **Degree is subtractive.** `deg(D₁ - D₂) = deg D₁ - deg D₂`. A direct
consequence of `degree_hom` being an `AddMonoidHom`.

iter-198 §4 substrate sharpening (Lane WD-A4a PUSH-BEYOND). -/
lemma degree_sub (D₁ D₂ : X.WeilDivisor) :
    degree (D₁ - D₂) = degree D₁ - degree D₂ := by
  rw [← degree_hom_apply, ← degree_hom_apply, ← degree_hom_apply]
  exact map_sub _ _ _

/-! ## §5. Principal divisors -/

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
noncomputable def principal [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [Scheme.IsRegularInCodimensionOne X] (f : X.functionField)
    (_hf : f ≠ 0) : X.WeilDivisor :=
  Finsupp.ofSupportFinite
    (fun Y : X.PrimeDivisor => Scheme.RationalMap.order Y f)
    (rationalMap_order_finite_support f)

/-- **The coefficient of `principal f hf` at a prime divisor `Y` is the order of
`f` along `Y`.** This is the basic structural unfolding of the
`Finsupp.ofSupportFinite` packaging in `principal`; one-line via
`Finsupp.ofSupportFinite_coe` from `Mathlib.Data.Finsupp.Defs`.

iter-193 substrate helper for the Lane I body close
(`degree_positivePart_principal_eq_finrank`). -/
lemma principal_apply [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [Scheme.IsRegularInCodimensionOne X] (f : X.functionField) (hf : f ≠ 0)
    (Y : X.PrimeDivisor) :
    (show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y =
      Scheme.RationalMap.order Y f := by
  change (Finsupp.ofSupportFinite
      (fun Y : X.PrimeDivisor => Scheme.RationalMap.order Y f)
      (rationalMap_order_finite_support f)) Y = _
  rw [Finsupp.ofSupportFinite_coe]

/-- **`Scheme.RationalMap.order Y 1 = 0`** — the order of the constant
function `1` is `0` at every prime divisor. Direct from
`map_one` of `Ring.ordFrac` + `WithZero.log_one`.

iter-193 substrate helper for further structural results
(`principal_one_eq_zero` and similar). -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.RationalMap.order_one
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)] :
    Scheme.RationalMap.order Y (1 : X.functionField) = 0 := by
  unfold Scheme.RationalMap.order
  rw [map_one, WithZero.log_one]

/-- **The principal divisor of the constant function `1` is the zero
divisor.** A direct consequence of `Scheme.RationalMap.order_one`. -/
@[simp]
lemma principal_one [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [Scheme.IsRegularInCodimensionOne X] :
    principal (1 : X.functionField) one_ne_zero = 0 := by
  change (_ : X.PrimeDivisor →₀ ℤ) = (0 : X.PrimeDivisor →₀ ℤ)
  apply Finsupp.ext
  intro Y
  rw [principal_apply]
  exact Scheme.RationalMap.order_one Y

/-- **The principal-divisor map is a group homomorphism `K(X)^× → Div(X)`.**

Concretely `div(fg) = div(f) + div(g)`, `div(f⁻¹) = -div(f)`, `div(1) = 0`. Bundled
as a `MonoidHom` from the multiplicative units of `K(X)` to `Multiplicative (Div(X))`
(equivalently: an additive map `(K(X)^×, ·) → (Div(X), +)`).

Blueprint reference: `thm:principal_hom` (Hartshorne II §6 p. 131).

iter-177 body: closes coordinate-wise from the DVR identities
`v_Y(fg) = v_Y(f) + v_Y(g)`, `v_Y(1) = 0`. The per-`Y` identities live in
`Scheme.RationalMap.order` via `Ring.ordFrac` (a `K →*₀ ℤᵐ⁰` monoid-with-zero
hom) and `WithZero.log_mul` / `WithZero.log_one`. -/
noncomputable def principal_hom [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [Scheme.IsRegularInCodimensionOne X] :
    (X.functionField)ˣ →* Multiplicative X.WeilDivisor where
  toFun u :=
    Multiplicative.ofAdd (principal (↑u : X.functionField) (Units.ne_zero u))
  map_one' := by
    -- Goal: Multiplicative.ofAdd (principal ↑1 _) = 1.
    -- Use `← ofAdd_zero` to rewrite RHS as `Multiplicative.ofAdd 0`,
    -- then `congr 1` reduces to `principal ↑1 _ = 0` (Finsupp equality),
    -- and `Finsupp.ext` peels to the per-`Y` coordinate identity, which
    -- closes by unfolding `order` to `WithZero.log (Ring.ordFrac _ 1) = 0`
    -- via `map_one` and `WithZero.log_one`.
    rw [← ofAdd_zero]
    congr 1
    apply Finsupp.ext
    intro Y
    change Scheme.RationalMap.order Y
        (((1 : (X.functionField)ˣ) : X.functionField)) = 0
    rw [Units.val_one]
    unfold Scheme.RationalMap.order
    rw [map_one, WithZero.log_one]
  map_mul' u v := by
    -- Goal: Multiplicative.ofAdd (principal ↑(u*v) _) =
    --       Multiplicative.ofAdd (principal ↑u _) * Multiplicative.ofAdd (principal ↑v _).
    -- Use `← ofAdd_add` to rewrite RHS, then `congr 1` reduces to
    -- `principal ↑(u*v) _ = principal ↑u _ + principal ↑v _` (Finsupp
    -- equality), and `Finsupp.ext` peels to the per-`Y` coordinate
    -- identity `order Y (uv) = order Y u + order Y v`, which closes by
    -- `Ring.ordFrac (uv) = Ring.ordFrac u * Ring.ordFrac v` (`map_mul`)
    -- and `WithZero.log_mul` (the nonzero hypotheses come from
    -- `Units.ne_zero` and `map_ne_zero`).
    rw [← ofAdd_add]
    congr 1
    apply Finsupp.ext
    intro Y
    change Scheme.RationalMap.order Y ((↑(u * v) : X.functionField))
      = Scheme.RationalMap.order Y (↑u : X.functionField)
      + Scheme.RationalMap.order Y (↑v : X.functionField)
    rw [Units.val_mul]
    unfold Scheme.RationalMap.order
    rw [map_mul]
    exact WithZero.log_mul
      ((map_ne_zero _).mpr (Units.ne_zero u))
      ((map_ne_zero _).mpr (Units.ne_zero v))

/-- **The principal divisor of `f⁻¹` is the negation of the principal divisor of
`f`.** `div(f⁻¹) = -div(f)`, the divisor-level form of the per-prime-divisor DVR
identity `v_Y(f⁻¹) = -v_Y(f)` (`Scheme.RationalMap.order_inv`). Equivalently the
zeros of `f⁻¹` are exactly the poles of `f` and vice versa — the divisor identity
underlying `principal_degree_zero` (Hartshorne II.6.10) and the linear-equivalence
symmetry law.

iter-001 substrate helper for the `principal_degree_zero` non-constant branch. -/
lemma principal_inv [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [Scheme.IsRegularInCodimensionOne X] (f : X.functionField) (hf : f ≠ 0) :
    -(principal f hf) = principal f⁻¹ (inv_ne_zero hf) := by
  apply Finsupp.ext
  intro Y
  change -((show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y) = _
  rw [principal_apply, principal_apply, Scheme.RationalMap.order_inv]

/-- **Principal divisors on a complete nonsingular curve have degree zero**
(Hartshorne Corollary II.6.10, Stacks 0BE3).

For every nonzero rational function `f ∈ K(C)^×` on a smooth proper curve `C`
over an algebraically closed field `k̄`,
`deg(div(f)) = 0 ∈ ℤ`.

Blueprint reference: `thm:principal_deg_zero` (Hartshorne II.6 Cor. 6.10 p. 138).

The proof (Hartshorne 6.10): if `f ∈ k̄` is constant then `div(f) = 0` and the
claim is trivial. Otherwise the inclusion `k̄(f) ⊂ K(C)` exhibits `K(C)` as a
finite extension of `k̄(f) ≅ k̄(t)`, so the corresponding morphism
`φ : C → ℙ¹_{k̄}` is finite, `div(f) = φ^*([0] - [∞])`, and pullback along a
finite morphism multiplies degree by `deg(φ)`. Two auxiliary sub-lemmas
(finite morphism induced by a non-constant rational function; multiplicativity
of degree under finite pullback, Hartshorne II.6.9) are deferred to follow-up
iters of `RR.1`. -/
theorem principal_degree_zero {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (C : Over (Spec (.of kbar))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsIntegral C.left] [IsLocallyNoetherian C.left]
    [Scheme.IsRegularInCodimensionOne C.left]
    (f : C.left.functionField) (hf : f ≠ 0) :
    degree (principal f hf) = 0 := by
  -- Hartshorne II.6.10 (iter-178 partial). Case-split on whether every
  -- prime-divisor order of `f` vanishes. On a complete nonsingular curve,
  -- this case split exactly recovers Hartshorne's constant-vs-non-constant
  -- split: `(∀ Y, ord_Y f = 0)` ⟺ `f ∈ k̄ \ {0}` (a nowhere-vanishing
  -- rational function on a complete curve is constant; that direction is
  -- Hartshorne II.6.10's "if `f ∈ k̄` then `(f) = 0`").
  by_cases hconst : ∀ Y : C.left.PrimeDivisor, Scheme.RationalMap.order Y f = 0
  · -- Constant branch: every order vanishes ⟹ `principal f hf = 0` ⟹
    -- `degree (principal f hf) = degree 0 = 0`.
    have hprincipal_zero : principal f hf = 0 := by
      apply Finsupp.ext
      intro Y
      change Scheme.RationalMap.order Y f = 0
      exact hconst Y
    rw [hprincipal_zero]
    unfold degree
    exact Finsupp.sum_zero_index
  · -- Non-constant branch (Hartshorne II.6.10 `f ∉ k̄`): the inclusion
    -- `k̄(f) ⊂ K(C)` defines a finite morphism `φ : C → ℙ¹_{k̄}` via the
    -- function-field-determines-curve correspondence (Hartshorne I.6.12),
    -- and `principal f hf = φ^*([0] - [∞])`. Pullback along a finite
    -- morphism of curves multiplies degrees by `deg(φ)` (Hartshorne
    -- II.6.9), so `deg(principal f hf) = deg(φ) · deg([0] - [∞]) =
    -- deg(φ) · 0 = 0`.
    -- This branch is gated on (i) the `φ : C → ℙ¹` construction (Lane 5
    -- `RationalCurveIso.lean:morphismToP1OfGlobalSections`, iter-178+),
    -- and (ii) the degree-multiplicativity-under-finite-pullback bridge
    -- (Hartshorne II.6.9, Mathlib gap).
    --
    -- **iter-001 genuine partial proof — elementary degree decomposition.**
    -- We reduce the bare gap to the precise Hartshorne II.6.9 content. Writing
    -- `D := div(f)`, the degree splits into zero-part minus pole-part:
    --   `deg D = Σ_Y max(ord_Y f, 0) − Σ_Y max(−ord_Y f, 0)`,
    -- valid because `n = max n 0 − max (−n) 0` for every integer `n`
    -- (`hdeg`). The pole part of `f` is the zero part of `f⁻¹` because
    -- `div(f⁻¹) = −div(f)` (`principal_inv`) and `Finsupp.sum_neg_index`
    -- (`hpoles`). Hence
    --   `deg(div f) = deg((f)_0) − deg((f⁻¹)_0)`,
    -- and the goal `= 0` is equivalent to the equality of the two
    -- zero-degrees. THIS equality is the genuine Hartshorne II.6.9 content:
    -- both `deg((f)_0)` and `deg((f⁻¹)_0)` equal the morphism degree
    -- `deg φ = [K(C) : k̄(ℙ¹)]` (the two function-field embeddings `k̄(f)`
    -- and `k̄(f⁻¹) = k̄(f)` give the SAME finite morphism `φ : C → ℙ¹`),
    -- formalised by `degree_positivePart_principal_eq_finrank` once the
    -- `Scheme.Hom.ofFunctionFieldEmbedding` substrate (Mathlib gap, see
    -- L1705) lands. The remaining `sorry` is exactly that equality.
    have hdeg : degree (principal f hf) =
        ((principal f hf).sum fun _ n => max n 0)
          - ((principal f hf).sum fun _ n => max (-n) 0) := by
      unfold degree
      rw [← Finsupp.sum_sub]
      apply Finsupp.sum_congr
      intro Y _
      omega
    have hpoles : ((principal f hf).sum fun _ n => max (-n) 0) =
        ((principal f⁻¹ (inv_ne_zero hf)).sum fun _ n => max n 0) := by
      rw [← principal_inv f hf]
      exact (Finsupp.sum_neg_index
        (g := (principal f hf : C.left.PrimeDivisor →₀ ℤ))
        (h := fun _ n => max n 0)
        (by intro a; exact max_self 0)).symm
    rw [hdeg, hpoles, sub_eq_zero]
    -- Goal: `deg((f)_0) = deg((f⁻¹)_0)`, i.e. zeros and poles of `f` have
    -- equal total degree. Both equal `deg φ` (Hartshorne II.6.9); substrate
    -- gap is the finite morphism `φ : C → ℙ¹` from `algebraMap k̄(ℙ¹) → K(C)`.
    sorry

/-! ## §6. Positive part of a Weil divisor

Iter-190 plan-phase Lane I Pin 2 corrective substrate. The carrier
`X.WeilDivisor = X.PrimeDivisor →₀ ℤ` is a finitely supported integer-valued
function on prime divisors; the *positive part* `(D)_0` is obtained by
replacing each coefficient `n_Y` with `max(n_Y, 0)`. Equivalently this is
the lattice join `D ⊔ 0` in the pointwise lattice structure (the
`semilatticeSup` instance on `Finsupp` is noncomputable). The complementary
*negative part* `(D)_∞ := (-D)_0` then gives the canonical decomposition
`D = (D)_0 - (D)_∞` into a difference of effective divisors.

Blueprint reference: `def:WeilDivisor_positivePart` /
`lem:degree_positivePart_principal_eq_finrank` of
`RiemannRoch_WeilDivisor.tex` §6 (iter-190 plan-phase additions).
-/

/-- **Positive part of a Weil divisor**.

`positivePart D` is the divisor obtained from `D` by replacing each
coefficient `n_Y` with `max(n_Y, 0)` (equivalently `D ⊔ 0` in the
pointwise lattice structure on `Finsupp`). For `D = div(f)` on a smooth
proper curve `C`, this recovers the divisor-of-zeros `(f)_0` — the
formal sum of the zeros of `f` with their multiplicities.

The complementary `negativePart D := positivePart (-D)` then gives
`D = positivePart D - negativePart D` as a difference of effective
divisors.

Implementation: `Finsupp.mapRange (fun n : ℤ => n ⊔ 0) (by simp)`, the
generic Mathlib packaging that maps a finsupp's coefficients through a
zero-preserving function. (The `D ⊔ 0` lattice form is equivalent but
requires the noncomputable `Finsupp.semilatticeSup` synthesis on
`PrimeDivisor →₀ ℤ`; the explicit `mapRange` form is more transparent
to typeclass synthesis.)

Blueprint reference: `def:WeilDivisor_positivePart` (project-bespoke;
chapter `RiemannRoch_WeilDivisor.tex` §6, Hartshorne II.6.10 phrasing). -/
noncomputable def positivePart (D : X.WeilDivisor) : X.WeilDivisor :=
  Finsupp.mapRange (fun n : ℤ => n ⊔ 0) (by simp) D

/-- The positive part of the zero divisor is zero. -/
@[simp]
lemma positivePart_zero : positivePart (0 : X.WeilDivisor) = 0 := by
  change Finsupp.mapRange (fun n : ℤ => n ⊔ 0) (by simp)
    (0 : X.PrimeDivisor →₀ ℤ) = (0 : X.PrimeDivisor →₀ ℤ)
  exact Finsupp.mapRange_zero

/-- **Degree of positive part as a sum of capped coefficients.** A purely
symbolic Mathlib manipulation: unfolding `positivePart`
(= `Finsupp.mapRange (max · 0)`) and `degree` (= `Finsupp.sum (fun _ n => n)`)
identifies `degree (positivePart D)` with the sum of `max (D Y) 0` over
the support of `D`.

This is the iter-192 structural-reduction helper consumed by
`degree_positivePart_principal_eq_finrank` below. The proof is one line
via `Finsupp.sum_mapRange_index` from
`Mathlib.Algebra.BigOperators.Finsupp.Basic`. -/
lemma degree_positivePart_eq_sum_max (D : X.WeilDivisor) :
    degree (positivePart D) = D.sum (fun _ n => max n 0) := by
  unfold positivePart degree
  exact Finsupp.sum_mapRange_index (h := fun _ b => b) (by intro _; rfl)

/-- **Degree splits into positive and negative parts:**
`deg D = deg (D)_0 − deg (D)_∞`, where `(D)_0 = positivePart D` is the
divisor of zeros and `(D)_∞ = positivePart (-D)` is the divisor of poles.
This is the degree-level form of the canonical decomposition
`D = (D)_0 − (D)_∞` of a Weil divisor into a difference of effective
divisors (blueprint `def:WeilDivisor_positivePart` §6 prose).

The proof is the integer identity `n = max n 0 − max (−n) 0` summed over the
support: rewrite both positive-part degrees via `degree_positivePart_eq_sum_max`,
turn the `(-D)`-sum into a `D`-sum via `Finsupp.sum_neg_index`, then combine and
close pointwise with `omega`.

iter-001 substrate helper; the canonical degree decomposition consumed by
`principal_degree_zero` (zeros vs. poles) and reusable for the
ramification-inertia chase in `degree_positivePart_principal_eq_finrank`. -/
lemma degree_eq_degree_positivePart_sub (D : X.WeilDivisor) :
    degree D = degree (positivePart D) - degree (positivePart (-D)) := by
  have hneg : (Finsupp.sum (-D) fun _ n => max n 0) =
      Finsupp.sum D (fun _ n => max (-n) 0) :=
    Finsupp.sum_neg_index (g := (D : X.PrimeDivisor →₀ ℤ)) (by intro a; exact max_self 0)
  rw [degree_positivePart_eq_sum_max, degree_positivePart_eq_sum_max, hneg]
  unfold degree
  rw [← Finsupp.sum_sub]
  apply Finsupp.sum_congr
  intro Y _
  omega

/-- **Positive part of a `Finsupp.single`.** Pointwise extraction of the
mapRange definition of `positivePart`: for a one-point-supported Weil divisor
`Finsupp.single Y n`, the positive part is `Finsupp.single Y (max n 0)`.
A direct consequence of `Finsupp.mapRange_single` (with `max 0 0 = 0` as
the zero-preservation witness).

iter-193 substrate helper paving the way for the Lane I body close. -/
@[simp]
lemma positivePart_single (Y : X.PrimeDivisor) (n : ℤ) :
    positivePart (Finsupp.single Y n : X.WeilDivisor) =
      Finsupp.single Y (max n 0) := by
  change Finsupp.mapRange (fun n : ℤ => n ⊔ 0) (by simp)
      (Finsupp.single Y n) = _
  rw [Finsupp.mapRange_single]

/-- **Degree of a `Finsupp.single` Weil divisor.** The degree of the
one-point-supported Weil divisor `Finsupp.single Y n` is `n`. A direct
consequence of `Finsupp.sum_single_index`.

iter-193 substrate helper for `degree_positivePart_principal_eq_finrank`. -/
@[simp]
lemma degree_single (Y : X.PrimeDivisor) (n : ℤ) :
    degree (Finsupp.single Y n : X.WeilDivisor) = n := by
  unfold degree
  change (Finsupp.single Y n : X.PrimeDivisor →₀ ℤ).sum (fun _ n => n) = n
  exact Finsupp.sum_single_index rfl

/-- **Sum-over-prime-divisors lower bound via a single contributing point.**
If `f` has order `1` at some prime divisor `Y₀`, then the degree of the positive
part of `principal f hf` is at least `1`.

iter-193 substrate helper consumed by `degree_positivePart_principal_eq_finrank`:
it formalises Step 2 of the Hartshorne II.6.9 recipe (`hlp` produces
the local-parameter prime divisor `Y₀` with coefficient `1`). -/
lemma one_le_degree_positivePart_principal_of_order_one
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [Scheme.IsRegularInCodimensionOne X]
    (f : X.functionField) (hf : f ≠ 0) (Y₀ : X.PrimeDivisor)
    (h₀ : Scheme.RationalMap.order Y₀ f = 1) :
    1 ≤ degree (positivePart (principal f hf)) := by
  classical
  rw [degree_positivePart_eq_sum_max]
  -- The sum is over a finset; isolate the Y₀ contribution.
  have hY₀_supp :
      Y₀ ∈ (show (X.PrimeDivisor →₀ ℤ) from principal f hf).support := by
    rw [Finsupp.mem_support_iff]
    rw [principal_apply]
    rw [h₀]
    exact one_ne_zero
  -- For the sum to be ≥ 1, isolate the Y₀ term (= 1) and the rest (≥ 0).
  have h_split :
      (show (X.PrimeDivisor →₀ ℤ) from principal f hf).sum
          (fun _ n => max n 0) =
        max ((show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y₀) 0 +
          ((show (X.PrimeDivisor →₀ ℤ) from principal f hf).support.erase Y₀).sum
            (fun Y => max
              ((show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y) 0) := by
    rw [show (show (X.PrimeDivisor →₀ ℤ) from principal f hf).sum
            (fun _ n => max n 0) =
          (show (X.PrimeDivisor →₀ ℤ) from principal f hf).support.sum
            (fun Y => max
              ((show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y) 0)
        from rfl]
    rw [Finset.sum_erase_eq_sub hY₀_supp]
    ring
  rw [h_split]
  -- The Y₀ term equals max 1 0 = 1.
  have hY₀_val :
      (show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y₀ = 1 := by
    rw [principal_apply]; exact h₀
  rw [hY₀_val]
  -- The remainder is a sum of non-negative integers, hence ≥ 0.
  have h_nonneg :
      0 ≤ ((show (X.PrimeDivisor →₀ ℤ) from principal f hf).support.erase Y₀).sum
        (fun Y => max
          ((show (X.PrimeDivisor →₀ ℤ) from principal f hf) Y) 0) :=
    Finset.sum_nonneg (fun Y _ => le_max_right _ _)
  -- Conclude: 1 = max 1 0 ≤ max 1 0 + 0 ≤ LHS + remainder.
  have : (max (1 : ℤ) 0) = 1 := by norm_num
  rw [this]
  linarith

/-- **Generic Finsupp identity**: the sum of clipped non-negative parts equals
the sum of the coefficients over the positive-coefficient sub-support.

For a finsupp `D : α →₀ ℤ`, `D.sum (max · 0)` agrees with the unclipped sum
`∑ D` restricted to the finset `{a ∈ supp D | 0 < D a}`. Negative-coefficient
points contribute `0` to the max and drop out; positive-coefficient points
contribute `D a` to both sides; the (vacuously zero) `D a = 0` case is excluded
by the `supp` filter on both sides.

iter-195 Lane I substrate helper for `degree_positivePart_principal_eq_finrank`:
it formalises the "the positive part of `D` is supported on the positive-coefficient
points" identity, which is Step 2.5 of the Hartshorne II.6.9 recipe (between the
`degree_positivePart_eq_sum_max` unfolding and the ramification-inertia chase). -/
lemma _root_.Finsupp.sum_max_zero_eq_sum_filter_pos {α : Type*}
    (D : α →₀ ℤ) :
    D.sum (fun _ n => max n 0) =
      ∑ a ∈ D.support.filter (fun a => 0 < D a), D a := by
  classical
  rw [Finsupp.sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hpos : 0 < D a
  · simp [hpos]
    omega
  · simp [hpos]
    omega

/-! ### Iter-194 typed-sorry instance scaffolding for `ProjectiveLineBar kbar`

The `degree_positivePart_principal_eq_finrank` theorem below specialises
`K = (ProjectiveLineBar kbar).left.functionField` and the uniformiser
witness `hLPUnif` quantifies over `(ProjectiveLineBar kbar).left.PrimeDivisor`
with `Scheme.RationalMap.order Y₀ t`, which requires the underlying
scheme to support the order machinery. The required typeclasses are
`IsIntegral`, `IsLocallyNoetherian`, and `Scheme.IsRegularInCodimensionOne`
on `(ProjectiveLineBar kbar).left`. These are mathematically true
(ProjectiveLineBar is `Proj` of `k̄[X₀, X₁]`, finite type over the field
`k̄`, smooth of dimension 1 over `k̄`, hence locally Noetherian, integral,
and regular at every point), but Mathlib does not currently ship them as
free instances. We declare them as named typed-sorry instances scheduled
for iter-194+ closure.
-/

/-- **Iter-194 axiom-clean closure**: `(ProjectiveLineBar kbar).left` is locally
Noetherian. Derivation chain: `(ProjectiveLineBar kbar).hom` is proper (existing
`projectiveLineBar_isProper`), hence locally of finite type
(`IsProper.toLocallyOfFiniteType`); the base `Spec (.of kbar)` is locally
Noetherian because the field `kbar` is Noetherian; locally-finite-type morphism
over a locally Noetherian base has locally Noetherian source
(`LocallyOfFiniteType.isLocallyNoetherian`). -/
instance instIsLocallyNoetherianProjectiveLineBar (kbar : Type u) [Field kbar] :
    IsLocallyNoetherian (ProjectiveLineBar kbar).left := by
  haveI : IsLocallyNoetherian (Spec (.of kbar)) := inferInstance
  haveI : LocallyOfFiniteType (ProjectiveLineBar kbar).hom :=
    IsProper.toLocallyOfFiniteType
  exact LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLineBar kbar).hom

/-- **Typed-sorry theorem** (iter-196+ demoted from `instance`):
`(ProjectiveLineBar kbar).left` is regular in codimension one (Hartshorne's
`(*)`). Derivation: smoothness ⟹ regular ⟹ DVR stalks at codim-1
points; the bridge from `SmoothOfRelativeDimension 1` to
`Scheme.IsRegularInCodimensionOne` is iter-194+ work.
**Demoted from `instance` per lean-auditor iter-196 must-fix**: the silent
propagation of `sorryAx` through `IsRegularInCodimensionOne`-typeclass
synthesis is a soundness exposure. Callers thread via
`haveI := isRegularInCodimOneProjectiveLineBar kbar`. -/
theorem isRegularInCodimOneProjectiveLineBar (kbar : Type u) [Field kbar]
    [IsIntegral (ProjectiveLineBar kbar).left] :
    Scheme.IsRegularInCodimensionOne (ProjectiveLineBar kbar).left := by
  -- **Iter-195 structural advance.** Expose the per-prime-divisor obligation.
  -- The body's recipe is the standard "smooth-of-dim-1 ⟹ DVR stalks at
  -- every codim-1 point" chain, which decomposes as:
  --   (i)  `SmoothOfRelativeDimension 1 (ProjectiveLineBar kbar).hom`
  --        (gated on BareScheme `projectiveLineBar_smoothOfRelDim` sorry);
  --   (ii) smooth scheme ⟹ each stalk is a regular local ring (Mathlib
  --        gap: no direct `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk`
  --        bridge ships in `b80f227`; iter-196+ Lane I directive Step A);
  --   (iii) `Y.coheight = 1` ⟹ stalk Krull dim = 1 (Mathlib gap, Stacks
  --        02IZ / 005X — topological coheight ↔ algebraic Krull dim);
  --   (iv) regular local ring of Krull dim 1 ⟹ DVR (Mathlib available
  --        via `IsRegularLocalRing.iff_finrank_cotangentSpace` +
  --        `IsLocalRing.finrank_CotangentSpace_eq_one_iff`).
  refine ⟨fun Y => ?_⟩
  -- Per-prime-divisor obligation:
  -- `IsDiscreteValuationRing ((ProjectiveLineBar kbar).left.presheaf.stalk Y.point)`
  -- with `Y.coheight : Order.coheight Y.point = 1` in scope.
  --
  -- **Iter-196 Lane I Route 2 structural advance** (PID-transfer via the
  -- 2-chart affine cover). The closure decomposes as:
  --
  --   (A) Pick the chart `i := 𝒰.idx Y.point` containing `Y.point` (where
  --       `𝒰 = (projectiveLineBarAffineCover kbar).openCover`), with the
  --       chart-side witness `y : Spec(Away 𝒜 (X i))` such that
  --       `(𝒰.f i).base y = Y.point`.
  --
  --   (B) Open-immersion stalk transfer: `(𝒰.f i)` is an open immersion
  --       (the chart is an open immersion into `ProjectiveLineBar`), so the
  --       induced map `(𝒰.f i).stalkMap y : stalk(Proj, Y.point) ⟶
  --       stalk(chart, y)` is an iso (`IsOpenImmersion.iff_isIso_stalkMap`).
  --
  --   (C) The chart's stalk at `y` identifies with `Localization.AtPrime
  --       y.asIdeal` via `Spec.stalkIso`. The chart's ring `Away 𝒜 (X i)`
  --       is isomorphic to `MvPolynomial Unit kbar` (project-local
  --       `homogeneousLocalizationAwayIso`); composing with `pUnitAlgEquiv`
  --       gives a ring iso to `Polynomial kbar`, a PID (Mathlib's
  --       `Polynomial.instEuclideanDomain` + `EuclideanDomain.toIsPrincipalIdealRing`
  --       + `IsPrincipalIdealRing.isDedekindDomain`).
  --
  --   (D) Conclude: in a Dedekind domain, localization at a non-zero prime
  --       ideal is a DVR via Mathlib's
  --       `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`.
  --
  -- The residual sub-claim — "the prime corresponding to `Y.point` in the
  -- chart is non-zero (equivalently: maximal, equivalently: `Y.point` is a
  -- closed point of `ProjectiveLineBar`)" — uses the coheight-1 hypothesis
  -- `Y.coheight : Order.coheight Y.point = 1`. The bridge from topological
  -- coheight to "prime is non-zero in the local affine chart" is a
  -- Mathlib-pending substrate (Stacks 02IZ / 005X; ``coheight on the
  -- specialisation preorder of a 1-dim integral scheme ⟹ point is
  -- closed''). This iter-196 advance lays the chart-pick + stalk-transfer
  -- skeleton; the final per-chart maximality bridge is the residual sorry.
  --
  -- **Step (A)**: Chart selection via the affine open cover.
  let 𝒰 := (projectiveLineBarAffineCover kbar).openCover
  let i := 𝒰.idx Y.point
  obtain ⟨y, hy⟩ := 𝒰.covers Y.point
  -- Now `y : 𝒰.X i = Spec(Away 𝒜 (X i))` with `(𝒰.f i).base y = Y.point`.
  --
  -- **Step (B)**: Open-immersion stalk transfer. The chart morphism is an
  -- open immersion, so its stalk map is an iso.
  have hopen : IsOpenImmersion (𝒰.f i) := inferInstance
  haveI hstalkIso : IsIso ((𝒰.f i).stalkMap y) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp hopen).2 y
  -- Step (B′): Transport `IsDiscreteValuationRing` from the chart stalk to
  -- the Proj stalk along the inverse of the (iso) stalkMap.
  -- The stalk map source is `Proj.presheaf.stalk ((𝒰.f i).base y)`; rewrite
  -- to `Proj.presheaf.stalk Y.point` using `hy`.
  have hbase : (𝒰.f i).base y = Y.point := hy
  rw [← hbase]
  -- New goal: `IsDiscreteValuationRing (Proj.presheaf.stalk ((𝒰.f i).base y))`.
  -- Set up the stalk iso (now usable since `hstalkIso : IsIso ((𝒰.f i).stalkMap y)`
  -- is in scope):
  have hiso : (ProjectiveLineBar kbar).left.presheaf.stalk ((𝒰.f i).base y) ≅
      (𝒰.X i).presheaf.stalk y := @asIso _ _ _ _ _ hstalkIso
  -- Domain on chart stalk: transport from `IsDomain (Proj stalk)` (which holds
  -- since `(ProjectiveLineBar kbar).left` is integral) via the iso `hiso`.
  haveI hDomProj : IsDomain ((ProjectiveLineBar kbar).left.presheaf.stalk
      ((𝒰.f i).base y)) := inferInstance
  haveI hDomChart : IsDomain ((𝒰.X i).presheaf.stalk y) :=
    MulEquiv.isDomain _ hiso.symm.commRingCatIsoToRingEquiv.toMulEquiv
  -- Suffices: the chart stalk at `y` is a DVR; transport along stalkMap iso.
  suffices hchart : IsDiscreteValuationRing ((𝒰.X i).presheaf.stalk y) by
    -- Apply RingEquiv-transport: chart ≃+* Proj.
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (hiso.symm.commRingCatIsoToRingEquiv)
  -- New goal: `IsDiscreteValuationRing ((𝒰.X i).presheaf.stalk y)`.
  --
  -- **Step (C)**: Identify chart stalk with `Localization.AtPrime y.asIdeal`
  -- via `Spec.stalkIso`. The chart `(𝒰.X i)` is by construction
  -- `Spec ((projectiveLineBarAffineCover kbar).X i) = Spec(Away 𝒜 (X i))`;
  -- the stalk at the point `y : Spec(Away 𝒜 (X i))` is `Localization.AtPrime
  -- y.asIdeal` (Mathlib `Spec.stalkIso`).
  have hspecstalk :
      (𝒰.X i).presheaf.stalk y ≅
      CommRingCat.of (Localization.AtPrime y.asIdeal) :=
    Spec.stalkIso ((projectiveLineBarAffineCover kbar).X i) y
  -- **Step (D)**: Establish PID / Dedekind structure on the chart ring
  -- `Away (projectiveLineBarGrading kbar) (X i)` via the iso to
  -- `MvPolynomial Unit kbar ≃ Polynomial kbar` (a Euclidean domain → PID →
  -- Dedekind).
  --
  -- The `(![X 0, X 1]) i` form appearing in the cover construction reduces
  -- definitionally to `MvPolynomial.X i`; we use the explicit `heq` to bridge.
  -- (`i` has type `𝒰.I₀ = Fin 2` but Lean needs a manual cast for `fin_cases`;
  -- we prove the universal statement and instantiate.)
  have heq : (![MvPolynomial.X 0, MvPolynomial.X 1] :
      Fin 2 → MvPolynomial (Fin 2) kbar) i = MvPolynomial.X i := by
    have h : ∀ (j : Fin 2), (![MvPolynomial.X 0, MvPolynomial.X 1] :
        Fin 2 → MvPolynomial (Fin 2) kbar) j = MvPolynomial.X j := by
      intro j; fin_cases j <;> rfl
    exact h i
  haveI hAwayIsDomain : IsDomain
      (HomogeneousLocalization.Away (projectiveLineBarGrading kbar)
        ((![MvPolynomial.X 0, MvPolynomial.X 1] :
            Fin 2 → MvPolynomial (Fin 2) kbar) i)) := by
    rw [heq]
    exact MulEquiv.isDomain _
      (homogeneousLocalizationAwayIso kbar i).toMulEquiv
  haveI hAwayPID : IsPrincipalIdealRing
      (HomogeneousLocalization.Away (projectiveLineBarGrading kbar)
        ((![MvPolynomial.X 0, MvPolynomial.X 1] :
            Fin 2 → MvPolynomial (Fin 2) kbar) i)) := by
    rw [heq]
    haveI : IsPrincipalIdealRing (MvPolynomial Unit kbar) :=
      IsPrincipalIdealRing.of_surjective
        (MvPolynomial.pUnitAlgEquiv kbar).symm.toRingHom
        (MvPolynomial.pUnitAlgEquiv kbar).symm.surjective
    exact IsPrincipalIdealRing.of_surjective
      (homogeneousLocalizationAwayIso kbar i).symm.toRingHom
      (homogeneousLocalizationAwayIso kbar i).symm.surjective
  haveI hAwayDed : IsDedekindDomain
      (HomogeneousLocalization.Away (projectiveLineBarGrading kbar)
        ((![MvPolynomial.X 0, MvPolynomial.X 1] :
            Fin 2 → MvPolynomial (Fin 2) kbar) i)) := inferInstance
  -- Bridge from the abstract instance class to the CommRingCat-lifted form
  -- that Mathlib's `Localization.AtPrime.isDomain` / `Spec.stalkIso`-consumers
  -- expect (`(projectiveLineBarAffineCover kbar).X i = .of (Away 𝒜 (![X 0, X 1] i))`
  -- is defeq, but typeclass synthesis doesn't unfold through `.of`).
  haveI hChartIsDomain : IsDomain
      ((projectiveLineBarAffineCover kbar).X i) := hAwayIsDomain
  haveI hChartDed : IsDedekindDomain
      ((projectiveLineBarAffineCover kbar).X i) := hAwayDed
  -- `y` is a point of `Spec (Away 𝒜 (X i))`, so `y.asIdeal` is a prime ideal.
  haveI hyPrime : y.asIdeal.IsPrime := y.isPrime
  -- The localization-at-prime `Localization.AtPrime y.asIdeal` is a domain
  -- (Mathlib `IsLocalization.isDomain_of_atPrime`).
  haveI hLocDom : IsDomain (Localization.AtPrime y.asIdeal) :=
    IsLocalization.isDomain_of_atPrime _ y.asIdeal
  -- **Residual maximality claim** (`y.asIdeal ≠ ⊥`): the only Mathlib-pending
  -- substrate gap. Equivalently, `y` is a closed point of `Spec(Away 𝒜 X_i)`
  -- (in a Dedekind domain, nonzero primes are exactly the maximal ideals).
  -- The bridge from the coheight-1 hypothesis `Y.coheight : Order.coheight
  -- Y.point = 1` (in the projective topology) to `y.asIdeal ≠ ⊥` (in the
  -- affine chart) uses two ingredients:
  --   • An open immersion preserves coheight at points within its image
  --     (Stacks 02IZ — opens of locally Noetherian schemes preserve
  --     codimension data).
  --   • In a 1-dim integral affine scheme (= `Spec(k̄[t])` after the
  --     chart-ring iso), coheight-1 points are precisely the closed points,
  --     i.e. maximal ideals.
  -- Once that bridge lands, this residual closes in ~5-10 LOC via
  -- `(Order.coheight_eq_one_of_isClosed_iff ...).mpr` or equivalent.
  have hy_ne_bot : y.asIdeal ≠ ⊥ := by
    -- **Iter-197 Lane I close** (Stacks 02IZ / 005X bridge):
    --   Suppose `y.asIdeal = ⊥`. Then `y` is the generic point of `Spec(R)`.
    --   The open immersion `𝒰.f i` sends the generic point of the (integral)
    --   chart to the generic point of the (integral) Proj scheme. So
    --   `Y.point = (𝒰.f i).base y = genericPoint ProjectiveLineBar`.
    --   But the generic point is the top of the scheme's specialisation
    --   preorder (`Scheme.le_iff_specializes` + `genericPoint_specializes`),
    --   hence `IsMax Y.point`, hence `Order.coheight Y.point = 0`.
    --   This contradicts `Y.coheight : Order.coheight Y.point = 1`.
    intro hbot
    -- Irreducibility of the affine chart (from `IsDomain` on the ring).
    haveI hIrredChart : IrreducibleSpace ↥(𝒰.X i) :=
      show IrreducibleSpace ↥(AlgebraicGeometry.Spec
        ((projectiveLineBarAffineCover kbar).X i)) from inferInstance
    -- Irreducibility of `ProjectiveLineBarScheme kbar` (= `(...).left`).
    haveI hIntegralPLBS : IsIntegral (ProjectiveLineBarScheme kbar) :=
      (‹IsIntegral (ProjectiveLineBar kbar).left› :
        IsIntegral (ProjectiveLineBarScheme kbar))
    haveI hIrredPLBS : IrreducibleSpace ↥(ProjectiveLineBarScheme kbar) :=
      inferInstance
    -- `y` (with `y.asIdeal = ⊥`) is the generic point of the chart.
    have hy_eq_gen : y = genericPoint ↥(𝒰.X i) := by
      have hbot_gen : genericPoint ↥(𝒰.X i) =
          (⊥ : PrimeSpectrum ↑((projectiveLineBarAffineCover kbar).X i)) :=
        AlgebraicGeometry.genericPoint_eq_bot_of_affine _
      rw [hbot_gen]
      exact PrimeSpectrum.ext hbot
    -- Open immersion sends generic point to generic point.
    have hbase_gen :
        (𝒰.f i).base y = genericPoint ↥(ProjectiveLineBarScheme kbar) := by
      rw [hy_eq_gen]
      exact AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion (𝒰.f i)
    -- Combine with `hbase : (𝒰.f i).base y = Y.point`.
    have hY_gen : Y.point = genericPoint ↥(ProjectiveLineBarScheme kbar) :=
      hbase ▸ hbase_gen
    -- The generic point is the top of the scheme's specialisation order.
    have hY_isMax : IsMax Y.point := by
      rw [hY_gen]
      intro b _
      exact Scheme.le_iff_specializes.mpr (genericPoint_specializes b)
    -- Hence `coheight Y.point = 0`, contradicting `Y.coheight = 1`.
    have hY_coheight_zero : Order.coheight Y.point = 0 :=
      Order.IsMax.coheight_eq_zero hY_isMax
    rw [Y.coheight] at hY_coheight_zero
    exact one_ne_zero hY_coheight_zero
  haveI hLocDVR : IsDiscreteValuationRing (Localization.AtPrime y.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      _ hy_ne_bot _
  -- Transport DVR back to the chart stalk via `hspecstalk.symm`.
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    hspecstalk.symm.commRingCatIsoToRingEquiv

/-- **Hartshorne II.6.9 specialised to `D = [∞]`** — typed-sorry pin (body
iter-194+).

For a smooth proper geometrically irreducible curve `C` over an algebraically
closed field `kbar`, equipped with a finite `k̄(ℙ¹)`-algebra structure on
`K(C)` (the canonical `φ`-induced one for a non-constant morphism
`φ : C → ℙ¹`), and a non-zero element `t ∈ K(ℙ¹)` which is a **uniformiser**
on `ℙ¹` (its zero divisor has degree `1`, encoded by `hLPUnif`: a unique
prime divisor `Y₀` of `ℙ¹` with `order Y₀ t = 1`, and no other prime
divisor has positive order), the degree of the positive part of the
principal divisor of `algebraMap K(ℙ¹) K(C) t` equals the function-field
extension degree:
\[
  \deg\bigl((\mathrm{div}\,(\varphi^{\#}\,t))_0\bigr)
  \;=\; [K(C) : k̄(\mathbb{P}^1)] \;=\;
   \mathrm{Module.finrank}_{k̄(\mathbb{P}^1)} K(C).
\]
Equivalently, `(div (φ^# t))_0 = φ^*[Y₀]` and `deg(φ^*[Y₀]) = deg(φ)`
(Hartshorne II.6.9 specialised at the divisor `[Y₀] ∈ Div(ℙ¹)`).

**Iter-194 refactor v2** (lane-i-localparameter-signature-v2):
the signature now drops the abstract `K` parameter and pins to
`(ProjectiveLineBar kbar).left.functionField`, with the uniformiser
hypothesis `hLPUnif` enforcing the local-parameter constraint
correctly (iter-193 `hlp` was insufficient; counter-witness
`K=K(C), t=u(u-1)` is now excluded because `t` lives strictly in
`K(ℙ¹)` and `hLPUnif` requires `t` to have a single zero of order
`1` on ℙ¹, ruling out functions with multiple zeros). The body
(~50-80 LOC owed iter-194+) chains
`Ideal.sum_ramification_inertia` + `Ideal.finrank_quotient_map` on
the Dedekind extension `A → B` at the maximal ideal
`m_{Y₀} = (t) ⊂ A`, per `analogies/ratcurveiso-pin2.md` Decision 2.

Blueprint reference: `lem:degree_positivePart_principal_eq_finrank`
(Hartshorne II.6.9, p. 137; chapter `RiemannRoch_WeilDivisor.tex` §6). -/
theorem degree_positivePart_principal_eq_finrank
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (C : Over (Spec (.of kbar))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    [IsIntegral C.left] [IsLocallyNoetherian C.left]
    [Scheme.IsRegularInCodimensionOne C.left]
    [IsIntegral (ProjectiveLineBar kbar).left]
    [IsLocallyNoetherian (ProjectiveLineBar kbar).left]
    [Scheme.IsRegularInCodimensionOne (ProjectiveLineBar kbar).left]
    [Algebra (ProjectiveLineBar kbar).left.functionField
       C.left.functionField]
    [Module.Finite (ProjectiveLineBar kbar).left.functionField
       C.left.functionField]
    (t : (ProjectiveLineBar kbar).left.functionField)
    (halg : algebraMap (ProjectiveLineBar kbar).left.functionField
       C.left.functionField t ≠ 0)
    (hLPUnif : ∃ Y₀ : (ProjectiveLineBar kbar).left.PrimeDivisor,
       Scheme.RationalMap.order Y₀ t = 1 ∧
       ∀ Y : (ProjectiveLineBar kbar).left.PrimeDivisor,
         Scheme.RationalMap.order Y t > 0 → Y = Y₀) :
    degree (positivePart
      (principal (algebraMap _ C.left.functionField t) halg)) =
      (Module.finrank (ProjectiveLineBar kbar).left.functionField
                       C.left.functionField : ℤ) := by
  -- **Iter-194 refactor v2** (lane-i-localparameter-signature-v2):
  -- the signature now drops the abstract `K` parameter and pins to
  -- `(ProjectiveLineBar kbar).left.functionField`, with the uniformiser
  -- hypothesis `hLPUnif` enforcing the local-parameter constraint
  -- correctly (iter-193 `hlp` was insufficient; counter-witness
  -- `K=K(C), t=u(u-1)` is now excluded because `t` lives strictly in
  -- `K(ℙ¹)` and `hLPUnif` requires `t` to have a single zero of order
  -- 1 on ℙ¹, ruling out functions with multiple zeros).
  --
  -- **Iter-194 partial structural advance.** We unpack the uniformiser
  -- witness to expose `Y₀ : PrimeDivisor(ℙ¹)`, but the body's main chain
  -- (`Ideal.sum_ramification_inertia` + `Ideal.finrank_quotient_map` on
  -- the Dedekind extension `A → B` at the maximal ideal `m_Y₀ = (t) ⊂ A`)
  -- requires the scheme-level morphism `φ : C → ℙ¹` and affine-chart
  -- transfer from the function-field embedding `algebraMap`. The
  -- function-field-determines-curve correspondence (Hartshorne I.6.12)
  -- and the affine-chart pullback bridge are themselves a Mathlib-pending
  -- substrate (no `Scheme.Hom.ofFunctionFieldEmbedding` constructor or
  -- `IsLocalization.AtPrime` ↔ `presheaf.stalk` bridge ships in
  -- `b80f227`). The full body is therefore deferred to iter-195+, contingent
  -- on the affine-chart-bridge substrate landing in `AbelianVarietyRigidity`
  -- (Lane E) via `pullbackSpecIso`.
  classical
  obtain ⟨Y₀, hY₀_one, hY₀_unique⟩ := hLPUnif
  -- `Y₀ : PrimeDivisor(ℙ¹)` is the unique zero of `t` on ℙ¹ with order 1.
  -- `hY₀_one : Scheme.RationalMap.order Y₀ t = 1`
  -- `hY₀_unique` : every other prime divisor with positive order = Y₀.
  -- (Both used downstream when the affine-chart bridge lands.)
  --
  -- **Iter-195 Y₀ pull-through cleanup.** Push the LHS through the two
  -- Mathlib-clean Finsupp reductions:
  --   Step A: `degree (positivePart D) = Σ_{Y ∈ supp D} max (D Y) 0`
  --           (via `degree_positivePart_eq_sum_max`, iter-192 helper);
  --   Step B: `Σ_{Y ∈ supp D} max (D Y) 0 = Σ_{Y ∈ supp D, 0 < D Y} D Y`
  --           (via `Finsupp.sum_max_zero_eq_sum_filter_pos`, iter-195 helper).
  -- After Steps A + B the goal reads
  --   `∑ Y ∈ supp(div_f) with 0 < ord_Y f, ord_Y f = Module.finrank K(ℙ¹) K(C)`
  -- where `f := algebraMap K(ℙ¹) K(C) t`.
  --
  -- The remaining gap is exactly Hartshorne II.6.9 (Stacks 0BE6,
  -- multiplicativity of degree under finite morphisms): the positive-order
  -- prime divisors of `f` on `C` are precisely the prime divisors lying
  -- over the unique zero `Y₀` of `t` on `ℙ¹` (i.e. the closed points
  -- of `φ⁻¹(Y₀)` for the morphism `φ : C → ℙ¹` induced by `algebraMap`),
  -- and summing their `ord` values reproduces the function-field extension
  -- degree via `Ideal.sum_ramification_inertia` + `Ideal.finrank_quotient_map`
  -- at the maximal ideal `m_{Y₀} ⊂ A := k̄[Y₀^{-1}]`. The scheme→ring
  -- bridge is `Scheme.Hom.ofFunctionFieldEmbedding` (no Mathlib
  -- constructor as of `b80f227`; cf. analogist verdict
  -- NEEDS_MATHLIB_GAP_FILL on the Hartshorne I.6.12 correspondence).
  rw [degree_positivePart_eq_sum_max,
      Finsupp.sum_max_zero_eq_sum_filter_pos]
  -- Goal now: `∑ Y ∈ (principal (algebraMap _ _ t) halg).support.filter
  --              (fun Y => 0 < (principal _ _) Y), (principal _ _) Y =
  --              (Module.finrank K(ℙ¹) K(C) : ℤ)`.
  --
  -- **Step C (iter-195 push)**: rewrite the per-coefficient finsupp
  -- application to the order function via `principal_apply`. After this,
  -- the LHS displays in its mathematical form
  --   `∑ Y ∈ supp(div_f) with 0 < ord_Y f, ord_Y f`,
  -- where `f := algebraMap K(ℙ¹) K(C) t`. The remaining content of the
  -- proof is the ramification-inertia bridge (Hartshorne II.6.9 +
  -- function-field correspondence), substrate-gated below.
  have hbridge : ∀ Y : C.left.PrimeDivisor,
      (show (C.left.PrimeDivisor →₀ ℤ) from
        principal ((algebraMap _ C.left.functionField) t) halg) Y =
        Scheme.RationalMap.order Y
          ((algebraMap _ C.left.functionField) t) := by
    intro Y; exact principal_apply _ halg Y
  -- Use `hbridge` to rewrite the summand AND the filter predicate to
  -- the order-on-the-curve form. The final goal reads
  --   `∑ Y ∈ supp(div_f) with 0 < ord_Y f, ord_Y f =
  --      (Module.finrank K(ℙ¹) K(C) : ℤ)`
  -- where `f := algebraMap K(ℙ¹) K(C) t`, i.e. the Hartshorne II.6.9
  -- ramification-inertia starting form.
  simp_rw [hbridge]
  -- Iter-196+ closure: introduce a named `Scheme.Hom.ofFunctionFieldEmbedding`
  -- substrate, port `Ideal.sum_ramification_inertia` to it via the
  -- affine-chart pullback bridge, and use `hY₀_one` + `hY₀_unique` on
  -- ℙ¹ side to control the filter set.
  sorry

/-! ## §7. Linear equivalence and the divisor class group -/

/-- **Linear equivalence of Weil divisors.**

Two Weil divisors `D, D' ∈ Div(X)` are linearly equivalent, written `D ~ D'`, if
and only if there exists a nonzero rational function `f ∈ K(X)^×` with
`D - D' = div(f) ∈ Div(X)`.

`~` is an equivalence relation (reflexivity from `div(1) = 0`, symmetry from
`div(f⁻¹) = -div(f)`, transitivity from `div(fg) = div(f) + div(g)`, all via
`thm:principal_hom`). The quotient `Cl(X) := Div(X) / im(div)` is the
**divisor class group** of `X`.

On a smooth proper curve `C` over `k̄`, `thm:principal_deg_zero` shows the
degree map descends to `deg : Cl(C) → ℤ`.

Blueprint reference: `def:linear_equivalence` (Hartshorne II §6 p. 131). -/
def LinearEquivalence [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [Scheme.IsRegularInCodimensionOne X] (D D' : X.WeilDivisor) : Prop :=
  ∃ (f : X.functionField) (hf : f ≠ 0), D - D' = principal f hf

end Scheme.WeilDivisor

end AlgebraicGeometry
