# Analogy: Mathlib API path for `Scheme.RationalMap.order`

## Mode
api-alignment

## Slug
dvr-rationalmap-order

## Iteration
175

## Question
For the body of `AlgebraicGeometry.Scheme.RationalMap.order`
(`AlgebraicJacobian/RiemannRoch/WeilDivisor.lean` L140), what is the correct
Mathlib API path to (a) extract the discrete valuation at a codim-1 point of
a (locally noetherian, regular-in-codim-1) integral scheme, (b) extend that
valuation from the local ring to the fraction field, and (c) handle the
junk-on-`f = 0` convention?

## Project artifact(s)
- `AlgebraicJacobian/RiemannRoch/WeilDivisor.lean`:140-142 — `RationalMap.order` body sorry.
- `blueprint/src/chapters/RiemannRoch_WeilDivisor.tex`, `def:order_at_point` block (statement-only `\leanok`).
- `AlgebraicJacobian/RiemannRoch/WeilDivisor.lean`:80-97 — `Scheme.PrimeDivisor`
  carrier (`coheight : Order.coheight point = 1`).

## Decisions identified

### Decision 1: Use `Ring.ordFrac` vs. roll-your-own DVR-`addVal`-then-extend

- **Mathlib idiom**: `Ring.ordFrac R : K →*₀ ℤᵐ⁰` (with `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`),
  defined at `Mathlib.RingTheory.OrderOfVanishing.Basic:324` (Stacks `02MD`). The
  hypotheses are exactly `[CommRing R] [Nontrivial R] [IsNoetherianRing R]
  [Ring.KrullDimLE 1 R]` plus `[Field K] [Algebra R K] [IsFractionRing R K]`.
  Internally `ordFrac` extends `Ring.ordMonoidWithZeroHom R : R →*₀ ℤᵐ⁰` to the
  fraction field via `Submonoid.LocalizationMap.lift₀` (the `lift₀` already
  handles the units-mapping discharge). The integer value on `r ∈ R` is the
  length of `R / (r)` (= the DVR valuation for an `r`-uniformised local DVR);
  on `a/b ∈ K`, it is `ord(a) - ord(b)` (in `Multiplicative ℤ` terms).
  Why Mathlib chose it: the natural codim-1 generality covers BOTH the
  global-Noetherian / Krull-dim-1 case (Dedekind domains, regular curves) and
  the strictly local DVR case; one definition serves both — the DVR
  `addVal` is then derivable as a corollary, not a prerequisite. The
  intermediate length-of-quotient definition `Ring.ord` (Stacks 02MD) is what
  lets the same formula work in any Krull-dim-≤-1 ring (not just DVRs).
- **Project's current path**: bare `sorry` body (iter-172 file-skeleton); the
  iter-174 docstring comment proposes "extract DVR addVal then extend to
  fraction field", which is the parallel-API path.
- **Gap**: divergent-with-cost (project's proposed path is parallel API; the
  shipped body has nothing yet, so the cost is *avoidance* of the parallel
  build, not refactor of shipped code).
- **Cost of divergence (if Project goes its own way)**:
  - 4–6 bridge lemmas to materialise an `AddValuation` on the stalk and lift
    to the fraction field (`IsDiscreteValuationRing.addVal` produces
    `AddValuation R ℕ∞`; `AddValuation.ofValuation` round-trips through
    `Valuation R (Multiplicative ℕ∞ᵒᵈ)`; `Valuation.extendToLocalization`
    needs the supp-disjoint side condition; finally the `ℕ∞ → ℤ` cast adds
    a junk choice on `⊤`). Each step is a separate definition and proof.
  - Downstream: `principal` (`Mathlib`-style `K → Div(X)` Finsupp) cannot
    consume `IsDedekindDomain.HeightOneSpectrum.valuation`-style adic
    valuations directly; it gets a project-bespoke `addVal` that must be
    bridged again at every Hartshorne-style identity (`v_Y(fg) = v_Y(f) +
    v_Y(g)`, etc.).
  - Loses access to `Ring.ord_mul`, `ord_pow`, `ord_of_isUnit`,
    `ordMonoidWithZeroHom_eq_ord`, `ordFrac_eq_div` — every algebraic
    identity needed for `thm:principal_hom` would be re-proved.
- **Verdict**: **ALIGN_WITH_MATHLIB** — the body must use `Ring.ordFrac`.

### Decision 2: Junk-on-`f = 0` convention (`ℤᵐ⁰ → ℤ` extraction)

- **Mathlib idiom**: `WithZero.log : ℤᵐ⁰ → ℤ` from
  `Mathlib.Algebra.GroupWithZero.WithZero:394`, defined as
  `x.recZeroCoe 0 Multiplicative.toAdd`. Properties:
  - `log_zero : log 0 = 0` (the junk-on-zero convention)
  - `log_exp : log (exp a) = a` (round-trip on nonzero)
  - `log_mul : log (x * y) = log x + log y` for `x, y ≠ 0` (the additive
    valuation identity that `thm:principal_hom` will downstream consume).
  This is the *named* Mathlib idiom for converting `ℤᵐ⁰` (the multiplicative
  value group with junk-zero) to the additive `ℤ` value group with junk-zero.
  The dual `WithTop ℤ → ℤ` is `WithTop.untop₀` (used by
  `MeromorphicOn.divisor` at `Mathlib.Analysis.Meromorphic.Divisor`); for our
  multiplicative-value-group case `WithZero.log` is the direct match.
  Why Mathlib chose it: it makes the junk choice canonical and reusable, so
  every downstream identity (e.g. `log_mul`, `log_pow`) lands as a `simp`
  lemma rather than a per-call-site case-split.
- **Project's current path**: not chosen yet (statement-only).
- **Gap**: identical (no prior project pin to compare).
- **Verdict**: **ALIGN_WITH_MATHLIB** — use `WithZero.log`.

### Decision 3: DVR-from-codim-1 chain (closing the typeclass synthesis)

- **Mathlib idiom**:
  - `AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian`
    (`Mathlib.AlgebraicGeometry.Noetherian`): for `[IsLocallyNoetherian X]`,
    the stalk is `IsNoetherianRing`.
  - `AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegral`
    (`Mathlib.AlgebraicGeometry.FunctionField`): for `[IsIntegral X]`, every
    stalk is `IsDomain` (hence `Nontrivial`).
  - `AlgebraicGeometry.instIsFractionRingCarrierStalkCommRingCatPresheafFunctionField`
    (`Mathlib.AlgebraicGeometry.FunctionField`): for `[IsIntegral X]`, the
    function field is a fraction ring of the stalk at every point — so
    `[IsFractionRing (X.presheaf.stalk Y.point) X.functionField]` is
    automatic.
  - For Krull-dim-1: `IsLocalization.AtPrime.ringKrullDim_eq_height`
    (`Mathlib.RingTheory.Ideal.Height`) + `IsAffineOpen.isLocalization_stalk`
    (`Mathlib.AlgebraicGeometry.AffineScheme`) gives
    `ringKrullDim (stalk) = primeIdealOf(x).height`.
- **Project's current path**: the chapter pre-pins (iter-173 prose, blueprint
  L98–L112) the project-side conjunction
  `∀ x, Order.coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x)`,
  not yet bundled as a typeclass.
- **Gap**: divergent-and-incomplete — **Mathlib has no direct
  `Order.coheight x = 1 → Ring.KrullDimLE 1 (X.presheaf.stalk x)` bridge**.
  The missing fact is the topological identity "coheight of `x` in the
  scheme's specialisation preorder equals the height of the prime ideal
  corresponding to `x` in any affine chart" (Stacks `02IZ` / `005X`). The
  step "ideal height → stalk Krull dim" is in Mathlib
  (`IsLocalization.AtPrime.ringKrullDim_eq_height`); the topological-to-
  prime-spectrum bridge is the gap.
- **Cost of divergence**: low for iter-175 — the workaround is to
  thread `[Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]` (or the explicit
  `[IsDiscreteValuationRing (X.presheaf.stalk Y.point)]` if downstream cares)
  as an explicit instance/hypothesis on the `order` signature at iter-175;
  the topological bridge can be deferred to a later iter or upstreamed to
  Mathlib as a small PR.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** for the topological coheight bridge;
  **PROCEED** with explicit-instance threading for iter-175.

## Recommendation

**Body of `RationalMap.order` (iter-175 prover lane):**

```lean
noncomputable def order {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (Y : X.PrimeDivisor)
    [Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]
    (f : X.functionField) : ℤ :=
  WithZero.log (Ring.ordFrac (X.presheaf.stalk Y.point) f)
```

Rationale per decision:

1. **`Ring.ordFrac`** is the canonical Mathlib API for "extension of the DVR
   `addVal` to the fraction field, in a way that respects the units-on-`R^×`
   and gives a `K →*₀ ℤᵐ⁰` monoid-with-zero hom". It works for ANY Noetherian
   Krull-dim-≤-1 commutative ring; under the project's additional
   `regular-in-codim-1` standing hypothesis the same value coincides with
   `IsDiscreteValuationRing.addVal` cast to `ℤ` (via the chain
   `ordFrac_eq_ord` ⟹ `ordMonoidWithZeroHom_eq_ord` ⟹ DVR `addVal_uniformizer`).
2. **`WithZero.log`** is the canonical `ℤᵐ⁰ → ℤ` projection with junk-on-zero;
   `log 0 = 0`, and `log_mul`/`log_pow` give the additive-valuation algebra
   identities `thm:principal_hom` will downstream consume for free.
3. **Typeclass threading**: add `[IsLocallyNoetherian X]` and
   `[Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]` as instance arguments on
   the `order` signature. The `IsFractionRing` instance is automatic from
   `[IsIntegral X]`; `Nontrivial` of the stalk is automatic from
   `IsDomain`. The codim-1 stalk instance is the project-side workaround for
   the missing Mathlib topological bridge (Decision 3).

**Downstream impact (for `principal`, `principal_hom`):**

- `principal f hf` becomes `Finsupp.onFinset`-style construction with
  Hartshorne 6.1 supplying finite support; values are
  `order Y f = WithZero.log (Ring.ordFrac _ f)`.
- `principal_hom` reduces to `log_mul` / `log_one` on the underlying `ℤᵐ⁰`
  values, applied prime-divisor-wise.
- `principal_degree_zero`'s sub-build (Hartshorne 6.10) is unchanged by this
  decision — the proof goes through the finite morphism into `ℙ¹` either way.

**Blueprint-side gap closure (writer's task this plan-phase):**

The `def:order_at_point` block should add a "Lean encoding" paragraph pinning
the API choice as:

> Lean encoding: `order Y f := WithZero.log (Ring.ordFrac (X.presheaf.stalk
> Y.point) f)`, where `Ring.ordFrac` is Mathlib's monoid-with-zero hom
> `K →*₀ ℤᵐ⁰` from `Mathlib.RingTheory.OrderOfVanishing.Basic` (Stacks 02MD).
> The junk-on-`f = 0` convention is `order Y 0 = 0`, inherited from
> `WithZero.log 0 = 0`. The Krull-dim-1 hypothesis on the stalk is threaded
> as `[Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]` (the topological
> coheight → stalk Krull-dim bridge is Mathlib-upstream-pending; see
> Stacks 02IZ).

**Mathlib upstream opportunity (optional, not iter-175 blocking):**

A two-line PR to Mathlib pinning the bridge
`Order.coheight (x : (Spec R)) = (asIdeal x).height` (and the `Scheme`-level
corollary via `IsAffineOpen.isLocalization_stalk`) would let the project
**drop** the explicit `[Ring.KrullDimLE 1 _]` argument and synthesise it
purely from `Order.coheight Y.point = 1` (via the structure carrier). This
is the cleanest long-term shape but is *not* on the iter-175 critical path.
