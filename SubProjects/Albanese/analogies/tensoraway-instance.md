# Analogy: `CommRing`/`Algebra` instance synthesis for `TensorProduct kbar (HomogeneousLocalization.Away 𝒜 (X i)) (GmRing kbar)`

## Mode
api-alignment

## Slug
tensoraway

## Iteration
170

## Question

Does `TensorProduct kbar (HomogeneousLocalization.Away 𝒜 (X i)) (Localization.Away (X ()))`
admit a `CommRing` instance via `inferInstance`? If not, is the missing hop a real
Mathlib gap (case i), synthesis-friction with a Mathlib-canonical fix (case ii), or
a mistake (case iii)? And: does `projGm_isReduced` close via the same chart-cover
idiom (Q5)?

## Project artifact(s)
- `AlgebraicJacobian/Genus0BaseObjects.lean:685-687` — `gmScalingP1` body (sorry).
- `AlgebraicJacobian/Genus0BaseObjects.lean:78-84` — `projectiveLineBarGrading` + its
  `GradedRing` instance.
- `AlgebraicJacobian/Genus0BaseObjects.lean:520-525` — `GmRing` (alias for
  `Localization.Away (X () : MvPolynomial Unit kbar)`).
- `AlgebraicJacobian/Genus0BaseObjects.lean:819-823` — `projGm_isReduced` (sorry).

## Decisions identified

### Decision Q1: existence of `CommRing (TensorProduct kbar (Away 𝒜 (X i)) (GmRing kbar))`

- **Mathlib idiom**: `Algebra.TensorProduct.instCommRing` fires whenever both
  factors are commutative `R`-algebras (`R = kbar` here). Cite:
  `Mathlib.RingTheory.TensorProduct.Basic`. The two factors must each carry:
  (a) a `CommRing` instance and (b) an `Algebra kbar _` instance.

  - `CommRing (HomogeneousLocalization 𝒜 x)` — shipped via
    `HomogeneousLocalization.homogeneousLocalizationCommRing` at
    `Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:473`.
  - `Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x)` — shipped at the same file,
    L509. **`Algebra kbar (HomogeneousLocalization 𝒜 x)` is NOT shipped** (the
    base ring of an `Algebra (𝒜 0)`-style instance does not auto-propagate to the
    underlying base of `𝒜`'s ambient module).
  - `CommRing (Localization.Away _)` and `Algebra kbar (GmRing kbar)` — shipped
    (Mathlib treats `GmRing` correctly as a `kbar`-algebra via
    `Localization.Away` + its base algebra).

- **Project's current path** (per iter-169 prover note): blocked on assuming
  `inferInstance : CommRing (TensorProduct kbar (Away 𝒜 _) (GmRing kbar))` would
  fire and finding it does not. The prover guessed "likely already there via
  `HomogeneousLocalization.instCommRing` — to verify" — but the missing piece is
  not `CommRing (Away 𝒜 _)` (which IS shipped) but
  **`Algebra kbar (Away 𝒜 _)`** (which is NOT shipped because Mathlib only ships
  `Algebra (𝒜 0)`).

- **Gap**: divergent-with-cost — the friction is real but minimal. Fixed by a
  one-line instance declaration.

- **Verdict on Q1**: case **(ii) synthesis-friction**, with a trivial canonical
  fix. Verified end-to-end via `lean_run_code` (5-line MWE; instance closes both
  `CommRing` and `Algebra kbar` on the tensor product).

### Decision Q2: the canonical fix

- **Mathlib idiom**: `Algebra.compHom B (f : R →+* S)`, where `[Algebra S B]`,
  derives `Algebra R B` via the composition `R →+* S →+* B`. Cite:
  `Mathlib.Algebra.Algebra.Defs` (`def Algebra.compHom`).

- **The 3-line project instance** to land in `Genus0BaseObjects.lean` (or its
  upstream chart-ring section, before any `TensorProduct kbar (Away 𝒜 _) _` is
  used):

  ```lean
  /-- `kbar`-algebra structure on `HomogeneousLocalization.Away 𝒜 f` via the
  composition `kbar →+* ↥(𝒜 0) →+* Away 𝒜 f`. Mathlib only ships
  `Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x)`; this instance bridges the
  remaining `kbar →+* 𝒜 0` algebra map shipped via
  `SetLike.GradeZero.instAlgebra`. Required for `TensorProduct kbar (Away _ _) _`
  to synthesize `CommRing`/`Algebra kbar`. -/
  noncomputable instance algebraKbarAway
      (f : MvPolynomial (Fin 2) kbar) :
      Algebra kbar
        (HomogeneousLocalization.Away (projectiveLineBarGrading kbar) f) :=
    Algebra.compHom _ (algebraMap kbar ((projectiveLineBarGrading kbar) 0))
  ```

  **Verified**: with this instance in scope, both

  ```lean
  CommRing (TensorProduct kbar (Away 𝒜 (X i)) (GmRing kbar))
  Algebra kbar (TensorProduct kbar (Away 𝒜 (X i)) (GmRing kbar))
  ```

  fire via `inferInstance`. No `letI` / `change` / `show` needed at the call
  site.

- **Verdict on Q2**: **PROCEED** with the `Algebra.compHom` recipe above (3
  lines, one named `instance`). This is the Mathlib-canonical idiom for building
  an algebra structure as a composition through an intermediate algebra. The
  prover's iter-169 escalation to "build the chart target as an explicit
  `Localization.Away` quotient" was over-engineered for this gap.

### Decision Q3: upstream cost

- Not applicable — Q1 returns (ii), not (i). For completeness: an upstream PR
  would generalize Mathlib's `instance : Algebra (𝒜 0) (HomogeneousLocalization
  𝒜 x)` (HomogeneousLocalization.lean:509) to

  ```lean
  instance [CommRing R] [Algebra R (𝒜 0)] :
      Algebra R (HomogeneousLocalization 𝒜 x) :=
    Algebra.compHom _ (algebraMap R (𝒜 0))
  ```

  along with the `IsScalarTower R (𝒜 0) (HomogeneousLocalization 𝒜 x)`
  companion instance. ~5 LOC total. Worth a PR (genuinely useful for any
  consumer that wants `Algebra kbar (Away 𝒜 _)` in the relative-Proj setting),
  but **not on the critical path** for iter-170: the project-side instance is
  trivial and unblocks the prover lane immediately.

- **Verdict on Q3**: **NEEDS_MATHLIB_GAP_FILL** (low-priority, optional upstream
  PR). Land the project-side instance now; the upstream PR is a follow-up.

### Decision Q4: alternative chart-target representation

- **Alternative considered**: route through a single
  `Localization.Away` of `MvPolynomial (Fin 3) kbar` (variables `X 0, X 1, t`)
  at the multiplicative element `X i * t`, then identify the result with
  `Away 𝒜 (X i) ⊗ GmRing`.

- **Cost**: building the ring iso between
  `Localization.Away (X i * t : MvPoly (Fin 3) kbar)` and
  `Away 𝒜 (X i) ⊗ GmRing` requires either:
  - Universal-property argument via `MvPolynomial.aeval` + `IsLocalization.lift`
    (~30-50 LOC, plus ~20 LOC to identify with `pullbackSpecIso`'s consumed shape).
  - Or routing the chart-side ring map through this alternative ring entirely
    (avoiding the tensor) — possible but loses `pullbackSpecIso` directly, since
    the latter expects a tensor-product shape.

- **Verdict on Q4**: **PROCEED with the Q2 instance — NOT the alternative.**
  The 3-line `Algebra.compHom` instance is 10x cheaper than the
  `Localization.Away` route. The alternative was only on the table because the
  prover believed the tensor route was completely blocked; once the instance is
  filled, the tensor route is the cleanest.

### Decision Q5: `projGm_isReduced` via chart-cover

- **Setup**: cover `((ProjectiveLineBar kbar) ⊗ Gm kbar).left` by pullbacks of
  the chart cover. Each chart is `pullback (chart_i) Gm`, identifiable via
  `pullbackSpecIso` with `Spec(Away 𝒜 (X i) ⊗_{kbar} GmRing)`. For each
  `i : Fin 2`, need the tensor ring to be reduced (or even a domain).

- **Available Mathlib bridges**:
  - `IsLocalization.Away.tensor` (`RingTheory/Localization/BaseChange.lean`,
    after L320) — gives `IsLocalization.Away (algebraMap R S r) (S ⊗[R] A)` when
    `A` is `IsLocalization.Away r` over `R`. **Doesn't fire here**: `GmRing` is
    `Localization.Away (X () : MvPolynomial Unit kbar)`, where `X () ∉ kbar`.
  - `IsGeometricallyReduced.isReduced_tensorProduct_of_isAlgebraic` at
    `RingTheory/Nilpotent/GeometricallyReduced.lean:52`. Requires
    `IsGeometricallyReduced kbar (Away 𝒜 (X i))` (a domain over an alg-closed
    field is geometrically reduced, **but this fact is not packaged as an
    instance over an arbitrary alg-closed field** — see below).
  - `Subalgebra.LinearDisjoint.isDomain` style results for "tensor of domains is
    a domain" all require `LinearDisjoint` hypotheses — **not free** for two
    independently-built algebras (no Mathlib lemma "tensor of two
    `IsDomain` `kbar`-algebras over an alg-closed `kbar` is `IsDomain`").

- **Recommended route**: the chart-cover strategy needs an extra ingredient —
  identifying `Away 𝒜 (X i) ⊗_{kbar} GmRing` as a localization of
  `Away 𝒜 (X i) [t]` (polynomial ring in one variable) at the image of `t`.
  This requires `homogeneousLocalizationAwayIso` (the iso
  `Away 𝒜 (X i) ≃+* MvPolynomial Unit kbar`) from
  `analogies/gmscaling-deep.md` Q2 to land first. After that:
  - `(MvPoly Unit kbar) ⊗[kbar] (Localization.Away (X ())) ≅
     Localization.Away (1 ⊗ X ()) (MvPoly Unit kbar ⊗ MvPoly Unit kbar)`
    via routine tensor-of-localization machinery; the LHS is a localization of
    a polynomial ring (i.e. of `kbar[u, t]`), hence a domain.
  - This gives `IsDomain` of each chart ring, hence `IsReduced`, hence the
    chart-cover route closes.
  - Total LOC for the chart-cover route, AFTER `homogeneousLocalizationAwayIso`
    lands: ~50-80 LOC (one chart-cover lemma + 4-5 ring-iso bridge lemmas).

- **Verdict on Q5**: **DOWNSTREAM of `gmscaling-deep.md` Q2**. The Mathlib
  `Algebra.TensorProduct.NoZeroDivisors`-style instance for two domains over a
  field is **not shipped in a form that fires here**, so `IsDomain`-based routes
  require the `kbar[u]`-identification. Don't tackle `projGm_isReduced` in
  iter-170 unless `homogeneousLocalizationAwayIso` also lands. Keep as
  scaffold-sorry.

## Recommendation

**Iter-170 prover lane (≤50 words):** Land the 3-line `algebraKbarAway` instance
via `Algebra.compHom` immediately after the `projectiveLineBarGrading_gradedRing`
instance. The chart-glue route (a) is unblocked: `CommRing` and `Algebra kbar`
on `TensorProduct kbar (Away 𝒜 _) (GmRing kbar)` then fire via `inferInstance`.
No `Localization.Away` quotient alternative needed. `projGm_isReduced` stays
gated on `homogeneousLocalizationAwayIso`.
