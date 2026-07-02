# `projectiveLineBar_smoothOfRelDim`: `ℙ¹_{k̄}` is smooth of relative dimension 1

**File:** `AlgebraicJacobian/Genus0BaseObjects/BareScheme.lean` (L161-163)
**Status:** scaffold `sorry` since iter-165; Mathlib gap. File flagged "off-limits this iteration" in `PROGRESS.md` iter-182.
**Confirmed-missing Mathlib pieces (search exhaustive iter-182):**
- No `SmoothOfRelativeDimension n` instance for `Proj` of any graded ring.
- No `IsStandardSmoothOfRelativeDimension R (MvPolynomial σ R)` lemma (would need to construct the `SubmersivePresentation` by hand).

## Claim

```
instance projectiveLineBar_smoothOfRelDim (kbar : Type u) [Field kbar] :
    SmoothOfRelativeDimension 1 (ProjectiveLineBar kbar).hom
```

i.e. the projective line `Proj k̄[X₀, X₁] → Spec k̄` is smooth of relative dimension `1`.

## Mathematical proof sketch

Smoothness of relative dimension `n` for a scheme morphism is **local on the source**: it suffices to exhibit, for each point `x ∈ X`, an affine open `V ∋ x` of `X` and an affine open `U ⊇ f(V)` of `Y` such that the induced ring map `Γ(Y,U) → Γ(X,V)` is `Algebra.IsStandardSmoothOfRelativeDimension n`. See `AlgebraicGeometry/Morphisms/Smooth.lean:135` (`SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension`).

For ℙ¹ over `Spec k̄` the 2-chart cover by `D₊(X₀)` and `D₊(X₁)` is the standard choice; both charts are isomorphic to `Spec k̄[T]` (the affine line). The base `Spec k̄` is itself affine. So we reduce to:

**(★)** `MvPolynomial Unit k̄` is standard smooth of relative dimension 1 over `k̄`.

`(★)` is constructed by hand:

```
def affLineSubmersivePresentation (k : Type*) [CommRing k] :
    Algebra.SubmersivePresentation k (MvPolynomial Unit k) Empty Unit where
  -- 1 generator `T = X ()`, 0 relations
  toPreSubmersivePresentation :=
    { toPresentation := Algebra.Presentation.naive (v := Empty.elim) ...,
      map := Empty.elim,
      map_inj := fun a => a.elim }
  jacobian_isUnit := by
    -- empty jacobian matrix has det = 1
    simp [PreSubmersivePresentation.jacobian, ...]
```

Dimension = `Fintype.card Unit - Fintype.card Empty = 1 - 0 = 1`.

## Concrete formalization plan (~150-250 LOC across iter-183+)

1. **Helper 1 (~40 LOC)** — `affLineSubmersivePresentation` above. Lives somewhere central (perhaps `AlgebraicJacobian/Genus0BaseObjects/AffineLineSmooth.lean` or directly inline in `BareScheme.lean`).
2. **Helper 2 (~10 LOC)** — `Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial Unit k)` instance from Helper 1 via `SubmersivePresentation.isStandardSmoothOfRelativeDimension` (`RingTheory/Extension/Presentation/Submersive.lean:93`).
3. **Helper 3 (~20 LOC)** — transfer along the chart-iso `homogeneousLocalizationAwayIso` (from `Genus0BaseObjects/ChartIso.lean`): use `Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv` to get
   ```
   Algebra.IsStandardSmoothOfRelativeDimension 1 k̄
     (HomogeneousLocalization.Away (projectiveLineBarGrading k̄) (MvPolynomial.X i))
   ```
   for each `i : Fin 2`.
4. **Helper 4 (~40 LOC)** — the affine chart `D₊(X i)` of `ProjectiveLineBarScheme k̄` has structure sheaf isomorphic (as `k̄`-algebra) to the above `HomogeneousLocalization.Away`. Use `Proj.affineOpenCoverOfIrrelevantLESpan` (already wired up in `projectiveLineBarAffineCover`) plus the local-iso lemmas it produces.
5. **Final (~40-80 LOC)** — the instance body. Given `x : ProjectiveLineBarScheme k̄`, the cover `projectiveLineBarAffineCover k̄` gives an `i : Fin 2` with `x ∈ D₊(X i)`. Provide `(U, V, hVU, ...)` with `U = ⊤` (all of `Spec k̄`) and `V = D₊(X i)`. The ring map `Γ(Spec k̄, ⊤) ≅ k̄ → Γ(ℙ¹, D₊(X i)) ≅ HomogeneousLocalization.Away _ (X i)` is `IsStandardSmoothOfRelativeDimension 1` by Helper 3.

## Risk

- The chart-iso `homogeneousLocalizationAwayIso` is a `RingEquiv`, not an `AlgEquiv` — need to upgrade via `homogeneousLocalizationAwayIso_algebraMap` (already proved in `ChartIso.lean:347`).
- `Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv` exists (`Smooth/StandardSmooth.lean`) but takes an `AlgEquiv`, so the upgrade above is essential.
- Section-iso threading through `Spec.map` ↔ `Spec.preimage` of the affine open in `Proj` is the messy bit.

## Why not closed iter-182

PROGRESS.md off-limits flag; substantial Mathlib infrastructure addition; budgeted iter-183+ alongside the smoothness pivot. No prior task_result for this file (i.e. no prover has been assigned to it before).
