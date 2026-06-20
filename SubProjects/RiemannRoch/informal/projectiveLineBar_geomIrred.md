# `projectiveLineBar_geomIrred`: `ℙ¹_{k̄}` is geometrically irreducible

**File:** `AlgebraicJacobian/Genus0BaseObjects/BareScheme.lean` (L154-156)
**Status:** scaffold `sorry` since iter-165; Mathlib gap. File flagged "off-limits this iteration" in `PROGRESS.md` iter-182.
**Confirmed-missing Mathlib pieces (search exhaustive iter-182):**
- No `GeometricallyIrreducible` instance for `Proj` of any graded ring.
- The class is defined (`AlgebraicGeometry/Geometrically/Irreducible.lean:42`) via `geometrically (IrreducibleSpace ·) f`, i.e. for every field extension `Spec K → Spec k̄`, the pullback `Proj k̄[X,Y] ×_{Spec k̄} Spec K` is `IrreducibleSpace`. Mathlib has no general lemma reducing this to a ring-theoretic statement on the graded ring.

## Claim

```
instance projectiveLineBar_geomIrred (kbar : Type u) [Field kbar] :
    GeometricallyIrreducible (ProjectiveLineBar kbar).hom
```

i.e. for every field `K` and every map `Spec K → Spec k̄`, `Proj k̄[X₀,X₁] ×_{Spec k̄} Spec K` is irreducible as a topological space.

## Mathematical proof sketch

`Proj k̄[X₀,X₁] ×_{Spec k̄} Spec K ≅ Proj K[X₀,X₁]` because tensoring the standard ℕ-grading by `K` over `k̄` preserves the grading. Then `Proj K[X₀,X₁] = ℙ¹_K`, which is irreducible: it has the two affine charts `Spec K[T]` (the affine line, which is irreducible since `K[T]` is a domain — `IsDomain ⟹ IrreducibleSpace (Spec _)` is `AlgebraicGeometry.Properties.lean`'s `instIrreducibleSpaceSpecOfIsDomain`), they cover, and their intersection `Spec K[T,T⁻¹]` is nonempty.

Two-chart irreducibility: a topological space is irreducible iff it is nonempty and any two nonempty opens meet. Cover by two open subsets `U₀, U₁` each irreducible with nonempty `U₀ ∩ U₁` ⟹ space irreducible. (Both charts contain the generic point of their respective `K[T]`, and these generic points map to the same generic point of `Proj K[X₀,X₁]`.)

## Concrete formalization plan (~200-350 LOC across iter-183+)

This is **harder** than the smoothness sketch because we must handle the **base change** `Proj k̄[X₀,X₁] ×_{Spec k̄} Spec K`:

1. **Helper A (~50 LOC)** — `Proj` of a base-changed graded ring is the base-change of `Proj`:
   ```
   Proj (𝒜 ⊗ K) ≅ Proj 𝒜 ×_{Spec k̄} Spec K
   ```
   where `𝒜 ⊗ K` is the natural ℕ-grading on `K[X₀,X₁] = K ⊗_{k̄} k̄[X₀,X₁]`. Mathlib has `AlgebraicGeometry.Proj.pullback` family of results but the precise statement here is bespoke for the standard polynomial grading.
2. **Helper B (~80 LOC)** — given a field `K`, build `Proj K[X₀,X₁] = ℙ¹_K` directly as
   `Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K)`. Show its 2-chart cover by `D₊(X₀), D₊(X₁)` plus the chart-iso to `Spec K[T]` (mirroring `ChartIso.lean` over `K` instead of `k̄`). All-in-all a re-instantiation of `BareScheme.lean + ChartIso.lean` over an arbitrary field, NOT just `k̄`.
3. **Helper C (~30 LOC)** — irreducibility of the affine line `Spec K[T]` over a field `K`: `K[T]` is a domain (`Polynomial.instIsDomain`), so `IrreducibleSpace (Spec K[T])` via `instIrreducibleSpaceSpecOfIsDomain`. After the chart-iso of Helper B, this gives `IrreducibleSpace (D₊(X i))` for each chart.
4. **Helper D (~40 LOC)** — two-chart cover lemma: if `X = U₀ ∪ U₁` with both `IrreducibleSpace`s and `U₀ ∩ U₁ ≠ ∅`, then `IrreducibleSpace X`. Search Mathlib for `IrreducibleSpace.of_isCompact_isIrreducible` / `IrreducibleSpace.of_isOpen_cover` — may exist.
5. **Helper E (~20 LOC)** — nonemptiness of `D₊(X₀) ∩ D₊(X₁) = D₊(X₀ * X₁)` over `K`: `K[X₀,X₁]` is a domain, `X₀ * X₁ ≠ 0` is a homogeneous element of positive degree, so `D₊(X₀ * X₁)` is nonempty.
6. **Final (~50-100 LOC)** — `GeometricallyIrreducible.iff_geometricallyIrreducible_fiber` plus universal-open-ness of `ℙ¹ / Spec k̄` to reduce to fibers. For each `s : Spec k̄` (here = unique point, since `k̄` is a field), the fiber over `s` is `Proj k̄[X₀,X₁] ×_{Spec k̄} Spec κ(s) = Proj k̄[X₀,X₁]`, and we use `GeometricallyIrreducible.geometrically_irreducibleSpace` which unfolds to "for every field `K → κ(s) = k̄`, the further pullback is irreducible" — Helper A reduces this to `IrreducibleSpace (Proj K[X₀,X₁])`, settled by Helpers B-E.

## Risk

- Helper A is the load-bearing piece and is genuinely hard: `Proj` distributing over base change is a substantive scheme-theoretic fact.
- Helper B duplicates infrastructure: avoid by parameterising `BareScheme.lean` constructions over a general field `K` instead of `k̄` (this is a refactor that touches `ChartIso.lean` too).

## Why not closed iter-182

PROGRESS.md off-limits flag; substantial Mathlib infrastructure (~200-350 LOC) gated on a more general `Proj k̄[Xᵢ] ×_S Spec K ≅ Proj K[Xᵢ]` lemma; budgeted iter-183+. No prior task_result for this file (no prover assigned previously).

## Alternative route

If `Algebra.IsGeometricallyReduced` is the *integrality* test sufficient downstream — but `GeometricallyIrreducible` is the one threaded through the AVR pipeline (called from `AbelianVarietyRigidity.lean`'s `iotaGm_isDominant` chain), so a weaker `IsIntegral` substitute is **not** acceptable.
