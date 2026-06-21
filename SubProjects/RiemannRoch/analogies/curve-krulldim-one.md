# Analogy: cleanest route to `Order.krullDim (α := C.left) ≤ 1` for a smooth proper geometrically-irreducible curve over `k̄`

## Mode
api-alignment (route-assemblability flavor)

## Slug
krulldim-route

## Iteration
012

## Question
For `C : Over (Spec (.of kbar))` with `[Field kbar] [IsAlgClosed kbar] [IsProper C.hom]
[SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] [IsIntegral C.left]`,
prove `Order.krullDim (α := C.left) ≤ 1`. SOLE remaining ingredient for the `hfin` /
`IsRegularInCodimensionOne` witness at `OcOfD.lean:635` (consumed by the new pin lemma
`finrank_cotangentSpace_stalk_eq_one_of_smooth (hdim : krullDim C.left ≤ 1)` via
`isClosed_singleton_of_coheight_eq_one`, codim-1 ⇒ closed — valid only once dim ≤ 1).

## Project artifact(s)
- `AlgebraicJacobian/RiemannRoch/OcOfD.lean:592-639` — `sheafOf`; the `IsRegularInCodimensionOne` witness, `hfin` sorry at 635.
- `AlgebraicJacobian/Albanese/CoheightBridge.lean:149-216` — `Scheme.ringKrullDim_stalk_eq_coheight` (the per-point bridge).

## Decisions identified

### Decision: outer reduction — scheme krullDim ⟶ per-stalk ringKrullDim (deliverable 4)
- **Mathlib/project idiom**: `Order.krullDim_eq_iSup_coheight` (`Mathlib.Order.KrullDimension`)
  + project `AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_coheight` (CoheightBridge.lean:149).
  Composed they give `krullDim X = ⨆ z, ringKrullDim (stalk z)` — this IS the
  "krullDim scheme = sup of local dims" statement; no separate affine-cover dimension lemma
  is needed (and none ships).
- **Gap**: identical / already in project.
- **Verdict**: PROCEED. Goal ⟺ `∀ z : C.left, ringKrullDim (stalk z) ≤ 1`.

### Decision: localization push — stalk dim ⟶ chart-ring dim (deliverable 3)
- **Mathlib idiom**: `IsLocalization.AtPrime.ringKrullDim_eq_height` (`Mathlib.RingTheory.Ideal.Height`)
  gives `ringKrullDim (stalk z) = p_z.height`; then `Ideal.primeHeight_le_ringKrullDim`
  (same file) gives `p_z.height ≤ ringKrullDim S_z`. (`Ideal.height_le_ringKrullDim_of_ne_top` is
  an equivalent handle.) Chart `S_z` and the `IsLocalization.AtPrime` instance come from the
  project's `isLocalization_stalk_standardSmooth_chart_of_smooth C z` (directive-verified).
- **Gap**: identical — clean, no new lemma. The asked-for "IsLocalization ⇒ ringKrullDim ≤"
  is NOT needed as a standalone; `primeHeight_le_ringKrullDim` does the job (height of the
  contracted prime, not a generic localization bound).
- **Verdict**: PROCEED. Reduces to `ringKrullDim S_z ≤ 1` for the standard-smooth chart.

### Decision: the crux — `ringKrullDim S ≤ 1` for a standard-smooth rel-dim-1 f.g. DOMAIN over `k̄` (deliverable 2)
- **Mathlib idiom**: NONE complete. Available pieces:
  - Noether normalization (module-finite form): `exists_finite_inj_algHom_of_fg k̄ S`
    (`Mathlib.RingTheory.NoetherNormalization`) ⇒ `g : MvPolynomial (Fin s) k̄ →ₐ[k̄] S`,
    injective, `Module.Finite`. (`exists_integral_inj_algHom_of_fg` is the integral variant.)
  - `MvPolynomial.ringKrullDim_of_isNoetherianRing` ⇒ `ringKrullDim k̄[Fin s] = s` (k̄ a field, dim 0).
  - Going-up primes: `Mathlib.RingTheory.Ideal.GoingUp`
    (`Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`, incomparability lemmas).
  - `Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth` ⇒ `Module.rank S Ω[S/k̄] = 1`.
- **Two genuine GAPS** block assembling `ringKrullDim S = s ≤ 1`:
  - **G1 (heaviest, most reusable)**: `ringKrullDim` invariant under a **module-finite / integral
    injective** ring extension (Cohen–Seidenberg dimension equality). ABSENT — Mathlib has the
    going-up *prime-correspondence* (`Ideal.GoingUp`) but NOT the packaged `ringKrullDim` (in)equality.
    Loogle `ringKrullDim _ = ringKrullDim _` returns only `RingEquiv` / quotient / surjective forms;
    `ringKrullDim, Module.Finite` and `ringKrullDim, Algebra.IsIntegral` return nothing usable.
  - **G2**: identifying the Noether count `s` with the relative dimension `= 1`. ABSENT. The natural
    bridge `s = Algebra.trdeg k̄ S` and `trdeg = Module.rank Ω` (perfect-base separable-generation)
    does not ship: loogle `Algebra.trdeg, Module.rank, KaehlerDifferential` is empty; only field-
    extension sep-degree facts (`Algebra.IsSeparable.sepDegree_eq`) exist, not the differential link.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision: smooth-morphism dimension shortcut (deliverable 1)
- **Mathlib idiom**: NONE. `AlgebraicGeometry.IsSmoothOfRelativeDimension` /
  `Algebra.IsStandardSmoothOfRelativeDimension` carry only the cotangent/rank API
  (`iff_of_isStandardSmooth` → `rank Ω = n`); there is NO theorem
  `IsSmoothOfRelativeDimension n f ⇒ dim X ≤ dim Y + n` nor `dim (smooth fiber) = n`.
  Loogle `IsSmoothOfRelativeDimension, ringKrullDim` → no results.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (the cleanest single shortcut if it existed; it does not).

## Recommendation

`krullDim C.left ≤ 1` is a **multi-piece dimension-theory build**, NOT a one-lemma wire-up. The
OUTER reduction is free (existing project + Mathlib): `krullDim X = ⨆ z, ringKrullDim (stalk z)`
via `krullDim_eq_iSup_coheight` + `ringKrullDim_stalk_eq_coheight`, then per stalk
`ringKrullDim (stalk z) = p_z.height ≤ ringKrullDim S_z` via
`IsLocalization.AtPrime.ringKrullDim_eq_height` + `primeHeight_le_ringKrullDim` on the
standard-smooth chart `S_z`. The ONLY hard obligation is `ringKrullDim S ≤ 1` for a
standard-smooth rel-dim-1 f.g. **domain** over `k̄`.

Cheapest assembly = **dim = trdeg via Noether normalization**: `exists_finite_inj_algHom_of_fg`
(S module-finite over `k̄[Fin s]`) + `MvPolynomial.ringKrullDim_of_isNoetherianRing` (`= s`) +
**G1** (dim invariant under module-finite injective ext, build from `Ideal.GoingUp`) ⇒
`ringKrullDim S = s`; then **G2** (`s ≤ 1` from rel-dim-1) closes it. G1 is the reusable
keystone lemma to scaffold first (`ringKrullDim_eq_of_finite_injective` /
`…_of_isIntegral_injective`); G2 needs `s = trdeg` (Noether basis is a transcendence basis) and
`trdeg ≤ 1` (no Ω-rank=trdeg in Mathlib — likely prove `s ≤ 1` by exhibiting two independent
transcendentals would contradict `rank Ω = 1`, or via the local-ring dim at the generic point).
Do NOT chase the Krull-height-theorem direction (`ringKrullDim_quotient_le`,
`height_le_…_spanFinrank`): cutting `n-1` equations gives a LOWER bound `dim ≥ 1`, never the
needed UPPER bound. Do NOT chase a smooth-morphism dimension formula or étale-local-structure
shortcut — both are larger absent theorems than G1+G2.
