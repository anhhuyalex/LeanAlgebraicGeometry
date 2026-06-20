# Analogy: kernel of the universal Kähler derivation = field of constants (FT.3)

## Mode
cross-domain-inspiration

## Slug
ftthree-kernel

## Iteration
154

## Structural problem (abstracted)

For a separably-generated (here char-0) field extension `K / k`, the kernel of
the universal derivation `d : K → Ω_{K/k}` is the relative algebraic closure of
`k` in `K`. Concretely: `d x = 0 ⟹ x algebraic over k`. Combined with the
standing "`k` algebraically closed in `K`" (from `[IsAlgClosed k] + [IsDomain B]`,
`K = Frac B`), this gives `x ∈ k`. The content lives in the *transcendental*
layer (`Ω_{K/k} ≠ 0`), so unramified/`Ω=0` arguments do not reach it.

The concrete Lean residual is the single `sorry` in
`AlgebraicJacobian/Cotangent/ChartAlgebra.lean:427`
(`KaehlerDifferential.mem_range_algebraMap_of_D_eq_zero`), stated on the
standard-smooth domain `B` (not yet on `K`): `D_B b = 0 ⟹ b ∈ range(algebraMap k B)`.

## Failed approaches (from directive)
- `Differential.ContainConstants` / `mem_range_of_deriv_eq_zero`: abstract single
  derivation `B → B`, only trivial `ContainConstants A A` instance ships.
- `FormallyUnramified.iff_isSeparable` + `Subsingleton Ω[L/K]`: only the algebraic
  (`EssFiniteType`, `Ω=0`) layer; misses the transcendental content.
- `Smooth.Field` (`FormallySmooth.of_algebraicIndependent_of_isSeparable`): gives
  formal smoothness but exposes no `Ω`-basis from a separating transcendence basis
  and no kernel description.
- `loogle "KaehlerDifferential.D _ _ ?x = 0"` → ∅: no shipped kernel-of-`D` lemma.

## HEADLINE FINDING (overturns iter-153 "genuine Mathlib gap" verdict)

FT.3 has **no single shipped kernel-of-`d` lemma**, but **every structural
ingredient to assemble it IS in Mathlib `b80f227`**, and a *cleaner route than
the directive's 4-step separating-transcendence-basis assembly* exists. I
verified the full chain by compilation via `lean_run_code` (each `example`
below type-checks against the project toolchain). FT.3 is **assemblable project
material (~100–150 LOC)**, NOT a Mathlib theory gap. The iter-153 bright-line
STOP should be lifted; re-dispatch a prover with the route below.

The decisive move is to **stop trying to describe `ker d` directly** and instead
realize the missing *injectivity of the cotangent base-change* via the
**Jacobi–Zariski / `H1Cotangent` exact sequence** + **formal smoothness of a
perfect-field (char-0) extension**. This is the "one shelf over" analogue: the
cotangent-complex API, not the derivation-kernel API.

## Analogues found

Ranked by porting cost (lowest first).

### Analogue: `Algebra.H1Cotangent.exact_δ_mapBaseChange` + `Algebra.FormallySmooth.of_perfectField`

- **Domain**: cotangent complex / deformation theory (Jacobi–Zariski), crossed
  with field-theoretic formal smoothness.
- **Same structural problem there**: for a tower `k → F → K`, the sequence
  `H¹(L_{K/F}) --δ--> K ⊗_F Ω_{F/k} --mapBaseChange--> Ω_{K/k}` is exact
  (`Algebra.H1Cotangent.exact_δ_mapBaseChange`,
  `Mathlib.RingTheory.Kaehler.JacobiZariski`/`CotangentComplex`). When `K/F` is
  formally smooth, `H¹(L_{K/F})` is `Subsingleton`
  (`instSubsingletonH1CotangentOfFormallySmooth`, `Mathlib.RingTheory.Smooth.Basic`),
  so `mapBaseChange k F K` is **injective**. This is exactly the directive's
  desired LEFT-exactness of `Ω_{F/k} ⊗ K → Ω_{K/k}`.
- **Why it applies without a transcendence basis**: take `F = k(b)`. In char 0,
  `F` is a **perfect field** (`PerfectField.ofCharZero`, `Mathlib.FieldTheory.Perfect`),
  and `K` is essentially of finite type over `F`
  (`Algebra.EssFiniteType.of_comp` from `EssFiniteType k K`,
  `Mathlib.RingTheory.EssentialFiniteType`). Then
  `Algebra.FormallySmooth.of_perfectField` (`Mathlib.RingTheory.Smooth.Field`)
  gives `FormallySmooth F K` directly — **no separating transcendence basis, no
  "all partials vanish" combinatorics, no freeness-of-Ω-on-a-basis step.**
- **Technique**: `mapBaseChange k F K (1 ⊗ D_F x) = D_K (algebraMap F K x)` via
  `KaehlerDifferential.mapBaseChange_tmul` + `map_D` (`one_smul`). So
  `D_K b = 0 ⟹ 1 ⊗ D_F b = 0 ⟹ D_F b = 0` by faithful flatness
  (`Module.FaithfullyFlat.one_tmul_eq_zero_iff`; the instance `FaithfullyFlat F K`
  for a field extension resolves by `inferInstance`). Contradiction with the base
  case below ⟹ `b` is algebraic over `k`.
- **Mapping to project**: in
  `KaehlerDifferential.mem_range_algebraMap_of_D_eq_zero`, first push `D_B b = 0`
  to `D_K b = 0` (`K = FractionRing B`) via `map_D` (the project already has this
  as `_hFunct`). Then run the contradiction with `F` realized as
  `FractionRing (Polynomial k)` embedded into `K` by `b` (see base case).
- **Porting cost**: **low–medium**. All lemmas verified to compose; the work is
  scalar-tower/instance plumbing.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `KaehlerDifferential.isLocalizedModule_map` + `polynomialEquiv_D` (transcendental base case)

- **Domain**: localization / essentially-étale base change of Kähler differentials.
- **Same structural problem there**: a localization `S → T` is formally étale
  (`Algebra.FormallyEtale.of_isLocalization`, `Mathlib.RingTheory.Etale.Basic`),
  so `Ω_{T/k}` is the localized module of `Ω_{S/k}`
  (`KaehlerDifferential.isLocalizedModule_map`, `Mathlib.RingTheory.Kaehler.Localization`).
- **Technique (FULLY verified, ~20 LOC)**: to show `D_{k(t)} t ≠ 0` for `t`
  transcendental, take `S = k[X]`, `T = FractionRing k[X]`. From `D_T(t)=0`,
  `map k k S T (D_S X) = 0`, so by `IsLocalizedModule.eq_zero_iff` there is
  `c ∈ nonZeroDivisors` with `c • D_S X = 0`. Apply the `k[X]`-linear iso
  `KaehlerDifferential.polynomialEquiv` (`polynomialEquiv_D : polynomialEquiv (D X) = derivative X = 1`):
  `c • 1 = 0` in `k[X]`, contradicting `nonZeroDivisors.coe_ne_zero`. No
  `NoZeroSMulDivisors` lemma even needed.
- **Mapping to project**: this is the only genuinely-new helper. Stated as
  `D_{FractionRing (Polynomial k)} (algebraMap _ _ X) ≠ 0`. To use it inside the
  main proof, embed `F := FractionRing (Polynomial k) (≅ RatFunc k)` into `K` via
  `IsFractionRing.lift` of the injective `k[X] → K`, `X ↦ b` (injective because
  `b` transcendental). Avoids `IntermediateField.adjoin` entirely.
- **Porting cost**: **low** (base case verified end-to-end).
- **Verdict**: ANALOGUE_FOUND.

### Analogue (discarded): separating-transcendence-basis freeness of `Ω`

- Mathlib has `Algebra.SubmersivePresentation.rank_kaehlerDifferential` and
  `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
  (`= n`), and `Algebra.trdeg`, but **no `IsTranscendenceBasis`-keyed
  freeness-of-`Ω` lemma** and **no general `rank Ω_{K/k} = trdeg`**. The
  directive's steps 1–2 (choose separating transcendence basis, `Ω` free on it)
  would have to be built. The `H1Cotangent` route makes this unnecessary —
  **discard**.

## Top suggestion

Build FT.3 by the **single-element / perfect-field route**, not the 4-step
transcendence-basis route. Concretely, in
`AlgebraicJacobian/Cotangent/ChartAlgebra.lean`, replace the `sorry` at L427 with:

1. A new private helper `_ratfunc_D_X_ne_zero` (≈20 LOC, **verified**):
   `D_{FractionRing (Polynomial k)} (algebraMap _ _ X) ≠ 0`, via
   `isLocalizedModule_map` + `IsLocalizedModule.eq_zero_iff` + `polynomialEquiv_D`.
2. The main reduction `D_B b = 0 ⟹ IsAlgebraic k b` (≈60–90 LOC): push to
   `K = FractionRing B`; `by_contra` ⟹ `Transcendental k b` ⟹ `k[X] → K` (`X↦b`)
   injective ⟹ `IsFractionRing.lift` gives a field embedding `F := RatFunc k → K`;
   register `Algebra F K` + `IsScalarTower k F K`; `FormallySmooth F K`
   (`of_perfectField`, using `PerfectField.ofCharZero` + `EssFiniteType.of_comp`);
   `mapBaseChange k F K` injective (via `exact_δ_mapBaseChange` + `Subsingleton H1`);
   `D_K b = mapBaseChange (1 ⊗ D_F X_F)` ⟹ `1 ⊗ D_F X_F = 0` ⟹ (`FaithfullyFlat F K`,
   `one_tmul_eq_zero_iff`) `D_F X_F = 0`, contradicting step 1.
3. Close with `b` algebraic ⟹ `b ∈ range(algebraMap k B)` (≈10 LOC, **verified**):
   `adjoin.finiteDimensional` + `IsAlgClosed.algebraMap_bijective_of_isIntegral`
   (the project already uses the latter in `constants_integral_over_base_field`).

First file to touch: `AlgebraicJacobian/Cotangent/ChartAlgebra.lean` (the `_mvPoly_*`
free-case helpers become dead and may be removed — they targeted the abandoned
transcendence-basis/joint-pderiv route). The `[IsAlgClosed k] [CharZero k]
[IsDomain B] [FiniteType k B] [IsStandardSmoothOfRelativeDimension n k B]`
signature is sufficient and unchanged; `n` and standard-smoothness are not even
needed for the kernel argument (only `IsDomain B` + `FiniteType` to build `K` and
`EssFiniteType k K`), though they remain harmless.

## Verified-compiling skeleton (each block type-checks against the project toolchain)

```lean
-- char-0 field perfect; field extension faithfully flat
example {k}   [Field k] [CharZero k] : PerfectField k := inferInstance
example {F K} [Field F] [Field K] [Algebra F K] : Module.FaithfullyFlat F K := inferInstance
-- perfect base + EssFiniteType ⟹ formally smooth
example {F K} [Field F] [Field K] [Algebra F K] [CharZero F] [Algebra.EssFiniteType F K] :
    Algebra.FormallySmooth F K := Algebra.FormallySmooth.of_perfectField
-- Subsingleton H1 ⟹ mapBaseChange injective
example {k F K} [CommRing k] [CommRing F] [CommRing K] [Algebra k F] [Algebra k K] [Algebra F K]
    [IsScalarTower k F K] [Algebra.FormallySmooth F K] :
    Function.Injective (KaehlerDifferential.mapBaseChange k F K) := by
  rw [injective_iff_map_eq_zero]; intro x hx
  obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k F K x).mp hx
  rw [Subsingleton.elim y 0, map_zero]
-- EssFiniteType chain for K = Frac B
example {k B} [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] :
    Algebra.EssFiniteType k (FractionRing B) :=
  Algebra.EssFiniteType.comp k B (FractionRing B)
-- mapBaseChange/D identity
example {k F K} [CommRing k] [CommRing F] [CommRing K] [Algebra k F] [Algebra k K] [Algebra F K]
    [IsScalarTower k F K] (x : F) :
    KaehlerDifferential.mapBaseChange k F K (1 ⊗ₜ KaehlerDifferential.D k F x)
      = KaehlerDifferential.D k K (algebraMap F K x) := by
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
-- transcendental base case (FULLY verified)
example {k} [Field k] :
    KaehlerDifferential.D k (FractionRing (Polynomial k))
      (algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X) ≠ 0 := by
  intro h
  have hmap : KaehlerDifferential.map k k (Polynomial k) (FractionRing (Polynomial k))
      (KaehlerDifferential.D k (Polynomial k) Polynomial.X) = 0 := by
    rw [KaehlerDifferential.map_D]; exact h
  haveI : IsLocalizedModule (nonZeroDivisors (Polynomial k))
      (KaehlerDifferential.map k k (Polynomial k) (FractionRing (Polynomial k))) :=
    KaehlerDifferential.isLocalizedModule_map _
  rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors (Polynomial k))] at hmap
  obtain ⟨c, hc⟩ := hmap
  rw [Submonoid.smul_def] at hc
  have hc1 := congrArg (KaehlerDifferential.polynomialEquiv (R := k)) hc
  rw [map_smul, KaehlerDifferential.polynomialEquiv_D, Polynomial.derivative_X,
    map_zero, smul_eq_mul, mul_one] at hc1
  exact nonZeroDivisors.coe_ne_zero c hc1
-- algebraic ⟹ in range (over alg-closed k)
example {k K} [Field k] [Field K] [IsAlgClosed k] [Algebra k K] {b : K} (hb : IsAlgebraic k b) :
    b ∈ (algebraMap k K).range := by
  haveI : FiniteDimensional k k⟮b⟯ := IntermediateField.adjoin.finiteDimensional hb.isIntegral
  haveI : Algebra.IsIntegral k k⟮b⟯ := Algebra.IsIntegral.of_finite k k⟮b⟯
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := k⟮b⟯)).surjective
    (IntermediateField.AdjoinSimple.gen k b)
  exact ⟨c, by have := congrArg (algebraMap k⟮b⟯ K) hc;
    rwa [← IsScalarTower.algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen] at this⟩
```

## Mathlib citations (module path; all [verified by compilation, b80f227])

| Lemma | Module |
|---|---|
| `PerfectField.ofCharZero` | `Mathlib.FieldTheory.Perfect` |
| `Algebra.FormallySmooth.of_perfectField` | `Mathlib.RingTheory.Smooth.Field` |
| `instSubsingletonH1CotangentOfFormallySmooth`, `Algebra.formallySmooth_iff` | `Mathlib.RingTheory.Smooth.Basic` |
| `Algebra.H1Cotangent.exact_δ_mapBaseChange`, `Algebra.H1Cotangent.δ` | `Mathlib.RingTheory.Kaehler.CotangentComplex` (Jacobi–Zariski) |
| `KaehlerDifferential.mapBaseChange_tmul`, `KaehlerDifferential.map_D`, `exact_mapBaseChange_map` | `Mathlib.RingTheory.Kaehler.Basic` |
| `Module.FaithfullyFlat.one_tmul_eq_zero_iff` | `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` |
| `Algebra.EssFiniteType.of_comp`, `.comp` | `Mathlib.RingTheory.EssentialFiniteType` |
| `KaehlerDifferential.isLocalizedModule_map`, `tensorKaehlerEquivOfFormallyEtale(_symm_D_algebraMap)`, `isBaseChange_of_formallyEtale` | `Mathlib.RingTheory.Kaehler.Localization` |
| `Algebra.FormallyEtale.of_isLocalization` | `Mathlib.RingTheory.Etale.Basic` |
| `KaehlerDifferential.polynomialEquiv`, `polynomialEquiv_D` | `Mathlib.RingTheory.Kaehler.Polynomial` |
| `IsLocalizedModule.eq_zero_iff` | `Mathlib.Algebra.Module.LocalizedModule.Basic` |
| `IsAlgClosed.algebraMap_bijective_of_isIntegral` | `Mathlib.FieldTheory.IsAlgClosed.Basic` |
| `IsFractionRing.lift` | `Mathlib.RingTheory.Localization.FractionRing` |
