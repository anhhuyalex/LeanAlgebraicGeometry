# Analogy: Mathlib infrastructure support for the two genus-0 completion routes

## Mode
api-alignment (api-availability survey)

## Slug
route-support

## Iteration
163

## Question
For Route R (rigidity / rational-map extension, Milne §I.3) and Route H (differential /
cotangent + Frobenius hybrid), which is LESS blocked by missing Mathlib infrastructure?
Per-piece: EXISTS (decl + module) | PARTIAL | [gap].

## Method
Direct grep over `/.lake/packages/mathlib/Mathlib` (source present locally). Not rate-limited;
verified decl names by reading the actual files. No mathematical-correctness judgement —
API availability only.

---

## Route R — rigidity / rational-map extension

### R1. Valuative criterion of properness — **EXISTS (keystone present)**
- `AlgebraicGeometry/ValuativeCriterion.lean`:
  - `structure ValuativeCommSq`, `def ValuativeCriterion` (`.Existence` / `.Uniqueness`), L53–88.
  - `ValuativeCriterion.existence` / `.uniqueness` (L103, L106).
  - `IsProper.eq_valuativeCriterion` (L328), `IsProper.of_valuativeCriterion` (L339,
    `[QuasiCompact] [QuasiSeparated] [LocallyOfFiniteType]`).
  - `IsSeparated.valuativeCriterion` (L273), `UniversallyClosed.*_valuativeCriterion`.
- The DVR you lift along: `RationalMap`/`PartialMap` machinery is fully built —
  `AlgebraicGeometry/RationalMap.lean` (`Scheme.PartialMap`, `Scheme.RationalMap`/`X ⤏ Y`,
  `RationalMap.domain` L485, `dense_domain` L496, `equivFunctionFieldOver` L473,
  `ofFunctionField`, `toPartialMap` for separated targets L517).
- **PARTIAL**: the *application* "rational map from a normal variety extends over a
  codim-1 point" is NOT a lemma. `RationalMap.lean` has no `valuativ`/`extend`/`normal`/`codim`
  mention. You must wire valuative criterion + (local ring at codim-1 = DVR) by hand.

### R1-bridge. Local ring at a codim-1 point of a normal variety is a DVR — **PARTIAL (ring side EXISTS)**
- `RingTheory/DiscreteValuationRing/TFAE.lean`:
  `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` (L168) — Noetherian + local + domain +
  integrally-closed + dim 1 ⟺ DVR (no `¬IsField` needed). This is exactly the surface codim-1
  local ring.
- `RingTheory/DedekindDomain/Dvr.lean`:
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` (L131),
  `Ring.DimensionLEOne.localization` (L68).
- **[gap]**: scheme-side plumbing "X normal ⟹ `𝒪_{X,x}` integrally closed" + "codim-1 ⟹
  `dim = 1`" is not assembled; must connect `IsIntegrallyClosed` of the stalk to the scheme's
  normality and Krull height (`RingTheory/KrullDimension/*` exists at ring level).

### R2. Weil divisors / codim-1 / pure-codim-1 indeterminacy locus on a surface — **[gap]**
- No algebraic Weil/Cartier divisor theory in `AlgebraicGeometry`. The only `Divisor.lean`
  is `Analysis/Meromorphic/Divisor.lean` (complex-analytic, irrelevant).
- No `div(f)`, no prime divisors, no "indeterminacy locus is pure codim 1".
- Krull height/codimension exists at ring level (`RingTheory/KrullDimension/`,
  `Ideal.height`) but is NOT assembled into scheme divisor theory.
- NOTE: Route R may AVOID this entirely — pointwise valuative-criterion extension at each
  codim-1 point (via R1-bridge) does not require global divisor theory. Whether R2 is on the
  critical path depends on the chosen proof; it is the most avoidable of R's gaps.

### R3. 𝔾_a, 𝔾_m group schemes + Hom(𝔾_a, A) = 0 — **PARTIAL (underlying schemes EXIST, group/triviality absent)**
- `AlgebraicGeometry/AffineSpace.lean`: `AffineSpace n S` = `𝔸(n;S)` (L46), full functorial
  API (`homOfVector`, `coord`, `map`, `SpecIso`). Gives the underlying scheme of 𝔾_a.
- Group-object machinery EXISTS: `GrpObj`/`Over … GrpObj` is used in
  `AlgebraicGeometry/Group/Abelian.lean` (e.g. instance at L35, `η[G]`).
- **[gap]**: no group-scheme structure put on 𝔸¹ (𝔾_a), no 𝔾_m at all, and no theorem
  `Hom(𝔾_a, A) = 0`. `AlgebraicGeometry/Group/` contains only `Abelian.lean`, `Smooth.lean`.

---

## Route H — differential / cotangent + Frobenius hybrid

### H1. Sheaf of (Kähler) differentials Ω of a scheme/morphism (quasi-coherent), pullback, Ω_A ≅ O^g — **[gap] at scheme level (ring level RICH)**
- Ring level EXISTS and is extensive: `RingTheory/Kaehler/Basic.lean` (`Ω[S⁄R]` =
  `KaehlerDifferential`, `KaehlerDifferential.D` derivation L197, `linearMapEquivDerivation`,
  `endEquiv`, `ideal_fg`), `RingTheory/Kaehler/Polynomial.lean`
  (`KaehlerDifferential.mvPolynomialEquiv` L31 — polynomial differentials are FREE, the
  Ω_A ≅ O^g ingredient), `JacobiZariski.lean`, `TensorProduct.lean`,
  `Algebra/Module/Presentation/Differentials.lean`.
- **[gap]**: NO `Ω` as a quasi-coherent sheaf on a scheme; no cotangent sheaf; no pullback of
  differentials along a scheme morphism. Only consumer of ring-level Ω in AG is
  `AlgebraicGeometry/Morphisms/FormallyUnramified.lean` (uses `Ω[S⁄R]` abstractly, not as a
  sheaf). `AlgebraicGeometry/Modules/{Presheaf,Sheaf,Tilde}` provides the `M~` sheafification
  to BUILD the sheaf from ring-level Ω, but it is not built.

### H2. H⁰(ℙ¹, O(n)) line-bundle cohomology (Serre's computation) — **[gap], most severe**
- Mathlib has NO coherent/quasi-coherent sheaf cohomology whatsoever. `AlgebraicGeometry/`
  has no `H^i`, no higher direct images, no `RΓ`.
- No `ℙⁿ` as a named scheme; no Serre twisting sheaf O(n); no Picard group of a scheme;
  no `Modules/` cohomology (`Modules/` = `Presheaf`, `Sheaf`, `Tilde` only).
- Only abstract/other cohomology exists: `CategoryTheory/Sites/SheafCohomology/{Basic,Cech,
  MayerVietoris}.lean` and `AlgebraicGeometry/Sites/ElladicCohomology.lean` — neither yields
  H⁰(ℙ¹, O(n)).
- Proj IS present and proper: `AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`
  (`IsProper (Proj.toSpecZero 𝒜)` L366) — so ℙ¹ as a scheme is constructible, but its
  cohomology is a foundational from-scratch build with zero starting point.

### H3. Relative Frobenius of a scheme over char p + "zero differential ⟹ factors through Frobenius" — **[gap]**
- No scheme Frobenius (relative or absolute): `grep frobenius AlgebraicGeometry/` = empty.
- Ring/field level EXISTS: `Algebra/CharP/Frobenius.lean` (`frobenius`, `iterateFrobenius`),
  `RingTheory/Frobenius.lean` (arithmetic Frobenius), `FieldTheory/PerfectClosure.lean`
  (`PerfectClosure`, `pthRoot`-style `mk`).
- **[gap]**: no scheme-morphism Frobenius and no factorization theorem. Entirely from scratch.

---

## Verdicts (per piece)

| Route | Piece | Status |
|---|---|---|
| R | R1 valuative criterion of properness | EXISTS (keystone) |
| R | R1-bridge codim-1 stalk = DVR | PARTIAL (ring side exists) |
| R | R2 Weil divisor / indeterminacy locus | [gap] (likely avoidable) |
| R | R3 𝔾_a/𝔾_m + Hom(𝔾_a,A)=0 | PARTIAL→[gap] |
| H | H1 sheaf of differentials Ω | [gap] scheme-level (ring rich) |
| H | H2 H⁰(ℙ¹,O(n)) line-bundle cohomology | [gap], SEVERE (no SCT cohomology at all) |
| H | H3 relative Frobenius of schemes | [gap], from scratch |

## Recommendation
**Route R is materially LESS blocked.** Its load-bearing keystone — the valuative criterion of
properness — is fully present, battle-tested, and exactly typed for a proper target
(`IsProper.of_valuativeCriterion` with `[QuasiCompact][QuasiSeparated][LocallyOfFiniteType]`),
and the `RationalMap`/`PartialMap` layer plus the DVR-at-height-1 ring bridge are both in
Mathlib. R's gaps (Weil divisors R2; 𝔾_a-triviality R3) are real but R2 is plausibly
side-steppable by pointwise valuative extension, and R3 is one targeted homomorphism-triviality
lemma over an EXISTING group-object + affine-space API. Route H is blocked on THREE independent
from-scratch foundational builds — scheme-level differentials (H1), a complete coherent-sheaf
cohomology theory + O(n) + Serre's H⁰ computation (H2, the single largest gap surfaced anywhere
in this survey: Mathlib has literally no quasi-coherent sheaf cohomology), and scheme Frobenius
+ its factorization theorem (H3). H1's ring-level Ω is rich, but the sheaf, the cohomology, and
the Frobenius are all absent. Prefer Route R.
