# Analogy: smooth-stalk `finrank κ(𝔪/𝔪²)=1` — Route R (regularity) vs Route C (conormal iso)

## Mode
api-alignment

## Slug
smooth-stalk-finrank-route-fork

## Iteration
006

## Question
For `R` Noetherian local k-algebra, integral domain, `EssFiniteType k R`,
`FormallySmooth k R`, residue field `κ = k` (k alg-closed, codim-1 pt k-rational),
`ringKrullDim R = 1`: prove `finrank κ (𝔪/𝔪²) = 1` (⟹ `IsDiscreteValuationRing R`).
Compare Route R (regularity, Stacks 00TT) vs Route C (conormal iso, Hartshorne II.8.7)
in the project's PINNED Mathlib (b80f227). All PRESENT/ABSENT below verified LOCALLY via
`lean_run_code`/source grep over `.lake-packages/mathlib`, NOT upstream loogle.

## Project artifact(s)
- `AlgebraicJacobian/RiemannRoch/SmoothRegular.lean` — Decl 1 `IsRegularLocalRing_of_smooth`
  (Route R, sorry on `spanFinrank 𝔪 ≤ ringKrullDim`); Decl 3 `isDiscreteValuationRing_of_smooth_dim_one`
  (the actual downstream need; currently routes through Decl 1).
- `AlgebraicJacobian/RiemannRoch/OcOfD.lean` — consumer; wiring lemma
  `isDiscreteValuationRing_stalk_of_finrank_cotangentSpace_eq_one` lands the DVR endpoint from `finrank=1`.

## KEY CORRECTION to prior memory
[[ocofd-sheafof-construction]] and [[smoothregular-isregularring-absent]] recorded the conormal iso
`𝔪/𝔪² ≅ Ω[R⁄k]⊗κ` as **ABSENT** ("no `CotangentSpace R ≅ Ω⊗κ`"). **This is WRONG.** Mathlib b80f227
ships `Algebra.FormallySmooth.kerCotangentToTensor_injective_iff`
(`Mathlib/RingTheory/Smooth/Basic.lean:280`) which delivers the hard (injective) half of the conormal
iso directly from `[FormallySmooth k R]` + `Subsingleton (H1Cotangent k κ)`. The cotangent-complex
vanishing obligation it raises is on **`H1Cotangent k κ`** (the EASY k→κ extension, subsingleton since
κ=k / κ separable over perfect k) — NOT on `H1Cotangent k R`, and is NOT as deep as flat-descent.

## Route table (step → Mathlib name → PRESENT/ABSENT, all checked locally)

### Route R (regularity / Stacks 00TT)
| Step | Mathlib / project name | Status |
|---|---|---|
| R0 regular ⟺ finrank cotangent = dim | `IsRegularLocalRing.iff_finrank_cotangentSpace` | PRESENT |
| R0' reduce regular to `spanFinrank 𝔪 ≤ dim` | `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`, `ringKrullDim_le_spanFinrank_maximalIdeal` | PRESENT |
| R1 `rank Ω[S⁄k] = dim S` for std-smooth chart (CI dim theory) | — | **ABSENT** |
| R2 Jacobian-criterion regularity over alg-closed k | — | **ABSENT** |
| R3 flat-descent of regularity + localization transport `S_q→(S_K)_m` | `IsRegularRing`, `IsRegularRing.isRegularLocalRing_localization` | **ABSENT** (identifier `IsRegularRing` unknown locally) |
| R-endpoint regular+dim1+domain ⟹ DVR | `IsLocalRing.finrank_CotangentSpace_eq_one_iff`, `IsDiscreteValuationRing.TFAE` | PRESENT |

Route R has **3 genuinely-absent deep gaps** (R1, R2, R3), each multi-hundred-LOC; R3 needs an
entire `IsRegularRing` API that does not exist in the snapshot.

### Route C (conormal / cotangent iso, Hartshorne II.8.7)
| Step | Mathlib name | Status |
|---|---|---|
| C-seq conormal right-exact `𝔪/𝔪² → κ⊗ₐΩ[R⁄k] → Ω[κ⁄k] → 0` | `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` | PRESENT |
| C-inj conormal map injective (the iso's hard half) | `Algebra.FormallySmooth.kerCotangentToTensor_injective_iff` | PRESENT (1-line, COMPILED) |
| C-sub `Subsingleton (H1Cotangent k κ)` | `Algebra.FormallySmooth.subsingleton_h1Cotangent` | PRESENT |
| C-fs `FormallySmooth k κ` (κ=k, or κ sep/perfect) | `Algebra.FormallySmooth.of_perfectField` (+ `IsAlgClosed ⟹ PerfectField` instance) | PRESENT |
| C-Ωκ `Ω[κ⁄k]=0` (κ=k) | `Subsingleton Ω[k⁄k]` (`inferInstance`) | PRESENT |
| C-surj conormal map surjective (from C-seq + C-Ωκ) | `exact_…` + `Subsingleton.elim` | PRESENT (~5-line, COMPILED) |
| C-ker source IS `𝔪/𝔪²` | `IsLocalRing.ker_residue` (`ker(residue R)=𝔪`) | PRESENT |
| C-rank `rank S Ω[S⁄k] = 1`, `Free S Ω[S⁄k]` on rel-dim-1 chart | `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`, `Algebra.IsStandardSmooth.free_kaehlerDifferential` | PRESENT |
| C-loc `Ω[R⁄k]` = localization of `Ω[S⁄k]` (rank/free transport) | `KaehlerDifferential.isLocalizedModule` | PRESENT |
| C-bc `finrank κ (κ⊗ᵣΩ[R⁄k]) = rank R Ω[R⁄k]` | `Module.finrank_baseChange` | PRESENT |
| C-endpoint finrank=1 ⟹ DVR | `IsLocalRing.finrank_CotangentSpace_eq_one_iff` | PRESENT |

Route C has **ZERO genuinely-absent lemmas** — it is a pure assembly of present Mathlib lemmas
(~50–80 LOC), modulo standard module bookkeeping (`κ⊗_R(𝔪/𝔪²) ≅ 𝔪/𝔪²` linking `CotangentSpace R`
to the conormal source; localization-of-free-module rank).

## Decisions identified

### Decision: which route delivers `finrank κ(𝔪/𝔪²)=1` with fewer new project lemmas
- **Mathlib idiom**: the Jacobian criterion for local algebras is expressed in Mathlib via the
  **conormal/cotangent complex** (`kerCotangentToTensor`, `H1Cotangent`, `Smooth/Local.lean`,
  `Smooth/Basic.lean`), NOT via a standalone `IsRegularRing` smooth→regular transport (which is absent).
  Cite: `Mathlib/RingTheory/Smooth/Basic.lean:280` (`kerCotangentToTensor_injective_iff`),
  `Mathlib/RingTheory/Kaehler/Basic.lean:836` (`exact_kerCotangentToTensor_mapBaseChange`),
  `Mathlib/RingTheory/Smooth/Local.lean:34,49` (residue-field Jacobian criterion).
- **Project's current path**: Route R (Decl 1 builds `IsRegularLocalRing R`, then Decl 3 reads
  finrank cotangent = dim). Blocked on R1+R2+R3, all absent; R3 needs the missing `IsRegularRing`.
- **Gap**: divergent-with-cost. Route R chose the regularity idiom, whose smooth→regular and
  flat-descent prerequisites are absent from the snapshot; Mathlib's actually-present idiom for the
  same numerical fact is the conormal iso (Route C).
- **Cost of divergence**: staying on Route R = building `IsRegularRing` + Jacobian regularity +
  flat descent (≈3 deep absent lemmas). Switching to Route C = assembling present lemmas only.
- **Verdict**: **ALIGN_WITH_MATHLIB** — commit to Route C.

### Decision (sub): does Route C hide a deep cotangent-complex-vanishing obligation?
- **No.** Smoothness of the stalk R is consumed as the *typeclass hypothesis* `[FormallySmooth k R]`
  fed into `kerCotangentToTensor_injective_iff`. The residual `Subsingleton` obligation lands on
  `H1Cotangent k κ` (the k→κ extension), discharged by `FormallySmooth.subsingleton_h1Cotangent`
  applied to `FormallySmooth k κ` (trivial for κ=k; `of_perfectField` for κ separable over alg-closed
  k). The deep `H1Cotangent k R` is never touched. **Verdict: PROCEED** (no hidden flat-descent).

## Recommendation

**Commit to Route C.** Retarget Decl 3 `isDiscreteValuationRing_of_smooth_dim_one` to assemble the
conormal iso directly, bypassing Decl 1's regularity (and its absent R1/R2/R3). Sketched chain
(all names PRESENT, verified locally):

1. Set `κ := IsLocalRing.ResidueField R`; `IsLocalRing.ker_residue` ⟹ source of
   `kerCotangentToTensor k R κ` is `(𝔪).Cotangent = 𝔪/𝔪²`.
2. `FormallySmooth k κ`: `Algebra.FormallySmooth.of_perfectField` (κ EssFiniteType over k via
   `EssFiniteType.comp`; `IsAlgClosed k ⟹ PerfectField k` instance). [κ=k makes this trivial.]
3. `Subsingleton (Algebra.H1Cotangent k κ) := FormallySmooth.subsingleton_h1Cotangent`.
4. **Injective**: `(FormallySmooth.kerCotangentToTensor_injective_iff hsurj).mpr ‹Subsingleton _›`.
5. **Surjective**: `exact_kerCotangentToTensor_mapBaseChange k R κ hsurj` + `Subsingleton Ω[κ⁄k]`
   (κ=k ⟹ `Ω[k⁄k]` subsingleton) ⟹ `mapBaseChange` kills everything ⟹ range = ⊤.
6. Bijective ⟹ `LinearEquiv` `𝔪/𝔪² ≃ κ⊗_R Ω[R⁄k]`; with `Module.finrank_baseChange` and the
   `CotangentSpace R ≅ κ⊗_R(𝔪/𝔪²) ≅ 𝔪/𝔪²` bookkeeping:
   `finrank κ (CotangentSpace R) = rank R Ω[R⁄k]`.
7. **rank R Ω[R⁄k] = 1**: from the rel-dim-1 standard-smooth chart `S` (geometric input threaded
   from the smooth curve in OcOfD): `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
   (=1) + `IsStandardSmooth.free_kaehlerDifferential`, transported to `R = S_q` via
   `KaehlerDifferential.isLocalizedModule`.
8. `finrank κ (CotangentSpace R) = 1` ⟹ `IsDiscreteValuationRing R` via
   `IsLocalRing.finrank_CotangentSpace_eq_one_iff`.

**Interface note**: step 7's `rank Ω[R⁄k]=1` is the one piece NOT pinned by `ringKrullDim R = 1`
alone (that would need the absent `rank Ω = dim` CI-dim theory R1). Thread the relative-dimension-1
Kähler fact from the smooth-curve geometry (OcOfD), e.g. add `Module.rank R Ω[R⁄k] = 1` (or the
rel-dim-1 chart) to the Decl 3 interface, rather than re-deriving it from Krull dim. This is the same
geometric input Route R's R1 also requires, but Route C consumes it as a present module fact instead
of feeding an absent regularity/flat-descent machine. Decl 3 is NOT a protected signature, so the
interface may be adjusted; the OcOfD wiring lemma already expects only `finrank=1`.

**Net**: Route C eliminates all 3 absent Route-R gaps, replacing them with ~50–80 LOC of present-lemma
assembly + the shared rel-dim-1 input. Decl 1 (`IsRegularLocalRing_of_smooth`, general dim) can be
dropped from the critical path (or later closed cheaply: finrank cotangent = 1 = dim ⟹
`iff_finrank_cotangentSpace.mpr`).

## Severity
high-stakes — determines whether the DVR-stalk substrate's critical path carries 3 absent deep
lemmas (Route R) or zero (Route C). Verdict: **ALIGN_WITH_MATHLIB → Route C**.
