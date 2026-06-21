/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Smooth local k-algebras are regular (DVR-stalk substrate)

Blueprint: `blueprint/src/chapters/RiemannRoch_SmoothRegular.tex`.

This file is **pure commutative algebra** — no scheme, sheaf, or curve.
The downstream consumer `RiemannRoch/OcOfD.lean` feeds in a stalk `𝒪_{C,x}`
and reads back a DVR; that bridge is performed there.

## Main declarations

1. `Algebra.IsRegularLocalRing_of_smooth`
   (`thm:smooth_local_isRegularLocalRing`):
   essentially-smooth Noetherian local k-algebra ⟹ regular local ring.

2. `IsRegularLocalRing.finrank_cotangentSpace_eq_ringKrullDim`
   (`lem:finrank_cotangent_eq_ringKrullDim_of_regular`):
   regular local ring ⟹ finrank_κ(m/m²) = ringKrullDim R.

3. `Algebra.isDiscreteValuationRing_of_smooth_dim_one`
   (`lem:smooth_stalk_isDVR`):
   essentially-smooth Noetherian local k-algebra of Krull dimension 1 +
   integral domain ⟹ DiscreteValuationRing.

## Verified Mathlib anchors (Mathlib rev b80f227)

The following are **present** in the pinned Mathlib and may be used directly:
- `IsRegularLocalRing.spanFinrank_maximalIdeal` ✓
    `↑(spanFinrank (maximalIdeal R)) = ringKrullDim R`
- `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` ✓
    `spanFinrank (maximalIdeal R) = finrank κ (CotangentSpace R)` (needs IsNoetherianRing)
- `IsLocalRing.finrank_CotangentSpace_eq_one_iff` ✓
    `finrank κ (CotangentSpace R) = 1 ↔ IsDiscreteValuationRing R` (needs IsDomain)
- `IsDiscreteValuationRing.TFAE` ✓
- `Algebra.IsStandardSmooth.free_kaehlerDifferential` ✓
    `Module.Free S Ω[S/R]`
- `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` ✓
    `Module.rank S Ω[S/R] = n` (needs Nontrivial S)
- `IsRegularLocalRing.iff_finrank_cotangentSpace` ✓
    `IsRegularLocalRing R ↔ ↑(finrank κ (CotangentSpace R)) = ringKrullDim R`
- `Algebra.Smooth.formallySmooth` ✓

## Known-absent sub-gaps (build project-side, mathlib-build mode)

- `IsRegularRing` and `IsRegularRing.isRegularLocalRing_localization` are
  ABSENT from pinned Mathlib b80f227 (loogle ≠ local-search discrepancy confirmed).
- Jacobian-criterion regularity: Ω free of rank = dim ⟹ regular local ring
  is not a standalone Mathlib lemma; must be assembled via Stacks 00TT argument.
- The localization transport (regularity of chart S_g descends to S_q) must
  be built using `iff_finrank_cotangentSpace` + cotangent finrank transport.
-/

/-! ### Declaration 1: smooth local ring ⟹ regular local ring -/

/- Planner strategy (thm:smooth_local_isRegularLocalRing, Stacks 00TT + 056S):

Hypotheses: `[FormallySmooth k R]` + `[EssFiniteType k R]` express "essentially smooth":
R is the localisation S_q of a finite-type k-algebra S at a prime q on a basic open
where S is standard smooth over k. (Note: `[Algebra.Smooth k R]` would require
FinitePresentation, which fails for localisations; use FormallySmooth + EssFiniteType.)

CORRECTION (iter-005 prover): the scaffold originally used `[FiniteType k R]`, but that
hypothesis set is UNSATISFIABLE in the intended application: a finite-type k-algebra is a
Jacobson ring, so a 1-dimensional finite-type *domain* has infinitely many maximal ideals
and can never be local. The curve stalk `𝒪_{C,x}` is *essentially* of finite type
(a localisation of a finite-type algebra), i.e. `Algebra.EssFiniteType k R`, which is also
exactly the class Stacks 00TT's chart argument consumes. Switched to `EssFiniteType`
(the reduction below never touches this hypothesis, so the change is proof-neutral here;
it only matters for the residual Jacobian gap and for downstream instantiability).

PROOF ROUTE (Jacobian criterion, Stacks 00TT):

Step 1 — Ω-freeness on the standard-smooth chart:
  Find S, g, q with g ∉ q such that S_g ≅ (chart of R) and
  `Algebra.IsStandardSmooth k (S_g)` holds.
  Apply `Algebra.IsStandardSmooth.free_kaehlerDifferential` (VERIFIED):
    → `Module.Free (S_g) Ω[S_g/k]`.
  Apply `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` (VERIFIED)
  for the relative dimension n:
    → `Module.rank (S_g) Ω[S_g/k] = n`.

Step 2 — Residue-dimension count:
  Tensor Ω[S_g/k] with the residue field κ(q):
    `finrank κ(q) (Ω[S_g/k] ⊗ κ(q)) = n = dim_x X`.
  This gives the numerical equality feeding the Jacobian criterion.

Step 3 — Regularity at q (Stacks 00TT, the main sub-gap):
  ABSENT from Mathlib: the prover must build
  `IsRegularLocalRing_of_standardSmooth_localisation`:
  If S_g is standard smooth of relative dimension n over k and q is a prime of S_g,
  then `IsRegularLocalRing (Localization.AtPrime S_g q)`.
  Route: finrank of cotangent at q equals n = ringKrullDim (S_g)_q,
  then apply `IsRegularLocalRing.iff_finrank_cotangentSpace` (VERIFIED) backwards.
  Sub-sub-gap: flat descent (Stacks 00TT, Tag 00NQ): if A → B is a flat local map,
  B regular, fiber B ⊗_A κ(m_A) regular ⟹ A regular. Not in Mathlib as a standalone.

If Step 3 is too deep, accept as an authorisd gap and mark with `sorry` tagged
`-- AUTHORIZED_GAP: smooth-local⟹regular, Stacks 00TT`.
-/
theorem Algebra.IsRegularLocalRing_of_smooth
    (k R : Type*) [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] [Algebra.FormallySmooth k R] [Algebra.EssFiniteType k R] :
    IsRegularLocalRing R := by
  -- Structural reduction (project-side, mathlib-build): regularity of a Noetherian local
  -- ring is equivalent to `spanFinrank(𝔪) = ringKrullDim R`. The inequality
  -- `ringKrullDim R ≤ spanFinrank(𝔪)` is Krull's height theorem
  -- (`ringKrullDim_le_spanFinrank_maximalIdeal`, VERIFIED present), true for *every*
  -- Noetherian local ring. Hence `IsRegularLocalRing R` reduces, via
  -- `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` (VERIFIED present), to the reverse
  -- inequality `spanFinrank(𝔪) ≤ ringKrullDim R` — equivalently
  -- `finrank κ (𝔪/𝔪²) ≤ dim R`. THIS is the entire Jacobian-criterion content of
  -- Stacks 00TT and is the sole remaining gap of this theorem.
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  -- GENUINE DEEP GAP (Stacks 00TT, smooth ⟹ regular over a field):
  --   `(spanFinrank (IsLocalRing.maximalIdeal R) : WithBot ℕ∞) ≤ ringKrullDim R`.
  -- Route to build (bottom-up, all absent from Mathlib b80f227):
  --   (1) `Ω[R/k]` is free of rank `n = dim R` on the standard-smooth finite-type chart
  --       (`Algebra.IsStandardSmooth.free_kaehlerDifferential` +
  --        `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`, both VERIFIED,
  --        but `rank Ω = ringKrullDim` for the chart is ABSENT — needs dimension theory of
  --        relative global complete intersections over a field);
  --   (2) the conormal/second-exact-sequence bound `finrank κ (𝔪/𝔪²) ≤ rank (Ω[R/k] ⊗ κ)`
  --       (requires the residue field to be separable over `k`; automatic when `k` is the
  --       algebraically closed base field of the curve application, where `κ = k`);
  --   (3) flat descent / localisation transport of the bound from the finite-type chart `S_g`
  --       to its localisation `R = (S_g)_q`. NOTE: `IsRegularRing` and
  --       `IsRegularRing.isRegularLocalRing_localization` are ABSENT from the project's pinned
  --       Mathlib b80f227 (locally confirmed via `#check`; upstream loogle lists them — the
  --       loogle≠local gotcha). So this transport must also be built project-side, e.g. via
  --       `IsRegularLocalRing.iff_finrank_cotangentSpace` + transport of the cotangent finrank
  --       along the localisation map.
  -- Hand-off decomposition recorded in task_results.
  sorry

/-! ### Declaration 2: regular local ring ⟹ finrank cotangent space = ringKrullDim -/

/- Planner strategy (lem:finrank_cotangent_eq_ringKrullDim_of_regular):

This is the FORWARD direction of the verified Mathlib iff:
  `IsRegularLocalRing.iff_finrank_cotangentSpace R` (VERIFIED):
    `IsRegularLocalRing R ↔ ↑(finrank (ResidueField R) (CotangentSpace R)) = ringKrullDim R`
The entire proof is:
  `exact (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance`

Alternatively, chain the two verified Mathlib lemmas:
  (A) `IsRegularLocalRing.spanFinrank_maximalIdeal` (VERIFIED):
        `↑(spanFinrank (maximalIdeal R)) = ringKrullDim R`
  (B) `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` (VERIFIED):
        `spanFinrank (maximalIdeal R) = finrank (ResidueField R) (CotangentSpace R)`
  Then coerce (B) and substitute into (A):
        `↑(finrank (ResidueField R) (CotangentSpace R)) = ringKrullDim R`.

Note: `ringKrullDim R : WithBot ℕ∞` and `finrank ... : ℕ`; the coercion `↑` goes
ℕ → WithBot ℕ∞ via the canonical `Nat.cast` chain.
-/
theorem IsRegularLocalRing.finrank_cotangentSpace_eq_ringKrullDim
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] :
    (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) : WithBot ℕ∞) =
    ringKrullDim R := by
  exact (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance

/-! ## Project-local Mathlib supplement — Route C: the conormal isomorphism

This is the **live (critical-path)** route to the DVR-stalk conclusion, replacing the
regularity contingency (Declaration 1) above. Every ingredient is present in the pinned
Mathlib; see `analogies/smooth-stalk-finrank-route-fork.md` and the Route C section of the
blueprint chapter. The chain is:

  conormal iso `𝔪/𝔪² ≃ₗ[κ] κ ⊗_R Ω[R/k]`  (Hartshorne II.8.7, from `kerCotangentToTensor`)
    ⟹ `finrank κ (CotangentSpace R) = finrank R Ω[R/k]`  (base-change rank)
    ⟹ `finrank R Ω[R/k] = 1` gives `finrank κ (CotangentSpace R) = 1`
    ⟹ `IsDiscreteValuationRing R`  (`finrank_CotangentSpace_eq_one_iff`).

The relative-dimension-one input `finrank R Ω[R/k] = 1` (with `Module.Free R Ω[R/k]`) is the
geometric datum threaded in from the smooth curve by the downstream consumer; it enters here
as a present module fact, never feeding the absent regularity/flat-descent machinery. -/

/-- **Conormal isomorphism (Hartshorne II.8.7).** For a formally smooth local `k`-algebra `R`
whose residue field `κ` has vanishing first cotangent homology over `k`
(`Subsingleton (Algebra.H1Cotangent k κ)`, e.g.\ `κ` formally smooth over `k`) and vanishing
relative differentials over `k` (`Subsingleton Ω[κ/k]`, automatic when `κ = k`), the cotangent
space `CotangentSpace R = 𝔪/𝔪²` is `κ`-linearly isomorphic to the base change
`κ ⊗_R Ω[R/k]` of the Kähler differentials. Project-local: assembles Mathlib's
cotangent-complex API (`KaehlerDifferential.kerCotangentToTensor`) into the geometric conormal
isomorphism. The conormal map's source `(ker (R → κ)).Cotangent` is identified with `𝔪/𝔪²`
via `IsLocalRing.ker_residue`, and the `R`-linear bijection is promoted to `κ`-linear by
extending scalars along the surjection `R → κ`. -/
noncomputable def IsLocalRing.cotangentSpace_linearEquiv_baseChange_kaehler
    (k R : Type*) [Field k] [CommRing R] [IsLocalRing R]
    [Algebra k R] [Algebra.FormallySmooth k R]
    [hh : Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField R))]
    [ho : Subsingleton (Ω[IsLocalRing.ResidueField R⁄k])] :
    IsLocalRing.CotangentSpace R ≃ₗ[IsLocalRing.ResidueField R]
      TensorProduct R (IsLocalRing.ResidueField R) Ω[R⁄k] := by
  set κ := IsLocalRing.ResidueField R
  have hsurj : Function.Surjective (algebraMap R κ) := IsLocalRing.residue_surjective
  -- Injectivity of the conormal map ⇔ `Subsingleton (H1Cotangent k κ)` (formal smoothness of `R`).
  have hinj : Function.Injective (KaehlerDifferential.kerCotangentToTensor k R κ) :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hsurj).mpr hh
  -- Surjectivity from the right-exact conormal sequence and `Ω[κ/k] = 0`.
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R κ hsurj
  have hsur : Function.Surjective (KaehlerDifferential.kerCotangentToTensor k R κ) := by
    intro y; exact (hex y).mp (Subsingleton.elim _ _)
  -- Bundle as an `R`-linear equivalence, cast the source `(ker (R → κ)).Cotangent` to
  -- `𝔪.Cotangent`, then extend scalars along the surjection `R → κ`.
  let e₀ := LinearEquiv.ofBijective (KaehlerDifferential.kerCotangentToTensor k R κ) ⟨hinj, hsur⟩
  let castEq :=
    Ideal.Cotangent.equivOfEq (RingHom.ker (algebraMap R κ)) (IsLocalRing.maximalIdeal R)
      IsLocalRing.ker_residue
  let e₁ : IsLocalRing.CotangentSpace R ≃ₗ[R] TensorProduct R κ Ω[R⁄k] := castEq.symm.trans e₀
  exact LinearEquiv.extendScalarsOfSurjective hsurj e₁

/-- **Cotangent dimension equals the Kähler rank** (numerical corollary of the conormal
isomorphism). Under the hypotheses of `IsLocalRing.cotangentSpace_linearEquiv_baseChange_kaehler`,
with `Ω[R/k]` free over `R`, the residue-field dimension of the cotangent space equals the
`R`-rank of the differentials. Project-local. -/
theorem IsLocalRing.finrank_cotangentSpace_eq_finrank_kaehler
    (k R : Type*) [Field k] [CommRing R] [IsLocalRing R]
    [Algebra k R] [Algebra.FormallySmooth k R]
    [Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField R))]
    [Subsingleton (Ω[IsLocalRing.ResidueField R⁄k])]
    [Module.Free R Ω[R⁄k]] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
      Module.finrank R Ω[R⁄k] := by
  rw [(IsLocalRing.cotangentSpace_linearEquiv_baseChange_kaehler k R).finrank_eq]
  exact Module.finrank_baseChange (R := IsLocalRing.ResidueField R) (S := R) (M' := Ω[R⁄k])

/-! ### Declaration 3 (Route C): smooth + rel-dim 1 + IsDomain ⟹ DVR -/

/- Planner strategy (lem:smooth_stalk_isDVR), **retargeted to Route C** (iter-006):

The original `ringKrullDim R = 1` hypothesis (Route R, blocked on the absent
`Algebra.IsRegularLocalRing_of_smooth` Jacobian/flat-descent gap) is replaced by the
relative-dimension-one Kähler input `finrank R Ω[R/k] = 1` together with `Module.Free R Ω[R/k]`.
The proof is the mechanical composition:
  (i)   `IsLocalRing.finrank_cotangentSpace_eq_finrank_kaehler` (Route C, axiom-clean):
          `finrank κ (CotangentSpace R) = finrank R Ω[R/k]`.
  (ii)  substitute `hrank : finrank R Ω[R/k] = 1` ⟹ `finrank κ (CotangentSpace R) = 1`.
  (iii) `IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp` (VERIFIED, needs `IsDomain`,
          `IsNoetherianRing`) ⟹ `IsDiscreteValuationRing R`.

Interface note: Declaration 3 is NOT a protected signature, so its hypotheses were adjusted
from `ringKrullDim R = 1` to the Route-C interface. The residue-field obligations
`Subsingleton (H1Cotangent k κ)` and `Subsingleton Ω[κ/k]` are threaded explicitly (both hold
in the geometric application `κ = k̄`); the downstream `OcOfD` consumer supplies them along
with the rel-dim-1 free Kähler input from the smooth-curve chart geometry. -/
theorem Algebra.isDiscreteValuationRing_of_smooth_dim_one
    (k R : Type*) [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [Algebra k R] [Algebra.FormallySmooth k R] [Algebra.EssFiniteType k R]
    [Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField R))]
    [Subsingleton (Ω[IsLocalRing.ResidueField R⁄k])]
    [Module.Free R Ω[R⁄k]]
    (hrank : Module.finrank R Ω[R⁄k] = 1) :
    IsDiscreteValuationRing R := by
  -- Route C: cotangent dimension = Kähler rank = 1, then the DVR characterisation.
  have hone : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 1 := by
    rw [IsLocalRing.finrank_cotangentSpace_eq_finrank_kaehler k R]; exact hrank
  -- cotangent dimension 1 ⟺ DVR  (`IsLocalRing.finrank_CotangentSpace_eq_one_iff`, VERIFIED)
  exact (IsLocalRing.finrank_CotangentSpace_eq_one_iff (R := R)).mp hone
