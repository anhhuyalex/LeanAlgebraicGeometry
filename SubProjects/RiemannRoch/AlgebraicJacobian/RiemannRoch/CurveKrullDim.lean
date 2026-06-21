/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.RiemannRoch.SmoothStalkDVR
import AlgebraicJacobian.Albanese.CoheightBridge

/-!
# Krull dimension of a smooth relative-dimension-one curve is at most one

Blueprint: `blueprint/src/chapters/RiemannRoch_CurveKrullDim.tex`

This file supplies three declarations establishing `Order.krullDim (α := C.left) ≤ 1`
for a smooth, relative-dimension-one, integral curve over an algebraically closed field.

## Structure

* **G1** (`ringKrullDim_le_of_moduleFinite_injective`, root namespace):
  Keystone Cohen–Seidenberg upper bound: a module-finite injective algebra extension
  cannot raise Krull dimension. Source: Stacks Tag 00OJ.

* **C** (`AlgebraicGeometry.chart_ringKrullDim_le_one`):
  A relative-dimension-one standard-smooth domain over a field has Krull dimension ≤ 1.
  Source: Stacks Tag 00P0; proved via Noether normalization + G1.

* **T** (`AlgebraicGeometry.krullDim_curve_le_one`):
  The Krull dimension of the underlying space of a smooth curve is at most one;
  assembled from G1, C, and the CoheightBridge.
-/

universe u

open AlgebraicGeometry CategoryTheory Order

-- ============================================================
-- G1 — Keystone: Cohen–Seidenberg upper bound (root namespace)
-- ============================================================

/- Planner strategy (G1 — `lem:ringKrullDim_le_of_moduleFinite_injective`,
   Stacks Tag 00OJ):

   **Mathlib idiom chosen**: algebra form `[Algebra R S] [Module.Finite R S]` +
   explicit `hinj : Function.Injective (algebraMap R S)`.
   Reason: `Algebra.IsIntegral.of_finite` is a **registered instance** in Mathlib
   (`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`), so `[Module.Finite R S]`
   immediately gives `[Algebra.IsIntegral R S]` without extra work.  The going-up
   machinery (`Ideal.exists_ideal_over_prime_of_isIntegral`,
   `Ideal.exists_ideal_over_maximal_of_isIntegral`) and incomparability
   consume `[Algebra.IsIntegral R S]` directly.

   **Proof route** (Stacks Tag 00OJ, "immediately from incomparability + going-up"):
   1. `haveI : Algebra.IsIntegral R S := inferInstance` (from `Module.Finite.of_finite`).
   2. Take a strict chain q₀ ⊊ q₁ ⊊ … ⊊ qₑ of primes in S.
      Contract to pᵢ := (algebraMap R S).ker ⊆ pᵢ = Ideal.comap (algebraMap R S) qᵢ.
      The contracted chain is increasing; it is strict because
      `Algebra.IsIntegral` satisfies incomparability: two primes of S lying over the
      same prime of R are incomparable in S (use `Ideal.isMaximal_of_isIntegral_of_isMaximal`
      / `Ideal.Incomparable` / `Ideal.eq_of_le_of_isIntegral`; check which is present).
      Injectivity of `algebraMap R S` ensures ker = ⊥ ⊆ every prime of R, so the
      contractions pᵢ are primes of R.
   3. The strict chain p₀ ⊊ … ⊊ pₑ witnesses length ≤ ringKrullDim R.
      Hence every chain length in S is realised in R ⟹ `ringKrullDim S ≤ ringKrullDim R`.

   **Recommended Mathlib API to drive the proof**:
   - `Algebra.IsIntegral.of_finite` (instance)
   - `Ideal.comap_isMaximal_of_surjective` / `Ideal.Incomparable` (incomparability)
   - `ringKrullDim_le_iff` or `Order.krullDim_le_iff` (chain-length ≤)
   - Alternatively, look for `ringKrullDim_le_of_isIntegral` or
     `ringKrullDim_algebraMap_le` — if one appears in a future Mathlib bump it may
     collapse this to a one-liner. -/
/-- Incomparability for integral extensions, general-ring form.  Mathlib ships this
only for `integralClosure R A` (`Ideal.IntegralClosure.comap_lt_comap`); this is the
version for an arbitrary integral `R`-algebra `A`.  Given primes `I < J` of `A`, their
contractions to `R` are strictly nested.  Proof: contraction is monotone, and the case
of equal contractions is excluded by passing to the quotient `A ⧸ I` — a domain integral
over the domain `R ⧸ I.comap`, in which `J ⧸ I` would be a nonzero prime contracting to
`⊥`, contradicting `Ideal.IsIntegralClosure.comap_ne_bot`. -/
theorem comap_lt_comap_of_isIntegral
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
    {I J : Ideal A} [I.IsPrime] (hIJ : I < J) :
    Ideal.comap (algebraMap R A) I < Ideal.comap (algebraMap R A) J := by
  refine lt_of_le_of_ne (Ideal.comap_mono hIJ.le) ?_
  intro heq
  -- Notation for the contracted prime `p = I.comap` and the quotient tower.
  set p := Ideal.comap (algebraMap R A) I with hp
  haveI : p.IsPrime := Ideal.IsPrime.comap _
  haveI : I.LiesOver p := ⟨hp⟩
  -- `A ⧸ I` is a domain integral over `R ⧸ p`; the latter is nontrivial.
  haveI : IsDomain (A ⧸ I) := Ideal.Quotient.isDomain I
  haveI : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr ‹p.IsPrime›.ne_top
  -- The image `J ⧸ I` is a nonzero ideal of `A ⧸ I`.
  set J' : Ideal (A ⧸ I) := Ideal.map (Ideal.Quotient.mk I) J with hJ'
  have hJ'_ne : J' ≠ ⊥ := by
    intro hbot
    -- `J' = ⊥` means `J ⊆ I`, contradicting `I < J`.
    have hJI : J ≤ I := by
      intro a ha
      have hmem : Ideal.Quotient.mk I a ∈ J' := Ideal.mem_map_of_mem _ ha
      rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
      exact hmem
    exact absurd (le_antisymm hIJ.le hJI) hIJ.ne
  -- Its contraction to `R ⧸ p` is `⊥`, because `J.comap = I.comap = p`.
  have hcontr : Ideal.comap (algebraMap (R ⧸ p) (A ⧸ I)) J' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_comap] at hx
    -- `algebraMap (R⧸p) (A⧸I) (mk p r) = mk I (algebraMap R A r)`.
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver I p r] at hx
    have hxJ : Ideal.Quotient.mk I (algebraMap R A r) ∈ J' := hx
    -- `mk I (a) ∈ J ⧸ I ↔ a ∈ J` (using `I ≤ J`).
    rw [hJ', ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIJ.le] at hxJ
    have hrp : r ∈ p := by rw [heq, Ideal.mem_comap]; exact hxJ
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact hrp
  -- `under (R⧸p) J' = comap (algebraMap (R⧸p) (A⧸I)) J' = ⊥` contradicts `under_ne_bot`.
  exact (Ideal.under_ne_bot (R ⧸ p) hJ'_ne) (by rw [Ideal.under_def]; exact hcontr)

theorem ringKrullDim_le_of_moduleFinite_injective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (_hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim S ≤ ringKrullDim R := by
  -- Module-finite ⇒ integral (registered instance), so incomparability holds.
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  -- `ringKrullDim X = Order.krullDim (PrimeSpectrum X)`; we show the contraction map
  -- `PrimeSpectrum.comap (algebraMap R S)` is strictly monotone (this is exactly the
  -- incomparability half of Cohen–Seidenberg), which by `Order.krullDim_le_of_strictMono`
  -- yields the dimension bound.  Injectivity of `algebraMap R S` is not needed for the
  -- `≤` direction (it is the going-up half giving equality); incomparability alone suffices.
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  intro q₁ q₂ h
  -- `h : q₁ < q₂` in `PrimeSpectrum S`; goal `comap q₁ < comap q₂` in `PrimeSpectrum R`.
  haveI : q₁.asIdeal.IsPrime := q₁.isPrime
  -- The `PrimeSpectrum` order is, by definition, the ideal-inclusion order, so `<`
  -- transfers to `asIdeal` definitionally.
  have hlt : q₁.asIdeal < q₂.asIdeal := h
  have key := comap_lt_comap_of_isIntegral (R := R) hlt
  change (PrimeSpectrum.comap (algebraMap R S) q₁).asIdeal
      < (PrimeSpectrum.comap (algebraMap R S) q₂).asIdeal
  simpa only [PrimeSpectrum.comap_asIdeal] using key

namespace AlgebraicGeometry

-- ============================================================
-- C — The crux: Krull dimension of a standard-smooth chart
-- ============================================================

/- Planner strategy (C — `lem:chart_ringKrullDim_le_one`, embedding-dimension route):

   The earlier trdeg route (`s = dim S = trdeg = rank Ω`) hit a genuine Mathlib gap
   (`dim = trdeg` / `trdeg = rank Ω` are both ABSENT) and is ABANDONED.  This proof
   uses the embedding-dimension inequality `dim R ≤ dim_κ(𝔪/𝔪²)` instead, reusing
   the conormal bridge already established for the DVR-stalk substrate.

   **Proof route** (every external step verified present in Mathlib):
   1. `Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim` rewrites
      `ringKrullDim S = ⨆_{𝔪 maximal} primeHeight 𝔪`, reducing the goal to
      `primeHeight 𝔪 ≤ 1` for every maximal `𝔪`.
   2. Localise: `T := Localization.AtPrime 𝔪`, a Noetherian local domain, with
      `IsLocalization.AtPrime.ringKrullDim_eq_height` giving
      `primeHeight 𝔪 = height 𝔪 = ringKrullDim T`.
   3. Krull's height theorem `ringKrullDim_le_spanFinrank_maximalIdeal` together with
      `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` bounds
      `ringKrullDim T ≤ finrank κ(T) (CotangentSpace T)`.
   4. The conormal bridge
      `Algebra.finrank_cotangentSpace_localization_eq_one_of_isStandardSmooth_dim_one`
      gives `finrank κ(T) (CotangentSpace T) = 1`.  Its two residue `Subsingleton`
      hypotheses come from `κ(T) = k̄`: since `𝔪` is maximal the composite
      `S ↠ κ(T)` is surjective (`algebraMap_residueField_surjective_of_isLocalization_atPrime`),
      so `κ(T)` is finite type over the algebraically closed `k̄`, hence `κ(T) ≅ k̄`
      (`IsAlgClosed.algebraMap_bijective_of_finiteType`), feeding
      `subsingleton_kaehlerDifferential_of_algebraMap_bijective` and
      `subsingleton_h1Cotangent_of_algebraMap_bijective`.
   Chaining: `primeHeight 𝔪 = ringKrullDim T ≤ finrank κ(T) (CotangentSpace T) = 1`. -/
theorem chart_ringKrullDim_le_one
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar] {S : Type u} [CommRing S] [Algebra kbar S]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 kbar S] [IsDomain S] :
    ringKrullDim S ≤ 1 := by
  -- Standard-smooth ⇒ finite type ⇒ Noetherian over the field `kbar`.
  haveI : Algebra.IsStandardSmooth kbar S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 1)
  haveI : Algebra.FiniteType kbar S := Algebra.FiniteType.of_finitePresentation
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing kbar S
  -- STEP 1: `ringKrullDim S = ⨆_{𝔪 maximal} primeHeight 𝔪`; reduce to a per-`𝔪` bound.
  rw [← Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim (R := S), ← WithBot.coe_one]
  refine WithBot.coe_le_coe.mpr (iSup_le fun I => iSup_le fun hI => ?_)
  -- Fix a maximal ideal `I`; goal `primeHeight I ≤ 1` (in `ℕ∞`).
  haveI : I.IsPrime := hI.isPrime
  set T := Localization.AtPrime I with hT
  haveI : IsNoetherianRing T := IsLocalization.isNoetherianRing I.primeCompl T inferInstance
  -- STEP 4: cotangent dimension of the localisation is one, via the conormal bridge.
  have hcot : Module.finrank (IsLocalRing.ResidueField T) (IsLocalRing.CotangentSpace T) = 1 := by
    -- Scalar tower `kbar → S → κ(T)`, needed to view `κ(T)` as a finite-type `kbar`-algebra.
    haveI : IsScalarTower kbar S (IsLocalRing.ResidueField T) := by
      refine IsScalarTower.of_algebraMap_eq fun x => ?_
      rw [IsScalarTower.algebraMap_apply kbar T (IsLocalRing.ResidueField T),
          IsScalarTower.algebraMap_apply S T (IsLocalRing.ResidueField T),
          IsScalarTower.algebraMap_apply kbar S T]
    -- `I` maximal ⇒ `S ↠ κ(T)` surjective ⇒ `κ(T)` finite type over `kbar` ⇒ `κ(T) ≅ kbar`.
    have hsurj : Function.Surjective (algebraMap S (IsLocalRing.ResidueField T)) :=
      Algebra.algebraMap_residueField_surjective_of_isLocalization_atPrime I T
    haveI : Algebra.FiniteType kbar (IsLocalRing.ResidueField T) :=
      Algebra.FiniteType.of_surjective
        (IsScalarTower.toAlgHom kbar S (IsLocalRing.ResidueField T)) hsurj
    have hbij : Function.Bijective (algebraMap kbar (IsLocalRing.ResidueField T)) :=
      IsAlgClosed.algebraMap_bijective_of_finiteType kbar _
    -- The two residue-field vanishings supplied by `κ(T) ≅ kbar`.
    haveI : Subsingleton (Ω[IsLocalRing.ResidueField T⁄kbar]) :=
      subsingleton_kaehlerDifferential_of_algebraMap_bijective hbij
    haveI : Subsingleton (Algebra.H1Cotangent kbar (IsLocalRing.ResidueField T)) :=
      subsingleton_h1Cotangent_of_algebraMap_bijective hbij
    exact Algebra.finrank_cotangentSpace_localization_eq_one_of_isStandardSmooth_dim_one
      kbar S T I.primeCompl
  -- STEP 3: Krull's height theorem + cotangent identification ⇒ `ringKrullDim T ≤ 1`.
  have hdimle : ringKrullDim T ≤ (1 : WithBot ℕ∞) := by
    calc ringKrullDim T
        ≤ ↑(Submodule.spanFinrank (IsLocalRing.maximalIdeal T)) :=
          ringKrullDim_le_spanFinrank_maximalIdeal T
      _ = ↑(Module.finrank (IsLocalRing.ResidueField T) (IsLocalRing.CotangentSpace T)) := by
          rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace T]
      _ = (1 : WithBot ℕ∞) := by rw [hcot]; rfl
  -- STEP 2: `primeHeight I = height I = ringKrullDim T`, so `primeHeight I ≤ 1`.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height I T, Ideal.height_eq_primeHeight,
      ← WithBot.coe_one] at hdimle
  exact WithBot.coe_le_coe.mp hdimle

-- ============================================================
-- T — The dimension bound for a smooth curve
-- ============================================================

/- Planner strategy (T — `thm:krullDim_curve_le_one`):

   **Proof route** (outer reduction + localisation push + C):

   STEP 1 — Reduce to pointwise coheight bound.
   `Order.krullDim_eq_iSup_coheight` (Mathlib, `Mathlib.Order.KrullDimension`) gives:
   `Order.krullDim (α := C.left) = ⨆ z, ↑(Order.coheight z)`.
   It suffices to show `↑(Order.coheight z) ≤ 1` for every `z : C.left`
   (use `iSup_le` / `ciSup_le`).

   STEP 2 — Bridge coheight → ring dimension.
   `AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_coheight C.left z`
   (imported from `AlgebraicJacobian.Albanese.CoheightBridge`) gives:
   `ringKrullDim (C.left.presheaf.stalk z) = Order.coheight z`.
   Goal becomes `ringKrullDim (C.left.presheaf.stalk z) ≤ 1`.

   STEP 3 — Standard-smooth chart at z.
   `AlgebraicGeometry.isLocalization_stalk_standardSmooth_chart_of_smooth C z`
   (imported from `AlgebraicJacobian.RiemannRoch.SmoothStalkDVR`) gives:
   `⟨V, hV, hxV, ψ, hψ, hLoc⟩` where:
   · `V : C.left.Opens`, `hV : IsAffineOpen V`, `hxV : z ∈ V`
   · `ψ : kbar →+* Γ(C.left, V)`, `hψ : RingHom.IsStandardSmoothOfRelativeDimension 1 ψ`
   · `hLoc : @IsLocalization _ _ (hV.primeIdealOf ⟨z, hxV⟩).asIdeal.primeCompl
               (C.left.presheaf.stalk z) _ (C.left.presheaf.algebra_section_stalk ⟨z, hxV⟩)`
   Set `S := Γ(C.left, V)` and `P := hV.primeIdealOf ⟨z, hxV⟩`.

   STEP 4 — Localisation + height bound.
   Via `algebraize [ψ]`: `Algebra kbar S` and
   `Algebra.IsStandardSmoothOfRelativeDimension 1 kbar S` (from `@[algebraize]` attribute on
   `RingHom.IsStandardSmoothOfRelativeDimension`).
   The stalk is a localisation at `P.asIdeal.primeCompl`, so
   `IsLocalization.AtPrime (C.left.presheaf.stalk z) P.asIdeal` holds (from `hLoc`).
   Apply:
   · `IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (C.left.presheaf.stalk z)`:
     `ringKrullDim (stalk z) = ↑P.asIdeal.height`
   · `Ideal.height_le_ringKrullDim_of_isPrime`:
     `↑P.asIdeal.height ≤ ringKrullDim S`

   STEP 5 — Chart dimension bound + IsDomain derivation.
   `C.left` is integral + `V` is a nonempty affine open ⟹ `Γ(C.left, V)` is a domain.
   (Derive via `IsIntegral.isDomain` on the restriction, or directly from `IsIntegral C.left`
   and an affine-scheme domain transfer lemma.)
   Then `chart_ringKrullDim_le_one` (C above) gives `ringKrullDim S ≤ 1`.

   STEP 6 — Chain and conclude.
   Chain: `ringKrullDim (stalk z) = ↑P.height ≤ ringKrullDim S ≤ 1`.
   Cast back: `↑(Order.coheight z) = ringKrullDim (stalk z) ≤ 1`.
   Take `iSup_le` over `z` to get `Order.krullDim (α := C.left) ≤ 1`. -/
theorem krullDim_curve_le_one
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))}
    [SmoothOfRelativeDimension 1 C.hom] [LocallyOfFiniteType C.hom]
    [IsIntegral C.left] :
    Order.krullDim (α := C.left) ≤ 1 := by
  -- STEP 1: reduce to a pointwise coheight bound.
  rw [Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun z => ?_
  -- STEP 2: bridge coheight → stalk dimension.
  rw [← Scheme.ringKrullDim_stalk_eq_coheight C.left z]
  -- Goal: `ringKrullDim (C.left.presheaf.stalk z) ≤ 1`.
  -- STEP 3: standard-smooth chart at `z` with stalk = localisation at `P`.
  obtain ⟨V, hV, hxV, ψ, hψ, hLoc⟩ :=
    isLocalization_stalk_standardSmooth_chart_of_smooth C z
  letI instST : Algebra (↑Γ(C.left, V)) (↑(C.left.presheaf.stalk z)) :=
    C.left.presheaf.algebra_section_stalk ⟨z, hxV⟩
  haveI instLoc : IsLocalization (hV.primeIdealOf ⟨z, hxV⟩).asIdeal.primeCompl
      (↑(C.left.presheaf.stalk z)) := hLoc
  -- STEP 4: base algebra + standard-smooth-of-rel-dim-1 instance via `algebraize`.
  algebraize [ψ]
  -- STEP 5: `Γ(C.left, V)` is a domain (integral scheme, nonempty chart).
  haveI : Nonempty V := Set.Nonempty.to_subtype ⟨z, hxV⟩
  haveI : IsDomain (↑Γ(C.left, V)) := IsIntegral.component_integral V
  haveI : (hV.primeIdealOf ⟨z, hxV⟩).asIdeal.IsPrime := (hV.primeIdealOf ⟨z, hxV⟩).isPrime
  haveI : IsLocalization.AtPrime (↑(C.left.presheaf.stalk z))
      (hV.primeIdealOf ⟨z, hxV⟩).asIdeal := instLoc
  -- STEP 6: chain `dim (stalk z) = height P = primeHeight P ≤ dim S ≤ 1`.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
        (hV.primeIdealOf ⟨z, hxV⟩).asIdeal (↑(C.left.presheaf.stalk z)),
      Ideal.height_eq_primeHeight]
  exact le_trans Ideal.primeHeight_le_ringKrullDim
    (chart_ringKrullDim_le_one (kbar := kbar) (S := ↑Γ(C.left, V)))

end AlgebraicGeometry
