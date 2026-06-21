/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.RiemannRoch.SmoothRegular
import AlgebraicJacobian.RiemannRoch.ResidueFieldKbar

/-!
# Geometric DVR-stalk bridge (Route C, at the curve stalk)

Blueprint: `blueprint/src/chapters/RiemannRoch_OcOfD.tex`,
§"The codimension-one regularity substrate".

This file realises the Route-C conormal chain of
`AlgebraicJacobian.RiemannRoch.SmoothRegular` at the *stalk* of a smooth curve.
The downstream consumer `RiemannRoch/OcOfD.lean` (L635) reads back
`finrank κ(x) (CotangentSpace 𝒪_{C,x}) = 1` and hence
`IsDiscreteValuationRing 𝒪_{C,x}` at each codimension-one point.

## Strategy

The curve stalk `𝒪_{C,x}` at a codimension-one point is the localisation
`T = Localization.AtPrime` of a relative-dimension-one standard-smooth affine
chart `S` of `C` over `k̄`.  The pure-commutative-algebra content of the
Route-C chain — turning the standard-smooth chart datum into a DVR at the
localisation — is isolated in the **abstract ring bridge**
`Algebra.isDiscreteValuationRing_localization_of_isStandardSmooth_dim_one`
(and its cotangent-dimension companion
`Algebra.finrank_cotangentSpace_localization_eq_one_of_isStandardSmooth_dim_one`).
This bridge needs no scheme theory: it consumes a standard-smooth `k̄`-algebra
`S`, a localisation `T`, and the residue-field rationality of `T`
(supplied as the two `Subsingleton` hypotheses, both automatic when
`κ(x) = k̄`), and emits the DVR / cotangent-dimension-one conclusion.

The remaining (scheme-theoretic) obligation, deferred to the next iteration, is
the *identification* of the curve stalk `C.left.presheaf.stalk x` with such a
localisation `T` of a standard-smooth chart, compatibly with the `k̄`-algebra
structure, together with the residue-field computation `κ(x) = k̄`.
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Algebra

/-! ## Project-local Mathlib supplement — the standard-smooth localisation bridge

These two lemmas are the pure commutative-algebra core of the Route-C
DVR-stalk substrate.  They have no Mathlib analogue because Mathlib's
standard-smooth Kähler API (`IsStandardSmooth.free_kaehlerDifferential`,
`IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`) lives at the
finite-type chart level, while the geometric application reads off the
differentials at the *localisation* (the stalk); the bridge transports
freeness and rank one across the localisation via
`KaehlerDifferential.isLocalizedModule_map` and assembles formal smoothness /
essential finite type of the localisation by composition. -/

/-- **Free rank-one Kähler differentials at a standard-smooth localisation.**
If `S` is a relative-dimension-one standard-smooth `k`-algebra and `T` is a
localisation of `S`, then `Ω[T/k]` is `T`-free of rank one.  Project-local:
transports the chart-level standard-smooth freeness/rank across the
localisation through `KaehlerDifferential.isLocalizedModule_map`. -/
theorem free_and_finrank_kaehlerDifferential_localization_eq_one
    (k S T : Type u) [Field k] [CommRing S] [CommRing T] [Nontrivial S] [Nontrivial T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (M : Submonoid S) [IsLocalization M T]
    [IsStandardSmoothOfRelativeDimension 1 k S] :
    Module.Free T Ω[T⁄k] ∧ Module.finrank T Ω[T⁄k] = 1 := by
  haveI : IsStandardSmooth k S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI : Module.Free S Ω[S⁄k] := IsStandardSmooth.free_kaehlerDifferential
  haveI hlm : IsLocalizedModule M (KaehlerDifferential.map k k S T) :=
    KaehlerDifferential.isLocalizedModule_map k S T M
  refine ⟨Module.free_of_isLocalizedModule (Rₛ := T) M (KaehlerDifferential.map k k S T), ?_⟩
  have hrankS : Module.finrank S Ω[S⁄k] = 1 := by
    have h : Module.rank S Ω[S⁄k] = (1 : ℕ) :=
      IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1
    exact Module.finrank_eq_of_rank_eq h
  rw [Module.finrank_of_isLocalizedModule_of_free T M (KaehlerDifferential.map k k S T)]
  exact hrankS

/-- **Cotangent space at a standard-smooth localisation with rational residue
field is one-dimensional.**  The pure-algebra core of the Route-C DVR-stalk
substrate: a localisation `T` of a relative-dimension-one standard-smooth
`k`-algebra `S`, whose residue field is `k`-rational (encoded by the two
`Subsingleton` hypotheses, both automatic when the residue field equals `k`),
has one-dimensional cotangent space `𝔪_T/𝔪_T²` over its residue field.
Combines `free_and_finrank_kaehlerDifferential_localization_eq_one` with
`SmoothRegular`'s conormal corollary
`IsLocalRing.finrank_cotangentSpace_eq_finrank_kaehler`. -/
theorem finrank_cotangentSpace_localization_eq_one_of_isStandardSmooth_dim_one
    (k S T : Type u) [Field k] [CommRing S] [CommRing T] [Nontrivial S]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (M : Submonoid S) [IsLocalization M T]
    [IsStandardSmoothOfRelativeDimension 1 k S]
    [IsLocalRing T]
    [Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField T))]
    [Subsingleton (Ω[IsLocalRing.ResidueField T⁄k])] :
    Module.finrank (IsLocalRing.ResidueField T) (IsLocalRing.CotangentSpace T) = 1 := by
  haveI : FormallySmooth k S :=
    haveI : IsStandardSmooth k S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
    inferInstance
  haveI : FormallySmooth S T := FormallySmooth.of_isLocalization M
  haveI : FormallySmooth k T := FormallySmooth.comp k S T
  obtain ⟨hfree, hrank⟩ :=
    free_and_finrank_kaehlerDifferential_localization_eq_one k S T M
  haveI := hfree
  rw [IsLocalRing.finrank_cotangentSpace_eq_finrank_kaehler k T]
  exact hrank

/-- **DVR at a standard-smooth localisation with rational residue field.**
The DVR endpoint of the pure-algebra Route-C chain: a Noetherian local
integral-domain localisation `T` of a relative-dimension-one standard-smooth
`k`-algebra `S`, with `k`-rational residue field, is a discrete valuation ring.
Combines `free_and_finrank_kaehlerDifferential_localization_eq_one` with
`SmoothRegular`'s `Algebra.isDiscreteValuationRing_of_smooth_dim_one`. -/
theorem isDiscreteValuationRing_localization_of_isStandardSmooth_dim_one
    (k S T : Type u) [Field k] [CommRing S] [CommRing T] [Nontrivial S]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (M : Submonoid S) [IsLocalization M T]
    [IsStandardSmoothOfRelativeDimension 1 k S]
    [IsLocalRing T] [IsDomain T] [IsNoetherianRing T]
    [Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField T))]
    [Subsingleton (Ω[IsLocalRing.ResidueField T⁄k])] :
    IsDiscreteValuationRing T := by
  haveI : IsStandardSmooth k S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI : FormallySmooth k S := inferInstance
  haveI : FormallySmooth S T := FormallySmooth.of_isLocalization M
  haveI : FormallySmooth k T := FormallySmooth.comp k S T
  haveI : FiniteType k S := FiniteType.of_finitePresentation
  haveI : EssFiniteType k S := EssFiniteType.of_finiteType k S
  haveI : EssFiniteType S T := EssFiniteType.of_isLocalization T M
  haveI : EssFiniteType k T := EssFiniteType.comp k S T
  obtain ⟨hfree, hrank⟩ :=
    free_and_finrank_kaehlerDifferential_localization_eq_one k S T M
  haveI := hfree
  exact isDiscreteValuationRing_of_smooth_dim_one k T hrank

/-- **The structure map into the residue field of a localisation at a maximal
ideal is surjective.**  Project-local: if `Rp` is a localisation of `R` at a
maximal prime `p` (i.e. `IsLocalization.AtPrime Rp p`), then the composite
`R → Rp → κ(Rp)` is surjective.  This is the affine-local input used to certify
that the residue field `κ(x)` of a smooth-curve stalk is finite type over `k̄`
(hence `= k̄`), keeping the residue-field `k̄`-algebra structure the one induced
from the stalk (avoiding the residue-field algebra diamond). -/
theorem algebraMap_residueField_surjective_of_isLocalization_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsMaximal]
    (Rp : Type u) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp] :
    Function.Surjective (algebraMap R (IsLocalRing.ResidueField Rp)) := by
  have hres : (algebraMap Rp (IsLocalRing.ResidueField Rp)) = IsLocalRing.residue Rp := rfl
  set φ : R →+* IsLocalRing.ResidueField Rp := algebraMap R (IsLocalRing.ResidueField Rp) with hφ
  have hφeq : ∀ r : R, φ r = IsLocalRing.residue Rp (algebraMap R Rp r) := by
    intro r
    rw [hφ, IsScalarTower.algebraMap_apply R Rp (IsLocalRing.ResidueField Rp), hres]
  have hker : ∀ r : R, φ r = 0 ↔ r ∈ p := by
    intro r
    rw [hφeq, IsLocalRing.residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff Rp p]
  intro y
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨⟨a, s⟩, hspec⟩ := IsLocalization.mk'_surjective p.primeCompl t
  simp only at hspec
  have hrel : IsLocalRing.residue Rp t * φ (s : R) = φ (a : R) := by
    have h2 := IsLocalization.mk'_spec Rp a s
    rw [hspec] at h2
    have h3 := congrArg (IsLocalRing.residue Rp) h2
    rw [map_mul] at h3
    rw [hφeq, hφeq]; exact h3
  have hsuptop : Ideal.span {(s : R)} ⊔ p = ⊤ := by
    by_contra h
    have heq : p = Ideal.span {(s : R)} ⊔ p := ‹p.IsMaximal›.eq_of_le h le_sup_right
    have hmem : (s : R) ∈ Ideal.span {(s : R)} ⊔ p :=
      Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
    rw [← heq] at hmem
    exact s.2 hmem
  have h1mem : (1 : R) ∈ Ideal.span {(s : R)} ⊔ p := hsuptop ▸ Submodule.mem_top
  rw [Submodule.mem_sup] at h1mem
  obtain ⟨u, hu, z, hz, huz⟩ := h1mem
  rw [Ideal.mem_span_singleton'] at hu
  obtain ⟨b, hb⟩ := hu
  have hφsb : φ ((s : R) * b) = 1 := by
    have hmem : (s : R) * b - 1 ∈ p := by
      have he : (s : R) * b = 1 - z := by rw [mul_comm, hb, ← huz]; ring
      rw [he]; simpa using p.neg_mem hz
    have h0 : φ ((s : R) * b - 1) = 0 := (hker _).mpr hmem
    rwa [map_sub, map_one, sub_eq_zero] at h0
  refine ⟨a * b, ?_⟩
  rw [map_mul]
  calc φ (a : R) * φ b
      = (IsLocalRing.residue Rp t * φ (s : R)) * φ b := by rw [hrel]
    _ = IsLocalRing.residue Rp t * φ ((s : R) * b) := by rw [map_mul]; ring
    _ = IsLocalRing.residue Rp t := by rw [hφsb, mul_one]

end Algebra

/-! ## Scheme-level targets — remaining obligations (handoff)

The four scheme-level pins of `RiemannRoch_OcOfD.tex` §"codimension-one
regularity substrate"
(`kaehlerDifferential_locallyFree_rank_one_of_smooth`,
`residueField_eq_of_coheight_eq_one`,
`finrank_cotangentSpace_stalk_eq_one_of_smooth`,
`isDiscreteValuationRing_stalk_of_smooth`) reduce, via the abstract algebra
bridge above, to two scheme-theoretic identifications that are **not** yet in
the project and are the documented next-iteration work:

* **Chart extraction + stalk-localisation identification.** From
  `SmoothOfRelativeDimension 1 C.hom` and a point `x : C.left`, produce an
  affine open `V ∋ x` of `C.left` whose coordinate ring `S = Γ(C.left, V)` is
  `Algebra.IsStandardSmoothOfRelativeDimension 1 k̄ S`, equip `S` and the stalk
  `T = C.left.presheaf.stalk x` with the `k̄`-algebra structure from the
  structure morphism, and supply `IsScalarTower k̄ S T` together with
  `IsLocalization (hV.primeIdealOf ⟨x,·⟩).asIdeal.primeCompl T`.  The stalk is
  a localisation by `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`
  [verified present]; the smoothness datum unfolds from
  `AlgebraicGeometry.IsSmoothOfRelativeDimension.mk` [verified present:
  `appLE C.hom U V e` is `RingHom.IsStandardSmoothOfRelativeDimension 1`], with
  `Γ(Spec k̄, U) ≅ k̄` via `Scheme.ΓSpecIso`.  Standard-smoothness of the *ring*
  `S` over `k̄` then follows from `appLE` standard-smoothness once `Γ(U)` is
  identified with `k̄`.

* **Residue-field rationality** (`residueField_eq_of_coheight_eq_one`).  At a
  codimension-one (hence closed) point of an integral finite-type `k̄`-scheme,
  `κ(x) = k̄` (Nullstellensatz / Jacobson).  No single-call Mathlib form was
  found (`IsLocalRing.ResidueField.finite_of_finite`,
  `Algebra.instFiniteResidueFieldOfQuasiFiniteAt`, and
  `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` are the closest raw
  material).  This supplies the two `Subsingleton` hypotheses of the abstract
  bridge (`Subsingleton Ω[κ(x)/k̄]`, `Subsingleton (H1Cotangent k̄ κ(x))`),
  both automatic once `κ(x) = k̄`.

Once both are in hand, each scheme pin is an application of the corresponding
`Algebra.*_localization_*` theorem above; `OcOfD.lean` L635 then closes via
`finrank_cotangentSpace_localization_eq_one_of_isStandardSmooth_dim_one`. -/

namespace AlgebraicGeometry

/- Planner strategy (Decl 1 of 2 — `lem:exists_standardSmooth_chart_of_smooth`):
   Entry: use the class field directly — NOT `HasRingHomProperty.appLE`, which yields
   the `Locally`-wrapped predicate and is the wrong shape.
     `obtain ⟨U, hU, V, hV, hx, e, hss⟩ :=
       ‹SmoothOfRelativeDimension 1 C.hom›.exists_isStandardSmoothOfRelativeDimension x`
   gives `hss : RingHom.IsStandardSmoothOfRelativeDimension 1 (C.hom.appLE U V e).hom`.
   Base identification: `Unique (Spec (.of kbar))` (Scheme.lean:629; automatic for Field)
   forces U = ⊤ via `Subsingleton.elim U ⊤` (only one affine open on Spec of a field).
   Compose with ΓSpecIso: define
     `ψ := (C.hom.appLE ⊤ V ...).hom.comp (ΓSpecIso kbar).inv.hom : kbar →+* Γ(C.left, V)`
   where `(ΓSpecIso kbar).inv.hom : kbar →+* Γ(Spec (.of kbar), ⊤)` (CommRingCat ring hom).
   Transport smoothness: use
     `isStandardSmoothOfRelativeDimension_respectsIso.left` (pre-compose with iso on the source)
   to lift `hss` along `(ΓSpecIso kbar).inv` to obtain
   `RingHom.IsStandardSmoothOfRelativeDimension 1 ψ`.
   Witness: `⟨V, hV, hx, ψ, h_ψ⟩`. -/
theorem exists_isStandardSmooth_chart_of_smooth
    {kbar : Type u} [Field kbar]
    (C : Over (Spec (.of kbar)))
    [SmoothOfRelativeDimension 1 C.hom]
    (x : C.left) :
    ∃ (V : C.left.Opens) (hV : IsAffineOpen V) (hx : x ∈ V)
      (ψ : kbar →+* Γ(C.left, V)),
      RingHom.IsStandardSmoothOfRelativeDimension 1 ψ := by
  obtain ⟨U, hU, V, hV, hx, e, hss⟩ :=
    (‹SmoothOfRelativeDimension 1 C.hom›).exists_isStandardSmoothOfRelativeDimension x
  -- `Spec` of a field is a single point, so the only nonempty open is `⊤`.
  have hU_top : U = ⊤ := by
    have hmem : C.hom.base x ∈ U := e hx
    rw [eq_top_iff]
    intro y _
    rwa [Subsingleton.elim y (C.hom.base x)]
  subst hU_top
  -- Precompose the chart map with `ΓSpecIso⁻¹ : k̄ ≅ Γ(Spec k̄, ⊤)` to pin the base to `k̄`.
  refine ⟨V, hV, hx, ((Scheme.ΓSpecIso (CommRingCat.of kbar)).inv ≫
      C.hom.appLE ⊤ V e).hom, ?_⟩
  have he : RingHom.IsStandardSmoothOfRelativeDimension 0
      (Scheme.ΓSpecIso (CommRingCat.of kbar)).inv.hom := by
    have h := RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of kbar)).symm.commRingCatIsoToRingEquiv
    rwa [CategoryTheory.Iso.commRingCatIsoToRingEquiv_toRingHom] at h
  rw [CommRingCat.hom_comp]
  simpa using hss.comp he

/- Planner strategy (Decl 2 of 2 — `lem:stalk_standardSmooth_localization_of_smooth`)
   prover may adjust this statement's packaging — not protected.
   Use Decl 1 to get `V, hV, hx, ψ, hψ` (set `S := Γ(C.left, V)`, `T := stalk x`).
   (1) Stalk as localization: `hV.isLocalization_stalk ⟨x, hx⟩` gives
       `IsLocalization.AtPrime T (hV.primeIdealOf ⟨x, hx⟩).asIdeal`
       (AffineScheme.lean:806; `Algebra S T` is automatic from the presheaf germ map).
   (2) Base and tower instances via `algebraize`:
       · `algebraize [ψ]` adds `Algebra kbar S` (= ψ.toAlgebra) and, via the
         `@[algebraize]` attribute on `RingHom.IsStandardSmoothOfRelativeDimension`,
         also `Algebra.IsStandardSmoothOfRelativeDimension 1 kbar S`.
       · `algebraize [ψ, (algebraMap S T).comp ψ]` additionally adds
         `Algebra kbar T` and `IsScalarTower kbar S T`.
   Instance list consumed by the pure-algebra bridge:
     `[Algebra kbar S]`, `[Algebra kbar T]`, `[Algebra S T]`, `[IsScalarTower kbar S T]`,
     `[IsLocalization M T]` (M = primeCompl),
     `[Algebra.IsStandardSmoothOfRelativeDimension 1 kbar S]`. -/
theorem isLocalization_stalk_standardSmooth_chart_of_smooth
    {kbar : Type u} [Field kbar]
    (C : Over (Spec (.of kbar)))
    [SmoothOfRelativeDimension 1 C.hom]
    (x : C.left) :
    ∃ (V : C.left.Opens) (hV : IsAffineOpen V) (hx : x ∈ V)
      (ψ : kbar →+* Γ(C.left, V))
      (_ : RingHom.IsStandardSmoothOfRelativeDimension 1 ψ),
      -- `Algebra Γ(C.left,V) (stalk x)` is NOT a global instance at `x : C.left`
      -- (algebra_section_stalk needs `⟨x, hx⟩ : ↑V`, not `x : C.left`).
      -- Use `IsLocalization M T` (the underlying class of `IsLocalization.AtPrime`)
      -- with explicit algebra instance to avoid unsynthesizable `[IsPrime]`.
      -- Semantically equivalent: `IsLocalization.AtPrime T P = IsLocalization P.primeCompl T`.
      @IsLocalization _ _ (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        (C.left.presheaf.stalk x) _
        (C.left.presheaf.algebra_section_stalk ⟨x, hx⟩) := by
  obtain ⟨V, hV, hx, ψ, hψ⟩ := exists_isStandardSmooth_chart_of_smooth C x
  exact ⟨V, hV, hx, ψ, hψ, hV.isLocalization_stalk ⟨x, hx⟩⟩

/- Planner strategy (`lem:cotangentSpace_finrank_eq_one_of_smooth`):
   Route: apply the pure-algebra core
   `Algebra.finrank_cotangentSpace_localization_eq_one_of_isStandardSmooth_dim_one`
   (same file, namespace `Algebra`) at `k := kbar`, `S := Γ(C.left, V)`, `T := stalk x`.

   STEP 1 — CHART + STALK-LOCALIZATION.
   `isLocalization_stalk_standardSmooth_chart_of_smooth C x`
   gives `⟨V, hV, hxV, ψ, hψ, hLoc⟩` where
     · `ψ : kbar →+* Γ(C.left, V)`,
     · `hψ : RingHom.IsStandardSmoothOfRelativeDimension 1 ψ`,
     · `hLoc : @IsLocalization _ _ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
                  (C.left.presheaf.stalk x) _ (C.left.presheaf.algebra_section_stalk ⟨x, hxV⟩)`.
   Set `S := Γ(C.left, V)`, `T := C.left.presheaf.stalk x`,
   `M := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl`.

   STEP 2 — INSTANCES via `algebraize`.
   · `algebraize [ψ]` → `Algebra kbar S` (= ψ.toAlgebra) and, via the `@[algebraize]`
     attribute on `RingHom.IsStandardSmoothOfRelativeDimension`,
     `Algebra.IsStandardSmoothOfRelativeDimension 1 kbar S`.
   · `algebraize [ψ, (algebraMap S T).comp ψ]` → additionally `Algebra kbar T` and
     `IsScalarTower kbar S T`.
   · `Algebra S T` from `hLoc`'s `algebra_section_stalk ⟨x, hxV⟩`.
   · `IsLocalization M T` = `hLoc` (carry the explicit instance through).
   · `IsLocalRing T` is automatic (stalk of a scheme is a local ring).
   · `Nontrivial S`: a standard-smooth k̄-algebra is nontrivial (field is nonzero).

   STEP 3 — RESIDUE = k̄ ⟹ two `Subsingleton` instances for the bridge.
   The bridge needs:
     `Subsingleton (Ω[IsLocalRing.ResidueField T ⁄ kbar])` and
     `Subsingleton (Algebra.H1Cotangent kbar (IsLocalRing.ResidueField T))`.
   Source: `residueField_eq_of_coheight_eq_one x hx hdim` (imported from `ResidueFieldKbar`)
   gives `⟨_, hbij⟩` with
     `hbij : Function.Bijective (algebraMap kbar (C.left.residueField x))`
   for the `residueFieldAlgebra` instance.
   Feed `hbij` to `subsingleton_kaehlerDifferential_of_algebraMap_bijective` and
   `subsingleton_h1Cotangent_of_algebraMap_bijective` (both from `ResidueFieldKbar`).

   *** THE CRUX — residue-field algebra DIAMOND ***
   `IsLocalRing.ResidueField T` (T = stalk x) is DEFEQ to `C.left.residueField x`
   (since `Scheme.residueField x = IsLocalRing.ResidueField (C.left.presheaf.stalk x)`),
   so the TYPES match. The issue is that the bridge's `Algebra kbar (ResidueField T)` is
   induced from the scalar-tower `Algebra kbar T` (quotiented by the maximal ideal),
   while `hbij` is for the `residueFieldAlgebra` coming from `C.hom.residueFieldMap`.
   Two viable routes:
     (a) [PREFERRED] Show the two `Algebra kbar (ResidueField T)` structures are equal:
         both are `RingHom.toAlgebra f` / `RingHom.toAlgebra g` with `f = g` because
         both factor the structure morphism `C.hom` through residue fields.
         Reconcile via `Algebra.algebra_ext` / `RingHom.ext` using the commuting-square
         compatibility of `appLE` with germ + residue maps.
     (b) Derive bijectivity of the bridge instance directly: the bridge map
         `kbar → T → ResidueField T` is a `kbar`-algebra ring hom from a field into
         `ResidueField T`, hence injective; surjectivity follows because `κ(x) = k̄`
         (from `hbij`) means the residue field is `k̄` and the composite is surjective.
         Combine with `residueFieldIsoBase`-style surjectivity.
   FLAG: if (a)/(b) prove multi-step-hard, land the bijectivity/diamond reconciliation
   as a `private` helper lemma and leave the precise handoff; partial progress is
   valuable.

   STEP 4 — CONCLUDE.
   `finrank_cotangentSpace_localization_eq_one_of_isStandardSmooth_dim_one kbar S T M`
   returns `finrank (ResidueField T) (CotangentSpace T) = 1`.
   The goal's `IsLocalRing.ResidueField (C.left.presheaf.stalk x)` and
   `IsLocalRing.CotangentSpace (C.left.presheaf.stalk x)` are DEFEQ to
   `ResidueField T` / `CotangentSpace T` (T = stalk x), so close by `exact` or `rfl`.

   NOTE: before committing to this route, the prover should run
   `lean_leansearch`/`lean_local_search` for a direct Mathlib shortcut (e.g.
   `IsRegularLocalRing` / smooth-local cotangent dimension), the way iter-010 found
   `residueFieldIsoBase` — but the bridge route above is the verified fallback. -/
/-- **Cotangent space at a codimension-one point of a smooth curve is one-dimensional.**
Scheme-level pin (`RiemannRoch_OcOfD.tex`, `lem:cotangentSpace_finrank_eq_one_of_smooth`).
The single substrate fact consumed by `OcOfD.lean` to build the
`IsRegularInCodimensionOne` witness. -/
theorem finrank_cotangentSpace_stalk_eq_one_of_smooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))}
    [SmoothOfRelativeDimension 1 C.hom] [LocallyOfFiniteType C.hom]
    [IsIntegral C.left]
    (x : C.left) (hx : Order.coheight x = 1)
    (hdim : Order.krullDim (α := C.left) ≤ 1) :
    Module.finrank
      (IsLocalRing.ResidueField (C.left.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (C.left.presheaf.stalk x)) = 1 := by
  obtain ⟨V, hV, hxV, ψ, hψ, hLoc⟩ :=
    isLocalization_stalk_standardSmooth_chart_of_smooth C x
  -- `Algebra S T` from the germ map; `IsLocalization M T` from `hLoc`.
  letI instST : Algebra (↑Γ(C.left, V)) (↑(C.left.presheaf.stalk x)) :=
    C.left.presheaf.algebra_section_stalk ⟨x, hxV⟩
  haveI instLoc : IsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (↑(C.left.presheaf.stalk x)) := hLoc
  -- base algebra + scalar tower + standard-smooth instance via `algebraize`.
  algebraize [ψ, (algebraMap (↑Γ(C.left, V)) (↑(C.left.presheaf.stalk x))).comp ψ]
  -- `S` is nontrivial: it maps into the (nontrivial) local stalk.
  haveI : Nontrivial (↑Γ(C.left, V)) :=
    (algebraMap (↑Γ(C.left, V)) (↑(C.left.presheaf.stalk x))).domain_nontrivial
  -- `S` is finite type over `k̄` (standard-smooth ⟹ finite presentation ⟹ finite type).
  haveI : Algebra.IsStandardSmooth kbar (↑Γ(C.left, V)) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI : Algebra.FiniteType kbar (↑Γ(C.left, V)) := Algebra.FiniteType.of_finitePresentation
  -- The point `x` is closed (codim one in a `≤ 1`-dim'l space), so the prime of the
  -- chart `S` it corresponds to is maximal.
  haveI hmax : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩
      (isClosed_singleton_of_coheight_eq_one x hx hdim)
  -- Residue-field rationality, in the *bridge's* `k̄`-algebra structure (no diamond):
  -- `S ↠ κ(x)` is surjective (localisation at a maximal ideal), so `κ(x)` is finite type
  -- over `k̄`, hence `κ(x) ≅ k̄` (`k̄` algebraically closed).
  have hsurj : Function.Surjective
      (algebraMap (↑Γ(C.left, V)) (IsLocalRing.ResidueField ↑(C.left.presheaf.stalk x))) :=
    Algebra.algebraMap_residueField_surjective_of_isLocalization_atPrime
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal (↑(C.left.presheaf.stalk x))
  haveI : Algebra.FiniteType kbar
      (IsLocalRing.ResidueField ↑(C.left.presheaf.stalk x)) :=
    Algebra.FiniteType.of_surjective
      (IsScalarTower.toAlgHom kbar (↑Γ(C.left, V))
        (IsLocalRing.ResidueField ↑(C.left.presheaf.stalk x))) hsurj
  have hbij : Function.Bijective
      (algebraMap kbar (IsLocalRing.ResidueField ↑(C.left.presheaf.stalk x))) :=
    IsAlgClosed.algebraMap_bijective_of_finiteType kbar _
  -- The two residue-field vanishings the bridge needs, from rationality `κ(x) ≅ k̄`.
  haveI : Subsingleton (Ω[IsLocalRing.ResidueField ↑(C.left.presheaf.stalk x)⁄kbar]) :=
    subsingleton_kaehlerDifferential_of_algebraMap_bijective hbij
  haveI : Subsingleton
      (Algebra.H1Cotangent kbar (IsLocalRing.ResidueField ↑(C.left.presheaf.stalk x))) :=
    subsingleton_h1Cotangent_of_algebraMap_bijective hbij
  refine Algebra.finrank_cotangentSpace_localization_eq_one_of_isStandardSmooth_dim_one
    kbar (↑Γ(C.left, V)) (↑(C.left.presheaf.stalk x))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl

end AlgebraicGeometry
