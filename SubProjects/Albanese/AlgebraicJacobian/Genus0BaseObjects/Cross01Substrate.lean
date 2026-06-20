/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.Genus0BaseObjects.BareScheme
import AlgebraicJacobian.Genus0BaseObjects.ChartIso
import AlgebraicJacobian.Genus0BaseObjects.Points

/-!
# Cross01 substrate — Lane B (𝔾ₘ-scaling) reusable lemmas

This file ships **substrate** lemmas needed to close the Lane B
`gmScalingP1_chart_agreement_cross01` cocycle proof (path (III.c) of
`AbelianVarietyRigidity.tex`) together with two off-target sorries
(`gm_geomIrred`, `projGm_isReduced`) in `Genus0BaseObjects/GmScaling.lean`.

The substrates are generic in the geometric situation and live in their own
file rather than inline so they can be re-used by the three GmScaling consumer
applications and, if upstreamed, by Mathlib itself.  Their construction
follows the recipe of `analogies/lane-b-substrate.md` (§2) and the prover-facing
specification at `blueprint/src/chapters/Genus0BaseObjects_Cross01Substrate.tex`.

## Contents (this iter)

* `AlgebraicGeometry.IsClosedImmersion.lift_iff_range_subset` —
  Substrate 1 (iter-189, axiom-clean): the closed-immersion universal
  property phrased as a topological range containment (under reduced
  source / target hypotheses).

* `AlgebraicGeometry.gmRing_tensor_homogeneousAway_isDomain` —
  Substrate 2 (iter-190): the tensor
  `Away f ⊗_{k̄} GmRing k̄` is a domain, via the iso chain to
  `Localization.Away (X () : MvPolynomial Unit (Away f))` per
  `analogies/lane-b-substrate.md` §3.
-/

set_option autoImplicit false
set_option linter.style.setOption false
set_option linter.style.show false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory TopologicalSpace Topology

noncomputable section

namespace AlgebraicGeometry

namespace IsClosedImmersion

/--
**Closed immersion lift by range inclusion.**
For a closed immersion `i : Z ⟶ X` whose source `Z` is reduced and a
quasi-compact morphism `g : Y ⟶ X` whose source `Y` is reduced, `g` factors
through `i` if and only if the topological range of `g` is contained in the
topological range of `i`.

This is the topological-range form of the universal property of closed
immersions; the kernel-inequality form is `IsClosedImmersion.lift` /
`IsClosedImmersion.lift_fac`.  The two forms are interchanged by the Galois
connection `vanishingIdeal ⊣ support` on ideal sheaves
(`IdealSheafData.gc` / `IdealSheafData.vanishingIdeal_support`).

This is **Substrate 1** of the Lane B Cross01 cocycle proof; see
`blueprint/src/chapters/Genus0BaseObjects_Cross01Substrate.tex`,
`Theorem~\ref{thm:IsClosedImmersion_lift_iff_range_subset}`.
-/
theorem lift_iff_range_subset
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z]
    (g : Y ⟶ X) [QuasiCompact g] [IsReduced Y] :
    (∃ h : Y ⟶ Z, h ≫ i = g) ↔ Set.range g.base ⊆ Set.range i.base := by
  refine ⟨?_, ?_⟩
  · -- (⇒) Forward direction: range pushdown.
    rintro ⟨h, rfl⟩
    rintro _ ⟨y, rfl⟩
    refine ⟨h.base y, ?_⟩
    simp [Scheme.Hom.comp_base]
  · -- (⇐) Backward direction: the substantive content.
    intro hrange
    -- Helper: the kernel of a ring hom into a reduced ring is a radical ideal.
    have ker_isRadical : ∀ {R S : Type u} [CommSemiring R] [CommSemiring S]
        [_root_.IsReduced S] (f : R →+* S), (RingHom.ker f).IsRadical := by
      intro R S _ _ _ f x hx
      obtain ⟨n, hxn⟩ := hx
      rw [RingHom.mem_ker] at hxn ⊢
      have h₁ : (f x) ^ n = 0 := by
        rw [← map_pow]; exact hxn
      exact eq_zero_of_pow_eq_zero h₁
    -- Step 1: For a closed immersion, the support of its kernel equals its range.
    -- (`support_ker` gives `closure (range)`; closed range collapses the closure.)
    have hi_range_eq : (i.ker.support : Set X) = Set.range i.base := by
      rw [Scheme.Hom.support_ker]
      exact i.isClosedEmbedding.isClosed_range.closure_eq
    -- Step 2: `g.ker.support ⊆ i.ker.support` (set-theoretic, via `closure_minimal`).
    have hsup_set : (g.ker.support : Set X) ⊆ (i.ker.support : Set X) := by
      rw [Scheme.Hom.support_ker]
      refine closure_minimal ?_ i.ker.support.isClosed
      exact hrange.trans hi_range_eq.ge
    -- Promote the set inclusion to the `Closeds X` ordering.
    have hsup : g.ker.support ≤ i.ker.support := hsup_set
    -- Step 3: `g.ker` is radical (because `Y` is reduced, so each `Γ(Y, g ⁻¹ᵁ U)` is reduced
    -- and the ring kernel is therefore radical, pointwise on affine opens).
    have hg_rad : g.ker.radical = g.ker := by
      refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical _)
      intro U
      rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
      exact ker_isRadical (g.app U.1).hom
    -- Step 4: `i.ker` is radical (same argument; closed immersions are quasi-compact).
    have hi_rad : i.ker.radical = i.ker := by
      refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical _)
      intro U
      rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
      exact ker_isRadical (i.app U.1).hom
    -- Step 5: thread the Galois connection `vanishingIdeal ⊣ support`.
    have hker : i.ker ≤ g.ker := by
      calc i.ker
          = i.ker.radical := hi_rad.symm
        _ = Scheme.IdealSheafData.vanishingIdeal i.ker.support :=
              Scheme.IdealSheafData.vanishingIdeal_support.symm
        _ ≤ Scheme.IdealSheafData.vanishingIdeal g.ker.support :=
              Scheme.IdealSheafData.vanishingIdeal_antimono hsup
        _ = g.ker.radical := Scheme.IdealSheafData.vanishingIdeal_support
        _ = g.ker := hg_rad
    -- Step 6: feed the kernel inequality to Mathlib's `IsClosedImmersion.lift`.
    exact ⟨IsClosedImmersion.lift i g hker, IsClosedImmersion.lift_fac i g hker⟩

end IsClosedImmersion

/--
**Substrate 2 — `Away f ⊗_{k̄} GmRing k̄` is a domain.**

For a non-zero homogeneous element `f` of positive degree `d` in the
`projectiveLineBar` grading on `MvPolynomial (Fin 2) k̄`, the tensor
`HomogeneousLocalization.Away (projectiveLineBarGrading k̄) f ⊗_{k̄} GmRing k̄`
is an integral domain.

The proof identifies the tensor with the localization
`Localization.Away (X () : MvPolynomial Unit (Away f))` via the
chain of natural isomorphisms in `analogies/lane-b-substrate.md` §3:
* `Away f ⊗_{k̄} 𝕜[t] ≃ 𝕜[t][Away f]` (`MvPolynomial.algebraTensorAlgEquiv`),
* tensor base change with the localization
  `𝕜[t] → GmRing k̄` produces `Localization.Away (X ())`
  (`IsLocalization.Away.tensorRight`).

`Localization.Away (X () : MvPolynomial Unit (Away f))` is a domain because
it is the localization of `MvPolynomial Unit (Away f)` (a polynomial ring
over the domain `Away f`) at the powers of the non-zero generator `X ()`.

This is **Substrate 2** of the Lane B Cross01 cocycle proof; see
`blueprint/src/chapters/Genus0BaseObjects_Cross01Substrate.tex`,
`Theorem~\ref{thm:gmRing_tensor_homogeneousAway_isDomain}`.
-/
@[nolint unusedArguments]
theorem gmRing_tensor_homogeneousAway_isDomain
    (kbar : Type u) [Field kbar] {d : ℕ} (_hd : 0 < d)
    (f : MvPolynomial (Fin 2) kbar)
    (_hf : f ∈ projectiveLineBarGrading kbar d)
    (_hf_ne : f ≠ 0) :
    IsDomain (TensorProduct kbar
      (HomogeneousLocalization.Away (projectiveLineBarGrading kbar) f)
      (GmRing kbar)) := by
  classical
  -- Abbreviation for the homogeneous localization (a `kbar`-algebra and a domain).
  let A : Type u := HomogeneousLocalization.Away (projectiveLineBarGrading kbar) f
  -- =====================================================================
  -- Step 1: `A` is a domain.
  -- =====================================================================
  -- The bridge `val : A → Localization.Away f` is injective, and we transport
  -- domain-ness via `Function.Injective.isDomain`.  This pattern is the same
  -- one used inside `projectiveLineBar_isReduced` (`GmScaling.lean` L734-738).
  haveI hLocAway_dom :
      IsDomain (Localization.Away (f : MvPolynomial (Fin 2) kbar)) := by
    have hPoly_dom : IsDomain (MvPolynomial (Fin 2) kbar) := inferInstance
    by_cases hf_zero : f = 0
    · -- if f = 0, Localization.Away f is Subsingleton, but we still need IsDomain.
      -- Instead, contradict with hf_ne.
      exact absurd hf_zero _hf_ne
    · exact IsLocalization.isDomain_localization
        (powers_le_nonZeroDivisors_of_noZeroDivisors hf_zero)
  haveI hA_dom : IsDomain A :=
    Function.Injective.isDomain (algebraMap A (Localization.Away f))
      (fun x y h => HomogeneousLocalization.val_injective _ h)
  -- =====================================================================
  -- Step 2: `MvPolynomial Unit A` is a domain (polynomial ring over a domain).
  -- =====================================================================
  haveI hT_dom : IsDomain (MvPolynomial Unit A) := inferInstance
  -- =====================================================================
  -- Step 3: Build the natural iso
  --   `A ⊗[kbar] (GmRing kbar) ≃ₐ[A] Localization.Away (X () : MvPolynomial Unit A)`.
  -- =====================================================================
  -- Step 3a:  `A ⊗[kbar] (MvPolynomial Unit kbar) ≃ₐ[A] MvPolynomial Unit A`.
  -- This is `MvPolynomial.algebraTensorAlgEquiv` directly.
  let e1 : TensorProduct kbar A (MvPolynomial Unit kbar) ≃ₐ[A] MvPolynomial Unit A :=
    MvPolynomial.algebraTensorAlgEquiv kbar A
  -- Step 3b: Establish IsLocalization of the target tensor.
  -- We use the `Algebra.TensorProduct.rightAlgebra` to view the tensor as a
  -- localization. The plan is to set up the algebra structure correctly
  -- so that `IsLocalization.Away.tensorRight` applies.
  --
  -- Plan: build a `RingEquiv` from `A ⊗[kbar] (GmRing kbar)` to
  -- `Localization.Away (X () : MvPolynomial Unit A)`, then transport IsDomain.
  --
  -- For the iso, we use:
  --   `A ⊗[kbar] (GmRing kbar) ≃ A ⊗[kbar] (MvPolynomial Unit kbar) localized at X()`
  --   ≃ `MvPolynomial Unit A` localized at X () (via e1)
  --   ≃ `Localization.Away (X () : MvPolynomial Unit A)`.
  --
  -- The first iso uses that tensor commutes with localization.
  -- We package this via `IsLocalization` instances + uniqueness of localization.
  --
  -- Concretely, we apply `IsLocalization.isDomain_localization` once we
  -- establish that `A ⊗[kbar] (GmRing kbar)` is the localization of a domain
  -- at a non-zero-divisor submonoid.
  --
  -- The cleanest path: show `IsLocalization (powers (1 ⊗ X())) (A ⊗[kbar] Gm)`,
  -- where the base ring `S := A ⊗[kbar] (MvPolynomial Unit kbar)` is a domain
  -- (via `e1`), and `1 ⊗ X()` is non-zero (corresponding to `X ()` in
  -- `MvPolynomial Unit A` via `e1`).
  let S : Type u := TensorProduct kbar A (MvPolynomial Unit kbar)
  haveI hS_dom : IsDomain S :=
    Function.Injective.isDomain e1.toRingHom e1.injective
  -- The element we localize at: `1 ⊗ X () : S`.
  let xS : S := (1 : A) ⊗ₜ[kbar] (MvPolynomial.X () : MvPolynomial Unit kbar)
  -- `xS ≠ 0`: it maps under `e1` to `X () : MvPolynomial Unit A`, which is non-zero.
  have hxS_ne : xS ≠ 0 := by
    intro h
    have he1 : e1 xS = e1 0 := by rw [h]
    have he1' : e1 xS = (MvPolynomial.X () : MvPolynomial Unit A) := by
      simp [e1, xS, MvPolynomial.algebraTensorAlgEquiv_tmul]
    rw [he1'] at he1
    simp at he1
  -- Now establish: `A ⊗[kbar] (GmRing kbar)` is an `IsLocalization` of `S` at `powers xS`.
  -- We use `IsLocalization.Away.tensorRight` with a tweak.
  --
  -- Detail: set up the algebra structures so that S = A ⊗[kbar] (MvPolynomial Unit kbar)
  -- is a `MvPolynomial Unit kbar`-algebra via `rightAlgebra`, and then
  -- `(GmRing kbar) ⊗[MvPolynomial Unit kbar] S` is a localization of `S`
  -- at the image of `powers (X())`, which equals `powers xS`.
  --
  -- Then identify `(GmRing kbar) ⊗[MvPolynomial Unit kbar] S ≃ A ⊗[kbar] (GmRing kbar)`
  -- via base-change cancellation.
  --
  -- To avoid heavy elaboration, we construct the iso explicitly by
  -- universal properties.
  letI rightAlg : Algebra (MvPolynomial Unit kbar) S :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower kbar (MvPolynomial Unit kbar) S := inferInstance
  -- A ⊗[kbar] (GmRing kbar) has commuting algebra maps from A and Gm.
  -- Define forward: φ : A ⊗[kbar] Gm →ₐ[kbar] Localization.Away xS
  -- via TensorProduct.lift on (A → LocAwayxS) and (Gm → LocAwayxS).
  -- (b) Gm → LocAwayxS via IsLocalization.Away.lift, using that X () maps to
  --     a unit in Localization.Away xS.
  -- The base map MvPolynomial Unit kbar → Localization.Away xS sends X () to
  -- the image of `xS` in `Localization.Away xS`, which is a unit.
  let polkToLocAwayxS : MvPolynomial Unit kbar →ₐ[kbar] Localization.Away xS :=
    (Algebra.ofId S (Localization.Away xS)).restrictScalars kbar |>.comp
      (Algebra.TensorProduct.includeRight :
        MvPolynomial Unit kbar →ₐ[kbar] S)
  -- Image of X () under polkToLocAwayxS is the image of xS in LocAwayxS.
  have hX_unit_polk : IsUnit
      (polkToLocAwayxS (MvPolynomial.X () : MvPolynomial Unit kbar)) := by
    have h_eq : polkToLocAwayxS (MvPolynomial.X () : MvPolynomial Unit kbar)
        = (algebraMap S (Localization.Away xS)) xS := by
      show (Algebra.ofId S (Localization.Away xS)).toRingHom
        ((Algebra.TensorProduct.includeRight : MvPolynomial Unit kbar →ₐ[kbar] S)
          (MvPolynomial.X ())) = _
      rfl
    rw [h_eq]
    exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away xS) xS
  let f2_ring : GmRing kbar →+* Localization.Away xS :=
    IsLocalization.Away.lift (S := GmRing kbar) (P := Localization.Away xS)
      (g := polkToLocAwayxS.toRingHom)
      (MvPolynomial.X () : MvPolynomial Unit kbar) hX_unit_polk
  -- Promote to AlgHom over kbar.
  let f2 : GmRing kbar →ₐ[kbar] Localization.Away xS :=
    { f2_ring with
      commutes' := fun k => by
        show f2_ring _ = _
        have step :
            (algebraMap kbar (GmRing kbar)) k
              = (algebraMap (MvPolynomial Unit kbar) (GmRing kbar))
                ((algebraMap kbar (MvPolynomial Unit kbar)) k) :=
          (IsScalarTower.algebraMap_apply kbar (MvPolynomial Unit kbar)
            (GmRing kbar) k).symm
        rw [step]
        show f2_ring ((algebraMap (MvPolynomial Unit kbar) (GmRing kbar)) _) = _
        rw [IsLocalization.Away.lift_eq]
        exact polkToLocAwayxS.commutes k }
  -- Promote f1 to AlgHom kbar via restrictScalars.
  let f1_kbar : A →ₐ[kbar] Localization.Away xS :=
    (Algebra.ofId A (Localization.Away xS)).restrictScalars kbar
  -- Build φ.
  let φ : TensorProduct kbar A (GmRing kbar) →ₐ[kbar] Localization.Away xS :=
    Algebra.TensorProduct.lift f1_kbar f2 (fun _ _ => Commute.all _ _)
  -- =====================================================================
  -- Step 4: Build ψ : Localization.Away xS →+* TensorProduct kbar A (GmRing kbar)
  -- =====================================================================
  -- First the map S = A ⊗[kbar] (MvPolynomial Unit kbar) → target.
  -- We use Algebra.TensorProduct.map (AlgHom.id A) (algebraMap : MvPolynomial Unit kbar → Gm).
  let target : Type u := TensorProduct kbar A (GmRing kbar)
  let s_to_target_alg : S →ₐ[kbar] target :=
    Algebra.TensorProduct.map (AlgHom.id kbar A)
      (IsScalarTower.toAlgHom kbar (MvPolynomial Unit kbar) (GmRing kbar))
  let s_to_target : S →+* target := s_to_target_alg.toRingHom
  -- Image of xS is `1 ⊗ X()` (where X () is mapped to GmRing kbar), which is a unit.
  have hxS_unit_target : IsUnit (s_to_target xS) := by
    have h_eq : s_to_target xS = (1 : A) ⊗ₜ[kbar]
        (algebraMap (MvPolynomial Unit kbar) (GmRing kbar)
          (MvPolynomial.X () : MvPolynomial Unit kbar)) := by
      show s_to_target_alg ((1 : A) ⊗ₜ[kbar] (MvPolynomial.X () : MvPolynomial Unit kbar)) = _
      simp [s_to_target_alg, Algebra.TensorProduct.map_tmul]
      rfl
    rw [h_eq]
    -- 1 ⊗ (unit element) is a unit. Use the inverse 1 ⊗ (inv element).
    refine IsUnit.map
      (Algebra.TensorProduct.includeRight : GmRing kbar →ₐ[kbar] target).toRingHom ?_
    exact IsLocalization.Away.algebraMap_isUnit
      (MvPolynomial.X () : MvPolynomial Unit kbar)
  -- Lift to ψ.
  let ψ_ring : Localization.Away xS →+* target :=
    IsLocalization.Away.lift (S := Localization.Away xS) (P := target)
      (g := s_to_target) xS hxS_unit_target
  -- =====================================================================
  -- Step 5: Show φ ∘ ψ_ring = id  and  ψ_ring ∘ φ = id on generators.
  -- For Step 5, we only need ψ_ring ∘ φ = id (left inverse → injective);
  -- then `IsDomain` transfers via `Function.Injective.isDomain` + LocAwayxS domain.
  -- =====================================================================
  -- First establish that LocAwayxS is a domain.
  haveI hLocAwayxS_dom : IsDomain (Localization.Away xS) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away xS)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hxS_ne)
  -- =====================================================================
  -- Step 5: Show ψ_ring ∘ φ = id (left inverse → φ injective → IsDomain).
  -- =====================================================================
  -- Helper A: ψ_ring on the image of algebraMap S → Localization.Away xS is s_to_target.
  have hψ_alg :
      ∀ a : S, ψ_ring ((algebraMap S (Localization.Away xS)) a) = s_to_target a := by
    intro a
    show IsLocalization.Away.lift xS hxS_unit_target
        ((algebraMap S (Localization.Away xS)) a) = _
    exact IsLocalization.Away.lift_eq xS hxS_unit_target a
  -- Helper B: ψ_ring (f1_kbar a) = a ⊗ 1.
  have h_psi_f1 : ∀ a : A, ψ_ring (f1_kbar a) = (a : A) ⊗ₜ[kbar] (1 : GmRing kbar) := by
    intro a
    have heq : f1_kbar a = (algebraMap S (Localization.Away xS))
        ((a : A) ⊗ₜ[kbar] (1 : MvPolynomial Unit kbar)) := by
      show (algebraMap A (Localization.Away xS)) a = _
      rw [IsScalarTower.algebraMap_apply A S (Localization.Away xS) a]
      rfl
    rw [heq, hψ_alg]
    show s_to_target_alg ((a : A) ⊗ₜ[kbar] (1 : MvPolynomial Unit kbar)) = _
    rw [show s_to_target_alg ((a : A) ⊗ₜ[kbar] (1 : MvPolynomial Unit kbar))
        = (AlgHom.id kbar A) a ⊗ₜ[kbar]
          (IsScalarTower.toAlgHom kbar (MvPolynomial Unit kbar) (GmRing kbar)) 1 from rfl]
    simp
  -- Helper C: ψ_ring (f2 b) = 1 ⊗ b. We show ψ_ring ∘ f2 = includeRight via
  -- the universal property of `IsLocalization.Away (X()) (GmRing kbar)`.
  have h_psi_f2_aux : ∀ p : MvPolynomial Unit kbar,
      ψ_ring (f2 ((algebraMap (MvPolynomial Unit kbar) (GmRing kbar)) p))
        = (1 : A) ⊗ₜ[kbar]
            (algebraMap (MvPolynomial Unit kbar) (GmRing kbar) p) := by
    intro p
    -- f2 (algebraMap _ _ p) = polkToLocAwayxS p
    have step1 : f2 ((algebraMap (MvPolynomial Unit kbar) (GmRing kbar)) p)
        = polkToLocAwayxS p := by
      show f2_ring _ = _
      exact IsLocalization.Away.lift_eq (MvPolynomial.X () : MvPolynomial Unit kbar)
        hX_unit_polk p
    rw [step1]
    -- polkToLocAwayxS p = (algebraMap S (Localization.Away xS)) ((1 : A) ⊗ₜ p)
    have step2 : polkToLocAwayxS p
        = (algebraMap S (Localization.Away xS))
            ((1 : A) ⊗ₜ[kbar] p) := rfl
    rw [step2, hψ_alg]
    -- s_to_target ((1 : A) ⊗ₜ p) = (1 : A) ⊗ₜ algebraMap _ _ p
    show s_to_target_alg ((1 : A) ⊗ₜ[kbar] p) = _
    rw [show s_to_target_alg ((1 : A) ⊗ₜ[kbar] p)
        = (AlgHom.id kbar A) 1 ⊗ₜ[kbar]
          (IsScalarTower.toAlgHom kbar (MvPolynomial Unit kbar) (GmRing kbar)) p from rfl]
    simp
  -- Helper D: ψ_ring (f2 b) = 1 ⊗ b. Two ring homs `GmRing kbar →+* target` agree iff
  -- they agree after composing with `algebraMap (MvPolynomial Unit kbar) (GmRing kbar)`.
  have h_psi_f2 : ∀ b : GmRing kbar,
      ψ_ring (f2 b) = (1 : A) ⊗ₜ[kbar] (b : GmRing kbar) := by
    have h_eq_ringhoms : (ψ_ring.comp f2.toRingHom)
        = ((Algebra.TensorProduct.includeRight :
            GmRing kbar →ₐ[kbar] target).toRingHom) := by
      refine IsLocalization.ringHom_ext (S := GmRing kbar) (P := target)
        (Submonoid.powers (MvPolynomial.X () : MvPolynomial Unit kbar)) ?_
      refine RingHom.ext fun p => ?_
      show ψ_ring (f2 ((algebraMap (MvPolynomial Unit kbar) (GmRing kbar)) p))
        = (Algebra.TensorProduct.includeRight : GmRing kbar →ₐ[kbar] target)
            ((algebraMap (MvPolynomial Unit kbar) (GmRing kbar)) p)
      rw [h_psi_f2_aux p]
      rfl
    intro b
    have hb := RingHom.congr_fun h_eq_ringhoms b
    -- hb : ψ_ring (f2 b) = includeRight b = 1 ⊗ b
    exact hb
  -- Main: ψ_ring ∘ φ = id on every tensor element.
  have h_left_inv : ∀ x : TensorProduct kbar A (GmRing kbar), ψ_ring (φ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      have hφ0 : φ (0 : TensorProduct kbar A (GmRing kbar)) = 0 := φ.map_zero
      rw [hφ0, ψ_ring.map_zero]
    | tmul a b =>
      have h_phi : φ (a ⊗ₜ b) = f1_kbar a * f2 b := by
        show Algebra.TensorProduct.lift f1_kbar f2 _ (a ⊗ₜ b) = _
        rw [Algebra.TensorProduct.lift_tmul]
      rw [h_phi]
      rw [ψ_ring.map_mul]
      rw [h_psi_f1 a, h_psi_f2 b]
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rw [mul_one, one_mul]
    | add x y hx hy =>
      have hφxy : φ (x + y) = φ x + φ y := φ.map_add _ _
      rw [hφxy, ψ_ring.map_add, hx, hy]
  -- Conclude IsDomain via φ injective.
  refine Function.Injective.isDomain φ.toRingHom ?_
  intro x y hxy
  have h1 : ψ_ring (φ x) = ψ_ring (φ y) := by
    show ψ_ring (φ.toRingHom x) = ψ_ring (φ.toRingHom y)
    rw [hxy]
  rw [h_left_inv x, h_left_inv y] at h1
  exact h1

end AlgebraicGeometry

end
