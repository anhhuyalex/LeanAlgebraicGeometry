/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Genus-`0` base objects (Stratum 1): the bare scheme `ProjectiveLineBar` and its 2-chart cover

This file is **Stratum 1** of the four-stratum split of the legacy
`AlgebraicJacobian.Genus0BaseObjects` (iter-175 refactor `g0bo-split`). It ships:

* the standard ℕ-grading on `MvPolynomial (Fin 2) k̄`;
* the `kbar`-algebra structure on `HomogeneousLocalization.Away 𝒜 f`;
* the projective line `ProjectiveLineBarScheme` / `ProjectiveLineBar` as an object of
  `Over (Spec (.of kbar))`;
* properness of `ProjectiveLineBar.hom` (`projectiveLineBar_isProper`);
* the scaffold `GeometricallyIrreducible` / `SmoothOfRelativeDimension 1` instances;
* the 2-chart affine open cover `projectiveLineBarAffineCover`.

Downstream strata: `ChartIso` (chart-ring iso), `Points` (k̄-points + `Ga` + `Gm`),
`GmScaling` (chart-bridge + `σ_×`).
-/

set_option autoImplicit false
set_option linter.style.setOption false

universe u w

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace AlgebraicGeometry

/-! ### (A) The projective line `ℙ¹` over `Spec k̄` (the `Proj` realisation) -/

/-- The **standard ℕ-grading on `k̄[X₀, X₁]`** by total degree.

This is the homogeneous-component decomposition `MvPolynomial.homogeneousSubmodule`
specialised to two variables (`Fin 2`) over `k̄`. The `GradedRing` instance is
`MvPolynomial.gradedAlgebra` (free).

Used to define `ProjectiveLineBar = Proj` of this graded ring. -/
abbrev projectiveLineBarGrading (kbar : Type u) [Field kbar] :
    ℕ → Submodule kbar (MvPolynomial (Fin 2) kbar) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) kbar

instance projectiveLineBarGrading_gradedRing (kbar : Type u) [Field kbar] :
    GradedRing (projectiveLineBarGrading kbar) :=
  MvPolynomial.gradedAlgebra

/-- `kbar`-algebra structure on `HomogeneousLocalization.Away 𝒜 f` via the
composition `kbar →+* ↥(𝒜 0) →+* Away 𝒜 f`. Mathlib only ships
`Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x)`; this instance bridges the
remaining `kbar →+* 𝒜 0` algebra map shipped via `SetLike.GradeZero.instAlgebra`.
Required for `TensorProduct kbar (Away _ _) _` to synthesize `CommRing`/`Algebra kbar`. -/
noncomputable instance algebraKbarAway (kbar : Type u) [Field kbar]
    (f : MvPolynomial (Fin 2) kbar) :
    Algebra kbar
      (HomogeneousLocalization.Away (projectiveLineBarGrading kbar) f) :=
  Algebra.compHom _ (algebraMap kbar ((projectiveLineBarGrading kbar) 0))

/-- **The projective line over `Spec k̄` as a scheme.** This is `Proj 𝒜` of the standard
ℕ-graded `k̄[X₀, X₁]`. Carries an `Over (Spec (.of kbar))` instance via
`Proj.toSpecZero` composed with the algebra-map identification of the degree-`0` piece
with `k̄` (Mathlib's `SetLike.GradeZero.instAlgebraSubtypeMemOfNat`).

`IsProper` is FREE — see the `instIsProper` instance below. `IsAlgClosed kbar` is *not*
required for the scheme itself but is needed for downstream `Smooth`/geometric
irreducibility instances. -/
def ProjectiveLineBarScheme (kbar : Type u) [Field kbar] : Scheme :=
  Proj (projectiveLineBarGrading kbar)

/-- The natural `Over (Spec (.of kbar))` structure on `ProjectiveLineBarScheme` via
`Proj.toSpecZero` and the identification `k̄ ≃ ↥(𝒜 0)`. -/
instance projectiveLineBarScheme_canOver (kbar : Type u) [Field kbar] :
    (ProjectiveLineBarScheme kbar).Over (Spec (.of kbar)) where
  hom := Proj.toSpecZero (projectiveLineBarGrading kbar) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap kbar ↥((projectiveLineBarGrading kbar) 0)))

/-- **The projective line `ℙ¹_{k̄}` as an object of `Over (Spec (.of kbar))`.** This is the
concrete scheme used by `morphism_P1_to_grpScheme_const` (iter-166) to formalise the
`𝔾_m`-scaling shortcut. -/
def ProjectiveLineBar (kbar : Type u) [Field kbar] : Over (Spec (.of kbar)) :=
  (ProjectiveLineBarScheme kbar).asOver (Spec (.of kbar))

/-- **`ℙ¹_{k̄}` is proper over `Spec k̄`.** FREE from
`AlgebraicGeometry.Proj.instIsProperToSpecZero…` — the algebra `k̄[X₀, X₁]` is finite type
over its degree-`0` piece `↥(𝒜 0) ≃ k̄` — chained via the standard properness-of-composition
lemma with the `Spec.map` of the algebra map `k̄ → ↥(𝒜 0)` (which is bijective hence
gives an iso of `Spec`s).

The chain:
* `Proj.toSpecZero 𝒜` is proper (Mathlib's
  `Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat`, given
  `Algebra.FiniteType ↥(𝒜 0) (MvPolynomial (Fin 2) k̄)` — supplied by the
  `IsScalarTower kbar ↥(𝒜 0) (MvPolynomial _ _)` + `Algebra.FiniteType k̄ (MvPolynomial _ _)`
  chain via `Algebra.FiniteType.of_restrictScalars_finiteType`);
* `Spec.map (algebraMap k̄ ↥(𝒜 0))` is an iso because `algebraMap k̄ ↥(𝒜 0)` is bijective
  in this standard ℕ-grading case (`𝒜 0 = MvPolynomial.homogeneousSubmodule (Fin 2) k̄ 0`
  is the constants subalgebra, naturally ≅ k̄);
* composition of proper + iso is proper. -/
instance projectiveLineBar_isProper (kbar : Type u) [Field kbar] :
    IsProper (ProjectiveLineBar kbar).hom := by
  -- Unfold to expose the Proj.toSpecZero ≫ Spec.map chain.
  change IsProper (Proj.toSpecZero (projectiveLineBarGrading kbar) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap kbar ↥((projectiveLineBarGrading kbar) 0))))
  -- The IsScalarTower kbar ↥(𝒜 0) (MvPolynomial _ kbar) needed for the FiniteType derivation.
  haveI : IsScalarTower kbar
      ↥(MvPolynomial.homogeneousSubmodule (Fin 2) kbar 0)
      (MvPolynomial (Fin 2) kbar) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- MvPolynomial.{Fin 2} k̄ is finite type over ↥(𝒜 0) (chained from finite-type over k̄).
  haveI : Algebra.FiniteType
      ↥(MvPolynomial.homogeneousSubmodule (Fin 2) kbar 0)
      (MvPolynomial (Fin 2) kbar) :=
    Algebra.FiniteType.of_restrictScalars_finiteType kbar _ _
  -- The algebra map `k̄ → ↥(𝒜 0)` is bijective: the degree-`0` piece of the homogeneous
  -- decomposition is exactly the constants `C(k̄) ⊆ MvPolynomial (Fin 2) k̄`. Injectivity
  -- follows from `MvPolynomial.C_injective`. Surjectivity uses
  -- `MvPolynomial.homogeneousComponent_of_mem` (which says the degree-`0` component of a
  -- homogeneous-degree-`0` polynomial is itself) plus `homogeneousComponent_zero`
  -- (which expresses the degree-`0` component as `C` of the constant coefficient).
  have hbij : Function.Bijective (algebraMap kbar
      ↥(MvPolynomial.homogeneousSubmodule (Fin 2) kbar 0)) := by
    refine ⟨?_, ?_⟩
    · intro x y h
      apply MvPolynomial.C_injective (Fin 2) kbar
      exact congrArg Subtype.val h
    · intro ⟨v, hv⟩
      refine ⟨MvPolynomial.coeff 0 v, ?_⟩
      apply Subtype.ext
      rw [SetLike.GradeZero.coe_algebraMap]
      have key := MvPolynomial.homogeneousComponent_of_mem hv (m := 0)
      -- `key : (homogeneousComponent 0) v = if 0 = 0 then v else 0` which simp resolves
      -- and combines with `homogeneousComponent_zero` to give `C (coeff 0 v) = v`.
      simp only [MvPolynomial.homogeneousComponent_zero, if_true] at key
      exact key
  -- Therefore `Spec.map (algebraMap k̄ ↥(𝒜 0))` is iso, and composition of proper + iso is
  -- proper.
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap kbar ↥(MvPolynomial.homogeneousSubmodule (Fin 2) kbar 0)))) := by
    rw [isIso_SpecMap_iff]
    exact hbij
  infer_instance

/-! ### Project-local Mathlib supplement — MvPolynomial as standard smooth algebra

This subsection ships an axiom-clean construction of the canonical submersive
presentation of `MvPolynomial ι R` as an `R`-algebra (no relations, generators
indexed by `ι`). Mathlib does not ship a direct instance
`Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R)`
(per iter-182 prover scout); we build it here from the underlying
`Algebra.SubmersivePresentation` machinery. This is a pure
`Mathlib`-supplement: it depends only on `Mathlib`, and is independent
of the rest of the project.
-/

/-- The canonical `Generators` of `MvPolynomial α R` over `R` indexed by `α`,
with `val := MvPolynomial.X` and section `σ' := id`. -/
noncomputable def mvPolyGenerators (R : Type u) [CommRing R] (α : Type w) :
    Algebra.Generators R (MvPolynomial α R) α :=
  Algebra.Generators.ofSurjective MvPolynomial.X <|
    fun s => ⟨s, MvPolynomial.aeval_X_left_apply s⟩

/-- The canonical `Presentation` of `MvPolynomial α R` over `R` with no relations
(`σ = PEmpty`) and generators indexed by `α`. The kernel of the natural
`aeval X` map is `⊥` since `aeval X` is the identity. -/
noncomputable def mvPolyPresentation (R : Type u) [CommRing R] (α : Type w) :
    Algebra.Presentation R (MvPolynomial α R) α PEmpty.{1} where
  __ := mvPolyGenerators R α
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    simp only [Set.range_eq_empty, Ideal.span_empty]
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    change ⊥ = RingHom.ker (MvPolynomial.aeval (R := R) (MvPolynomial.X : α → MvPolynomial α R))
    rw [MvPolynomial.aeval_X_left]
    ext x
    simp [RingHom.mem_ker]

/-- The canonical `PreSubmersivePresentation` of `MvPolynomial α R` over `R`.
The differential is on the zero module `PEmpty → P.Ring`. -/
noncomputable def mvPolyPreSubmersivePresentation (R : Type u) [CommRing R]
    (α : Type w) :
    Algebra.PreSubmersivePresentation R (MvPolynomial α R) α PEmpty.{1} where
  __ := mvPolyPresentation R α
  map := PEmpty.elim
  map_inj := fun a _ _ => PEmpty.elim a

/-- The canonical `SubmersivePresentation` of `MvPolynomial α R` over `R`.
The Jacobian is the determinant of the zero-sized matrix, which is `1` (a unit). -/
noncomputable def mvPolySubmersivePresentation (R : Type u) [CommRing R]
    (α : Type w) :
    Algebra.SubmersivePresentation R (MvPolynomial α R) α PEmpty.{1} where
  __ := mvPolyPreSubmersivePresentation R α
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [Matrix.det_isEmpty]

/-- **Mathlib supplement**: `MvPolynomial (Fin n) R` is `R`-standard smooth of
relative dimension `n`. Built from `mvPolySubmersivePresentation` with
dimension `Nat.card (Fin n) - Nat.card PEmpty = n`. -/
instance mvPolynomialFin_isStandardSmoothOfRelativeDimension
    (R : Type u) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) :=
  (mvPolySubmersivePresentation R (Fin n)).isStandardSmoothOfRelativeDimension <| by
    simp [Algebra.Presentation.dimension]

/-! ### `GeometricallyIrreducible` instance -/

/-- **`ℙ¹_{k̄}` is geometrically irreducible over `Spec k̄`.** Project-side scaffold sorry
(Mathlib does not ship `GeometricallyIrreducible` for `Proj` of a polynomial ring;
plan-marked acceptable for iter-165). -/
instance projectiveLineBar_geomIrred (kbar : Type u) [Field kbar] :
    GeometricallyIrreducible (ProjectiveLineBar kbar).hom :=
  sorry

/-! ### The 2-chart affine cover of `ℙ¹_{k̄}` -/

/-- **Per-chart degree-1 homogeneity witness** for the affine cover of
`ProjectiveLineBarScheme` by `D₊(X 0)` and `D₊(X 1)`. Hoisted to top-level
out of the inline `by fin_cases i <;> simp` proof inside
`projectiveLineBarAffineCover` (per `analogies/gmscaling-cover-bridge.md`
Step 1) so the kernel doesn't `whnf` tactic-built proof closures during
downstream defeq in `gmScalingP1`. -/
noncomputable def projectiveLineBarAffineCover_fDeg
    (kbar : Type u) [Field kbar] :
    ∀ i, (![(MvPolynomial.X 0 : MvPolynomial (Fin 2) kbar), MvPolynomial.X 1]) i ∈
      projectiveLineBarGrading kbar ((![1, 1] : Fin 2 → ℕ) i) :=
  fun i => by
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
      MvPolynomial.isHomogeneous_X]

/-- **Positive-degree witness** for the affine cover indexing. Hoisted to
top-level out of the inline `by fin_cases i <;> exact Nat.one_pos` proof
inside `projectiveLineBarAffineCover` for the same defeq reasons as
`projectiveLineBarAffineCover_fDeg`. -/
lemma projectiveLineBarAffineCover_hm :
    ∀ i, 0 < (![1, 1] : Fin 2 → ℕ) i :=
  fun i => by fin_cases i <;> exact Nat.one_pos

/-- **The 2-chart affine open cover of `ProjectiveLineBarScheme`** by `D₊(X 0)` and
`D₊(X 1)`. Specialises `Proj.affineOpenCoverOfIrrelevantLESpan` to the family
`![X 0, X 1] : Fin 2 → MvPolynomial (Fin 2) k̄` with `m := ![1, 1]`.

The non-trivial bit is `hf`: the irrelevant ideal `(X 0, X 1)` is contained in
`Ideal.span {X 0, X 1}` — proved by writing any irrelevant element as a sum of monomials
whose multi-index `d ≠ 0`, hence `d j > 0` for some `j ∈ Fin 2`, hence
`monomial d r ∈ Ideal.span {X 0, X 1}` via `MvPolynomial.X_dvd_monomial`. -/
noncomputable def projectiveLineBarAffineCover (kbar : Type u) [Field kbar] :
    (ProjectiveLineBarScheme kbar).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (projectiveLineBarGrading kbar)
    (m := ![1, 1])
    (![MvPolynomial.X 0, MvPolynomial.X 1])
    (projectiveLineBarAffineCover_fDeg kbar)
    projectiveLineBarAffineCover_hm
    (by
      classical
      intro p hp
      rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff,
        GradedRing.proj_apply] at hp
      have hp' : MvPolynomial.homogeneousComponent 0 p = 0 := by
        have := hp
        rw [show DirectSum.decompose (projectiveLineBarGrading kbar) p 0
            = ⟨MvPolynomial.homogeneousComponent 0 p,
                MvPolynomial.homogeneousComponent_mem 0 p⟩ from Subtype.ext
          (MvPolynomial.decomposition.decompose'_apply p 0)] at this
        exact this
      have h0 : MvPolynomial.coeff 0 p = 0 := by
        rw [MvPolynomial.homogeneousComponent_zero] at hp'
        exact MvPolynomial.C_injective _ _ (hp'.trans MvPolynomial.C_0.symm)
      rw [MvPolynomial.as_sum p]
      refine Ideal.sum_mem _ fun d hd ↦ ?_
      have hcoeff : MvPolynomial.coeff d p ≠ 0 := MvPolynomial.mem_support_iff.mp hd
      have hd_ne : d ≠ 0 := fun heq => hcoeff (heq ▸ h0)
      have hd_nonzero : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
        by_contra h
        push Not at h
        apply hd_ne
        ext k
        fin_cases k
        · simpa using h.1
        · simpa using h.2
      rcases hd_nonzero with h0' | h1'
      · obtain ⟨q, hq⟩ : (MvPolynomial.X 0 : MvPolynomial (Fin 2) kbar) ∣
            MvPolynomial.monomial d (MvPolynomial.coeff d p) :=
          MvPolynomial.X_dvd_monomial.mpr (Or.inr h0')
        rw [hq, mul_comm]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩)
      · obtain ⟨q, hq⟩ : (MvPolynomial.X 1 : MvPolynomial (Fin 2) kbar) ∣
            MvPolynomial.monomial d (MvPolynomial.coeff d p) :=
          MvPolynomial.X_dvd_monomial.mpr (Or.inr h1')
        rw [hq, mul_comm]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, rfl⟩))

-- NOTE iter-197: relocated to AlgebraicJacobian/Genus0BaseObjects/ChartIso.lean per BareScheme smoothness-relocation refactor.

end AlgebraicGeometry

end
