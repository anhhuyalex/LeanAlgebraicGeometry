/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.ProjectiveSpace
import AlgebraicJacobian.Picard.GlueDescent
import AlgebraicJacobian.Picard.GrassmannianQuot
import AlgebraicJacobian.Picard.TensorObjSubstrate

/-!
# The Serre twisting sheaf `O(m)` on the integral model of projective space

Mathlib v4.31 has no twisted structure sheaf on `Proj`.  This file constructs
`O(m)` on the integral model `Proj ℤ[Xᵢ : i ∈ n]` of projective space as a
`SheafOfModules`, by gluing the trivial line bundles on the basic opens
`D₊(Xᵢ)` along the transition units `(Xᵢ/Xⱼ)^m`, through the project descent
engine `AlgebraicGeometry.Scheme.Modules.glue` (`Picard/GlueDescent.lean`) —
the same pattern as the Grassmannian universal quotient
(`Picard/GrassmannianQuot.lean`), in rank one.

Main definitions:

* `ProjTwist.basicOpenCover n` — the open cover of `Proj ℤ[Xᵢ]` by the
  `D₊(Xᵢ)`;
* `ProjTwist.awayUnit n i j` — the unit `Xᵢ/Xⱼ` of the degree-zero localized
  ring `(ℤ[Xᵢ]_{XᵢXⱼ})₀`, and `ProjTwist.overlapUnit n i j` its image in
  `Γ(V(i,j), O)` on the scheme-theoretic overlap of the cover;
* `ProjTwist.twistTransition n m i j` — the rank-one transition isomorphism
  multiplication by `(Xᵢ/Xⱼ)^m`, conjugated by the structure-sheaf pullback
  comparison `Modules.pullbackUnitIso`;
* `ProjTwist.serreTwist n m` — `O(m)` on `Proj ℤ[Xᵢ : i ∈ n]`, the glued
  sheaf of modules transported along the cover isomorphism `fromGlued`.

The convention is that the transition *from* the `i`-th trivialisation *to*
the `j`-th multiplies by `(Xᵢ/Xⱼ)^m`, corresponding to the local generator
`Xᵢ^m` of `O(m)` on `D₊(Xᵢ)`.

Blueprint: `def:serre_twist`, `lem:serre_twist_transition_unit`,
`lem:serre_twist_cocycle` (`blueprint/src/chapters/Picard_QuotScheme.tex`).
-/

open CategoryTheory Limits MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.Grassmannian (scalarEnd scalarEnd_one scalarEnd_comp)

noncomputable section

namespace AlgebraicGeometry

universe u

namespace ProjTwist

variable (n : Type u)

/-- The variable `Xᵢ` is homogeneous of degree `1`. -/
lemma X_mem_deg_one (i : n) :
    (X i : MvPolynomial n (ULift.{u} ℤ)) ∈ homogeneousSubmodule n (ULift.{u} ℤ) 1 :=
  isHomogeneous_X _ _

/-- The product `XᵢXⱼ` is homogeneous of degree `2`. -/
lemma X_mul_X_mem_deg_two (i j : n) :
    (X i * X j : MvPolynomial n (ULift.{u} ℤ)) ∈
      homogeneousSubmodule n (ULift.{u} ℤ) 2 :=
  SetLike.mul_mem_graded (X_mem_deg_one n i) (X_mem_deg_one n j)

/-- The basic opens `D₊(Xᵢ)` cover `Proj ℤ[Xᵢ : i ∈ n]`: the variables
generate the coordinate ring over its degree-zero part. -/
lemma iSup_basicOpen_X_eq_top :
    ⨆ i, Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _ (fun i => ⟨1, X_mem_deg_one n i⟩) ?_
  rw [eq_top_iff]
  rintro a -
  have ha : a ∈ Algebra.adjoin (ULift.{u} ℤ)
      (Set.range (X : n → MvPolynomial n (ULift.{u} ℤ))) := by
    rw [MvPolynomial.adjoin_range_X]; trivial
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
      have hr : (algebraMap (ULift.{u} ℤ) (MvPolynomial n (ULift.{u} ℤ))) r
          ∈ homogeneousSubmodule n (ULift.{u} ℤ) 0 := by
        rw [MvPolynomial.algebraMap_eq]
        exact isHomogeneous_C _ _
      exact Subalgebra.algebraMap_mem
        (Algebra.adjoin (homogeneousSubmodule n (ULift.{u} ℤ) 0)
          (Set.range (X : n → MvPolynomial n (ULift.{u} ℤ))))
        (⟨_, hr⟩ : homogeneousSubmodule n (ULift.{u} ℤ) 0)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/-- The open cover of the integral model by the basic opens `D₊(Xᵢ)`. -/
def basicOpenCover :
    (Proj (homogeneousSubmodule n (ULift.{u} ℤ))).OpenCover where
  I₀ := n
  X i := (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i)).toScheme
  f i := (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i)).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    have : x ∈ ⨆ i, Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i) := by
      rw [iSup_basicOpen_X_eq_top]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- The glue datum of the basic-open cover of the integral model. -/
@[reducible] def glueData : Scheme.GlueData.{u} := (basicOpenCover n).gluedCover

/-- The fraction `Xᵢ/Xⱼ = Xᵢ²/(XᵢXⱼ)` as an element of the degree-zero
localized ring `(ℤ[X]_{XᵢXⱼ})₀`. -/
def awayFraction (i j : n) :
    Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j) :=
  Away.mk _ (X_mul_X_mem_deg_two n i j) 1 (X i * X i)
    (by simpa using X_mul_X_mem_deg_two n i i)

/-- The fraction `Xⱼ/Xᵢ = Xⱼ²/(XᵢXⱼ)` in the *same* localized ring
`(ℤ[X]_{XᵢXⱼ})₀` — the inverse of `awayFraction`. -/
def awayFractionInv (i j : n) :
    Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j) :=
  Away.mk _ (X_mul_X_mem_deg_two n i j) 1 (X j * X j)
    (by simpa using X_mul_X_mem_deg_two n j j)

lemma awayFraction_mul_inv (i j : n) :
    awayFraction n i j * awayFractionInv n i j = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    awayFraction, awayFractionInv, Away.val_mk, Away.val_mk, Localization.mk_mul]
  have hnum : (X i * X i) * (X j * X j)
      = ((X i * X j) ^ 1 * (X i * X j) ^ 1 : MvPolynomial n (ULift.{u} ℤ)) := by
    ring
  rw [hnum]
  exact Localization.mk_self
    ((⟨(X i * X j) ^ 1, 1, rfl⟩ :
        Submonoid.powers (X i * X j : MvPolynomial n (ULift.{u} ℤ))) *
      (⟨(X i * X j) ^ 1, 1, rfl⟩ :
        Submonoid.powers (X i * X j : MvPolynomial n (ULift.{u} ℤ))))

/-- The fraction `Xᵢ/Xⱼ` as a unit of `(ℤ[X]_{XᵢXⱼ})₀`, with inverse
`Xⱼ/Xᵢ`. -/
def awayUnit (i j : n) :
    (Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j))ˣ where
  val := awayFraction n i j
  inv := awayFractionInv n i j
  val_inv := awayFraction_mul_inv n i j
  inv_val := (mul_comm _ _).trans (awayFraction_mul_inv n i j)

/-! ## The transition units on the scheme-theoretic overlaps -/

/-- The scheme-theoretic overlap of the glue datum factors through the basic
open `D₊(XᵢXⱼ) = D₊(Xᵢ) ⊓ D₊(Xⱼ)`. -/
lemma range_overlap_le (i j : n) :
    Set.range (pullback.fst ((basicOpenCover n).f i) ((basicOpenCover n).f j) ≫
        (basicOpenCover n).f i).base ⊆
      Set.range ((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
        (X i * X j)).ι).base := by
  rw [Scheme.Opens.range_ι, Proj.basicOpen_mul]
  rintro _ ⟨v, rfl⟩
  refine ⟨?_, ?_⟩
  · have hx : ((pullback.fst _ _ ≫ (basicOpenCover n).f i) v : Proj _) ∈
        Set.range ⇑((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
          (X i)).ι) := by
      rw [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact (Scheme.Opens.range_ι _) ▸ hx
  · have hcond := congrArg (fun (φ : pullback ((basicOpenCover n).f i)
        ((basicOpenCover n).f j) ⟶ Proj (homogeneousSubmodule n (ULift.{u} ℤ))) =>
          φ.base v) pullback.condition
    simp only at hcond
    rw [hcond]
    have hx : ((pullback.snd _ _ ≫ (basicOpenCover n).f j) v : Proj _) ∈
        Set.range ⇑((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
          (X j)).ι) := by
      rw [Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    exact (Scheme.Opens.range_ι _) ▸ hx

/-- The canonical morphism from the scheme-theoretic overlap of the `i`-th and
`j`-th charts to the basic open `D₊(XᵢXⱼ)`. -/
def overlapHom (i j : n) :
    pullback ((basicOpenCover n).f i) ((basicOpenCover n).f j) ⟶
      (Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)).toScheme :=
  IsOpenImmersion.lift
    ((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)).ι)
    (pullback.fst ((basicOpenCover n).f i) ((basicOpenCover n).f j) ≫
      (basicOpenCover n).f i)
    (range_overlap_le n i j)

/-- The ring homomorphism carrying degree-zero fractions over `XᵢXⱼ` to
sections of the structure sheaf on the scheme-theoretic overlap. -/
def overlapRingHom (i j : n) :
    Away (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j) →+*
      Γ(pullback ((basicOpenCover n).f i) ((basicOpenCover n).f j), ⊤) :=
  ((overlapHom n i j).appTop.hom.comp
    ((Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ))
      (X i * X j)).topIso.inv.hom)).comp
    (Proj.awayToSection (homogeneousSubmodule n (ULift.{u} ℤ)) (X i * X j)).hom

/-- The transition unit `(Xᵢ/Xⱼ)` as a unit of the sections of the structure
sheaf on the scheme-theoretic overlap of the `i`-th and `j`-th charts. -/
def overlapUnit (i j : n) :
    Γ(pullback ((basicOpenCover n).f i) ((basicOpenCover n).f j), ⊤)ˣ :=
  Units.map (overlapRingHom n i j).toMonoidHom (awayUnit n i j)

/-! ## Rank-one transitions -/

/-- A unit of the global sections induces an automorphism of the structure
sheaf, multiplication by the unit (rank-one `matrixToFreeIso`). -/
def unitScalarIso {Y : Scheme.{u}} (v : Γ(Y, ⊤)ˣ) :
    SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf where
  hom := scalarEnd v.val
  inv := scalarEnd v.inv
  hom_inv_id := by rw [scalarEnd_comp, v.val_inv, scalarEnd_one]
  inv_hom_id := by rw [scalarEnd_comp, v.inv_val, scalarEnd_one]

@[simp]
lemma unitScalarIso_one {Y : Scheme.{u}} :
    unitScalarIso (1 : Γ(Y, ⊤)ˣ) = Iso.refl _ :=
  Iso.ext (by rw [Iso.refl_hom]; exact (congrArg scalarEnd Units.val_one).trans scalarEnd_one)

/-- Iso-level structure-sheaf-pullback cancellation: for equal base morphisms,
`pullbackUnitIso φ ≪≫ (pullbackUnitIso ψ).symm` is the `eqToIso` transport
(the rank-one analogue of `pullbackFreeIso_trans_symm_eqToIso`). -/
lemma pullbackUnitIso_trans_symm_eqToIso {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ) :
    Scheme.Modules.pullbackUnitIso φ ≪≫ (Scheme.Modules.pullbackUnitIso ψ).symm
      = eqToIso (congrArg
          (fun α => (Scheme.Modules.pullback α).obj
            (SheafOfModules.unit T.ringCatSheaf)) h) := by
  subst h; simp

/-- The fraction `Xᵢ/Xᵢ` is `1`. -/
lemma awayFraction_self (i : n) : awayFraction n i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_one, awayFraction, Away.val_mk]
  have hden : (⟨(X i * X i) ^ 1, 1, rfl⟩ :
      Submonoid.powers (X i * X i : MvPolynomial n (ULift.{u} ℤ)))
      = ⟨X i * X i, 1, pow_one _⟩ := Subtype.ext (pow_one _)
  rw [hden]
  exact Localization.mk_self_mk _ _

lemma awayUnit_self (i : n) : awayUnit n i i = 1 :=
  Units.ext (awayFraction_self n i)

lemma overlapUnit_self (i : n) : overlapUnit n i i = 1 := by
  rw [overlapUnit, awayUnit_self, map_one]

/-- The rank-one transition isomorphism of the Serre twist `O(m)`:
multiplication by `(Xᵢ/Xⱼ)^m`, conjugated by the structure-sheaf pullback
comparisons on the scheme-theoretic overlap. -/
def twistTransition (m : ℕ) (i j : n) :
    (Scheme.Modules.pullback ((glueData n).f i j)).obj
        (SheafOfModules.unit ((glueData n).U i).ringCatSheaf) ≅
      (Scheme.Modules.pullback ((glueData n).t i j ≫ (glueData n).f j i)).obj
        (SheafOfModules.unit ((glueData n).U j).ringCatSheaf) :=
  Scheme.Modules.pullbackUnitIso ((glueData n).f i j) ≪≫
    unitScalarIso ((overlapUnit n i j) ^ m) ≪≫
    (Scheme.Modules.pullbackUnitIso ((glueData n).t i j ≫ (glueData n).f j i)).symm

/-- **(C1)** The diagonal transition of the Serre twist is the canonical
cast: `Xᵢ/Xᵢ = 1`, so the scalar automorphism is the identity and the two
pullback comparisons cancel. -/
lemma twistTransition_self (m : ℕ) (i : n) :
    twistTransition n m i i
      = eqToIso (congrArg
          (fun φ => (Scheme.Modules.pullback φ).obj
            (SheafOfModules.unit ((glueData n).U i).ringCatSheaf))
          (show (glueData n).f i i = (glueData n).t i i ≫ (glueData n).f i i by
            rw [(glueData n).t_id i, Category.id_comp])) := by
  have hmid : unitScalarIso ((overlapUnit n i i) ^ m)
      = Iso.refl (SheafOfModules.unit
          (pullback ((basicOpenCover n).f i) ((basicOpenCover n).f i)).ringCatSheaf) := by
    rw [overlapUnit_self, one_pow, unitScalarIso_one]
  calc twistTransition n m i i
      = Scheme.Modules.pullbackUnitIso ((glueData n).f i i) ≪≫
          unitScalarIso ((overlapUnit n i i) ^ m) ≪≫
          (Scheme.Modules.pullbackUnitIso
            ((glueData n).t i i ≫ (glueData n).f i i)).symm := rfl
    _ = Scheme.Modules.pullbackUnitIso ((glueData n).f i i) ≪≫
          (Scheme.Modules.pullbackUnitIso
            ((glueData n).t i i ≫ (glueData n).f i i)).symm := by
        refine (congrArg (fun e =>
          Scheme.Modules.pullbackUnitIso ((glueData n).f i i) ≪≫ e ≪≫
            (Scheme.Modules.pullbackUnitIso
              ((glueData n).t i i ≫ (glueData n).f i i)).symm) hmid).trans ?_
        exact congrArg (fun e => Scheme.Modules.pullbackUnitIso ((glueData n).f i i) ≪≫ e)
          (Iso.refl_trans _)
    _ = eqToIso (congrArg
          (fun φ => (Scheme.Modules.pullback φ).obj
            (SheafOfModules.unit ((glueData n).U i).ringCatSheaf))
          (show (glueData n).f i i = (glueData n).t i i ≫ (glueData n).f i i by
            rw [(glueData n).t_id i, Category.id_comp])) :=
      pullbackUnitIso_trans_symm_eqToIso
        (show (glueData n).f i i = (glueData n).t i i ≫ (glueData n).f i i by
          rw [(glueData n).t_id i, Category.id_comp])

/-- **(C2)** The triple-overlap cocycle condition for the Serre-twist
transitions, in the exact form consumed by `Scheme.Modules.glue`.  At the
level of transition units this is the identity
`(Xᵢ/Xⱼ)^m (Xⱼ/Xₖ)^m = (Xᵢ/Xₖ)^m` in `Γ(V(i,j,k), O)`; the remaining work is
transporting the conjugated scalar isomorphisms to the triple overlap through
the `pullbackUnitIso` coherences (the rank-one analogue of
`bundleTransition_cocycle_transport`, `GrassmannianQuot.lean`). -/
lemma twistTransition_cocycle (m : ℕ) (i j k : n) :
    Scheme.Modules.pullbackBaseChangeTransport
        (pullback.fst ((glueData n).f i j) ((glueData n).f i k)) ((glueData n).f i j)
        ((glueData n).t i j ≫ (glueData n).f j i) (twistTransition n m i j) ≪≫
      (Scheme.Modules.pullbackCongr
        (Scheme.Modules.glueData_bridge_mid (glueData n) i j k)).app
          (SheafOfModules.unit ((glueData n).U j).ringCatSheaf) ≪≫
      Scheme.Modules.pullbackBaseChangeTransport
        ((glueData n).t' i j k ≫ pullback.fst ((glueData n).f j k) ((glueData n).f j i))
        ((glueData n).f j k) ((glueData n).t j k ≫ (glueData n).f k j)
        (twistTransition n m j k) ≪≫
      (Scheme.Modules.pullbackCongr
        (Scheme.Modules.glueData_bridge_tgt (glueData n) i j k)).app
          (SheafOfModules.unit ((glueData n).U k).ringCatSheaf)
    = (Scheme.Modules.pullbackCongr
        (Scheme.Modules.glueData_bridge_src (glueData n) i j k)).app
          (SheafOfModules.unit ((glueData n).U i).ringCatSheaf) ≪≫
      Scheme.Modules.pullbackBaseChangeTransport
        (pullback.snd ((glueData n).f i j) ((glueData n).f i k)) ((glueData n).f i k)
        ((glueData n).t i k ≫ (glueData n).f k i) (twistTransition n m i k) := by
  sorry

/-! ## The Serre twisting sheaf

The descent engine `Scheme.Modules.glue` (`Picard/GlueDescent.lean`) is
universe-monomorphic at `Scheme.GlueData.{0}` (see the NOTE at
`GlueDescent.lean:934`), so the glued sheaf itself is only available for a
`Type 0` index — which covers the intended consumers `n = Fin (m + 1)`
(`ℙ^m`).  The cover, units and transitions above stay universe-polymorphic
for a future generalisation of the engine. -/

section Universe0

variable (n₀ : Type)

/-- The Serre twist `O(m)` on the glued total space of the basic-open cover. -/
def serreTwistGlued (m : ℕ) : (glueData n₀).glued.Modules :=
  Scheme.Modules.glue (glueData n₀)
    (fun i => SheafOfModules.unit ((glueData n₀).U i).ringCatSheaf)
    (fun i j => twistTransition n₀ m i j)
    (fun i => twistTransition_self n₀ m i)
    (fun i j k => twistTransition_cocycle n₀ m i j k)

/-- **The Serre twisting sheaf `O(m)`** on the integral model
`Proj ℤ[Xᵢ : i ∈ n₀]` of projective space: the glued sheaf transported along
the canonical isomorphism `fromGlued`. -/
def serreTwist (m : ℕ) :
    (Proj (homogeneousSubmodule n₀ (ULift.{0} ℤ))).Modules :=
  (Scheme.Modules.pullback (inv (basicOpenCover n₀).fromGlued)).obj
    (serreTwistGlued n₀ m)

end Universe0

end ProjTwist

end AlgebraicGeometry
