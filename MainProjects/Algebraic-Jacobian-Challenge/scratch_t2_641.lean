import Mathlib
import AlgebraicJacobian.Cohomology.CechHigherDirectImageUnconditional

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

variable {S S' X X' : Scheme.{u}}

/-! ### (A) Spec-cartesian ⟹ ring-pushout (converse of `isPullback_SpecMap_of_isPushout`) -/

theorem isPushout_of_isPullback_SpecMap {A B C P : CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ C)
    (ρ : B ⟶ P) (σ : C ⟶ P)
    (H : IsPullback (Spec.map ρ) (Spec.map σ) (Spec.map φ) (Spec.map ψ)) :
    IsPushout φ ψ ρ σ := by
  have H' : IsPullback (Scheme.Spec.map ρ.op) (Scheme.Spec.map σ.op)
      (Scheme.Spec.map φ.op) (Scheme.Spec.map ψ.op) := H
  have H'' := IsPullback.of_map_of_faithful (F := Scheme.Spec) H'
  simpa using H''.unop.flip

/-! ### (B) The slice iso `pullback g' j_σ ≅ V'_σ` and the restricted top map -/

noncomputable def coverInterOpen_baseChange_sliceIso
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    (pullback g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) : Scheme.{u}) ≅
      ↑(coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) :=
  haveI hfst : IsOpenImmersion (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) :=
    isOpenImmersion_of_isPullback_left g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (restrictedCartesianAffinePushout g' 𝒰 σ)
  @IsOpenImmersion.isoOfRangeEq _ _ _
    (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
    (Scheme.Opens.ι (coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom) σ))
    hfst inferInstance
    (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι,
        coverInterOpen_baseChange_eq f g f' g' h 𝒰 σ, Scheme.Opens.opensRange_ι])

lemma coverInterOpen_baseChange_sliceIso_hom_ι
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    (coverInterOpen_baseChange_sliceIso f g f' g' h 𝒰 σ).hom ≫
        Scheme.Opens.ι (coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
          h.isoPullback.symm.hom) σ) =
      pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) := by
  unfold coverInterOpen_baseChange_sliceIso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

lemma coverInterOpen_baseChange_sliceIso_inv_fst
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    (coverInterOpen_baseChange_sliceIso f g f' g' h 𝒰 σ).inv ≫
        pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) =
      Scheme.Opens.ι (coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) := by
  rw [Iso.inv_comp_eq, ← coverInterOpen_baseChange_sliceIso_hom_ι f g f' g' h 𝒰 σ]

/-- The restriction of `g'` over the intersection open: `V'_σ ⟶ V_σ`. -/
noncomputable def coverInterOpen_baseChange_restrictedMap
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    (↑(coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) : Scheme.{u}) ⟶
      ↑(coverInterOpen 𝒰 σ) :=
  (coverInterOpen_baseChange_sliceIso f g f' g' h 𝒰 σ).inv ≫
    pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))

lemma coverInterOpen_baseChange_restrictedMap_comm
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    Scheme.Opens.ι (coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) ≫ g' =
      coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ ≫
        Scheme.Opens.ι (coverInterOpen 𝒰 σ) := by
  unfold coverInterOpen_baseChange_restrictedMap
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    coverInterOpen_baseChange_sliceIso_inv_fst f g f' g' h 𝒰 σ]

/-! ### (C) The corner ring map `ρ : Γ(V_σ) ⟶ Γ(V'_σ)` and the ring pushout square -/

section LiteralSpec

variable {R R' : CommRingCat.{u}}
variable (f : X ⟶ Spec R) (g : Spec R' ⟶ Spec R) (f' : X' ⟶ Spec R') (g' : X' ⟶ X)

/-- The corner ring map `ρ : Γ(X, V_σ) ⟶ Γ(X', V'_σ)` presenting the restricted top map
of the base-change square, conjugated by the two `isoSpec`s. -/
noncomputable def coverInterCornerRingMap
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    Γ(X, coverInterOpen 𝒰 σ) ⟶
      Γ(X', coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) :=
  Spec.preimage
    ((coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).isoSpec.inv ≫
      coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ ≫
      (coverInterOpen_isAffine f 𝒰 σ).isoSpec.hom)

lemma coverInterCornerRingMap_SpecMap
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    Spec.map (coverInterCornerRingMap f g f' g' h 𝒰 σ) =
      (coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).isoSpec.inv ≫
      coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ ≫
      (coverInterOpen_isAffine f 𝒰 σ).isoSpec.hom := by
  unfold coverInterCornerRingMap
  rw [Spec.map_preimage]

/-- The restricted base-change square over the affine intersection open, as a
pushout of rings `(φ, ψ, ρ, ψ')` with corner `Γ(X', V'_σ)`. -/
theorem coverInter_ring_isPushout
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    IsPushout (Spec.preimage ((coverInterOpen_isAffine f 𝒰 σ).fromSpec ≫ f))
      (Spec.preimage g)
      (coverInterCornerRingMap f g f' g' h 𝒰 σ)
      (Spec.preimage ((coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).fromSpec ≫ f')) := by
  apply isPushout_of_isPullback_SpecMap
  rw [Spec.map_preimage, Spec.map_preimage, Spec.map_preimage,
    coverInterCornerRingMap_SpecMap f g f' g' h 𝒰 σ]
  -- paste the restricted square onto the global cartesian square
  have H₁ : IsPullback (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) ≫ f')
      (Scheme.Opens.ι (coverInterOpen 𝒰 σ) ≫ f) g :=
    (restrictedCartesianAffinePushout g' 𝒰 σ).paste_vert h
  refine H₁.of_iso'
    ((coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).isoSpec.symm ≪≫ (coverInterOpen_baseChange_sliceIso f g f' g' h 𝒰 σ).symm)
    (coverInterOpen_isAffine f 𝒰 σ).isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · -- e₁.hom ≫ pullback.snd = (ĩ.inv ≫ restrictedMap ≫ e.hom) ≫ e.inv
    simp [coverInterOpen_baseChange_restrictedMap]
  · -- e₁.hom ≫ (pullback.fst ≫ f') = (fromSpec ≫ f') ≫ 𝟙
    have hfac := coverInterOpen_baseChange_sliceIso_inv_fst f g f' g' h 𝒰 σ
    rw [Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.comp_id, Category.assoc,
      ← Category.assoc ((coverInterOpen_baseChange_sliceIso f g f' g' h 𝒰 σ).inv),
      hfac, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc]
  · -- e₂.hom ≫ (V.ι ≫ f) = (fromSpec ≫ f) ≫ 𝟙
    rw [Iso.symm_hom, Category.comp_id, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc]
  · simp

end LiteralSpec

/-! ### (D) The tensor rewrite: `N' ≅ N ⊗_{A_σ} B` (blueprint `lem:coverinter_rhs_tensor_rewrite`) -/

section LiteralSpec2

variable {R R' : CommRingCat.{u}}
variable (f : X ⟶ Spec R) (g : Spec R' ⟶ Spec R) (f' : X' ⟶ Spec R') (g' : X' ⟶ X)

noncomputable def coverInter_baseChanged_sections_tensor_rewrite
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward (coverInterOpen_isAffine f'
            ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
            σ).isoSpec.hom).obj
          ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen
              ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
              σ))).obj
            ((Scheme.Modules.pullback g').obj F))) ≅
      (ModuleCat.extendScalars (coverInterCornerRingMap f g f' g' h 𝒰 σ).hom).obj
        (moduleSpecΓFunctor.obj
          ((Scheme.Modules.pushforward (coverInterOpen_isAffine f 𝒰 σ).isoSpec.hom).obj
            ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F))) :=
  -- notation
  letI hV := coverInterOpen_isAffine f 𝒰 σ
  letI hV' := coverInterOpen_isAffine f'
    ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom) σ
  -- the V-side restriction is `tilde N` after pushing along `isoSpec`
  letI isoA : (Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F ≅
      (Scheme.Modules.pullback hV.isoSpec.hom).obj
        (tilde (moduleSpecΓFunctor.obj
          ((Scheme.Modules.pushforward hV.isoSpec.hom).obj
            ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F)))) :=
    (pushforwardEquivOfIso hV.isoSpec).unitIso.app
        ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F) ≪≫
      (Scheme.Modules.pushforward hV.isoSpec.inv).mapIso
        (pullbackRestrict_iso_tilde F hF hV) ≪≫
      ((pullbackIsoPushforwardInv hV.isoSpec).app _).symm
  moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pushforward hV'.isoSpec.hom).mapIso
        ((Scheme.Modules.pullbackComp (Scheme.Opens.ι (coverInterOpen
              ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
              σ)) g').app F ≪≫
          (Scheme.Modules.pullbackCongr
            (coverInterOpen_baseChange_restrictedMap_comm f g f' g' h 𝒰 σ)).app F ≪≫
          ((Scheme.Modules.pullbackComp
              (coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ)
              (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).symm).app F ≪≫
          (Scheme.Modules.pullback
              (coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ)).mapIso isoA ≪≫
          (Scheme.Modules.pullbackComp
            (coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ)
            hV.isoSpec.hom).app _ ≪≫
          (Scheme.Modules.pullbackCongr (by
            rw [coverInterCornerRingMap_SpecMap f g f' g' h 𝒰 σ, Iso.hom_inv_id_assoc])).app _ ≪≫
          ((Scheme.Modules.pullbackComp hV'.isoSpec.hom
            (Spec.map (coverInterCornerRingMap f g f' g' h 𝒰 σ))).symm).app _) ≪≫
      (Scheme.Modules.pushforward hV'.isoSpec.hom).mapIso
        ((pullbackIsoPushforwardInv hV'.isoSpec).app _) ≪≫
      (Scheme.Modules.pushforwardComp hV'.isoSpec.inv hV'.isoSpec.hom).app _ ≪≫
      (Scheme.Modules.pushforwardCongr hV'.isoSpec.inv_hom_id).app _ ≪≫
      (Scheme.Modules.pushforwardId _).app _ ≪≫
      pullback_spec_tilde_iso (coverInterCornerRingMap f g f' g' h 𝒰 σ) _) ≪≫
  (tilde.toTildeΓNatIso.app
    ((ModuleCat.extendScalars (coverInterCornerRingMap f g f' g' h 𝒰 σ).hom).obj
      (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward hV.isoSpec.hom).obj
          ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F))))).symm

/-! ### (E) Literal-Spec per-intersection-open base change -/

noncomputable def pushPullObj_coverInter_baseChange_spec
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj
          (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))) ≅
      (Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pullback g').obj
          (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))) :=
  (Scheme.Modules.pullback g).mapIso
      (pushPullObj_coverInter_pushforward_iso_tilde f 𝒰 F hF σ) ≪≫
    (Scheme.Modules.pullbackCongr (Spec.map_preimage g).symm).app _ ≪≫
    affinePushforwardPullbackBaseChange
      (Spec.preimage ((coverInterOpen_isAffine f 𝒰 σ).fromSpec ≫ f))
      (Spec.preimage g)
      (coverInterCornerRingMap f g f' g' h 𝒰 σ)
      (Spec.preimage ((coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).fromSpec ≫ f'))
      (coverInter_ring_isPushout f g f' g' h 𝒰 σ)
      (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward (coverInterOpen_isAffine f 𝒰 σ).isoSpec.hom).obj
          ((Scheme.Modules.pullback (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).obj F))) ≪≫
    (Scheme.Modules.pushforward (Spec.map (Spec.preimage ((coverInterOpen_isAffine f'
        ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso h.isoPullback.symm.hom)
        σ).fromSpec ≫ f')))).mapIso
      (pullback_spec_tilde_iso (coverInterCornerRingMap f g f' g' h 𝒰 σ) _ ≪≫
        (tilde.functor _).mapIso
          (coverInter_baseChanged_sections_tensor_rewrite f g f' g' h 𝒰 F hF σ).symm) ≪≫
    (pushPullObj_coverInter_baseChanged_pushforward_iso_tilde f g f' g' h 𝒰 F hF σ).symm

end LiteralSpec2

/-! ### (F) Abstract-affine version (the line-641 target) -/

noncomputable def pushPullObj_coverInter_baseChange'
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) [IsSeparated f] [IsAffine S] [IsAffine S']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj
          (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))) ≅
      (Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pullback g').obj
          (pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))) := by
  -- transport the cartesian square to the literal-`Spec` bases along the `isoSpec`s
  have h' : IsPullback g' (f' ≫ S'.isoSpec.hom) (f ≫ S.isoSpec.hom)
      (S'.isoSpec.inv ≫ (g ≫ S.isoSpec.hom)) :=
    h.of_iso (Iso.refl _) (Iso.refl _) S'.isoSpec S.isoSpec (by simp) (by simp) (by simp)
      (by simp)
  haveI : IsSeparated f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsSeparated) h ‹_›
  haveI : IsSeparated (f ≫ S.isoSpec.hom) := inferInstance
  haveI : IsSeparated (f' ≫ S'.isoSpec.hom) := inferInstance
  haveI : ∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 (f ≫ S.isoSpec.hom)
      (S'.isoSpec.inv ≫ (g ≫ S.isoSpec.hom))).pushforwardIso h'.isoPullback.symm.hom).X i) :=
    fun i => inferInstanceAs (IsAffine (pullback (𝒰.f i ≫ (f ≫ S.isoSpec.hom))
      (S'.isoSpec.inv ≫ (g ≫ S.isoSpec.hom))))
  exact
    (pushforwardEquivOfIso S'.isoSpec).unitIso.app _ ≪≫
      (Scheme.Modules.pushforward S'.isoSpec.inv).mapIso
        (((pullbackIsoPushforwardInv S'.isoSpec.symm).app _).symm ≪≫
          (Scheme.Modules.pullback S'.isoSpec.inv).mapIso
            ((Scheme.Modules.pullback g).mapIso
              ((pushforwardEquivOfIso S.isoSpec).unitIso.app _ ≪≫
                ((pullbackIsoPushforwardInv S.isoSpec).app _).symm) ≪≫
              (Scheme.Modules.pullbackComp g S.isoSpec.hom).app _) ≪≫
          (Scheme.Modules.pullbackComp S'.isoSpec.inv (g ≫ S.isoSpec.hom)).app _ ≪≫
          (Scheme.Modules.pullback (S'.isoSpec.inv ≫ (g ≫ S.isoSpec.hom))).mapIso
            ((Scheme.Modules.pushforwardComp f S.isoSpec.hom).app _) ≪≫
          pushPullObj_coverInter_baseChange_spec (f ≫ S.isoSpec.hom)
            (S'.isoSpec.inv ≫ (g ≫ S.isoSpec.hom)) (f' ≫ S'.isoSpec.hom) g' h' 𝒰 F hF σ ≪≫
          (Scheme.Modules.pushforwardComp f' S'.isoSpec.hom).symm.app _) ≪≫
      ((pushforwardEquivOfIso S'.isoSpec).unitIso.app _).symm

end AlgebraicGeometry
