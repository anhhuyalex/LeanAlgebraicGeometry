/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.GlueDescent
import AlgebraicJacobian.Picard.SerreTwist

/-!
# Global sections of a glued sheaf of modules

The descent engine `AlgebraicGeometry.Scheme.Modules.glue` (`Picard/GlueDescent.lean`)
builds the glued sheaf as an equalizer of pushforward products,
`glue D M g ≅ equalizer (∏ᵢ (ιᵢ)_* Mᵢ ⇉ ∏_{ij} (j_ij)_* (f_ij^* Mᵢ))`
(`glueIsoEqualizer`, literally `Iso.refl`).  This file computes the **global
sections** of the glued sheaf from this presentation: evaluation at the maximal
open `⊤` preserves limits (`SheafOfModules.evaluation` and the limit machinery of
sheaves of modules), so `Γ(glue D M g, ⊤)` is the equalizer *of
`Γ(𝒪)`-modules* of the two section-level descent legs — concretely, the submodule
of **compatible families** `(sᵢ)ᵢ ∈ ∏ᵢ Γ(Uᵢ, Mᵢ)` whose two overlap restrictions
agree through the transition isomorphisms `g`.

Main definitions and results:

* `Scheme.Modules.gammaTop` — the global-sections functor `Γ(-, ⊤)` on
  `X.Modules`, as evaluation of sheaves of modules at `⊤`;
* `Scheme.Modules.gammaPiHom`, `gammaPiHom_apply`, `gamma_pi_ext`,
  `gamma_pi_surjective` — global sections of a categorical product of sheaves of
  modules form the product of the global sections, with components the
  projections `(Pi.π N i).app ⊤`;
* `Scheme.Modules.glueLegAComponent` / `glueLegBComponent` — the
  `(i,j)`-components of the two descent legs of `glue` (re-exposed from the
  `Pi.lift` bodies of `glueLegA`/`glueLegB`);
* `Scheme.Modules.glueGammaCompatible` — the `Γ(𝒪)`-submodule of compatible
  families `{ s : ∀ i, Γ((ιᵢ)_* Mᵢ, ⊤) // aᵢⱼ(s i) = bᵢⱼ(s j) }`;
* `Scheme.Modules.glueSectionsEquiv` — **the glued-section equivalence**
  `Γ(glue D M g, ⊤) ≃ₗ[Γ(𝒪)] glueGammaCompatible D M g`, with forward map the
  chart projections `(glueProj i).app ⊤` (`glueSectionsEquiv_apply_coe`) and
  inverse the unique glued section of a compatible family
  (`glueProj_app_glueSectionsEquiv_symm`);
* `Scheme.Modules.glue_sections_ext` — global sections of the glued sheaf are
  jointly detected by the chart projections.

Blueprint: `def:glue_gamma_compatible`, `lem:glue_sections_equalizer`
(`blueprint/src/chapters/Picard_QuotScheme.tex`, `sec:projective_vocabulary`).
-/

universe u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-! ## The global-sections functor at `⊤` -/

/-- The global-sections functor `Γ(-, ⊤)` on sheaves of modules over a scheme:
evaluation of `SheafOfModules` at the maximal open.  It preserves all (small)
limits by the sheaf-of-modules limit machinery, which is the engine behind the
computation of `Γ(glue …, ⊤)` below. -/
abbrev gammaTop (X : Scheme.{0}) :
    X.Modules ⥤ ModuleCat.{0} (X.ringCatSheaf.obj.obj (op ⊤)) :=
  SheafOfModules.evaluation _ (op ⊤)

/-- `Γ(-, ⊤)` preserves (small) limits of sheaves of modules.  Restated for the
`X.Modules`-instance path so that the comparison-isomorphism instances fire on
the descent-equalizer presentation of the glued sheaf. -/
instance gammaTop_preservesLimits (X : Scheme.{0}) :
    PreservesLimitsOfSize.{0, 0} (gammaTop X) :=
  inferInstanceAs (PreservesLimitsOfSize.{0, 0}
    (SheafOfModules.evaluation (R := X.ringCatSheaf) (op ⊤)))

/-- Element-level bridge: the action of `gammaTop` on a morphism of sheaves of
modules is the action on sections `Hom.app ⊤`. -/
lemma gammaTop_map_apply {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    (gammaTop X).map φ x = φ.app ⊤ x := rfl

/-- Global sections of a pushforward at the maximal open are the global sections
of the original sheaf of modules, definitionally. -/
lemma gamma_pushforward_top {X Y : Scheme.{0}} (f : X ⟶ Y) (M : X.Modules) :
    Γ((Scheme.Modules.pushforward f).obj M, ⊤) = Γ(M, ⊤) := rfl

/-- Global sections of the unit sheaf of modules are the structure-sheaf
sections, definitionally.  This identifies the chart-section spaces of the
compatible families of a rank-one descent datum (such as the Serre twist)
with the structure-sheaf sections of the charts. -/
lemma gamma_unit_top (X : Scheme.{0}) :
    (Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) : Type) = (Γ(X, ⊤) : Type) := rfl

/-- Equal morphisms of sheaves of modules act equally on global sections. -/
lemma app_top_congr {X : Scheme.{0}} {A B : X.Modules} {φ ψ : A ⟶ B} (h : φ = ψ)
    (x : Γ(A, ⊤)) : φ.app ⊤ x = ψ.app ⊤ x := by rw [h]

/-- Composition of morphisms of sheaves of modules acts on global sections by
composition of the section maps. -/
lemma comp_app_top_apply {X : Scheme.{0}} {A B C : X.Modules} (φ : A ⟶ B) (ψ : B ⟶ C)
    (x : Γ(A, ⊤)) : (φ ≫ ψ).app ⊤ x = ψ.app ⊤ (φ.app ⊤ x) := rfl

/-! ## Global sections of a product of sheaves of modules -/

section GammaPi

variable {X : Scheme.{0}} {ι : Type} (N : ι → X.Modules)

/-- The comparison from the global sections of a categorical product of sheaves
of modules to the product of the global sections: the limit-preservation
comparison of `gammaTop` followed by the concrete product identification of
`ModuleCat`. -/
def gammaPiHom :
    (gammaTop X).obj (∏ᶜ N) ⟶
      ModuleCat.of _ (∀ i, ((gammaTop X).obj (N i) : Type)) :=
  piComparison (gammaTop X) N ≫ (ModuleCat.piIsoPi fun i => (gammaTop X).obj (N i)).hom

instance : IsIso (gammaPiHom N) := by
  dsimp only [gammaPiHom]
  infer_instance

/-- The components of the product comparison are the section-level product
projections. -/
lemma gammaPiHom_apply (x : Γ(∏ᶜ N, ⊤)) (i : ι) :
    gammaPiHom N x i = (Pi.π N i).app ⊤ x :=
  calc gammaPiHom N x i
      = ((ModuleCat.piIsoPi fun i => (gammaTop X).obj (N i)).hom
          (piComparison (gammaTop X) N x)) i := rfl
    _ = Pi.π (fun i => (gammaTop X).obj (N i)) i (piComparison (gammaTop X) N x) :=
        congr(($(ModuleCat.piIsoPi_hom_ker_subtype
          (fun i => (gammaTop X).obj (N i)) i)) (piComparison (gammaTop X) N x))
    _ = (gammaTop X).map (Pi.π N i) x :=
        congr(($(piComparison_comp_π (gammaTop X) N i)) x)
    _ = (Pi.π N i).app ⊤ x := rfl

/-- Global sections of a product of sheaves of modules are jointly detected by
the product projections. -/
lemma gamma_pi_ext {x y : Γ(∏ᶜ N, ⊤)}
    (h : ∀ i, (Pi.π N i).app ⊤ x = (Pi.π N i).app ⊤ y) : x = y := by
  have hinj : Function.Injective (gammaPiHom N) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hinj
  funext i
  rw [gammaPiHom_apply, gammaPiHom_apply]
  exact h i

/-- Every family of sections of the factors is the family of projections of a
global section of the product. -/
lemma gamma_pi_surjective (s : ∀ i, Γ(N i, ⊤)) :
    ∃ x : Γ(∏ᶜ N, ⊤), ∀ i, (Pi.π N i).app ⊤ x = s i := by
  refine ⟨inv (gammaPiHom N) s, fun i => ?_⟩
  have hsec : gammaPiHom N (inv (gammaPiHom N) s) = s :=
    congr(($(IsIso.inv_hom_id (gammaPiHom N))) s)
  rw [← gammaPiHom_apply, hsec]

end GammaPi

/-! ## Lifting an element through an equalizer of modules -/

/-- An element on which two parallel maps of modules agree lifts through their
categorical equalizer: probe the equalizer with the free rank-one module via
`LinearMap.toSpanSingleton` and evaluate the lift at `1`. -/
private lemma moduleCat_equalizer_element_lift {R : RingCat.{0}} {A B : ModuleCat.{0} R}
    (f g : A ⟶ B) (x : A) (hx : f x = g x) :
    ∃ z : (equalizer f g : ModuleCat.{0} R), equalizer.ι f g z = x := by
  have hcond : ModuleCat.ofHom (LinearMap.toSpanSingleton R A x) ≫ f
      = ModuleCat.ofHom (LinearMap.toSpanSingleton R A x) ≫ g := by
    ext : 1
    apply LinearMap.ext_ring
    change f (LinearMap.toSpanSingleton (R : Type) (A : Type) x (1 : R))
      = g (LinearMap.toSpanSingleton (R : Type) (A : Type) x (1 : R))
    have h1 : LinearMap.toSpanSingleton (R : Type) (A : Type) x (1 : R) = x :=
      one_smul _ x
    rw [h1]
    exact hx
  refine ⟨equalizer.lift (ModuleCat.ofHom (LinearMap.toSpanSingleton R A x)) hcond
    (1 : R), ?_⟩
  have h4 := congr(($(equalizer.lift_ι
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R A x)) hcond)) (1 : R))
  exact h4.trans (one_smul _ x)

/-! ## The two descent legs, componentwise -/

section GlueSections

variable (D : Scheme.GlueData.{0}) (M : ∀ i, (D.U i).Modules)

/-- The `(i,j)`-component of the first descent leg of `glue`: restrict the
`i`-th chart section to the overlap `V (i,j)` via the unit of the
pullback–pushforward adjunction along `f_ij` and the pushforward-composition
comparison.  Re-exposes the `Pi.lift` body of `glueLegA`. -/
def glueLegAComponent (p : D.J × D.J) :
    (Scheme.Modules.pushforward (D.ι p.1)).obj (M p.1) ⟶
      (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
        ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)) :=
  (Scheme.Modules.pushforward (D.ι p.1)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p.1 p.2)).unit.app (M p.1)) ≫
    (Scheme.Modules.pushforwardComp (D.f p.1 p.2) (D.ι p.1)).hom.app
      ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))

/-- The `(i,j)`-component of the second descent leg of `glue`: restrict the
`j`-th chart section, transport it across the transition isomorphism `g_ij`,
and reindex the immersion via the glue condition.  Re-exposes the `Pi.lift`
body of `glueLegB`. -/
def glueLegBComponent
    (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) (p : D.J × D.J) :
    (Scheme.Modules.pushforward (D.ι p.2)).obj (M p.2) ⟶
      (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
        ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)) :=
  (Scheme.Modules.pushforward (D.ι p.2)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
    (Scheme.Modules.pushforwardComp (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
      ((Scheme.Modules.pullback (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
    (Scheme.Modules.pushforward
      ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map (g p.1 p.2).inv ≫
    (Scheme.Modules.pushforwardCongr
      (show (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 = D.f p.1 p.2 ≫ D.ι p.1 by
        rw [Category.assoc]; exact D.glue_condition p.1 p.2)).hom.app
      ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))

set_option backward.isDefEq.respectTransparency false in
/-- The first descent leg followed by the `p`-th overlap projection is the
`p.1`-th chart projection followed by the leg component. -/
lemma glueLegA_π (p : D.J × D.J) :
    glueLegA D M ≫
        Pi.π (fun p : D.J × D.J =>
          (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p
      = Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.1 ≫
          glueLegAComponent D M p :=
  Limits.Pi.lift_π _ _

set_option backward.isDefEq.respectTransparency false in
/-- The second descent leg followed by the `p`-th overlap projection is the
`p.2`-th chart projection followed by the leg component. -/
lemma glueLegB_π
    (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) (p : D.J × D.J) :
    glueLegB D M g ≫
        Pi.π (fun p : D.J × D.J =>
          (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p
      = Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.2 ≫
          glueLegBComponent D M g p :=
  Limits.Pi.lift_π _ _

variable (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
      (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))

/-! ## The compatible-families submodule -/

/-- **The compatible families of chart sections** (`def:glue_gamma_compatible`):
the `Γ(𝒪)`-submodule of `∏ᵢ Γ((ιᵢ)_* Mᵢ, ⊤)` of families whose two overlap
restrictions agree through the transition isomorphisms: for every pair `(i,j)`,
the `i`-th section restricted to the overlap `V (i,j)` equals the `j`-th section
restricted and transported across `g i j`.  By `glueSectionsEquiv` below this is
exactly the image of the global sections of the glued sheaf.  Note that
`Γ((ιᵢ)_* Mᵢ, ⊤) = Γ(Mᵢ, ⊤)` definitionally (`gamma_pushforward_top`). -/
def glueGammaCompatible : Submodule Γ(D.glued, ⊤)
    (∀ i, Γ((Scheme.Modules.pushforward (D.ι i)).obj (M i), ⊤)) where
  carrier := { s | ∀ p : D.J × D.J,
    (glueLegAComponent D M p).app ⊤ (s p.1) = (glueLegBComponent D M g p).app ⊤ (s p.2) }
  add_mem' := by
    intro s t hs ht p
    simp only [Pi.add_apply, map_add]
    rw [hs p, ht p]
  zero_mem' := by
    intro p
    simp only [Pi.zero_apply, map_zero]
  smul_mem' := by
    intro r s hs p
    simp only [Pi.smul_apply, Hom.app_smul]
    rw [hs p]

lemma mem_glueGammaCompatible_iff
    (s : ∀ i, Γ((Scheme.Modules.pushforward (D.ι i)).obj (M i), ⊤)) :
    s ∈ glueGammaCompatible D M g ↔ ∀ p : D.J × D.J,
      (glueLegAComponent D M p).app ⊤ (s p.1)
        = (glueLegBComponent D M g p).app ⊤ (s p.2) :=
  Iff.rfl

variable (hC1 : ∀ i, g i i = eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj (M i))
      (show D.f i i = D.t i i ≫ D.f i i by rw [D.t_id i, Category.id_comp])))
  (hC2 : ∀ i j k,
      pullbackBaseChangeTransport (pullback.fst (D.f i j) (D.f i k))
          (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
        (Scheme.Modules.pullbackCongr (glueData_bridge_mid D i j k)).app (M j) ≪≫
        pullbackBaseChangeTransport (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
          (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
        (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i j k)).app (M k)
      = (Scheme.Modules.pullbackCongr (glueData_bridge_src D i j k)).app (M i) ≪≫
        pullbackBaseChangeTransport (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i) (g i k))

/-! ## Projections of a glued section are compatible -/

set_option backward.isDefEq.respectTransparency false in
/-- The chart projections of the glued sheaf satisfy the descent-leg
compatibility, morphism-level: `glueProj p.1 ≫ a_p = glueProj p.2 ≫ b_p`.
This is the `p`-th component of the equalizer condition. -/
lemma glueProj_leg_compat (p : D.J × D.J) :
    glueProj D M g hC1 hC2 p.1 ≫ glueLegAComponent D M p
      = glueProj D M g hC1 hC2 p.2 ≫ glueLegBComponent D M g p := by
  have hcond : equalizer.ι (glueLegA D M) (glueLegB D M g) ≫ glueLegA D M
      = equalizer.ι (glueLegA D M) (glueLegB D M g) ≫ glueLegB D M g :=
    equalizer.condition _ _
  calc glueProj D M g hC1 hC2 p.1 ≫ glueLegAComponent D M p
      = (glueIsoEqualizer D M g hC1 hC2).hom ≫
          equalizer.ι (glueLegA D M) (glueLegB D M g) ≫
          (Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.1 ≫
            glueLegAComponent D M p) := by
        simp only [glueProj, Category.assoc]
    _ = (glueIsoEqualizer D M g hC1 hC2).hom ≫
          equalizer.ι (glueLegA D M) (glueLegB D M g) ≫
          (glueLegA D M ≫
            Pi.π (fun p : D.J × D.J =>
              (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
                ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p) :=
        congrArg (fun z => (glueIsoEqualizer D M g hC1 hC2).hom ≫
          equalizer.ι (glueLegA D M) (glueLegB D M g) ≫ z) (glueLegA_π D M p).symm
    _ = (glueIsoEqualizer D M g hC1 hC2).hom ≫
          (equalizer.ι (glueLegA D M) (glueLegB D M g) ≫ glueLegA D M) ≫
          Pi.π (fun p : D.J × D.J =>
            (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
              ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p := by
        simp only [Category.assoc]
    _ = (glueIsoEqualizer D M g hC1 hC2).hom ≫
          (equalizer.ι (glueLegA D M) (glueLegB D M g) ≫ glueLegB D M g) ≫
          Pi.π (fun p : D.J × D.J =>
            (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
              ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p :=
        congrArg (fun z => (glueIsoEqualizer D M g hC1 hC2).hom ≫ z ≫
          Pi.π (fun p : D.J × D.J =>
            (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
              ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p) hcond
    _ = (glueIsoEqualizer D M g hC1 hC2).hom ≫
          equalizer.ι (glueLegA D M) (glueLegB D M g) ≫
          (glueLegB D M g ≫
            Pi.π (fun p : D.J × D.J =>
              (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
                ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p) := by
        simp only [Category.assoc]
    _ = (glueIsoEqualizer D M g hC1 hC2).hom ≫
          equalizer.ι (glueLegA D M) (glueLegB D M g) ≫
          (Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.2 ≫
            glueLegBComponent D M g p) :=
        congrArg (fun z => (glueIsoEqualizer D M g hC1 hC2).hom ≫
          equalizer.ι (glueLegA D M) (glueLegB D M g) ≫ z) (glueLegB_π D M g p)
    _ = glueProj D M g hC1 hC2 p.2 ≫ glueLegBComponent D M g p := by
        simp only [glueProj, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The family of chart projections of a global section of the glued sheaf is
compatible. -/
lemma glueProj_app_mem_glueGammaCompatible (w : Γ(glue D M g hC1 hC2, ⊤)) :
    (fun i => (glueProj D M g hC1 hC2 i).app ⊤ w) ∈ glueGammaCompatible D M g := by
  intro p
  have h1 := app_top_congr (glueProj_leg_compat D M g hC1 hC2 p) w
  rw [comp_app_top_apply, comp_app_top_apply] at h1
  exact h1

/-! ## The glued-section equivalence -/

/-- The section-level chart-projection map, as a `Γ(𝒪)`-linear map. -/
def glueSectionsHom :
    Γ(glue D M g hC1 hC2, ⊤) →ₗ[Γ(D.glued, ⊤)]
      ∀ i, Γ((Scheme.Modules.pushforward (D.ι i)).obj (M i), ⊤) where
  toFun w i := (glueProj D M g hC1 hC2 i).app ⊤ w
  map_add' w w' := by
    funext i
    simp only [map_add, Pi.add_apply]
  map_smul' r w := by
    funext i
    simp only [Hom.app_smul, RingHom.id_apply, Pi.smul_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The chart projection factored through the descent-equalizer inclusion. -/
lemma glueProj_app_factor (v : Γ(glue D M g hC1 hC2, ⊤)) (i : D.J) :
    (glueProj D M g hC1 hC2 i).app ⊤ v
      = (Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i).app ⊤
          (((glueIsoEqualizer D M g hC1 hC2).hom ≫
            equalizer.ι (glueLegA D M) (glueLegB D M g)).app ⊤ v) := by
  -- the composite-application form is definitionally the nested application, so
  -- the factorisation is `app_top_congr` of the associativity regrouping
  have h : glueProj D M g hC1 hC2 i
      = ((glueIsoEqualizer D M g hC1 hC2).hom ≫
          equalizer.ι (glueLegA D M) (glueLegB D M g)) ≫
          Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i := by
    simp only [glueProj, Category.assoc]
  exact app_top_congr h v

set_option backward.isDefEq.respectTransparency false in
/-- Global sections of the glued sheaf are jointly detected by the chart
projections. -/
lemma glue_sections_ext {w w' : Γ(glue D M g hC1 hC2, ⊤)}
    (h : ∀ i, (glueProj D M g hC1 hC2 i).app ⊤ w = (glueProj D M g hC1 hC2 i).app ⊤ w') :
    w = w' := by
  have hmono : Mono ((gammaTop D.glued).map ((glueIsoEqualizer D M g hC1 hC2).hom ≫
      equalizer.ι (glueLegA D M) (glueLegB D M g))) := by
    rw [Functor.map_comp]
    have h2 : Mono ((gammaTop D.glued).map
        (equalizer.ι (glueLegA D M) (glueLegB D M g))) := by
      rw [← equalizerComparison_comp_π]
      exact mono_comp _ _
    exact mono_comp _ _
  have hinj : Function.Injective ((gammaTop D.glued).map
      ((glueIsoEqualizer D M g hC1 hC2).hom ≫
        equalizer.ι (glueLegA D M) (glueLegB D M g))) :=
    (ModuleCat.mono_iff_injective _).mp hmono
  have hinj' : Function.Injective (fun v : Γ(glue D M g hC1 hC2, ⊤) =>
      ((glueIsoEqualizer D M g hC1 hC2).hom ≫
        equalizer.ι (glueLegA D M) (glueLegB D M g)).app ⊤ v) := hinj
  apply hinj'
  apply gamma_pi_ext
  intro i
  exact (glueProj_app_factor D M g hC1 hC2 w i).symm.trans
    ((h i).trans (glueProj_app_factor D M g hC1 hC2 w' i))

set_option backward.isDefEq.respectTransparency false in
/-- Every compatible family of chart sections arises from a global section of
the glued sheaf: the section-level equalizer lift. -/
lemma glueSectionsHom_surjOn (s : ∀ i, Γ((Scheme.Modules.pushforward (D.ι i)).obj (M i), ⊤))
    (hs : s ∈ glueGammaCompatible D M g) :
    ∃ w : Γ(glue D M g hC1 hC2, ⊤), ∀ i, (glueProj D M g hC1 hC2 i).app ⊤ w = s i := by
  -- a product section with the prescribed projections
  obtain ⟨x₀, hx₀⟩ := gamma_pi_surjective
    (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) s
  -- the two descent legs agree on it
  have hEq : (glueLegA D M).app ⊤ x₀ = (glueLegB D M g).app ⊤ x₀ := by
    apply gamma_pi_ext
    intro p
    calc (Pi.π (fun p : D.J × D.J =>
            (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
              ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p).app ⊤
          ((glueLegA D M).app ⊤ x₀)
        = (glueLegA D M ≫ Pi.π (fun p : D.J × D.J =>
            (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
              ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p).app ⊤ x₀ :=
          (comp_app_top_apply _ _ _).symm
      _ = (Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.1 ≫
            glueLegAComponent D M p).app ⊤ x₀ :=
          app_top_congr (glueLegA_π D M p) x₀
      _ = (glueLegAComponent D M p).app ⊤
            ((Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.1).app ⊤ x₀) :=
          comp_app_top_apply _ _ _
      _ = (glueLegAComponent D M p).app ⊤ (s p.1) :=
          congrArg (fun z => (glueLegAComponent D M p).app ⊤ z) (hx₀ p.1)
      _ = (glueLegBComponent D M g p).app ⊤ (s p.2) := hs p
      _ = (glueLegBComponent D M g p).app ⊤
            ((Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.2).app ⊤ x₀) :=
          congrArg (fun z => (glueLegBComponent D M g p).app ⊤ z) (hx₀ p.2).symm
      _ = (Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.2 ≫
            glueLegBComponent D M g p).app ⊤ x₀ :=
          (comp_app_top_apply _ _ _).symm
      _ = (glueLegB D M g ≫ Pi.π (fun p : D.J × D.J =>
            (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
              ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p).app ⊤ x₀ :=
          app_top_congr (glueLegB_π D M g p).symm x₀
      _ = (Pi.π (fun p : D.J × D.J =>
            (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
              ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) p).app ⊤
            ((glueLegB D M g).app ⊤ x₀) :=
          comp_app_top_apply _ _ _
  -- lift through the section-level equalizer of the evaluated legs
  obtain ⟨z, hz⟩ := moduleCat_equalizer_element_lift
    ((gammaTop D.glued).map (glueLegA D M)) ((gammaTop D.glued).map (glueLegB D M g))
    x₀ hEq
  set c := equalizerComparison (glueLegA D M) (glueLegB D M g) (gammaTop D.glued) with hc
  refine ⟨(glueIsoEqualizer D M g hC1 hC2).inv.app ⊤ (inv c z), fun i => ?_⟩
  -- the equalizer inclusion of the lifted point is `x₀`
  have hι : (equalizer.ι (glueLegA D M) (glueLegB D M g)).app ⊤ (inv c z) = x₀ := by
    have h2 : inv c ≫ (gammaTop D.glued).map
          (equalizer.ι (glueLegA D M) (glueLegB D M g))
        = equalizer.ι ((gammaTop D.glued).map (glueLegA D M))
            ((gammaTop D.glued).map (glueLegB D M g)) := by
      rw [IsIso.inv_comp_eq]
      exact (equalizerComparison_comp_π _ _ _).symm
    exact (congr(($(h2)) z)).trans hz
  -- unfold the projection through the equalizer inclusion
  have hfac : (glueIsoEqualizer D M g hC1 hC2).inv ≫ glueProj D M g hC1 hC2 i
      = equalizer.ι (glueLegA D M) (glueLegB D M g) ≫
          Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i := by
    rw [glueProj, Iso.inv_hom_id_assoc]
  calc (glueProj D M g hC1 hC2 i).app ⊤
        ((glueIsoEqualizer D M g hC1 hC2).inv.app ⊤ (inv c z))
      = ((glueIsoEqualizer D M g hC1 hC2).inv ≫ glueProj D M g hC1 hC2 i).app ⊤
          (inv c z) := (comp_app_top_apply _ _ _).symm
    _ = (equalizer.ι (glueLegA D M) (glueLegB D M g) ≫
          Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i).app ⊤
          (inv c z) := app_top_congr hfac _
    _ = (Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i).app ⊤
          ((equalizer.ι (glueLegA D M) (glueLegB D M g)).app ⊤ (inv c z)) :=
        comp_app_top_apply _ _ _
    _ = (Pi.π (fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i).app ⊤ x₀ :=
        congrArg (fun z => (Pi.π (fun i =>
          (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i).app ⊤ z) hι
    _ = s i := hx₀ i

/-- **Global sections of the glued sheaf are the compatible families**
(`lem:glue_sections_equalizer`).  The `Γ(𝒪)`-linear equivalence between the
global sections of `glue D M g` and the submodule of compatible families of
chart sections, with forward map the chart projections `(glueProj i).app ⊤`.
This is the section-level form of the descent-equalizer presentation
`glueIsoEqualizer`: `Γ(-, ⊤)` preserves the equalizer of pushforward products,
and `Γ` of a pushforward at `⊤` is `Γ` of the original sheaf. -/
def glueSectionsEquiv :
    Γ(glue D M g hC1 hC2, ⊤) ≃ₗ[Γ(D.glued, ⊤)] glueGammaCompatible D M g :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (glueGammaCompatible D M g) (glueSectionsHom D M g hC1 hC2)
      (glueProj_app_mem_glueGammaCompatible D M g hC1 hC2))
    ⟨fun w w' h => glue_sections_ext D M g hC1 hC2
        (fun i => congrFun (congrArg Subtype.val h) i),
      fun s => by
        obtain ⟨w, hw⟩ := glueSectionsHom_surjOn D M g hC1 hC2 s.val s.property
        exact ⟨w, Subtype.ext (funext hw)⟩⟩

@[simp]
lemma glueSectionsEquiv_apply_coe (w : Γ(glue D M g hC1 hC2, ⊤)) (i : D.J) :
    (glueSectionsEquiv D M g hC1 hC2 w : ∀ i,
        Γ((Scheme.Modules.pushforward (D.ι i)).obj (M i), ⊤)) i
      = (glueProj D M g hC1 hC2 i).app ⊤ w := rfl

/-- The inverse of the glued-section equivalence produces the unique global
section with the prescribed chart projections. -/
lemma glueProj_app_glueSectionsEquiv_symm (s : glueGammaCompatible D M g) (i : D.J) :
    (glueProj D M g hC1 hC2 i).app ⊤ ((glueSectionsEquiv D M g hC1 hC2).symm s)
      = (s : ∀ i, Γ((Scheme.Modules.pushforward (D.ι i)).obj (M i), ⊤)) i := by
  have h := (glueSectionsEquiv D M g hC1 hC2).apply_symm_apply s
  have h' := congrFun (congrArg Subtype.val h) i
  rw [← h']
  rfl

end GlueSections

/-! ## Pullback along an isomorphism is pushforward of the inverse -/

/-- For an isomorphism of schemes `φ`, the two pushforwards of sheaves of
modules form an (adjoint) equivalence, via the pushforward pseudofunctor
coherences. -/
def pushforwardEquivalenceOfIso {X Y : Scheme.{0}} (φ : X ⟶ Y) [IsIso φ] :
    Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward (inv φ))
    (Scheme.Modules.pushforward φ)
    ((Scheme.Modules.pushforwardId Y).symm ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id φ).symm ≪≫
      (Scheme.Modules.pushforwardComp (inv φ) φ).symm)
    (Scheme.Modules.pushforwardComp φ (inv φ) ≪≫
      Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id φ) ≪≫
      Scheme.Modules.pushforwardId X)

/-- **Pullback along an isomorphism of schemes is pushforward of the inverse**:
both are left adjoint to the pushforward along the isomorphism.  This converts
the pullback transport of a glued sheaf along `fromGlued` into a pushforward,
whose global sections are definitionally those of the original sheaf. -/
def pullbackIsoPushforwardInv {X Y : Scheme.{0}} (φ : X ⟶ Y) [IsIso φ] :
    Scheme.Modules.pullback φ ≅ Scheme.Modules.pushforward (inv φ) :=
  Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction φ)
    (pushforwardEquivalenceOfIso φ).toAdjunction

/-- The `Γ(-, ⊤)` additive equivalence induced by an isomorphism of sheaves of
modules. -/
def gammaAddEquivOfIso {X : Scheme.{0}} {A B : X.Modules} (e : A ≅ B) :
    Γ(A, ⊤) ≃+ Γ(B, ⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  left_inv x :=
    (comp_app_top_apply e.hom e.inv x).symm.trans (app_top_congr e.hom_inv_id x)
  right_inv y :=
    (comp_app_top_apply e.inv e.hom y).symm.trans (app_top_congr e.inv_hom_id y)
  map_add' x y := map_add _ x y

end AlgebraicGeometry.Scheme.Modules

/-! ## Global sections of the Serre twist over the basic-open cover

Instantiation of the glued-section API at the Serre twisting sheaf `O(m)` on the
integral model: sections of the glued twist are the compatible families of
chart sections (`(Xᵢ/Xⱼ)^m`-twisted agreement on overlaps), and the twist on
`Proj` itself has the same global sections through the `fromGlued`
identification.  This is the scaffold consumed by the computation
`Γ(Proj ℤ[X], O(m)) ≅ (ℤ[X])_m` (degree-`m` forms). -/

namespace AlgebraicGeometry.ProjTwist

open AlgebraicGeometry.Scheme

variable (n₀ : Type)

/-- **Global sections of the glued Serre twist are the compatible families**
of chart sections of the trivialising cover: the instantiation of
`Scheme.Modules.glueSectionsEquiv` at the descent datum of `O(m)`. -/
def serreTwistGluedSectionsEquiv (m : ℕ) :
    Γ(serreTwistGlued n₀ m, ⊤) ≃ₗ[Γ((glueData n₀).glued, ⊤)]
      Scheme.Modules.glueGammaCompatible (glueData n₀)
        (fun i => SheafOfModules.unit ((glueData n₀).U i).ringCatSheaf)
        (fun i j => twistTransition n₀ m i j) :=
  Scheme.Modules.glueSectionsEquiv (glueData n₀)
    (fun i => SheafOfModules.unit ((glueData n₀).U i).ringCatSheaf)
    (fun i j => twistTransition n₀ m i j)
    (fun i => twistTransition_self n₀ m i)
    (fun i j k => twistTransition_cocycle n₀ m i j k)

/-- The Serre twist on `Proj` is the pushforward of the glued twist along
`fromGlued`: the pullback along the inverse cover isomorphism is converted by
`pullbackIsoPushforwardInv`. -/
def serreTwistIsoPushforwardGlued (m : ℕ) :
    serreTwist n₀ m ≅
      (Scheme.Modules.pushforward (basicOpenCover n₀).fromGlued).obj
        (serreTwistGlued n₀ m) :=
  (Scheme.Modules.pullbackIsoPushforwardInv
      (inv (basicOpenCover n₀).fromGlued)).app (serreTwistGlued n₀ m) ≪≫
    (Scheme.Modules.pushforwardCongr
      (IsIso.inv_inv (f := (basicOpenCover n₀).fromGlued))).app (serreTwistGlued n₀ m)

/-- Global sections of the Serre twist on `Proj` agree with those of the glued
model (`Γ` of a pushforward at `⊤` is definitional). -/
def serreTwistSectionsToGlued (m : ℕ) :
    Γ(serreTwist n₀ m, ⊤) ≃+ Γ(serreTwistGlued n₀ m, ⊤) :=
  Scheme.Modules.gammaAddEquivOfIso (serreTwistIsoPushforwardGlued n₀ m)

/-- **Global sections of `O(m)` on the integral model are the compatible
families over the basic-open cover** — the concrete equalizer description of
`Γ(Proj ℤ[Xᵢ], O(m))` feeding the degree-`m`-forms computation. -/
def serreTwistSectionsCompatible (m : ℕ) :
    Γ(serreTwist n₀ m, ⊤) ≃+
      Scheme.Modules.glueGammaCompatible (glueData n₀)
        (fun i => SheafOfModules.unit ((glueData n₀).U i).ringCatSheaf)
        (fun i j => twistTransition n₀ m i j) :=
  (serreTwistSectionsToGlued n₀ m).trans
    (serreTwistGluedSectionsEquiv n₀ m).toAddEquiv

end AlgebraicGeometry.ProjTwist
