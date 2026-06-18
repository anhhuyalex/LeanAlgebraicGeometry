/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Cohomology.FlatBaseChange

/-!
# Flat base change for the pushforward, global (`H⁰`-as-equalizer) chain

This file builds the global ("FBC-B") leg of the `i = 0` flat-base-change package:
`H⁰(X, F) = Γ(X, F)` of a quasi-compact, quasi-separated scheme is the equalizer of
a *finite* affine cover, and flat base change commutes with that finite equalizer.

It is the companion of `AlgebraicJacobian.Cohomology.FlatBaseChange`, which it imports
read-only (using the affine global-sections comparison as a per-term black box).

See `blueprint/src/chapters/Cohomology_FlatBaseChange.tex` (FBC-B section).
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## Project-local Mathlib supplement — finite affine covers with quasi-compact overlaps -/

/-- A quasi-compact scheme admits a *finite* affine open cover; when it is moreover
quasi-separated, every pairwise intersection of cover members is quasi-compact.

Project-local: packages `isCompact_iff_finite_and_eq_biUnion_affineOpens` (finite affine
subcover of `⊤`) with `quasiSeparatedSpace_iff_forall_affineOpens` (quasi-compact overlaps)
into the single combinatorial input feeding the finite sheaf-condition equalizer of the
`H⁰` flat-base-change argument. -/
theorem Scheme.exists_finite_affineCover_inter_isQuasiCompact (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ s : Set X.affineOpens, s.Finite ∧ (⨆ i ∈ s, (i : X.Opens)) = ⊤ ∧
      ∀ U ∈ s, ∀ V ∈ s, IsCompact ((U : Set X) ∩ (V : Set X)) := by
  obtain ⟨s, hs, he⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
      (by simpa using isCompact_univ (X := ↥X))
  refine ⟨s, hs, he.symm, ?_⟩
  intro U _ V _
  exact quasiSeparatedSpace_iff_forall_affineOpens.mp ‹_› U V

/-! ## Project-local Mathlib supplement — the global sections as a sheaf-condition equalizer -/

open TopCat.Presheaf SheafConditionEqualizerProducts in
/-- For `M : X.Modules` and any open cover `U : ι → X.Opens`, the sheaf-condition fork
of the underlying abelian-group presheaf of `M` is a limit (an equalizer of products):
```
Γ(M, ⨆ i, U i) ⟶ ∏ i, Γ(M, U i) ⇉ ∏ (i,j), Γ(M, U i ⊓ U j).
```
This is the equalizer-products form of the sheaf condition specialised to the abelian
presheaf `M.presheaf` of a sheaf of `𝒪_X`-modules. Combined with the finite affine cover
of `Scheme.exists_finite_affineCover_inter_isQuasiCompact` it computes `Γ(X, M) = Γ(M, ⊤)`
as a *finite* equalizer; that finiteness is what the flat-base-change argument needs to
commute `- ⊗_A B` past the equalizer.

Project-local: packages `M.isSheaf` through Mathlib's
`isSheaf_iff_isSheafEqualizerProducts` at the level of `X.Modules`. -/
noncomputable def Modules.gammaIsLimitSheafConditionFork {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    IsLimit (fork M.presheaf U) :=
  ((isSheaf_iff_isSheafEqualizerProducts M.presheaf).mp M.isSheaf U).some

open TopCat.Presheaf SheafConditionEqualizerProducts in
/-! ## Project-local Mathlib supplement — global sections as an `A`-module `eqLocus`

This block presents `Γ(X, M)` of a sheaf of modules as a `LinearMap.eqLocus` of two
`A`-linear maps over the ground ring `A = Γ(X, ⊤)`, the shape required by
`LinearMap.tensorEqLocusEquiv` (flat base change preserves finite equalizers). Every
section over an open `U` is viewed as an `A`-module by restriction of scalars along the
structure-sheaf restriction `A → Γ(X, U)`, and the structure-sheaf restriction maps of
`M` become `A`-linear maps between these. -/

/-- The ground ring `A = Γ(X, ⊤)` of a scheme, as a `CommRing` (taken from the
`CommRingCat`-valued structure presheaf so the `CommRing`/`Algebra` instances resolve). -/
abbrev groundRing (X : Scheme.{u}) : Type u := X.presheaf.obj (Opposite.op (⊤ : X.Opens))

/-- The structure-sheaf restriction ring hom `A = Γ(X, ⊤) → Γ(X, U)`. Project-local:
the `A`-algebra structure on the sections over `U` used to view them as `A`-modules. -/
noncomputable def rhoU (X : Scheme.{u}) (U : X.Opens) :
    groundRing X →+* (X.ringCatSheaf.obj.obj (Opposite.op U)) :=
  (X.ringCatSheaf.obj.map (homOfLE (le_top)).op).hom

/-- The sections `Γ(M, U)` of a sheaf of modules over an open `U`, regarded as an
`A`-module (`A = Γ(X, ⊤)`) by restriction of scalars along `rhoU`. Project-local: the
common `A`-module home for the global-sections equalizer presentation. -/
noncomputable abbrev gammaModA {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    ModuleCat (groundRing X) :=
  (ModuleCat.restrictScalars (rhoU X U)).obj (M.val.obj (Opposite.op U))

/-- Restriction-of-scalars transitivity: `(Γ(X,U) → Γ(X,V)) ∘ (A → Γ(X,U)) = (A → Γ(X,V))`.
Project-local glue making the structure-sheaf restriction maps `A`-linear. -/
theorem rhoU_comp {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) :
    ((X.ringCatSheaf.obj.map (homOfLE h).op).hom).comp (rhoU X U) = rhoU X V := by
  ext a
  change (X.ringCatSheaf.obj.map (homOfLE h).op).hom (rhoU X U a) = rhoU X V a
  have e : (X.ringCatSheaf.obj.map (homOfLE (le_top) : V ⟶ ⊤).op)
      = (X.ringCatSheaf.obj.map (homOfLE (le_top) : U ⟶ ⊤).op)
          ≫ (X.ringCatSheaf.obj.map (homOfLE h).op) := by
    rw [← X.ringCatSheaf.obj.map_comp]; rfl
  simp only [rhoU, e, RingCat.hom_comp]; rfl

/-- The structure-sheaf restriction `Γ(M, U) → Γ(M, V)` (`V ≤ U`) as a morphism of
`A`-modules, built from `M.val.map` by restriction of scalars. -/
noncomputable def gammaResAHom {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    gammaModA M U ⟶ gammaModA M V :=
  (ModuleCat.restrictScalars (rhoU X U)).map (M.val.map (homOfLE h).op) ≫
    (ModuleCat.restrictScalarsComp'App (rhoU X U)
        (X.ringCatSheaf.obj.map (homOfLE h).op).hom (rhoU X V)
        (rhoU_comp h).symm (M.val.obj (Opposite.op V))).inv

/-- The structure-sheaf restriction `Γ(M, U) → Γ(M, V)` (`V ≤ U`) as an `A`-linear map.
Project-local: the building block of the `leftRes`/`rightRes` legs of the equalizer. -/
noncomputable def gammaResA {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    gammaModA M U →ₗ[groundRing X] gammaModA M V := (gammaResAHom M h).hom

@[simp] theorem gammaResA_apply {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (x : gammaModA M U) :
    gammaResA M h x = (M.val.map (homOfLE h).op).hom x := by
  simp only [gammaResA, gammaResAHom, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.restrictScalars.map_apply, ModuleCat.restrictScalarsComp'App_inv_apply]

/-- Functoriality of the `A`-linear restriction maps. -/
theorem gammaResA_comp {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens} (h1 : V ≤ U)
    (h2 : W ≤ V) (x : gammaModA M U) :
    gammaResA M h2 (gammaResA M h1 x) = gammaResA M (h2.trans h1) x := by
  simp only [gammaResA_apply]
  change (M.presheaf.map (homOfLE h2).op) ((M.presheaf.map (homOfLE h1).op) x)
     = (M.presheaf.map (homOfLE (h2.trans h1)).op) x
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  congr 1

/-- The `leftRes` leg `∏ᵢ Γ(M,Uᵢ) → ∏ᵢⱼ Γ(M, Uᵢ ⊓ Uⱼ)` (restrict the `i`-th factor),
as an `A`-linear map. Project-local: the first leg of the sheaf-condition equalizer in the
`A`-module presentation. -/
noncomputable def leftRes {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    (∀ i, gammaModA M (U i)) →ₗ[groundRing X] (∀ p : ι × ι, gammaModA M (U p.1 ⊓ U p.2)) :=
  LinearMap.pi (fun p => (gammaResA M (inf_le_left)).comp (LinearMap.proj p.1))

/-- The `rightRes` leg `∏ᵢ Γ(M,Uᵢ) → ∏ᵢⱼ Γ(M, Uᵢ ⊓ Uⱼ)` (restrict the `j`-th factor),
as an `A`-linear map. -/
noncomputable def rightRes {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    (∀ i, gammaModA M (U i)) →ₗ[groundRing X] (∀ p : ι × ι, gammaModA M (U p.1 ⊓ U p.2)) :=
  LinearMap.pi (fun p => (gammaResA M (inf_le_right)).comp (LinearMap.proj p.2))

/-- The `A`-linear map `Γ(M, ⊤) → ∏ᵢ Γ(M, Uᵢ)` restricting a global section to the cover. -/
noncomputable def toCover {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    gammaModA M (⊤ : X.Opens) →ₗ[groundRing X] (∀ i, gammaModA M (U i)) :=
  LinearMap.pi (fun _ => gammaResA M le_top)

/-- The restriction of a global section to a cover is a compatible family: it lands in the
`eqLocus` of the two restriction legs. Project-local: the equalizer-membership feeding the
global-sections `eqLocus` presentation. -/
theorem leftRes_toCover {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (s : gammaModA M (⊤ : X.Opens)) :
    leftRes M U (toCover M U s) = rightRes M U (toCover M U s) := by
  funext p
  simp only [leftRes, rightRes, toCover, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, gammaResA_comp]

/-- The global-sections-to-compatible-families map corestricted to the `eqLocus`. -/
noncomputable def toCoverEqLocus {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    gammaModA M (⊤ : X.Opens) →ₗ[groundRing X] LinearMap.eqLocus (leftRes M U) (rightRes M U) :=
  (toCover M U).codRestrict _ (leftRes_toCover M U)

/-- **Global sections as an `A`-module equalizer.** For `M : X.Modules` and an open cover
`U` of `X` (`⨆ i, U i = ⊤`), the global sections `Γ(X, M) = Γ(M, ⊤)`, regarded as a module
over the ground ring `A = Γ(X, ⊤)`, are `A`-linearly isomorphic to the `eqLocus` of the two
restriction legs `leftRes`, `rightRes : ∏ᵢ Γ(M, Uᵢ) → ∏ᵢⱼ Γ(M, Uᵢ ⊓ Uⱼ)`.

Project-local: this is the `LinearMap.eqLocus` presentation of global sections over the
ground ring `A` that `LinearMap.tensorEqLocusEquiv` (flat base change preserves finite
equalizers) consumes for the `H⁰` flat-base-change argument. Injectivity is the separatedness
of the sheaf of modules (`TopCat.Sheaf.eq_of_locally_eq'`) and surjectivity is the gluing
axiom (`TopCat.Sheaf.existsUnique_gluing'`), both on the underlying `Ab`-sheaf `M.presheaf`. -/
noncomputable def gammaTopEquivEqLocus {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) :
    gammaModA M (⊤ : X.Opens) ≃ₗ[groundRing X] LinearMap.eqLocus (leftRes M U) (rightRes M U) :=
  LinearEquiv.ofBijective (toCoverEqLocus M U)
    ⟨by
      intro s t hst
      have h := Subtype.ext_iff.mp hst
      refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
        U ⊤ (fun _ => homOfLE le_top) hU.ge _ _ ?_
      intro i
      have hi := congrFun h i
      simpa only [toCoverEqLocus, LinearMap.codRestrict_apply, toCover, LinearMap.pi_apply,
        gammaResA_apply] using hi,
     by
      rintro ⟨sf, hsf⟩
      have hcompat : TopCat.Presheaf.IsCompatible M.presheaf U sf := by
        intro i j
        have h := congrFun hsf (i, j)
        simpa only [leftRes, rightRes, LinearMap.pi_apply, LinearMap.comp_apply,
          LinearMap.proj_apply, gammaResA_apply] using h
      obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
        (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) U ⊤ (fun _ => homOfLE le_top) hU.ge sf hcompat
      refine ⟨s, ?_⟩
      apply Subtype.ext
      funext i
      simpa only [toCoverEqLocus, LinearMap.codRestrict_apply, toCover, LinearMap.pi_apply,
        gammaResA_apply] using hs i⟩

/-- **Flat base change commutes with the `H⁰` equalizer.** For `M : X.Modules`, a cover `U`
of `X` (`⨆ i, U i = ⊤`), and a flat `A`-algebra `B` (`A = Γ(X, ⊤)`), base changing the global
sections `Γ(X, M)` along `A → B` is the `eqLocus` of the base-changed restriction legs:
\[ B ⊗_A Γ(X, M) ≅ \operatorname{eqLocus}(B ⊗ \mathrm{leftRes},\ B ⊗ \mathrm{rightRes}). \]

Project-local: the composite of the equalizer presentation
`gammaTopEquivEqLocus` with `LinearMap.tensorEqLocusEquiv` (flatness commutes with the finite
equalizer). This is the module-level core that the `H⁰` flat-base-change reduction consumes:
the right-hand side is, by the same presentation applied to the base-changed sheaf, the global
sections of the pulled-back module over `B`. -/
noncomputable def baseChangeGammaEquiv {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (B : Type u) [CommRing B] [Algebra (groundRing X) B]
    [Module.Flat (groundRing X) B] :
    TensorProduct (groundRing X) B (gammaModA M (⊤ : X.Opens)) ≃ₗ[B]
      LinearMap.eqLocus (TensorProduct.AlgebraTensorModule.lTensor B B (leftRes M U))
        (TensorProduct.AlgebraTensorModule.lTensor B B (rightRes M U)) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (gammaTopEquivEqLocus M U hU)) ≪≫ₗ
    LinearMap.tensorEqLocusEquiv B B (leftRes M U) (rightRes M U)

open scoped TensorProduct

namespace Modules

/-- Canonical algebra map `B → Γ(X', O)` for the base-change pullback `X' = X ×_{Spec A} Spec B`,
from the projection `X' ⟶ Spec B`. -/
noncomputable def pullbackGroundRingAlg {X : Scheme.{u}} (B : Type u) [CommRing B]
    [Algebra (groundRing X) B] :
    B →+* groundRing (pullback X.toSpecΓ
      (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B)))) :=
  ((pullback.snd X.toSpecΓ
      (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B)))).appTop).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

/-- **Base change of the finite equalizer diagram** (`lem:base_changed_equalizer_diagram`).

For `F : X.Modules`, a cover `U` of `X` (`⨆ i, U i = ⊤`) and a flat `A`-algebra `B`
(`A = groundRing X`), the equalizer locus of the *base-changed* restriction legs
`id_B ⊗ leftRes`, `id_B ⊗ rightRes` of `F` is `B`-linearly isomorphic to the equalizer
locus of the restriction legs `leftRes F' U'`, `rightRes F' U'` of the pulled-back module
`F' = (g')^* F` over the base-changed cover `U' i = (g')⁻¹(U i)` of
`X' = X ×_{Spec A} Spec B`, regarded as a `B`-module by restriction of scalars along
`pullbackGroundRingAlg B`.

This is the concrete (Čech-free) realization of Stacks Tag 02KH's relation
`Č•(𝒰_B, F_B) = Č•(𝒰, F) ⊗_A B`: each fork term is the sections of `F_B = (g')^*F` over an
*affine* piece `(U_i)_B` (resp. `(U_{ij})_B`), and the concrete affine pullback dictionary
`pullback_spec_tilde_iso` (Stacks 01I9, `(Spec φ)^* M̃ ≅ (B ⊗_A M)~`) supplies the per-chart
isomorphism `Γ((U_i)_B, F_B) ≅ Γ(U_i, F) ⊗_A B` *at the module level* — no abstract base-change
map, no flatness, no mate identification, since every piece is affine. These tilde isomorphisms
are natural in restriction, so they intertwine `leftRes`/`rightRes`; finally `- ⊗_A B` commutes
with the *finite* products `∏ᵢ`, `∏ᵢⱼ` (so the base-changed fork is literally `(- ⊗_A B)` of the
original fork).

The remaining `sorry` is exactly that per-chart `pullback_spec_tilde_iso` identification together
with the finite-product/tensor commutation; constructing it requires the restriction-compatibility
of the pullback dictionary over each affine chart of the (a priori non-affine) `X`. This is the
single genuine gap of the direct route. It is consumed by `baseChangeEqLocusToPullbackGamma`. -/
noncomputable def _root_.AlgebraicGeometry.baseChange_sheafConditionFork_tensorIso
    {X : Scheme.{u}} (F : X.Modules) (B : Type u) [CommRing B]
    [Algebra (groundRing X) B] [Module.Flat (groundRing X) B]
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    LinearMap.eqLocus (TensorProduct.AlgebraTensorModule.lTensor B B (leftRes F U))
        (TensorProduct.AlgebraTensorModule.lTensor B B (rightRes F U)) ≃ₗ[B]
      (ModuleCat.restrictScalars (pullbackGroundRingAlg B)).obj
        (ModuleCat.of (groundRing (pullback X.toSpecΓ
            (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B))))) (LinearMap.eqLocus
          (leftRes ((Scheme.Modules.pullback (pullback.fst X.toSpecΓ
              (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B))))).obj F)
            (fun i => (TopologicalSpace.Opens.map (pullback.fst X.toSpecΓ
              (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B)))).base).obj (U i)))
          (rightRes ((Scheme.Modules.pullback (pullback.fst X.toSpecΓ
              (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B))))).obj F)
            (fun i => (TopologicalSpace.Opens.map (pullback.fst X.toSpecΓ
              (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B)))).base).obj (U i))))) :=
  -- GENUINE GAP: the per-chart `pullback_spec_tilde_iso` (Stacks 01I9) identification of the
  -- base-changed legs `id_B ⊗ leftRes/rightRes` with `leftRes F' U'`, `rightRes F' U'`, plus the
  -- finite-product/tensor commutation `B ⊗ ∏ᵢ (-) ≅ ∏ᵢ (B ⊗ -)`. Constructing the forward map
  -- needs the restriction-compatibility of the affine pullback dictionary over each chart of `X`.
  sorry

/-- **Per-chart base-change core of `thm:fbcb_global_direct`.** For a cover `U` of `X`
(`⨆ i, U i = ⊤`), the equalizer locus of the *base-changed* restriction legs
`id_B ⊗ leftRes`, `id_B ⊗ rightRes` of `F` is `B`-linearly isomorphic to the global
sections `Γ(X', F')` of the pulled-back module `F' = (g')^* F` over
`X' = X ×_{Spec A} Spec B`, viewed as a `B`-module by restriction of scalars along
`pullbackGroundRingAlg B`.

This is the single remaining ingredient of the direct (Čech-free) route: it packages the
per-chart pullback dictionary `pullback_spec_tilde_iso` (Stacks 01I9,
`(Spec φ)^* M̃ ≅ (B ⊗_A M)~`, giving `Γ((U_i)_B, F') ≅ Γ(U_i, F) ⊗_A B`) and the affine
base change of the overlaps (`affineBaseChange_pushforward_iso`) with the `X'`-side
equalizer-locus presentation `gammaTopEquivEqLocus` applied to `F'` and the base-changed
cover `U' i = (g')⁻¹(U i)`.

The `gammaTopEquivEqLocus`-half of the route (the `X'`-side presentation `eX'`) is
constructed below; the genuine gap is the per-chart identification of the base-changed
legs with the restriction legs of `U'`, which additionally needs the base-changed cover to
be *finite* (so `B ⊗ -` commutes with the product over the index set), i.e. `X`
quasi-compact + quasi-separated — a hypothesis the current signature of
`baseChangeGammaPullbackEquiv` does not carry. See `task_results` for the precise blockers. -/
noncomputable def baseChangeEqLocusToPullbackGamma {X : Scheme.{u}} (F : X.Modules)
    (B : Type u) [CommRing B] [Algebra (groundRing X) B] [Module.Flat (groundRing X) B]
    {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    LinearMap.eqLocus (TensorProduct.AlgebraTensorModule.lTensor B B (leftRes F U))
        (TensorProduct.AlgebraTensorModule.lTensor B B (rightRes F U)) ≃ₗ[B]
      (ModuleCat.restrictScalars (pullbackGroundRingAlg B)).obj
        (gammaModA ((Scheme.Modules.pullback
            (pullback.fst X.toSpecΓ
              (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B))))).obj F) ⊤) := by
  -- The base-changed scheme `X' = X ×_{Spec A} Spec B` and its projection `g' : X' ⟶ X`.
  -- The pulled-back module `F' = (g')^* F` over `X'`.
  -- The base-changed cover `U' i = (g')⁻¹(U i)` of `X'`: preimages of the `U i`.
  have hU' : iSup (fun i => (TopologicalSpace.Opens.map
      (pullback.fst X.toSpecΓ
        (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B)))).base).obj (U i)) = ⊤ := by
    have hmap := TopologicalSpace.Opens.map_iSup
      (pullback.fst X.toSpecΓ
        (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B)))).base U
    rw [hU, TopologicalSpace.Opens.map_top] at hmap
    exact hmap.symm
  -- The `X'`-side equalizer-locus presentation of `Γ(X', F')` (over `groundRing X'`):
  -- `gammaModA F' ⊤ ≃ₗ[groundRing X'] eqLocus (leftRes F' U') (rightRes F' U')`.
  -- This realises the second half of the composite route (`gammaTopEquivEqLocus` at `F'`).
  have eX' := gammaTopEquivEqLocus
    ((Scheme.Modules.pullback (pullback.fst X.toSpecΓ
      (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B))))).obj F)
    (fun i => (TopologicalSpace.Opens.map
      (pullback.fst X.toSpecΓ
        (Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B)))).base).obj (U i))
    hU'
  -- REMAINING GAP (the per-chart base-change core + `B`-linear restriction-of-scalars
  -- transport of `eX'`):
  --   (a) per chart `i`: `Γ((U_i)_B, F') ≅ Γ(U_i, F) ⊗_A B` via `pullback_spec_tilde_iso`
  --       (Stacks 01I9), and likewise on overlaps via `affineBaseChange_pushforward_iso`
  --       (currently `sorry` in FlatBaseChange.lean) — these intertwine the base-changed
  --       legs `id_B ⊗ leftRes/rightRes` with `leftRes F' U'`, `rightRes F' U'`;
  --   (b) `B ⊗ ∏_i (-) ≅ ∏_i (B ⊗ -)` needs `ι` finite (X qcqs), absent from this signature;
  --   (c) restriction of scalars of `eX'.symm` along `pullbackGroundRingAlg B` to land in the
  --       stated `ModuleCat B` codomain.
  -- (c) Transport `eX'` to a `B`-linear equivalence by restriction of scalars along
  -- `pullbackGroundRingAlg B`, using the ModuleCat `restrictScalars` *functor* (there is no
  -- `IsScalarTower B (groundRing X') _` instance, so `LinearEquiv.restrictScalars` is unavailable):
  -- `(restrictScalars φ).obj (Γ(X',F')-as-eqLocus) ≃ₗ[B] (restrictScalars φ).obj (gammaModA F' ⊤)`.
  have transportC := (((ModuleCat.restrictScalars (pullbackGroundRingAlg B)).mapIso
      eX'.symm.toModuleIso).toLinearEquiv)
  -- It remains (the genuine gap, (a)+(b)): the per-chart identification of the base-changed legs
  -- with `leftRes F' U'`, `rightRes F' U'`. This is now the named blueprint lemma
  -- `baseChange_sheafConditionFork_tensorIso` (`lem:base_changed_equalizer_diagram`), whose
  -- codomain is exactly `transportC`'s domain.
  exact baseChange_sheafConditionFork_tensorIso F B U hU ≪≫ₗ transportC

/-- `thm:fbcb_global_direct` — `Γ(X,F) ⊗_A B ≃ₗ[B] Γ(X', F')`, `A = groundRing X`,
`X' = X ×_{Spec A} Spec B`, `F' = (g')^* F`.

Assembled as the direct (Čech-free) composite of:
* `baseChangeGammaEquiv F U hU B` — flat base change past the finite `H⁰` equalizer:
  `B ⊗_A Γ(X,F) ≃ₗ[B] eqLocus (id_B ⊗ leftRes, id_B ⊗ rightRes)`; and
* `baseChangeEqLocusToPullbackGamma` — the per-chart identification of that base-changed
  equalizer locus with `Γ(X', F')`.

The cover `U` is the canonical affine open cover `X.affineCover` (any cover with
`⨆ U i = ⊤` makes the first leg typecheck; the second leg's proof additionally wants it
finite, i.e. `X` qcqs). -/
noncomputable def baseChangeGammaPullbackEquiv {X : Scheme.{u}} (F : X.Modules)
    (B : Type u) [CommRing B] [Algebra (groundRing X) B] [Module.Flat (groundRing X) B] :
    let sp := Spec.map (CommRingCat.ofHom (algebraMap (groundRing X) B))
    let g' : pullback X.toSpecΓ sp ⟶ X := pullback.fst X.toSpecΓ sp
    TensorProduct (groundRing X) B (gammaModA F (⊤ : X.Opens)) ≃ₗ[B]
      (ModuleCat.restrictScalars (pullbackGroundRingAlg B)).obj
        (gammaModA ((Scheme.Modules.pullback g').obj F) ⊤) :=
  baseChangeGammaEquiv F (fun i => (X.affineCover.f i).opensRange)
      X.affineCover.iSup_opensRange B ≪≫ₗ
    baseChangeEqLocusToPullbackGamma F B (fun i => (X.affineCover.f i).opensRange)
      X.affineCover.iSup_opensRange

end Modules

/-! ## The IsIso chain: separated case, Mayer–Vietoris, and the global-sections bridge

The three lemmas below are the sheaf-morphism-level legs of the `H⁰` flat-base-change
chain. They are phrased at the *section-over-`⊤`* level of the base-change map
`pushforwardBaseChangeMap` over an affine base `S' = Spec B`: the top-section map
`(pushforwardBaseChangeMap …).app ⊤` is the concrete comparison
`Γ(X, F) ⊗_A B → Γ(X_B, F_B)` of the blueprint, and the bridge
`flatBaseChange_isIso_iff_gammaTensorComparison` upgrades its being an isomorphism to the
full sheaf-morphism isomorphism (using quasi-coherence of the pushforward + tilde
full-faithfulness over the affine base).  The concrete module isomorphism realizing this
top-section comparison is `Modules.baseChangeGammaPullbackEquiv` (built, modulo the single
gap `baseChange_sheafConditionFork_tensorIso`); the residual to connect it is the naturality
square identifying `(pushforwardBaseChangeMap …).app ⊤` with that equivalence. -/

/-- **Flat base change, separated case** (`lem:flat_base_change_separated`).
For `g` flat, `f` quasi-compact and separated, `F` quasi-coherent, over affine bases
`S = Spec A`, `S' = Spec B`, the top-section comparison map
`Γ(X, F) ⊗_A B → Γ(X_B, F_B)` (`= (pushforwardBaseChangeMap …).app ⊤`) is an isomorphism.

Blueprint proof: `Γ(X,F)` and `Γ(X_B,F_B)` are the equalizers of the finite forks of a
finite affine cover `𝒰` and its base change `𝒰_B`
(`Modules.gammaIsLimitSheafConditionFork`); by `baseChange_sheafConditionFork_tensorIso`
the `X_B`-fork is the `X`-fork with `- ⊗_A B` applied; flatness commutes `- ⊗_A B` past the
finite equalizer (`LinearMap.tensorEqLocusEquiv`, packaged in
`Modules.baseChangeGammaEquiv`). The composite is `Modules.baseChangeGammaPullbackEquiv`. -/
theorem flatBaseChange_pushforward_isIso_of_isSeparated
    {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [IsSeparated f]
    [IsAffine S] [IsAffine S'] (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((pushforwardBaseChangeMap f g f' g' h.w F).app (⊤ : S'.Opens)) :=
  -- The top-section map is the comparison `Γ(X,F) ⊗_A B → Γ(X_B,F_B)`, an isomorphism by
  -- `Modules.baseChangeGammaPullbackEquiv` (flat past the finite equalizer ∘
  -- `baseChange_sheafConditionFork_tensorIso`). Residual: identify `.app ⊤` with that equiv.
  sorry

/-- **Flat base change, Mayer–Vietoris reduction of the quasi-separated case**
(`lem:flat_base_change_mayer_vietoris`). For `g` flat, `f` quasi-compact and
quasi-separated, `F` quasi-coherent, over affine bases, the top-section comparison map is an
isomorphism.

Blueprint proof: choose a finite affine cover `X = U_1 ∪ … ∪ U_t` and induct on `t`. `t = 1`
is the affine case (`pullback_spec_tilde_iso`); for `t > 1` use the two-member cover
`{U_1 ∪ … ∪ U_{t-1}, U_t}`, whose intersection is separated (so the separated case
`flatBaseChange_pushforward_isIso_of_isSeparated` applies), and flatness preserves the finite
Mayer–Vietoris equalizer. -/
theorem flatBaseChange_pushforward_mayerVietoris
    {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [QuasiSeparated f]
    [IsAffine S] [IsAffine S'] (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((pushforwardBaseChangeMap f g f' g' h.w F).app (⊤ : S'.Opens)) :=
  -- Mayer–Vietoris induction on the size of a finite affine cover, base case the separated
  -- lemma above; each inductive step uses flat-preserves-finite-equalizer. Heaviest leg;
  -- scaffolded this iter.
  sorry

/-- **Reduction of the base-change map to the global-sections comparison** (the bridge,
`lem:flat_base_change_reduce_global_sections`). Over affine bases `S = Spec A`,
`S' = Spec B` with `g` flat and `f` quasi-compact quasi-separated, the sheaf-level base-change
map `g^*(f_*F) → f'_*(g')^*F` is an isomorphism **iff** its top-section comparison map
`Γ(X,F) ⊗_A B → Γ(X_B,F_B)` is.

Blueprint proof: being an isomorphism is local on `S'`; `f_*F` is quasi-coherent (qcqs `f`),
hence the tilde of the `A`-module `Γ(X,F)`, and likewise `f'_*F'` is the tilde of
`Γ(X_B,F_B)`; under the tilde-equivalence the sheaf map is the tilde of the top-section
comparison, and `~(-)` is fully faithful on quasi-coherent modules, so one is an isomorphism
iff the other is. The forward direction is the elementary "a section of an isomorphism is an
isomorphism"; the reverse is the tilde full-faithfulness content. -/
theorem flatBaseChange_isIso_iff_gammaTensorComparison
    {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [QuasiSeparated f]
    [IsAffine S] [IsAffine S'] (F : X.Modules) [F.IsQuasicoherent] :
    IsIso (pushforwardBaseChangeMap f g f' g' h.w F) ↔
      IsIso ((pushforwardBaseChangeMap f g f' g' h.w F).app (⊤ : S'.Opens)) := by
  constructor
  · -- Forward: the sections-over-`⊤` functor preserves isomorphisms
    -- (`Scheme.Modules.Hom.isIso_iff_isIso_app`).
    intro hiso
    haveI := hiso
    infer_instance
  · -- Reverse: tilde full-faithfulness over the affine base `S' = Spec B` upgrades an
    -- isomorphism on global sections to a sheaf-morphism isomorphism. Scaffolded this iter.
    intro hsec
    sorry

end AlgebraicGeometry
