/-
Copyright (c) 2026 Axel Delaval. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Exactness of the tilde functor (Stacks 01HV) — Route-P step P3

Project-local supplement feeding `AlgebraicGeometry.qcoh_kernel_qcoh`.

For `X = Spec R`, the tilde functor `~ : ModuleCat R ⥤ (Spec R).Modules`,
`M ↦ M^~`, is exact.  The named target of this file is
`AlgebraicGeometry.tildePreservesFiniteLimits : PreservesFiniteLimits (tilde.functor R)`
(the *left*-exactness / kernel-preservation half).

## What is delivered (axiom-clean)

* `tilde_preservesFiniteColimits` — the *right*-exactness half: `~` is a left adjoint
  (`AlgebraicGeometry.tilde.adjunction`), hence preserves all colimits, in particular finite
  colimits.  This is one of the two halves of exactness.
* `tilde_toStalk_map_injective` — the *flatness core* in the only publicly-accessible form:
  for an injective `R`-module map `f : M ⟶ N`, the localised stalk map
  `M_𝔭 →ₗ[R] N_𝔭` (built from Mathlib's `IsLocalizedModule (tilde.toStalk · x)` instances) is
  injective.  This is the algebraic content that "localisation `R → R_𝔭` is flat" contributes
  to mono-preservation.

## What is delivered (axiom-clean), continued

* `tilde_stalkFunctor_map_toStalk` — the **germ-naturality** transport identity (the crux flagged
  by the planner).  For `f : M ⟶ N` and a point `x ↔ 𝔭`, the `Ab`-valued stalk map of `~f`
  (computed through the faithful, limit-preserving `Scheme.Modules.toPresheaf`) intertwines the two
  localisation maps `tilde.toStalk`: `toStalk M x ≫ (Ab-stalk map) = f ≫ toStalk N x`.  This
  identifies the otherwise opaque `Ab`-germ-induced stalk map with the localised module map of `f`
  on the image of `toStalk`.  Proven on the public `Ab`-stalk path (`stalkFunctor_map_germ_apply` +
  the `⊤`-section naturality `StructureSheaf.comapₗ_const`), avoiding the module-private handles.
* `tildePreservesFiniteLimits_of_toPresheaf` — the **categorical reduction**: since
  `Scheme.Modules.toPresheaf` reflects finite limits (faithful + preserves limits + reflects isos,
  and `(Spec R).Modules` has finite limits), `~` preserves finite limits as soon as the composite
  `~ ⋙ toPresheaf` does.  This is `Limits.preservesFiniteLimits_of_reflects_of_preserves`.

## Why `tildePreservesFiniteLimits` itself is NOT closed here

The mathematical route (blueprint `lem:tilde_preserves_kernels`) is stalkwise flatness.  The
**categorical-glue obstruction is FALSE** — `tildePreservesFiniteLimits_of_toPresheaf` (above)
discharges it via `preservesFiniteLimits_of_reflects_of_preserves`; no "right-exact + mono ⟹
left-exact" lemma is needed.  The single remaining gap is the **stalkwise localisation step**:
showing the composite `~ ⋙ Scheme.Modules.toPresheaf` preserves finite limits.  Stalkwise this is
exactly localisation-is-flat:
* The `Ab`-germ-induced stalk map of `~f` is identified on the image of `toStalk` with the localised
  map of `f` by `tilde_stalkFunctor_map_toStalk`; and the localised map is injective
  (`tilde_toStalk_map_injective`).
* What still has to be built (~100–150 LOC): upgrade this to a full stalkwise *isomorphism* of the
  kernel-comparison map.  Concretely, (a) prove the `Ab` stalk map is `R`-linear (via `germₗ` +
  `R`-linearity of `Scheme.Modules.Hom.app`) so it equals `IsLocalizedModule.map …`, then (b)
  feed `∀ x, PreservesFiniteLimits (~ ⋙ toPresheaf ⋙ stalkFunctor x)` through a jointly-reflecting
  stalk family (`CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectsLimit`) to obtain
  `PreservesFiniteLimits (~ ⋙ toPresheaf)`, then `tildePreservesFiniteLimits_of_toPresheaf`.
  The `ModuleCat R`-valued stalk path is dead (Mathlib privacy of `toStalkₗ'`, `stalkIsoₗ`,
  `stalkToLocalizationₗ`, `structurePresheafInModuleCat`); use the public `Ab` path throughout.

See `task_results/AlgebraicJacobian.Cohomology.TildeExactness.md` for the precise next steps.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-! ## Project-local Mathlib supplement — exactness of the tilde functor -/

/-- **Right-exactness of `~`.**  The tilde functor `~ : ModuleCat R ⥤ (Spec R).Modules`
preserves finite colimits: it is a left adjoint (`AlgebraicGeometry.tilde.adjunction`), so it
preserves all colimits.  Project-local because the packaged statement is what the
kernel/cokernel quasi-coherence argument (Stacks `lemma-kernel-cokernel-quasi-coherent`)
consumes alongside the (still open) finite-limit half. -/
theorem tilde_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (tilde.functor R) := inferInstance

/-- **Flatness core of mono-preservation for `~`.**  For an injective `R`-module map
`f : M ⟶ N` and a point `x ↔ 𝔭` of `Spec R`, the induced localised map on stalks
`M_𝔭 →ₗ[R] N_𝔭` — assembled from Mathlib's `IsLocalizedModule (tilde.toStalk · x).hom`
instances via `IsLocalizedModule.map` — is injective.  This is exactly the contribution of
"localisation `R → R_𝔭` is flat" to the statement that `~` preserves monomorphisms (Stacks
01HV, exactness of `~`).  Stated with the publicly-accessible stalk-localisation map
`AlgebraicGeometry.tilde.toStalk`, the only such handle exported by Mathlib. -/
theorem tilde_toStalk_map_injective {M N : ModuleCat R} (f : M ⟶ N)
    (hf : Function.Injective f.hom) (x : PrimeSpectrum.Top R) :
    Function.Injective (IsLocalizedModule.map x.asIdeal.primeCompl
      (AlgebraicGeometry.tilde.toStalk M x).hom (AlgebraicGeometry.tilde.toStalk N x).hom f.hom) :=
  IsLocalizedModule.map_injective _ _ _ _ hf

/-- **Reduction of the named target.**  `tildePreservesFiniteLimits` follows once `~` is shown to
preserve every kernel `parallelPair f 0`; all the ambient typeclass hypotheses of
`Functor.preservesFiniteLimits_of_preservesKernels` are already discharged for
`tilde.functor R` (it is additive, `ModuleCat R` and `(Spec R).Modules` have the requisite
finite (co)products / zero objects).  Recorded project-locally so the remaining obligation is a
single, sharply-stated hypothesis for the continuation lane. -/
theorem tilde_preservesFiniteLimits_of_preservesKernels
    (H : ∀ {M N : ModuleCat R} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (tilde.functor R)) :
    PreservesFiniteLimits (tilde.functor R) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- **Germ-naturality of the localisation map `toStalk`.**  For an `R`-module map
`f : M ⟶ N` and a point `x ↔ 𝔭` of `Spec R`, the `Ab`-valued stalk map of `~f` (computed via the
faithful, limit-preserving forgetful functor `Scheme.Modules.toPresheaf`) intertwines the two
localisation maps `tilde.toStalk`: precomposing with `toStalk M x` and postcomposing `f` agree.

This is the load-bearing transport identity for mono/kernel preservation of `~`: it identifies the
otherwise opaque `Ab`-germ-induced stalk map with the localised module map of `f`.  Project-local
because Mathlib only exports the localisation handles `tilde.toStalk` and `toOpenₗ` and the section
naturality `comapₗ_const`; the germ-level statement is assembled here. -/
theorem tilde_stalkFunctor_map_toStalk {M N : ModuleCat R} (f : M ⟶ N)
    (x : PrimeSpectrum.Top R) (m : M) :
    (TopCat.Presheaf.stalkFunctor _ x).map
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map (tilde.map f))
        ((tilde.toStalk M x).hom m)
      = (tilde.toStalk N x).hom (f.hom m) := by
  change (TopCat.Presheaf.stalkFunctor _ x).map
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map (tilde.map f))
        (TopCat.Presheaf.germ (AlgebraicGeometry.moduleStructurePresheaf R M).presheaf ⊤ x
          (by trivial) (StructureSheaf.toOpenₗ R M ⊤ m))
      = TopCat.Presheaf.germ (AlgebraicGeometry.moduleStructurePresheaf R N).presheaf ⊤ x
          (by trivial) (StructureSheaf.toOpenₗ R N ⊤ (f.hom m))
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x True.intro
    ((Scheme.Modules.toPresheaf (Spec (.of R))).map (tilde.map f)) (StructureSheaf.toOpenₗ R M ⊤ m)]
  congr 1
  simp only [Scheme.Modules.toPresheaf_map, Scheme.Modules.mapPresheaf_app,
    Scheme.Modules.Hom.app]
  rw [StructureSheaf.toOpenₗ_eq_const, StructureSheaf.toOpenₗ_eq_const]
  simp only [AlgebraicGeometry.tilde.map, AlgebraicGeometry.SpecModulesToSheafFullyFaithful,
    CategoryTheory.NatTrans.comp_app, AlgebraicGeometry.tilde.modulesSpecToSheafIso,
    ModuleCat.hom_comp]
  erw [StructureSheaf.comapₗ_const (hb := le_of_eq PrimeSpectrum.basicOpen_one.symm)]
  rfl

/-- **Reduction of `tildePreservesFiniteLimits` to the presheaf level.**  The forgetful functor
`Scheme.Modules.toPresheaf` from `𝒪_{Spec R}`-modules to presheaves of abelian groups is faithful,
preserves limits, and reflects isomorphisms; hence (since `(Spec R).Modules` has finite limits) it
reflects finite limits.  Therefore, to show `~` preserves finite limits it suffices to show the
composite `~ ⋙ toPresheaf` does.  This isolates the remaining obligation of
`lem:tilde_preserves_kernels` to a statement about the abelian-presheaf-valued composite, whose
stalks are computed by `tilde_stalkFunctor_map_toStalk`.  Project-local categorical glue (it refutes
the earlier-feared "no right-exact + mono ⟹ left-exact" obstruction: the reduction is purely
`preservesFiniteLimits_of_reflects_of_preserves`). -/
theorem tildePreservesFiniteLimits_of_toPresheaf
    (H : PreservesFiniteLimits
      (tilde.functor R ⋙ Scheme.Modules.toPresheaf (Spec (.of R)))) :
    PreservesFiniteLimits (tilde.functor R) :=
  haveI := H
  Limits.preservesFiniteLimits_of_reflects_of_preserves (tilde.functor R)
    (Scheme.Modules.toPresheaf (Spec (.of R)))

/-! ## Project-local Mathlib supplement — R-linear packaging of the Ab-stalk map -/

/-- **Germ–scalar compatibility (`R`-linearity of the germ map).**  For `s` a section of `M^~`
over `U` and `r : R`, the germ at `x` of `(algebraMap R Γ(O_X,U) r) • s` equals `r •` the germ of
`s` (the `R`-action on the stalk being the localisation one through `tilde.toStalk R x`).  This is
the section-level half of "the `Ab`-stalk map of `~f` is `R`-linear".  Project-local because the
linear germ `StructureSheaf.germₗ` is not exported (no `public`); it is rebuilt here from the public
`PresheafOfModules.germ_smul` and `StructureSheaf.algebraMap_germ_apply`. -/
theorem tilde_germ_algebraMap_smul {M : ModuleCat R} (U : (Spec (.of R)).Opens)
    (x : PrimeSpectrum.Top R) (hxU : x ∈ U) (r : R) (s : Γ(AlgebraicGeometry.tilde M, U)) :
    (ConcreteCategory.hom
        ((AlgebraicGeometry.tilde M).presheaf.germ U x hxU))
        ((algebraMap R Γ(Spec (.of R), U) r) • s)
      = r • (ConcreteCategory.hom
        ((AlgebraicGeometry.tilde M).presheaf.germ U x hxU)) s := by
  erw [PresheafOfModules.germ_smul, StructureSheaf.algebraMap_germ_apply]
  rfl

/-- **Sub-step (A): the `Ab`-stalk map `σ_x` is `R`-linear.**  The stalk-functor image
`σ_x := (stalkFunctor Ab x).map (toPresheaf.map (~f))` is a priori only an `Ab`-morphism between
the stalks; this packages it as the genuine `R`-linear map `M_𝔭 →ₗ[R] N_𝔭`.  Project-local: the
`ModuleCat R`-valued stalk functor for `SheafOfModules` is not exported (its building blocks
`stalkIsoₗ`/`toStalkₗ'` are private), so the linear structure is reconstructed here on the public
`Ab` stalk via germ-linearity. -/
noncomputable def stalkMapₗ {M N : ModuleCat R} (f : M ⟶ N) (x : PrimeSpectrum.Top R) :
    (AlgebraicGeometry.tilde M).presheaf.stalk x →ₗ[R]
      (AlgebraicGeometry.tilde N).presheaf.stalk x where
  toFun := (TopCat.Presheaf.stalkFunctor _ x).map
    ((Scheme.Modules.toPresheaf (Spec (.of R))).map (AlgebraicGeometry.tilde.map f))
  map_add' a b := map_add _ a b
  map_smul' r ζ := by
    dsimp only [RingHom.id_apply]
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.germ_exist (AlgebraicGeometry.tilde M).presheaf x ζ
    rw [← tilde_germ_algebraMap_smul U x hxU r s]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map (AlgebraicGeometry.tilde.map f)),
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map (AlgebraicGeometry.tilde.map f))]
    rw [Scheme.Modules.toPresheaf_map, Scheme.Modules.mapPresheaf_app]
    simp only [Opposite.unop_op]
    erw [Scheme.Modules.Hom.app_smul, tilde_germ_algebraMap_smul U x hxU r]
    rfl

/-- **Identification of `σ_x` with the localised module map.**  The `R`-linear `Ab`-stalk map
`stalkMapₗ f x` is exactly the localisation `M_𝔭 →ₗ[R] N_𝔭` of `f`, i.e.
`IsLocalizedModule.map _ (toStalk M x) (toStalk N x) f`.  Both are `R`-linear and agree on the image
of the localisation map `tilde.toStalk M x` (by `tilde_stalkFunctor_map_toStalk`), so they coincide
by `IsLocalizedModule.ext`.  Project-local: it packages the otherwise opaque germ-induced stalk map
as the concrete localised map, whose flatness-injectivity is `tilde_toStalk_map_injective`. -/
theorem stalkMapₗ_eq {M N : ModuleCat R} (f : M ⟶ N) (x : PrimeSpectrum.Top R) :
    stalkMapₗ f x = IsLocalizedModule.map x.asIdeal.primeCompl
      (AlgebraicGeometry.tilde.toStalk M x).hom (AlgebraicGeometry.tilde.toStalk N x).hom
      f.hom := by
  apply IsLocalizedModule.ext x.asIdeal.primeCompl (AlgebraicGeometry.tilde.toStalk M x).hom
    (fun s => IsLocalizedModule.map_units (AlgebraicGeometry.tilde.toStalk N x).hom s)
  ext m
  change stalkMapₗ f x ((AlgebraicGeometry.tilde.toStalk M x).hom m) = _
  rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
  exact tilde_stalkFunctor_map_toStalk f x m

/-- **Stalkwise injectivity of `~f` for a monomorphism `f`.**  For an injective `R`-module map
`f`, the `R`-linear `Ab`-stalk map `σ_x = stalkMapₗ f x` of `~f` is injective at every point `x`.
This is the stalkwise-flatness contribution to mono-preservation of `~`, now stated on the genuine
linear stalk map: it combines the identification `stalkMapₗ_eq` with the localisation injectivity
`tilde_toStalk_map_injective`.  Project-local stepping stone toward `tildePreservesFiniteLimits`. -/
theorem stalkMapₗ_injective {M N : ModuleCat R} (f : M ⟶ N) (hf : Function.Injective f.hom)
    (x : PrimeSpectrum.Top R) : Function.Injective (stalkMapₗ f x) := by
  rw [stalkMapₗ_eq]
  exact tilde_toStalk_map_injective f hf x

end AlgebraicGeometry
