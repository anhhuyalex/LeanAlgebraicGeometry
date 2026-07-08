/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AlgebraicJacobian.Picard.TensorObjSubstrate
import AlgebraicJacobian.Picard.SectionGradedRing
import AlgebraicJacobian.Picard.QuotScheme

/-!
# Affine tensor-section substrate (`TensorSectionFormula`)

This leaf file records the Tier-1 substrate bricks for the affine tensor-section
formula that feeds the quasi-coherent case of
`Scheme.Modules.pullbackTensorMap_isIso` ([Stacks 01CD]; the section formula is
[Stacks 01CD]/[Stacks 01CA] read on a basis of affine opens).

For `A B : X.Modules` the substrate tensor `Scheme.Modules.tensorObj A B`
(`Picard/TensorObjSubstrate.lean`) is the sheafification of the presheaf-of-modules
tensor `P := PresheafOfModules.Monoidal.tensorObj A.val B.val` of the underlying
presheaves.  Objectwise, `P(V) = Γ(A, V) ⊗_{Γ(X, V)} Γ(B, V)`
(`tensorPresheaf_obj`), so the sheafification unit provides a canonical
`Γ(X, V)`-linear **section comparison**

  `tensorSectionHom A B V : Γ(A, V) ⊗_{Γ(X, V)} Γ(B, V) ⟶ Γ(tensorObj A B, V)`

for every open `V` (`tensorSectionHom`), natural in restriction
(`tensorSectionHom_naturality_apply`).  Over the total space it is exactly the
section multiplication `sectionsMul` of the graded-ring machinery
(`tensorSectionHom_top_eq_sectionsMul`), and the substrate `tensorObj` and the
section-graded `sheafTensorObj` are the same object
(`tensorObjIsoSheafTensorObj`, definitional).

## Contents

* `tensorPresheaf` — the presheaf-of-modules tensor of the underlying presheaves.
* `tensorSectionHom` — the section comparison map at an open `V`.
* `tensorPresheaf_obj` — the objectwise identification of the domain as
  `Γ(A, V) ⊗ Γ(B, V)`.
* `tensorSectionHom_naturality_apply` — restriction naturality.
* `tensorSectionHom_top_eq_sectionsMul` — the `⊤`-value is `sectionsMul`.
* `tensorObjIsoSheafTensorObj` — the (definitional) `tensorObj ≅ sheafTensorObj`
  bridge.
* `isIso_sheafification_tensorSectionUnit` — the categorical crux: sheafifying the
  presheaf comparison unit is an isomorphism (the reflective localization inverts
  the unit), which is why the affine formula reduces to the presheaf-tensor
  localization on a basis of affine opens.

## Wiring plan (the quasi-coherent case of `pullbackTensorMap_isIso`)

The remaining, genuinely hard step — promoting `tensorSectionHom A B V` to a
`LinearEquiv` for quasi-coherent `A B` and *affine* `V` — is deliberately left to
a later wiring pass, because it requires computing the sheafification value on the
basis of basic opens as a localization of the presheaf tensor, and that
computation lives against the (currently `private`) tilde-comparison engine of
`Picard/QuotScheme.lean`.  Concretely, the wiring pass should:

1. On a basic open `D(f) ⊆ V` (affine `V = Spec Γ(X, V)`), identify
   `Γ(A, D(f)) = Γ(A, V)_f` and `Γ(B, D(f)) = Γ(B, V)_f` via
   `isLocalizedModule_basicOpen_of_isQuasicoherent` (QuotScheme.lean), so
   `P(D(f)) = Γ(A, V)_f ⊗_{Γ(X, V)_f} Γ(B, V)_f`.
2. Feed `LocalizedModule.equivTensorProduct` /
   `RingTheory.Localization.BaseChange` to identify this with
   `(Γ(A, V) ⊗_{Γ(X, V)} Γ(B, V))_f`, i.e. `P` is a localizing presheaf on the
   basic-open basis; hence `tensorObj A B|_V` is the tilde of
   `Γ(A, V) ⊗ Γ(B, V)` and `tensorSectionHom A B V` is a `LinearEquiv`.
3. Transport through `Modules.pullback_app_isoTensor` (QuotScheme.lean, the
   pullback side) and globalize by `isIso_of_isIso_restrict` over the affine cover,
   discharging the `pullbackTensorMap_restrict` restriction coherence.

### Statement-narrowing recommendation for the orchestrator

`Modules.pullbackTensorMap_isIso` is stated for *arbitrary* `A B` (no
quasi-coherence hypothesis), matching the general [Stacks 01CD] statement for
ringed spaces.  The chart-chase route above only closes the *quasi-coherent* case.
Since the sole consumer (`pullback_moduleTensorPow_iso`) already carries
`[F.IsQuasicoherent] [L.IsQuasicoherent]`, narrowing
`pullbackTensorMap_isIso` (or introducing a quasi-coherent variant
`pullbackTensorMap_isIso_of_isQuasicoherent`) to require
`[A.IsQuasicoherent] [B.IsQuasicoherent]` would make the affine section formula
sufficient and unblock the qcoh case without the general ringed-space stalk
machinery.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The presheaf-of-modules tensor of the underlying presheaves of `A B : X.Modules`;
objectwise `Γ(A, V) ⊗_{Γ(X, V)} Γ(B, V)`.  Its sheafification is
`Scheme.Modules.tensorObj A B`. -/
noncomputable abbrev tensorPresheaf (A B : X.Modules) : X.PresheafOfModules :=
  PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) A.val B.val

/-- The **section comparison** at an open `V`: the `Γ(X, V)`-linear map
`Γ(A, V) ⊗_{Γ(X, V)} Γ(B, V) ⟶ Γ(tensorObj A B, V)`, defined as the `V`-component of
the sheafification-adjunction unit at the presheaf tensor.  On the total space it is
the section multiplication `sectionsMul`; for quasi-coherent `A B` and affine `V` it
is an isomorphism (the affine tensor-section formula — see the module docstring). -/
noncomputable def tensorSectionHom (A B : X.Modules) (V : X.Opens) :
    (tensorPresheaf A B).obj (op V) ⟶ (tensorObj A B).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (tensorPresheaf A B)).app (op V)

/-- The domain of `tensorSectionHom` over `V` is the `Γ(X, V)`-module tensor product
`Γ(A, V) ⊗ Γ(B, V)` (the objectwise formula for the presheaf-of-modules tensor). -/
lemma tensorPresheaf_obj (A B : X.Modules) (V : X.Opens) :
    (tensorPresheaf A B).obj (op V) =
      MonoidalCategory.tensorObj (C := ModuleCat (X.presheaf.obj (op V)))
        (A.val.obj (op V)) (B.val.obj (op V)) := rfl

/-- Restriction naturality of the section comparison (element-wise): the comparison
commutes with restriction of sections along an inclusion `V ⊆ W`. -/
lemma tensorSectionHom_naturality_apply (A B : X.Modules) {V W : X.Opens} (i : op W ⟶ op V)
    (x : (tensorPresheaf A B).obj (op W)) :
    tensorSectionHom A B V ((tensorPresheaf A B).map i x) =
      (tensorObj A B).val.map i (tensorSectionHom A B W x) :=
  PresheafOfModules.naturality_apply _ i x

/-- Over the total space `⊤`, the section comparison is the section multiplication
`sectionsMul` of the graded-ring machinery (definitional). -/
lemma tensorSectionHom_top_eq_sectionsMul (A B : X.Modules) :
    tensorSectionHom A B ⊤ = sectionsMul A B := rfl

/-- **Bridge (bonus).**  The substrate tensor `Scheme.Modules.tensorObj` (the object
in which `pullbackTensorMap_isIso` is stated) and the section-graded
`Scheme.Modules.sheafTensorObj` are the *same* object: both sheafify the
presheaf-of-modules tensor of the underlying presheaves. -/
noncomputable def tensorObjIsoSheafTensorObj (A B : X.Modules) :
    tensorObj A B ≅ sheafTensorObj A B := Iso.refl _

/-- **Categorical crux.**  Sheafifying the underlying presheaf comparison unit is an
isomorphism: the reflective sheafification inverts the localization unit of
`tensorPresheaf A B`.  This is the reason the affine section formula reduces to the
presheaf-tensor localization on a basis of affine opens. -/
lemma isIso_sheafification_tensorSectionUnit (A B : X.Modules) :
    IsIso (sheafification.map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app (tensorPresheaf A B))) :=
  isIso_sheafification_map_unit _

/-! ## Quasi-coherence from basic-open section localization (the reusable criterion)

The affine tensor-section wiring pass (see the module docstring) will produce, for
`A B : X.Modules` quasi-coherent and `V` affine, the fact that the section restriction
`Γ(A ⊗ B, V) → Γ(A ⊗ B, D(f))` is `IsLocalizedModule (powers f)` (the affine tensor-section
formula composed with the module-localization heart
`(M ⊗_R N)_f ≅ M_f ⊗_{R_f} N_f`, `RingTheory.Localization.BaseChange`).  The lemma below
packages the *converse* direction of `Scheme.Modules.isLocalizedModule_basicOpen`
(`QuotScheme.lean`): a sheaf of modules whose section restrictions are localizations on all
basic opens of all affine opens is quasi-coherent.  It is the general form of the
pushforward-specialised assembly `pushforward_isQuasicoherent`/
`pushforward_isQuasicoherent_over_affine`, and is exactly the criterion the 01CB
(`tensorObj`/`sheafTensorObj`) instance feeds once the affine section-localization is in hand. -/

open TopologicalSpace in
/-- The family of all affine opens covers a scheme (for the opens Grothendieck topology).
Reconstruction of the `private` `QuotScheme.coversTop_affineOpens`. -/
private theorem coversTop_affineOpens' (S : Scheme.{u}) :
    (Opens.grothendieckTopology ↥S).CoversTop
      (fun U : S.affineOpens => U.1) := by
  intro W y hy
  obtain ⟨V, hVaff, hyV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S) hy
  refine ⟨V, homOfLE hVW, ?_, hyV⟩
  rw [CategoryTheory.Sieve.mem_ofObjects_iff]
  exact ⟨⟨V, hVaff⟩, ⟨𝟙 V⟩⟩

set_option maxHeartbeats 1600000 in
-- The tilde-presentation transport + affine-cover `of_coversTop` assembly (mirroring
-- `QuotScheme.pushforward_isQuasicoherent_over_affine`) needs heartbeat/instance headroom.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Quasi-coherence from basic-open section localization** (the converse of
`Scheme.Modules.isLocalizedModule_basicOpen`).  If for every affine open `U` and every
`f : Γ(X, U)` the section restriction `restrictBasicOpenₗ M f : Γ(M, U) → Γ(M, X.basicOpen f)`
exhibits the target as the localization of the source at `powers f`, then `M` is quasi-coherent.

Quasi-coherence is local (`SheafOfModules.IsQuasicoherent.of_coversTop`) on the affine-opens
cover; on each affine `U` the hypothesis feeds
`isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule` to produce the P1 datum
`IsIso (fromTildeΓ ((pullback hU.fromSpec).obj M))`, whose tilde presentation transports along
`U.ι = isoSpec.hom ≫ fromSpec` back to the geometric slice (`overRestrictPresentationInv`).
This is the pushforward-free form of `Scheme.Modules.pushforward_isQuasicoherent`. -/
theorem isQuasicoherent_of_isLocalizedModule_basicOpen (M : X.Modules)
    (H : ∀ (U : X.Opens), IsAffineOpen U → ∀ (f : Γ(X, U)),
      letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
        Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen f))
      letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) :=
        IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      IsLocalizedModule (Submonoid.powers f) (Scheme.Modules.restrictBasicOpenₗ M f)) :
    M.IsQuasicoherent := by
  haveI hslice : ∀ U : X.affineOpens, (M.over U.1).IsQuasicoherent := by
    intro U
    haveI hP1 : IsIso (Scheme.Modules.fromTildeΓ
        ((Scheme.Modules.pullback U.2.fromSpec).obj M)) :=
      Scheme.Modules.isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule M U.2
        (fun f' => H U.1 U.2 f')
    -- global presentation of the `fromSpec`-pullback, via the tilde presentation
    let eT' : tilde ((modulesSpecToSheaf.obj
          ((Scheme.Modules.pullback U.2.fromSpec).obj M)).presheaf.obj (Opposite.op ⊤))
        ≅ (Scheme.Modules.pullback U.2.fromSpec).obj M :=
      @asIso _ _ _ _
        (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback U.2.fromSpec).obj M)) hP1
    have P_M' : ((Scheme.Modules.pullback U.2.fromSpec).obj M).Presentation :=
      SheafOfModules.Presentation.ofIsIso.{u} eT'.hom
        (AlgebraicGeometry.presentationTilde.{u} _ Set.univ (by simp) _ (Submodule.span_eq _))
    -- transport along `U.ι = isoSpec.hom ≫ fromSpec`
    have hcomp : U.2.isoSpec.hom ≫ U.2.fromSpec = U.1.ι := by
      rw [← U.2.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
    have P_ι : ((Scheme.Modules.pullback U.1.ι).obj M).Presentation :=
      SheafOfModules.Presentation.ofIsIso.{u, u, u}
        ((Scheme.Modules.pullbackComp U.2.isoSpec.hom U.2.fromSpec).app M ≪≫
          (Scheme.Modules.pullbackCongr hcomp).app M).hom
        (Scheme.Modules.presentationPullbackOfSchemeIso U.2.isoSpec.symm
          ((Scheme.Modules.pullback U.2.fromSpec).obj M) P_M')
    exact (Scheme.Modules.overRestrictPresentationInv U.1 M P_ι).isQuasicoherent
  exact SheafOfModules.IsQuasicoherent.of_coversTop M
    (fun U : X.affineOpens => U.1) (coversTop_affineOpens' X)

end AlgebraicGeometry.Scheme.Modules
