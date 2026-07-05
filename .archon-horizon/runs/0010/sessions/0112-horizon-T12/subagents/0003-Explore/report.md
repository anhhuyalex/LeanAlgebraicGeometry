I have gathered all the necessary information. Here is the structured report.

---

# Report: Base-change / pullback-module infrastructure

All paths absolute. Project root = `/home/Axel/LeanAlgebraicGeometry-Horizon/MainProjects/Algebraic-Jacobian-Challenge`; Mathlib = `/home/Axel/LeanAlgebraicGeometry-Horizon/.lake-packages/mathlib`.

Ambient context in `Cohomology/CechHigherDirectImageUnconditional.lean`: `universe u`, `open CategoryTheory Limits`, `namespace AlgebraicGeometry`, `open Scheme.Modules`, and `variable {S S' X X' : Scheme.{u}}` (line 93). Two later sections add `variable {R R' : CommRingCat.{u}}` and `variable (f : X ⟶ Spec R) (g : Spec R' ⟶ Spec R) (f' : X' ⟶ Spec R') (g' : X' ⟶ X)` (lines 1351-1352 and 1435-1436).

---

## 1. `pullback_spec_tilde_iso` and nearby tilde/sections dictionaries

File: `AlgebraicJacobian/Cohomology/FlatBaseChange.lean`

**`pullback_spec_tilde_iso`** — line 704. Doc: "Affine pullback of a tilde-module. Pulling `M^~` back along `Spec φ` is `tilde(R' ⊗_R M)`; the pullback companion of `pushforward_spec_tilde_iso`, Stacks 01I9. Built by uniqueness-of-left-adjoints (`conjugateIsoEquiv` of the two composite adjunctions, identified by `gammaPushforwardNatIso`)."
```lean
noncomputable def pullback_spec_tilde_iso {R R' : CommRingCat.{u}}
    (φ : R ⟶ R') (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M)
```

**`pushforward_spec_tilde_iso`** (the pushforward companion) — line 553. Doc: "Affine pushforward of a tilde-module (unconditional): `(Spec φ)_* (M^~) ≅ tilde(restrictScalars φ M)`."
```lean
noncomputable def pushforward_spec_tilde_iso {R R' : CommRingCat.{u}}
    (φ : R ⟶ R') (M : ModuleCat.{u} R') :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.restrictScalars φ.hom).obj M)
```

**`gammaPushforwardNatIso`** — line 682. Doc: "Naturality of the Γ-fragment comparison; the right-adjoint natural iso driving `pullback_spec_tilde_iso`."
```lean
noncomputable def gammaPushforwardNatIso {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := R') ⋙ ModuleCat.restrictScalars φ.hom
```

**`gammaPushforwardIso`** — line 300. Doc: "Γ-fragment comparison at an object: `Γ_R((Spec φ)_* N) ≅ restrictScalars φ (Γ_{R'} N)`."
```lean
noncomputable def gammaPushforwardIso {R R' : CommRingCat.{u}} (φ : R ⟶ R') (N) :
    (moduleSpecΓFunctor (R := R)).obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N) ≅
      (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := R')).obj N)
```
(There is also `gammaPushforwardIsoAt` at line 344, an open-indexed variant `Γ(N,U) ≅ restrictScalars φ (Γ(M^~,(Spec φ)⁻¹U))`.)

Related tilde/sections lemmas in this file:
- `fromTildeΓ_app_isIso_of_isLocalizedModule` — line 381 (`IsIso (N.fromTildeΓ.app (basicOpen a))`), uses `tilde.toOpen` and `Scheme.Modules.toOpen_fromTildeΓ_app`.
- `pushforward_spec_tilde_iso_of_isLocalizedModule` — line 446.
- `ΓSpecIso_inv_naturality` used at line 286 (`StructureSheaf.globalSectionsIso`).

The `tilde` / `moduleSpecΓFunctor` primitives live in Mathlib `Mathlib/AlgebraicGeometry/Modules/Tilde.lean` (see §7 below): `moduleSpecΓFunctor` (line 48), `tilde` (line 147), `tilde.functor` (line 227, `ModuleCat R ⥤ (Spec (.of R)).Modules`), `tilde.toTildeΓNatIso` (line 328), `tilde.adjunction` (line 335).

---

## 2. Altitude-1/2 bridge and qcoh-preservation

File: `AlgebraicJacobian/Cohomology/CechHigherDirectImageUnconditional.lean`

**`pullback_isQuasicoherent`** — line 407. Doc: "Pullback preserves quasi-coherence (Stacks 01BG, open case): `(V.ι)^* F` is quasi-coherent; thin re-export of `isQuasicoherent_pullback_opens`."
```lean
theorem pullback_isQuasicoherent (V : X.Opens) (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pullback V.ι).obj F).IsQuasicoherent
```

**`pullbackRestrict_iso_tilde`** — line 419. Doc: "Altitude 1: `(V.ι)^* F` pushed to `Spec Γ(X,V)` via `isoSpec` is `tilde N` (Stacks 01I8). Uses `pushforward_iso_preserves_qcoh` + `qcoh_iso_tilde_sections`."
```lean
noncomputable def pullbackRestrict_iso_tilde (F : X.Modules) (hF : F.IsQuasicoherent)
    {V : X.Opens} (hV : IsAffineOpen V) :
    (Scheme.Modules.pushforward hV.isoSpec.hom).obj ((Scheme.Modules.pullback V.ι).obj F) ≅
      tilde (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward hV.isoSpec.hom).obj ((Scheme.Modules.pullback V.ι).obj F)))
```

**`qcoh_iso_tilde_sections`** — this is defined in `AlgebraicJacobian/Cohomology/QcohTildeSections.lean` line 66 (NOT in the Cech file; it is only *used* there at line 428). Doc: "Affine structure theorem 01I8 packaged as `F ≅ (Γ F)^~` when `[IsIso F.fromTildeΓ]`."
```lean
noncomputable def qcoh_iso_tilde_sections (F : (Spec R).Modules) [IsIso F.fromTildeΓ] :
    F ≅ tilde (moduleSpecΓFunctor.obj F)
```
Companions in that file: `qcoh_iso_tilde_sections_of_presentation` (line 75), `..._of_genSections` (line 133), `qcoh_iso_tilde_sections_qcoh` (line 1557, `[IsQuasicoherent F]` unconditional form), and simp lemmas `qcoh_iso_tilde_sections_hom/_inv` (lines 82/88).

**`pushforward_iso_preserves_qcoh`** — defined in `AlgebraicJacobian/Cohomology/OpenImmersionPushforward.lean` line 715 (used in the Cech file). Doc: "Quasi-coherence is preserved by pushforward along a scheme iso."
```lean
lemma pushforward_iso_preserves_qcoh {X Y : Scheme.{u}} (φ : X ≅ Y) (H : X.Modules)
    (hH : H.IsQuasicoherent) :
    ((Scheme.Modules.pushforwardEquivOfIso φ).functor.obj H).IsQuasicoherent
```

Also relevant altitude-2 forms in the Cech file: `pushPullObj_pushforward_iso_tilde` (line 443, literal `Spec R` base), `pushPullObj_pushforward_iso_tilde_affine` (line 474, abstract `[IsAffine S]`), `coverInterOpen_isAffine` (line 508), `pushPullObj_coverInter_pushforward_iso_tilde` (line 557).

---

## 3. The ambient-pullback → restricted-square → ring-pushout recipe (session-0011)

All in `AlgebraicJacobian/Cohomology/CechHigherDirectImageUnconditional.lean` unless noted. The concrete corner uses `V = coverInterOpen 𝒰 σ` (a finite fibre-power intersection open) rather than an explicit `g'⁻¹V ⊓ f'⁻¹U''`; the base-changed corner is the pulled-back intersection open `V'_σ`.

**(a) Restricted morphisms between the open subschemes.**

`restrictedCartesianAffinePushout` — line 541. Doc: "Restricting the global cartesian square over the intersection open `V ↪ X` gives a cartesian square `X' ×_X V → V`; sorry-free via `IsPullback.of_hasPullback`."
```lean
theorem restrictedCartesianAffinePushout (g' : X' ⟶ X)
    (𝒰 : X.OpenCover) {κ : Type} (σ : κ → 𝒰.I₀) :
    IsPullback (pullback.snd g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (pullback.fst g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))
      (Scheme.Opens.ι (coverInterOpen 𝒰 σ)) g' :=
  (IsPullback.of_hasPullback g' (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).flip
```

`coverInterOpen_baseChange_sliceIso` — line 1281: identifies the categorical pullback `pullback g' j_σ` with the base-changed intersection open `V'_σ` via `IsOpenImmersion.isoOfRangeEq` + `coverInterOpen_baseChange_eq`. Returns `(pullback g' (ι (coverInterOpen 𝒰 σ)) : Scheme) ≅ ↑(coverInterOpen (...pushforwardIso h.isoPullback.symm.hom) σ)`.

`coverInterOpen_baseChange_restrictedMap` — line 1326: the restricted morphism `V'_σ ⟶ V_σ`, `= sliceIso.inv ≫ pullback.snd g' j_σ`.

`coverInterOpen_baseChange_restrictedMap_comm` — line 1337. Doc: "The restricted square commutes: `ι_{V'_σ} ≫ g' = (g'|_σ) ≫ ι_{V_σ}`."
```lean
lemma coverInterOpen_baseChange_restrictedMap_comm
    (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (𝒰 : X.OpenCover)
    {κ : Type} [Finite κ] (σ : κ → 𝒰.I₀) :
    Scheme.Opens.ι (coverInterOpen ((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
        h.isoPullback.symm.hom) σ) ≫ g' =
      coverInterOpen_baseChange_restrictedMap f g f' g' h 𝒰 σ ≫
        Scheme.Opens.ι (coverInterOpen 𝒰 σ)
```
(supporting: `coverInterOpen_baseChange_sliceIso_hom_ι` line 1303, `..._inv_fst` line 1315.)

**(b) `P` is affine.**

`coverInterOpen_isAffine` — line 508 (Cech file). Doc: "Every finite nonempty fibre-power intersection `coverInterOpen 𝒰 σ` is affine (separated `f`, affine `S`, affine cover); via `IsSeparated.isClosedImmersion_diagonal` + `IsAffineOpen.iInf` + `isAffineOpen_opensRange`."
```lean
theorem coverInterOpen_isAffine (f : X ⟶ S) [IsSeparated f] [IsAffine S]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] {κ : Type} [Finite κ] [Nonempty κ]
    (σ : κ → 𝒰.I₀) : IsAffineOpen (coverInterOpen 𝒰 σ)
```
The base-changed corner `V'_σ` is affine by the same lemma applied to `f'` and the pushed-forward cover (used e.g. as `coverInterOpen_isAffine f' (...pushforwardIso...) σ` at line 1366). See §8 for the explicit `g'⁻¹UX ⊓ iY⁻¹UT` variant.

**(c) Ring-pushout / tensor description.**

The Spec-cartesian ⟹ ring-pushout converse:
`isPushout_of_isPullback_SpecMap` — line 1264. Doc: "A square of rings whose `Spec`-square is cartesian is a pushout of rings; `Scheme.Spec` fully faithful, reflect via `IsPullback.of_map_of_faithful`."
```lean
theorem isPushout_of_isPullback_SpecMap {A B C P : CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ C)
    (ρ : B ⟶ P) (σ : C ⟶ P)
    (H : IsPullback (Spec.map ρ) (Spec.map σ) (Spec.map φ) (Spec.map ψ)) :
    IsPushout φ ψ ρ σ
```

Corner ring map + its `Spec`:
`coverInterCornerRingMap` — line 1356: `ρ : Γ(X, V_σ) ⟶ Γ(X', V'_σ)` `= Spec.preimage (isoSpec.inv ≫ restrictedMap ≫ isoSpec.hom)`.
`coverInterCornerRingMap_SpecMap` — line 1373: `Spec.map ρ = e'.inv ≫ restrictedMap ≫ e.hom`.

**The pushout itself** — `coverInter_ring_isPushout` — line 1394. This is the exact session-0011 recipe (`isPushout_of_isPullback_SpecMap` ← `restrictedCartesianAffinePushout ... .paste_vert h` ← `IsPullback.of_iso'` with the two `isoSpec`s and the `sliceIso`):
```lean
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
        σ).fromSpec ≫ f'))
```
Proof body (lines 1406-1429): `apply isPushout_of_isPullback_SpecMap`; `rw [Spec.map_preimage,…, coverInterCornerRingMap_SpecMap]`; `have H₁ := (restrictedCartesianAffinePushout g' 𝒰 σ).paste_vert h`; `refine H₁.of_iso' (e'.symm ≪≫ sliceIso.symm) e.symm (Iso.refl _) (Iso.refl _) …`.

**The Γ(X',P) ≅ Γ(X,V) ⊗_{Γ(S,U)} Γ(S',U'') description** is realized module-theoretically by:
`coverInter_baseChanged_sections_tensor_rewrite` — line 1450. Doc: "The base-changed section module `Γ(V'_σ, (j'_σ)^*((g')^*F))` is the corner extension of scalars `B ⊗_{A_σ} N` of `N = Γ(V_σ, F|_{V_σ})` along `ρ`; via `coverInterOpen_baseChange_restrictedMap_comm`, `pullbackRestrict_iso_tilde`, `pullback_spec_tilde_iso`."
```lean
noncomputable def coverInter_baseChanged_sections_tensor_rewrite
    (h : IsPullback g' f' f g) [IsSeparated f] [IsSeparated f']
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    [∀ i, IsAffine (((Scheme.Pullback.openCoverOfLeft 𝒰 f g).pushforwardIso
      h.isoPullback.symm.hom).X i)]
    (F : X.Modules) (hF : F.IsQuasicoherent)
    {κ : Type} [Finite κ] [Nonempty κ] (σ : κ → 𝒰.I₀) :
    moduleSpecΓFunctor.obj (… ((pullback (ι V'_σ)).obj ((pullback g').obj F))) ≅
      (ModuleCat.extendScalars (coverInterCornerRingMap f g f' g' h 𝒰 σ).hom).obj
        (moduleSpecΓFunctor.obj (… ((pullback (ι V_σ)).obj F)))
```
(Full LHS/RHS types verbatim at lines 1457-1468.)

The affine base-change brick over that pushout:
**`affinePushforwardPullbackBaseChange`** (in `FlatBaseChange.lean` line 802). Doc: "Affine termwise base change (abstract-`B` framing): for a ring pushout `(φ,ψ,ρ,σ)` and `A`-module `M`, `g^*(f_* M̃) ≅ f'_*((g')^* M̃)`; 5-step chain from the two tilde dictionaries + `baseChangeCancelModuleIso`, never forms the adjoint mate."
```lean
noncomputable def affinePushforwardPullbackBaseChange {R A R' B : CommRingCat.{u}}
    (φ : R ⟶ A) (ψ : R ⟶ R') (ρ : A ⟶ B) (σ : R' ⟶ B)
    (h : CategoryTheory.IsPushout φ ψ ρ σ) (M : ModuleCat.{u} A) :
    (Scheme.Modules.pullback (Spec.map ψ)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)) ≅
      (Scheme.Modules.pushforward (Spec.map σ)).obj
        ((Scheme.Modules.pullback (Spec.map ρ)).obj (tilde M))
```
Supporting module core `baseChangeCancelModuleIso` (FlatBaseChange.lean line 765): `extendScalars_ψ (restrictScalars_φ M) ≅ restrictScalars_σ (extendScalars_ρ M)`, i.e. `R' ⊗_R M ≅ restrict_σ(B ⊗_A M)`, via `Algebra.IsPushout.cancelBaseChange` + `CommRingCat.isPushout_iff_isPushout`. `cech_degree_affine_baseChange` (Cech file line 361) is a thin re-export of `affinePushforwardPullbackBaseChange`.

Full per-σ assembly: `pushPullObj_coverInter_baseChange_spec` — line 1525 (chains LHS→tilde, `affinePushforwardPullbackBaseChange` for `coverInter_ring_isPushout`, the tensor rewrite, RHS→tilde).

---

## 4. `pullback_isQuasicoherent` in PullbackQuasicoherent.lean

File: `AlgebraicJacobian/Cohomology/PullbackQuasicoherent.lean`. The declaration there is named **`pullback_isQuasicoherent_hom`** (general-morphism case; there is no bare `pullback_isQuasicoherent` in this file — that name is the open-case re-export in the Cech file, §2). Line 160. Doc: "Pullback preserves quasi-coherence (Stacks 01BG, general-morphism case): for any `g : Y ⟶ X` and quasi-coherent `F`, `g^* F` is quasi-coherent; via `IsQuasicoherent.of_coversTop` on the preimage cover + `presentationPullbackSliceOfOver`."
```lean
theorem pullback_isQuasicoherent_hom {Y X : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pullback g).obj F).IsQuasicoherent
```
(Preceded by `set_option backward.isDefEq.respectTransparency false`, `synthInstance.maxHeartbeats 1000000`, `maxHeartbeats 2000000`.) Supporting in same file: `pullbackUnitIso` (line 88), `presentationPullbackSliceOfOver` (line 109).

---

## 5. `Scheme.Modules.pullbackComp / pullbackCongr / restrictFunctorIsoPullback / pullbackUnitIso`

The first three are **Mathlib**, file `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`, in `namespace Scheme.Modules` with `variable {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) …`:

`pullbackComp` — line 232:
```lean
def pullbackComp : pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  SheafOfModules.pullbackComp _ _
```
`pullbackCongr` — line 248:
```lean
def pullbackCongr {f g : X ⟶ Y} (hf : f = g) : pullback f ≅ pullback g := eqToIso (hf ▸ rfl)
```
`restrictFunctorIsoPullback` — line 421:
```lean
def restrictFunctorIsoPullback : restrictFunctor f ≅ pullback f :=
  (restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)
```
(companions: `pushforwardComp` line 223, `pushforwardCongr` line 237, `pushforwardId` line 203, `pullbackId` line 212, `pullbackPushforwardAdjunction` line 185.)

`pullbackUnitIso` is **project-local**, `AlgebraicJacobian/Cohomology/PullbackQuasicoherent.lean` line 88:
```lean
noncomputable def pullbackUnitIso {Y X : Scheme.{u}} (g : Y ⟶ X) :
    (Scheme.Modules.pullback g).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  @asIso _ _ _ _ _ (pullbackObjUnitToUnit_isIso_hom g)
```
(There is no `Scheme.Modules.pullbackUnitIso`; the Mathlib primitive it wraps is `SheafOfModules.pullbackObjUnitToUnit`.)

Two other iso-transport helpers used above, both project-local:
- `Scheme.Modules.pushforwardEquivOfIso` — `AlgebraicJacobian/Cohomology/OpenImmersionPushforward.lean` line 204: `(φ : X ≅ Y) : X.Modules ≌ Y.Modules`.
- `Scheme.Modules.pullbackIsoPushforwardInv` — `AlgebraicJacobian/Cohomology/AffinePushPullEssImage.lean` line 57: `(e : X ≅ Y) : pullback e.hom ≅ pushforward e.inv`.

---

## 6. Sections of a pullback module sheaf (module/ring identification via tensor products)

The main declaration is in `AlgebraicJacobian/Picard/QuotScheme.lean`:

**`pullback_app_isoTensor_baseMap_sectionLinearEquiv`** — line 4645. Doc: "For quasi-coherent `N` and affine `U ≤ g⁻¹V`, `Γ((pullback g).obj N, U) ≅ Γ(Y,U) ⊗_{Γ(X,V)} Γ(N,V)` as a `Γ(Y,U)`-linear equivalence, intertwining `1 ⊗ x` with `pullback_app_isoTensor_baseMap`."
```lean
theorem pullback_app_isoTensor_baseMap_sectionLinearEquiv
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules) [N.IsQuasicoherent]
    {U : Y.Opens} {V : X.Opens}
    (_hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (e : U ≤ g ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Y, U) := (g.appLE V U e).hom.toAlgebra
    letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj N, U) :=
      Module.compHom _ (g.appLE V U e).hom
    Nonempty {f : TensorProduct Γ(X, V) Γ(Y, U) Γ(N, V) ≃ₗ[Γ(Y, U)]
                Γ((Scheme.Modules.pullback g).obj N, U) //
      ∀ x : Γ(N, V),
        f (1 ⊗ₜ[Γ(X, V)] x) = pullback_app_isoTensor_baseMap g N e x}
```
Companion linear map `pullback_app_isoTensor_baseMap` — line 353: `Γ(N, V) →ₗ[Γ(X, V)] Γ((pullback g).obj N, U)` (built from the adjunction unit `pullback_app_isoTensor_unitAtV` line 321, post-composed with the presheaf restriction).

Downstream consumer giving the matrix-presentation base change:
**`exists_matrixPresentation_pullback_sections`** — `AlgebraicJacobian/Picard/FlatteningStratificationUniversal.lean` line 111. Doc: "The section module `Γ(g^*G, W)` admits a presentation whose relation matrix is `P.relMatrix.map (g.appLE V W e)` — the base change of a presentation of `Γ(G, V)`."
```lean
theorem exists_matrixPresentation_pullback_sections
    {V : X.Opens} (hV : IsAffineOpen V) {W : Y.Opens} (hW : IsAffineOpen W)
    (e : W ≤ g ⁻¹ᵁ V) {ee mm : ℕ}
    (P : MatrixPresentation Γ(X, V) Γ(G, V) ee mm) :
    ∃ P' : MatrixPresentation Γ(Y, W)
      Γ((Scheme.Modules.pullback g).obj G, W) ee mm,
      P'.relMatrix = P.relMatrix.map (g.appLE V W e).hom
```
(The `Γ((pullback g).obj G, W)`-as-`Module Γ(X,V)` structure is `Module.compHom _ (g.appLE V W e).hom` throughout, e.g. lines 118-120.)

The four-corner ring pushout on section rings (Beck–Chevalley on sections) is in `AlgebraicJacobian/Picard/GenericFlatnessGeometric.lean`:
**`isPushout_appLE_pullback_piece`** — line 733:
```lean
theorem isPushout_appLE_pullback_piece (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsAffineOpen UX) :
    CategoryTheory.IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST)
      (g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left)
      (iY.appLE UT (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_right)
```
(via Mathlib `isIso_pushoutSection_of_isAffineOpen` + `isIso_pushoutSection_iff`). Consumed by `flat_section_pullback_piece` (line 748), which passes through `CommRingCat.isPushout_iff_isPushout` to `Algebra.IsPushout`.

---

## 7. `Scheme.Modules.pullback` (Mathlib)

File `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`, `namespace Scheme.Modules`, `variable (f : X ⟶ Y)`, line 180. Doc: "The pullback functor for categories of sheaves of modules over schemes."
```lean
def pullback : Y.Modules ⥤ X.Modules :=
  SheafOfModules.pullback f.toRingCatSheafHom
```
`tilde` and `moduleSpecΓFunctor` (from §1) are in `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`, `variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)`:
```lean
noncomputable def moduleSpecΓFunctor : (Spec (.of R)).Modules ⥤ ModuleCat R :=          -- line 48
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤)
def tilde : (Spec R).Modules where …                                                     -- line 147
@[simps] protected noncomputable def tilde.functor : ModuleCat R ⥤ (Spec (.of R)).Modules -- line 227
def tilde.adjunction : tilde.functor R ⊣ moduleSpecΓFunctor                               -- line 335
```

---

## 8. `IsAffineOpen` preimage / intersection lemmas

Mathlib `Mathlib/AlgebraicGeometry/Morphisms/Affine.lean`:
- `IsAffineOpen.preimage` — line 50: `(hU : IsAffineOpen U) (f : X ⟶ Y) [IsAffineHom f] : IsAffineOpen (f ⁻¹ᵁ U)`.
- `IsAffineOpen.inf` — line ~327: `(hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V)` (needs `IsAffineHom (pullback.diagonal (terminal.from X))`).
- `IsAffineOpen.iInf` — line 331: `[IsAffineHom (pullback.diagonal (terminal.from X))] {ι} [Finite ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i)) : IsAffineOpen (⨅ i, U i)`. (Also `biInf` line 336.)

Mathlib `Mathlib/AlgebraicGeometry/AffineScheme.lean` (namespace `IsAffineOpen`):
- `preimage_of_isIso` — line 518: `(hU : IsAffineOpen U) (f : X ⟶ Y) [IsIso f] : IsAffineOpen (f ⁻¹ᵁ U)`.
- `preimage_of_isOpenImmersion` — line 523: `(hU : IsAffineOpen U) (f : X ⟶ Y) [IsOpenImmersion f] (hU' : U ≤ f.opensRange) : IsAffineOpen (f ⁻¹ᵁ U)`.
- `isAffineOpen_opensRange` — line 261 (`[IsAffine X] (f : X ⟶ Y) [IsOpenImmersion f] : IsAffineOpen f.opensRange`).

**How the project shows `P = g'⁻¹V ⊓ f'⁻¹U''` is affine.** The exact shape appears in `AlgebraicJacobian/Picard/GenericFlatnessGeometric.lean`:
**`isAffineOpen_pullback_piece`** — line 723. Doc: "The piece `g⁻¹UX ⊓ iY⁻¹UT` of a fibre-product square over affine opens is affine: it is isomorphic to the pullback of the restricted affine cospan (`Scheme.Hom.isPullback_resLE`)."
```lean
theorem isAffineOpen_pullback_piece (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsAffineOpen UX) : IsAffineOpen (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) := by
  have : IsAffine US := hUS
  have : IsAffine UT := hUT
  have : IsAffine UX := hUX
  exact IsAffine.of_isIso (Scheme.Hom.isPullback_resLE H hUST hUSX rfl).isoPullback.hom
```
(i.e. it is proved by exhibiting the intersection as the pullback of restricted affines and using `IsAffine.of_isIso` on the `isoPullback`, rather than via `IsAffineOpen.preimage`.) In the Čech route (`CechHigherDirectImageUnconditional.lean`) the corner affineness is instead obtained from `coverInterOpen_isAffine` (§3b) applied to `f'` and the pushed-forward cover, since there the corner is the base-changed intersection open `V'_σ`.
