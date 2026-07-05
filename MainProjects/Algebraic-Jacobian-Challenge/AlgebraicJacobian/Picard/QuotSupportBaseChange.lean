/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.QuotScheme
import AlgebraicJacobian.Cohomology.PullbackQuasicoherent
import AlgebraicJacobian.Picard.PullbackFinitePresentation

/-!
# Proper support is stable under base change

This file proves `AlgebraicGeometry.Scheme.Modules.HasProperSupport.of_isPullback`
(`lem:proper_support_base_change`): for a cartesian square

```
  X' --g'--> X
  |f'        |f
  v          v
  S' --g---> S
```

and a finitely presented sheaf of modules `F` on `X` whose schematic support is
proper over `S`, the schematic support of `g'^* F` is proper over `S'`
(Nitsure §1; Stacks 01W4, 056H).

## Proof layout

1. **Annihilators pull back** (`map_app_mem_annihilator_pullback`): a section `r`
   of `𝒪_X` over an affine open `U` annihilating `Γ(F, U)` pulls back to a section
   annihilating `Γ(g'^* F, V')` for every open `V' ≤ g'⁻¹ U`.  The engine is a
   purely categorical smul-transport: scalar multiplication by a global section
   `w` is an endomorphism `smulGlobal M w : M ⟶ M` of the sheaf of modules, the
   pullback functor intertwines it with `smulGlobal (g'^* M) (g'♯ w)`
   (`pullback_map_smulGlobal`, an adjoint-transpose computation along
   `pullbackPushforwardAdjunction`), and on an affine scheme `smulGlobal M w`
   vanishes as soon as `w` kills global sections (`smulGlobal_eq_zero_of_isAffine`,
   by the quasi-coherent basic-open localization `isLocalizedModule_basicOpen`
   plus sheaf separation).  No tilde/tensor dictionary is needed.
2. **Finite sections at every affine open**
   (`module_finite_sections_of_isFinitePresentation`): for a finitely presented
   `F`, the section module `Γ(F, V)` is finite over `Γ(X, V)` for *every* affine
   open `V` (Stacks 01PC): finite generation is supplied on a basic-open cover by
   `exists_affine_finite_sections_nhds` and glued by
   `Module.Finite.of_localizationSpan'`.
3. **Ideal-sheaf inclusion** (`annihilator_le_map_pullback`):
   `annihilator F ≤ (annihilator (g'^* F)).map g'`, i.e. the annihilator of `F`
   is killed by `𝒪_X → (ι')_* 𝒪_{Z'} → (ι' ≫ g')_* 𝒪` where
   `ι' : Z' = supp (g'^* F) ⟶ X'`.  Pointwise on affines this is step 1 combined
   with the characterization `annihilator_ideal` (which consumes step 2) and
   `ker_subschemeι_app`, assembled by sheaf separation on `Z'`.
4. **Assembly**: step 3 yields a morphism `l : Z' ⟶ Z = supp F` over `g'`
   (`IdealSheafData.subschemeMap`).  With `W := Z ×_S S'`, the comparison
   `m : W ⟶ X'` is a closed immersion (base change of `ι : Z ⟶ X` along `g'`,
   by pasting `IsPullback.of_bot`), the induced `c : Z' ⟶ W` satisfies
   `c ≫ m = ι'`, hence `c` is proper (`IsProper.of_comp`), and
   `ι' ≫ f' = c ≫ pullback.snd (ι ≫ f) g` is proper because properness is
   stable under base change and composition.

## References

Blueprint: `lem:proper_support_base_change`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Nitsure], §1 (FGA Explained Ch. 5, arXiv:math/0504020); Stacks 01W4
(properness is stable under base change), 056H (scheme-theoretic support).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

variable {X : Scheme.{u}}

/-! ## §1. Scalar multiplication by a global section, and its pullback

The endomorphism `smulGlobal M w : M ⟶ M` of a sheaf of modules given by scalar
multiplication with a global section `w` of the structure sheaf, and the
transport `pullback_map_smulGlobal`: the pullback functor sends `smulGlobal M w`
to `smulGlobal (f^* M) (f♯ w)`.  The latter is proved by an adjoint-transpose
computation: under `pullbackPushforwardAdjunction` both sides correspond to the
same morphism `M ⟶ f_* f^* M`, because the adjunction unit is `𝒪`-linear and
the module structure of the pushforward is restriction of scalars along `f♯`. -/

/-- Restriction of structure-sheaf sections collapses under composition. -/
private lemma resRing_res {A B C : X.Opens} (hBA : B ≤ A) (i : C ⟶ B)
    (hCA : C ≤ A) (w : Γ(X, A)) :
    X.presheaf.map i.op (X.presheaf.map (homOfLE hBA).op w)
      = X.presheaf.map (homOfLE hCA).op w := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun (k : C ⟶ A) => X.presheaf.map k.op w) (Subsingleton.elim _ _)

/-- Restriction of module sections collapses under composition. -/
private lemma res_res (M : X.Modules) {A B C : X.Opens} (hBA : B ≤ A) (i : C ⟶ B)
    (hCA : C ≤ A) (x : Γ(M, A)) :
    M.presheaf.map i.op (M.presheaf.map (homOfLE hBA).op x)
      = M.presheaf.map (homOfLE hCA).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun (k : C ⟶ A) => M.presheaf.map k.op x) (Subsingleton.elim _ _)

/-- The identity restriction acts as the identity on module sections. -/
private lemma res_self (M : X.Modules) {A : X.Opens} (h : A ≤ A) (x : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op x = x := by
  rw [Subsingleton.elim (homOfLE h) (𝟙 A), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **Scalar multiplication by a global section**, as an endomorphism of a sheaf
of modules: for `w : Γ(X, ⊤)` the components of `smulGlobal M w` are
`t ↦ (w|_U) • t`.  Naturality is `map_comp_smul` (restriction is semilinear),
and each component is linear because the section rings are commutative.
Project-local: Mathlib carries the sections-level `Scheme.Modules.smul` but not
the sheaf-level endomorphism. -/
noncomputable def smulGlobal (M : X.Modules) (w : Γ(X, ⊤)) : M ⟶ M where
  val := PresheafOfModules.homMk
    { app := fun U => M.smul (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op w)
      naturality := fun {U V} i => by
        have h := (Scheme.Modules.map_comp_smul (M := M) (i := i.unop)
          (r := X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op w)).symm
        rw [resRing_res (le_top : U.unop ≤ ⊤) i.unop (le_top : V.unop ≤ ⊤) w] at h
        simpa using h.symm }
    (fun U r m => by
      show X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op w • (r • m)
        = r • (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op w • m)
      rw [smul_smul, smul_smul, mul_comm])

@[simp]
lemma smulGlobal_app_apply (M : X.Modules) (w : Γ(X, ⊤)) (U : X.Opens) (t : Γ(M, U)) :
    (smulGlobal M w).app U t = X.presheaf.map (homOfLE le_top).op w • t := rfl

/-- The module structure on sections of the pushforward is restriction of scalars
along `h♯`: for `a : Γ(Y, O)` and a section `y` of `(pushforward h).obj K` over
`O` — which is definitionally a section of `K` over `h⁻¹ O` — the action of `a`
is the action of `h.app O a`. -/
lemma pushforward_smul_apply {X Y : Scheme.{u}} (h : X ⟶ Y) (K : X.Modules) (O : Y.Opens)
    (a : Γ(Y, O)) (y : Γ((Scheme.Modules.pushforward h).obj K, O)) :
    a • y = ((h.app O a • (y : Γ(K, h ⁻¹ᵁ O))) : Γ(K, h ⁻¹ᵁ O)) := rfl

/-- Compatibility of `app` with top-restriction: restricting a global section
along `h` and then to `h⁻¹ O` agrees with applying `h.app O` to the restriction. -/
private lemma app_res_top {X Y : Scheme.{u}} (h : X ⟶ Y) (O : Y.Opens) (w : Γ(Y, ⊤)) :
    h.app O (Y.presheaf.map (homOfLE le_top).op w)
      = X.presheaf.map (homOfLE le_top).op (h.appTop w) := by
  have hnat := congr($(h.naturality ((homOfLE (le_top : O ≤ ⊤)).op)) w)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hnat
  rw [hnat]
  show X.presheaf.map ((Opens.map h.base).map (homOfLE le_top)).op (h.appTop w) = _
  exact congrArg (fun (k : h ⁻¹ᵁ O ⟶ (⊤ : X.Opens)) => X.presheaf.map k.op (h.appTop w))
    (Subsingleton.elim _ _)

/-- **The pullback functor intertwines scalar multiplication by global sections**:
`f^*(w • 𝟙_M) = (f♯ w) • 𝟙_{f^* M}`.  Proof by adjoint transpose along
`pullbackPushforwardAdjunction`: both sides transpose to the same morphism
`M ⟶ f_* f^* M` because the adjunction unit is a morphism of `𝒪_Y`-modules
(`Hom.app_smul`) and the `𝒪_Y`-module structure of the pushforward is
restriction of scalars along `f♯` (`pushforward_smul_apply`).  This is the
categorical heart of annihilator base change — no affine dictionary is used. -/
theorem pullback_map_smulGlobal {X Y : Scheme.{u}} (h : X ⟶ Y) (M : Y.Modules)
    (w : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback h).map (smulGlobal M w)
      = smulGlobal ((Scheme.Modules.pullback h).obj M) (h.appTop w) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv M
    ((Scheme.Modules.pullback h).obj M)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hnat := ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.naturality
    (smulGlobal M w)).symm
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hnat
  rw [hnat]
  ext O t
  show ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).app O
      ((smulGlobal M w).app O t)
    = ((Scheme.Modules.pushforward h).map
        (smulGlobal ((Scheme.Modules.pullback h).obj M) (h.appTop w))).app O
      (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).app O t)
  rw [smulGlobal_app_apply, Scheme.Modules.Hom.app_smul]
  rw [pushforward_smul_apply h _ O]
  rw [app_res_top]
  rfl

/-- If `smulGlobal M w = 0` then `w` kills every section of `f^* M` after
restriction along `f`. -/
theorem smulGlobal_pullback_eq_zero {X Y : Scheme.{u}} (h : X ⟶ Y) (M : Y.Modules)
    (w : Γ(Y, ⊤)) (hw : smulGlobal M w = 0) :
    smulGlobal ((Scheme.Modules.pullback h).obj M) (h.appTop w) = 0 := by
  rw [← pullback_map_smulGlobal, hw, Functor.map_zero]

/-! ## §2. Annihilation of all sections on an affine scheme

On an affine scheme, a global section of `𝒪` annihilating the global sections of
a quasi-coherent module annihilates all its sections: on basic opens because
sections there are localizations of the global sections
(`isLocalizedModule_basicOpen`, Stacks 01P0/01I8), in general by sheaf
separation over the basic-open basis. -/

private lemma smul_res_basicOpen_eq_zero [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] (w : Γ(X, ⊤)) (hw : ∀ t : Γ(M, ⊤), w • t = 0)
    (b : Γ(X, ⊤)) (y : Γ(M, X.basicOpen b)) :
    X.presheaf.map (homOfLE le_top).op w • y = 0 := by
  haveI := (isAffineOpen_top X).isLocalization_basicOpen b
  letI : Module Γ(X, ⊤) Γ(M, X.basicOpen b) :=
    Module.compHom _ (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen b))
  haveI : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen b) Γ(M, X.basicOpen b) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI := isLocalizedModule_basicOpen M (isAffineOpen_top X) b
  obtain ⟨⟨x, s⟩, hx⟩ :=
    IsLocalizedModule.surj (Submonoid.powers b) (restrictBasicOpenₗ M b) y
  -- multiplying the target by the denominator lands in the image of a global section
  have hz : (s : Γ(X, ⊤)) • (X.presheaf.map (homOfLE le_top).op w • y) = 0 := by
    have hcomm : (s : Γ(X, ⊤)) • (X.presheaf.map (homOfLE le_top).op w • y)
        = X.presheaf.map (homOfLE le_top).op w • ((s : Γ(X, ⊤)) • y) := by
      rw [← algebraMap_smul Γ(X, X.basicOpen b) (s : Γ(X, ⊤))
          (X.presheaf.map (homOfLE le_top).op w • y),
        ← algebraMap_smul Γ(X, X.basicOpen b) (s : Γ(X, ⊤)) y,
        smul_smul, smul_smul, mul_comm]
    rw [hcomm, hx]
    show X.presheaf.map (homOfLE le_top).op w
        • M.presheaf.map (homOfLE (X.basicOpen_le b)).op x = 0
    rw [← Scheme.Modules.map_smul, hw x, map_zero]
  -- the denominator acts invertibly on the localized sections
  have hu := IsLocalizedModule.map_units (S := Submonoid.powers b)
    (restrictBasicOpenₗ M b) s
  rw [Module.End.isUnit_iff] at hu
  apply hu.injective
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, hz, smul_zero]

/-- **Global annihilation implies local annihilation on an affine scheme**
(Stacks 01P0 applied to the annihilator): if `w : Γ(X, 𝒪)` kills the global
sections of a quasi-coherent module `M` on an affine scheme, it kills all
sections of `M`.  On basic opens this is the section localization
`isLocalizedModule_basicOpen`; the general case follows by separation of the
underlying abelian sheaf over the basic-open basis. -/
theorem smul_res_eq_zero_of_isAffine [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] (w : Γ(X, ⊤)) (hw : ∀ t : Γ(M, ⊤), w • t = 0)
    (O : X.Opens) (t : Γ(M, O)) :
    X.presheaf.map (homOfLE le_top).op w • t = 0 := by
  let 𝒰 : {b : Γ(X, ⊤) // X.basicOpen b ≤ O} → X.Opens := fun i => X.basicOpen i.1
  have hcover : O ≤ iSup 𝒰 := by
    intro x hx
    obtain ⟨b, hble, hxb⟩ := (isAffineOpen_top X).exists_basicOpen_le
      (⟨x, hx⟩ : O) (by trivial)
    exact Opens.mem_iSup.mpr ⟨⟨b, hble⟩, hxb⟩
  let S : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  refine S.eq_of_locally_eq' 𝒰 O (fun i => homOfLE i.2) hcover
    (X.presheaf.map (homOfLE le_top).op w • t) 0 (fun i => ?_)
  show M.presheaf.map (homOfLE i.2).op (X.presheaf.map (homOfLE le_top).op w • t)
    = M.presheaf.map (homOfLE i.2).op 0
  rw [map_zero, Scheme.Modules.map_smul,
    resRing_res (le_top : O ≤ ⊤) (homOfLE i.2) le_top w]
  exact smul_res_basicOpen_eq_zero M w hw i.1 (M.presheaf.map (homOfLE i.2).op t)

/-- Endomorphism form of `smul_res_eq_zero_of_isAffine`. -/
theorem smulGlobal_eq_zero_of_isAffine [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] (w : Γ(X, ⊤)) (hw : ∀ t : Γ(M, ⊤), w • t = 0) :
    smulGlobal M w = 0 := by
  ext U t
  rw [smulGlobal_app_apply, Scheme.Modules.Hom.zero_app]
  exact smul_res_eq_zero_of_isAffine M w hw U t

/-! ## §3. Annihilators pull back -/

/-- Annihilation transports across an equality of opens. -/
private lemma smul_res_eqToHom_eq_zero {Z : Scheme.{u}} (N : Z.Modules)
    {A B : Z.Opens} (hAB : A = B) {a : Γ(Z, B)}
    (ha : ∀ s : Γ(N, B), a • s = 0) (m : Γ(N, A)) :
    Z.presheaf.map (eqToHom hAB).op a • m = 0 := by
  subst hAB
  simpa using ha m

/-- `appLE` is invariant under an equality of morphisms. -/
private lemma appLE_eq_appLE_of_eq {A B : Scheme.{u}} {f₁ f₂ : A ⟶ B} (hf : f₁ = f₂)
    (O : B.Opens) (W : A.Opens) (e : W ≤ f₁ ⁻¹ᵁ O) :
    f₁.appLE O W e = f₂.appLE O W (hf ▸ e) := by
  subst hf; rfl

/-- **Annihilators are stable under pullback** (Stacks 056H, section level; the
heart of `lem:proper_support_base_change`).  Let `g' : X' ⟶ X`, let `F` be a
quasi-coherent sheaf of modules on `X`, `U` an affine open of `X` and
`V' ≤ g'⁻¹ U` any open of `X'`.  If `r ∈ Ann_{Γ(X,U)} Γ(F, U)`, then the image
of `r` in `Γ(X', V')` annihilates `Γ(g'^* F, V')`.

The proof runs entirely through the smul-endomorphism transport: `r` induces the
zero endomorphism of `F|_U` (`smulGlobal_eq_zero_of_isAffine`, using
quasi-coherence of the restriction), the pullback functor along
`g'.resLE U V' : V' ⟶ U` sends it to the smul endomorphism of the corresponding
restriction of `g'^* F` (`pullback_map_smulGlobal` plus the pseudofunctor
comparisons `pullbackComp`/`pullbackCongr`), and section transport along the
open immersions is `gammaPullbackImageIso` with its semilinearity. -/
theorem map_app_mem_annihilator_pullback {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] (U : X.affineOpens) {V' : X'.Opens}
    (hle : V' ≤ g' ⁻¹ᵁ U.1) {r : Γ(X, U.1)}
    (hr : r ∈ Module.annihilator Γ(X, U.1) Γ(F, U.1)) :
    X'.presheaf.map (homOfLE hle).op (g'.app U.1 r)
      ∈ Module.annihilator Γ(X', V') Γ((Scheme.Modules.pullback g').obj F, V') := by
  haveI : IsAffine U.1.toScheme := U.2
  haveI hGqc : ((Scheme.Modules.pullback U.1.ι).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent_hom U.1.ι F ‹_›
  -- the image identifications
  have himgU : U.1.ι ''ᵁ ⊤ = U.1 := Scheme.Opens.ι_image_top U.1
  have himgV : V'.ι ''ᵁ ⊤ = V' := Scheme.Opens.ι_image_top V'
  -- the transported annihilating section on the affine open subscheme
  set r₀ : Γ(U.1.toScheme, ⊤) := (gammaImageRingEquiv U.1.ι ⊤).symm
    (X.presheaf.map (eqToHom himgU).op r) with hr₀
  -- `r₀` kills the global sections of the restriction of `F`
  have hw : ∀ t : Γ((Scheme.Modules.pullback U.1.ι).obj F, ⊤), r₀ • t = 0 := by
    intro t
    have hinj : Function.Injective ⇑((gammaPullbackImageIso U.1.ι F ⊤).hom) :=
      (gammaPullbackImageIso U.1.ι F ⊤).addCommGroupIsoToAddEquiv.injective
    apply hinj
    rw [map_zero, gammaPullbackImageIso_hom_semilinear, hr₀,
      RingEquiv.apply_symm_apply]
    exact smul_res_eqToHom_eq_zero F himgU
      (fun s => Module.mem_annihilator.mp hr s)
      ((gammaPullbackImageIso U.1.ι F ⊤).hom t)
  -- hence the smul endomorphism vanishes on the affine restriction …
  have hz : smulGlobal ((Scheme.Modules.pullback U.1.ι).obj F) r₀ = 0 :=
    smulGlobal_eq_zero_of_isAffine _ r₀ hw
  -- … and pulls back to zero along the restriction of `g'`
  set h : V'.toScheme ⟶ U.1.toScheme := g'.resLE U.1 V' hle with hh
  have hz' : smulGlobal
      ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback U.1.ι).obj F))
      (h.appTop r₀) = 0 :=
    smulGlobal_pullback_eq_zero h _ r₀ hz
  -- identify the pulled-back module with the restriction of `g'^* F`
  have hcomp : h ≫ U.1.ι = V'.ι ≫ g' := Scheme.Hom.resLE_comp_ι g' hle
  let e : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback U.1.ι).obj F)
      ≅ (Scheme.Modules.pullback V'.ι).obj ((Scheme.Modules.pullback g').obj F) :=
    (Scheme.Modules.pullbackComp h U.1.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app F ≪≫
      ((Scheme.Modules.pullbackComp V'.ι g').app F).symm
  -- `h♯ r₀` kills the global sections of the restriction of `g'^* F`
  have hann : ∀ t : Γ((Scheme.Modules.pullback V'.ι).obj
      ((Scheme.Modules.pullback g').obj F), ⊤), h.appTop r₀ • t = 0 := by
    intro t
    have h1 : h.appTop r₀ • e.inv.app ⊤ t = 0 := by
      have h0 := congrArg (fun (φ : (Scheme.Modules.pullback h).obj
          ((Scheme.Modules.pullback U.1.ι).obj F) ⟶ _) => φ.app ⊤ (e.inv.app ⊤ t)) hz'
      simp only [smulGlobal_app_apply, Scheme.Modules.Hom.zero_app] at h0
      rw [res_self _ le_top (h.appTop r₀)] at h0
      simpa using h0
    have h2 : e.hom.app ⊤ (e.inv.app ⊤ t) = t := by
      rw [← Scheme.Modules.Hom.comp_app_apply?]
      sorry
    sorry
  sorry

end Modules

end Scheme

end AlgebraicGeometry
