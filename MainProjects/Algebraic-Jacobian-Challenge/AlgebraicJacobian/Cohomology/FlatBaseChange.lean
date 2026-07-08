/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/- USER (2026-06-29): TWO standing directives for this file.
   (A) FBC PIVOT — prove flat base change via the ČECH-TO-COHOMOLOGY SPECTRAL SEQUENCE, not the
       walled mate-calculus naturality (`pullbackSpecTildeNatIso_comp` /
       `pushforwardPullbackBaseChange_restrict_naturality`). Build the relative SS
       `E₂^{p,q}=Ȟ^p(𝒰,R^q f_*F) ⟹ R^{p+q}f_*F` (Stacks 01EO/03OW, Cohomology 20.11.5) on Mathlib's
       `Algebra.Homology.SpectralObject.*` / `SpectralSequence.Basic` / `TotalComplex` scaffold; use its
       base-change functoriality to close `cech_flatBaseChange` (02KH), then Kleiman 4.8
       (`Scheme.PicScheme.representable`). Full plan + anchors: `.archon/USER_HINTS.md` temporary hint.
   (B) Mate-calc chain deleted iter-312 in favor of the SS route; the two canonical-mate stubs
       (`affineBaseChange_pushforward_iso`, `flatBaseChange_pushforward_isIso`) were pruned in
       run 0009 (superseded, zero consumers — the live route is the concrete-tilde
       `affinePushforwardPullbackBaseChange` consumed by `cech_flatBaseChange`).
       This file is now sorry-free. -/

/-!
# Flat base change for the pushforward of a quasi-coherent sheaf (`i = 0`)

This file establishes the `i = 0` (direct-image) case of flat base change: the
formation of the pushforward `f_* F` of a quasi-coherent sheaf commutes with flat
base change on the target.

Throughout we work with a (commutative, eventually cartesian) square of schemes
```
  X' --g'--> X
  |f'        |f
  v          v
  S' --g---> S
```
recorded by morphisms `f : X ⟶ S`, `g : S' ⟶ S`, `f' : X' ⟶ S'`, `g' : X' ⟶ X`
with `g' ≫ f = f' ≫ g`, and `F : X.Modules` a sheaf of modules on `X`.

The main declarations are:

* `AlgebraicGeometry.pushforwardBaseChangeMap` — the canonical base-change map
  `g^*(f_* F) ⟶ f'_*((g')^* F)`, built as the adjoint mate of the unit of the
  `((g')^*, (g')_*)`-adjunction (kept for reference; the live route never forms
  this mate).
* `AlgebraicGeometry.affinePushforwardPullbackBaseChange` — the concrete-tilde
  affine base-change isomorphism for a ring pushout square, assembled from the
  tilde dictionaries and `cancelBaseChange`; this is the brick consumed by the
  Čech route to Stacks 02KH (`cech_flatBaseChange` in
  `Cohomology/CechHigherDirectImageUnconditional.lean`).

See `blueprint/src/chapters/Cohomology_FlatBaseChange.tex`.

Source: Stacks Project, Cohomology of Schemes, §"Cohomology and base change, I",
Tag 02KH.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

variable {S S' X X' : Scheme.{u}}
  (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)

/-- The canonical base-change map for the pushforward of a sheaf of modules.

Given a commutative square
```
  X' --g'--> X
  |f'        |f
  v          v
  S' --g---> S
```
(with `comm : g' ≫ f = f' ≫ g`) and a sheaf of modules `F` on `X`, this is the
canonical morphism `g^*(f_* F) ⟶ f'_*((g')^* F)` of sheaves of modules on `S'`.

It is the image, under the `(g^*, g_*)`-adjunction transpose, of the composite
```
  f_* F --f_*(unit)--> f_* (g')_* (g')^* F
        = (g' ≫ f)_* (g')^* F = (f' ≫ g)_* (g')^* F = g_* f'_* (g')^* F,
```
where `unit` is the unit of the `((g')^*, (g')_*)`-adjunction and the middle
equalities are the pseudofunctoriality of pushforward together with the
commutativity of the square.

Source: Stacks Project, Cohomology of Schemes, §"Cohomology and base change, I",
base-change diagram. -/
noncomputable def pushforwardBaseChangeMap (comm : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (Scheme.Modules.pullback g).obj ((pushforward f).obj F) ⟶
      (pushforward f').obj ((Scheme.Modules.pullback g').obj F) :=
  ((pullbackPushforwardAdjunction g).homEquiv _ _).symm
    ((pushforward f).map ((pullbackPushforwardAdjunction g').unit.app F) ≫
      (pushforwardComp g' f).hom.app _ ≫
      (pushforwardCongr comm).hom.app _ ≫
      (pushforwardComp f' g).inv.app _)

/-! ## Project-local Mathlib supplement — locality of isomorphisms for `Scheme.Modules`

Mathlib provides the per-open criterion `Scheme.Modules.Hom.isIso_iff_isIso_app`
(`IsIso φ ↔ ∀ U, IsIso (φ.app U)`) and the stalkwise criterion
`TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` for `TopCat.Sheaf`-valued morphisms,
but it does not package the stalk-local criterion at the level of `Scheme.Modules`
morphisms. The following lemmas bridge that gap; they are the locality tools needed for
the affine reduction of `affineBaseChange_pushforward_iso` (where one checks the
base-change map after restricting to / taking stalks over affine opens). -/

/-- **Stalk-local criterion for isomorphisms of `𝒪_X`-modules.** A morphism `φ : M ⟶ N`
of sheaves of modules over a scheme `X` is an isomorphism iff its underlying morphism of
abelian presheaves is a stalkwise isomorphism. Project-local: Mathlib only ships the
per-open criterion and the `TopCat.Sheaf`-level stalk criterion separately. -/
theorem Modules.isIso_iff_isIso_stalkFunctor_map {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) :
    IsIso φ ↔ ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((Scheme.Modules.toPresheaf X).map φ)) := by
  constructor
  · intro h x
    haveI : IsIso ((Scheme.Modules.toPresheaf X).map φ) := Functor.map_isIso _ _
    exact Functor.map_isIso _ _
  · intro h
    -- Package the underlying abelian presheaves as `TopCat.Sheaf`es.
    let MS : TopCat.Sheaf Ab.{u} X := ⟨M.presheaf, M.isSheaf⟩
    let NS : TopCat.Sheaf Ab.{u} X := ⟨N.presheaf, N.isSheaf⟩
    let fS : MS ⟶ NS := ⟨(Scheme.Modules.toPresheaf X).map φ⟩
    haveI : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map fS.hom) := h
    haveI hSiso : IsIso fS := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso fS
    have h1 : IsIso ((Scheme.Modules.toPresheaf X).map φ) :=
      (TopCat.Sheaf.forget Ab.{u} X).map_isIso fS
    exact (CategoryTheory.isIso_iff_of_reflects_iso φ (Scheme.Modules.toPresheaf X)).mp h1

/-- **Basis-local criterion for isomorphisms of `𝒪_X`-modules.** If `B` is a basis of
opens of `X` and `φ : M ⟶ N` restricts to an isomorphism on the sections over every basic
open `B i`, then `φ` is an isomorphism. This reduces iso-checking from *all* opens (the
content of `Scheme.Modules.Hom.isIso_iff_isIso_app`) to a chosen basis. Project-local:
Mathlib provides the stalkwise pieces (`germ_exist_of_isBasis`,
`stalkFunctor_map_injective_of_isBasis`) but not the packaged criterion at the
`Scheme.Modules` level. -/
theorem Modules.isIso_of_isIso_app_of_isBasis {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type*} {B : ι → X.Opens} (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    (φ : M ⟶ N) (h : ∀ i, IsIso (φ.app (B i))) : IsIso φ := by
  -- Reduce to a stalkwise isomorphism of the underlying `Ab`-presheaf morphism `α`.
  rw [Modules.isIso_iff_isIso_stalkFunctor_map]
  intro x
  -- `α.app (op (B i))` is definitionally `φ.app (B i)`, hence an isomorphism on each basic open.
  have happ : ∀ U ∈ Set.range B,
      IsIso (((Scheme.Modules.toPresheaf X).map φ).app (Opposite.op U)) := by
    rintro U ⟨i, rfl⟩; exact h i
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, ?_⟩
  · -- Injectivity of the stalk map from injectivity on a basis.
    refine TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB ?_ x
    intro U hU
    haveI := happ U hU
    exact (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf X).map φ).app (Opposite.op U))).injective
  · -- Surjectivity: a germ at `x` comes from a section over a basic open, where `α` is onto.
    intro t
    obtain ⟨U, hxU, hU, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB N.presheaf x t
    haveI := happ U hU
    obtain ⟨s', hs'⟩ := (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf X).map φ).app (Opposite.op U))).surjective s
    refine ⟨M.presheaf.germ U x hxU s', ?_⟩
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rw [hs']
    rfl

/-- **Affine-open locality criterion for isomorphisms of `𝒪_X`-modules.** A morphism
`φ : M ⟶ N` of sheaves of modules is an isomorphism iff it restricts to an isomorphism on
the sections over every affine open of `X`. This is the precise reduction used in the
affine proof of `affineBaseChange_pushforward_iso`: the affine opens of `X` form a basis,
and over an affine open the base-change map becomes the pure ring-theoretic
`cancelBaseChange` isomorphism. -/
theorem Modules.isIso_iff_isIso_app_affineOpens {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) : IsIso φ ↔ ∀ U : X.affineOpens, IsIso (φ.app U) := by
  refine ⟨fun _ U => inferInstance, fun h => ?_⟩
  exact Modules.isIso_of_isIso_app_of_isBasis
    (B := (Subtype.val : X.affineOpens → X.Opens))
    (by simpa [Subtype.range_val] using X.isBasis_affineOpens) φ h

/-! ## Project-local Mathlib supplement — affine tilde dictionary (global sections)

The affine reduction of `affineBaseChange_pushforward_iso` needs to translate
`Scheme.Modules.pushforward (Spec.map φ)` of a `tilde`-module into restriction of
scalars. The first concrete piece is the *global-sections* identification: for a
ring map `φ : R ⟶ R'` and an `R'`-module `M`, the `R`-module of global sections of
the pushforward of `M^~` should be the restriction of scalars along `φ` of the
`R'`-module of global sections of `M^~`. Both have the same underlying additive
group (the global sections `Γ(M^~, ⊤)`, since `(Spec.map φ)⁻¹ᵁ ⊤ = ⊤`); the only
content is that the two `R`-actions agree, which is exactly the naturality of
`Scheme.ΓSpecIso` (`ΓSpecIso_inv_naturality`: the global-sections map of `Spec.map φ`
is `φ`).

STATUS (iter-234): the iso

  `(ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := R')).obj (tilde M))
     ≅ (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map φ)).obj (tilde M))`

typechecks via `LinearEquiv.toModuleIso` with the identity `AddEquiv` on the common
carrier **only under** `set_option backward.isDefEq.respectTransparency false`, and
its sole `map_smul'` goal reduces (after `erw [ModuleCat.restrictScalars.smul_def]`)
to showing the `R`-action of the restriction of scalars (defeq `φ.hom r • s`, an
`R'`-action) agrees with the `R`-action of `moduleSpecΓFunctor (R)` of the pushforward.
That action is `Module.compHom` along `(StructureSheaf.globalSectionsIso R).hom` of the
`Γ(Spec R, ⊤)`-action, which is in turn `restrictScalars` along the pushforward ring map
`(Spec.map φ).appTop`, landing on the `Γ(Spec R', ⊤)`-action. The two sides therefore
both reduce to `c • s` for a common `Γ(Spec R', ⊤)`-action, with the scalars equal by
`ΓSpecIso_inv_naturality`. The BLOCKER is purely instance-level: the intermediate
`Γ(Spec R, ⊤)`- and `Γ(Spec R', ⊤)`-actions are buried in `Module.compHom` /
`ModuleCat.restrictScalars` and are not synthesizable `SMul`/`Module` instances on the
final carrier type, so `change`/`rw`/`rfl`/`IsScalarTower.algebraMap_smul` cannot name
the common action. Closing it needs either (a) a term-mode `@`-explicit smul reduction
threading the `Module.compHom`/`restrictScalars` instances by hand, then
`ΓSpecIso_inv_naturality`; or (b) a functorial construction via
`ModuleCat.restrictScalarsComp` (× 2) + an `eqToIso` from the RingHom equality
`(Spec.map φ).appTop ≫ (ΓSpecIso R').inv = (ΓSpecIso R).inv ≫ ... ` so that no element
smul is touched. The informal agent was unavailable (MOONSHOT_API_KEY → HTTP 401; no
other provider key set). See `task_results` for the full attempt log.

UPDATE (iter-236): route (a) is **empirically the carrier wall** and is now confirmed
DEAD. The `LinearEquiv.toModuleIso` with `AddEquiv.refl` typechecks once the linear
equivalence is annotated with the explicit ring `≃ₗ[(R : Type u)]` (no
`respectTransparency` needed), and its `map_smul'` goal, after `rw [RingHom.id_apply]`
+ four `erw [ModuleCat.restrictScalars.smul_def]`, reduces **exactly** to
`A • m = B • m` where `A, B : Γ(Spec R', ⊤)` are equal by `ΓSpecIso_inv_naturality`.
But `A` lives in the *type alias*
`((Opens.map (Spec.map φ).base).op ⋙ ringCatSheaf).obj (op ⊤)`, which is only **defeq**
(via `(Spec.map φ)⁻¹ᵁ ⊤ = ⊤`, `rfl`) to `B`'s type `ringCatSheaf.obj (op ⊤)`. Every
finisher (`congr 1` → `whnf` timeout; `congrArg (· • m)`, `change _ • (m : …) = _`,
forcing the binder type) fails at `failed to synthesize HSMul Γ(Spec R',⊤) ↑(carrier)`
because instance resolution does not reduce the alias to find the registered
`Module Γ(Spec R',⊤) (carrier)` instance. This is the documented carrier-instance wall.

Route (b) (element-free) is now **executed and axiom-clean** (iter-236): the
`Γ`-fragment iso is `gammaPushforwardIso` below (general `N`), with the tilde
specialisation `gammaPushforwardTildeIso`. The construction is exactly the planned one:
both `(moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map φ)).obj N)` and
`(restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := R')).obj N)` peel **by `rfl`** to
nested `ModuleCat.restrictScalars` towers over the common `Γ(N, ⊤)` (the
`forgetToSheafModuleCat` / `initialOpOfTerminal` wrapping is an identity restriction);
the towers are reconciled by `ModuleCat.restrictScalarsComp'App` (×2) + an `eqToIso`
from the ring equation `globalSectionsIso_hom_comp_specMap_appTop` — NO element-level
`smul`, dodging the route-(a) carrier wall.

What remains for the full object iso `pushforward_spec_tilde_iso`
(`pushforward (Spec φ)_* (tilde M) ≅ tilde (restrictScalars φ M)`): the comparison
factors as `pushforward (tilde M) ⟵[fromTildeΓ] tilde (Γ (pushforward (tilde M)))
⟶[tilde.map gammaPushforwardTildeIso.hom] tilde (restrictScalars φ M)`, where the second
map is an iso (tilde of an iso) but `fromTildeΓ (pushforward (tilde M))` is an iso **iff**
`pushforward (Spec φ)_* (tilde M)` is quasi-coherent. That QC fact is the sole remaining
obligation; it is Mathlib-absent and circular with the obvious counit route (`Γ` only
reflects isos between QC objects, since the tilde adjunction unit — not the counit — is
the iso), so it needs an independent argument: either a `SheafOfModules.Presentation` of
the pushforward, or `IsQuasicoherent.of_coversTop` over the basic opens with the
slice/over-category restriction shown QC, or a direct `Modules.isIso_of_isIso_app_of_isBasis`
construction of the object iso on basic opens via `IsLocalizedModule`
(`(restrictScalars φ M)` localised at `a` = `M` localised at `φ a`). -/

/-! ## Project-local Mathlib supplement — global-sections / pushforward ring map -/

/-- The global-sections comparison ring map underlying `Spec.map φ` at the top open is
conjugate to `φ` via the global-sections isomorphisms `Γ(Spec -) ≅ -`. Concretely, the
square
```
  R  --gsR.hom-->  Γ(Spec R, ⊤)
  |φ                     |(Spec.map φ).appTop
  v                      v
  R' --gsR'.hom--> Γ(Spec R', ⊤)
```
commutes, where `gsR = StructureSheaf.globalSectionsIso R`. This is the ring-level
heart of the affine pushforward-of-tilde identification (`pushforward_spec_tilde_iso`):
it is exactly the `eqToIso` hypothesis required by the element-free
`ModuleCat.restrictScalarsComp'` route for the Γ-fragment iso (route (b) above), since
`moduleSpecΓFunctor` builds its `R`-action by `restrictScalars` along `gsR.hom` and the
pushforward builds its `Γ(Spec R, ⊤)`-action by `restrictScalars` along
`(Spec.map φ).appTop`. Project-local: Mathlib ships the underlying
`Scheme.ΓSpecIso_inv_naturality` but not this `globalSectionsIso`/`appTop` form. -/
theorem globalSectionsIso_hom_comp_specMap_appTop {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    (StructureSheaf.globalSectionsIso ↑R).hom ≫ (Spec.map φ).appTop
      = φ ≫ (StructureSheaf.globalSectionsIso ↑R').hom := by
  have hR : (StructureSheaf.globalSectionsIso ↑R).hom = (Scheme.ΓSpecIso R).inv := rfl
  have hR' : (StructureSheaf.globalSectionsIso ↑R').hom = (Scheme.ΓSpecIso R').inv := rfl
  rw [hR, hR']
  exact (Scheme.ΓSpecIso_inv_naturality φ).symm

/-! ## Project-local Mathlib supplement — Γ of an affine pushforward -/

/-- **Global sections of an affine pushforward = restriction of scalars.** For a ring
map `φ : R ⟶ R'` and *any* sheaf of modules `N` on `Spec R'`, the `R`-module of global
sections of the pushforward `(Spec φ)_* N` is the restriction of scalars along `φ` of the
`R'`-module of global sections of `N`. Built element-free (route (b)): both sides peel
(by `rfl`) to nested `ModuleCat.restrictScalars` towers over the common global-section
module `Γ(N, ⊤)`; the two towers are reconciled by collapsing each via
`ModuleCat.restrictScalarsComp'App` and applying the ring equation
`globalSectionsIso_hom_comp_specMap_appTop`. No element-level scalar multiplication is
touched, dodging the carrier-instance wall. Project-local: the affine companion of the
global-sections fragment of flat base change. -/
noncomputable def gammaPushforwardIso {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (N : (Spec R').Modules) :
    (moduleSpecΓFunctor (R := R)).obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N) ≅
      (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := R')).obj N) := by
  set SecN : ModuleCat ↑((Spec R').ringCatSheaf.obj.obj (Opposite.op ⊤)) :=
    (((SheafOfModules.forgetToSheafModuleCat (Spec R').ringCatSheaf (Opposite.op ⊤)
        (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj N).val.obj (Opposite.op ⊤)) with hSecN
  set gsRhom := (StructureSheaf.globalSectionsIso ↑R).hom.hom with hgsR
  set gsR'hom := (StructureSheaf.globalSectionsIso ↑R').hom.hom with hgsR'
  set pushTop := ((Spec.map φ).toRingCatSheafHom.hom.app (Opposite.op ⊤)).hom with hpush
  have hcomp : pushTop.comp gsRhom = gsR'hom.comp φ.hom := by
    apply RingHom.ext
    intro x
    have h := congr($(globalSectionsIso_hom_comp_specMap_appTop φ).hom x)
    simp only [hpush, hgsR, hgsR', RingHom.comp_apply] at h ⊢
    exact h
  exact (ModuleCat.restrictScalarsComp'App gsRhom pushTop (pushTop.comp gsRhom) rfl SecN).symm ≪≫
    (ModuleCat.restrictScalarsCongr hcomp).app SecN ≪≫
    (ModuleCat.restrictScalarsComp'App φ.hom gsR'hom (gsR'hom.comp φ.hom) rfl SecN)

/-- **Γ-fragment for a tilde-module.** Specialising `gammaPushforwardIso` to `N = M^~`
and using the unit iso `tilde.toTildeΓNatIso` (`Γ(M^~, ⊤) ≅ M`), the `R`-module of global
sections of `(Spec φ)_* (M^~)` is the restriction of scalars of `M` along `φ`. This is the
`Γ`-fragment comparison used to recognise the section-level base-change map in the affine
reduction of `affineBaseChange_pushforward_iso`. Project-local: corollary of
`gammaPushforwardIso`. -/
noncomputable def gammaPushforwardTildeIso {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (M : ModuleCat.{u} R') :
    (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)) ≅
      (ModuleCat.restrictScalars φ.hom).obj M :=
  gammaPushforwardIso φ (tilde M) ≪≫
    (ModuleCat.restrictScalars φ.hom).mapIso (tilde.toTildeΓNatIso.app M).symm

/-- **Sections of an affine pushforward over an arbitrary open = restriction of scalars.**
The `D(a)`-level (indeed arbitrary-open) generalization of `gammaPushforwardIso`. For a ring map
`φ : R ⟶ R'`, an `Spec R'`-module `N`, and an open `U` of `Spec R` with preimage
`V = (Spec φ)⁻¹ U` in `Spec R'`, the `R`-module of sections of the pushforward
`(Spec φ)_* N` over `U` is the restriction of scalars along `φ` of the `R'`-module of sections of
`N` over `V`. Because `modulesSpecToSheaf` forgets to the *global* section ring uniformly (it
restricts scalars along the global-sections map at the top open, not at `U`), the construction is
*identical* to that of `gammaPushforwardIso` — the same restriction-of-scalars composition identity
twice plus the same `⊤`-level ring equation `globalSectionsIso_hom_comp_specMap_appTop` — with only
the evaluation open changed from `⊤` to `U` / `V`. Project-local. -/
noncomputable def gammaPushforwardIsoAt {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (N : (Spec R').Modules) (U : (Spec R).Opens) :
    (modulesSpecToSheaf.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N)).val.obj
        (Opposite.op U) ≅
      (ModuleCat.restrictScalars φ.hom).obj
        ((modulesSpecToSheaf.obj N).val.obj
          (Opposite.op ((TopologicalSpace.Opens.map (Spec.map φ).base).obj U))) := by
  set SecN : ModuleCat ↑((Spec R').ringCatSheaf.obj.obj (Opposite.op ⊤)) :=
    (((SheafOfModules.forgetToSheafModuleCat (Spec R').ringCatSheaf (Opposite.op ⊤)
        (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj N).val.obj
          (Opposite.op ((TopologicalSpace.Opens.map (Spec.map φ).base).obj U))) with hSecN
  set gsRhom := (StructureSheaf.globalSectionsIso ↑R).hom.hom with hgsR
  set gsR'hom := (StructureSheaf.globalSectionsIso ↑R').hom.hom with hgsR'
  set pushTop := ((Spec.map φ).toRingCatSheafHom.hom.app (Opposite.op ⊤)).hom with hpush
  have hcomp : pushTop.comp gsRhom = gsR'hom.comp φ.hom := by
    apply RingHom.ext
    intro x
    have h := congr($(globalSectionsIso_hom_comp_specMap_appTop φ).hom x)
    simp only [hpush, hgsR, hgsR', RingHom.comp_apply] at h ⊢
    exact h
  exact (ModuleCat.restrictScalarsComp'App gsRhom pushTop (pushTop.comp gsRhom) rfl SecN).symm ≪≫
    (ModuleCat.restrictScalarsCongr hcomp).app SecN ≪≫
    (ModuleCat.restrictScalarsComp'App φ.hom gsR'hom (gsR'hom.comp φ.hom) rfl SecN)

/-! ## Project-local Mathlib supplement — restriction of scalars and localization -/

/-- **Counit of the tilde–Γ adjunction is a basic-open isomorphism whenever the restriction
of the global sections is a localization.** For a sheaf of modules `N` on `Spec R` and `a : R`,
if the structure-sheaf restriction map `Γ(N, ⊤) → Γ(N, D(a))` (read in `ModuleCat R` via the
global-sections forgetful functor `modulesSpecToSheaf`) exhibits `Γ(N, D(a))` as the localization
of `Γ(N, ⊤)` at `Submonoid.powers a`, then the counit `fromTildeΓ N` is an isomorphism on the
sections over `D(a)`. This is the section-level engine of `pushforward_spec_tilde_iso`: it isolates
the *only* nontrivial input (`Γ(N, D(a)) = Γ(N, ⊤)[1/a]`) and discharges the rest — the comparison
`fromTildeΓ` is, on `D(a)`, the canonical map between two localizations of `Γ(N, ⊤)` (the tilde
localization `toOpen` and the restriction), hence an isomorphism by the uniqueness of localized
modules. Project-local: Mathlib has the localization-uniqueness lemmas but not this packaging at
the level of `fromTildeΓ`. -/
lemma fromTildeΓ_app_isIso_of_isLocalizedModule {R : CommRingCat.{u}} (N : (Spec R).Modules)
    (a : R)
    [IsLocalizedModule (Submonoid.powers a)
      ((modulesSpecToSheaf.obj N).val.map
        (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op).hom] :
    IsIso (Scheme.Modules.Hom.app N.fromTildeΓ (PrimeSpectrum.basicOpen a)) := by
  -- The underlying function of `Hom.app` agrees (by `rfl`) with that of the `modulesSpecToSheaf`
  -- image, where the tilde–Γ triangle identity `toOpen_fromTildeΓ_app` applies.
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : ⇑(ConcreteCategory.hom
        (Scheme.Modules.Hom.app N.fromTildeΓ (PrimeSpectrum.basicOpen a))) =
      ⇑(ConcreteCategory.hom
        ((modulesSpecToSheaf.map N.fromTildeΓ).1.app (Opposite.op (PrimeSpectrum.basicOpen a)))) :=
    rfl
  rw [hfun]
  -- Abbreviations: `j` is the tilde localization map, `ρ` the structure-sheaf restriction, both
  -- localizations of `Γ(N, ⊤)` at `powers a`; `L` is the section map of the counit.
  set j := (tilde.toOpen ((modulesSpecToSheaf.obj N).val.obj (Opposite.op ⊤))
    (PrimeSpectrum.basicOpen a)).hom with hj
  set ρ := ((modulesSpecToSheaf.obj N).val.map
    (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op).hom with hρ
  haveI hρinst : IsLocalizedModule (Submonoid.powers a) ρ := by rw [hρ]; infer_instance
  clear_value ρ
  set L := ((modulesSpecToSheaf.map N.fromTildeΓ).1.app
    (Opposite.op (PrimeSpectrum.basicOpen a))).hom with hL
  -- The triangle identity gives `L ∘ₗ j = ρ`.
  have htri : L ∘ₗ j = ρ := by
    have := Scheme.Modules.toOpen_fromTildeΓ_app N (PrimeSpectrum.basicOpen a)
    apply_fun ModuleCat.Hom.hom at this
    simp only [hL, hj, hρ, ModuleCat.hom_comp] at this ⊢
    exact this
  -- `L` equals the canonical iso between the two localizations of `Γ(N, ⊤)`, hence bijective.
  set ej := IsLocalizedModule.iso (Submonoid.powers a) j with hej
  set eρ := IsLocalizedModule.iso (Submonoid.powers a) ρ with heρ
  let e := ej.symm.trans eρ
  have hcomp : e.toLinearMap ∘ₗ j = ρ := by
    ext x
    simp only [e, hej, heρ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, IsLocalizedModule.iso_symm_apply]
    exact IsLocalizedModule.iso_mk_one (Submonoid.powers a) ρ x
  have hLeq : L = e.toLinearMap :=
    IsLocalizedModule.ext (Submonoid.powers a) j (IsLocalizedModule.map_units ρ)
      (htri.trans hcomp.symm)
  rw [show ⇑(ConcreteCategory.hom ((modulesSpecToSheaf.map N.fromTildeΓ).1.app
    (Opposite.op (PrimeSpectrum.basicOpen a)))) = ⇑L from rfl, hLeq]
  exact e.bijective

/-- **Affine pushforward of a tilde-module, conditional on the basic-open localization fact.**
This is the full assembly of `pushforward_spec_tilde_iso` (route iii), modulo the single
remaining ingredient: that on each basic open `D(a)` the structure-sheaf restriction of the
pushforward `(Spec φ)_* M^~` exhibits its sections over `D(a)` as the localization at
`Submonoid.powers a` of its global sections. Given that hypothesis (`hloc`), the counit
`fromTildeΓ ((Spec φ)_* M^~)` is an isomorphism (basis-locality criterion
`Modules.isIso_of_isIso_app_of_isBasis` over the basic opens, with each section iso supplied by
`fromTildeΓ_app_isIso_of_isLocalizedModule`), so `(Spec φ)_* M^~` lies in the essential image of
`tilde` and the global-sections comparison `gammaPushforwardTildeIso` upgrades to the desired
object isomorphism.

The hypothesis `hloc` is the *only* outstanding obligation for the unconditional
`pushforward_spec_tilde_iso`: it is the affine "`(Spec φ)⁻¹ D(a) = D(φ a)`, and localizing
`restrict φ M` at `a` agrees with localizing `M` at `φ a`" fact (Stacks, widetilde-pullback),
whose ring-change core is `IsLocalizedModule.powers_restrictScalars` below. Discharging it
requires identifying the `modulesSpecToSheaf` global-ring `R`-action on the sections of the
pushforward over `D(a)` with restriction of scalars along `φ` of the `R'`-localization
`M[1/φ a]` — the section-level structure-sheaf naturality at `D(a)`. -/
noncomputable def pushforward_spec_tilde_iso_of_isLocalizedModule {R R' : CommRingCat.{u}}
    (φ : R ⟶ R') (M : ModuleCat.{u} R')
    (hloc : ∀ a : R, IsLocalizedModule (Submonoid.powers a)
      ((modulesSpecToSheaf.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M))).val.map
        (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op).hom) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.restrictScalars φ.hom).obj M) := by
  have hiso : IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M))) := by
    apply Modules.isIso_of_isIso_app_of_isBasis
      (B := fun a : R => PrimeSpectrum.basicOpen a) PrimeSpectrum.isBasis_basic_opens
    intro a
    haveI := hloc a
    exact fromTildeΓ_app_isIso_of_isLocalizedModule _ a
  exact (asIso (Scheme.Modules.fromTildeΓ _)).symm ≪≫
    (tilde.functor R).mapIso (gammaPushforwardTildeIso φ M)

/-- **Restriction of scalars of a localized module is a localized module.** If `f : M →ₗ[A] N`
exhibits `N` as the localization of `M` at the image submonoid `Algebra.algebraMapSubmonoid A S`
(for `S : Submonoid R` and `A` an `R`-algebra), then the `R`-linear map underlying `f`
exhibits `N` as the localization of `M` at `S` itself. This is the exact converse of
`IsLocalizedModule.of_restrictScalars` and is the ring-change ingredient powering the affine
pushforward identification: localizing `restrictScalars φ M` at `a ∈ R` agrees with localizing
`M` at `φ a ∈ R'`. Project-local: Mathlib ships only the forward direction. -/
lemma IsLocalizedModule.powers_restrictScalars
    {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (S : Submonoid R) (f : M →ₗ[A] N)
    [IsLocalizedModule (Algebra.algebraMapSubmonoid A S) f] :
    IsLocalizedModule S (f.restrictScalars R) where
  map_units x := by
    have h := IsLocalizedModule.map_units f
      (⟨algebraMap R A x, Submonoid.mem_map.mpr ⟨x, x.2, rfl⟩⟩ : Algebra.algebraMapSubmonoid A S)
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at h ⊢
    exact h
  surj y := by
    obtain ⟨⟨x, ⟨_, t, ht, rfl⟩⟩, e⟩ := IsLocalizedModule.surj (Algebra.algebraMapSubmonoid A S) f y
    exact ⟨⟨x, ⟨t, ht⟩⟩, by simpa [Submonoid.smul_def, IsScalarTower.algebraMap_smul] using e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨⟨_, c, hc, rfl⟩, h⟩ :=
      IsLocalizedModule.exists_of_eq (S := Algebra.algebraMapSubmonoid A S) (f := f) e
    exact ⟨⟨c, hc⟩, by simpa [Submonoid.smul_def, IsScalarTower.algebraMap_smul] using h⟩

/-- **The structure-sheaf restriction of a tilde-module from `⊤` to `D(b)` is a localization.**
Read in `ModuleCat R'` via `modulesSpecToSheaf`, the restriction map
`Γ(M^~, ⊤) → Γ(M^~, D(b))` exhibits its target as the localization of its source at
`Submonoid.powers b`. This packages the Mathlib instance
`tilde.toOpen … (basicOpen b)` (which makes `M → Γ(M^~, D(b))` a localization) together with the
triangle identity `tilde.toOpen_res` and the fact that `M → Γ(M^~, ⊤)` is bijective (localization
at the trivial submonoid `powers 1`). Project-local. -/
lemma tildeRestriction_isLocalizedModule {R' : CommRingCat.{u}} (M : ModuleCat.{u} R') (b : R') :
    IsLocalizedModule (Submonoid.powers b)
      ((modulesSpecToSheaf.obj (tilde M)).val.map
        (homOfLE (show PrimeSpectrum.basicOpen b ≤ ⊤ from le_top)).op).hom := by
  -- `toOpen M ⊤` is a localization at `powers (1 : R')` (since `basicOpen 1 = ⊤`), hence bijective.
  haveI inst1 : IsLocalizedModule (Submonoid.powers (1 : R')) (tilde.toOpen M ⊤).hom := by
    have h := (inferInstance : IsLocalizedModule (Submonoid.powers (1 : R'))
      (tilde.toOpen M (PrimeSpectrum.basicOpen (1 : R'))).hom)
    rw [PrimeSpectrum.basicOpen_one] at h
    exact h
  have hbij : Function.Bijective (tilde.toOpen M ⊤).hom := by
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
        (S := Submonoid.powers (1 : R')) (f := (tilde.toOpen M ⊤).hom) hxy
      obtain ⟨n, hn⟩ := c.2
      have hc1 : (↑c : R') = 1 := by simpa using hn.symm
      rw [Submonoid.smul_def, Submonoid.smul_def, hc1, one_smul, one_smul] at hc
      exact hc
    · obtain ⟨⟨x, c⟩, hc⟩ := IsLocalizedModule.surj
        (Submonoid.powers (1 : R')) (tilde.toOpen M ⊤).hom y
      obtain ⟨n, hn⟩ := c.2
      have hc1 : (↑c : R') = 1 := by simpa using hn.symm
      refine ⟨x, ?_⟩
      rw [Submonoid.smul_def, hc1, one_smul] at hc
      exact hc.symm
  -- Triangle identity: `toOpen ⊤ ≫ (restriction) = toOpen (D b)`.
  have htri := tilde.toOpen_res M (⊤ : (Spec R').Opens) (PrimeSpectrum.basicOpen b)
    (homOfLE (le_top))
  -- The inverse equivalence `Γ(M^~, ⊤) ≃ M`.
  set le : M ≃ₗ[R'] ((modulesSpecToSheaf.obj (tilde M)).val.obj (Opposite.op ⊤)) :=
    LinearEquiv.ofBijective (tilde.toOpen M ⊤).hom hbij with hle
  -- The triangle at the level of linear maps: `restriction ∘ₗ le = toOpen (D b)`.
  have htri2 : ((modulesSpecToSheaf.obj (tilde M)).val.map
        (homOfLE (show PrimeSpectrum.basicOpen b ≤ ⊤ from le_top)).op).hom ∘ₗ le.toLinearMap
      = (tilde.toOpen M (PrimeSpectrum.basicOpen b)).hom := by
    have h := congrArg ModuleCat.Hom.hom htri
    rw [ModuleCat.hom_comp] at h
    exact h
  -- Hence `restriction = toOpen (D b) ∘ₗ le⁻¹`, a localization at `powers b` precomposed with
  -- a linear equivalence.
  have key : ((modulesSpecToSheaf.obj (tilde M)).val.map
        (homOfLE (show PrimeSpectrum.basicOpen b ≤ ⊤ from le_top)).op).hom
      = (tilde.toOpen M (PrimeSpectrum.basicOpen b)).hom ∘ₗ le.symm.toLinearMap :=
    (LinearEquiv.eq_comp_toLinearMap_symm _ _).mpr htri2
  rw [key]
  exact IsLocalizedModule.of_linearEquiv_right (Submonoid.powers b)
    (tilde.toOpen M (PrimeSpectrum.basicOpen b)).hom le.symm

/-- **Affine pushforward of a tilde-module (unconditional).** For a ring map `φ : R ⟶ R'`
and an `R'`-module `M`, pushing the quasi-coherent sheaf `M^~` forward along `Spec φ` is,
up to canonical isomorphism, the tilde of the restriction of scalars of `M` along `φ`. This
is the unconditional form of `pushforward_spec_tilde_iso_of_isLocalizedModule`: the latter's
hypothesis `hloc` (each structure-sheaf restriction `Γ(N,⊤) → Γ(N,D(a))` is a localization at
`powers a`) is discharged here by the `D(a)`-level transport. See blueprint
`lem:pushforward_spec_tilde_iso`. -/
noncomputable def pushforward_spec_tilde_iso {R R' : CommRingCat.{u}}
    (φ : R ⟶ R') (M : ModuleCat.{u} R') :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.restrictScalars φ.hom).obj M) := by
  apply pushforward_spec_tilde_iso_of_isLocalizedModule φ M
  intro a
  -- STRATEGY (`of_linearEquiv`): the restriction map `ρ : Γ(N,⊤) → Γ(N,D(a))` of
  -- `N := (Spec φ)_* (M^~)` is, under the isomorphisms
  -- `gammaPushforwardIsoAt φ (tilde M) ⊤` and `gammaPushforwardIsoAt φ (tilde M) (D a)`,
  -- identified with the restriction of scalars along `φ` of the `R'`-side tilde restriction
  -- `σ : Γ(M^~, ⊤) → Γ(M^~, D(φ a))`. That `σ` is a localization at `powers (φ a)`
  -- (`tildeRestriction_isLocalizedModule`), so its restriction of scalars along `φ` is a
  -- localization at `powers a` (`IsLocalizedModule.powers_restrictScalars`); transporting along
  -- the two isomorphisms then yields `hloc(a)`.
  -- The two bricks for this discharge are now in place and axiom-clean:
  --   • `gammaPushforwardIsoAt φ (tilde M) U : Γ(N, U) ≅ restrictScalars φ (Γ(M^~, (Spec φ)⁻¹ U))`
  --     — the open-indexed `e_{D(a)}` isomorphism (blueprint movement (1)); and
  --   • `tildeRestriction_isLocalizedModule M (φ a)` — the `R'`-side restriction
  --     `Γ(M^~, ⊤) → Γ(M^~, D(φ a))` is a localization at `powers (φ a)`.
  -- The `of_linearEquiv` finish is: with `e₁ = gammaPushforwardIsoAt φ (tilde M) ⊤` and
  -- `e₂ = gammaPushforwardIsoAt φ (tilde M) (D a)`, the naturality square
  -- `e₂.hom ∘ ρ = (restrictScalars φ σ) ∘ e₁.hom` (where `σ` is the `R'`-side restriction and
  -- `ρ` the pushforward-side one) gives `ρ = e₂.symm ∘ₗ (restrictScalars φ σ) ∘ₗ e₁`; then
  -- `IsLocalizedModule.powers_restrictScalars` upgrades `σ` (localization at `powers (φ a)`,
  -- since `algebraMapSubmonoid R' (powers a) = powers (φ a)` along `φ.hom.toAlgebra`) to a
  -- localization at `powers a` of `restrictScalars φ σ`, and two applications of
  -- `IsLocalizedModule.of_linearEquiv` / `of_linearEquiv_right` transport this to `ρ`.
  --
  -- iter-240 PIVOT (`algebraize`): preimage opens are *definitionally* the basic opens
  -- (`AlgebraicGeometry.SpecMap_preimage_basicOpen` is `rfl`), so the `R'`-side restriction
  -- `σ` is literally `tilde M`'s restriction `⊤ → D(φ a)`, and `algebraize [φ.hom]` supplies the
  -- honest `Algebra ↑R ↑R'`/`IsScalarTower` instances that `powers_restrictScalars` needs.
  algebraize [φ.hom]
  -- `σ` : the `R'`-side restriction map `Γ(M^~, ⊤) → Γ(M^~, D(φ a))` of `tilde M`.
  set σmor := (modulesSpecToSheaf.obj (tilde M)).val.map
      (homOfLE (show PrimeSpectrum.basicOpen (φ.hom a) ≤ ⊤ from le_top)).op with hσmor
  -- Re-expose the `compHom`-via-`φ` `R`-module/scalar-tower instances (the ones the
  -- `ModuleCat.restrictScalars φ.hom` objects carry) on the bare section carriers, so that
  -- `powers_restrictScalars` can see them.
  letI mTop : Module R ↑((modulesSpecToSheaf.obj (tilde M)).val.obj (Opposite.op ⊤)) :=
    inferInstanceAs (Module R ((ModuleCat.restrictScalars φ.hom).obj
      ((modulesSpecToSheaf.obj (tilde M)).val.obj (Opposite.op ⊤))))
  letI mDa : Module R ↑((modulesSpecToSheaf.obj (tilde M)).val.obj
      (Opposite.op (PrimeSpectrum.basicOpen (φ.hom a)))) :=
    inferInstanceAs (Module R ((ModuleCat.restrictScalars φ.hom).obj
      ((modulesSpecToSheaf.obj (tilde M)).val.obj (Opposite.op (PrimeSpectrum.basicOpen (φ.hom a))))))
  haveI tTop : IsScalarTower R R' ↑((modulesSpecToSheaf.obj (tilde M)).val.obj (Opposite.op ⊤)) :=
    ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  haveI tDa : IsScalarTower R R' ↑((modulesSpecToSheaf.obj (tilde M)).val.obj
      (Opposite.op (PrimeSpectrum.basicOpen (φ.hom a)))) :=
    ⟨fun x y z => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  -- `σ` is a localization at `powers (φ a)`.
  haveI hσloc : IsLocalizedModule (Submonoid.powers (φ.hom a)) σmor.hom :=
    tildeRestriction_isLocalizedModule M (φ.hom a)
  -- restriction of scalars of `σ` along `φ` is a localization at `powers a`.
  have himg : Algebra.algebraMapSubmonoid (R' : Type u) (Submonoid.powers a)
      = Submonoid.powers (φ.hom a) := by
    rw [Algebra.algebraMapSubmonoid_powers]; rfl
  haveI : IsLocalizedModule (Algebra.algebraMapSubmonoid (R' : Type u) (Submonoid.powers a))
      σmor.hom := by rw [himg]; exact hσloc
  haveI hGloc := @IsLocalizedModule.powers_restrictScalars (↑R) (↑R') _ _ _ _ _ _ _
    mTop mDa _ _ tTop tDa (Submonoid.powers a) σmor.hom this
  -- The restriction-of-scalars of `σ` as a `ModuleCat R` morphism (bundled `compHom` instances).
  set Gmor := (ModuleCat.restrictScalars φ.hom).map σmor with hGmor
  -- `Gmor.hom` is `σmor.hom.restrictScalars R`, hence a localization at `powers a`.
  haveI hG : IsLocalizedModule (Submonoid.powers a) Gmor.hom := hGloc
  -- The pushforward restriction `ρ` (a `ModuleCat R` morphism).
  set ρ := (modulesSpecToSheaf.obj ((pushforward (Spec.map φ)).obj (tilde M))).val.map
      (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op with hρdef
  -- The two open-indexed comparison isos (`e_{⊤}`, `e_{D(a)}`), via `gammaPushforwardIsoAt`.
  set e₁ := gammaPushforwardIsoAt φ (tilde M) ⊤ with he₁
  set e₂ := gammaPushforwardIsoAt φ (tilde M) (PrimeSpectrum.basicOpen a) with he₂
  -- Naturality square (at the `ModuleCat R` level): conjugating the pushforward restriction `ρ`
  -- by `e₁`, `e₂` gives the restriction of scalars along `φ` of the `R'`-side restriction `σ`.
  -- The common underlying `R'`-side forget restriction map (with `FN` inlined so it matches
  -- the unfolded `gammaPushforwardIsoAt`).
  set tForget := ((SheafOfModules.forgetToSheafModuleCat (Spec R').ringCatSheaf (Opposite.op ⊤)
        (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj (tilde M)).val.map
      (homOfLE (show (TopologicalSpace.Opens.map (Spec.map φ).base).obj
        (PrimeSpectrum.basicOpen a) ≤ ⊤ from le_top)).op with htForget
  -- Structural identifications (peel `modulesSpecToSheaf`/pushforward through `restrictScalars`),
  -- written with the *raw* ring maps so they match `gammaPushforwardIsoAt`'s unfolding.
  have hσ' : σmor = (ModuleCat.restrictScalars
      (StructureSheaf.globalSectionsIso (↑R' : CommRingCat)).hom.hom).map tForget := rfl
  have hρ' : ρ = (ModuleCat.restrictScalars
        (StructureSheaf.globalSectionsIso (↑R : CommRingCat)).hom.hom).map
      ((ModuleCat.restrictScalars
        ((Spec.map φ).toRingCatSheafHom.hom.app (Opposite.op ⊤)).hom).map tForget) := rfl
  -- The open-naturality square `ρ ≫ e₂.hom = e₁.hom ≫ Gmor` (the residual `hsq`).
  have hsq : ρ ≫ e₂.hom = e₁.hom ≫ Gmor := by
    -- Substitute the structural exposures, then unfold `gammaPushforwardIsoAt`. Here
    --   ρ = rsc gsR ∘ rsc pushTop ∘ tForget,  Gmor = rsc φ ∘ σmor = rsc φ ∘ rsc gsR' ∘ tForget,
    --   e_U = (rsc-comp')⁻¹ ≫ (restrictScalarsCongr hcomp).app SecN ≫ (rsc-comp').
    rw [he₁, he₂, hGmor, hρ', hσ']
    simp only [gammaPushforwardIsoAt, Iso.trans_hom, Iso.symm_hom]
    -- KEY INSIGHT (iter-241): every constituent of `gammaPushforwardIsoAt` is the IDENTITY on
    -- underlying elements — `restrictScalarsComp'App_{hom,inv}_apply`, `restrictScalarsCongr`
    -- app, and `restrictScalars.map_apply` are all `rfl`; the middle `restrictScalarsCongr` (now
    -- replaces the former `eqToIso`, removing the only non-`rfl` cast) merely repackages the module
    -- structure on the unchanged carrier. So both legs of the square send `x` to the underlying
    -- `tForget x` definitionally — a pointwise `rfl` closes it, sidestepping the rewrite-matching
    -- pathology that defeated the prior `restrictScalarsComp'App_inv_naturality`-rewrite route.
    ext x
    rfl
  -- Solve for `ρ` and transport the localization across the two equivalences.
  have hρ : ρ = (e₁.hom ≫ Gmor) ≫ e₂.inv := (Iso.eq_comp_inv e₂).mpr hsq
  have key : ρ.hom
      = e₂.toLinearEquiv.symm.toLinearMap ∘ₗ
          (Gmor.hom ∘ₗ e₁.toLinearEquiv.toLinearMap) := by
    rw [hρ]; rfl
  rw [key]
  haveI hstep : IsLocalizedModule (Submonoid.powers a)
      (Gmor.hom ∘ₗ e₁.toLinearEquiv.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers a) Gmor.hom e₁.toLinearEquiv
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers a)
    (Gmor.hom ∘ₗ e₁.toLinearEquiv.toLinearMap) e₂.toLinearEquiv.symm

/-! ## Project-local Mathlib supplement — affine pullback dictionary -/

/-- **Naturality of the Γ-fragment comparison.** The per-object isomorphisms
`gammaPushforwardIso φ N : Γ_R((Spec φ)_* N) ≅ restrictScalars φ (Γ_{R'} N)` assemble into a
natural isomorphism of functors `(Spec R').Modules ⥤ ModuleCat R`
\[ (\operatorname{Spec}\varphi)_* \;\circ\; \Gamma_R
   \;\cong\; \Gamma_{R'} \;\circ\; \operatorname{restr}_\varphi . \]
Every constituent of `gammaPushforwardIso` is the identity on underlying elements (the
`restrictScalarsComp'App` isos and `restrictScalarsCongr` merely repackage the module structure
on the unchanged carrier), so naturality is a pointwise `rfl`. This is the right-adjoint natural
isomorphism that drives the affine pullback dictionary `pullback_spec_tilde_iso` via
`Adjunction.natIsoOfRightAdjointNatIso`. Project-local. -/
noncomputable def gammaPushforwardNatIso {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := R') ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (fun N => gammaPushforwardIso φ N) (by
    intro N N' g
    ext x
    rfl)

/-- **Affine pullback of a tilde-module.** For a ring map `φ : R ⟶ R'` and an `R`-module `M`,
pulling the quasi-coherent sheaf `M^~` back along `Spec φ` is, up to canonical isomorphism, the
tilde of the extension of scalars `R' ⊗_R M`. This is the pullback companion of
`pushforward_spec_tilde_iso` and is part (1) of Stacks Tag 01I9 (`lemma-widetilde-pullback`).

The construction is the uniqueness-of-left-adjoints route. Pullback along `Spec φ` is left adjoint
to pushforward, and `tilde` is left adjoint to global sections; their composite
`tilde_R ⋙ pullback` is left adjoint to `pushforward ⋙ Γ_R`. Symmetrically `extendScalars φ` is
left adjoint to `restrictScalars φ`, so `extendScalars ⋙ tilde_{R'}` is left adjoint to
`Γ_{R'} ⋙ restrictScalars φ`. The two right adjoints are identified by the natural isomorphism
`gammaPushforwardNatIso` (which is the global-sections comparison `gammaPushforwardIso`), so
`Adjunction.natIsoOfRightAdjointNatIso` yields an isomorphism of the two left adjoints; evaluating
at `M` gives the claim. Project-local: the affine companion of the pushforward dictionary. See
blueprint `lem:pullback_spec_tilde_iso`. -/
noncomputable def pullback_spec_tilde_iso {R R' : CommRingCat.{u}}
    (φ : R ⟶ R') (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  let adjL := (tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
  let adjR := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := R'))
  (((conjugateIsoEquiv adjL adjR).symm (gammaPushforwardNatIso φ)).symm).app M

/-! ## Project-local Mathlib supplement — affine termwise base-change brick (IN PROGRESS)

The concrete-tilde route to flat base change (Stacks 02KH) builds a *fresh* base-change
isomorphism `e : g^* ∘ f_* ≅ f'_* ∘ (g')^*` by gluing affine-local isomorphisms, instead of
proving the canonical adjoint mate `pushforwardBaseChangeMap` is an isomorphism (which walls on the
mate ↔ `cancelBaseChange` coherence). The affine-local brick is the floor of that construction:
over the fully affine pushout square
```
  Spec (A ⊗_R R') --Spec ρ--> Spec A
  |Spec σ                      |Spec φ
  v                            v
  Spec R'      ----Spec ψ---->  Spec R
```
(`φ : R → A`, `ψ : R → R'`, `ρ = includeLeft`, `σ = includeRight` into `A ⊗_R R'`) it produces the
termwise isomorphism `g^*(f_* M̃) ≅ f'_*((g')^* M̃)`, assembled from the two sorry-free tilde
dictionaries `pushforward_spec_tilde_iso` / `pullback_spec_tilde_iso` and the pure
commutative-algebra cancellation `Algebra.IsPushout.cancelBaseChange`, never forming the adjoint
mate.

STATUS (iter-305): the load-bearing module-level core — the `R'`-linear iso
`(extendScalars ψ) ∘ (restrictScalars φ) ≅ (restrictScalars σ) ∘ (extendScalars ρ)` realising
`R' ⊗_R M ≅ (A ⊗_R R') ⊗_A M` — was PROVEN to typecheck axiom-clean in the **CommRingCat framing**
(ambient algebras supplied as `φ.hom.toAlgebra` / `ψ.hom.toAlgebra`), by `@`-threading the
`RingHom.toAlgebra` instances through `Algebra.IsPushout.cancelBaseChange` (so its output is defeq to
the `compHom`-based `ModuleCat.extendScalars`/`restrictScalars` objects) with `IsPushout` transported
from `TensorProduct.isPushout'` via `Algebra.algebra_ext`. See `task_results` for the full working
construction. It is NOT yet landed as a top-level declaration: stating the tensor `A ⊗_R R'` in the
signature forces a Type-u framing whose *opaque* ambient `[Algebra R A]`/`[Algebra R R']` lets the
GLOBAL `Algebra.TensorProduct.leftAlgebra`/`rightAlgebra` instances win over the `toAlgebra` `letI`s,
breaking the `compHom`-defeq on the inner `Module A (A⊗_R R')` and outer `Module R' (·)`. The
recommended fix (iter-306) is the abstract-`B` framing: take `ρ : A ⟶ B`, `σ : R' ⟶ B` and a
`CategoryTheory.IsPushout φ ψ ρ σ` (or `IsPullback` of the Spec square) hypothesis, derive
`Algebra.IsPushout` in the proof with all algebras `toAlgebra` (no global tensor instances to shadow),
and assemble the 5-step chain. See blueprint `lem:affine_pushforward_pullback_baseChange`. -/

/-- **Module-level base-change cancellation iso (abstract-`B` framing).** Given a pushout square of
commutative rings
```
  R --φ--> A
  |ψ       |ρ
  v        v
  R' --σ-> B
```
(so `B ≅ A ⊗_R R'`) and an `A`-module `M`, the `R'`-linear isomorphism
`extendScalars_ψ (restrictScalars_φ M) ≅ restrictScalars_σ (extendScalars_ρ M)`, i.e.
`R' ⊗_R M ≅ restrictScalars_σ (B ⊗_A M)`. It realises the inverse of Mathlib's
`Algebra.IsPushout.cancelBaseChange` between the extension-of-scalars objects attached to the two
legs of the square. The abstract `B` (rather than the concrete `A ⊗_R R'`) keeps all ambient
algebra instances `toAlgebra`, so no global tensor-product instance shadows them and
`cancelBaseChange`'s output module structures land defeq on the `compHom`-based
`extendScalars`/`restrictScalars` objects. Project-local: the module core of the affine termwise
base-change brick. See blueprint `lem:baseChangeCancelModuleIso`. -/
noncomputable def baseChangeCancelModuleIso {R A R' B : CommRingCat.{u}}
    (φ : R ⟶ A) (ψ : R ⟶ R') (ρ : A ⟶ B) (σ : R' ⟶ B)
    (h : CategoryTheory.IsPushout φ ψ ρ σ) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.restrictScalars φ.hom).obj M) ≅
      (ModuleCat.restrictScalars σ.hom).obj ((ModuleCat.extendScalars ρ.hom).obj M) := by
  letI iRA : Algebra (R : Type u) (A : Type u) := φ.hom.toAlgebra
  letI iRR' : Algebra (R : Type u) (R' : Type u) := ψ.hom.toAlgebra
  letI iAB : Algebra (A : Type u) (B : Type u) := ρ.hom.toAlgebra
  letI iR'B : Algebra (R' : Type u) (B : Type u) := σ.hom.toAlgebra
  letI iRB : Algebra (R : Type u) (B : Type u) := (ρ.hom.comp φ.hom).toAlgebra
  letI iMR : Module (R : Type u) M := ((ModuleCat.restrictScalars φ.hom).obj M).isModule
  haveI tRAM : IsScalarTower (R : Type u) A M :=
    ⟨fun r a m => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  haveI tRAB : @IsScalarTower (R : Type u) A B _ iAB.toSMul iRB.toSMul :=
    @IsScalarTower.of_algebraMap_eq (R : Type u) A B _ _ _ iRA iAB iRB (fun _ => rfl)
  haveI tRR'B : @IsScalarTower (R : Type u) R' B _ iR'B.toSMul iRB.toSMul :=
    @IsScalarTower.of_algebraMap_eq (R : Type u) R' B _ _ _ iRR' iR'B iRB (fun r => by
      change (ρ.hom.comp φ.hom) r = σ.hom (ψ.hom r)
      have := congrArg (fun m => (CommRingCat.Hom.hom m) r) h.w
      simpa using this)
  haveI hpush : @Algebra.IsPushout (R : Type u) R' _ _ iRR' A B _ _ iRA iR'B iAB iRB tRAB tRR'B :=
    (CommRingCat.isPushout_iff_isPushout).mp h.flip
  exact LinearEquiv.toModuleIso
    (@Algebra.IsPushout.cancelBaseChange (R : Type u) R' _ _ iRR' A B _ _ iRA iRB iAB iR'B
      tRAB tRR'B hpush M _ iMR _ tRAM).symm

/-- **Affine termwise base change (abstract-`B` framing).** For a pushout square of commutative
rings `(φ : R ⟶ A, ψ : R ⟶ R', ρ : A ⟶ B, σ : R' ⟶ B)` — equivalently the cartesian square of
affine schemes obtained by `Spec` — and an `A`-module `M`, the base-change comparison
`g^*(f_* M̃) ≅ f'_*((g')^* M̃)` for `f = Spec φ`, `g = Spec ψ`, `f' = Spec σ`, `g' = Spec ρ`. It is
assembled as a 5-step chain from the two affine tilde dictionaries
(`pushforward_spec_tilde_iso` / `pullback_spec_tilde_iso`) and the module-level cancellation core
`baseChangeCancelModuleIso`, and it **never** forms the adjoint mate
`pushforwardBaseChangeMap`, so it sidesteps the unresolved mate ↔ `cancelBaseChange` coherence
obligation of the canonical route. This is the affine-local brick (the floor) of the active
concrete-tilde route to flat base change (Stacks 02KG/02KH). Project-local. See blueprint
`lem:affine_pushforward_pullback_baseChange`. -/
noncomputable def affinePushforwardPullbackBaseChange {R A R' B : CommRingCat.{u}}
    (φ : R ⟶ A) (ψ : R ⟶ R') (ρ : A ⟶ B) (σ : R' ⟶ B)
    (h : CategoryTheory.IsPushout φ ψ ρ σ) (M : ModuleCat.{u} A) :
    (Scheme.Modules.pullback (Spec.map ψ)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)) ≅
      (Scheme.Modules.pushforward (Spec.map σ)).obj
        ((Scheme.Modules.pullback (Spec.map ρ)).obj (tilde M)) :=
  (Scheme.Modules.pullback (Spec.map ψ)).mapIso (pushforward_spec_tilde_iso φ M)
    ≪≫ pullback_spec_tilde_iso ψ ((ModuleCat.restrictScalars φ.hom).obj M)
    ≪≫ (tilde.functor R').mapIso (baseChangeCancelModuleIso φ ψ ρ σ h M)
    ≪≫ (pushforward_spec_tilde_iso σ ((ModuleCat.extendScalars ρ.hom).obj M)).symm
    ≪≫ (Scheme.Modules.pushforward (Spec.map σ)).mapIso (pullback_spec_tilde_iso ρ M).symm


/-! ## Project-local Mathlib supplement — cancellation/localization compatibility

For a tower of commutative rings `R → S → S'` and a further homomorphism `R → A`, the
cancellation isomorphism `Algebra.IsPushout.cancelBaseChange` for the `S'`-tower is the
base change along `S → S'` of the cancellation isomorphism for the `S`-tower. This is the
purely commutative-algebraic "cancellation move" of the affine-restriction naturality square
(`pushforwardPullbackBaseChange_restrict_naturality`); see blueprint
`lem:cancelBaseChange_localization_compat`. It carries no scheme scaffolding.
-/

section CancelBaseChangeCompat

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower TensorProduct.isPushout'

/-- Value of `cancelBaseChange` on a simple tensor `(algebraMap S B s * algebraMap A B a) ⊗ₜ m`:
the cancellation isomorphism sends it to `s ⊗ₜ (a • m)`. This is the simple-tensor formula
behind `cancelBaseChange`, packaged so the two factors `S → B` and `A → B` are explicit. -/
private lemma cancelBaseChange_algebraMap_mul_tmul
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (s : S) (a : A) (m : M) :
    Algebra.IsPushout.cancelBaseChange R S A B M
      ((algebraMap S B s * algebraMap A B a) ⊗ₜ[A] m) = s ⊗ₜ[R] (a • m) := by
  have h1 : (algebraMap S B s * algebraMap A B a) ⊗ₜ[A] m
      = algebraMap S B s ⊗ₜ[A] (a • m) := by
    rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
  rw [h1]
  have h2 : algebraMap S B s ⊗ₜ[A] (a • m) = s • ((1 : B) ⊗ₜ[A] (a • m)) := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  rw [h2, LinearEquiv.map_smul, Algebra.IsPushout.cancelBaseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Value of `cancelBaseChange` on a simple tensor `(a ⊗ₜ s) ⊗ₜ m` of the concrete pushout
`TensorProduct R A S`: the cancellation isomorphism sends it to `s ⊗ₜ (a • m)`. -/
private lemma cancelBaseChange_tmul_tmul
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (a : A) (s : S) (m : M) :
    Algebra.IsPushout.cancelBaseChange R S A (TensorProduct R A S) M ((a ⊗ₜ[R] s) ⊗ₜ[A] m)
      = s ⊗ₜ[R] (a • m) := by
  have hb : (a ⊗ₜ[R] s : TensorProduct R A S)
      = algebraMap S (TensorProduct R A S) s * algebraMap A (TensorProduct R A S) a := by
    rw [Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_self_apply]
  rw [hb, cancelBaseChange_algebraMap_mul_tmul]

/-- **Compatibility of cancellation with localizing the outer base.** For a tower of commutative
rings `R → S → S'` and a homomorphism `R → A`, with the pushouts realized as the concrete tensor
products `A ⊗[R] S` and `A ⊗[R] S'`, the cancellation isomorphism
`Algebra.IsPushout.cancelBaseChange` for the `S'`-tower is the base change along `S → S'` of the
cancellation isomorphism for the `S`-tower. Concretely, the square with horizontal maps the two
`cancelBaseChange`s and vertical maps the `S → S'` base-change maps on `(A ⊗[R] S) ⊗[A] M` and on
`S ⊗[R] M` commutes. This is the purely commutative-algebraic "cancellation move" of the
affine-restriction naturality square; see blueprint `lem:cancelBaseChange_localization_compat`. -/
lemma cancelBaseChange_localization_compat
    {R S S' A : Type u} [CommRing R] [CommRing S] [CommRing S'] [CommRing A]
    [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S'] [Algebra R A]
    {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (x : TensorProduct A (TensorProduct R A S) M) :
    Algebra.IsPushout.cancelBaseChange R S' A (TensorProduct R A S') M
        (LinearMap.rTensor M
          (Algebra.TensorProduct.map (AlgHom.id A A) (IsScalarTower.toAlgHom R S S')).toLinearMap x)
      = LinearMap.rTensor M
          ((IsScalarTower.toAlgHom R S S').toLinearMap.restrictScalars R)
          (Algebra.IsPushout.cancelBaseChange R S A (TensorProduct R A S) M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | add b1 b2 hb1 hb2 => simp only [add_tmul, map_add, hb1, hb2]
    | tmul a s =>
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        IsScalarTower.coe_toAlgHom', LinearMap.coe_restrictScalars,
        cancelBaseChange_tmul_tmul]

/-- **Inverse form of `cancelBaseChange_localization_compat`.** The `cancelBaseChange⁻¹` of the
`S'`-tower is the base change along `S → S'` of the `cancelBaseChange⁻¹` of the `S`-tower. This is
the form directly consumed by the affine brick, which uses `cancelBaseChange.symm` (via
`baseChangeCancelModuleIso`). Derived from `cancelBaseChange_localization_compat` by injectivity of
the cancellation isomorphism. Project-local. -/
lemma cancelBaseChange_localization_compat_symm
    {R S S' A : Type u} [CommRing R] [CommRing S] [CommRing S'] [CommRing A]
    [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S'] [Algebra R A]
    {M : Type u} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (y : TensorProduct R S M) :
    LinearMap.rTensor M
        (Algebra.TensorProduct.map (AlgHom.id A A) (IsScalarTower.toAlgHom R S S')).toLinearMap
        ((Algebra.IsPushout.cancelBaseChange R S A (TensorProduct R A S) M).symm y)
      = (Algebra.IsPushout.cancelBaseChange R S' A (TensorProduct R A S') M).symm
          (LinearMap.rTensor M
            ((IsScalarTower.toAlgHom R S S').toLinearMap.restrictScalars R) y) := by
  apply (Algebra.IsPushout.cancelBaseChange R S' A (TensorProduct R A S') M).injective
  rw [cancelBaseChange_localization_compat, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end CancelBaseChangeCompat

/-! ## Project-local Mathlib supplement — general-scheme gluing scaffolding

The active concrete-tilde route to flat base change (Stacks 02KH) glues the affine-local
isomorphisms `affinePushforwardPullbackBaseChange` over the affine basis of `S'`. The gluing
(`pushforwardPullbackBaseChangeAbHom` → `…Hom` → `…NatIso`, blueprint §`sec:fbc_gluing`) is driven
by `TopCat.Sheaf.restrictHomEquivHom`, whose hypothesis is the *affine-restriction naturality* of
the brick: for an inclusion of affine opens `Spec R'' ⊆ Spec R'` of `S'` (over the same chosen
affine `Spec R ⊆ S`), the bricks `e_{R'}` and `e_{R''}` are intertwined by the structure-sheaf
restriction maps (blueprint `lem:pushforwardPullbackBaseChange_restrict_naturality`).

`BaseChangeChartTower` is the algebraic datum of that inclusion: the chosen affine chart datum
`(φ : R → A)` (the affine morphism `f` over `Spec R`, so `X_{Spec R} = Spec A`), the two base rings
`R'`, `R''` with the tower map `j : R' → R''` (the restriction `Spec R'' ⊆ Spec R'`), and the two
fully-affine pushout squares (= cartesian squares of affine schemes after `Spec`) realizing the
two charts `B' = A ⊗_R R'`, `B'' = A ⊗_R R''`. The two bricks `brickR'`/`brickR''` are exactly the
two `affinePushforwardPullbackBaseChange` isomorphisms the restriction square compares. -/

/-- **Chart-tower datum for the affine-restriction naturality of the base-change brick.** An
inclusion of affine opens `Spec R'' ⊆ Spec R'` of the base `S'`, both over the same chosen affine
`Spec R ⊆ S` (so `R → R' → R''` is a tower with `j` the restriction), together with the affine
chart datum `φ : R → A` (`X_{Spec R} = Spec A`) and the two fully-affine pushout squares realizing
the charts `B' = A ⊗_R R'`, `B'' = A ⊗_R R''`. This is the indexing datum of the general-scheme
gluing chain (blueprint §`sec:fbc_gluing`): the affine-restriction naturality lemma
`lem:pushforwardPullbackBaseChange_restrict_naturality` is stated against exactly this data,
comparing `brickR'` and `brickR''`. Project-local scaffolding. -/
structure BaseChangeChartTower where
  /-- The chosen affine `Spec R ⊆ S` over the `g`-image. -/
  R : CommRingCat.{u}
  /-- The affine chart `X_{Spec R} = Spec A` (`f` over `Spec R` is `Spec φ`). -/
  A : CommRingCat.{u}
  /-- The larger affine open `Spec R' ⊆ S'`. -/
  R' : CommRingCat.{u}
  /-- The smaller affine open `Spec R'' ⊆ Spec R'`. -/
  R'' : CommRingCat.{u}
  /-- The affine chart morphism `f|_{Spec R} = Spec φ`. -/
  φ : R ⟶ A
  /-- The base morphism `g|_{Spec R'} = Spec ψ`. -/
  ψ : R ⟶ R'
  /-- The restriction `Spec R'' ⊆ Spec R'`, i.e. the tower map `j : R' → R''`. -/
  j : R' ⟶ R''
  /-- The chart pushout `B' = A ⊗_R R'`. -/
  B' : CommRingCat.{u}
  /-- The chart pushout `B'' = A ⊗_R R''`. -/
  B'' : CommRingCat.{u}
  ρ' : A ⟶ B'
  σ' : R' ⟶ B'
  ρ'' : A ⟶ B''
  σ'' : R'' ⟶ B''
  /-- The `Spec R'`-chart square is a pushout (cartesian after `Spec`). -/
  h' : CategoryTheory.IsPushout φ ψ ρ' σ'
  /-- The `Spec R''`-chart square is a pushout (cartesian after `Spec`). -/
  h'' : CategoryTheory.IsPushout φ (ψ ≫ j) ρ'' σ''

namespace BaseChangeChartTower

variable (T : BaseChangeChartTower.{u})

/-- The canonical comparison `B' ⟶ B''` between the two chart pushouts, induced by the universal
property of `B' = A ⊗_R R'` applied to the cocone `(ρ'', j ≫ σ'')`. It is the affine model of the
restriction `X_{Spec R''} ⊆ X_{Spec R'}` on the total spaces. Project-local. -/
noncomputable def connect : T.B' ⟶ T.B'' :=
  T.h'.desc T.ρ'' (T.j ≫ T.σ'') (by rw [← Category.assoc]; exact T.h''.w)

@[reassoc] lemma inl_connect : T.ρ' ≫ T.connect = T.ρ'' := T.h'.inl_desc _ _ _

@[reassoc] lemma inr_connect : T.σ' ≫ T.connect = T.j ≫ T.σ'' := T.h'.inr_desc _ _ _

/-- The affine base-change brick `e_{R'}` over `Spec R'` (an isomorphism of `Spec R'`-modules):
`g^*(f_* M̃) ≅ f'_*((g')^* M̃)` in the fully-affine chart over `Spec R'`. Project-local. -/
noncomputable def brickR' (M : ModuleCat.{u} T.A) :
    (Scheme.Modules.pullback (Spec.map T.ψ)).obj
        ((Scheme.Modules.pushforward (Spec.map T.φ)).obj (tilde M)) ≅
      (Scheme.Modules.pushforward (Spec.map T.σ')).obj
        ((Scheme.Modules.pullback (Spec.map T.ρ')).obj (tilde M)) :=
  affinePushforwardPullbackBaseChange T.φ T.ψ T.ρ' T.σ' T.h' M

/-- The affine base-change brick `e_{R''}` over `Spec R''` (an isomorphism of `Spec R''`-modules),
for the composite base map `ψ ≫ j : R → R''`. Project-local. -/
noncomputable def brickR'' (M : ModuleCat.{u} T.A) :
    (Scheme.Modules.pullback (Spec.map (T.ψ ≫ T.j))).obj
        ((Scheme.Modules.pushforward (Spec.map T.φ)).obj (tilde M)) ≅
      (Scheme.Modules.pushforward (Spec.map T.σ'')).obj
        ((Scheme.Modules.pullback (Spec.map T.ρ'')).obj (tilde M)) :=
  affinePushforwardPullbackBaseChange T.φ (T.ψ ≫ T.j) T.ρ'' T.σ'' T.h'' M

end BaseChangeChartTower

end AlgebraicGeometry
