/-
Copyright (c) 2026 Archon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon
-/
import Mathlib

/-!
# Foundational cohomology/bundle interface

This file is the foundational cohomology/bundle interface over Mathlib
`Scheme.Modules`, corresponding to blueprint chapter
`Kemeny_PeerDependencies.tex`.

The substrate is supplied by Mathlib: for a scheme `X`, the category
`X.Modules` of sheaves of `𝒪_X`-modules is abelian and carries an additive
pushforward functor.  This file assembles, directly over that substrate, the
thin project-side foundational interface — the stalk-local isomorphism
criterion, the additive global-sections functor, a local-freeness predicate,
and the derived pushforward / sheaf-cohomology functors and base-change
comparison morphism — that the secant-bundle arguments invoke.  These
definitions are Archon-original infrastructure built directly over Mathlib; they
carry no external source.

The Grothendieck-abelian / injective-resolution bridge
(`found:modules_grothendieck_abelian`, `found:has_injective_resolutions`) is now
established here (`instIsGrothendieckAbelianModules`,
`instHasInjectiveResolutionsModules`): `AB5OfSize (SheafOfModules R)` and
`HasSeparator (SheafOfModules R)` are assembled directly over Mathlib (see the
heavy-bridge section), so `X.Modules` is Grothendieck abelian and has injective
resolutions unconditionally.  `higherDirectImage` (`R^if_*`) still lists
`[HasInjectiveResolutions X.Modules]` as an instance binder, but it is now
self-dischargeable.  The scalar sheaf cohomology `Scheme.HModule` is computed via
the *light* bridge in `TopCat.Sheaf Ab X` and returns an object of `Ab.{u}`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry

/-! ## Project-local Mathlib supplement — stalk-local isomorphism criterion -/

/-- Project-local (`def:peer_module_iso_locality`).

A morphism of `𝒪_X`-modules is an isomorphism if and only if the induced
morphism on every stalk of the underlying sheaf of abelian groups is an
isomorphism.  This reduces, via the faithful and iso-reflecting forgetful
functor `Scheme.Modules.toPresheaf`, to the stalkwise criterion for sheaves on
the underlying topological space of `X`.  Replaces the former `opaque … : Prop
:= True` peer stub with a real theorem. -/
theorem Modules.isIso_iff_isIso_stalkFunctor_map {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) :
    IsIso φ ↔ ∀ x : X,
      IsIso ((TopCat.Presheaf.stalkFunctor _ x).map ((Scheme.Modules.toPresheaf X).map φ)) := by
  rw [← isIso_iff_of_reflects_iso φ (Scheme.Modules.toPresheaf X)]
  let sh : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) ⟶ ⟨N.presheaf, N.isSheaf⟩ :=
    ⟨(Scheme.Modules.toPresheaf X).map φ⟩
  have key := TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso sh
  refine ⟨fun h x => ?_, fun h => ?_⟩
  · haveI : IsIso ((sheafToPresheaf _ Ab).map sh) := h
    exact key.mp ((fullyFaithfulSheafToPresheaf _ _).isIso_of_isIso_map sh) x
  · haveI : IsIso sh := key.mpr h
    exact (inferInstance : IsIso ((sheafToPresheaf _ Ab).map sh))

/-! ## Project-local Mathlib supplement — additive global sections -/

/-- The forgetful functor to abelian-group presheaves is additive.  Project-local
because the additivity of the underlying `SheafOfModules.forget` does not transfer
through the `Scheme.Modules.toPresheaf` definition during instance synthesis. -/
instance Scheme.Modules.toPresheaf_additive (X : Scheme.{u}) :
    (Scheme.Modules.toPresheaf X).Additive :=
  inferInstanceAs (SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf X.ringCatSheaf.obj).Additive

/-- Project-local (`found:global_sections_ab`).

The additive global-sections functor `Γ_Ab : X.Modules ⥤ AddCommGrpCat`, sending
an `𝒪_X`-module `ℱ` to its abelian group of global sections `ℱ(X)` and a
morphism to its induced map on global sections.  It is the composition of the
forgetful functor to abelian-group presheaves with evaluation at the top open.
It is the module-level `Γ` comparison anchor; sheaf cohomology itself is
right-derived from the sheaf-level global sections of the light bridge, not from
this functor directly. -/
noncomputable def Scheme.globalSectionsAb (X : Scheme.{u}) : X.Modules ⥤ AddCommGrpCat :=
  Scheme.Modules.toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (Opposite.op ⊤)

/-- The additive global-sections functor is additive (it is a composition of the
additive forgetful functor with an additive evaluation functor). -/
instance Scheme.globalSectionsAb_additive (X : Scheme.{u}) :
    (Scheme.globalSectionsAb X).Additive where
  map_add {M N f g} := by
    change ((Scheme.Modules.toPresheaf X).map (f + g)).app (Opposite.op ⊤) =
      ((Scheme.Modules.toPresheaf X).map f).app (Opposite.op ⊤) +
      ((Scheme.Modules.toPresheaf X).map g).app (Opposite.op ⊤)
    rw [Functor.map_add]
    rfl

/-! ## Project-local Mathlib supplement — local freeness -/

/-- Project-local (`found:locally_free`).

The predicate that an `𝒪_X`-module `ℱ` is locally free (of some constant finite
rank `r`): `X` is covered by open subsets on which the restriction of `ℱ` is
isomorphic to the free `𝒪`-module `𝒪^{⊕ r}`.  Modelled, following
`SheafOfModules.isQuasicoherent`, as a structural predicate on `X.Modules`
rather than a bundled structure.  Kemeny's "locally free of rank `k`" assertions
are instances of this predicate.  The rank is recorded as a finite index type
`I` (of cardinality the rank); local freeness of constant finite rank. -/
def Scheme.Modules.IsLocallyFree {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∃ (I : Type u) (_ : Finite I), ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U),
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj F ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) I))

/-! ## Project-local Mathlib supplement — light cohomology bridge

This is the *light* tier of the two-tier cohomology bridge.  Scalar sheaf
cohomology `H^i(X, ℱ)` only needs derived functors in the category
`TopCat.Sheaf Ab X` of abelian-group sheaves on the (essentially small) site of
opens of `X`.  That category is *literally* of the form `CategoryTheory.Sheaf J
Ab` (`TopCat.Sheaf C X` unfolds to `Sheaf (Opens.grothendieckTopology X) C`), so
Mathlib's `Sheaf.isGrothendieckAbelian_of_essentiallySmall` applies directly and
makes it Grothendieck abelian — hence equipped with injective resolutions —
*unconditionally*, with no `SheafOfModules`-level `AB5`/`HasSeparator` obligation.

All universes are pinned (`TopCat.Sheaf.{u} Ab.{u} X` for `X : Scheme.{u}`):
`Ab` and the sheaf category carry free universe parameters whose
metavariable-laden synthesis otherwise blocks `Abelian`/`EnoughInjectives`
instance resolution; pinning them to `u` keeps the chain
`IsGrothendieckAbelian → EnoughInjectives → HasInjectiveResolutions` defeq-stable. -/

/-- Project-local (`found:modules_to_absheaf`).

The forgetful functor `(-)^{Ab} : X.Modules ⥤ TopCat.Sheaf Ab X` sending an
`𝒪_X`-module to its underlying sheaf of abelian groups.  It is the lift, through
the fully faithful `sheafToPresheaf`, of the existing forgetful functor
`Scheme.Modules.toPresheaf` to abelian-group presheaves: every `𝒪_X`-module's
underlying presheaf is a sheaf, so the lift exists, and functoriality is
inherited from `toPresheaf`.  This is the functor along which scalar sheaf
cohomology is computed. -/
noncomputable def Scheme.Modules.toAbSheaf (X : Scheme.{u}) :
    X.Modules ⥤ TopCat.Sheaf.{u} Ab.{u} X where
  obj M := ⟨M.presheaf, M.isSheaf⟩
  map φ := ⟨(Scheme.Modules.toPresheaf X).map φ⟩
  map_id M := by apply Sheaf.hom_ext; exact (Scheme.Modules.toPresheaf X).map_id M
  map_comp f g := by apply Sheaf.hom_ext; exact (Scheme.Modules.toPresheaf X).map_comp f g

/-- Project-local (`found:absheaf_groth_abelian`).

The category `TopCat.Sheaf Ab X` of abelian-group sheaves on a scheme `X` is
Grothendieck abelian.  Since `TopCat.Sheaf Ab X` unfolds to `Sheaf
(Opens.grothendieckTopology X) Ab`, this is a direct application of
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`: `Ab` is
Grothendieck abelian, the site of opens is essentially small, and abelian-group
presheaves have sheafification. -/
instance instIsGrothendieckAbelianTopCatSheafAb (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u} (TopCat.Sheaf.{u} Ab.{u} X) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (Opens.grothendieckTopology (X : TopCat)) Ab.{u}

/-- Project-local helper: abelian-group sheaves on a scheme have enough
injectives.  Immediate from `instIsGrothendieckAbelianTopCatSheafAb` via
`IsGrothendieckAbelian.enoughInjectives`; isolated as an instance so that the
`HasInjectiveResolutions` instance below and the right-derived global-sections
functor can synthesize it. -/
noncomputable instance instEnoughInjectivesTopCatSheafAb (X : Scheme.{u}) :
    EnoughInjectives (TopCat.Sheaf.{u} Ab.{u} X) :=
  IsGrothendieckAbelian.enoughInjectives

/-- Project-local (`found:absheaf_has_injective_resolutions`).

The category `TopCat.Sheaf Ab X` has injective resolutions: being Grothendieck
abelian it has enough injectives (`instEnoughInjectivesTopCatSheafAb`), and an
abelian category with enough injectives admits an injective resolution of every
object. -/
noncomputable instance instHasInjectiveResolutionsTopCatSheafAb (X : Scheme.{u}) :
    HasInjectiveResolutions (TopCat.Sheaf.{u} Ab.{u} X) :=
  ⟨fun Z => InjectiveResolution.instHasInjectiveResolution Z⟩

/-- Project-local: the additive global-sections functor on abelian-group sheaves,
`Γ : TopCat.Sheaf Ab X ⥤ Ab`, evaluation of the underlying presheaf at the top
open `⊤`.  Mirrors `Scheme.globalSectionsAb` one level up, on the sheaf category
where the light injective-resolution bridge lives; right-deriving it computes
scalar sheaf cohomology. -/
noncomputable def Scheme.absheafGlobalSections (X : Scheme.{u}) :
    TopCat.Sheaf.{u} Ab.{u} X ⥤ Ab.{u} :=
  TopCat.Sheaf.forget Ab X ⋙ (CategoryTheory.evaluation _ _).obj (Opposite.op ⊤)

/-- The sheaf-level global-sections functor is additive (forgetful inclusion to
abelian-group presheaves composed with the additive evaluation at `⊤`). -/
instance Scheme.absheafGlobalSections_additive (X : Scheme.{u}) :
    (Scheme.absheafGlobalSections X).Additive where
  map_add {M N f g} := by
    change ((TopCat.Sheaf.forget Ab X).map (f + g)).app (Opposite.op ⊤) =
      ((TopCat.Sheaf.forget Ab X).map f).app (Opposite.op ⊤) +
      ((TopCat.Sheaf.forget Ab X).map g).app (Opposite.op ⊤)
    rw [Functor.map_add]; rfl

/-! ## Project-local Mathlib supplement — heavy cohomology bridge

This is the *heavy* tier of the two-tier cohomology bridge.  Higher direct
images `R^if_*` are right-derived in the module category `X.Modules` itself, so
unlike scalar `H^i` they genuinely need `X.Modules` to be Grothendieck abelian.
Sheaves of modules over the *varying* structure ring sheaf are not literally
objects of a category `Sheaf J A`, so `Sheaf.isGrothendieckAbelian_of_essentiallySmall`
does **not** apply; Grothendieck-abelianness must be assembled from its
constituent axioms — `AB5` exactness of filtered colimits and a separator.

The chain is built generically over a sheaf of rings `R` on a small site and
then specialised to `X.Modules = SheafOfModules X.ringCatSheaf`:

* `AB5` for `PresheafOfModules R₀` (filtered colimits exact, detected through the
  forgetful functor to abelian-group presheaves, which is itself a functor
  category to the `AB5` category `Ab`);
* `AB5` for `SheafOfModules R` (transported across the exact sheafification left
  adjoint `PresheafOfModules.sheafification (𝟙 R.obj)`);
* a separator for `SheafOfModules R` (the sheafification of the small separating
  family `PresheafOfModules.freeYoneda` of free-Yoneda presheaves of modules);
* `IsGrothendieckAbelian` for `SheafOfModules R`, hence for `X.Modules`,
  assembling local smallness, filtered colimits, `AB5`, and the separator;
* injective resolutions for `X.Modules`, discharging the
  `[HasInjectiveResolutions X.Modules]` hypothesis carried by `higherDirectImage`.

All universes are pinned to `u` (`AB5OfSize.{u, u}`, `IsGrothendieckAbelian.{u}`
for `X : Scheme.{u}`); the size parameter `w` of the Grothendieck axioms must be
fixed to `u` or the `AB5OfSize`/`HasSeparator` fields fail to align during
synthesis. -/

/-- Project-local (`found:presheafmod_ab5`).

The category `PresheafOfModules R₀` of presheaves of modules over a presheaf of
rings `R₀` satisfies `AB5OfSize`: it has filtered colimits and these are exact.
Filtered colimits are exact in `Ab` (`instAB5AddCommGrp`), hence in the functor
category `Cᵒᵖ ⥤ Ab` of abelian-group presheaves, and the forgetful functor
`PresheafOfModules.toPresheaf` preserves colimits while reflecting and preserving
finite limits, so `HasExactColimitsOfShape.domain_of_functor` transports the
exactness back to `PresheafOfModules R₀`. -/
instance instAB5OfSizePresheafOfModules {C : Type*} [Category C] (R₀ : Cᵒᵖ ⥤ RingCat.{u}) :
    AB5OfSize.{u, u} (PresheafOfModules.{u} R₀) where
  ofShape K _ _ := by
    haveI : HasExactColimitsOfShape K Ab.{u} := CategoryTheory.AB5OfSize.ofShape (C := Ab.{u}) K
    haveI : HasExactColimitsOfShape K (Cᵒᵖ ⥤ Ab.{u}) := inferInstance
    exact HasExactColimitsOfShape.domain_of_functor K (PresheafOfModules.toPresheaf R₀)

/-- Project-local helper: a separating family transports along a left adjoint
whose right adjoint is faithful.  If `S : β → C` is separating and `F ⊣ Gr` with
`Gr` faithful, then the family `b ↦ F.obj (S b)` is separating in the target.
Used to sheafify the presheaf-of-modules separating family
(`PresheafOfModules.freeYoneda`) into a separating family of sheaves of modules. -/
private theorem isSeparating_ofObj_leftAdjoint {C' : Type*} [Category C'] {β : Type*} {S : β → C'}
    {D : Type*} [Category D] {F : C' ⥤ D} {Gr : D ⥤ C'}
    (adj : F ⊣ Gr) [Gr.Faithful]
    (hS : ObjectProperty.IsSeparating (.ofObj S)) :
    ObjectProperty.IsSeparating (.ofObj (fun b => F.obj (S b))) := by
  intro X Y f g H
  apply Gr.map_injective
  refine hS (Gr.map f) (Gr.map g) ?_
  rintro Z hZ k
  obtain ⟨b, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hZ
  have hh := H _ (ObjectProperty.ofObj_apply (fun b => F.obj (S b)) b) ((adj.homEquiv _ _).symm k)
  simpa [Adjunction.homEquiv_naturality_right] using congrArg (adj.homEquiv (S b) Y) hh

section HeavyBridge

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Project-local (`found:sheafmod_ab5`).

The category `SheafOfModules R` of sheaves of modules over a sheaf of rings `R`
on a small site satisfies `AB5OfSize`.  Filtered colimits of sheaves of modules
are computed by sheafifying the corresponding presheaf colimit; transporting the
presheaf-level `AB5` (`instAB5OfSizePresheafOfModules`) across the exact
sheafification adjunction `PresheafOfModules.sheafification (𝟙 R.obj)`, whose
right adjoint is fully faithful, yields exactness of filtered colimits at the
sheaf level via `Adjunction.hasExactColimitsOfShape`. -/
instance instAB5OfSizeSheafOfModules : AB5OfSize.{u, u} (SheafOfModules.{u} R) where
  ofShape K _ _ := by
    haveI : Presheaf.IsLocallyInjective J (𝟙 R.obj) := inferInstance
    haveI : Presheaf.IsLocallySurjective J (𝟙 R.obj) := inferInstance
    have adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
    haveI : HasExactColimitsOfShape K (PresheafOfModules R.obj) :=
      CategoryTheory.AB5OfSize.ofShape (C := PresheafOfModules R.obj) K
    exact adj.hasExactColimitsOfShape K

/-- Project-local (`found:sheafmod_separator`).

The category `SheafOfModules R` has a separator.  The presheaf category
`PresheafOfModules R.obj` has the small separating family `freeYoneda` of free
presheaves of modules on Yoneda presheaves (`PresheafOfModules.freeYoneda.isSeparating`);
its image under the sheafification left adjoint is a separating family of sheaves
of modules (`isSeparating_ofObj_leftAdjoint`, since the right adjoint is
faithful), and the coproduct of a separating family is a separator
(`isSeparator_sigma`). -/
instance instHasSeparatorSheafOfModules : HasSeparator (SheafOfModules.{u} R) := by
  haveI : Presheaf.IsLocallyInjective J (𝟙 R.obj) := inferInstance
  haveI : Presheaf.IsLocallySurjective J (𝟙 R.obj) := inferInstance
  have adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  exact ⟨_, (isSeparator_sigma _).2
    (isSeparating_ofObj_leftAdjoint adj (PresheafOfModules.freeYoneda.isSeparating R.obj))⟩

/-- Project-local: `SheafOfModules R` is Grothendieck abelian.  Assembles the four
Grothendieck-abelian data on the abelian category `SheafOfModules R`: local
smallness and filtered colimits hold by inference, `AB5` is
`instAB5OfSizeSheafOfModules`, and the separator is `instHasSeparatorSheafOfModules`.
Keyed on the `SheafOfModules` head so that `instIsGrothendieckAbelianModules` can
transfer it to `X.Modules`. -/
instance instIsGrothendieckAbelianSheafOfModules :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) where

end HeavyBridge

/-- Project-local (`found:modules_grothendieck_abelian`).

For every scheme `X`, the category `X.Modules` of `𝒪_X`-modules is Grothendieck
abelian.  Since `X.Modules = SheafOfModules X.ringCatSheaf`, this is
`instIsGrothendieckAbelianSheafOfModules` applied to the structure ring sheaf,
transferred across the definitional equality (instance resolution does not unfold
the `Scheme.Modules` def on its own, so the transfer is made explicit). -/
instance instIsGrothendieckAbelianModules (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u} X.Modules :=
  inferInstanceAs (IsGrothendieckAbelian.{u} (SheafOfModules.{u} X.ringCatSheaf))

/-- Project-local (`found:has_injective_resolutions`).

For every scheme `X`, the category `X.Modules` has injective resolutions.  Being
Grothendieck abelian (`instIsGrothendieckAbelianModules`) it has enough
injectives, and an abelian category with enough injectives admits an injective
resolution of every object.  This discharges the `[HasInjectiveResolutions
X.Modules]` hypothesis carried by `higherDirectImage` (`R^if_*`). -/
noncomputable instance instHasInjectiveResolutionsModules (X : Scheme.{u}) :
    HasInjectiveResolutions X.Modules :=
  letI : EnoughInjectives X.Modules :=
    inferInstanceAs (EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf))
  ⟨fun Z => InjectiveResolution.instHasInjectiveResolution Z⟩

/-! ## Project-local Mathlib supplement — derived pushforward and cohomology

The higher direct image `R^if_*` is the `i`-th right-derived functor of the
additive pushforward, computed in the module category `X.Modules`, and therefore
requires `HasInjectiveResolutions X.Modules` — the *heavy* bridge
`found:has_injective_resolutions`, which follows from `IsGrothendieckAbelian
X.Modules` (`found:modules_grothendieck_abelian`) and reduces to the genuinely
not-in-Mathlib `AB5OfSize (SheafOfModules R)` and `HasSeparator (SheafOfModules
R)`.  That bridge is now established earlier in this file
(`instHasInjectiveResolutionsModules`), so although `higherDirectImage` still
lists `[HasInjectiveResolutions X.Modules]` as an instance binder it is
self-dischargeable.

Scalar sheaf cohomology `H^i(X, ℱ)`, by contrast, is now *unconditional*: it is
computed via the light bridge above, deriving the abelian-group-sheaf global
sections functor, which has injective resolutions with no hypothesis on
`X.Modules`. -/

/-- Project-local (`def:peer_higher_direct_image`).

The higher direct image `R^i f_* ℱ` is the `i`-th right-derived functor of the
additive pushforward `f_*`.  Replaces the former `opaque … : Type := Unit` peer
stub with the genuine functor `X.Modules ⥤ Y.Modules`. -/
noncomputable def higherDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [HasInjectiveResolutions X.Modules] : X.Modules ⥤ Y.Modules :=
  (Scheme.Modules.pushforward f).rightDerived n

/-- Project-local (`def:peer_scheme_hmodule`).

Sheaf cohomology `H^i(X, ℱ)`, computed via the *light* bridge: it is the `i`-th
right-derived functor of the abelian-group-sheaf global-sections functor
`Scheme.absheafGlobalSections`, evaluated at the underlying abelian-group sheaf
`(toAbSheaf X).obj ℱ` of `ℱ`.  This is now *unconditional* — injective
resolutions in `TopCat.Sheaf Ab X` are supplied by
`instHasInjectiveResolutionsTopCatSheafAb`, requiring no hypothesis on
`X.Modules`.  Replaces the former hypothesis-bearing definition. -/
noncomputable def Scheme.HModule {X : Scheme.{u}} (i : ℕ) (F : X.Modules) : Ab.{u} :=
  ((Scheme.absheafGlobalSections X).rightDerived i).obj ((Scheme.Modules.toAbSheaf X).obj F)

/-! ## Project-local Mathlib supplement — base-change comparison morphism -/

/-- Project-local (`def:peer_affine_pushforward_base_change`).

The base-change comparison natural transformation `g^* f_* ⟶ f'_* g'^*` attached
to a commutative square
```
  X' --g'--> X
  f'|        |f
    v        v
  Y' --g-->  Y
```
of schemes (`h : f' ≫ g = g' ≫ f`).  It is the Beck–Chevalley mate, under the
two `pullback ⊣ pushforward` adjunctions, of the canonical comparison
`g^* ∘ f'^* ≅ f^* ∘ g'^*` of inverse-image functors (built from `pullbackComp`
and the square).  Commutativity alone defines the morphism; cartesianness of the
square (not required here) is what makes it an isomorphism.  Replaces the former
`opaque … : Type := Unit` peer stub with the genuine morphism of functors. -/
noncomputable def pushforwardBaseChangeMap
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback g' ⋙ Scheme.Modules.pushforward f' :=
  (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f')
      ((Scheme.Modules.pullbackComp f' g).hom ≫ (Scheme.Modules.pullbackCongr h).hom ≫
        (Scheme.Modules.pullbackComp g' f).inv)).natTrans

/-! ## Project-local Mathlib supplement — commutative ring structure on structure-sheaf sections

The structure ring sheaf `X.ringCatSheaf` of a scheme is `RingCat`-valued, so its
sections `X.ringCatSheaf(U)` present at the type level only as a (possibly
noncommutative) ring: Mathlib forgets that `X.ringCatSheaf` is the image of the
`CommRingCat`-valued structure sheaf `𝒪_X = X.presheaf` under the forgetful
functor `CommRingCat ⥤ RingCat`, so `CommRing (X.ringCatSheaf.val.obj U)` does not
synthesize.  This is the key obstruction to applying the (commutative-base)
exterior/symmetric power functors openwise on a `PresheafOfModules X.ringCatSheaf.val`,
and `ringCatSheaf_commRing` removes it. -/

/-- Project-local (`found:ringcatsheaf_commring`).

The value `X.ringCatSheaf(U)` of the structure ring sheaf — a priori only an object
of `RingCat` — carries a commutative-ring structure, recovered from the
`CommRingCat`-valued structure-sheaf sections `𝒪_X(U) = X.presheaf.obj U`.  The two
carriers are definitionally equal (the ring sheaf is the image of `𝒪_X` under
`forget₂ CommRingCat RingCat`), so the `CommRing` instance transports directly.
Supplied as a `def` (not a global instance) to avoid a `Ring`-diamond against the
`RingCat`-level ring structure; downstream uses it via `letI`. -/
@[reducible] noncomputable def Scheme.ringCatSheaf_commRing (X : Scheme.{u}) (U : (Opens X)ᵒᵖ) :
    CommRing (X.ringCatSheaf.presheaf.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

end AlgebraicGeometry

/-! ## Project-local Mathlib supplement — symmetric power functor

Mathlib provides only the *type* `SymmetricPower R ι M`
(`Mathlib.LinearAlgebra.TensorPower.Symmetric`), as the quotient of the `ι`-fold
tensor power `⨂[R] (_ : ι), M` by the symmetrisation relation, together with its
module instances and the canonical maps `mk` / `tprod`.  The functorial action on
morphisms and its packaging as a functor on `ModuleCat R` are an explicit Mathlib
TODO; both are built here, mirroring the existing `ModuleCat.exteriorPower.functor`
chain.  This is the symmetric-power analogue of the exterior-power functor anchor
`mathlib:exterior_power_functor`, supplying the `\uses` dependency
`found:modulecat_sym_power` of the secant-bundle filtration arguments.

The construction is two-layer, exactly as the exterior case:

* Layer 1 (linear algebra): `SymmetricPower.map (f : M →ₗ[R] N) : Sym ι M →ₗ Sym ι N`,
  obtained by descending `mk ∘ PiTensorProduct.map (fun _ => f)` through the
  symmetrisation quotient — well-defined because `PiTensorProduct.map` acts
  factorwise (`PiTensorProduct.map_tprod`) and the result is permutation-invariant
  (`SymmetricPower.tprod_equiv`).  Functoriality (`map_id`, `map_comp`) descends
  from `PiTensorProduct.map_id` / `map_comp` via `span_tprod_eq_top`.
* Layer 2 (categorical wrapper): `ModuleCat.symmetricPower.functor`.

UNIVERSE NOTE: `SymmetricPower (R ι : Type u)` couples the ring and the index type
in the *same* universe `u`, so the categorical functor indexes the `n`-th power by
`ULift.{u} (Fin n)` (not `Fin n`, which would force `R : Type 0`); this is the one
shape difference from the exterior twin. -/

open scoped TensorProduct
open TensorProduct

namespace SymmetricPower

variable {R ι : Type u} [CommSemiring R] {M N P : Type*}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- The composite linear map `(⨂[R] _:ι, M) →ₗ Sym[R] ι N` underlying
`SymmetricPower.map f`: factorwise application of `f` followed by symmetrisation. -/
private noncomputable def mapAux (f : M →ₗ[R] N) : (⨂[R] (_ : ι), M) →ₗ[R] Sym[R] ι N :=
  (SymmetricPower.mk R ι N).comp (PiTensorProduct.map (fun _ => f))

/-- `mapAux f` is constant on symmetrisation-equivalence classes: the factorwise
action commutes with permutations, so it descends to the symmetric power. -/
private theorem mapAux_respects (f : M →ₗ[R] N) :
    addConGen (Rel R ι M) ≤ AddCon.ker (mapAux f).toAddMonoidHom := by
  apply AddCon.addConGen_le
  rintro _ _ ⟨e, g⟩
  change mapAux f (⨂ₜ[R] i, g i) = mapAux f (⨂ₜ[R] i, g (e i))
  simp only [mapAux, LinearMap.comp_apply, PiTensorProduct.map_tprod]
  change (⨂ₛ[R] i, f (g i)) = ⨂ₛ[R] i, f (g (e i))
  rw [tprod_equiv e (fun i => f (g i))]

/-- Project-local (`found:modulecat_sym_power`, layer 1).

The functorial action of the `ι`-indexed symmetric power on a linear map
`f : M →ₗ[R] N`, obtained by descending `SymmetricPower.mk ∘ PiTensorProduct.map f`
through the symmetrisation quotient (well-definedness is `mapAux_respects`).  This
is the linear-algebra ingredient that Mathlib lists as a TODO; the categorical
`ModuleCat.symmetricPower.functor` is a thin wrapper over it. -/
noncomputable def map (f : M →ₗ[R] N) : Sym[R] ι M →ₗ[R] Sym[R] ι N where
  toAddHom := (AddCon.lift _ (mapAux f).toAddMonoidHom (mapAux_respects f)).toAddHom
  map_smul' r x := by
    induction x using AddCon.induction_on with
    | H a =>
      change mapAux f (r • a) = (RingHom.id R) r • mapAux f a
      rw [RingHom.id_apply, map_smul]

/-- `SymmetricPower.map` acts factorwise on pure symmetric tensors. -/
@[simp] theorem map_tprod (f : M →ₗ[R] N) (g : ι → M) :
    map f (⨂ₛ[R] i, g i) = ⨂ₛ[R] i, f (g i) := by
  change mapAux f (PiTensorProduct.tprod R g) = _
  simp only [mapAux, LinearMap.comp_apply, PiTensorProduct.map_tprod]; rfl

variable (ι M) in
/-- `SymmetricPower.map` preserves identities. -/
@[simp] theorem map_id :
    (map (LinearMap.id : M →ₗ[R] M) : Sym[R] ι M →ₗ[R] Sym[R] ι M) = LinearMap.id := by
  apply LinearMap.ext_on (span_tprod_eq_top R ι M); rintro _ ⟨g, rfl⟩; simp [map_tprod]

/-- `SymmetricPower.map` preserves composition. -/
theorem map_comp (f : M →ₗ[R] N) (h : N →ₗ[R] P) :
    (map (h ∘ₗ f) : Sym[R] ι M →ₗ[R] Sym[R] ι P) = (map h) ∘ₗ (map f) := by
  apply LinearMap.ext_on (span_tprod_eq_top R ι M); rintro _ ⟨g, rfl⟩; simp [map_tprod]

end SymmetricPower

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Project-local (`found:modulecat_sym_power`, layer 2).

The `n`-th symmetric power of an object of `ModuleCat R`, indexed by
`ULift.{u} (Fin n)` to keep the ring/index universe coupling of `SymmetricPower`
satisfied while leaving `R : Type u` general (mirroring `ModuleCat.exteriorPower`). -/
noncomputable def symmetricPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (SymmetricPower R (ULift.{u} (Fin n)) M)

namespace symmetricPower

/-- The morphism `M.symmetricPower n ⟶ N.symmetricPower n` induced by `f : M ⟶ N`,
the categorical wrapper of `SymmetricPower.map`. -/
noncomputable def map {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℕ) :
    M.symmetricPower n ⟶ N.symmetricPower n :=
  ofHom (SymmetricPower.map f.hom)

variable (R) in
/-- Project-local (`found:modulecat_sym_power`).

The `n`-th symmetric power as a functor `ModuleCat R ⥤ ModuleCat R`,
`M ↦ Sym^n M`, `f ↦ Sym^n f`.  This is the symmetric-power analogue of
`ModuleCat.exteriorPower.functor`, absent from Mathlib (only the underlying type
`SymmetricPower` is provided).  Functoriality is `SymmetricPower.map_id` /
`map_comp`. -/
@[simps]
noncomputable def functor (n : ℕ) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} R where
  obj M := M.symmetricPower n
  map f := map f n
  map_id M := by
    apply ModuleCat.hom_ext
    simp only [map, ModuleCat.hom_id, SymmetricPower.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [map, ModuleCat.hom_comp, SymmetricPower.map_comp]
    rfl

end symmetricPower

end ModuleCat

/-! ## Project-local Mathlib supplement — base change of symmetric powers

Mathlib provides the symmetric-power type `SymmetricPower R ι M` over a *fixed*
base ring `R`, and the functorial action `SymmetricPower.map` along an `R`-linear
map is built above, but neither has any variance in the base ring.  For the
openwise symmetric power on a presheaf of modules the transition maps run over a
*ring homomorphism* `R(U) → R(V)` (the restriction maps are semilinear, not
linear), so a base-change comparison `Sym^i_A N → Sym^i_B N` over an algebra map
`A → B` is needed.  This is the symmetric analogue of
`ModuleCat.exteriorPower.baseChange` below.

The A-module structure on the target `Sym[B] ι N` (and the scalar tower
`IsScalarTower A B (Sym[B] ι N)`) are taken as explicit instance binders: they do
*not* synthesize from `[Algebra A B] [Module B (Sym[B] ι N)]` alone (diamond
avoidance), and at the point of use (the categorical wrapper) they are exactly the
structures installed by `ModuleCat.restrictScalars`. -/

namespace SymmetricPower

variable {A B ι : Type u} [CommSemiring A] [CommSemiring B] [Algebra A B]
  {N : Type*} [AddCommMonoid N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- Underlying A-linear map `(⨂[A] _:ι, N) →ₗ[A] Sym[B] ι N` for base change:
factorwise symmetrisation over `B`, viewed as `A`-multilinear via restriction of
scalars and lifted through the `A`-tensor power's universal property. -/
private noncomputable def baseChangeAux
    [Module A (Sym[B] ι N)] [IsScalarTower A B (Sym[B] ι N)] :
    (⨂[A] (_ : ι), N) →ₗ[A] Sym[B] ι N :=
  PiTensorProduct.lift ((SymmetricPower.tprod B (ι := ι) (M := N)).restrictScalars A)

private theorem baseChangeAux_apply_tprod
    [Module A (Sym[B] ι N)] [IsScalarTower A B (Sym[B] ι N)] (g : ι → N) :
    baseChangeAux (⨂ₜ[A] i, g i) = (⨂ₛ[B] i, g i) := by
  simp only [baseChangeAux, PiTensorProduct.lift.tprod]
  rfl

private theorem baseChangeAux_respects
    [Module A (Sym[B] ι N)] [IsScalarTower A B (Sym[B] ι N)] :
    addConGen (Rel A ι N) ≤
      AddCon.ker (baseChangeAux (A := A) (B := B) (ι := ι) (N := N)).toAddMonoidHom := by
  apply AddCon.addConGen_le
  rintro _ _ ⟨e, g⟩
  change baseChangeAux (⨂ₜ[A] i, g i) = baseChangeAux (⨂ₜ[A] i, g (e i))
  rw [baseChangeAux_apply_tprod, baseChangeAux_apply_tprod, tprod_equiv e g]

/-- Project-local (`found:sympow_base_change_linear`).

The linear-algebra base-change comparison `Sym^i_A N → Sym^i_B N`, the `A`-linear
map from the symmetric power formed over `A` to the one formed over the `A`-algebra
`B`, acting as the identity on representatives of decomposable symmetric tensors
(`baseChange_tprod`).  Obtained by descending the factorwise symmetrising map
`baseChangeAux` through the `A`-symmetrisation quotient (well-definedness is
`baseChangeAux_respects`, from perm-invariance over `B`).  Mathlib supplies no
variance of the symmetric power in the base ring, so this is project infrastructure;
it is the symmetric twin of `ModuleCat.exteriorPower.baseChange`. -/
noncomputable def baseChange
    [Module A (Sym[B] ι N)] [IsScalarTower A B (Sym[B] ι N)] :
    Sym[A] ι N →ₗ[A] Sym[B] ι N where
  toAddHom := (AddCon.lift _ (baseChangeAux (A := A) (B := B) (ι := ι) (N := N)).toAddMonoidHom
    baseChangeAux_respects).toAddHom
  map_smul' r x := by
    induction x using AddCon.induction_on with
    | H a =>
      change baseChangeAux (r • a) = (RingHom.id A) r • baseChangeAux a
      rw [RingHom.id_apply, map_smul]

/-- `SymmetricPower.baseChange` acts as the identity on representatives of
decomposable symmetric tensors. -/
@[simp] theorem baseChange_tprod
    [Module A (Sym[B] ι N)] [IsScalarTower A B (Sym[B] ι N)] (g : ι → N) :
    baseChange (⨂ₛ[A] i, g i) = (⨂ₛ[B] i, g i) := by
  change baseChangeAux (⨂ₜ[A] i, g i) = _
  rw [baseChangeAux_apply_tprod]

end SymmetricPower

/-! ## Project-local Mathlib supplement — base change of exterior powers

Mathlib provides the exterior power `⋀[R]^n M` and (via
`ModuleCat.exteriorPower.functor`) its functoriality over a *fixed* commutative
base `R`, but not its variance in the base ring.  The openwise exterior power on a
presheaf of modules needs the transition maps to run over the (semilinear)
restriction ring maps `R(U) → R(V)`, so a base-change comparison `⋀^i_A N → ⋀^i_B N`
over an algebra map `A → B` is required.  As on the symmetric side, the A-module
structure on the target `⋀[B]^n N` and the scalar tower are taken as explicit
instance binders (they do not synthesize from `[Algebra A B] [Module B N]`). -/

namespace ModuleCat.exteriorPower

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- The A-alternating map `N [⋀^Fin n]→ₗ[A] ⋀[B]^n N` underlying base change: the
canonical B-alternating map `exteriorPower.ιMulti B n` into `⋀[B]^n N`, viewed as
A-alternating via restriction of scalars (the alternating condition is preserved). -/
noncomputable def baseChangeAlt (n : ℕ)
    [Module A (⋀[B]^n N)] [IsScalarTower A B (⋀[B]^n N)] :
    N [⋀^Fin n]→ₗ[A] (⋀[B]^n N) :=
  AlternatingMap.mk
    (MultilinearMap.restrictScalars A (exteriorPower.ιMulti B n).toMultilinearMap)
    (fun v _ _ h hij => (exteriorPower.ιMulti B n).map_eq_zero_of_eq v h hij)

/-- Project-local (`found:exterior_base_change_linear`).

The linear-algebra base-change comparison `⋀^i_A N → ⋀^i_B N`, the `A`-linear map
from the exterior power formed over `A` to the one formed over the `A`-algebra `B`,
acting as the identity on representatives of decomposable wedges
(`baseChange_apply_ιMulti`).  Obtained from the universal property of `⋀[A]^n N`
applied to the A-restriction of the canonical B-alternating map `baseChangeAlt`.
Mathlib supplies the exterior power only over a fixed base
(`ModuleCat.exteriorPower.functor`), so this variance in the base ring is project
infrastructure. -/
noncomputable def baseChange (n : ℕ)
    [Module A (⋀[B]^n N)] [IsScalarTower A B (⋀[B]^n N)] :
    (⋀[A]^n N) →ₗ[A] (⋀[B]^n N) :=
  exteriorPower.alternatingMapLinearEquiv (baseChangeAlt n)

/-- `ModuleCat.exteriorPower.baseChange` acts as the identity on representatives of
decomposable wedges. -/
@[simp] theorem baseChange_apply_ιMulti (n : ℕ)
    [Module A (⋀[B]^n N)] [IsScalarTower A B (⋀[B]^n N)] (v : Fin n → N) :
    baseChange n (exteriorPower.ιMulti A n v) = exteriorPower.ιMulti B n v := by
  rw [baseChange, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Project-local (`found:exterior_power_base_change`).

Base-change functoriality of exterior powers: for a ring homomorphism `φ : R → S`
of commutative rings and a `φ`-semilinear map `g : M →ₛₗ[φ] N` (`M` an `R`-module,
`N` an `S`-module), the induced `φ`-semilinear map `⋀^n g : ⋀[R]^n M → ⋀[S]^n N` on
exterior powers.  It is the categorical wrapper of the linear-algebra comparison
`baseChange` along restriction of scalars: `g` is composed (over `R`) with the
fixed-base functoriality `exteriorPower.map` and then with `baseChange n`, the
`R`-module structures on `N` and `⋀[S]^n N` being the restriction-of-scalars
structures assembled from `φ.toAlgebra`.  Mathlib supplies the exterior power only
over a fixed base, so this variance in the base ring is project infrastructure. -/
noncomputable def baseChangeMap {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (g : M →ₛₗ[φ] N) :
    (⋀[R]^n M) →ₛₗ[φ] (⋀[S]^n N) := by
  letI alg : Algebra R S := φ.toAlgebra
  letI modRN : Module R N := Module.compHom N φ
  haveI towerN : IsScalarTower R S N := ⟨fun r s n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  letI modRE : Module R (⋀[S]^n N) := Module.compHom _ φ
  haveI towerE : IsScalarTower R S (⋀[S]^n N) :=
    ⟨fun r s n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  letI gR : M →ₗ[R] N :=
    { toFun := g, map_add' := g.map_add, map_smul' := fun r m => map_smulₛₗ g r m }
  let comp : (⋀[R]^n M) →ₗ[R] (⋀[S]^n N) := (baseChange n).comp (_root_.exteriorPower.map n gR)
  exact { toFun := comp, map_add' := comp.map_add, map_smul' := fun r x => comp.map_smul r x }

/-- `ModuleCat.exteriorPower.baseChangeMap` sends a decomposable wedge
`v 0 ∧ ⋯ ∧ v (n-1)` to `g (v 0) ∧ ⋯ ∧ g (v (n-1))` formed over `S`: the defining
action on the spanning decomposable wedges. -/
@[simp] theorem baseChangeMap_apply_ιMulti {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (n : ℕ) {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (g : M →ₛₗ[φ] N) (v : Fin n → M) :
    baseChangeMap φ n g (exteriorPower.ιMulti R n v)
      = exteriorPower.ιMulti S n (fun i => g (v i)) := by
  letI alg : Algebra R S := φ.toAlgebra
  letI modRN : Module R N := Module.compHom N φ
  haveI towerN : IsScalarTower R S N := ⟨fun r s n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  letI modRE : Module R (⋀[S]^n N) := Module.compHom _ φ
  haveI towerE : IsScalarTower R S (⋀[S]^n N) :=
    ⟨fun r s n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  change baseChange n (_root_.exteriorPower.map n
      ({ toFun := g, map_add' := g.map_add, map_smul' := fun r m => map_smulₛₗ g r m } :
        M →ₗ[R] N) (exteriorPower.ιMulti R n v)) = _
  rw [_root_.exteriorPower.map_apply_ιMulti, baseChange_apply_ιMulti]
  rfl

/-- Project-local (`found:exterior_base_change_map_id`).

Base change along the identity ring map recovers the fixed-base exterior power:
for an `R`-linear map `g : M → N` (an `id_R`-semilinear map), the base-change map
`baseChangeMap (RingHom.id R) n g` coincides with the fixed-base functorial action
`exteriorPower.map n g`.  Both are `R`-linear maps `⋀[R]^n M → ⋀[R]^n N`; they
agree on the spanning decomposable wedges by `baseChangeMap_apply_ιMulti` and
`exteriorPower.map_apply_ιMulti`.  This is the identity-ring-map naturality of base
change feeding the openwise exterior-power presheaf assembly. -/
theorem baseChangeMap_id {R : Type u} [CommRing R] (n : ℕ) {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) :
    baseChangeMap (RingHom.id R) n g = _root_.exteriorPower.map n g := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R n M)
  rintro _ ⟨v, rfl⟩
  rw [baseChangeMap_apply_ιMulti, _root_.exteriorPower.map_apply_ιMulti]
  rfl

/-- Project-local (`found:exterior_base_change_map_comp`).

Base change respects composition of ring maps: for ring homomorphisms `φ : R → S`,
`ψ : S → T` and semilinear maps `g : M →ₛₗ[φ] N`, `h : N →ₛₗ[ψ] P`, the base-change
map of the composite `h ∘ₛₗ g` (which is `(ψ.comp φ)`-semilinear) along `ψ.comp φ`
factors as the composite of the base-change maps of `g` and `h`.  Both sides are
additive maps `⋀[R]^n M → ⋀[T]^n P` agreeing on decomposable wedges via
`baseChangeMap_apply_ιMulti`.  This is the composition naturality of base change
feeding the openwise exterior-power presheaf assembly. -/
theorem baseChangeMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T) [RingHomCompTriple φ ψ χ] (n : ℕ) {M N P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [AddCommGroup P] [Module T P]
    (g : M →ₛₗ[φ] N) (h : N →ₛₗ[ψ] P) :
    baseChangeMap χ n (h.comp g) = (baseChangeMap ψ n h).comp (baseChangeMap φ n g) := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R n M)
  rintro _ ⟨v, rfl⟩
  rw [baseChangeMap_apply_ιMulti]
  rw [LinearMap.comp_apply, baseChangeMap_apply_ιMulti, baseChangeMap_apply_ιMulti]
  rfl

/-- Project-local categorical wrapper of `baseChangeMap`.

For a ring homomorphism `φ : R → S` and a morphism `g : M ⟶ (restrictScalars φ).obj N`
(equivalently a `φ`-semilinear map `M → N`), the induced morphism on exterior powers
`M.exteriorPower n ⟶ (restrictScalars φ).obj (N.exteriorPower n)`.  This is the
`ModuleCat`-morphism repackaging of `baseChangeMap` via `semilinearMapAddEquiv`, the
form consumed by the openwise exterior-power presheaf assembly. -/
noncomputable def baseChangeMapCat {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    M.exteriorPower n ⟶ (ModuleCat.restrictScalars φ).obj (N.exteriorPower n) :=
  (ModuleCat.semilinearMapAddEquiv φ (M.exteriorPower n) (N.exteriorPower n))
    (baseChangeMap φ n ((ModuleCat.semilinearMapAddEquiv φ M N).symm g))

/-- Generator action of `baseChangeMapCat`: on a decomposable wedge `v 0 ∧ ⋯` it produces
the wedge of the `g`-images formed over `S`. -/
@[simp] theorem baseChangeMapCat_hom_ιMulti {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (n : ℕ) {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars φ).obj N) (v : Fin n → M) :
    (baseChangeMapCat φ n g).hom (exteriorPower.ιMulti R n v)
      = exteriorPower.ιMulti S n (fun i => g.hom (v i)) := by
  change baseChangeMap φ n ((ModuleCat.semilinearMapAddEquiv φ M N).symm g)
      (exteriorPower.ιMulti R n v) = _
  rw [baseChangeMap_apply_ιMulti]
  rfl

end ModuleCat.exteriorPower

/-! ## Project-local Mathlib supplement — base change of symmetric powers (semilinear) -/

namespace ModuleCat.symmetricPower

/-- Project-local (`found:sym_power_base_change`).

Base-change functoriality of symmetric powers: for a ring homomorphism `φ : R → S`
of commutative rings and a `φ`-semilinear map `g : M →ₛₗ[φ] N` (`M` an `R`-module,
`N` an `S`-module), the induced `φ`-semilinear map
`Sym^i g : Sym[R] ι M → Sym[S] ι N` on symmetric powers.  It is the categorical
wrapper of the linear-algebra comparison `SymmetricPower.baseChange` along
restriction of scalars: `g` is composed (over `R`) with the fixed-base
functoriality `SymmetricPower.map` and then with `SymmetricPower.baseChange`, the
`R`-module structures on `N` and `Sym[S] ι N` being the restriction-of-scalars
structures assembled from `φ.toAlgebra`.  This is the symmetric twin of
`ModuleCat.exteriorPower.baseChangeMap`; Mathlib supplies no variance of the
symmetric power in the base ring. -/
noncomputable def baseChangeMap {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {ι : Type u} {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (g : M →ₛₗ[φ] N) :
    Sym[R] ι M →ₛₗ[φ] Sym[S] ι N := by
  letI alg : Algebra R S := φ.toAlgebra
  letI modRN : Module R N := Module.compHom N φ
  haveI towerN : IsScalarTower R S N := ⟨fun r s n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  letI modRE : Module R (Sym[S] ι N) := Module.compHom _ φ
  haveI towerE : IsScalarTower R S (Sym[S] ι N) :=
    ⟨fun r s n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  letI gR : M →ₗ[R] N :=
    { toFun := g, map_add' := g.map_add, map_smul' := fun r m => map_smulₛₗ g r m }
  let comp : Sym[R] ι M →ₗ[R] Sym[S] ι N :=
    (_root_.SymmetricPower.baseChange).comp (_root_.SymmetricPower.map gR)
  exact { toFun := comp, map_add' := comp.map_add, map_smul' := fun r x => comp.map_smul r x }

/-- `ModuleCat.symmetricPower.baseChangeMap` sends a decomposable symmetric tensor
`m 0 ⋯ m (n-1)` to `g (m 0) ⋯ g (m (n-1))` formed over `S`: the defining action on
the spanning decomposable symmetric tensors. -/
@[simp] theorem baseChangeMap_tprod {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {ι : Type u} {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (g : M →ₛₗ[φ] N) (m : ι → M) :
    baseChangeMap φ (ι := ι) g (⨂ₛ[R] i, m i) = ⨂ₛ[S] i, g (m i) := by
  letI alg : Algebra R S := φ.toAlgebra
  letI modRN : Module R N := Module.compHom N φ
  haveI towerN : IsScalarTower R S N := ⟨fun r s n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  letI modRE : Module R (Sym[S] ι N) := Module.compHom _ φ
  haveI towerE : IsScalarTower R S (Sym[S] ι N) :=
    ⟨fun r s n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  change _root_.SymmetricPower.baseChange (A := R) (B := S) (ι := ι) (N := N)
      (_root_.SymmetricPower.map
        ({ toFun := g, map_add' := g.map_add, map_smul' := fun r x => map_smulₛₗ g r x } :
          M →ₗ[R] N) (⨂ₛ[R] i, m i)) = _
  rw [_root_.SymmetricPower.map_tprod, _root_.SymmetricPower.baseChange_tprod]
  rfl

/-- Project-local (`found:sym_base_change_map_id`).

Base change along the identity ring map recovers the fixed-base symmetric power:
for an `R`-linear map `g : M → N`, the base-change map `baseChangeMap (RingHom.id R) g`
coincides with the fixed-base functorial action `SymmetricPower.map g`.  They agree on
the spanning decomposable symmetric tensors via `baseChangeMap_tprod` and
`SymmetricPower.map_tprod`.  This is the identity-ring-map naturality of symmetric base
change feeding the openwise symmetric-power presheaf assembly. -/
theorem baseChangeMap_id {R : Type u} [CommRing R] {ι M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) :
    baseChangeMap (RingHom.id R) (ι := ι) g = _root_.SymmetricPower.map g := by
  apply LinearMap.ext_on (_root_.SymmetricPower.span_tprod_eq_top R ι M)
  rintro _ ⟨m, rfl⟩
  rw [baseChangeMap_tprod, _root_.SymmetricPower.map_tprod]

/-- Project-local (`found:sym_base_change_map_comp`).

Base change respects composition of ring maps: for ring homomorphisms `φ : R → S`,
`ψ : S → T` (composing to `χ`) and semilinear maps `g : M →ₛₗ[φ] N`, `h : N →ₛₗ[ψ] P`,
the base-change map of the composite `h ∘ₛₗ g` along `χ` factors as the composite of the
base-change maps of `g` and `h`.  Both sides agree on the spanning decomposable symmetric
tensors via `baseChangeMap_tprod`.  This is the composition naturality of symmetric base
change feeding the openwise symmetric-power presheaf assembly. -/
theorem baseChangeMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T) [RingHomCompTriple φ ψ χ] {ι M N P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [AddCommGroup P] [Module T P]
    (g : M →ₛₗ[φ] N) (h : N →ₛₗ[ψ] P) :
    baseChangeMap χ (ι := ι) (h.comp g) = (baseChangeMap ψ h).comp (baseChangeMap φ g) := by
  apply LinearMap.ext_on (_root_.SymmetricPower.span_tprod_eq_top R ι M)
  rintro _ ⟨m, rfl⟩
  rw [baseChangeMap_tprod, LinearMap.comp_apply, baseChangeMap_tprod, baseChangeMap_tprod]
  rfl

/-- Project-local categorical wrapper of the symmetric `baseChangeMap`.

For a ring homomorphism `φ : R → S` and a morphism `g : M ⟶ (restrictScalars φ).obj N`
(equivalently a `φ`-semilinear map `M → N`), the induced morphism on symmetric powers
`M.symmetricPower n ⟶ (restrictScalars φ).obj (N.symmetricPower n)`.  This is the
`ModuleCat`-morphism repackaging of the symmetric `baseChangeMap` via `semilinearMapAddEquiv`,
the form consumed by the openwise symmetric-power presheaf assembly. -/
noncomputable def baseChangeMapCat {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    M.symmetricPower n ⟶ (ModuleCat.restrictScalars φ).obj (N.symmetricPower n) :=
  (ModuleCat.semilinearMapAddEquiv φ (M.symmetricPower n) (N.symmetricPower n))
    (baseChangeMap φ (ι := ULift.{u} (Fin n)) ((ModuleCat.semilinearMapAddEquiv φ M N).symm g))

/-- Generator action of the symmetric `baseChangeMapCat`: on a decomposable symmetric tensor
`m 0 ⋯` it produces the symmetric tensor of the `g`-images formed over `S`. -/
@[simp] theorem baseChangeMapCat_hom_tprod {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (n : ℕ) {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars φ).obj N) (m : ULift.{u} (Fin n) → M) :
    (baseChangeMapCat φ n g).hom (⨂ₛ[R] i, m i)
      = ⨂ₛ[S] i, g.hom (m i) := by
  change baseChangeMap φ (ι := ULift.{u} (Fin n)) ((ModuleCat.semilinearMapAddEquiv φ M N).symm g)
      (⨂ₛ[R] i, m i) = _
  rw [baseChangeMap_tprod]
  rfl

end ModuleCat.symmetricPower

/-! ## Project-local Mathlib supplement — openwise exterior power of a presheaf of modules -/

namespace AlgebraicGeometry.PresheafOfModules

/-- The openwise transition map for the exterior-power presheaf: the categorical
base-change map on exterior powers induced by the (semilinear) restriction map of `F`. -/
private noncomputable def extPowMap {X : Scheme.{u}} (n : ℕ)
    (F : PresheafOfModules (X.ringCatSheaf.presheaf)) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    letI := X.ringCatSheaf_commRing U
    letI := X.ringCatSheaf_commRing V
    (F.obj U).exteriorPower n ⟶
      (ModuleCat.restrictScalars ((X.ringCatSheaf.presheaf.map f).hom)).obj
        ((F.obj V).exteriorPower n) :=
  letI := X.ringCatSheaf_commRing U
  letI := X.ringCatSheaf_commRing V
  ModuleCat.exteriorPower.baseChangeMapCat ((X.ringCatSheaf.presheaf.map f).hom) n (F.map f)

set_option maxHeartbeats 2000000 in
-- `rw [F.map_id]` forces a `whnf` of the scheme structure-sheaf functor on the identity
-- morphism, which is expensive; the bumped limit accommodates that single rewrite.
private theorem extPowMap_id {X : Scheme.{u}} (n : ℕ)
    (F : PresheafOfModules (X.ringCatSheaf.presheaf)) (U : (Opens X)ᵒᵖ) :
    letI := X.ringCatSheaf_commRing U
    extPowMap n F (𝟙 U) = (ModuleCat.restrictScalarsId'
        ((X.ringCatSheaf.presheaf.map (𝟙 U)).hom)
        (by rw [CategoryTheory.Functor.map_id, RingCat.hom_id])).inv.app
      ((F.obj U).exteriorPower n) := by
  letI := X.ringCatSheaf_commRing U
  rw [extPowMap]
  apply ModuleCat.hom_ext
  refine LinearMap.ext_on (exteriorPower.ιMulti_span _ n (F.obj U)) ?_
  rintro _ ⟨v, rfl⟩
  rw [ModuleCat.exteriorPower.baseChangeMapCat_hom_ιMulti,
    ModuleCat.restrictScalarsId'_inv_app, ModuleCat.restrictScalarsId'App_inv_apply]
  rw [F.map_id]
  simp only [ModuleCat.restrictScalarsId'_inv_app, ModuleCat.restrictScalarsId'App_inv_apply]
  rfl

set_option maxHeartbeats 4000000 in
-- The proof reduces both sides on decomposable wedges; `rw [F.map_comp]` and the
-- `restrictScalarsComp'` element actions each force an expensive `whnf` of the scheme
-- structure-sheaf functor, so the heartbeat limit is raised to accommodate them.
private theorem extPowMap_comp {X : Scheme.{u}} (n : ℕ)
    (F : PresheafOfModules (X.ringCatSheaf.presheaf)) {U V W : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    letI := X.ringCatSheaf_commRing U
    letI := X.ringCatSheaf_commRing V
    letI := X.ringCatSheaf_commRing W
    extPowMap n F (f ≫ g) = extPowMap n F f ≫
      (ModuleCat.restrictScalars ((X.ringCatSheaf.presheaf.map f).hom)).map (extPowMap n F g) ≫
      (ModuleCat.restrictScalarsComp' ((X.ringCatSheaf.presheaf.map f).hom)
        ((X.ringCatSheaf.presheaf.map g).hom) ((X.ringCatSheaf.presheaf.map (f ≫ g)).hom)
        (by rw [CategoryTheory.Functor.map_comp, RingCat.hom_comp])).inv.app
          ((F.obj W).exteriorPower n) := by
  letI := X.ringCatSheaf_commRing U
  letI := X.ringCatSheaf_commRing V
  letI := X.ringCatSheaf_commRing W
  rw [extPowMap, extPowMap, extPowMap, F.map_comp]
  apply ModuleCat.hom_ext
  refine LinearMap.ext_on (exteriorPower.ιMulti_span _ n (F.obj U)) ?_
  rintro _ ⟨v, rfl⟩
  simp only [ModuleCat.exteriorPower.baseChangeMapCat_hom_ιMulti, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.restrictScalars.map_apply,
    ModuleCat.restrictScalarsComp'_inv_app, ModuleCat.restrictScalarsComp'App_inv_apply]
  erw [ModuleCat.exteriorPower.baseChangeMapCat_hom_ιMulti]
  rfl

/-- Project-local (`found:presheafmod_exterior_power`).

The `n`-th exterior power of a presheaf of modules over the structure ring sheaf of a
scheme `X`: openwise the `ModuleCat`-level exterior power `(F.obj U).exteriorPower n`, with
transition maps the semilinear base-change maps `ModuleCat.exteriorPower.baseChangeMapCat`
of the (semilinear) restriction maps of `F`.  The per-open `CommRing` structure on the
`RingCat`-valued sections is supplied by `Scheme.ringCatSheaf_commRing`; the presheaf
identity and composition coherence laws are `extPowMap_id` and `extPowMap_comp`, which are
the openwise incarnations of the identity-ring-map and composition naturality of base
change.  Mathlib provides the exterior power only over a fixed commutative base, so this
openwise variance is project infrastructure. -/
noncomputable def exteriorPower {X : Scheme.{u}} (n : ℕ)
    (F : PresheafOfModules (X.ringCatSheaf.presheaf)) :
    PresheafOfModules (X.ringCatSheaf.presheaf) :=
  PresheafOfModules.mk
    (fun U => letI := X.ringCatSheaf_commRing U; (F.obj U).exteriorPower n)
    (fun {_ _} f => extPowMap n F f)
    (fun U => extPowMap_id n F U)
    (fun {_ _ _} f g => extPowMap_comp n F f g)

/-! ## Project-local Mathlib supplement — openwise symmetric power of a presheaf of modules -/

/-- The openwise transition map for the symmetric-power presheaf: the categorical
base-change map on symmetric powers induced by the (semilinear) restriction map of `F`. -/
private noncomputable def symPowMap {X : Scheme.{u}} (n : ℕ)
    (F : PresheafOfModules (X.ringCatSheaf.presheaf)) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    letI := X.ringCatSheaf_commRing U
    letI := X.ringCatSheaf_commRing V
    (F.obj U).symmetricPower n ⟶
      (ModuleCat.restrictScalars ((X.ringCatSheaf.presheaf.map f).hom)).obj
        ((F.obj V).symmetricPower n) :=
  letI := X.ringCatSheaf_commRing U
  letI := X.ringCatSheaf_commRing V
  ModuleCat.symmetricPower.baseChangeMapCat ((X.ringCatSheaf.presheaf.map f).hom) n (F.map f)

set_option maxHeartbeats 2000000 in
-- `rw [F.map_id]` forces a `whnf` of the scheme structure-sheaf functor on the identity
-- morphism, which is expensive; the bumped limit accommodates that single rewrite.
private theorem symPowMap_id {X : Scheme.{u}} (n : ℕ)
    (F : PresheafOfModules (X.ringCatSheaf.presheaf)) (U : (Opens X)ᵒᵖ) :
    letI := X.ringCatSheaf_commRing U
    symPowMap n F (𝟙 U) = (ModuleCat.restrictScalarsId'
        ((X.ringCatSheaf.presheaf.map (𝟙 U)).hom)
        (by rw [CategoryTheory.Functor.map_id, RingCat.hom_id])).inv.app
      ((F.obj U).symmetricPower n) := by
  letI := X.ringCatSheaf_commRing U
  rw [symPowMap]
  apply ModuleCat.hom_ext
  refine LinearMap.ext_on (SymmetricPower.span_tprod_eq_top _ (ULift.{u} (Fin n)) (F.obj U)) ?_
  rintro _ ⟨m, rfl⟩
  rw [ModuleCat.symmetricPower.baseChangeMapCat_hom_tprod,
    ModuleCat.restrictScalarsId'_inv_app, ModuleCat.restrictScalarsId'App_inv_apply]
  rw [F.map_id]
  simp only [ModuleCat.restrictScalarsId'_inv_app, ModuleCat.restrictScalarsId'App_inv_apply]
  rfl

set_option maxHeartbeats 4000000 in
-- The proof reduces both sides on decomposable symmetric tensors; `rw [F.map_comp]` and the
-- `restrictScalarsComp'` element actions each force an expensive `whnf` of the scheme
-- structure-sheaf functor, so the heartbeat limit is raised to accommodate them.
private theorem symPowMap_comp {X : Scheme.{u}} (n : ℕ)
    (F : PresheafOfModules (X.ringCatSheaf.presheaf)) {U V W : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    letI := X.ringCatSheaf_commRing U
    letI := X.ringCatSheaf_commRing V
    letI := X.ringCatSheaf_commRing W
    symPowMap n F (f ≫ g) = symPowMap n F f ≫
      (ModuleCat.restrictScalars ((X.ringCatSheaf.presheaf.map f).hom)).map (symPowMap n F g) ≫
      (ModuleCat.restrictScalarsComp' ((X.ringCatSheaf.presheaf.map f).hom)
        ((X.ringCatSheaf.presheaf.map g).hom) ((X.ringCatSheaf.presheaf.map (f ≫ g)).hom)
        (by rw [CategoryTheory.Functor.map_comp, RingCat.hom_comp])).inv.app
          ((F.obj W).symmetricPower n) := by
  letI := X.ringCatSheaf_commRing U
  letI := X.ringCatSheaf_commRing V
  letI := X.ringCatSheaf_commRing W
  rw [symPowMap, symPowMap, symPowMap, F.map_comp]
  apply ModuleCat.hom_ext
  refine LinearMap.ext_on (SymmetricPower.span_tprod_eq_top _ (ULift.{u} (Fin n)) (F.obj U)) ?_
  rintro _ ⟨m, rfl⟩
  simp only [ModuleCat.symmetricPower.baseChangeMapCat_hom_tprod, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.restrictScalars.map_apply,
    ModuleCat.restrictScalarsComp'_inv_app, ModuleCat.restrictScalarsComp'App_inv_apply]
  erw [ModuleCat.symmetricPower.baseChangeMapCat_hom_tprod]
  rfl

/-- Project-local (`found:presheafmod_sym_power`).

The `n`-th symmetric power of a presheaf of modules over the structure ring sheaf of a
scheme `X`: openwise the `ModuleCat`-level symmetric power `(F.obj U).symmetricPower n`, with
transition maps the semilinear base-change maps `ModuleCat.symmetricPower.baseChangeMapCat`
of the (semilinear) restriction maps of `F`.  The per-open `CommRing` structure on the
`RingCat`-valued sections is supplied by `Scheme.ringCatSheaf_commRing`; the presheaf
identity and composition coherence laws are `symPowMap_id` and `symPowMap_comp`, the openwise
incarnations of the identity-ring-map and composition naturality of symmetric base change.
This is the symmetric twin of `PresheafOfModules.exteriorPower`. -/
noncomputable def symPower {X : Scheme.{u}} (n : ℕ)
    (F : PresheafOfModules (X.ringCatSheaf.presheaf)) :
    PresheafOfModules (X.ringCatSheaf.presheaf) :=
  PresheafOfModules.mk
    (fun U => letI := X.ringCatSheaf_commRing U; (F.obj U).symmetricPower n)
    (fun {_ _} f => symPowMap n F f)
    (fun U => symPowMap_id n F U)
    (fun {_ _ _} f g => symPowMap_comp n F f g)

end AlgebraicGeometry.PresheafOfModules

/-! ## Project-local Mathlib supplement — exterior/symmetric powers of an `𝒪_X`-module -/

namespace AlgebraicGeometry.Scheme.Modules

/-- Project-local (`found:oxmod_exterior_power`).

The `n`-th exterior power of an `𝒪_X`-module `F : X.Modules`: forget `F` to its underlying
presheaf of modules, apply the openwise presheaf exterior power
`PresheafOfModules.exteriorPower n`, and sheafify back to an `𝒪_X`-module via
`PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)`.  Kemeny's bundles `⋀^{k+1} M_L`,
`⋀^k π^*𝓜` and `⋀^k Γ` are instances of this construction. -/
noncomputable def exteriorPower {X : Scheme.{u}} (n : ℕ) (F : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.exteriorPower n ((SheafOfModules.forget X.ringCatSheaf).obj F))

/-- Project-local (`found:oxmod_sym_power`).

The `n`-th symmetric power of an `𝒪_X`-module `F : X.Modules`: forget `F` to its underlying
presheaf of modules, apply the openwise presheaf symmetric power
`PresheafOfModules.symPower n`, and sheafify back to an `𝒪_X`-module via
`PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)`.  This is the symmetric twin of
`Scheme.Modules.exteriorPower`. -/
noncomputable def symPower {X : Scheme.{u}} (n : ℕ) (F : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.symPower n ((SheafOfModules.forget X.ringCatSheaf).obj F))

/-! ## Project-local Mathlib supplement — evaluation map and kernel bundle

This block isolates the general foundational substrate behind Kemeny's kernel
bundle `M_L`: for an arbitrary scheme `X` and an arbitrary `𝒪_X`-module `F`, the
trivial bundle on the (global) sections, the evaluation morphism onto `F`, and
its kernel.  Specialising `X` to a K3 surface and `F` to a line bundle `L`
recovers Kemeny's defining sequence `0 → M_L → H⁰(L) ⊗ 𝒪_X → L → 0`. -/

/-- Project-local (`found:trivial_bundle`).

The trivial `𝒪_X`-module on an index type `I`: the free `𝒪_X`-module `𝒪_X^{(I)}`,
i.e. `SheafOfModules.free I` over the structure ring sheaf `X.ringCatSheaf`.  This
is the project-side name for the constant bundle `V ⊗_k 𝒪_X` of Kemeny's
construction, with `I` an index set of a basis of `V`; for the evaluation morphism
below `I` is taken to be the section type `F.sections` directly, sidestepping any
basis/`choose` dependency.  For finite `I` it is locally free of constant rank
`|I|` (cf. `Scheme.Modules.IsLocallyFree`). -/
noncomputable def trivialBundle {X : Scheme.{u}} (I : Type u) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) I

/-- Project-local (`found:eval_morphism`).

The evaluation morphism `ev_F : H⁰(X,F) ⊗_k 𝒪_X → F` out of the trivial bundle on
the sections of `F`.  It is the counit of the free `⊣` global-sections adjunction:
under the free hom-bijection `SheafOfModules.freeHomEquiv` — `Hom(𝒪_X^{(I)}, F) ≃
(I → F.sections)` — taken with index type `I := F.sections`, the evaluation map is
the morphism corresponding to the *identity* family of sections.  This is the
`𝒪_X`-linear extension of `1 ↦ s` on each section `s ∈ H⁰(X,F)`.  Routing through
`F.sections` (what `freeHomEquiv` consumes) rather than the derived/Ab-sheaf `Γ`
keeps the construction `choose`-free. -/
noncomputable def evalMap {X : Scheme.{u}} (F : X.Modules) :
    trivialBundle (X := X) F.sections ⟶ F :=
  (SheafOfModules.freeHomEquiv F (I := F.sections)).symm id

/-- Project-local (`found:eval_kernel_bundle`).

The evaluation kernel bundle `M_F := ker(ev_F)`, the categorical kernel
(`Limits.kernel`) of the evaluation morphism `evalMap` taken in the abelian
category `X.Modules` (Grothendieck abelian via the heavy bridge in this file,
hence with all kernels).  It sits in the left-exact sequence
`0 → M_F → H⁰(X,F) ⊗_k 𝒪_X → F`.  Specialising `X` to a K3 surface and `F` to a
line bundle `L` gives Kemeny's kernel bundle `M_L`. -/
noncomputable def evalKernel {X : Scheme.{u}} (F : X.Modules) : X.Modules :=
  Limits.kernel (evalMap F)

/-! ## Project-local Mathlib supplement — local freeness of the trivial bundle

This block establishes that the trivial bundle `trivialBundle I = 𝒪_X^{(I)}` is
locally free of constant rank `|I|` for finite `I` — the first of the two
reusable infrastructure cores behind the local freeness of Kemeny's kernel
bundle `M_L` (blueprint `found:trivial_bundle_locally_free`).

The key step is that restriction of a free module along an open immersion is
again free.  The earlier-attempted route through
`SheafOfModules.mapFreeIso`/coproduct-preservation of `restrictFunctor` is
sidestepped: `restrictFunctor f` is isomorphic to the inverse-image functor
`Scheme.Modules.pullback f = SheafOfModules.pullback f.toRingCatSheafHom`
(`restrictFunctorIsoPullback`), whose underlying functor on the sites of opens is
`Opens.map f.base`.  For an open immersion this is the *right* adjoint of the
image functor `f.opensFunctor` (the image ⊣ preimage adjunction
`f.isOpenEmbedding.isOpenMap.adjunction`), hence *final*
(`Functor.final_of_adjunction`).  Finality is exactly the hypothesis under which
Mathlib's `SheafOfModules.pullbackObjFreeIso` shows the pullback of a free sheaf
of modules is free, so the restriction-of-free iso drops out by composition. -/

/-- Project-local helper (supports `found:trivial_bundle_locally_free`).

Restriction of a free `𝒪_Y`-module along an open immersion `f : X ⟶ Y` is the
free `𝒪_X`-module on the same index type:
`(restrictFunctor f).obj (free I) ≅ free I`.  Obtained from
`SheafOfModules.pullbackObjFreeIso` via `restrictFunctorIsoPullback`, using that
`Opens.map f.base` is final for an open immersion (it is the right adjoint of the
image functor). -/
noncomputable def restrictFunctorObjFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Type u) :
    (restrictFunctor f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  letI : (TopologicalSpace.Opens.map f.base).Final :=
    Functor.final_of_adjunction f.isOpenEmbedding.isOpenMap.adjunction
  (restrictFunctorIsoPullback f).app _ ≪≫
    SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

/-- Project-local helper: local freeness is invariant under isomorphism of
`𝒪_X`-modules.  Transport each local trivialisation of `F` across the restriction
of the iso `e : F ≅ G`.  Used to move local freeness along the various canonical
isomorphisms in the kernel-bundle chain. -/
theorem isLocallyFree_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (hF : F.IsLocallyFree) : G.IsLocallyFree := by
  obtain ⟨I, hI, hcov⟩ := hF
  refine ⟨I, hI, fun x => ?_⟩
  obtain ⟨U, hxU, ⟨iso⟩⟩ := hcov x
  exact ⟨U, hxU, ⟨((restrictFunctor U.ι).mapIso e).symm ≪≫ iso⟩⟩

/-- Project-local (`found:trivial_bundle_locally_free`).

For a scheme `X` and a finite index type `I`, the trivial bundle
`trivialBundle I = 𝒪_X^{(I)}` is locally free of constant rank `|I|`.  The free
module is already globally free, so the single trivialising cover by `U = ⊤`
suffices: `restrictFunctorObjFreeIso` identifies its restriction to `⊤` with the
free `𝒪_⊤`-module on `I`.  In particular, for a finite-dimensional `k`-vector
space `V` of dimension `r` the trivial bundle `V ⊗_k 𝒪_X` is locally free of
rank `r`. -/
theorem trivialBundle_isLocallyFree {X : Scheme.{u}} (I : Type u) [Finite I] :
    (trivialBundle (X := X) I).IsLocallyFree := by
  refine ⟨I, inferInstance, fun x => ⟨⊤, trivial, ⟨?_⟩⟩⟩
  exact restrictFunctorObjFreeIso (⊤ : X.Opens).ι I

/-! ## Project-local Mathlib supplement — the evaluation short exact sequence

This block records the evaluation short complex
`0 → M_F → H⁰(X,F) ⊗ 𝒪_X → F → 0` and shows it is short exact precisely when the
evaluation morphism is an epimorphism (blueprint
`found:eval_shortexact_of_globally_generated`).

MODELLING DECISION (no "globally generated" predicate on `X.Modules`): rather
than introduce a stalk-generation predicate, we take *`evalMap F` is an
epimorphism* as the working hypothesis standing for "`F` is globally generated".
With that hypothesis the short-exactness is purely formal: `M_F = ker(ev_F)` by
construction (`evalKernel`), so the kernel inclusion is a monomorphism and the
kernel sequence is exact (`ShortComplex.exact_kernel`); the only extra input is
the epi on the right, which is exactly the hypothesis.  The epi half is therefore
definitional under this model, and only the abelian-category assembly remains. -/

/-- Project-local helper (supports `found:eval_shortexact_of_globally_generated`).

The evaluation short complex `M_F → H⁰(X,F) ⊗ 𝒪_X → F`, with the kernel inclusion
`kernel.ι (evalMap F)` followed by the evaluation morphism `evalMap F`.  Its `X₁`
is definitionally `evalKernel F` and its `X₃` is `F`. -/
noncomputable def evalShortComplex {X : Scheme.{u}} (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (Limits.kernel.ι (evalMap F)) (evalMap F) (Limits.kernel.condition _)

/-- Project-local (`found:eval_shortexact_of_globally_generated`).

If the evaluation morphism `evalMap F` is an epimorphism — the working model of
"`F` is globally generated" (see the section note) — then the evaluation
sequence `0 → M_F → H⁰(X,F) ⊗ 𝒪_X → F → 0` is short exact: the kernel inclusion
is mono, the kernel sequence is exact (`ShortComplex.exact_kernel`), and the
evaluation morphism is epi by hypothesis. -/
theorem evalShortComplex_shortExact_of_globallyGenerated {X : Scheme.{u}} (F : X.Modules)
    (hF : Epi (evalMap F)) : (evalShortComplex F).ShortExact where
  exact := ShortComplex.exact_kernel (evalMap F)
  mono_f := by dsimp only [evalShortComplex, ShortComplex.mk]; infer_instance
  epi_g := hF

/-! ## Project-local Mathlib supplement — kernel of a finite free presentation

L2 of the Core-2 affine-reduction chain (`lem:module_kernel_free_basicOpen_cover`).
Pure commutative algebra: a short exact sequence `0 → K → R^m → R^n → 0` of
`R`-modules with finite free middle and free right term forces the kernel `K` to be
finitely presented and projective, hence locally free on a basic-open cover of
`Spec R`. -/

/-- Project-local (`lem:module_kernel_free_basicOpen_cover`), L2 of the Core-2
affine-reduction chain.

Let `S : 0 → K → R^m → R^n → 0` be a short exact sequence of `R`-modules (`R` a
commutative ring) with `S.X₂` finite free and `S.X₃` free.  Then the kernel `S.X₁`
is finitely presented and projective (the sequence splits since `S.X₃` is
projective, exhibiting `S.X₁` as a finite projective summand of `S.X₂`), so its
free locus is all of `Spec R`; refining the open free locus to basic opens and
extracting a finite subcover by quasi-compactness of `Spec R` produces a finite
family `t ⊆ R` whose basic opens cover `Spec R` and on each of which the localized
kernel `S.X₁` is free of finite rank. -/
theorem kernel_module_free_on_basicOpen_cover {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Free R S.X₂] [Module.Finite R S.X₂] [Module.Free R S.X₃] :
    ∃ (t : Finset R),
      (∀ p : PrimeSpectrum R, ∃ f ∈ t, p ∈ PrimeSpectrum.basicOpen f) ∧
      ∀ f ∈ t, Module.Free (Localization.Away f) (LocalizedModule.Away f S.X₁) := by
  classical
  -- The sequence splits because `S.X₃` is (categorically) projective.
  have sp : S.Splitting := hS.splittingOfProjective
  -- The retraction `sp.r : S.X₂ ⟶ S.X₁` realizes `S.X₁` as a projective summand.
  have hsplit : sp.r.hom ∘ₗ S.f.hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp, sp.f_r, ModuleCat.hom_id]
  have hproj : Module.Projective R S.X₁ :=
    Module.Projective.of_split S.f.hom sp.r.hom hsplit
  have hsurj : Function.Surjective sp.r.hom :=
    Function.RightInverse.surjective (g := S.f.hom) (fun x => by
      have := LinearMap.congr_fun hsplit x; simpa using this)
  have hfin : Module.Finite R S.X₁ := Module.Finite.of_surjective sp.r.hom hsurj
  have hfp : Module.FinitePresentation R S.X₁ := Module.finitePresentation_of_projective R S.X₁
  -- Projectivity makes the free locus all of `Spec R`.
  have hloc : Module.freeLocus R S.X₁ = Set.univ := Module.freeLocus_eq_univ_iff.mpr hproj
  -- Pointwise: every prime sits in a basic open with free localized kernel.
  have hpt : ∀ p : PrimeSpectrum R, ∃ f : R, p ∈ PrimeSpectrum.basicOpen f ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away f S.X₁) := by
    intro p
    have hp : p ∈ Module.freeLocus R S.X₁ := by rw [hloc]; trivial
    have : Module.Free _ _ := (Module.mem_freeLocus).mp hp
    obtain ⟨r, hr, hr', _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl S.X₁)
      (Localization.AtPrime p.asIdeal)
    exact ⟨r, by simpa [PrimeSpectrum.mem_basicOpen] using hr, hr'⟩
  -- Choose such an `f` for each prime, then extract a finite subcover.
  choose g hg hgfree using hpt
  obtain ⟨tp, htp⟩ := isCompact_univ.elim_finite_subcover
    (fun p : PrimeSpectrum R => (PrimeSpectrum.basicOpen (g p) : Set (PrimeSpectrum R)))
    (fun p => (PrimeSpectrum.basicOpen (g p)).isOpen)
    (fun q _ => Set.mem_iUnion.mpr ⟨q, hg q⟩)
  refine ⟨tp.image g, ?_, ?_⟩
  · intro p
    have hpmem : p ∈ ⋃ q ∈ tp, (PrimeSpectrum.basicOpen (g q) : Set (PrimeSpectrum R)) :=
      htp (Set.mem_univ p)
    obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp hpmem
    exact ⟨g q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, hpq⟩
  · intro f hf
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hf
    exact hgfree q

/-! ## Project-local Mathlib supplement — local freeness is local on the base

L1 of the Core-2 affine-reduction chain (`lem:isLocallyFree_local`).  The crux is
the restrict–restrict bookkeeping: a trivialisation of `𝒦` over an open `V` of a
cover member `Uᵢ` transports to a trivialisation over the image open
`Uᵢ.ι ''ᵁ V` of `X`, via the scheme isomorphism `Scheme.Hom.isoImage`. -/

/-- Project-local helper (supports `lem:isLocallyFree_local`).

Transport a free trivialisation across a scheme isomorphism `e : S ≅ T`: if the
restriction of `A : T.Modules` along `e.hom` is free on `I`, then `A` itself is
free on `I`.  Inverts `restrictFunctor e.hom` using its pseudo-functorial inverse
`restrictFunctor e.inv` (`restrictFunctorComp`/`restrictFunctorId`) and the
restriction-of-free iso `restrictFunctorObjFreeIso` for the open immersion
`e.inv`. -/
noncomputable def freeIso_of_restrictFunctor_hom_freeIso {S T : Scheme.{u}} (e : S ≅ T)
    (A : T.Modules) (I : Type u)
    (hB : (restrictFunctor e.hom).obj A ≅ SheafOfModules.free (R := S.ringCatSheaf) I) :
    A ≅ SheafOfModules.free (R := T.ringCatSheaf) I :=
  letI NI : restrictFunctor e.hom ⋙ restrictFunctor e.inv ≅ 𝟭 T.Modules :=
    (restrictFunctorComp e.inv e.hom).symm ≪≫
      restrictFunctorCongr e.inv_hom_id ≪≫ restrictFunctorId
  (NI.app A).symm ≪≫ (restrictFunctor e.inv).mapIso hB ≪≫
    restrictFunctorObjFreeIso e.inv I

/-- Project-local (`lem:isLocallyFree_local`), L1 of the Core-2 affine-reduction
chain.

Local freeness is local on the base.  If `X` is covered by opens `{Uᵢ}` and on
each `Uᵢ` the restriction `𝒦|_{Uᵢ}` is locally free of the fixed finite rank `I`
(here phrased as the existence, for each point of `Uᵢ`, of a trivialising open `V`
of `Uᵢ`), then `𝒦` is locally free of rank `I` on `X`.  Each trivialising `V ⊆ Uᵢ`
maps isomorphically onto the image open `Uᵢ.ι ''ᵁ V ⊆ X` (`Scheme.Hom.isoImage`),
along which the trivialisation transports
(`freeIso_of_restrictFunctor_hom_freeIso`). -/
theorem isLocallyFree_of_isLocallyFree_cover {X : Scheme.{u}} (𝒦 : X.Modules)
    {ι : Type*} (U : ι → X.Opens) (hcov : (⨆ i, U i) = ⊤)
    (I : Type u) [Finite I]
    (hfree : ∀ i, ∀ y : (U i).toScheme,
      ∃ (V : (U i).toScheme.Opens) (_ : y ∈ V),
        Nonempty ((restrictFunctor V.ι).obj ((restrictFunctor (U i).ι).obj 𝒦) ≅
          SheafOfModules.free (R := V.toScheme.ringCatSheaf) I)) :
    𝒦.IsLocallyFree := by
  refine ⟨I, inferInstance, fun x => ?_⟩
  -- find a cover member `U i` containing `x`
  have hx : x ∈ (⨆ i, U i) := by rw [hcov]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨i, hxi⟩ := hx
  -- the lift of `x` into `↥(U i)`, and a trivialising open `V` there
  obtain ⟨V, hyV, ⟨iso0⟩⟩ := hfree i ⟨x, hxi⟩
  -- the image open `W ⊆ X` and the scheme iso `e : ↥V ≅ ↥W`
  set W : X.Opens := (U i).ι ''ᵁ V with hW
  set e : V.toScheme ≅ W.toScheme := (U i).ι.isoImage V with he
  have hxW : x ∈ W := (Scheme.Opens.mem_ι_image_iff (x := ⟨x, hxi⟩)).mpr hyV
  refine ⟨W, hxW, ⟨?_⟩⟩
  -- `e.hom ≫ W.ι = V.ι ≫ (U i).ι`
  have hj : e.hom ≫ W.ι = V.ι ≫ (U i).ι := (U i).ι.isoImage_hom_ι V
  -- trivialisation of `𝒦` restricted to `V.ι ≫ (U i).ι`
  have iso_j : (restrictFunctor (V.ι ≫ (U i).ι)).obj 𝒦 ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) I :=
    (restrictFunctorComp V.ι (U i).ι).app 𝒦 ≪≫ iso0
  -- transport across `e` to land on `W`
  have hB : (restrictFunctor e.hom).obj ((restrictFunctor W.ι).obj 𝒦) ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) I :=
    ((restrictFunctorComp e.hom W.ι).app 𝒦).symm ≪≫
      (restrictFunctorCongr hj).app 𝒦 ≪≫ iso_j
  exact freeIso_of_restrictFunctor_hom_freeIso e ((restrictFunctor W.ι).obj 𝒦) I hB

/-! ## Project-local Mathlib supplement — affine bridge: a free SES is a tilde

L3 of the Core-2 affine-reduction chain (`lem:kernel_iso_tilde_affine`).  A short
exact sequence `0 → 𝒦 → 𝒢 → ℋ → 0` of `(Spec R).Modules` whose middle and right
terms are free (`𝒢 ≅ free m`, `ℋ ≅ free n`) is the `tilde` of an `R`-module short
exact sequence `0 → K → R^m → R^n → 0`, with `𝒦 ≅ tilde K`.

ROUTE (the splitting sidestep — `tilde` does NOT preserve arbitrary kernels, and we
do not need it to).  `tildeFinsupp` identifies `free m ≅ tilde R^m`, `free n ≅
tilde R^n`; full-faithfulness of `tilde.functor R` writes the transported surjection
`tilde R^m → tilde R^n` as `tilde φ` for a unique `φ : R^m → R^n`; faithfulness
reflects the epi, so `φ` is surjective and `K := ker φ` gives a module SES which
splits (`R^n` is free, hence projective).  An additive functor carries a splitting
to a splitting (`ShortComplex.Splitting.map`), so the mapped inclusion
`tilde (ker φ) → tilde R^m` is a kernel of `tilde φ` with no left-exactness used; the
given `𝒦 → 𝒢` is a kernel of the same map (transported along the trivialising isos
via `KernelFork.isLimitOfIsLimitOfIff`), and kernel uniqueness
(`IsLimit.conePointUniqueUpToIso`) gives `𝒦 ≅ tilde (ker φ)`. -/

/-- Project-local (`lem:kernel_iso_tilde_affine`), L3 of the Core-2 affine-reduction
chain.

Let `S : 0 → 𝒦 → 𝒢 → ℋ → 0` be a short exact sequence of `(Spec R).Modules` with
`𝒢 ≅ free m` and `ℋ ≅ free n`.  Then there is a short exact sequence of `R`-modules
`T : 0 → K → R^m → R^n → 0` (with `T.X₂ = R^m`, `T.X₃ = R^n` finite free) together
with an isomorphism `𝒦 ≅ tilde K`.  The middle/right terms of `T` are recorded as
definitional equalities so a caller can transport the `Module.Free`/`Module.Finite`
instances of `R^m`, `R^n` onto `T.X₂`, `T.X₃` (the input to
`kernel_module_free_on_basicOpen_cover`). -/
theorem kernel_iso_tilde_of_free_ses_affine {R : CommRingCat.{u}}
    (S : ShortComplex (Spec R).Modules) (hS : S.ShortExact)
    {m n : Type u}
    (e₂ : S.X₂ ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) m)
    (e₃ : S.X₃ ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) n) :
    ∃ (T : ShortComplex (ModuleCat.{u} R)), T.ShortExact ∧
      T.X₂ = ModuleCat.of ↑R (m →₀ ↑R) ∧ T.X₃ = ModuleCat.of ↑R (n →₀ ↑R) ∧
      Nonempty (S.X₁ ≅ tilde T.X₁) := by
  classical
  haveI : (tilde.functor R).Faithful := tilde.fullyFaithfulFunctor.faithful
  haveI : Epi S.g := hS.epi_g
  -- index the free modules and trivialise `𝒢`, `ℋ` as tildes of finite free modules
  set Rm : ModuleCat.{u} R := ModuleCat.of ↑R (m →₀ ↑R) with hRm
  set Rn : ModuleCat.{u} R := ModuleCat.of ↑R (n →₀ ↑R) with hRn
  let β : (tilde.functor R).obj Rm ≅ S.X₂ := tildeFinsupp m ≪≫ e₂.symm
  let γ : (tilde.functor R).obj Rn ≅ S.X₃ := tildeFinsupp n ≪≫ e₃.symm
  -- transported surjection and its preimage `φ`
  let αraw : (tilde.functor R).obj Rm ⟶ (tilde.functor R).obj Rn := β.hom ≫ S.g ≫ γ.inv
  let φ : Rm ⟶ Rn := tilde.fullyFaithfulFunctor.preimage αraw
  have hφ : (tilde.functor R).map φ = αraw := tilde.fullyFaithfulFunctor.map_preimage αraw
  -- `αraw` is epi (composite of an epi with isos); `tilde` reflects it, so `φ` is epi
  have hαepi : Epi αraw := by
    change Epi (β.hom ≫ S.g ≫ γ.inv); infer_instance
  have hφepi : Epi φ := by
    apply (tilde.functor R).epi_of_epi_map (f := φ)
    rw [hφ]; exact hαepi
  -- the module short complex `T = 0 → ker φ → R^m → R^n → 0`
  let T : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hTse : T.ShortExact :=
    { exact := ShortComplex.exact_kernel φ
      mono_f := by dsimp only [T, ShortComplex.mk]; infer_instance
      epi_g := hφepi }
  -- `R^n` is free hence projective, so `T` splits; an additive functor carries the
  -- splitting, exhibiting `tilde (ker φ) → tilde R^m` as a kernel of `tilde φ`
  haveI : CategoryTheory.Projective T.X₃ := by
    change CategoryTheory.Projective Rn; infer_instance
  let sp : T.Splitting := hTse.splittingOfProjective
  have hkerT : IsLimit (KernelFork.ofι (T.map (tilde.functor R)).f
      (T.map (tilde.functor R)).zero) := (sp.map (tilde.functor R)).fIsKernel
  -- the given kernel `𝒦 → 𝒢`, transported along the trivialising isos, is a kernel
  -- of the same map `tilde φ`
  have hkerS := KernelFork.isLimitOfIsLimitOfIff hS.fIsKernel
      ((tilde.functor R).map φ) β.symm (fun W ψ => by
    rw [hφ]
    change ψ ≫ S.g = 0 ↔ ψ ≫ β.symm.hom ≫ αraw = 0
    rw [β.symm_hom, show β.inv ≫ αraw = S.g ≫ γ.inv by
      simp only [αraw, Iso.inv_hom_id_assoc]]
    rw [← Category.assoc]
    constructor
    · intro h; rw [h, Limits.zero_comp]
    · intro h
      rw [← cancel_mono γ.inv, Limits.zero_comp]
      exact h)
  -- kernel uniqueness: both forks are kernels of `tilde φ`
  refine ⟨T, hTse, rfl, rfl, ⟨IsLimit.conePointUniqueUpToIso hkerS hkerT⟩⟩

/-! ## Project-local Mathlib supplement — tilde-pullback base-change chain

This section decomposes the gap node `found:tilde_restrict_basicOpen`: for a
commutative ring `R`, `f ∈ R`, and an `R`-module `M`, the restriction of `tilde M`
to the basic open `D(f)` is the inverse image along `e_f : D(f) ≅ Spec R_f` of the
tilde over `R_f` of the localized module `M_f`.  The chain bottoms out at the
genuinely novel core `q_f^* tilde M ≅ tilde M_f` (`tildePullbackSpecMapIso`), proved
stalkwise.  See blueprint chapter `Kemeny_PeerDependencies.tex`. -/

/-- Project-local (`found:basicOpenIso_hom_specMap`).

The basic-open inclusion `j_f : D(f) ↪ Spec R` factors as `e_f.hom ≫ q_f`, where
`e_f : D(f) ≅ Spec R_f` is `basicOpenIsoSpecAway f` and
`q_f := Spec.map (algebraMap R R_f)` is the localization Spec map.  This is the
defining factorization equation of `basicOpenIsoSpecAway` (an `isoOfRangeEq`). -/
theorem basicOpenIsoSpecAway_hom_comp_specMap {R : CommRingCat.{u}} (f : R) :
    (basicOpenIsoSpecAway f).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (↑R) (Localization.Away f)))
      = Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Project-local helper (node 2 linchpin): scalar coherence for the pushforward of a
sheaf of modules along the localization `Spec` map `q_f : Spec R_f → Spec R`.

For `G` an `𝒪_{Spec R_f}`-module, the `R`-action on the global sections of `q_f_* G`
(through `moduleSpecΓFunctor` over `R`) equals the `R`-action obtained by restricting,
along `algebraMap R R_f`, the `R_f`-action on the global sections of `G` (over `R_f`).
The two carriers are definitionally equal (preimage of `⊤` is `⊤`); the content is the
ring naturality `Scheme.ΓSpecIso_inv_naturality` of `q_f = Spec.map (algebraMap R R_f)`.
This is the scalar bridge used to base-change `R`-linear comparison maps to `R_f`-linear
ones in the tilde-pullback chain. -/
lemma pushforward_smul_coherence {R : CommRingCat.{u}} (f : R)
    (G : (Spec (CommRingCat.of (Localization.Away f))).Modules) (r : R)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap (↑R) (Localization.Away f))))).obj G)) :
    (r • x) =
      (((algebraMap (↑R) (Localization.Away f)) r) •
        (show ((moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away f))).obj G : Type u)
          from x)) := by
  erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def,
    ModuleCat.restrictScalars.smul_def]
  congr 1
  simp only [Limits.IsInitial.to_self, CategoryTheory.Functor.map_id, CategoryTheory.id_apply]
  exact (congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap (↑R) (Localization.Away f)))) r)).symm

/-- Project-local (`found:tilde_pullback_globalSections`), node 2 of the tilde-pullback
chain.  The canonical `R_f`-linear comparison map
`η_M : M_f → Γ(Spec R_f, q_f^* tilde M)`, where `M_f := R_f ⊗_R M` is the base change
(`ModuleCat.extendScalars`).  No isomorphism is asserted; bijectivity is established
stalkwise downstream (`tildePullbackComparison_stalk_isIso`).

Construction: the unit of `q_f^* ⊣ (q_f)_*` at `tilde M` gives
`tilde M → (q_f)_* q_f^* tilde M`; applying `Γ` over `Spec R` and `tilde.isoTop`
(`Γ(Spec R, tilde M) = M`) yields an `R`-linear `M → Γ(Spec R, (q_f)_* q_f^* tilde M)`.
By `pushforward_smul_coherence` this lands, as an `R`-linear map, in the restriction of
scalars of `Γ(Spec R_f, q_f^* tilde M)`; the `extendScalars ⊣ restrictScalars`
adjunction transposes it to the `R_f`-linear `η_M`. -/
noncomputable def tilde_pullback_specMap_globalSectionsMap {R : CommRingCat.{u}} (f : R)
    (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap (↑R) (Localization.Away f))).obj M ⟶
      (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away f))).obj
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap (↑R) (Localization.Away f))))).obj (tilde M)) :=
  let q := Spec.map (CommRingCat.ofHom (algebraMap (↑R) (Localization.Away f)))
  let N := (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away f))).obj
      ((Scheme.Modules.pullback q).obj (tilde M))
  let g : M ⟶ moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj
      ((Scheme.Modules.pullback q).obj (tilde M))) :=
    (tilde.isoTop M).hom ≫ moduleSpecΓFunctor.map
      ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app (tilde M))
  let sl : (↑M : Type u) →ₛₗ[algebraMap (↑R) (Localization.Away f)] (↑N : Type u) :=
    { toFun := fun m => g.hom m
      map_add' := fun a b => g.hom.map_add a b
      map_smul' := fun r m => by
        rw [g.hom.map_smul]
        exact pushforward_smul_coherence f _ r (g.hom m) }
  let g' : M ⟶ (ModuleCat.restrictScalars (algebraMap (↑R) (Localization.Away f))).obj N :=
    ModuleCat.semilinearMapAddEquiv (algebraMap (↑R) (Localization.Away f)) M N sl
  ((ModuleCat.extendRestrictScalarsAdj
    (algebraMap (↑R) (Localization.Away f))).homEquiv M N).symm g'

/-- Project-local (`found:tilde_pullback_comparison`), node 3 of the tilde-pullback chain.

The base-change comparison morphism `α_M : tilde M_f ⟶ q_f^* tilde M` over `Spec R_f`,
where `M_f := R_f ⊗_R M`.  It is the transpose, under the tilde–`Γ` adjunction over
`R_f` (`tilde.adjunction`), of the canonical `R_f`-linear map `η_M`
(`tilde_pullback_specMap_globalSectionsMap`).  Its stalkwise invertibility is proved in
`tildePullbackComparison_stalk_isIso`, upgrading it to the core iso
`tildePullbackSpecMapIso`. -/
noncomputable def tildePullbackComparison {R : CommRingCat.{u}} (f : R)
    (M : ModuleCat.{u} R) :
    (tilde.functor (CommRingCat.of (Localization.Away f))).obj
        ((ModuleCat.extendScalars (algebraMap (↑R) (Localization.Away f))).obj M) ⟶
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap (↑R) (Localization.Away f))))).obj (tilde M) :=
  ((tilde.adjunction (R := CommRingCat.of (Localization.Away f))).homEquiv _ _).symm
    (tilde_pullback_specMap_globalSectionsMap f M)

/-! ### Node-4 decomposition: stalkwise iso of the tilde base-change comparison

The READY bottom nodes of the `tildePullbackComparison_stalk_isIso` chain
(`found:tilde_pullback_comparison_stalk`), built bottom-up.  The remaining nodes
((a1) sheafification-stalk and its consequences) are gated on a genuine
infrastructure gap and are deferred. -/

/-- Project-local (`lem:tilde_pullback_stalk_localizationTransitivity`), sub-lemma (c):
the pure-algebra heart of the node-4 stalk argument.

Localizing an `R`-module `M` first at the powers of `f` (the localization
`g : M → Mf` landing in the `R_f`-module `Mf`) and then at a prime `𝔭 ⊆ R_f`
(the localization `h : Mf → N`) exhibits `N` as the localization of `M` at the
contracted prime `𝔮 = 𝔭 ∩ R`.  This is module-level transitivity of localization
along the ring tower `R → R_f → (R_f)_𝔭`, packaged through base change
(`IsBaseChange.comp`) and the ring transitivity
`IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`. -/
theorem tildePullbackComparison_stalk_localizationTransitivity
    {R : Type*} [CommRing R] (f : R)
    {Rf : Type*} [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf]
    {M : Type*} [AddCommGroup M] [Module R M]
    {Mf : Type*} [AddCommGroup Mf] [Module R Mf] [Module Rf Mf] [IsScalarTower R Rf Mf]
    (g : M →ₗ[R] Mf) [IsLocalizedModule (Submonoid.powers f) g]
    (𝔭 : Ideal Rf) [𝔭.IsPrime]
    {N : Type*} [AddCommGroup N] [Module Rf N] [Module R N] [IsScalarTower R Rf N]
    (h : Mf →ₗ[Rf] N) [IsLocalizedModule 𝔭.primeCompl h] :
    IsLocalizedModule (𝔭.comap (algebraMap R Rf)).primeCompl
      (h.restrictScalars R ∘ₗ g) := by
  -- `r ∈ 𝔮ᶜ ↔ φ r ∈ 𝔭ᶜ`, where `𝔮 = 𝔭.comap φ` and `φ = algebraMap R Rf`.
  have mem_iff : ∀ {r : R},
      r ∈ (𝔭.comap (algebraMap R Rf)).primeCompl ↔ algebraMap R Rf r ∈ 𝔭.primeCompl := by
    intro r; exact not_congr Ideal.mem_comap
  -- An element of `powers f` maps into `𝔭ᶜ` (it is a unit in `Rf`, hence not in the prime `𝔭`),
  -- so its contraction lands in `𝔮ᶜ`.
  have powers_compl : ∀ {s : R}, s ∈ Submonoid.powers f →
      s ∈ (𝔭.comap (algebraMap R Rf)).primeCompl := by
    intro s hs
    rw [mem_iff]
    exact fun hmem => Ideal.IsPrime.ne_top ‹𝔭.IsPrime›
      (Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.map_units Rf ⟨s, hs⟩))
  refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} heq => ?_⟩
  · -- `map_units`: `r ∈ 𝔮ᶜ` acts invertibly on `N`.
    have hx : algebraMap R Rf ↑x ∈ 𝔭.primeCompl := mem_iff.mp x.2
    have hu := IsLocalizedModule.map_units h ⟨algebraMap R Rf ↑x, hx⟩
    rw [Module.End.isUnit_iff] at hu ⊢
    have hfun : (⇑((algebraMap R (Module.End R N)) ↑x))
        = ⇑((algebraMap Rf (Module.End Rf N)) (algebraMap R Rf ↑x)) := by
      funext n
      change (↑x : R) • n = (algebraMap R Rf (↑x : R)) • n
      exact (IsScalarTower.algebraMap_smul Rf (↑x : R) n).symm
    rw [hfun]; exact hu
  · -- `surj'`.
    obtain ⟨⟨mf, t⟩, ht⟩ := IsLocalizedModule.surj 𝔭.primeCompl h y
    obtain ⟨⟨r₁, s₁⟩, hrs₁⟩ := IsLocalization.surj (Submonoid.powers f) (t : Rf)
    obtain ⟨⟨m, s₂⟩, hms₂⟩ := IsLocalizedModule.surj (Submonoid.powers f) g mf
    have ht' : (↑t : Rf) • y = h mf := ht
    have hrs₁' : (↑t : Rf) * algebraMap R Rf (↑s₁ : R) = algebraMap R Rf r₁ := hrs₁
    have hms₂' : (↑s₂ : R) • mf = g m := hms₂
    -- `φ r₁ = t * φ s₁ ∈ 𝔭ᶜ`, so `r₁ ∈ 𝔮ᶜ`.
    have hr₁ : r₁ ∈ (𝔭.comap (algebraMap R Rf)).primeCompl := by
      rw [mem_iff, ← hrs₁']
      exact Submonoid.mul_mem _ t.2 (mem_iff.mp (powers_compl s₁.2))
    refine ⟨⟨(↑s₁ : R) • m, ⟨(↑s₂ : R) * r₁, Submonoid.mul_mem _ (powers_compl s₂.2) hr₁⟩⟩, ?_⟩
    change ((↑s₂ : R) * r₁) • y = h (g ((↑s₁ : R) • m))
    -- scale `t • y = h mf` by `s₁` to clear `t`'s denominator: `r₁ • y = h (s₁ • mf)`.
    have step1 : r₁ • y = h ((↑s₁ : R) • mf) := by
      have e : algebraMap R Rf r₁ • y = h ((↑s₁ : R) • mf) := by
        rw [← hrs₁', mul_comm, mul_smul, ht', IsScalarTower.algebraMap_smul Rf,
          LinearMap.map_smul_of_tower h (↑s₁ : R) mf]
      rw [← IsScalarTower.algebraMap_smul Rf r₁ y]; exact e
    rw [mul_smul, step1, ← LinearMap.map_smul_of_tower h (↑s₂ : R) ((↑s₁ : R) • mf),
      smul_comm (↑s₂ : R) (↑s₁ : R) mf, hms₂', LinearMap.map_smul_of_tower g (↑s₁ : R) m]
  · -- `exists_of_eq`.
    have heq' : h (g x₁) = h (g x₂) := heq
    obtain ⟨c₁, hc₁⟩ := IsLocalizedModule.exists_of_eq (S := 𝔭.primeCompl) (f := h) heq'
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers f) (c₁ : Rf)
    have hc₁' : (↑c₁ : Rf) • g x₁ = (↑c₁ : Rf) • g x₂ := hc₁
    have hrs' : (↑c₁ : Rf) * algebraMap R Rf (↑s : R) = algebraMap R Rf r := hrs
    have hr : r ∈ (𝔭.comap (algebraMap R Rf)).primeCompl := by
      rw [mem_iff, ← hrs']
      exact Submonoid.mul_mem _ c₁.2 (mem_iff.mp (powers_compl s.2))
    have hg_eq : g (r • x₁) = g (r • x₂) := by
      have e : algebraMap R Rf r • g x₁ = algebraMap R Rf r • g x₂ := by
        rw [← hrs', mul_comm (↑c₁ : Rf) (algebraMap R Rf (↑s : R)), mul_smul, mul_smul, hc₁']
      rw [LinearMap.map_smul_of_tower g r x₁, LinearMap.map_smul_of_tower g r x₂,
        ← IsScalarTower.algebraMap_smul Rf r (g x₁), ← IsScalarTower.algebraMap_smul Rf r (g x₂)]
      exact e
    obtain ⟨c₂, hc₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) (f := g) hg_eq
    have hc₂' : (↑c₂ : R) • (r • x₁) = (↑c₂ : R) • (r • x₂) := hc₂
    refine ⟨⟨(↑c₂ : R) * r, Submonoid.mul_mem _ (powers_compl c₂.2) hr⟩, ?_⟩
    change ((↑c₂ : R) * r) • x₁ = ((↑c₂ : R) * r) • x₂
    rw [mul_smul, mul_smul]; exact hc₂'

/-! #### Stalk module-structure enablers (iter-020)

For a tilde over a ring presented as `CommRingCat.of A`, Mathlib's stalk `Module`
and `IsLocalizedModule` instances (`AlgebraicGeometry.tilde`, Tilde.lean lines
120/132) do *not* fire by `inferInstance` — the discrimination tree fails on the
`CommRingCat.of` presentation (the iter-019 blocker; reconfirmed iter-020: even a
free-variable `Mf : ModuleCat ↑(CommRingCat.of A)` fails).  The underlying
`moduleStructurePresheaf` / `StructureSheaf.toStalkₗ` forms *do* synthesize, so we
re-expose them as `CommRingCat.of`-keyed instances.  These are the gap-independent
enablers for the node-4 source/target stalk localization lemmas, and they are
definitionally the Mathlib instances (no new module structure, no diamond). -/

/-- Project-local enabler (`mathlib:tilde_stalk_localization` shim): the stalk
`Module` instance for a tilde over a `CommRingCat.of A` ring.  Definitionally the
Mathlib instance, re-keyed so it fires on the `CommRingCat.of` presentation. -/
noncomputable instance instModuleStalkOfTilde {A : Type u} [CommRing A]
    (N : ModuleCat.{u} ↑(CommRingCat.of A))
    (x : PrimeSpectrum.Top ↑(CommRingCat.of A)) :
    Module ↑(CommRingCat.of A) ((tilde N).presheaf.stalk x) :=
  inferInstanceAs (Module ↑(CommRingCat.of A)
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf ↑(CommRingCat.of A) N).presheaf x))

/-- Project-local enabler (`mathlib:tilde_stalk_localization` shim): the stalk
`IsLocalizedModule` instance for a tilde over a `CommRingCat.of A` ring.
Definitionally the Mathlib instance, re-keyed for the `CommRingCat.of`
presentation. -/
instance instIsLocalizedModuleStalkOfTilde {A : Type u} [CommRing A]
    (N : ModuleCat.{u} ↑(CommRingCat.of A))
    (x : PrimeSpectrum.Top ↑(CommRingCat.of A)) :
    IsLocalizedModule x.asIdeal.primeCompl (tilde.toStalk N x).hom :=
  inferInstanceAs (IsLocalizedModule x.asIdeal.primeCompl
    (StructureSheaf.toStalkₗ ↑(CommRingCat.of A) N x))

/-- Project-local (`lem:tilde_pullback_stalk_source_isLocalizedModule` support):
the extension-of-scalars unit `M → R_f ⊗_R M` along the localization `R → R_f`
exhibits `M_f := R_f ⊗_R M` as the localization of `M` at the powers of `f`.

This is `IsLocalization.tensorProduct_isLocalizedModule` transported across the
canonical identification of the base-change tensor `R_f ⊗_R M` with the carrier of
`ModuleCat.extendScalars` — whose first tensor factor carries the
`restrictScalars`/`compHom` `R`-module structure rather than the `Algebra` one, so
the two tensor presentations are defeq but not syntactically equal.  The bridge is
the identity-on-carrier `R`-linear equivalence `α` between the two `R`-module
structures on `R_f`. -/
theorem extendScalars_unit_isLocalizedModule {R : CommRingCat.{u}} (f : R)
    (M : ModuleCat.{u} R) :
    IsLocalizedModule (Submonoid.powers f)
      ((ModuleCat.extendRestrictScalarsAdj
        (algebraMap (↑R) (Localization.Away f))).unit.app M).hom := by
  let φ := algebraMap (↑R) (Localization.Away f)
  let α : (Localization.Away f) ≃ₗ[↑R]
      ↑((ModuleCat.restrictScalars φ).obj
        (ModuleCat.of (Localization.Away f) (Localization.Away f))) :=
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl,
      map_smul' := fun r x => by
        change (r • x : Localization.Away f) = φ r • x
        exact Algebra.smul_def r x }
  let e := TensorProduct.congr α (LinearEquiv.refl (↑R) (↑M))
  haveI base := IsLocalization.tensorProduct_isLocalizedModule
    (Submonoid.powers f) (Localization.Away f) (M := (↑M : Type u))
  have key := IsLocalizedModule.of_linearEquiv
    (S := Submonoid.powers f)
    (f := (TensorProduct.mk (↑R) (Localization.Away f) ↑M) 1) (e := e)
  have heq : (e.toLinearMap ∘ₗ ((TensorProduct.mk (↑R) (Localization.Away f) ↑M) 1))
      = ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M).hom := by
    ext m; rfl
  rw [← heq]; exact key

/-- Project-local (`lem:tilde_pullback_stalk_source_isLocalizedModule`), sub-lemma
(d1): the source stalk `(M̃_f)_x` of the tilde base-change comparison, together with
its composite structure map `M → M_f → (M̃_f)_x` (the extension-of-scalars unit
followed by the tilde-stalk germ, restricted to scalars in `R`), is a localization
of `M` at the contracted prime `𝔮 = x ∩ R`.

Obtained by feeding the extension-of-scalars localization
(`extendScalars_unit_isLocalizedModule`) and the tilde-stalk localization
(`instIsLocalizedModuleStalkOfTilde`) into the transitivity lemma
`tildePullbackComparison_stalk_localizationTransitivity` (sub-lemma (c)).  The
structure map is written through the `ModuleCat.restrictScalars` functor so that its
`R`-module structures synthesize at statement-elaboration time (the bare
`LinearMap.restrictScalars` form would need the diamond-trap `Module ↑R` instances,
which are supplied here only inside the proof via `letI`). -/
theorem tildePullbackComparison_stalk_source_isLocalizedModule
    {R : CommRingCat.{u}} (f : R) (M : ModuleCat.{u} R)
    (x : PrimeSpectrum.Top ↑(CommRingCat.of (Localization.Away f))) :
    IsLocalizedModule
      (x.asIdeal.comap (algebraMap (↑R) (Localization.Away f))).primeCompl
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap (↑R) (Localization.Away f))).unit.app M
          ≫ (ModuleCat.restrictScalars (algebraMap (↑R) (Localization.Away f))).map
            (tilde.toStalk
              ((ModuleCat.extendScalars
                (algebraMap (↑R) (Localization.Away f))).obj M) x)).hom := by
  let φ := algebraMap (↑R) (Localization.Away f)
  let Mf : ModuleCat.{u} ↑(CommRingCat.of (Localization.Away f)) :=
    (ModuleCat.extendScalars φ).obj M
  letI iMfLoc : Module (Localization.Away f) (↑Mf) :=
    inferInstanceAs (Module ↑(CommRingCat.of (Localization.Away f)) ↑Mf)
  letI iMfR : Module (↑R) (↑Mf) := Module.compHom (↑Mf) φ
  haveI iMfST : IsScalarTower (↑R) (Localization.Away f) (↑Mf) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let Nstk := (tilde Mf).presheaf.stalk x
  letI iNLoc : Module (Localization.Away f) Nstk :=
    inferInstanceAs (Module ↑(CommRingCat.of (Localization.Away f)) Nstk)
  letI iNR : Module (↑R) Nstk := Module.compHom Nstk φ
  haveI iNST : IsScalarTower (↑R) (Localization.Away f) Nstk :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let g' : (↑M : Type u) →ₗ[↑R] (↑Mf : Type u) :=
    ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M).hom
  haveI hg : IsLocalizedModule (Submonoid.powers f) g' := extendScalars_unit_isLocalizedModule f M
  let h' : (↑Mf : Type u) →ₗ[Localization.Away f] Nstk := (tilde.toStalk Mf x).hom
  haveI hh : IsLocalizedModule x.asIdeal.primeCompl h' :=
    instIsLocalizedModuleStalkOfTilde Mf x
  have res := tildePullbackComparison_stalk_localizationTransitivity (R := ↑R) f
    (Rf := Localization.Away f) (g := g') (𝔭 := x.asIdeal) (h := h')
  convert res using 1

/-! #### Node-4 (a)-chain: stalkwise comparison via sheafification + topological pullback

The base-change comparison `tildePullbackComparison f M : tilde M_f ⟶ q_f^* tilde M`
is shown stalkwise iso by identifying both stalks with localizations of `M`.  The
target stalk `(q_f^* tilde M)_x` is computed in two steps:

* (a1) `tildePullbackComparison_stalk_sheafificationStalkIso`: the sheaf-of-modules
  pullback is the *sheafification* of the presheaf-of-modules pullback `P₀`, so its
  stalk equals the stalk of `P₀` (sheafification is a stalkwise iso).
* (a2) the presheaf-pullback stalk equals the stalk of `tilde M` at the image point
  `q_f x` (topological inverse-image stalk, `TopCat.Presheaf.stalkPullbackIso`).

All stalk computations are performed on the underlying `AddCommGrpCat`-valued
presheaves (`Scheme.Modules.toPresheaf` / `PresheafOfModules.toPresheaf`); no
`Module ↑R` synthesis on the stalk is needed at this layer. -/

/-- Project-local helper: the localization `Spec` map `q_f : Spec R_f → Spec R`
induced by `R → R_f`. -/
noncomputable def localizationSpecMap {R : CommRingCat.{u}} (f : R) :
    Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap (↑R) (Localization.Away f)))

/-- Project-local helper: the *presheaf*-of-modules pullback of `tilde M` along the
localization Spec map `q_f`, before sheafification.  Its sheafification is the
sheaf-of-modules pullback `q_f^* tilde M` (`SheafOfModules.pullbackIso`). -/
noncomputable def presheafPullbackTilde {R : CommRingCat.{u}} (f : R) (M : ModuleCat.{u} R) :=
  (PresheafOfModules.pullback (localizationSpecMap f).toRingCatSheafHom.hom).obj
    ((SheafOfModules.forget _).obj (tilde M))

set_option synthInstance.maxHeartbeats 1000000 in
-- The `HasWeakSheafify (Opens.grothendieckTopology _) Ab` instance feeding the
-- `toSheafify`-stalk-iso lemma is expensive to synthesize on the `Spec R_f` site.
/-- Project-local (`lem:tilde_pullback_stalk_sheafificationStalk`), sub-lemma (a1).

The stalk at `x` of the sheaf-of-modules pullback `q_f^* tilde M` is canonically
isomorphic to the stalk at `x` of the *presheaf*-of-modules pullback
`presheafPullbackTilde f M` (its underlying `AddCommGrpCat` presheaf).

Construction: `SheafOfModules.pullbackIso` exhibits `q_f^* tilde M` as the
sheafification of `presheafPullbackTilde f M`; the comparison map is the
sheafification-adjunction unit, whose underlying `AddCommGrpCat` map is the
abelian-group sheafification unit `toSheafify`
(`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`), and the
stalk functor sends `toSheafify` to an isomorphism
(`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` at `AddCommGrpCat`). -/
noncomputable def tildePullbackComparison_stalk_sheafificationStalkIso
    {R : CommRingCat.{u}} (f : R) (M : ModuleCat.{u} R)
    (x : PrimeSpectrum.Top ↑(CommRingCat.of (Localization.Away f))) :
    ((Scheme.Modules.pullback (localizationSpecMap f)).obj (tilde M)).presheaf.stalk x ≅
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj (presheafPullbackTilde f M).presheaf :=
  haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify _ (presheafPullbackTilde f M).presheaf)) := by
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso _ AddCommGrpCat
      (presheafPullbackTilde f M).presheaf
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapIso
      ((Scheme.Modules.toPresheaf _).mapIso
        ((SheafOfModules.pullbackIso (localizationSpecMap f).toRingCatSheafHom).app (tilde M))) ≪≫
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify _ (presheafPullbackTilde f M).presheaf))).symm

/-- Project-local (`lem:tilde_pullback_stalk_pullbackStalkIso`), sub-lemma (a):
the combined pullback-stalk identification.

For the localization Spec map `q_f : Spec R_f → Spec R` (an open immersion, as
`R_f = R_f` is a localization away from `f`) and `x ∈ Spec R_f`, the stalk at `x`
of the sheaf-of-modules pullback `q_f^* tilde M` is canonically isomorphic (as an
abelian group) to the stalk of `tilde M` at the image point `q_f x ∈ Spec R`.

ROUTE (more direct than the planned sheafification + topological-pullback chain):
since `q_f` is an open immersion, the pullback functor is isomorphic to the
restriction functor (`SheafOfModules.restrictFunctorIsoPullback`), and Mathlib's
`Scheme.Modules.restrictStalkNatIso` computes the stalk of a restriction along an
open immersion as the stalk at the image point.  Composing the two yields the
identification without needing the abstract presheaf-of-modules-pullback /
topological-inverse-image Beck–Chevalley bridge (sub-lemma (a2)). -/
noncomputable def tildePullbackComparison_stalk_pullbackStalkIso
    {R : CommRingCat.{u}} (f : R) (M : ModuleCat.{u} R)
    (x : ↥(Spec (CommRingCat.of (Localization.Away f)))) :
    ((Scheme.Modules.pullback (localizationSpecMap f)).obj (tilde M)).presheaf.stalk x ≅
      (tilde M).presheaf.stalk ((localizationSpecMap f).base x) :=
  haveI : IsOpenImmersion (localizationSpecMap f) :=
    isOpenImmersion_SpecMap_localizationAway f
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapIso
      ((Scheme.Modules.toPresheaf _).mapIso
        ((restrictFunctorIsoPullback (localizationSpecMap f)).symm.app (tilde M))) ≪≫
    (restrictStalkNatIso (localizationSpecMap f) x).app (tilde M)

/-! #### Node-4 (d2) remains open — see `task_results`.

The target-stalk localized-module claim
`tildePullbackComparison_stalk_target_isLocalizedModule` needs an `R`-LINEAR
equivalence `(tilde M)_{q_f x} ≃ₗ[R] (q_f^* tilde M)_x` to transport
`IsLocalizedModule` (via `IsLocalizedModule.of_linearEquiv`) from the tilde-stalk
germ.  The pullback stalk `(q_f^* tilde M)_x` carries no natural `R`/`R_f`-module
instance (its module structure lives over the *structure-sheaf stalk* of `Spec R_f`
at `x`, which is not identified with a localization of `R_f` at this layer), so the
abelian-group iso `tildePullbackComparison_stalk_pullbackStalkIso` (sub-lemma (a))
cannot yet be upgraded to an `R`-linear equivalence.  Closing (d2) requires:
(i) identifying the `Spec R_f` structure-sheaf stalk at `x` with `(R_f)_x`;
(ii) endowing `(q_f^* tilde M)_x` with the resulting (restricted) `R`-module
structure; (iii) proving (a)'s germ-based comparison is `R`-linear — germ
naturality of the module action, of the same flavour as the deferred (d3). -/

end AlgebraicGeometry.Scheme.Modules
