/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.Cohomology.StructureSheafModuleK.SheafProperty

/-!
# Sheaves of `k`-modules: finite-length carriers and producer instances

Sub-file (3/3) of the `StructureSheafModuleK` split (refactor iter-174). This file
hosts the downstream finite-length carriers (`IsAffineHModuleVanishing`,
`IsHModuleHomFinite`), their algebraic bridges (the `HModule` / `HModule'`
abbrevs, the H⁰ `LinearEquiv` transport companions, the constant-sheaf-Γ adjunction
upgrade), and the curve-side producer instances. Upstream sub-files
`Presheaf.lean` and `SheafProperty.lean` provide the structure-sheaf object the
carriers depend on.

Downstream finite-length carriers in this file:

* H>0 affine cohomology vanishing is carried by iter-040's
  `IsAffineHModuleVanishing` (the producer instance for the curve case
  lives at iter-051).
* H⁰ Hom-finiteness is carried by iter-043's **wholespace**
  `IsHModuleHomFinite`; the producer instance on a proper geometrically
  integral $k$-curve is supplied at iter-046 from Stein finiteness
  (`module_finite_globalSections_of_isProper`).
* The iter-041 per-affine-open variant `IsAffineHModuleHomFinite` was an
  abandoned attempt (dead scaffolding — $\Gamma(U, O_C)$ is not finite
  over $k$ on a proper affine open of a non-trivial curve) and has been
  removed from this file.

See `blueprint/src/chapters/Cohomology_StructureSheafModuleK.tex`.
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Phase A step 5/6 bridge (iter-009 scaffold): the parallel `Sheaf.H` for
`ModuleCat k`-valued sheaves. Mathlib's `CategoryTheory.Sheaf.H` is
parameterised over `Sheaf J AddCommGrpCat` only, so closing `genus` honestly
requires this `ModuleCat k`-flavoured version. The result carries `Module k`
automatically via `CategoryTheory.Abelian.Ext.instModule`, and
`Module.finrank k` is therefore well-defined on it. The declaration is a
`noncomputable abbrev` (rather than `def`) so that instance synthesis sees
through the wrapper to find `Module k` and `AddCommGroup` instances. -/
noncomputable abbrev HModule
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasSheafify J (ModuleCat.{u} k)] [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) : Type (u+1) :=
  Abelian.Ext ((constantSheaf J (ModuleCat.{u} k)).obj (ModuleCat.of k k)) F n

/-- Phase A step 6 algebraic bridge (iter-010 scaffold): the $k$-linear
identification of `HModule k F 0` with the Hom group from the constant
sheaf at `ModuleCat.of k k`. Mathlib provides
`CategoryTheory.Abelian.Ext.linearEquiv₀ : Ext X Y 0 ≃ₗ[R] (X ⟶ Y)` in any
`Linear R`-enriched abelian category; specialised to the `Linear k`
enrichment of `Sheaf J (ModuleCat.{u} k)` (auto-inferable from
`HasSheafify J (ModuleCat.{u} k)`), this collapses `HModule k F 0` to a
`k`-linear Hom group. The closure body is `Abelian.Ext.linearEquiv₀`;
probe-confirmed one-liner (iter-010 plan-agent). Used downstream to
identify `H⁰(C, toModuleKSheaf C)` with `Γ(C, O_C)` viewed as a
`k`-module on a connected proper `k`-curve. -/
noncomputable def HModule_zero_linearEquiv
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasSheafify J (ModuleCat.{u} k)] [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) :
    HModule k F 0 ≃ₗ[k]
      ((constantSheaf J (ModuleCat.{u} k)).obj (ModuleCat.of k k) ⟶ F) :=
  Abelian.Ext.linearEquiv₀

/-- Phase A step 6 *Path 2* (iter-013 scaffold): the `ModuleCat k`-flavored
cohomology of an open `X : C` with values in a sheaf `F : Sheaf J (ModuleCat.{u} k)`.
Mirrors Mathlib's `Sheaf.H' F n X = (F.cohomologyPresheaf n).obj (op X)`
(`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean` L105) for
`AddCommGrpCat`-valued sheaves, with `AddCommGrpCat.free → ModuleCat.free k`.

The codomain is `Type u` (not `ModuleCat.{u} k`): `Abelian.Ext` returns a bare
`Type u` carrying `Module k` via `Abelian.Ext.instModule` through the `Linear k`
enrichment. The `noncomputable abbrev` form (rather than `def`) is required so
instance synthesis sees through the wrapper to find `Module k (HModule' k F n X)`
and `AddCommGroup (HModule' k F n X)` — under `def`, `Module.finrank` would fail
to typecheck (cf. iter-009 design rationale on `HModule`).

This is the prerequisite for the iter-014+ `ModuleCat k`-flavored Mayer-Vietoris
LES (mirror of `Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean`).
The iter-014+ work will state and prove the LES on a `MayerVietorisSquare`,
specialising to a 2-affine cover of a proper `k`-curve in iter-015+. The
comparison theorem `cechCohomology_OC C 𝒰 n ≅ HModule k (toModuleKSheaf C) n`
for an acyclic cover (the technical heart of Path-2) is also queued for
iter-015+. -/
noncomputable abbrev HModule' (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (n : ℕ) (X : C) : Type u :=
  Abelian.Ext ((presheafToSheaf _ _).obj
    ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj X)) F n

/-- Phase A step 6 *Path 2* (iter-015): the `H⁰` algebraic bridge for `HModule'`,
mirroring iter-010's `HModule_zero_linearEquiv` for the iter-014 `HModule'`. The
$k$-linear identification of `HModule' k F 0 X` with the Hom group from the
sheafified representable `(presheafToSheaf _ _).obj ((yoneda ⋙ ModuleCat.free k).obj X)`.
Mathlib provides `CategoryTheory.Abelian.Ext.linearEquiv₀ : Ext X Y 0 ≃ₗ[R] (X ⟶ Y)`
in any `Linear R`-enriched abelian category; specialised to `R = k` and to the
`Linear k`-enriched abelian category `Sheaf J (ModuleCat.{u} k)` (the `Linear k`
enrichment is auto-inferable from `HasSheafify J (ModuleCat.{u} k)` via Mathlib's
`Sheaf.linear`), this collapses `HModule' k F 0 X` to a `k`-linear Hom group. The
closure body is `Abelian.Ext.linearEquiv₀`; probe-confirmed one-liner (iter-015
plan-agent). Used downstream as the algebraic prerequisite for Stein-factorization-
derived `H⁰(C, O_C) ≃ k` on a connected proper `k`-curve (multi-iteration; queued
iter-017+ alongside the Mayer-Vietoris LES of iter-016+). -/
noncomputable def HModule'_zero_linearEquiv
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (X : C) :
    HModule' k F 0 X ≃ₗ[k]
      ((presheafToSheaf _ _).obj
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj X) ⟶ F) :=
  Abelian.Ext.linearEquiv₀

/-- Iter-038 `Module.Finite` H⁰ transport companion for `HModule k F 0`. The iter-010
H⁰ bridge `HModule_zero_linearEquiv : HModule k F 0 ≃ₗ[k] ((constantSheaf J _).obj
(ModuleCat.of k k) ⟶ F)` identifies the degree-zero cohomology with a `k`-linear Hom
group; Mathlib's `Module.Finite.equiv` then transports `Module.Finite k`-ness across.
The `.symm` is required: iter-010's bridge has `HModule k F 0` on the LHS and the
Hom group on the RHS, but we want the Hom hypothesis on the LHS and the
`HModule` conclusion on the RHS, so we apply `.symm` first. Mirrors iter-037's
`module_finite_HModule_of_HModule'_X₄` pattern at degree $0$, with no Mayer-Vietoris
machinery required. Used downstream as a building block for `Module.Finite k
(HModule k (toModuleKSheaf C) 0)` once the Hom-from-constant-sheaf finiteness
input is supplied for proper geometrically integral $k$-curves. -/
theorem module_finite_HModule_zero
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasSheafify J (ModuleCat.{u} k)] [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k))
    [Module.Finite k ((constantSheaf J (ModuleCat.{u} k)).obj (ModuleCat.of k k) ⟶ F)] :
    Module.Finite k (HModule k F 0) :=
  Module.Finite.equiv (HModule_zero_linearEquiv k F).symm

/-- Iter-038 `Module.Finite` H⁰ transport companion for `HModule' k F 0 X`. Parallel
of `Scheme.module_finite_HModule_zero` for the iter-014 sheaf-parameterised carrier
`HModule'`. The iter-015 H⁰ bridge `HModule'_zero_linearEquiv : HModule' k F 0 X ≃ₗ[k]
((presheafToSheaf _ _).obj ((yoneda ⋙ ModuleCat.free k).obj X) ⟶ F)` identifies the
degree-zero open-evaluation cohomology with a `k`-linear Hom group from the sheafified
representable; Mathlib's `Module.Finite.equiv` then transports `Module.Finite k`-ness
across. The `.symm` is required for the same orientation reason as in
`Scheme.module_finite_HModule_zero`. -/
theorem module_finite_HModule'_zero
    (k : Type u) [Field k]
    {C : Type v} [Category.{u, v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J (Type u)] [HasSheafify J (ModuleCat.{u} k)]
    [HasExt (Sheaf J (ModuleCat.{u} k))]
    (F : Sheaf J (ModuleCat.{u} k)) (X : C)
    [Module.Finite k ((presheafToSheaf _ _).obj
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj X) ⟶ F)] :
    Module.Finite k (HModule' k F 0 X) :=
  Module.Finite.equiv (HModule'_zero_linearEquiv k F X).symm

/-- Iter-039 curve specialisation of iter-038's `module_finite_HModule_zero` to
the structure sheaf `Scheme.toModuleKSheaf C` of a `Spec k`-scheme `C`. The
Grothendieck topology `Opens.grothendieckTopology C.left.toTopCat` is auto-inferred
via the iter-005 instances `instHasSheafify_Opens_ModuleCatK` and
`instHasExt_Sheaf_Opens_ModuleCatK`. The sheaf argument is inferred from the
result type. Mirrors iter-030 / iter-035 / iter-036 / iter-037's `_curve`
patterns. Used downstream as a building block for `Module.Finite k (HModule k
(toModuleKSheaf C) 0)` once the Hom-from-constant-sheaf finiteness input is
supplied for proper geometrically integral $k$-curves (typically the morally
trivial `H^0(C, O_C) ≃ k` from Stein factorization on a connected proper
curve). -/
theorem module_finite_HModule_zero_curve
    (k : Type u) [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    [Module.Finite k
      ((constantSheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)).obj
        (ModuleCat.of k k) ⟶ Scheme.toModuleKSheaf C)] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 0) :=
  Scheme.module_finite_HModule_zero k _

/-- Iter-039 curve specialisation of iter-038's `module_finite_HModule'_zero` to
the structure sheaf `Scheme.toModuleKSheaf C` of a `Spec k`-scheme `C`,
evaluated at an arbitrary open `U` of the underlying topological space. Parallel
of `module_finite_HModule_zero_curve` for the iter-014 sheaf-parameterised
carrier `HModule'`.  Same auto-inferred topology / instance setup. The open `U`
is an explicit parameter (unlike the implicit topology); the sheaf argument is
inferred. Used downstream in the cover-evaluation chain for proper geometrically
integral $k$-curves: for each affine corner $X_i$ of an `AffineCoverMVSquare`,
the iter-039 transport propagates `Module.Finite k`-ness from the Hom group
`((presheafToSheaf _ _).obj ((yoneda ⋙ free_k).obj X_i) ⟶ toModuleKSheaf C)` —
morally `Module.Finite k (Γ(X_i, O_C))` for affine $X_i$ — to the H⁰ cohomology
piece `HModule' k (toModuleKSheaf C) 0 X_i`. -/
theorem module_finite_HModule'_zero_curve
    (k : Type u) [Field k]
    (C : Over (Spec (CommRingCat.of k)))
    (U : TopologicalSpace.Opens C.left.toTopCat)
    [Module.Finite k
      ((presheafToSheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)).obj
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U) ⟶
          Scheme.toModuleKSheaf C)] :
    Module.Finite k (Scheme.HModule' k (Scheme.toModuleKSheaf C) 0 U) :=
  Scheme.module_finite_HModule'_zero k _ U

/-- Iter-040 affine cohomology vanishing carrier predicate. Packages the
geometric statement that for every affine open `U` of `C.left.toTopCat` and
every degree `i > 0`, the open-evaluation cohomology `Scheme.HModule' k F i U`
is the zero `k`-module (formulated as `Subsingleton`, since `HModule'` returns
a `Type u` rather than a `ModuleCat` object — see iter-014 abbrev). The class
is the affine-vanishing input the cover-evaluation chain consumes once the
producer instance is supplied (queued for iter-041+; multi-iteration
project-local construction expected since Mathlib does not yet provide
scheme-level Serre vanishing on affines for the `ModuleCat k`-flavour). -/
class IsAffineHModuleVanishing
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)) :
    Prop where
  subsingleton_HModule' : ∀ {U : TopologicalSpace.Opens C.left.toTopCat},
    AlgebraicGeometry.IsAffineOpen U → ∀ i, 0 < i →
      Subsingleton (Scheme.HModule' k F i U)

/-- Iter-040 immediate consumer of `IsAffineHModuleVanishing`: given the
class hypothesis, the open-evaluation cohomology `HModule' k F i U` is
`Module.Finite k` for any affine open `U` and any `i > 0`. The proof unfolds
the class field to `Subsingleton (HModule' k F i U)` and then invokes
Mathlib's auto-derived `Subsingleton M → Module.Finite R M` instance (any
subsingleton module is finitely generated by the empty set, hence finite).
This consumer is the building block for the cover-evaluation chain: combined
with iter-039's `H^0` curve specialisations and iter-037's general-degree
corner-bridge transport, it closes the algebraic side of `Module.Finite k
(HModule k (toModuleKSheaf C) 1)` once the producer instance for
`IsAffineHModuleVanishing` is supplied. -/
theorem module_finite_HModule'_of_isAffineHModuleVanishing
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    [IsAffineHModuleVanishing k C F]
    {U : TopologicalSpace.Opens C.left.toTopCat}
    (hU : AlgebraicGeometry.IsAffineOpen U) (i : ℕ) (hi : 0 < i) :
    Module.Finite k (Scheme.HModule' k F i U) :=
  have : Subsingleton (Scheme.HModule' k F i U) :=
    IsAffineHModuleVanishing.subsingleton_HModule' (F := F) hU i hi
  inferInstance

/-- Iter-043 wholespace H⁰ Hom-finiteness carrier predicate. Packages the
algebraic statement that the global Hom group
`((constantSheaf _).obj (ModuleCat.of k k) ⟶ F)` is finite over `k`. Morally
`Γ(C.left, F)` (the **global** sections of `F`) being finite over `k`. On a
proper geometrically integral $k$-curve $C$ with $F = O_C$, this is
$\Gamma(C, O_C) \simeq k$ (Stein factorization on a proper geometrically
connected curve), so this class admits a producer instance from the
geometric content of $C$ (supplied at iter-046).

**Historical note on the abandoned per-affine-open variant.** An earlier
iter-041 attempt packaged Hom-finiteness of
`((presheafToSheaf _ _).obj ((yoneda ⋙ free k).obj U) ⟶ F)` **for every
affine open** `U`. By Yoneda + free-functor + sheafify adjunctions this
Hom group is `≃ₗ[k] Γ(U, F)`, and on a proper smooth $k$-curve $C$ with
$F = O_C$, $\Gamma(U, O_C)$ is **NOT finite over $k$** for $U$ a proper
affine open — e.g. for the standard cover of $\mathbb{P}^1_k$ by
$U_0 = U_1 = \mathbb{A}^1_k$, $\Gamma(U_i, O_{\mathbb{P}^1}) = k[t]$ is
infinite over $k$. That per-open class therefore admits no producer
instance on a non-trivial proper curve and has been deleted as dead
scaffolding.

This wholespace version captures only the **global** Hom group, which on
a proper curve is finite via Stein. Iter-044+ LES finite-length transport
uses this wholespace class (in conjunction with iter-040's H>0 affine
vanishing). -/
class IsHModuleHomFinite
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)) : Prop where
  module_finite_hom : Module.Finite k
    ((constantSheaf (Opens.grothendieckTopology C.left.toTopCat)
        (ModuleCat.{u} k)).obj (ModuleCat.of k k) ⟶ F)

/-- Iter-043 immediate consumer: with the wholespace H⁰ Hom-finiteness class
hypothesis in scope, transport via iter-038's `module_finite_HModule_zero`
(which transports `Module.Finite k`-ness across iter-010's H⁰ algebraic bridge
`HModule_zero_linearEquiv : HModule k F 0 ≃ₗ[k] ((constantSheaf _).obj _ ⟶ F)`)
to obtain `Module.Finite k (HModule k F 0)`. Works at the global level
(one Hom-finiteness instance, not one per affine open). -/
theorem module_finite_HModule_zero_of_isHModuleHomFinite
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    [IsHModuleHomFinite k C F] :
    Module.Finite k (Scheme.HModule k F 0) :=
  have := IsHModuleHomFinite.module_finite_hom (k := k) (C := C) (F := F)
  module_finite_HModule_zero k F

/-- Iter-043 curve specialisation: direct dot-notation wrapper for
`F := Scheme.toModuleKSheaf C`. Saves call sites in the curve setting from
re-typing the sheaf argument when chaining into the LES finite-length
transport (queued for iter-044+). Mirrors the iter-039/iter-042 `_curve`
patterns. -/
theorem module_finite_HModule_zero_of_isHModuleHomFinite_curve
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    [IsHModuleHomFinite k C (Scheme.toModuleKSheaf C)] :
    Module.Finite k (Scheme.HModule k (Scheme.toModuleKSheaf C) 0) :=
  module_finite_HModule_zero_of_isHModuleHomFinite k C _

/-- Iter-044 geometric Stein input for the iter-043 wholespace H⁰
Hom-finiteness carrier. For `C : Over (Spec (CommRingCat.of k))` an
integral $k$-scheme with proper structure morphism, the global sections
$\Gamma(C, O_C)$ form a finite-dimensional $k$-vector space.

This is Stein's classical statement, packaged via Mathlib's
`AlgebraicGeometry.finite_appTop_of_universallyClosed`
(`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`):
for $X$ integral and $f \colon X \to \Spec K$ universally closed and
locally of finite type, the structure-morphism ring map `f.appTop`
is module-finite. `IsProper f` packages both `UniversallyClosed f` and
`LocallyOfFiniteType f`.

The bridge from `RingHom.Finite (C.hom.appTop.hom)` to
`Module.Finite k (C.left.presheaf.obj (op ⊤))` (where the algebra
structure on `Γ(C, ⊤)` is iter-006's `kToSection`-derived) uses
`RingHom.finite_algebraMap` plus `Module.Finite.of_equiv_equiv` to
transport the base ring from intermediate `Γ(Spec k, ⊤)` to `k` along
the ring iso `Scheme.ΓSpecIso (CommRingCat.of k)`. The compatibility
of algebra maps reduces to showing
`kToSection C (op ⊤).hom = (C.hom.appTop.hom).comp (Scheme.ΓSpecIso _).inv.hom`,
which collapses via `Subsingleton.elim` on the `⊤ ⟶ ⊤` hom-set +
`Functor.map_id`.

Iter-045+ consumes this input to assemble the producer instance
`IsHModuleHomFinite k C (toModuleKSheaf C)` via lifting Mathlib's
`constantSheafΓAdj.homEquiv` to a `LinearEquiv` + identification of
`Sheaf.Γ.obj (toModuleKSheaf C)` with the underlying global sections
+ transport via `Module.Finite.equiv`. -/
theorem module_finite_globalSections_of_isProper
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] [IsProper C.hom] :
    Module.Finite k (C.left.presheaf.obj (Opposite.op ⊤)) := by
  have hf : (C.hom.appTop.hom).Finite :=
    AlgebraicGeometry.finite_appTop_of_universallyClosed k C.hom
  letI alg2 : Algebra ((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op ⊤))
               (C.left.presheaf.obj (Opposite.op ⊤))
    := RingHom.toAlgebra C.hom.appTop.hom
  have hM_inter :
      Module.Finite ((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op ⊤))
        (C.left.presheaf.obj (Opposite.op ⊤)) := by
    rw [← RingHom.finite_algebraMap]; exact hf
  refine Module.Finite.of_equiv_equiv
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
    (RingEquiv.refl _) ?_
  ext x
  simp only [RingHom.coe_comp, RingEquiv.coe_toRingHom, RingEquiv.refl_apply,
    Function.comp_apply, RingHom.algebraMap_toAlgebra]
  have h_kts : (Scheme.toModuleKSheaf.kToSection C (Opposite.op ⊤)).hom =
                (C.hom.appTop.hom).comp ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    ext y
    simp only [Scheme.toModuleKSheaf.kToSection, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply]
    exact congrFun (congrArg (·.hom) (C.left.presheaf.map_id (Opposite.op (⊤ :
                TopologicalSpace.Opens C.left.toTopCat)))) _
  calc (CommRingCat.Hom.hom (Scheme.toModuleKSheaf.kToSection C (Opposite.op ⊤)))
        ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv x)
       = (C.hom.appTop.hom).comp ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
          ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv x) :=
              congrFun (congrArg DFunLike.coe h_kts) _
    _  = C.hom.appTop.hom x := by
        simp only [RingHom.coe_comp, Function.comp_apply]
        congr 1
        change ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫
              (Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom x = x
        rw [Iso.hom_inv_id]; rfl

/-- Iter-045: LinearEquiv between the global-sections module
`(Sheaf.Γ J _).obj F` (an object of `ModuleCat k`) and the underlying carrier
of `F.obj.obj (op ⊤)` for any sheaf `F` on a topological space `X`.

The underlying iso comes from `Sheaf.ΓNatIsoSheafSections` (Mathlib
`Mathlib/CategoryTheory/Sites/GlobalSections.lean`): on a site with terminal
`T`, the global-sections functor is naturally iso to evaluation at `T`. For
the topology of opens `Opens.grothendieckTopology X`, the terminal in
`TopologicalSpace.Opens X` is the top open `⊤` (this is `Preorder.isTerminalTop`
for any preorder with a top element). The categorical iso in `ModuleCat k` is
converted to a `LinearEquiv` via `Iso.toLinearEquiv` (Mathlib's standard
upgrading of `ModuleCat`-isos to LinearEquivs).

Iter-046+ uses this `LinearEquiv` together with the linearised constant-sheaf
/ global-sections adjunction (multi-iteration; project-local lift of
Mathlib's `Adjunction.homAddEquiv` to `≃ₗ[k]`) to construct the producer
instance `IsHModuleHomFinite k C (toModuleKSheaf C)`. -/
noncomputable def SheafGammaObj_linearEquiv_top
    (k : Type u) [Field k] {X : TopCat.{u}}
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)) :
    (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} k)).obj F
      ≃ₗ[k] F.obj.obj (Opposite.op (⊤ : TopologicalSpace.Opens X)) :=
  ((Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
      (ModuleCat.{u} k) (T := ⊤) (Preorder.isTerminalTop _)).app F).toLinearEquiv

/-- Iter-045 immediate consumer: combining iter-044's geometric Stein input
`module_finite_globalSections_of_isProper` with `SheafGammaObj_linearEquiv_top`
yields `Module.Finite k ((Sheaf.Γ).obj (toModuleKSheaf C))` for a proper
integral `Spec k`-scheme `C`.

The `haveI` is necessary because `Module.Finite.equiv` does not
auto-synthesise the `[Module.Finite k]` hypothesis on the source: the iter-044
declaration's conclusion is `Module.Finite k (C.left.presheaf.obj (op ⊤))`,
but the source of `(SheafGammaObj_linearEquiv_top _ _).symm` is
`(toModuleKSheaf C).obj.obj (op ⊤)` — these are *the same Module* (via the
iter-006 `toModuleKPresheaf_obj` simp lemma) but Lean needs the `haveI` to
register the typeclass under the new spelling.

This is the algebraic input for the iter-046+ producer-instance assembly:
bridging from `Sheaf.Γ.obj` to the Hom group `((constantSheaf @ unit) ⟶ -)`
requires the linearised constant-sheaf-Γ adjunction, which is multi-iteration
project-local infrastructure. -/
theorem module_finite_gammaObj_of_isProper
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] [IsProper C.hom] :
    Module.Finite k
      ((Sheaf.Γ (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)).obj
        (Scheme.toModuleKSheaf C)) := by
  haveI : Module.Finite k
      ((Scheme.toModuleKSheaf C).obj.obj
        (Opposite.op (⊤ : TopologicalSpace.Opens C.left.toTopCat)) : ModuleCat k) :=
    module_finite_globalSections_of_isProper k C
  exact Module.Finite.equiv
    (SheafGammaObj_linearEquiv_top k (Scheme.toModuleKSheaf C)).symm

/-- Iter-046: applied LinearEquiv from the constant-sheaf-Γ adjunction. For any
sheaf `F : Sheaf J (ModuleCat k)` and `X : ModuleCat k`, gives a `k`-LinearEquiv
between the Hom group `((constantSheaf).obj X ⟶ F)` (sheaf morphisms from the
constant sheaf at `X`) and `(X ⟶ (Sheaf.Γ).obj F)` (module morphisms into the
global sections of `F`).

Built from `(constantSheafΓAdj).homLinearEquiv` (iter-046 Mathlib gap-fill).
The five `haveI` lines establish the typeclass scaffolding required to invoke
the gap-fill: `presheafToSheaf` Linear (via `sheafificationAdjunction`),
`constantSheaf` Additive + Linear (via composition), and `Sheaf.Γ` Additive +
Linear (via the `right_adjoint_*` propagators along `constantSheafΓAdj`).

Used in iter-046's producer instance `instIsHModuleHomFinite_toModuleKSheaf`
to bridge from `Sheaf.Γ.obj`-finiteness (iter-045) to Hom-from-constantSheaf-
finiteness (the `IsHModuleHomFinite` carrier). -/
noncomputable def constantSheafGammaHom_linearEquiv
    (k : Type u) [Field k] {C : Type v} [Category.{u, v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J (ModuleCat.{u} k)] [HasGlobalSectionsFunctor J (ModuleCat.{u} k)]
    (X : ModuleCat.{u} k) (F : Sheaf J (ModuleCat.{u} k)) :
    ((constantSheaf J _).obj X ⟶ F) ≃ₗ[k] (X ⟶ (Sheaf.Γ J _).obj F) :=
  haveI : (presheafToSheaf J (ModuleCat.{u} k)).Linear k :=
    (sheafificationAdjunction J _).left_adjoint_linear k
  haveI : (constantSheaf J (ModuleCat.{u} k)).Additive := by
    unfold constantSheaf; infer_instance
  haveI : (Sheaf.Γ J (ModuleCat.{u} k)).Additive :=
    (constantSheafΓAdj J _).right_adjoint_additive
  haveI : (constantSheaf J (ModuleCat.{u} k)).Linear k := by
    unfold constantSheaf; infer_instance
  haveI : (Sheaf.Γ J (ModuleCat.{u} k)).Linear k :=
    (constantSheafΓAdj J _).right_adjoint_linear k
  (constantSheafΓAdj J _).homLinearEquiv k X F

/-- Iter-046: Hom-from-`k` upgrade. The Hom group `(ModuleCat.of k k ⟶ M)` for
`M : ModuleCat k` is canonically `k`-LinearEquivalent to `M` via `f ↦ f 1`.
Direct one-liner combining `ModuleCat.homLinearEquiv` (Mathlib's
LinearEquiv-version of the underlying-LinearMap correspondence) with
`LinearMap.ringLmapEquivSelf` (the standard `(R →ₗ[R] M) ≃ₗ[S] M` evaluation). -/
noncomputable def homFromOne_linearEquiv (k : Type u) [Field k] (M : ModuleCat.{u} k) :
    (ModuleCat.of k k ⟶ M) ≃ₗ[k] M :=
  (ModuleCat.homLinearEquiv (M := ModuleCat.of k k) (N := M) (S := k)).trans
    (LinearMap.ringLmapEquivSelf k k M)

/-- Iter-046: **the producer instance** for `IsHModuleHomFinite k C (toModuleKSheaf C)`
on a proper integral `Spec k`-scheme `C`. Closes the four-step chain:

  (1) `constantSheafGammaHom_linearEquiv` (iter-046 step 1) bridges the Hom group
      `((constantSheaf).obj k ⟶ toModuleKSheaf C)` to `(k ⟶ Sheaf.Γ.obj (toModuleKSheaf C))`.
  (2) `homFromOne_linearEquiv` (iter-046 step 3) identifies `(k ⟶ M)` with `M`
      as `k`-modules.
  (3) Combined LinearEquiv from (1)+(2): `((constantSheaf).obj k ⟶ toModuleKSheaf C)
      ≃ₗ[k] Sheaf.Γ.obj (toModuleKSheaf C)`.
  (4) `module_finite_gammaObj_of_isProper` (iter-045 step 2) provides
      `Module.Finite k (Sheaf.Γ.obj (toModuleKSheaf C))` from `[IsIntegral C.left]
      [IsProper C.hom]` (iter-044 geometric Stein input).
  (5) Transport via `Module.Finite.equiv (.symm)` of the combined LinearEquiv.

Once landed, iter-043's curve consumer `module_finite_HModule_zero_of_isHModuleHomFinite_curve`
fires automatically on `Module.Finite k (HModule k (toModuleKSheaf C) 0)` queries,
closing the H⁰ side of the genus-finrank Module.Finite ladder.

Marked `instance` (not `theorem`) — this is a *producer* of a typeclass instance,
to be picked up by typeclass synthesis when the consumer asks for
`IsHModuleHomFinite k C (toModuleKSheaf C)`. Hypotheses `[IsIntegral C.left]`,
`[IsProper C.hom]` are class arguments propagated via instance synthesis from
the use site (where `C` is concretely a proper integral `Spec k`-scheme, e.g.\ a
smooth proper geometrically irreducible curve). -/
noncomputable instance instIsHModuleHomFinite_toModuleKSheaf
    (k : Type u) [Field k] (C : Over (Spec (CommRingCat.of k)))
    [IsIntegral C.left] [IsProper C.hom] :
    IsHModuleHomFinite k C (Scheme.toModuleKSheaf C) where
  module_finite_hom := by
    haveI := Scheme.module_finite_gammaObj_of_isProper k C
    let LE1 := constantSheafGammaHom_linearEquiv k
      (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.of k k)
      (Scheme.toModuleKSheaf C)
    let LE2 := homFromOne_linearEquiv k
      ((Sheaf.Γ (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)).obj
        (Scheme.toModuleKSheaf C))
    exact Module.Finite.equiv (LE1.trans LE2).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Phase A step 6 *Path 2* (iter-012 scaffold): the Čech cochain complex of
the structure sheaf of a `Spec k`-scheme `C : Over (Spec (CommRingCat.of k))`,
with respect to an arbitrary indexed family of opens `𝒰 : ι → Opens C.left.toTopCat`.
Built from Mathlib's `CategoryTheory.cechComplexFunctor` (file
`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`) applied to the
underlying presheaf of `Scheme.toModuleKSheaf C` (iter-006). The result is a
cochain complex valued in `ModuleCat.{u} k`, indexed by `ℕ`.

The cohomology of this complex is `Scheme.cechCohomology_OC` below. The
downstream comparison theorem (Čech cohomology = derived-functor cohomology
= `Scheme.HModule k (Scheme.toModuleKSheaf C)` for an acyclic cover) is
queued for iter-013+; iter-012 only establishes the Čech-side carrier. -/
noncomputable def Scheme.cechCochain_OC
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  (cechComplexFunctor 𝒰).obj ((sheafToPresheaf _ _).obj (Scheme.toModuleKSheaf C))

/-- Phase A step 6 *Path 2* (iter-012 scaffold): the `n`-th Čech cohomology
of the structure sheaf for an arbitrary indexed open cover. Defined as the
`n`-th homology of the Čech cochain complex `Scheme.cechCochain_OC`. The
result lives in `ModuleCat.{u} k` and therefore carries a `Module k`
structure for free; the iter-013+ comparison theorem will identify it
with `Scheme.HModule k (Scheme.toModuleKSheaf C) n` when the cover is
acyclic. -/
noncomputable def Scheme.cechCohomology_OC
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) (n : ℕ) :
    ModuleCat.{u} k :=
  (Scheme.cechCochain_OC C 𝒰).homology n

/-- Iter-047: parameterised Čech cochain complex generalising iter-012's
`Scheme.cechCochain_OC` to any sheaf of `k`-modules `F`, not just the structure
sheaf. Built from the same Mathlib `CategoryTheory.cechComplexFunctor`
(`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`) applied to the
underlying presheaf of `F`. The result is a cochain complex valued in
`ModuleCat.{u} k`, indexed by `ℕ`. Iter-012's specialisation
`Scheme.cechCochain_OC C 𝒰` is recovered by setting `F := Scheme.toModuleKSheaf C`
(see `Scheme.cechCochain_OC_eq` below).

This generalisation is the foundational scaffolding the iter-048+ Čech-vs-derived
comparison theorem will build on: the comparison map
`Scheme.cechCohomology k C F 𝒰 n →ₗ[k] Scheme.HModule' k F n (⨆ᵢ 𝒰 i)`
(queued for iter-048) is naturally parameterised over the sheaf `F`, not just
the structure sheaf, so the parameterised carrier is the right level of
generality. -/
noncomputable def Scheme.cechCochain
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  (cechComplexFunctor 𝒰).obj ((sheafToPresheaf _ _).obj F)

/-- Iter-047: parameterised Čech cohomology generalising iter-012's
`Scheme.cechCohomology_OC`. The `n`-th cohomology of the parameterised Čech
cochain complex. The result lives in `ModuleCat.{u} k`. Iter-012's
specialisation is recovered by `Scheme.cechCohomology_OC_eq` below. -/
noncomputable def Scheme.cechCohomology
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) (n : ℕ) :
    ModuleCat.{u} k :=
  (Scheme.cechCochain C F 𝒰).homology n

/-- Iter-047 bridge: iter-012's `Scheme.cechCochain_OC` is definitionally the
`F := Scheme.toModuleKSheaf C` specialisation of `Scheme.cechCochain`. The
proof is `rfl` since iter-012's body is the same `(cechComplexFunctor 𝒰).obj
((sheafToPresheaf _ _).obj (Scheme.toModuleKSheaf C))` term. Used by downstream
consumers (iter-048+) to switch between the iter-012 structure-sheaf-specific
form and the iter-047 parameterised form without semantic loss. -/
theorem Scheme.cechCochain_OC_eq
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) :
    Scheme.cechCochain_OC C 𝒰 = Scheme.cechCochain C (Scheme.toModuleKSheaf C) 𝒰 :=
  rfl

/-- Iter-047 bridge: iter-012's `Scheme.cechCohomology_OC` is definitionally the
`F := Scheme.toModuleKSheaf C` specialisation of `Scheme.cechCohomology`. -/
theorem Scheme.cechCohomology_OC_eq
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) (n : ℕ) :
    Scheme.cechCohomology_OC C 𝒰 n =
      Scheme.cechCohomology C (Scheme.toModuleKSheaf C) 𝒰 n :=
  rfl

/-- Iter-048: Čech-side acyclicity carrier predicate. The cover `𝒰` is
*Čech-acyclic for the sheaf `F` of `k`-modules* on `C` if positive-degree Čech
cohomology vanishes (in the `Subsingleton` sense — `Scheme.cechCohomology C F 𝒰 n`
has type `ModuleCat.{u} k`, but `Subsingleton` on the underlying type is the
natural and more chainable form). Mirrors the iter-040 / iter-043 carrier-
predicate pattern: a single-field `Prop` class capturing a combinatorial
vanishing condition that downstream consumers receive as an instance argument.

This is the foundational Čech-side input that the iter-051 producer instance for
`IsAffineHModuleVanishing k C (toModuleKSheaf C)` will consume, in conjunction
with the iter-049+ Čech-vs-derived comparison theorem and iter-048's consumer. -/
class Scheme.IsCechAcyclicCover
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k))
    {ι : Type u} (𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat) : Prop where
  subsingleton_cechCohomology :
    ∀ (n : ℕ), 0 < n → Subsingleton (Scheme.cechCohomology C F 𝒰 n)

/-- Iter-048: subsingleton transport via Čech acyclicity + comparison.

Given the iter-048 carrier hypothesis `[IsCechAcyclicCover F 𝒰]` AND an explicit
comparison iso `compIso n : cechCohomology C F 𝒰 n ≃ₗ[k] HModule' k F n (⨆ 𝒰 i)`
(the Čech-vs-derived comparison, queued for iter-049+ to construct as a
theorem), conclude that `Subsingleton (HModule' k F n (⨆ 𝒰 i))` for `n ≥ 1`.

The `compIso` is taken as an *explicit argument*, not a class field. The
comparison itself is a `LinearEquiv` (data), so it cannot be a field of a
`Prop`-valued class; more importantly, decoupling the Čech-side combinatorial
vanishing (iter-048) from the substantive comparison theorem (iter-049+) lets
each step land as a single iteration. Iter-049+ will provide the comparison as
a theorem, which iter-048's consumer accepts directly via this argument.

The consumer body extracts the class field (the `Subsingleton` on
`cechCohomology n`) and transports along `(compIso n).symm.toEquiv.subsingleton`. -/
theorem Scheme.subsingleton_HModule'_supr_of_isCechAcyclicCover
    {k : Type u} [Field k] {C : Over (Spec (.of k))}
    {F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)}
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [Scheme.IsCechAcyclicCover F 𝒰]
    (compIso : ∀ (n : ℕ),
      Scheme.cechCohomology C F 𝒰 n ≃ₗ[k]
        Scheme.HModule' k F n (⨆ i, 𝒰 i))
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (Scheme.HModule' k F n (⨆ i, 𝒰 i)) := by
  haveI := Scheme.IsCechAcyclicCover.subsingleton_cechCohomology
    (F := F) (𝒰 := 𝒰) n hn
  exact (compIso n).symm.toEquiv.subsingleton

/-- Iter-048: curve specialisation at `F := Scheme.toModuleKSheaf C`.

Mirrors the iter-039 / iter-042 / iter-043 `_curve` pattern: a thin dot-notation
wrapper that saves call sites in the curve setting (where `F` is the structure
sheaf) from re-typing `Scheme.toModuleKSheaf C` whenever the iter-048 consumer
is chained through. Used by the iter-051 `IsAffineHModuleVanishing k C (toModuleKSheaf C)`
producer instance. -/
theorem Scheme.subsingleton_HModule'_supr_of_isCechAcyclicCover_curve
    {k : Type u} [Field k] (C : Over (Spec (.of k)))
    {ι : Type u} {𝒰 : ι → TopologicalSpace.Opens C.left.toTopCat}
    [Scheme.IsCechAcyclicCover (Scheme.toModuleKSheaf C) 𝒰]
    (compIso : ∀ (n : ℕ),
      Scheme.cechCohomology C (Scheme.toModuleKSheaf C) 𝒰 n ≃ₗ[k]
        Scheme.HModule' k (Scheme.toModuleKSheaf C) n (⨆ i, 𝒰 i))
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (Scheme.HModule' k (Scheme.toModuleKSheaf C) n (⨆ i, 𝒰 i)) :=
  Scheme.subsingleton_HModule'_supr_of_isCechAcyclicCover (𝒰 := 𝒰) compIso n hn

end AlgebraicGeometry
