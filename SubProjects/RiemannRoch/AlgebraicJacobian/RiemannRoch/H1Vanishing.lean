/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Cohomology.StructureSheafModuleK
import AlgebraicJacobian.RiemannRoch.WeilDivisor

/-!
# Vanishing of `H¹` for skyscraper sheaves on a curve (RR.2.H¹)

This file is the **RR.2.H¹** project-side build of the closed-point
skyscraper `H¹`-vanishing identity

  `dim_{k̄} H¹(C, skyscraperSheaf P (ModuleCat.of k̄ k̄)) = 0`

on a smooth proper geometrically irreducible curve `C / k̄`. The file is
the iter-191 Lane H **file-skeleton**: each of the eight pinned
declarations carries the *intended* substantive type signature (matching
the blueprint `\lean{...}` pin in `chapters/RiemannRoch_H1Vanishing.tex`),
with `sorry` bodies; the iter-192+ closure follows the classical
Hartshorne III.2.5 flasque-vanishing argument.

The chapter strategy (Hartshorne III §2): an injective resolution of a
flasque sheaf yields a flasque quotient at each stage; the
global-sections functor is exact on a flasque-to-flasque-to-flasque
short exact sequence; hence the right-derived global-sections functor
vanishes on a flasque input in positive degree. We specialise the
abstract flasque-vanishing to the closed-point skyscraper sheaf, which
is flasque because it is the pushforward, along the closed embedding of
a one-point subspace, of the constant sheaf on an irreducible base.

## Eight pinned declarations

1. `AlgebraicGeometry.Scheme.IsFlasque` — predicate on
   `Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)`.
2. `AlgebraicGeometry.Scheme.IsFlasque.pushforward` — pushforward of a
   flasque sheaf is flasque (Hartshorne II.1, Ex. 1.16(d)).
3. `AlgebraicGeometry.Scheme.IsFlasque.constant_of_irreducible` —
   constant sheaf on an irreducible space is flasque (Hartshorne
   II.1, Ex. 1.16(a)).
4. `AlgebraicGeometry.Scheme.HModule_flasque_eq_zero` — flasque sheaves
   have zero `HModule` in positive degree (Hartshorne III.2.5).
5. `AlgebraicGeometry.Scheme.skyscraperSheaf_eq_pushforward_const` —
   skyscraper sheaf is the pushforward of a constant sheaf along the
   closed embedding of the closure of the support point.
6. `AlgebraicGeometry.Scheme.PrimeDivisor.closure_isIrreducible` — the
   closure of the support point of a `PrimeDivisor` is irreducible.
7. `AlgebraicGeometry.Scheme.skyscraperSheaf_isFlasque` —
   closed-point skyscraper sheaf is flasque.
8. `AlgebraicGeometry.Scheme.H1_skyscraperSheaf_finrank_eq_zero` — the
   `RR.2.H¹` headline (`dim_{k̄} H¹(C, k(P)) = 0`), obtained by composing
   declarations 4 and 7.

The eighth declaration also lives as a `private` typed-`sorry` helper at
`AlgebraicJacobian/RiemannRoch/RRFormula.lean`. The `private` modifier
mangles the internal name of the RRFormula copy, so the public
declaration in this file is the one resolved by the blueprint's
`\lean{...}` pin and by downstream consumers (`sync_leanok` keys on the
fully-qualified public name).

## References

Blueprint: `blueprint/src/chapters/RiemannRoch_H1Vanishing.tex`.
Source: Hartshorne, *Algebraic Geometry*, II.1, Exercise 1.16
(flasque sheaves), Exercise 1.17 (skyscraper sheaves);
III.2, Proposition 2.5 (flasque sheaves are acyclic).
-/

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace TopCat
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-! ## §1. Flasque sheaves of `kbar`-modules -/

/-- **Flasque sheaf of `kbar`-modules on a topological space**
(Hartshorne II.1, Exercise 1.16; III.2, paragraph preceding Lemma 2.4).

A sheaf `F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)`
is **flasque** when, for every inclusion of opens `V ≤ U` in `X`, the
restriction map
`F.val.obj (op U) → F.val.obj (op V)` is surjective as a map of
`kbar`-modules.

The predicate is read off the underlying presheaf of `kbar`-modules and
applies uniformly to the project's `ModuleCat kbar`-flavoured cohomology
pipeline (it does not depend on any topological-space hypothesis on `X`,
so the curve specialisation is by instance synthesis on
`C.left.toTopCat`).

Blueprint reference: `def:isFlasque_sheaf`. -/
def Scheme.IsFlasque
    {kbar : Type u} [Field kbar] {X : TopCat.{u}}
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)) : Prop :=
  ∀ ⦃U V : TopologicalSpace.Opens X⦄ (h : V ≤ U),
    Function.Surjective ((F.val.map (homOfLE h).op).hom)

/-- **Pushforward of a flasque sheaf is flasque** (Hartshorne II.1,
Exercise 1.16(d)).

For a continuous map of topological spaces `f : X ⟶ Y` and a flasque
sheaf `F` of `kbar`-modules on `X`, the pushforward sheaf `f _* F` is
flasque on `Y`. The reason is purely formal: the restriction map of
`f _* F` along `V ≤ U` in `Y` is, by definition of pushforward, the
restriction map of `F` along `f ⁻¹ V ≤ f ⁻¹ U` in `X`, which is
surjective by hypothesis on `F`.

**iter-191 Lane H prover dispatch** — closed via the unfolding
`pushforward.map (homOfLE h).op = F.val.map ((Opens.map f).map (homOfLE h)).op`
(by `rfl`), so flasqueness of `F` along `(Opens.map f).map (homOfLE h)` gives
the conclusion. Blueprint reference: `lem:isFlasque_pushforward`. -/
theorem Scheme.IsFlasque.pushforward
    {kbar : Type u} [Field kbar] {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)}
    (hF : Scheme.IsFlasque F) :
    Scheme.IsFlasque
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} kbar) f).obj F) := by
  intro U V h
  exact hF ((Opens.map f).map (homOfLE h)).le

/-- **Constant sheaf on an irreducible topological space is flasque**
(Hartshorne II.1, Exercise 1.16(a)).

For an irreducible topological space `X`, every nonempty open is
connected and dense; the constant presheaf `U ↦ A` already satisfies the
sheaf condition, and its restriction maps are the identity on `A` (for
the nonempty branches) and factor through `0` (for the empty branch).

**iter-191 Lane H file-skeleton** — Tier-3 honest typed sorry; closure
is iter-192+. Blueprint reference:
`lem:isFlasque_constant_irreducible`. -/
theorem Scheme.IsFlasque.constant_of_irreducible
    (kbar : Type u) [Field kbar] {X : TopCat.{u}}
    [IrreducibleSpace X] (A : ModuleCat.{u} kbar) :
    Scheme.IsFlasque
      ((constantSheaf (Opens.grothendieckTopology X)
        (ModuleCat.{u} kbar)).obj A) := by
  -- iter-196 Lane H prover attempt: case analysis on `V = ⊥`.
  -- Empty branch (closed below): `F.val.obj (op ⊥)` is terminal in `ModuleCat kbar`
  -- by `TopCat.Sheaf.isTerminalOfEqEmpty`; hence the underlying type is
  -- `Subsingleton`, so any element of the codomain equals the image of `0`.
  -- Non-empty branch (residual): on an irreducible space, every non-empty open is
  -- connected/dense, so the sheafification unit
  -- `A → ((constantSheaf J D).obj A).val.obj (op V)` is iso for non-empty `V`;
  -- composition with the inverse on `V` and the unit on `U` lifts any
  -- `y ∈ F(V)` to a preimage in `F(U)`. Formalising this requires the
  -- plus-construction characterisation of sheafification on irreducible spaces
  -- (Mathlib snapshot `b80f227` does not ship a direct lemma).
  intro U V h y
  by_cases hV : V = ⊥
  · -- empty branch: codomain is terminal, hence Subsingleton.
    subst hV
    have hterm : Limits.IsTerminal
        (((constantSheaf (Opens.grothendieckTopology X)
            (ModuleCat.{u} kbar)).obj A).val.obj
          (Opposite.op (⊥ : TopologicalSpace.Opens X))) :=
      TopCat.Sheaf.isTerminalOfEqEmpty
        ((constantSheaf (Opens.grothendieckTopology X)
          (ModuleCat.{u} kbar)).obj A) rfl
    have hzero : Limits.IsZero
        (((constantSheaf (Opens.grothendieckTopology X)
            (ModuleCat.{u} kbar)).obj A).val.obj
          (Opposite.op (⊥ : TopologicalSpace.Opens X))) :=
      hterm.isZero
    have hsub : Subsingleton
        ((((constantSheaf (Opens.grothendieckTopology X)
            (ModuleCat.{u} kbar)).obj A).val.obj
          (Opposite.op (⊥ : TopologicalSpace.Opens X))) : Type u) :=
      ModuleCat.subsingleton_of_isZero hzero
    exact ⟨0, Subsingleton.elim _ _⟩
  · -- non-empty branch: requires sheafification-unit-iso on irreducible space.
    sorry

/-- **Injective sheaves have vanishing higher cohomology** (axiom-clean
helper, Hartshorne III §1).

For a topological space `X` and an injective object `I` of the
`kbar`-module sheaf category, the `kbar`-flavoured derived
global-sections cohomology `HModule kbar I i` is the zero `kbar`-module
for every `i ≥ 1`. This is immediate from Mathlib's
`HasInjectiveDimensionLT` framework: `Injective I` gives
`HasInjectiveDimensionLT I 1` (Mathlib
`instHasInjectiveDimensionLTOfNatNatOfInjective`), and
`HasInjectiveDimensionLT.subsingleton` yields
`Subsingleton (Abelian.Ext Y I i)` for `i ≥ 1` and any `Y`; specialising
`Y` to the constant sheaf at `kbar` and applying
`Module.finrank_zero_of_subsingleton` closes the goal.

**iter-192 Lane H prover dispatch** — closed axiom-clean. Used as the
`Ext^i(_, I) = 0` input inside the Hartshorne III.2.5 long-exact-sequence
chase for `HModule_flasque_eq_zero` below. -/
theorem Scheme.HModule_injective_finrank_eq_zero
    {kbar : Type u} [Field kbar] {X : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)]
    [HasExt (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar))]
    {I : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)}
    [Injective I] (i : ℕ) (hi : 1 ≤ i) :
    Module.finrank kbar (Scheme.HModule kbar I i) = 0 := by
  have hsub : Subsingleton (Scheme.HModule kbar I i) :=
    HasInjectiveDimensionLT.subsingleton I 1 i hi _
  exact Module.finrank_zero_of_subsingleton

/-- **The canonical injective-embedding short exact sequence**
`0 → F → Injective.under F → cokernel(Injective.ι F) → 0` of sheaves of
`kbar`-modules (axiom-clean helper). The embedding `Injective.ι F` is
mono by `Injective.ι_mono`, the cokernel projection is epi by
construction, and the middle row is exact at `Injective.under F` by
`ShortComplex.exact_cokernel`. -/
noncomputable def Scheme.injectiveSES
    {kbar : Type u} [Field kbar] {X : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)]
    [HasExt (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar))]
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)) :
    CategoryTheory.ShortComplex
      (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)) :=
  ShortComplex.mk (Injective.ι F) (Limits.cokernel.π (Injective.ι F))
    (Limits.cokernel.condition (Injective.ι F))

/-- The injective-embedding short complex is short exact. -/
theorem Scheme.injectiveSES_shortExact
    {kbar : Type u} [Field kbar] {X : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)]
    [HasExt (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar))]
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)) :
    (Scheme.injectiveSES F).ShortExact :=
  { exact := ShortComplex.exact_cokernel (Injective.ι F)
    mono_f := Injective.ι_mono F
    epi_g := Limits.coequalizer.π_epi }

/-- **Generic LES vanishing lemma**: in an abelian category with enough Ext,
if `0 → S.X₁ → S.X₂ → S.X₃ → 0` is short exact with `S.X₂` injective and the
post-composition `Hom(X, S.X₂) → Hom(X, S.X₃)` is surjective, then
`Ext X S.X₁ 1` is the zero `Subsingleton`.

This is the structural skeleton of the Hartshorne III.2.5 argument
specialised at degree 1: the long exact sequence
`Ext X S.X₂ 0 → Ext X S.X₃ 0 → Ext X S.X₁ 1 → Ext X S.X₂ 1`
collapses because the rightmost term vanishes (injectivity of `S.X₂`)
and the leftmost map is surjective by the `Hom`-level hypothesis. The
proof composes:
- `HasInjectiveDimensionLT.subsingleton` (injective ⇒ `Ext X S.X₂ 1 = 0`).
- `Abelian.Ext.covariant_sequence_exact₁` (any `x₁ ∈ Ext X S.X₁ 1` lifts
  to some `x₃ ∈ Ext X S.X₃ 0` via the connecting morphism).
- `Abelian.Ext.addEquiv₀` (identifies `Ext X S.X₃ 0` with `Hom(X, S.X₃)`).
- `comp_extClass_assoc` (the LES "complex" identity used to discharge
  `(Ext.mk₀ S.g).comp extClass = 0`).

**iter-192 Lane H prover dispatch** — closed axiom-clean. Used to peel
off the `i = 1` case of `HModule_flasque_eq_zero` once the
`Hom(X, I) → Hom(X, G)`-surjectivity input (Hartshorne II Ex. 1.16(b))
is supplied for an injective resolution. -/
theorem ext_one_eq_zero_of_hom_surjective_of_injective
    {C : Type v} [Category.{u} C] [Abelian C] [HasExt C]
    (X : C) {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    (hsurj : Function.Surjective (fun (f : X ⟶ S.X₂) => f ≫ S.g))
    (x₁ : Abelian.Ext X S.X₁ 1) : x₁ = 0 := by
  have hinj_subs : Subsingleton (Abelian.Ext X S.X₂ 1) :=
    HasInjectiveDimensionLT.subsingleton S.X₂ 1 1 le_rfl _
  have hker : x₁.comp (Abelian.Ext.mk₀ S.f) (show (1 : ℕ) + 0 = 1 by omega) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x₃, hx₃⟩ :=
    Abelian.Ext.covariant_sequence_exact₁ X hS x₁ hker
      (n₀ := 0) (show 0 + 1 = 1 by omega)
  obtain ⟨y, hy⟩ := hsurj (Abelian.Ext.addEquiv₀ x₃)
  simp only at hy
  have hx3eq : Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ x₃) = x₃ := by
    rw [← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.symm_apply_apply]
  have hx3_factored :
      x₃ = (Abelian.Ext.mk₀ y).comp (Abelian.Ext.mk₀ S.g)
        (show (0 : ℕ) + 0 = 0 by omega) := by
    rw [Abelian.Ext.mk₀_comp_mk₀, hy, hx3eq]
  rw [← hx₃, hx3_factored]
  rw [Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ y) (Abelian.Ext.mk₀ S.g) hS.extClass
      (show (0 : ℕ) + 0 = 0 by omega) (show (0 : ℕ) + 1 = 1 by omega)
      (show (0 : ℕ) + 0 + 1 = 1 by omega)]
  have hSg_extClass_zero :
      (Abelian.Ext.mk₀ S.g).comp hS.extClass (show (0 : ℕ) + 1 = 1 by omega) = 0 := by
    have key := hS.comp_extClass_assoc (Y := S.X₁) (n := 0)
      (Abelian.Ext.mk₀ (𝟙 S.X₁)) (n' := 1) (h := show (1 : ℕ) + 0 = 1 by omega)
    rw [Abelian.Ext.comp_mk₀_id] at key
    exact key
  rw [hSg_extClass_zero, Abelian.Ext.comp_zero]

/-- **Higher-degree LES vanishing lemma** (axiom-clean structural helper,
iter-193 Lane H prover dispatch).

Given a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` in an abelian
category with injective `S.X₂` and `n₀ ≥ 1`, if every element of
`Abelian.Ext X S.X₃ n₀` is zero, then so is every element of
`Abelian.Ext X S.X₁ (n₀ + 1)`. This is the higher-degree analogue of
`ext_one_eq_zero_of_hom_surjective_of_injective`: at degrees `n₀ ≥ 1` the
`Hom`-surjectivity hypothesis is replaced by the (stronger, recursable)
"`Ext^{n₀}(_, S.X₃) = 0`" hypothesis.

**Proof structure**: by `HasInjectiveDimensionLT.subsingleton` applied to
`S.X₂` injective at degree `n₀ + 1 ≥ 2`, `Abelian.Ext X S.X₂ (n₀ + 1)` is
subsingleton, so the LES bracket `Ext X S.X₃ n₀ →ᵟ Ext X S.X₁ (n₀+1) →
Ext X S.X₂ (n₀+1)` makes the connecting morphism δ surjective.
Combined with the source `Ext X S.X₃ n₀ = 0`, the conclusion follows.
Used in the `i ≥ 2` case of `Scheme.HModule_flasque_eq_zero`. -/
theorem ext_succ_eq_zero_of_injective_of_lower_zero
    {C : Type v} [Category.{u} C] [Abelian C] [HasExt C]
    (X : C) {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    {n₀ : ℕ} (h_n₀ : 1 ≤ n₀)
    (hX₃ : ∀ y : Abelian.Ext X S.X₃ n₀, y = 0)
    (x₁ : Abelian.Ext X S.X₁ (n₀ + 1)) : x₁ = 0 := by
  have hinj_subs : Subsingleton (Abelian.Ext X S.X₂ (n₀ + 1)) :=
    HasInjectiveDimensionLT.subsingleton S.X₂ 1 (n₀ + 1) (by omega) _
  have hker : x₁.comp (Abelian.Ext.mk₀ S.f)
      (show (n₀ + 1) + 0 = (n₀ + 1) by omega) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x₃, hx₃⟩ :=
    Abelian.Ext.covariant_sequence_exact₁ X hS x₁ hker (rfl : n₀ + 1 = n₀ + 1)
  rw [hX₃ x₃] at hx₃
  rw [← hx₃, Abelian.Ext.zero_comp]

/-! ### iter-194 Lane H substrate: forget₂ infrastructure for the
Hartshorne II.1.16(b) bridge

The two helpers below set up the `forget₂ (ModuleCat kbar) AddCommGrpCat`
bridge that lets the project's `Scheme.IsFlasque` data feed into
Mathlib's `TopCat.Sheaf.IsFlasque.epi_of_shortExact` lemma.

The bridge is **structural**: `sheafCompose J (forget₂ ModuleCat AddCommGrpCat)`
is additive (hence preserves zero morphisms) and is a functor between
the corresponding sheaf categories. Its action on a sheaf
`F : Sheaf J (ModuleCat kbar)` produces an `AddCommGrpCat`-valued
sheaf whose section-level data is the underlying additive group of
the original — so `Function.Surjective` of section-level maps transfers
trivially across the bridge.

The remaining iter-194+ work is to lift `S.ShortExact` (at the
`ModuleCat kbar` level) to a corresponding `S.ShortExact` after
`sheafCompose forget₂` — the structural skeleton is in place; what's
missing is either `(sheafCompose forget₂).PreservesFiniteLimits` +
`PreservesFiniteColimits` instances (cleanest) or a direct port of
Mathlib's Zorn proof (~150-200 LOC). -/

/-- Additive instance for `sheafCompose J F` when `F` is additive.
Lets us discharge `PreservesZeroMorphisms` for the
`sheafCompose (forget₂ ModuleCat AddCommGrpCat)` functor. -/
instance sheafCompose_additive {C : Type*} [CategoryTheory.Category C]
    (J : CategoryTheory.GrothendieckTopology C)
    {A B : Type*} [CategoryTheory.Category A] [CategoryTheory.Category B]
    [CategoryTheory.Preadditive A] [CategoryTheory.Preadditive B]
    (F : A ⥤ B) [F.Additive] [J.HasSheafCompose F] :
    (CategoryTheory.sheafCompose J F).Additive where
  map_add := by
    intro X Y f g
    apply (CategoryTheory.sheafToPresheaf J B).map_injective
    change CategoryTheory.Functor.whiskerRight (f + g).hom F =
      CategoryTheory.Functor.whiskerRight f.hom F +
      CategoryTheory.Functor.whiskerRight g.hom F
    ext c
    simp
    rfl

/-- `PreservesZeroMorphisms` instance for `sheafCompose J F` when `F`
is additive (derived from the `Additive` instance above). -/
instance sheafCompose_preservesZero {C : Type*} [CategoryTheory.Category C]
    (J : CategoryTheory.GrothendieckTopology C)
    {A B : Type*} [CategoryTheory.Category A] [CategoryTheory.Category B]
    [CategoryTheory.Preadditive A] [CategoryTheory.Preadditive B]
    (F : A ⥤ B) [F.Additive] [J.HasSheafCompose F] :
    (CategoryTheory.sheafCompose J F).PreservesZeroMorphisms :=
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive _

/-- **iter-195 Lane H prover dispatch — single helper for SAb.Exact closure.**
`PreservesFiniteLimits` instance for `sheafCompose J F` when `F` preserves
finite limits, `A` and `B` are abelian and have finite limits, and the
sheaf categories have finite limits.

The proof uses the canonical factorisation
`sheafCompose J F ⋙ sheafToPresheaf J B = sheafToPresheaf J A ⋙ (whiskeringRight _ _ _).obj F`
(by `rfl`): the right side preserves finite limits (each factor does), and
`sheafToPresheaf J B` reflects them (it is fully faithful, hence reflects isos),
so `sheafCompose J F` does too.

This is the single helper that closes the `SAb.Exact` gap in
`Scheme.IsFlasque.shortExact_app_surjective`: by
`Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`, a
finite-limit-preserving additive functor between abelian categories takes
short exact sequences to exact short complexes. -/
instance sheafCompose_preservesFiniteLimits
    {C : Type*} [CategoryTheory.Category C]
    (J : CategoryTheory.GrothendieckTopology C)
    {A B : Type*} [CategoryTheory.Category A] [CategoryTheory.Category B]
    [CategoryTheory.Limits.HasFiniteLimits A]
    [CategoryTheory.Limits.HasFiniteLimits B]
    (F : A ⥤ B) [CategoryTheory.Limits.PreservesFiniteLimits F]
    [J.HasSheafCompose F] :
    CategoryTheory.Limits.PreservesFiniteLimits
      (CategoryTheory.sheafCompose J F) := by
  have heq :
    (CategoryTheory.sheafCompose J F ⋙ CategoryTheory.sheafToPresheaf J B) =
      (CategoryTheory.sheafToPresheaf J A ⋙
        (CategoryTheory.Functor.whiskeringRight _ _ _).obj F) := rfl
  haveI hcomp : CategoryTheory.Limits.PreservesFiniteLimits
      (CategoryTheory.sheafCompose J F ⋙ CategoryTheory.sheafToPresheaf J B) := by
    rw [heq]
    refine ⟨fun K _ _ => ?_⟩
    infer_instance
  exact CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves _
    (CategoryTheory.sheafToPresheaf J B)

/-- **`Scheme.IsFlasque` transfers to `TopCat.Sheaf.IsFlasque` under
`sheafCompose forget₂`** (axiom-clean structural helper).

The forget₂ functor `ModuleCat kbar → AddCommGrpCat` is faithful and
preserves the underlying function of every morphism. So
`Function.Surjective` of the underlying section-level restriction map
transfers across to `Epi` in `AddCommGrpCat` (via
`AddCommGrpCat.epi_iff_surjective`), and `Scheme.IsFlasque F` (which
says all restrictions are sectionwise surjective) directly produces
the `TopCat.Sheaf.IsFlasque` (which says all restrictions are epi). -/
theorem Scheme.IsFlasque.toAddCommGrpCat
    {kbar : Type u} [Field kbar] {X : TopCat.{u}}
    {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)}
    (hF : Scheme.IsFlasque F) :
    TopCat.Sheaf.IsFlasque
      ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
        (CategoryTheory.forget₂ (ModuleCat.{u} kbar) AddCommGrpCat.{u})).obj F) := by
  refine ⟨?_⟩
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  -- `i : U ⟶ V` in `(Opens X)ᵒᵖ` corresponds to `V.unop ≤ U.unop` in `Opens X`.
  have hle : V.unop ≤ U.unop := leOfHom i.unop
  obtain ⟨x, hx⟩ := hF hle y
  exact ⟨x, hx⟩

/-- **Hartshorne II.1, Exercise 1.16(b)** (sections form): the
sheaf-morphism `S.g` is sectionwise-surjective on a short exact sequence
whose leftmost sheaf is flasque.

For a sheaf-level short exact sequence
`0 → S.X₁ → S.X₂ → S.X₃ → 0` in `Sheaf (Opens.grothendieckTopology X)
(ModuleCat kbar)` with `S.X₁` flasque, the section-level map
`(S.g.val.app (op U)).hom : S.X₂.val.obj (op U) → S.X₃.val.obj (op U)`
is surjective for every open `U`.

**Proof sketch** (Hartshorne II.1 Ex 1.16(b), Zorn's lemma):
Let `t ∈ S.X₃.val.obj (op U)`. Consider pairs `(V, s)` where `V ⊆ U` is
open and `s ∈ S.X₂.val.obj (op V)` restricts to `t|_V`. Order by
extension. Any chain has an upper bound (sheaf gluing condition on
`S.X₂`). By Zorn's lemma, a maximal element `(V₀, s₀)` exists. Suppose
`V₀ ≠ U`. Pick `x ∈ U \ V₀`. Stalkwise, `S.X₂_x → S.X₃_x` is surjective
(SES in the abelian sheaf category preserves stalks). So in some
neighborhood `W` of `x` (after shrinking), there is
`s'_W ∈ S.X₂.val.obj (op W)` with image `t|_W`. On `V₀ ∩ W`,
`s₀ - s'_W` lies in `S.X₁.val.obj (op (V₀ ∩ W))` (since both map to
`t|_{V₀∩W}`). Use flasqueness of `S.X₁` to extend the difference to
`α ∈ S.X₁.val.obj (op W)`. Set `s'' := s'_W + α`. Then `s''` agrees with
`s₀` on `V₀ ∩ W`. By sheaf gluing on `S.X₂`, get a unique
`s''' ∈ S.X₂.val.obj (op (V₀ ∪ W))` extending both. This contradicts
maximality. Hence `V₀ = U`.

**iter-194 Lane H prover dispatch** — body closed via the **forget₂**
trick: convert the project-side `Scheme.IsFlasque` data to Mathlib's
`TopCat.Sheaf.IsFlasque` predicate (on `AddCommGrpCat`-valued sheaves)
via the `sheafCompose (Opens.grothendieckTopology X) (forget₂
(ModuleCat kbar) AddCommGrpCat)` functor, then invoke Mathlib's
`TopCat.Sheaf.IsFlasque.epi_of_shortExact` which is exactly this lemma
at the `AddCommGrpCat`-valued sheaf level. The underlying function of
the section-level morphism is the same before and after `forget₂`, so
`Function.Surjective` at the `ModuleCat kbar` level transfers from
`Epi` at the `AddCommGrpCat` level via `ModuleCat.epi_iff_surjective`
respectively `AddCommGrpCat.epi_iff_surjective`. Blueprint reference:
out-of-scope subsection of `thm:H1_vanishing_flasque` (the
Hartshorne II.1 Ex 1.16(b) input). -/
theorem Scheme.IsFlasque.shortExact_app_surjective
    {kbar : Type u} [Field kbar] {X : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)]
    {S : CategoryTheory.ShortComplex
      (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar))}
    (hS : S.ShortExact)
    (hF : Scheme.IsFlasque S.X₁)
    (U : TopologicalSpace.Opens X) :
    Function.Surjective ((S.g.hom.app (Opposite.op U)).hom) := by
  -- Set up the forget₂ functor at the sheaf level.
  set Fforget := CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ (ModuleCat.{u} kbar) AddCommGrpCat.{u}) with hFforget
  -- Build the AddCommGrpCat-valued ShortComplex via `S.map Fforget`.
  -- (Lean accepts this because `Fforget` has `PreservesZeroMorphisms` via the
  -- `sheafCompose_preservesZero` instance above.)
  set SAb : CategoryTheory.ShortComplex
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    S.map Fforget with hSAb
  -- The IsFlasque hypothesis transfers across `forget₂`.
  haveI : TopCat.Sheaf.IsFlasque SAb.X₁ := hF.toAddCommGrpCat
  -- Mathlib's `IsFlasque.epi_of_shortExact` applies once we exhibit
  -- `SAb.ShortExact`. We decompose into its three components.
  -- (a) `Mono SAb.f` — provable axiom-clean using
  --     `Sheaf.Hom.mono_of_presheaf_mono` + `NatTrans.mono_of_mono_app`
  --     (since `forget₂` preserves underlying-function-level mono).
  -- (b) `Epi SAb.g` — provable axiom-clean using
  --     `Sheaf.isLocallySurjective_iff_epi'` + the fact that
  --     `IsLocallySurjective` only depends on underlying types (so transfers
  --     across `forget₂`).
  -- (c) `SAb.Exact` — the remaining gap. Requires
  --     `(sheafCompose forget₂).PreservesHomology` (specifically
  --     preservation of kernels and cokernels in the sheaf category).
  haveI hMono_SAb_f : CategoryTheory.Mono SAb.f := by
    haveI : CategoryTheory.Mono S.f := hS.mono_f
    haveI hmono : CategoryTheory.Mono (Fforget.map S.f).hom := by
      change CategoryTheory.Mono
        (CategoryTheory.Functor.whiskerRight S.f.hom
          (CategoryTheory.forget₂ (ModuleCat.{u} kbar) AddCommGrpCat.{u}))
      apply CategoryTheory.NatTrans.mono_of_mono_app
    change CategoryTheory.Mono (Fforget.map S.f)
    exact CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono _ _ _
  haveI hEpi_SAb_g : CategoryTheory.Epi SAb.g := by
    haveI : CategoryTheory.Epi S.g := hS.epi_g
    change CategoryTheory.Epi (Fforget.map S.g)
    rw [← CategoryTheory.Sheaf.isLocallySurjective_iff_epi']
    haveI hf : CategoryTheory.Sheaf.IsLocallySurjective S.g := by
      rw [CategoryTheory.Sheaf.isLocallySurjective_iff_epi']
      infer_instance
    refine ⟨?_⟩
    intro V s
    exact @CategoryTheory.Presheaf.imageSieve_mem _ _ _ _ _ _ _ _ _ _ _ S.g.hom hf _ s
  have hSAb_exact : SAb.ShortExact :=
    -- **iter-195 Lane H prover dispatch — closed via single helper.**
    -- Use `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`
    -- in the forward direction: since `Fforget` preserves finite limits
    -- (helper `sheafCompose_preservesFiniteLimits` above) and is additive
    -- (helper `sheafCompose_additive`), it sends any `ShortExact` complex
    -- to an exact short complex.
    { exact := ((CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
        Fforget).mp inferInstance S hS).1
      mono_f := hMono_SAb_f
      epi_g := hEpi_SAb_g }
  -- Apply Mathlib's lemma to get `Epi (SAb.g.hom.app (op U))`.
  haveI : CategoryTheory.Epi (SAb.g.hom.app (Opposite.op U)) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact hSAb_exact
  -- Convert Epi to surjectivity at the AddCommGrpCat level.
  have hSurj_Ab : Function.Surjective ((SAb.g.hom.app (Opposite.op U))) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  -- The section-level morphism `SAb.g.hom.app (op U)` is precisely the
  -- image of `S.g.hom.app (op U)` under `forget₂`. The underlying function
  -- is the same — `forget₂ ModuleCat AddCommGrpCat` preserves underlying types.
  -- So surjectivity transfers.
  intro y
  obtain ⟨x, hx⟩ := hSurj_Ab y
  exact ⟨x, hx⟩

/-- **Hartshorne II.1, Exercise 1.16(c)** (project-side cokernel
inheritance, axiom-clean):

The cokernel of a flasque-by-flasque short exact sequence is flasque.

For a sheaf-level short exact sequence
`0 → S.X₁ → S.X₂ → S.X₃ → 0` in `Sheaf (Opens.grothendieckTopology X)
(ModuleCat kbar)` with both `S.X₁` and `S.X₂` flasque, `S.X₃` is also
flasque. The hypothesis `h_b` packages the Hartshorne II.1 Ex 1.16(b)
sections-surjectivity input as a parameter (rather than calling
`Scheme.IsFlasque.shortExact_app_surjective` directly), keeping this
lemma's axiom-set clean — `sorryAx` traces only through the consumer
site, not through this declaration.

**Proof**: for `V ≤ U`, given `t ∈ S.X₃.val.obj (op V)`, lift via `h_b` at
`V` to `t̃ ∈ S.X₂.val.obj (op V)`, extend via flasqueness of `S.X₂` from
`V` to `U` getting `T̃ ∈ S.X₂.val.obj (op U)`, then set
`T := S.g.val.app (op U) T̃ ∈ S.X₃.val.obj (op U)`. The restriction of
`T` to `V` equals `t` by naturality of `S.g.val` and the lift property of
`t̃`.

**iter-193 Lane H prover dispatch** — closed axiom-clean. Used in the
`i ≥ 2` case of `HModule_flasque_eq_zero` to inherit flasqueness on the
quotient `G = cokernel(Injective.ι F)`. Blueprint reference: substrate
input in proof of `thm:H1_vanishing_flasque`. -/
theorem Scheme.IsFlasque.cokernel_of_shortExact_flasque_flasque
    {kbar : Type u} [Field kbar] {X : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)]
    {S : CategoryTheory.ShortComplex
      (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar))}
    (hI : Scheme.IsFlasque S.X₂)
    (h_b : ∀ (U : TopologicalSpace.Opens X),
      Function.Surjective ((S.g.hom.app (Opposite.op U)).hom)) :
    Scheme.IsFlasque S.X₃ := by
  intro U V hVU t
  obtain ⟨tLift, htLift⟩ := h_b V t
  obtain ⟨TExt, hTExt⟩ := hI hVU tLift
  refine ⟨(S.g.hom.app (Opposite.op U)).hom TExt, ?_⟩
  have nat := S.g.hom.naturality_apply (homOfLE hVU).op TExt
  -- nat : (S.g.hom.app (op V)).hom ((S.X₂.val.map _).hom TExt) =
  --       (S.X₃.val.map _).hom ((S.g.hom.app (op U)).hom TExt)
  rw [hTExt, htLift] at nat
  exact nat.symm

/-- **Hartshorne III, Lemma 2.4** (Tier-3 typed sorry): every injective
sheaf of `kbar`-modules on `X` is flasque.

For an injective sheaf `I` of `kbar`-modules on `X`, `I` is flasque as a
sheaf. The classical proof uses the extension-by-zero `j_!` functor: for
`V ⊆ U` open, the open immersion `j_V : V ↪ X` gives `j_{V!}(O_V)
↪ j_{U!}(O_U)`, and `Hom(j_{U!}(O_U), I) → Hom(j_{V!}(O_V), I)` is
surjective by injectivity of `I`. Translating via the
`j_{(-)!}` ⊣ `j_{(-)}*` adjunction (or the equivalent presheaf form for
the constant ring sheaf `kbar`), this gives surjectivity of `I(U) → I(V)`.

**Tier-3 typed sorry** — requires the `j_!` extension-by-zero
construction (Mathlib snapshot `b80f227` does not ship `j_!` for sheaves
of modules at this generality); estimate ~100-150 LOC. Scheduled iter-194+.
Blueprint reference: substrate input in proof of
`thm:H1_vanishing_flasque`. -/
theorem Scheme.IsFlasque.injective_flasque
    {kbar : Type u} [Field kbar] {X : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)]
    (I : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar))
    [Injective I] : Scheme.IsFlasque I := by
  sorry

/-- **Auxiliary subsingleton lemma for `HModule_flasque_eq_zero`**
(iter-193 Lane H prover dispatch).

For a flasque sheaf `F` of `kbar`-modules on `X` and any `n : ℕ`, the
`(n+1)`-th derived global-sections cohomology `HModule kbar F (n+1)` is
subsingleton (i.e., has at most one element). This statement is the
strong-induction-on-`n` carrier of the main theorem
`HModule_flasque_eq_zero`: the `F`-generalised quantifier inside the
`induction` block lets the inductive step apply the IH on the flasque
quotient sheaf at one lower degree. Once subsingleton is established,
`Module.finrank_zero_of_subsingleton` gives the `finrank = 0` conclusion
in the main statement. -/
private theorem Scheme.HModule_flasque_subsingleton_aux
    {kbar : Type u} [Field kbar] {X : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)]
    [HasExt (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar))]
    (n : ℕ) :
    ∀ {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)},
      Scheme.IsFlasque F → Subsingleton (Scheme.HModule kbar F (n + 1)) := by
  induction n with
  | zero =>
    intro F hF
    refine ⟨fun x y => ?_⟩
    -- i = 1 case: use ext_one_eq_zero_of_hom_surjective_of_injective on the
    -- canonical injective SES `0 → F → Injective.under F → cokernel → 0`.
    have hSES := Scheme.injectiveSES_shortExact F
    -- Injective.under F is injective by Mathlib's instance.
    have hI_inj : Injective (Scheme.injectiveSES F).X₂ := Injective.injective_under F
    -- 1.16(b) at U = ⊤ gives section-level surjectivity, which we lift to
    -- Hom-from-(constantSheaf k)-surjectivity via the explicit `constantSheaf
    -- ⊣ (sheafSections at ⊤)` adjunction (`constantSheafAdj` with terminal
    -- `⊤ ∈ Opens X` via `Preorder.isTerminalTop`) and the rank-1 free
    -- structure of `ModuleCat.of kbar kbar` (a kbar-linear hom from `kbar`
    -- is determined by its image of `1`, with the inverse map
    -- `LinearMap.toSpanSingleton kbar _ s` for any chosen lift `s`).
    have hsurj : Function.Surjective
        (fun (f : (constantSheaf (Opens.grothendieckTopology X)
            (ModuleCat.{u} kbar)).obj (ModuleCat.of kbar kbar) ⟶
            (Scheme.injectiveSES F).X₂) => f ≫ (Scheme.injectiveSES F).g) := by
      intro g
      -- Set up the adjunction at the terminal `⊤ ∈ Opens X`.
      let hT : Limits.IsTerminal (⊤ : TopologicalSpace.Opens X) :=
        Preorder.isTerminalTop (TopologicalSpace.Opens X)
      let adj := constantSheafAdj (Opens.grothendieckTopology X)
        (ModuleCat.{u} kbar) hT
      -- 1.16(b) at U = ⊤ gives section-level surjectivity.
      have h_b_top : Function.Surjective
          (((Scheme.injectiveSES F).g.hom.app
            (Opposite.op (⊤ : TopologicalSpace.Opens X))).hom) :=
        Scheme.IsFlasque.shortExact_app_surjective hSES hF ⊤
      -- Convert `g` to a section-level morphism via `adj.homEquiv`.
      let g_sec : ModuleCat.of kbar kbar ⟶
          (Scheme.injectiveSES F).X₃.val.obj
            (Opposite.op (⊤ : TopologicalSpace.Opens X)) :=
        adj.homEquiv _ _ g
      -- Pick the value of `g_sec` at `1 : kbar`.
      let s₃ : (Scheme.injectiveSES F).X₃.val.obj
          (Opposite.op (⊤ : TopologicalSpace.Opens X)) := g_sec.hom 1
      -- Apply 1.16(b) at ⊤ to get a lift in `X₂`.
      obtain ⟨s₂, hs₂⟩ := h_b_top s₃
      -- Construct the section-level lift `f_sec : kbar ⟶ X₂.val.obj (op ⊤)`.
      let f_sec : ModuleCat.of kbar kbar ⟶
          (Scheme.injectiveSES F).X₂.val.obj
            (Opposite.op (⊤ : TopologicalSpace.Opens X)) :=
        ModuleCat.ofHom (LinearMap.toSpanSingleton kbar _ s₂)
      -- Lift `f_sec` back to a sheaf-level morphism via `adj.homEquiv.symm`.
      refine ⟨(adj.homEquiv _ _).symm f_sec, ?_⟩
      -- Verify `(adj.homEquiv.symm f_sec) ≫ S.g = g` by applying `adj.homEquiv`.
      apply (adj.homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
      change f_sec ≫ ((sheafSections (Opens.grothendieckTopology X)
        (ModuleCat.{u} kbar)).obj (Opposite.op ⊤)).map (Scheme.injectiveSES F).g = g_sec
      -- Verify the section-level equation at the linear map level.
      -- Two `kbar`-linear maps from `kbar` agree iff they agree at `1`.
      apply ModuleCat.hom_ext
      ext
      -- Goal (post `LinearMap.ext_ring`): both sides applied at `1`.
      change ((Scheme.injectiveSES F).g.hom.app (Opposite.op ⊤)).hom
          ((LinearMap.toSpanSingleton kbar _ s₂) 1) = g_sec.hom 1
      rw [LinearMap.toSpanSingleton_apply_one]
      exact hs₂
    rw [ext_one_eq_zero_of_hom_surjective_of_injective _ hSES hsurj x,
        ext_one_eq_zero_of_hom_surjective_of_injective _ hSES hsurj y]
  | succ m ih =>
    intro F hF
    refine ⟨fun x y => ?_⟩
    -- i = m + 2, m + 1 ≥ 1. Use the LES iso via the canonical injective SES,
    -- with the flasque quotient G inheriting flasqueness from F + Injective.under F
    -- (Hartshorne III Lemma 2.4 + II Ex 1.16(c)). Reduce to IH at degree m + 1.
    have hSES := Scheme.injectiveSES_shortExact F
    have hI_inj : Injective (Scheme.injectiveSES F).X₂ := Injective.injective_under F
    have hI_flasque : Scheme.IsFlasque (Scheme.injectiveSES F).X₂ :=
      Scheme.IsFlasque.injective_flasque _
    have h_b : ∀ U, Function.Surjective
        (((Scheme.injectiveSES F).g.hom.app (Opposite.op U)).hom) :=
      fun U => Scheme.IsFlasque.shortExact_app_surjective hSES hF U
    have hG_flasque : Scheme.IsFlasque (Scheme.injectiveSES F).X₃ :=
      Scheme.IsFlasque.cokernel_of_shortExact_flasque_flasque hI_flasque h_b
    have hG_sub : Subsingleton (Scheme.HModule kbar (Scheme.injectiveSES F).X₃ (m + 1)) :=
      ih hG_flasque
    have hX₃_zero :
        ∀ y : Abelian.Ext
            ((constantSheaf (Opens.grothendieckTopology X)
              (ModuleCat.{u} kbar)).obj (ModuleCat.of kbar kbar))
            (Scheme.injectiveSES F).X₃ (m + 1), y = 0 :=
      fun y => Subsingleton.elim (α := Scheme.HModule kbar (Scheme.injectiveSES F).X₃ (m + 1)) y 0
    have h_n₀ : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le _)
    rw [ext_succ_eq_zero_of_injective_of_lower_zero _ hSES h_n₀ hX₃_zero x,
        ext_succ_eq_zero_of_injective_of_lower_zero _ hSES h_n₀ hX₃_zero y]

/-- **Flasque sheaves have vanishing higher cohomology** (Hartshorne
III.2, Proposition 2.5).

For a topological space `X` and a flasque sheaf `F` of `kbar`-modules on
`X`, the `kbar`-flavoured derived global-sections cohomology
`HModule kbar F i` is the zero `kbar`-module for every `i ≥ 1`. In
particular, `dim_{kbar} HModule kbar F 1 = 0`.

The proof structure mirrors Hartshorne III §2 verbatim: embed `F` into
an injective `I` of the abelian sheaf category, form the quotient short
exact sequence `0 → F → I → G → 0` (Mathlib: `Scheme.injectiveSES`,
axiom-clean), observe that `G` inherits flasqueness from `F` and `I`
(the latter by Hartshorne III Lemma 2.4), read off the short exact
sequence on global sections from the flasque input
(Hartshorne II Ex. 1.16(b)), and apply the long exact sequence
(`Abelian.Ext.covariant_sequence_exact₁`) to get `HModule kbar F 1 = 0`
and a reduction `HModule kbar F i ≅ HModule kbar G (i - 1)` for `i ≥ 2`;
iteration closes the higher-degree cases.

**iter-193 Lane H prover dispatch** — body fully closed structurally;
sorries are isolated to two named substrate helpers
(`shortExact_app_surjective` and `injective_flasque`, both Tier-3).
The proof decomposes cleanly into the two cases via the auxiliary
subsingleton lemma `Scheme.HModule_flasque_subsingleton_aux`:
* `i = 1`: invoke `ext_one_eq_zero_of_hom_surjective_of_injective` on the
  `injectiveSES F` short-exact data, supplying the Hartshorne II Ex 1.16(b)
  input. The Hom-from-constant-sheaf surjectivity is derived axiom-clean
  from `IsFlasque.shortExact_app_surjective` at `U = ⊤` via the explicit
  `constantSheafAdj` (at terminal `⊤ ∈ Opens X` via
  `Preorder.isTerminalTop`) + the rank-1 free structure of
  `ModuleCat.of kbar kbar` (`LinearMap.toSpanSingleton` lift).
* `i ≥ 2`: invoke `ext_succ_eq_zero_of_injective_of_lower_zero` on
  `injectiveSES F`, supplying `Subsingleton (HModule kbar G (i-1))` via the
  IH applied to the flasque quotient `G` (the latter via
  `IsFlasque.cokernel_of_shortExact_flasque_flasque` and
  `IsFlasque.injective_flasque`).

Blueprint reference: `thm:H1_vanishing_flasque`. -/
theorem Scheme.HModule_flasque_eq_zero
    {kbar : Type u} [Field kbar] {X : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)]
    [HasExt (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar))]
    {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} kbar)}
    (hF : Scheme.IsFlasque F) (i : ℕ) (hi : 1 ≤ i) :
    Module.finrank kbar (Scheme.HModule kbar F i) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, n + 1 = i := ⟨i - 1, by omega⟩
  have hsub : Subsingleton (Scheme.HModule kbar F (n + 1)) :=
    Scheme.HModule_flasque_subsingleton_aux n hF
  exact Module.finrank_zero_of_subsingleton

/-! ## §2. Skyscraper sheaves are flasque -/

/-! ### Project-local Mathlib supplement — Inner iso `skyscraperSheaf ≅ constantSheaf` on `PUnit`

The three definitions below (`alphaConstToSkyPUnit`, `betaSkyToConstPUnit`,
`alpha_beta_eq_toSheafify`) form the substrate of the **inner iso** for
`Scheme.skyscraperSheaf_eq_pushforward_const`. On the one-point space
`PUnit`, the constant sheaf at `A` agrees with the skyscraper sheaf at
`PUnit.unit` with value `A`: both have value `A` at the open `⊤` (since
`PUnit.unit ∈ ⊤`) and terminal value at the open `⊥` (by the sheaf
condition on the empty open).

The forward and inverse maps are built directly:
- `alphaConstToSkyPUnit` : `(Functor.const _).obj A → skyscraperPresheaf PUnit.unit A`
  — the obvious presheaf morphism: `eqToHom` at non-empty opens, terminal
  map at `⊥`.
- `betaSkyToConstPUnit` : `skyscraperPresheaf PUnit.unit A → ((constantSheaf J).obj A).val`
  — the inverse: `eqToHom ≫ toSheafify` at non-empty opens, terminal
  map at `⊥`.
- `alpha_beta_eq_toSheafify` : the composition collapses to the
  sheafification unit, the key identity that makes both iso directions
  follow via `toSheafify_sheafifyLift` and `sheafify_hom_ext`.

Iter-197 Lane H closure: replaces the iter-196 `sorry` at the inner iso
of `skyscraperSheaf_eq_pushforward_const`. The full iso is consumed
inline in that theorem below (see Step 2). -/

/-- Presheaf morphism from the constant presheaf at `A` to the
skyscraper presheaf at `PUnit.unit` with value `A`. Used as input to
`sheafifyLift` to build the forward direction of the inner iso. -/
noncomputable def alphaConstToSkyPUnit
    {kbar : Type u} [Field kbar]
    [∀ U : TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}),
      Decidable (PUnit.unit ∈ U)]
    (A : ModuleCat.{u} kbar) :
    (CategoryTheory.Functor.const
        ((TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}))ᵒᵖ)).obj A ⟶
      skyscraperPresheaf (C := ModuleCat.{u} kbar)
        (X := TopCat.of PUnit.{u + 1}) (PUnit.unit : PUnit.{u + 1}) A where
  app U := if h : PUnit.unit ∈ U.unop then eqToHom (by simp [skyscraperPresheaf, h])
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality {U V} i := by
    simp only [CategoryTheory.Functor.const_obj_obj, skyscraperPresheaf_obj,
      CategoryTheory.Functor.const_obj_map, Category.id_comp]
    by_cases hV : PUnit.unit ∈ V.unop
    · have hU : PUnit.unit ∈ U.unop := i.unop.le hV
      simp only [skyscraperPresheaf_map, dif_pos hV, dif_pos hU, eqToHom_trans]
    · apply ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext

/-- Presheaf morphism from the skyscraper presheaf at `PUnit.unit` with
value `A` to the underlying presheaf of the constant sheaf at `A` on
`PUnit`. The inverse of `alphaConstToSkyPUnit` modulo sheafification. -/
noncomputable def betaSkyToConstPUnit
    {kbar : Type u} [Field kbar]
    [∀ U : TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}),
      Decidable (PUnit.unit ∈ U)]
    (A : ModuleCat.{u} kbar) :
    skyscraperPresheaf (C := ModuleCat.{u} kbar) PUnit.unit A ⟶
      ((constantSheaf (Opens.grothendieckTopology
            (TopCat.of PUnit.{u + 1}))
          (ModuleCat.{u} kbar)).obj A).val := by
  let J := Opens.grothendieckTopology (TopCat.of PUnit.{u + 1})
  let D := ModuleCat.{u} kbar
  let CS := (constantSheaf J D).obj A
  refine
    { app := fun U => ?_
      naturality := fun {U V} i => ?_ }
  · by_cases h : PUnit.unit ∈ U.unop
    · exact eqToHom (by simp [skyscraperPresheaf, h]) ≫
        (toSheafify J ((CategoryTheory.Functor.const
            ((TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}))ᵒᵖ)).obj A)).app U
    · have hU : U.unop = ⊥ := by
        rcases U.unop.eq_bot_or_top with hbot | htop
        · exact hbot
        · exfalso; apply h; rw [htop]; trivial
      exact (TopCat.Sheaf.isTerminalOfEqEmpty CS hU).from _
  · by_cases hV : PUnit.unit ∈ V.unop
    case neg =>
      have hVbot : V.unop = ⊥ := by
        rcases V.unop.eq_bot_or_top with hbot | htop
        · exact hbot
        · exfalso; apply hV; rw [htop]; trivial
      exact (TopCat.Sheaf.isTerminalOfEqEmpty CS hVbot).hom_ext _ _
    case pos =>
      have hU : PUnit.unit ∈ U.unop := i.unop.le hV
      simp only [dif_pos hV, dif_pos hU, skyscraperPresheaf_map]
      have hnat := (toSheafify J
        ((CategoryTheory.Functor.const
            ((TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}))ᵒᵖ)).obj A)).naturality i
      simp only [CategoryTheory.Functor.const_obj_obj,
        CategoryTheory.Functor.const_obj_map, Category.id_comp] at hnat
      rw [hnat]
      simp [eqToHom_trans_assoc]
      rfl

/-- Composition lemma: `alphaConstToSkyPUnit ≫ betaSkyToConstPUnit` equals
the sheafification unit. This is the key identity that makes both
directions of the inner iso commute. -/
lemma alphaConstToSkyPUnit_comp_betaSkyToConstPUnit_eq_toSheafify
    {kbar : Type u} [Field kbar]
    [∀ U : TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}),
      Decidable (PUnit.unit ∈ U)]
    (A : ModuleCat.{u} kbar) :
    alphaConstToSkyPUnit A ≫ betaSkyToConstPUnit A =
      toSheafify (Opens.grothendieckTopology
          (TopCat.of PUnit.{u + 1}))
        ((CategoryTheory.Functor.const
            ((TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}))ᵒᵖ)).obj A) := by
  apply CategoryTheory.NatTrans.ext
  funext U
  by_cases h : PUnit.unit ∈ U.unop
  · change (alphaConstToSkyPUnit A).app U ≫ (betaSkyToConstPUnit A).app U = _
    simp only [alphaConstToSkyPUnit, betaSkyToConstPUnit, dif_pos h]
    simp [eqToHom_trans_assoc]
  · have hU : U.unop = ⊥ := by
      rcases U.unop.eq_bot_or_top with hbot | htop
      · exact hbot
      · exfalso; apply h; rw [htop]; trivial
    apply (TopCat.Sheaf.isTerminalOfEqEmpty
      ((constantSheaf (Opens.grothendieckTopology
          (TopCat.of PUnit.{u + 1}))
        (ModuleCat.{u} kbar)).obj A) hU).hom_ext

/-- **Inner iso**: on the one-point space `PUnit`, the skyscraper sheaf
at `PUnit.unit` with value `A` is isomorphic to the constant sheaf at
`A`. This closes the inner-iso gap of
`Scheme.skyscraperSheaf_eq_pushforward_const` below. -/
noncomputable def Scheme.skyscraperSheaf_iso_constantSheaf_punit
    (kbar : Type u) [Field kbar]
    [∀ U : TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}),
      Decidable (PUnit.unit ∈ U)]
    (A : ModuleCat.{u} kbar) :
    skyscraperSheaf (C := ModuleCat.{u} kbar)
        (X := TopCat.of PUnit.{u + 1}) (PUnit.unit : PUnit.{u + 1}) A ≅
      (constantSheaf (Opens.grothendieckTopology
          (TopCat.of PUnit.{u + 1}))
        (ModuleCat.{u} kbar)).obj A := by
  refine
    { hom := ⟨betaSkyToConstPUnit A⟩
      inv := ⟨sheafifyLift _ (alphaConstToSkyPUnit A)
        (skyscraperPresheaf_isSheaf _ _)⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply CategoryTheory.Sheaf.hom_ext
    have key : betaSkyToConstPUnit A ≫ sheafifyLift
        (Opens.grothendieckTopology (TopCat.of PUnit.{u + 1}))
        (alphaConstToSkyPUnit A) (skyscraperPresheaf_isSheaf _ _) = 𝟙 _ := by
      apply CategoryTheory.NatTrans.ext
      funext U
      by_cases h : PUnit.unit ∈ U.unop
      · change (betaSkyToConstPUnit A).app U ≫
          (sheafifyLift _ (alphaConstToSkyPUnit A) _).app U = _
        have htsl := toSheafify_sheafifyLift
          (Opens.grothendieckTopology (TopCat.of PUnit.{u + 1}))
          (alphaConstToSkyPUnit A) (skyscraperPresheaf_isSheaf _ _)
        simp only [betaSkyToConstPUnit, dif_pos h]
        change (eqToHom _ ≫ (toSheafify
            (Opens.grothendieckTopology (TopCat.of PUnit.{u + 1}))
            _).app U) ≫
          (sheafifyLift (Opens.grothendieckTopology
              (TopCat.of PUnit.{u + 1}))
            (alphaConstToSkyPUnit A) (skyscraperPresheaf_isSheaf _ _)).app U = _
        rw [Category.assoc]
        rw [show (toSheafify
              (Opens.grothendieckTopology
                (TopCat.of PUnit.{u + 1}))
              ((CategoryTheory.Functor.const
                  ((TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}))ᵒᵖ)).obj A)).app U ≫
            (sheafifyLift (Opens.grothendieckTopology
                (TopCat.of PUnit.{u + 1}))
              (alphaConstToSkyPUnit A) (skyscraperPresheaf_isSheaf _ _)).app U =
            (alphaConstToSkyPUnit A).app U
            from congrFun (congrArg CategoryTheory.NatTrans.app htsl) U]
        simp only [alphaConstToSkyPUnit, dif_pos h, eqToHom_trans, eqToHom_refl]
        rfl
      · have hU : U.unop = ⊥ := by
          rcases U.unop.eq_bot_or_top with hbot | htop
          · exact hbot
          · exfalso; apply h; rw [htop]; trivial
        apply (TopCat.Sheaf.isTerminalOfEqEmpty
          (skyscraperSheaf (C := ModuleCat.{u} kbar)
            (X := TopCat.of PUnit.{u + 1}) (PUnit.unit : PUnit.{u + 1}) A) hU).hom_ext
    exact key
  · apply CategoryTheory.Sheaf.hom_ext
    change sheafifyLift _ (alphaConstToSkyPUnit A) _ ≫ betaSkyToConstPUnit A = 𝟙 _
    apply sheafify_hom_ext _ _ _
      ((constantSheaf (Opens.grothendieckTopology
          (TopCat.of PUnit.{u + 1}))
        (ModuleCat.{u} kbar)).obj A).property
    change toSheafify _ _ ≫ sheafifyLift _ (alphaConstToSkyPUnit A) _ ≫
        betaSkyToConstPUnit A = toSheafify _ _ ≫ 𝟙 _
    rw [← Category.assoc, toSheafify_sheafifyLift]
    change alphaConstToSkyPUnit A ≫ betaSkyToConstPUnit A = toSheafify
      (Opens.grothendieckTopology (TopCat.of PUnit.{u + 1}))
      ((CategoryTheory.Functor.const
          ((TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}))ᵒᵖ)).obj A) ≫ 𝟙 _
    rw [Category.comp_id]
    exact alphaConstToSkyPUnit_comp_betaSkyToConstPUnit_eq_toSheafify A

/-- **Skyscraper sheaf as pushforward of a constant sheaf** (Hartshorne
II.1, Exercise 1.17).

The closed-point skyscraper sheaf `skyscraperSheaf P A` on a topological
space `X` is naturally isomorphic to the pushforward, along the constant
map `PUnit → X` at `P`, of the constant sheaf with value `A` on
`PUnit`. The constant sheaf on `PUnit` is itself isomorphic to the
skyscraper sheaf at `PUnit.unit`, so this is the sheaf-level
counterpart of Mathlib's presheaf-level
`skyscraperPresheaf_eq_pushforward` (Mathlib snapshot `b80f227`
`Topology/Sheaves/Skyscraper.lean`).

For our usage on a curve, `PUnit` plays the role of `closure {P}`
(which on a Noetherian space with `P` closed is a singleton, hence
homeomorphic to `PUnit`).

**iter-196 Lane H prover attempt** — partial structural skeleton.
The proof composes two isos:
* **Outer**: `skyscraperSheaf P A ≅
  (TopCat.Sheaf.pushforward _ const).obj (skyscraperSheaf PUnit.unit A)`,
  obtained from Mathlib's presheaf-level `skyscraperPresheaf_eq_pushforward`
  (`Topology/Sheaves/Skyscraper.lean`) lifted to sheaves via `eqToIso` on
  the underlying presheaf equality; both sides are sheaves (the LHS by
  `skyscraperPresheaf_isSheaf`; the RHS by `pushforward_sheaf_of_sheaf`).
* **Inner**: `skyscraperSheaf PUnit.unit A ≅ (constantSheaf J_punit).obj A`
  as sheaves on `PUnit`. The forward direction is given by
  `constantSheafAdj.homEquiv.symm` applied to the canonical map
  `A → skyscraperSheaf PUnit.unit A.val.obj (op ⊤)` (which simplifies to
  `eqToHom (by simp [skyscraperPresheaf])` since `PUnit.unit ∈ ⊤`). The
  inverse direction requires showing `(constantSheaf J_punit).obj A.val.obj
  (op ⊤) ≅ A` (the adjunction-unit iso), then transporting via the
  sheaf-on-PUnit characterisation that sheaves are determined by their
  value at `⊤` (Mathlib's `isSheaf_on_punit_iff_isTerminal`).
The remaining gap is the inner iso, which needs ~50-80 LOC of explicit
pointwise iso construction on the two opens `⊥`, `⊤` of `PUnit`.
Blueprint reference: `lem:skyscraperSheaf_eq_pushforward`. -/
theorem Scheme.skyscraperSheaf_eq_pushforward_const
    (kbar : Type u) [Field kbar]
    {X : TopCat.{u}} (P : X)
    [∀ U : TopologicalSpace.Opens X, Decidable (P ∈ U)]
    [∀ U : TopologicalSpace.Opens (TopCat.of PUnit.{u + 1}),
      Decidable (PUnit.unit ∈ U)]
    (A : ModuleCat.{u} kbar) :
    Nonempty
      (skyscraperSheaf (C := ModuleCat.{u} kbar) P A ≅
        (TopCat.Sheaf.pushforward (ModuleCat.{u} kbar)
            (TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit.{u + 1}) P))).obj
          ((constantSheaf
              (Opens.grothendieckTopology (TopCat.of PUnit.{u + 1}))
              (ModuleCat.{u} kbar)).obj A)) := by
  refine ⟨?_⟩
  -- Step 1 (axiom-clean, below): outer sheaf-level equality
  --   skyscraperSheaf P A = pushforward_const (skyscraperSheaf PUnit.unit A)
  -- via `ObjectProperty.FullSubcategory.ext` on the underlying presheaf
  -- equality `skyscraperPresheaf_eq_pushforward` from Mathlib.
  have hsky_eq :
      skyscraperSheaf (C := ModuleCat.{u} kbar) P A =
        (TopCat.Sheaf.pushforward (ModuleCat.{u} kbar)
            (TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit.{u + 1}) P))).obj
          (skyscraperSheaf (C := ModuleCat.{u} kbar) PUnit.unit A) := by
    apply ObjectProperty.FullSubcategory.ext
    exact skyscraperPresheaf_eq_pushforward P A
  -- Step 2 (iter-197 Lane H closure): inner sheaf iso on PUnit
  --   skyscraperSheaf PUnit.unit A ≅ (constantSheaf J_punit).obj A
  -- Closed via `Scheme.skyscraperSheaf_iso_constantSheaf_punit` (above),
  -- built from the project-local presheaf morphisms `alphaConstToSkyPUnit`
  -- and `betaSkyToConstPUnit` and the composition identity
  -- `alphaConstToSkyPUnit_comp_betaSkyToConstPUnit_eq_toSheafify`.
  have hinner_iso :
      Nonempty (skyscraperSheaf (C := ModuleCat.{u} kbar) PUnit.unit A ≅
        (constantSheaf (Opens.grothendieckTopology (TopCat.of PUnit.{u + 1}))
          (ModuleCat.{u} kbar)).obj A) :=
    ⟨Scheme.skyscraperSheaf_iso_constantSheaf_punit kbar A⟩
  -- Step 3: compose. Push forward the inner iso along `const → P` and chain
  -- with the outer equality via `eqToIso`.
  let i_inner := Classical.choice hinner_iso
  exact (eqToIso hsky_eq).trans
    ((TopCat.Sheaf.pushforward (ModuleCat.{u} kbar)
        (TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit.{u + 1}) P))).mapIso
      i_inner)

/-- **Closure of the support point of a `PrimeDivisor` is irreducible**.

For any scheme `X` and any `P : X.PrimeDivisor`, the topological
closure of the singleton `{P.point}` is an irreducible subset of `X`.
This is a project-bespoke ancillary that holds in full generality: the
closure of any irreducible set in a topological space is irreducible,
and a singleton `{x}` is irreducible (it is nonempty and contains no
proper non-empty closed subsets).

**iter-191 Lane H prover dispatch** — closed via
`isIrreducible_singleton.closure`. Blueprint reference:
`lem:closedPoint_closure_irreducible`. -/
theorem Scheme.PrimeDivisor.closure_isIrreducible
    {X : Scheme.{u}} (P : X.PrimeDivisor) :
    IsIrreducible (closure ({P.point} : Set X)) :=
  isIrreducible_singleton.closure

/-- **The closed-point skyscraper sheaf is flasque**.

For a smooth proper geometrically irreducible curve `C / kbar` and a
prime divisor `P : C.left.PrimeDivisor` (equivalently, a closed point
on the curve), the closed-point skyscraper sheaf
`skyscraperSheaf P.point (ModuleCat.of kbar kbar)` is flasque as a
sheaf of `kbar`-modules on the underlying topological space of `C`.

The proof originally was planned to compose the four lemma-blocks of this
chapter (`skyscraperSheaf_eq_pushforward_const`,
`PrimeDivisor.closure_isIrreducible`, `IsFlasque.constant_of_irreducible`,
`IsFlasque.pushforward`). The iter-191 prover dispatch takes a more direct
route: unfold `skyscraperSheaf.val = skyscraperPresheaf`, then on the
`p ∈ V` branch the restriction map is an `eqToHom` (hence iso, hence
surjective in `ConcreteCategory`); on the `p ∉ V` branch the codomain is
the terminal object of `ModuleCat kbar`, which is the zero object, hence
`Subsingleton` on the underlying type. Either branch closes the
`Function.Surjective` obligation. This bypasses (3) and (5).

**iter-191 Lane H prover dispatch** — closed directly via
`skyscraperPresheaf_map`. Blueprint reference:
`lem:skyscraperSheaf_isFlasque`. -/
theorem Scheme.skyscraperSheaf_isFlasque
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (C : Over (Spec (.of kbar))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] [IsIntegral C.left]
    (P : C.left.PrimeDivisor)
    [∀ U : TopologicalSpace.Opens C.left, Decidable (P.point ∈ U)] :
    Scheme.IsFlasque
      (skyscraperSheaf (C := ModuleCat.{u} kbar) P.point
        (ModuleCat.of kbar kbar)) := by
  intro U V h
  change Function.Surjective
    (((skyscraperPresheaf P.point (ModuleCat.of kbar kbar)).map
      (homOfLE h).op).hom)
  by_cases hV : P.point ∈ V
  · -- restriction is `eqToHom`, hence an iso, hence surjective
    have heq : (skyscraperPresheaf P.point (ModuleCat.of kbar kbar)).obj
        (Opposite.op U) =
        (skyscraperPresheaf P.point (ModuleCat.of kbar kbar)).obj
        (Opposite.op V) := by
      simp [skyscraperPresheaf, h hV, hV]
    have hmap := skyscraperPresheaf_map P.point (ModuleCat.of kbar kbar)
      (i := (homOfLE h).op)
    rw [dif_pos hV] at hmap
    rw [hmap]
    have : IsIso (eqToHom heq) := inferInstance
    exact (ConcreteCategory.bijective_of_isIso (eqToHom heq)).2
  · -- codomain is zero (terminal in ModuleCat), so surjective trivially
    have hzero : Limits.IsZero
        ((skyscraperPresheaf P.point (ModuleCat.of kbar kbar)).obj
          (Opposite.op V)) := by
      simp [skyscraperPresheaf, hV]
      exact (terminalIsTerminal).isZero
    have : Subsingleton ((skyscraperPresheaf P.point
        (ModuleCat.of kbar kbar)).obj (Opposite.op V)) :=
      ModuleCat.subsingleton_of_isZero hzero
    intro y; exact ⟨0, Subsingleton.elim _ _⟩

/-! ## §3. The closed-point skyscraper sheaf has vanishing `H¹` -/

/-- **`H¹` of the closed-point skyscraper sheaf vanishes** (Hartshorne
III.2.5 applied to the flasque skyscraper).

For a smooth proper geometrically irreducible curve `C / kbar` and a
prime divisor `P : C.left.PrimeDivisor` (a closed point on the curve),
`dim_{kbar} H¹(C, skyscraperSheaf P (ModuleCat.of kbar kbar)) = 0`.

The proof composes the two substrate inputs of this chapter:
`skyscraperSheaf_isFlasque` (the skyscraper sheaf is flasque) and
`HModule_flasque_eq_zero` at `i = 1` (flasque ⇒ `H¹ = 0`); then
`Module.finrank kbar 0 = 0` closes the dimension identity.

**iter-191 Lane H prover dispatch** — closed via composition of
`HModule_flasque_eq_zero` (still typed-`sorry` pending iter-192+
Hartshorne III.2.5 closure) and `skyscraperSheaf_isFlasque` (now closed
directly in this file) at `i = 1`. The same name also occurs as a
`private` typed-`sorry` helper at
`AlgebraicJacobian/RiemannRoch/RRFormula.lean`; the `private` modifier
mangles that copy's internal name, so the public name resolved by the
blueprint's `\lean{...}` pin (and by `sync_leanok`) is the declaration
below. Blueprint reference:
`lem:H1_skyscraperSheaf_finrank_eq_zero_main`. -/
theorem Scheme.H1_skyscraperSheaf_finrank_eq_zero
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (C : Over (Spec (.of kbar))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] [IsIntegral C.left]
    (P : C.left.PrimeDivisor)
    [∀ U : TopologicalSpace.Opens C.left, Decidable (P.point ∈ U)] :
    Module.finrank kbar
        (Scheme.HModule kbar
          (skyscraperSheaf (C := ModuleCat.{u} kbar) P.point
            (ModuleCat.of kbar kbar)) 1) = 0 :=
  Scheme.HModule_flasque_eq_zero (Scheme.skyscraperSheaf_isFlasque C P) 1 le_rfl

end AlgebraicGeometry
