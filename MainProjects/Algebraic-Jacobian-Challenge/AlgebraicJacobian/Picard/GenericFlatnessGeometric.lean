/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.FlatteningStratification
import AlgebraicJacobian.Picard.QuotScheme
import AlgebraicJacobian.Cohomology.QcohTildeSections

/-!
# Generic flatness: the geometric statement (Nitsure §4)

This file proves the **geometric generic flatness theorem**
`AlgebraicGeometry.genericFlatness` (blueprint node `thm:generic_flatness`,
Nitsure §4): over an integral locally noetherian base `S`, a finitely
presented module sheaf on a finite-type (quasi-compact and locally of finite
type) `X ⟶ S` has flat sections over all affine pairs below some non-empty
open `V ⊆ S`.

It is the geometric-glue layer on top of the algebraic generic-freeness
engine of `AlgebraicJacobian.Picard.FlatteningStratification`
(`GenericFreeness.genericFlatnessAlgebraic`, Stacks 051R).  The declaration
lives in its own file — rather than in `FlatteningStratification.lean`, whose
remaining statements it logically belongs with — because the glue needs the
qcqs section-localization engine of `AlgebraicJacobian.Picard.QuotScheme`
(Stacks 01P0/01PC/01I8) and the base-ring descent of
`AlgebraicJacobian.Cohomology.QcohTildeSections`, and importing those files
into `FlatteningStratification.lean` perturbs the instance environment of its
(heavy, finished) dévissage proofs.

The layer structure, bottom to top:

1. `Module.Flat.of_isLocalizedModule_algebra` — mixed-base stability: flatness
   over the base survives localizing the module at a submonoid of the fibre
   algebra (Mathlib has only the same-ring version).
2. `flat_section_chartBasic` — on a basic open of a chart lying above a base
   basic open `D(g)`, sections are flat over the ambient affine `Γ(S, U₀)`,
   given freeness of the chart sections localized at `g`.
3. `flat_section_pair` — the two-layer basic-open reduction from an arbitrary
   affine pair `(U, W)` to chart-basic pieces, via
   `Module.flat_of_isLocalized_span` and two
   `Module.flat_iff_of_isLocalization` exchanges.
4. `genericFlatness` — chart supply by
   `Scheme.Modules.exists_affine_finite_sections_nhds` (Stacks 01PC), one
   generic-freeness witness per chart, product denominator, `V := D(f)`.
-/

universe u v

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry

/-! ## §1b. Geometric glue for generic flatness

The algebraic generic-freeness theorem (`GenericFreeness.genericFlatnessAlgebraic`)
concerns one finite module over one finite-type algebra.  The geometric statement
`genericFlatness` below quantifies over *all* affine pairs `U ≤ V`, `W ≤ p ⁻¹ᵁ U`.
This section provides the glue:

* `Module.Flat.of_isLocalizedModule_algebra` — flatness over the base survives
  localizing the module at a submonoid of the fibre algebra (mixed-base
  stability; Mathlib has only the same-ring `Module.Flat.of_isLocalizedModule`);
* `flat_sections_congr` — transport of section flatness along an equality of
  opens (the `appLE` restriction witness is proof-irrelevant);
* `flat_section_chartBasic` — the core: on a basic open of a chart lying above a
  base basic open `D(g)`, the sections of `F` are flat over the ambient affine
  `Γ(S, U₀)`, given that the chart sections localized at `g` are free.  The
  abstract localization is matched with the section module by the qcqs
  section-localization engine (`Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact`,
  Stacks 01P0) via the base-ring descent
  `isLocalizedModule_powers_restrictScalars_of_algebraMap`, and the remaining
  fibre-side localization is absorbed by the mixed-base stability lemma;
* `flat_section_pair` — the two-layer basic-open reduction: an arbitrary affine
  pair `(U, W)` is covered fibre-side by opens that are simultaneously basic in
  `W` and in a chart and lie above base basic opens common to `U` and `U₀`
  (`exists_basicOpen_le_affine_inter`, twice), and
  `Module.flat_of_isLocalized_span` plus two `Module.flat_iff_of_isLocalization`
  exchanges assemble the pieces. -/

section GenericFlatnessGeometricGlue

/-- Elementwise fibre-side `appLE` coherence: restricting the image of `appLE`
equals `appLE` into the smaller open. -/
private lemma appLE_res_apply {S X : Scheme.{u}} (p : X ⟶ S) {U : S.Opens}
    {W W' : X.Opens} (e : W ≤ p ⁻¹ᵁ U) (h : W' ≤ W) (u : Γ(S, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((p.appLE U W e).hom u) =
      (p.appLE U W' (h.trans e)).hom u := by
  have h1 := congrArg (fun (φ : Γ(S, U) ⟶ Γ(X, W')) => φ.hom u)
    (Scheme.Hom.appLE_map (f := p) e (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h1

/-- Elementwise base-side `appLE` coherence: `appLE` of a restricted base section
equals `appLE` from the larger base open. -/
private lemma appLE_base_res_apply {S X : Scheme.{u}} (p : X ⟶ S) {U U' : S.Opens}
    {W : X.Opens} (h : U' ≤ U) (e' : W ≤ p ⁻¹ᵁ U') (e : W ≤ p ⁻¹ᵁ U) (u : Γ(S, U)) :
    (p.appLE U' W e').hom ((S.presheaf.map (homOfLE h).op).hom u) =
      (p.appLE U W e).hom u := by
  have h1 := congrArg (fun (φ : Γ(S, U) ⟶ Γ(X, W)) => φ.hom u)
    (Scheme.Hom.map_appLE (f := p) e' (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h1

/-- Transport of section flatness along an equality of opens: the `Module.compHom`
structures via `appLE` agree definitionally because the `≤`-witness of `appLE` is
proof-irrelevant. -/
private theorem flat_sections_congr {S X : Scheme.{u}} (p : X ⟶ S) (F : X.Modules)
    {U₀ : S.Opens} {O₁ O₂ : X.Opens} (hEq : O₁ = O₂)
    (e₁ : O₁ ≤ p ⁻¹ᵁ U₀) (e₂ : O₂ ≤ p ⁻¹ᵁ U₀)
    (h : letI : Module Γ(S, U₀) Γ(F, O₁) := Module.compHom _ (p.appLE U₀ O₁ e₁).hom
         Module.Flat Γ(S, U₀) Γ(F, O₁)) :
    letI : Module Γ(S, U₀) Γ(F, O₂) := Module.compHom _ (p.appLE U₀ O₂ e₂).hom
    Module.Flat Γ(S, U₀) Γ(F, O₂) := by
  subst hEq
  exact h

open TensorProduct in
/-- **Mixed-base stability of flatness under module localization.**  Let `B` be an
`R`-algebra, `N` a `B`-module that is flat over `R`, and `g : N →ₗ[B] N'` a
localization of `N` at a submonoid `p ⊆ B`.  Then `N'` is still flat over `R`.

Mathlib's `Module.Flat.of_isLocalizedModule` treats only submonoids of `R`
itself; here the localization happens on the fibre side.  The proof rewrites
`𝟙 N' ⊗ f` as the `IsLocalizedModule.map` of `𝟙 N ⊗ f` (Mathlib's
`IsLocalizedModule.map_lTensor`, with the `IsLocalizedModule.rTensor` instances)
and uses that localization preserves injectivity
(`IsLocalizedModule.map_injective`). -/
theorem _root_.Module.Flat.of_isLocalizedModule_algebra {R B : Type v} [CommRing R]
    [CommRing B] [Algebra R B] (p : Submonoid B) {N N' : Type v} [AddCommGroup N]
    [Module R N] [Module B N] [IsScalarTower R B N] [AddCommGroup N'] [Module R N']
    [Module B N'] [IsScalarTower R B N'] (g : N →ₗ[B] N') [IsLocalizedModule p g]
    [Module.Flat R N] : Module.Flat R N' := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ I
  rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := B)]
  rw [← IsLocalizedModule.map_lTensor (S := p) (g := g) (f := I.subtype)]
  exact IsLocalizedModule.map_injective p
    (TensorProduct.AlgebraTensorModule.rTensor R I g)
    (TensorProduct.AlgebraTensorModule.rTensor R P g)
    (TensorProduct.AlgebraTensorModule.lTensor B N I.subtype)
    (by
      rw [TensorProduct.AlgebraTensorModule.coe_lTensor (A := B)]
      exact Module.Flat.lTensor_preserves_injective_linearMap I.subtype
        Subtype.val_injective)

set_option maxHeartbeats 1200000 in
-- Heartbeat headroom: several `IsLocalizedModule`/scalar-tower instance chains
-- at localized section modules (qcqs section-localization engine).
/-- **Chart-basic core of generic flatness.**  Let `Wj ≤ p ⁻¹ᵁ U₀` be an affine
chart whose section module localized at `g ∈ Γ(S, U₀)` is free over
`Γ(S, U₀)_g` (the output of algebraic generic freeness), and let `c ∈ Γ(X, Wj)`
cut a basic open lying above the base basic open `D(g)`.  Then the sections of
`F` over `D(c)` (presented as any open `O = D(c)`) are flat over `Γ(S, U₀)`.

Route: `D(β) = Wj ⊓ p ⁻¹ᵁ D(g)` for `β := appLE g`; the section restriction
`Γ(F, Wj) → Γ(F, D(β))` is a localization at `powers β` over `Γ(X, Wj)`
(Stacks 01P0) hence at `powers g` over `Γ(S, U₀)` (base-ring descent), so
`Γ(F, D(β))` inherits freeness-hence-flatness over `Γ(S, U₀)` from the
hypothesis; finally `Γ(F, D(β)) → Γ(F, D(c))` is a fibre-side localization,
absorbed by mixed-base stability. -/
private theorem flat_section_chartBasic {S X : Scheme.{u}} (p : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] {U₀ : S.Opens}
    {Wj : X.Opens} (hWj : IsAffineOpen Wj) (eWj : Wj ≤ p ⁻¹ᵁ U₀) (g : Γ(S, U₀))
    (hfree :
      letI : Module Γ(S, U₀) Γ(F, Wj) := Module.compHom _ (p.appLE U₀ Wj eWj).hom
      Module.Free (Localization.Away g)
        (LocalizedModule (Submonoid.powers g) Γ(F, Wj)))
    (c : Γ(X, Wj)) (hc : X.basicOpen c ≤ p ⁻¹ᵁ (S.basicOpen g))
    {O : X.Opens} (hO : O = X.basicOpen c) (eO : O ≤ p ⁻¹ᵁ U₀) :
    letI : Module Γ(S, U₀) Γ(F, O) := Module.compHom _ (p.appLE U₀ O eO).hom
    Module.Flat Γ(S, U₀) Γ(F, O) := by
  subst hO
  letI : Module Γ(S, U₀) Γ(F, Wj) := Module.compHom _ (p.appLE U₀ Wj eWj).hom
  -- the base element pushed into the chart ring, and its basic open
  set β : Γ(X, Wj) := (p.appLE U₀ Wj eWj).hom g with hβ
  have hDβ : X.basicOpen β = Wj ⊓ p ⁻¹ᵁ (S.basicOpen g) := by
    rw [hβ, show (p.appLE U₀ Wj eWj).hom g
        = (X.presheaf.map (homOfLE eWj).op).hom ((p.app U₀).hom g) from rfl]
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
  have hDcβ : X.basicOpen c ≤ X.basicOpen β := by
    rw [hDβ]
    exact le_inf (X.basicOpen_le c) hc
  have eβ : X.basicOpen β ≤ p ⁻¹ᵁ U₀ := (X.basicOpen_le β).trans eWj
  -- (1) chart-side localization of sections at β (Stacks 01P0)
  letI : Module Γ(X, Wj) Γ(F, X.basicOpen β) :=
    Module.compHom _ (algebraMap Γ(X, Wj) Γ(X, X.basicOpen β))
  haveI : IsScalarTower Γ(X, Wj) Γ(X, X.basicOpen β) Γ(F, X.basicOpen β) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI hlocB : IsLocalizedModule (Submonoid.powers β)
      (Scheme.Modules.restrictBasicOpenₗ F β) :=
    Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact F hWj.isCompact
      hWj.isQuasiSeparated β
  -- (2) `Γ(S, U₀)`-module structures and scalar towers
  letI : Algebra Γ(S, U₀) Γ(X, Wj) := (p.appLE U₀ Wj eWj).hom.toAlgebra
  letI : Module Γ(S, U₀) Γ(F, X.basicOpen β) :=
    Module.compHom _ (p.appLE U₀ (X.basicOpen β) eβ).hom
  haveI : IsScalarTower Γ(S, U₀) Γ(X, Wj) Γ(F, Wj) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI : IsScalarTower Γ(S, U₀) Γ(X, Wj) Γ(F, X.basicOpen β) :=
    IsScalarTower.of_algebraMap_smul (fun a n => by
      change (X.presheaf.map (homOfLE (X.basicOpen_le β)).op).hom
          ((p.appLE U₀ Wj eWj).hom a) • n
        = (p.appLE U₀ (X.basicOpen β) eβ).hom a • n
      rw [appLE_res_apply p eWj (X.basicOpen_le β) a])
  -- (3) base-ring descent of the localization, and flatness of `Γ(F, D(β))`
  haveI hlocA : IsLocalizedModule (Submonoid.powers g)
      ((Scheme.Modules.restrictBasicOpenₗ F β).restrictScalars Γ(S, U₀)) := by
    refine isLocalizedModule_powers_restrictScalars_of_algebraMap g _ ?_
    exact hlocB
  haveI hfreeg : Module.Free (Localization.Away g)
      (LocalizedModule (Submonoid.powers g) Γ(F, Wj)) := hfree
  haveI hflatLoc : Module.Flat Γ(S, U₀)
      (LocalizedModule (Submonoid.powers g) Γ(F, Wj)) := by
    haveI : Module.Flat (Localization.Away g)
        (LocalizedModule (Submonoid.powers g) Γ(F, Wj)) := inferInstance
    exact (Module.flat_iff_of_isLocalization (Localization.Away g)
      (Submonoid.powers g) (LocalizedModule (Submonoid.powers g) Γ(F, Wj))).mp this
  haveI hflatNβ : Module.Flat Γ(S, U₀) Γ(F, X.basicOpen β) :=
    Module.Flat.of_linearEquiv
      (IsLocalizedModule.iso (Submonoid.powers g)
        ((Scheme.Modules.restrictBasicOpenₗ F β).restrictScalars Γ(S, U₀))).symm
  -- (4) restrict from `D(β)` to `D(c)` and absorb by mixed-base stability
  set c' : Γ(X, X.basicOpen β) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le β)).op).hom c with hc'
  have hDc' : X.basicOpen c' = X.basicOpen c := by
    rw [hc', Scheme.basicOpen_res]
    exact inf_eq_right.mpr hDcβ
  have ec' : X.basicOpen c' ≤ p ⁻¹ᵁ U₀ := (X.basicOpen_le c').trans eβ
  letI : Module Γ(X, X.basicOpen β) Γ(F, X.basicOpen c') :=
    Module.compHom _ (algebraMap Γ(X, X.basicOpen β) Γ(X, X.basicOpen c'))
  haveI : IsScalarTower Γ(X, X.basicOpen β) Γ(X, X.basicOpen c')
      Γ(F, X.basicOpen c') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI hlocC : IsLocalizedModule (Submonoid.powers c')
      (Scheme.Modules.restrictBasicOpenₗ F c') :=
    Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact F
      (hWj.basicOpen β).isCompact (hWj.basicOpen β).isQuasiSeparated c'
  letI : Module Γ(S, U₀) Γ(F, X.basicOpen c') :=
    Module.compHom _ (p.appLE U₀ (X.basicOpen c') ec').hom
  letI : Algebra Γ(S, U₀) Γ(X, X.basicOpen β) :=
    (p.appLE U₀ (X.basicOpen β) eβ).hom.toAlgebra
  haveI : IsScalarTower Γ(S, U₀) Γ(X, X.basicOpen β) Γ(F, X.basicOpen β) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI : IsScalarTower Γ(S, U₀) Γ(X, X.basicOpen β) Γ(F, X.basicOpen c') :=
    IsScalarTower.of_algebraMap_smul (fun a n => by
      change (X.presheaf.map (homOfLE (X.basicOpen_le c')).op).hom
          ((p.appLE U₀ (X.basicOpen β) eβ).hom a) • n
        = (p.appLE U₀ (X.basicOpen c') ec').hom a • n
      rw [appLE_res_apply p eβ (X.basicOpen_le c') a])
  haveI hflatC' : Module.Flat Γ(S, U₀) Γ(F, X.basicOpen c') :=
    Module.Flat.of_isLocalizedModule_algebra (Submonoid.powers c')
      (Scheme.Modules.restrictBasicOpenₗ F c')
  exact flat_sections_congr p F hDc' ec' eO hflatC'

set_option maxHeartbeats 1600000 in
-- Heartbeat headroom: per-piece instance provisioning under binders for the
-- `flat_of_isLocalized_span` application.
/-- **Two-layer basic-open reduction for generic flatness.**  Given affine charts
`Wc j ≤ p ⁻¹ᵁ U₀` covering `p ⁻¹ᵁ U₀`, all of whose section modules localized
at `f ∈ Γ(S, U₀)` are free (the output of algebraic generic freeness at a
common denominator `f`), every affine pair `U ≤ D(f)`, `W ≤ p ⁻¹ᵁ U` has flat
sections: cover `W` by opens simultaneously basic in `W` and in a chart, lying
above base basic opens common to `U` and `U₀`; conclude with
`Module.flat_of_isLocalized_span` over `Γ(X, W)` and the two
`Module.flat_iff_of_isLocalization` exchanges on the base. -/
private theorem flat_section_pair {S X : Scheme.{u}} (p : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] {U₀ : S.Opens} (hU₀ : IsAffineOpen U₀)
    {ι : Type u} (Wc : ι → X.Opens) (hWc : ∀ j, IsAffineOpen (Wc j))
    (eWc : ∀ j, Wc j ≤ p ⁻¹ᵁ U₀)
    (hcover : ∀ x ∈ p ⁻¹ᵁ U₀, ∃ j, x ∈ Wc j) (f : Γ(S, U₀))
    (hfree : ∀ j,
      letI : Module Γ(S, U₀) Γ(F, Wc j) :=
        Module.compHom _ (p.appLE U₀ (Wc j) (eWc j)).hom
      Module.Free (Localization.Away f)
        (LocalizedModule (Submonoid.powers f) Γ(F, Wc j)))
    {U : S.Opens} (hU : IsAffineOpen U) (hUf : U ≤ S.basicOpen f)
    {W : X.Opens} (hW : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U) :
    letI : Module Γ(S, U) Γ(F, W) := Module.compHom _ (p.appLE U W e).hom
    Module.Flat Γ(S, U) Γ(F, W) := by
  letI : Module Γ(S, U) Γ(F, W) := Module.compHom _ (p.appLE U W e).hom
  have hUU₀ : U ≤ U₀ := hUf.trans (S.basicOpen_le f)
  have hWU₀ : W ≤ p ⁻¹ᵁ U₀ := e.trans (fun x hx => hUU₀ hx)
  -- per-point choice of a simultaneous basic open
  have Hx : ∀ x : ↥W, ∃ (b : Γ(X, W)) (a : Γ(S, U)) (a' : Γ(S, U₀)) (j : ι)
      (c : Γ(X, Wc j)),
      X.basicOpen b = X.basicOpen c ∧ (x : X) ∈ X.basicOpen b ∧
      S.basicOpen a = S.basicOpen a' ∧
      X.basicOpen b ≤ p ⁻¹ᵁ (S.basicOpen a) := by
    intro x
    have hxU : p.base x.1 ∈ U := e x.2
    have hxU₀ : p.base x.1 ∈ U₀ := hUU₀ hxU
    obtain ⟨a, a', haa', hpa⟩ :=
      AlgebraicGeometry.exists_basicOpen_le_affine_inter hU hU₀ (p.base x.1)
        ⟨hxU, hxU₀⟩
    obtain ⟨j, hxj⟩ := hcover x.1 (hWU₀ x.2)
    have hxT : x.1 ∈ (W ⊓ (p ⁻¹ᵁ S.basicOpen a ⊓ Wc j) : X.Opens) :=
      ⟨x.2, ⟨hpa, hxj⟩⟩
    obtain ⟨b₁, hb₁le, hxb₁⟩ := hW.exists_basicOpen_le
      (⟨x.1, hxT⟩ : ↥(W ⊓ (p ⁻¹ᵁ S.basicOpen a ⊓ Wc j) : X.Opens)) x.2
    obtain ⟨f₁, c, hfc, hxf₁⟩ := AlgebraicGeometry.exists_basicOpen_le_affine_inter
      (hW.basicOpen b₁) (hWc j) x.1 ⟨hxb₁, hxj⟩
    obtain ⟨b, hb⟩ := hW.basicOpen_basicOpen_is_basicOpen b₁ f₁
    exact ⟨b, a, a', j, c, hb.trans hfc, hb.symm ▸ hxf₁, haa',
      hb.symm ▸ ((X.basicOpen_le f₁).trans
        (hb₁le.trans (inf_le_right.trans inf_le_left)))⟩
  choose bb aa aa' jj cc hbc hxb haa' hba using Hx
  -- the covering family spans `Γ(X, W)`
  have hspan : Ideal.span (Set.range bb) = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    apply le_antisymm
    · exact iSup_le fun r => X.basicOpen_le _
    · intro y hy
      exact TopologicalSpace.Opens.mem_iSup.mpr
        ⟨⟨bb ⟨y, hy⟩, Set.mem_range_self _⟩, hxb ⟨y, hy⟩⟩
  -- instance packs for the span lemma
  letI : Algebra Γ(S, U) Γ(X, W) := (p.appLE U W e).hom.toAlgebra
  haveI : IsScalarTower Γ(S, U) Γ(X, W) Γ(F, W) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI instBpiece : ∀ r : Set.range bb, Module Γ(X, W) Γ(F, X.basicOpen r.1) :=
    fun r => Module.compHom _ (algebraMap Γ(X, W) Γ(X, X.basicOpen r.1))
  haveI instTowerB : ∀ r : Set.range bb,
      IsScalarTower Γ(X, W) Γ(X, X.basicOpen r.1) Γ(F, X.basicOpen r.1) :=
    fun r => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI instLoc : ∀ r : Set.range bb, IsLocalizedModule (Submonoid.powers r.1)
      (Scheme.Modules.restrictBasicOpenₗ F r.1) := fun r =>
    Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact F hW.isCompact
      hW.isQuasiSeparated r.1
  letI instRpiece : ∀ r : Set.range bb, Module Γ(S, U) Γ(F, X.basicOpen r.1) :=
    fun r =>
      Module.compHom _ (p.appLE U (X.basicOpen r.1) ((X.basicOpen_le r.1).trans e)).hom
  haveI instTowerR : ∀ r : Set.range bb,
      IsScalarTower Γ(S, U) Γ(X, W) Γ(F, X.basicOpen r.1) := fun r =>
    IsScalarTower.of_algebraMap_smul fun u n => by
      change (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom
          ((p.appLE U W e).hom u) • n
        = (p.appLE U (X.basicOpen r.1) ((X.basicOpen_le r.1).trans e)).hom u • n
      rw [appLE_res_apply p e (X.basicOpen_le r.1) u]
  -- assemble by the span criterion; the pieces are handled below
  refine Module.flat_of_isLocalized_span (R := Γ(S, U)) Γ(X, W) Γ(F, W)
    (Set.range bb) hspan (fun r => Γ(F, X.basicOpen r.1))
    (fun r => Scheme.Modules.restrictBasicOpenₗ F r.1) ?_
  -- per-piece flatness
  intro r
  obtain ⟨x, hx⟩ := r.2
  have hbar : X.basicOpen r.1 ≤ p ⁻¹ᵁ (S.basicOpen (aa x)) := hx ▸ hba x
  have hbcr : X.basicOpen r.1 = X.basicOpen (cc x) := hx ▸ hbc x
  have epieceU₀ : X.basicOpen r.1 ≤ p ⁻¹ᵁ U₀ := (X.basicOpen_le r.1).trans hWU₀
  have haU : S.basicOpen (aa x) ≤ U := S.basicOpen_le (aa x)
  have haU₀ : S.basicOpen (aa x) ≤ U₀ :=
    (haa' x).symm ▸ S.basicOpen_le (aa' x)
  -- module structures over the three base rings
  letI mA : Module Γ(S, S.basicOpen (aa x)) Γ(F, X.basicOpen r.1) :=
    Module.compHom _ (p.appLE (S.basicOpen (aa x)) (X.basicOpen r.1) hbar).hom
  letI mA0 : Module Γ(S, U₀) Γ(F, X.basicOpen r.1) :=
    Module.compHom _ (p.appLE U₀ (X.basicOpen r.1) epieceU₀).hom
  -- localization instances on the base
  haveI hloc1 : IsLocalization.Away (aa x) Γ(S, S.basicOpen (aa x)) :=
    hU.isLocalization_basicOpen (aa x)
  haveI tow1 : IsScalarTower Γ(S, U) Γ(S, S.basicOpen (aa x))
      Γ(F, X.basicOpen r.1) :=
    IsScalarTower.of_algebraMap_smul fun u n => by
      change (p.appLE (S.basicOpen (aa x)) (X.basicOpen r.1) hbar).hom
          ((S.presheaf.map (homOfLE haU).op).hom u) • n
        = (p.appLE U (X.basicOpen r.1) ((X.basicOpen_le r.1).trans e)).hom u • n
      rw [appLE_base_res_apply p haU hbar ((X.basicOpen_le r.1).trans e) u]
  letI algA : Algebra Γ(S, U₀) Γ(S, S.basicOpen (aa x)) :=
    ((S.presheaf.map (homOfLE haU₀).op).hom).toAlgebra
  haveI hloc2 : IsLocalization.Away (aa' x) Γ(S, S.basicOpen (aa x)) :=
    hU₀.isLocalization_of_eq_basicOpen (aa' x) (homOfLE haU₀) (haa' x)
  haveI tow2 : IsScalarTower Γ(S, U₀) Γ(S, S.basicOpen (aa x))
      Γ(F, X.basicOpen r.1) :=
    IsScalarTower.of_algebraMap_smul fun u n => by
      change (p.appLE (S.basicOpen (aa x)) (X.basicOpen r.1) hbar).hom
          ((S.presheaf.map (homOfLE haU₀).op).hom u) • n
        = (p.appLE U₀ (X.basicOpen r.1) epieceU₀).hom u • n
      rw [appLE_base_res_apply p haU₀ hbar epieceU₀ u]
  -- flatness over `Γ(S, U₀)` from the chart-basic core
  have hA : Module.Flat Γ(S, U₀) Γ(F, X.basicOpen r.1) := by
    have hDaf : S.basicOpen (aa x) ≤ S.basicOpen f := haU.trans hUf
    have hcle : X.basicOpen (cc x) ≤ p ⁻¹ᵁ (S.basicOpen (f * aa' x)) := by
      have h1 : X.basicOpen (cc x) ≤ p ⁻¹ᵁ (S.basicOpen (aa x)) := hbcr ▸ hbar
      have h2 : S.basicOpen (aa x) ≤ S.basicOpen (f * aa' x) := by
        rw [Scheme.basicOpen_mul]
        exact le_inf hDaf (haa' x).le
      exact h1.trans (fun y hy => h2 hy)
    letI mWj : Module Γ(S, U₀) Γ(F, Wc (jj x)) :=
      Module.compHom _ (p.appLE U₀ (Wc (jj x)) (eWc (jj x))).hom
    have hfree_g :
        Module.Free (Localization.Away (f * aa' x))
          (LocalizedModule (Submonoid.powers (f * aa' x)) Γ(F, Wc (jj x))) :=
      GenericFreeness.free_localizedModule_powers_mul Γ(S, U₀) Γ(F, Wc (jj x))
        f (aa' x) (hfree (jj x))
    exact flat_section_chartBasic p F (hWc (jj x)) (eWc (jj x)) (f * aa' x)
      hfree_g (cc x) hcle hbcr epieceU₀
  -- exchange the base ring twice: `U₀ → D(aa x) → U`
  have h2 : Module.Flat Γ(S, S.basicOpen (aa x)) Γ(F, X.basicOpen r.1) :=
    (Module.flat_iff_of_isLocalization (R := Γ(S, U₀))
      Γ(S, S.basicOpen (aa x)) (Submonoid.powers (aa' x))
      Γ(F, X.basicOpen r.1)).mpr hA
  exact (Module.flat_iff_of_isLocalization (R := Γ(S, U))
    Γ(S, S.basicOpen (aa x)) (Submonoid.powers (aa x))
    Γ(F, X.basicOpen r.1)).mp h2

end GenericFlatnessGeometricGlue

/-! ## §2. Generic flatness (Nitsure §4)

Over a noetherian integral base `S`, a coherent sheaf on a finite-type
`X ⟶ S` is flat above some non-empty open `V ⊆ S`. This is the inductive
engine of the flattening-stratification theorem: combined with
Noetherian induction on the closed complement `S ∖ V`, it produces the
finite stratification of `S` by flatness loci.

Algebraically (theorem `generic_flatness_algebraic`, no Lean pin): for a
noetherian domain `A`, a finite-type `A`-algebra `B`, and a finite
`B`-module `M`, there exists a non-zero `f ∈ A` such that `M_f` is a
free `A_f`-module. The geometric form (this declaration) restricts to a
non-empty affine open `Spec A ⊆ S` and applies the algebraic form on
each finite-type-algebra patch of `X` above `Spec A`.

Blueprint reference: `thm:generic_flatness` (Nitsure §4). -/

/-- **Generic flatness theorem** (Nitsure §4 / Stacks ?).

For a noetherian integral scheme `S`, a finite-type morphism `p : X ⟶ S`,
and a coherent `𝓞_X`-module `𝓕`, there exists a non-empty open subscheme
`V ⊆ S` such that `𝓕|_{X_V} = 𝓕|_{p⁻¹V}` is flat over `𝓞_V`.

PROVED (run 0010, T12 r4), following Nitsure §4: pass to a non-empty affine
open `U₀ ⊆ S` with `A := Γ(S, U₀)` a noetherian domain, cover the compact
preimage `p ⁻¹ᵁ U₀` by finitely many affine charts with finitely generated
sections (`Scheme.Modules.exists_affine_finite_sections_nhds`, Stacks 01PC),
apply algebraic generic freeness (`GenericFreeness.genericFlatnessAlgebraic`)
on each chart, and take `f ∈ A` the product of the witnesses.  The witness
open is `V := D(f)`, non-empty since `A` is a domain and `f ≠ 0`; the
quantified flatness on affine pairs below `V` is `flat_section_pair` (§1b).

Statement repair (run 0010, T12 r2): Nitsure requires `p` of **finite type**
(EGA sense: quasi-compact AND locally of finite type). With
`LocallyOfFiniteType` alone the statement is FALSE: for
`X = ⨿_q Spec 𝔽_q → Spec ℤ` (locally of finite type, not quasi-compact,
structure sheaf finitely presented) every non-empty open `V ⊆ Spec ℤ`
contains all but finitely many primes `q`, and `𝔽_q` is never flat over the
corresponding `ℤ[1/n]`. Quasi-compactness is what bounds the number of
denominators to clear. Hence the `[QuasiCompact p]` hypothesis below. -/
theorem genericFlatness {S X : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (p : X ⟶ S) [QuasiCompact p] [LocallyOfFiniteType p] (F : X.Modules)
    [F.IsFinitePresentation] :
    ∃ (V : S.Opens), (V : Set S).Nonempty ∧
      ∀ {U : S.Opens} (_ : IsAffineOpen U) (_ : U ≤ V) {W : X.Opens}
        (_ : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U),
        letI : Module Γ(S, U) Γ(F, W) := Module.compHom _ (p.appLE U W e).hom
        Module.Flat Γ(S, U) Γ(F, W) := by
  classical
  -- an ambient nonempty affine chart of the integral base
  obtain ⟨x₀⟩ : Nonempty S := inferInstance
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀U₀, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
  haveI : IsDomain Γ(S, U₀) := @IsIntegral.component_integral _ _ _ ⟨⟨x₀, hx₀U₀⟩⟩
  haveI : IsNoetherianRing Γ(S, U₀) :=
    IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  -- affine charts with finitely generated sections covering the compact preimage
  have hK : IsCompact ((p ⁻¹ᵁ U₀ : X.Opens) : Set X) :=
    p.isCompact_preimage hU₀.isCompact
  have HX : ∀ x : X, x ∈ p ⁻¹ᵁ U₀ → ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      V ≤ p ⁻¹ᵁ U₀ ∧ Module.Finite Γ(X, V) Γ(F, V) := fun x hx =>
    Scheme.Modules.exists_affine_finite_sections_nhds F x (p ⁻¹ᵁ U₀) hx
  choose! V hVaff hxV hVle hVfin using HX
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : ↥(p ⁻¹ᵁ U₀ : X.Opens) => ((V x.1 : X.Opens) : Set X))
    (fun x => (V x.1).2)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxV y hy⟩)
  -- per-chart generic freeness over `A := Γ(S, U₀)`
  have hGF : ∀ i : ↥t, ∃ fi : Γ(S, U₀), fi ≠ 0 ∧
      (letI : Module Γ(S, U₀) Γ(F, V i.1.1) :=
        Module.compHom _ (p.appLE U₀ (V i.1.1) (hVle i.1.1 i.1.2)).hom
      Module.Free (Localization.Away fi)
        (LocalizedModule (Submonoid.powers fi) Γ(F, V i.1.1))) := by
    intro i
    letI : Module Γ(S, U₀) Γ(F, V i.1.1) :=
      Module.compHom _ (p.appLE U₀ (V i.1.1) (hVle i.1.1 i.1.2)).hom
    letI : Algebra Γ(S, U₀) Γ(X, V i.1.1) :=
      (p.appLE U₀ (V i.1.1) (hVle i.1.1 i.1.2)).hom.toAlgebra
    haveI : IsScalarTower Γ(S, U₀) Γ(X, V i.1.1) Γ(F, V i.1.1) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI hft : Algebra.FiniteType Γ(S, U₀) Γ(X, V i.1.1) :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) p ‹_› ⟨U₀, hU₀⟩
        ⟨V i.1.1, hVaff i.1.1 i.1.2⟩ (hVle i.1.1 i.1.2)
    haveI := hVfin i.1.1 i.1.2
    exact GenericFreeness.genericFlatnessAlgebraic Γ(S, U₀) Γ(X, V i.1.1)
      Γ(F, V i.1.1)
  choose ff hff0 hffree using hGF
  -- the common denominator
  set f : Γ(S, U₀) := ∏ i ∈ (Finset.univ : Finset ↥t), ff i with hfdef
  have hf0 : f ≠ 0 := by
    rw [hfdef]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hff0 i
  refine ⟨S.basicOpen f, ?_, ?_⟩
  · -- non-emptiness: on a reduced scheme `D(f) = ⊥` forces `f = 0`
    rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty]
    intro hbot
    exact hf0 ((basicOpen_eq_bot_iff f).mp hbot)
  · -- flatness on every affine pair below `D(f)`, via the two-layer reduction
    intro U hU hUf W hW e
    refine flat_section_pair p F hU₀ (fun i : ↥t => V i.1.1)
      (fun i => hVaff i.1.1 i.1.2) (fun i => hVle i.1.1 i.1.2) ?_ f ?_ hU hUf hW e
    · -- the charts cover `p ⁻¹ᵁ U₀`
      intro x hx
      have := ht hx
      rw [Set.mem_iUnion₂] at this
      obtain ⟨i, hi, hxi⟩ := this
      exact ⟨⟨i, hi⟩, hxi⟩
    · -- freeness at the common denominator, chart by chart
      intro i
      letI : Module Γ(S, U₀) Γ(F, V i.1.1) :=
        Module.compHom _ (p.appLE U₀ (V i.1.1) (hVle i.1.1 i.1.2)).hom
      have h1 := GenericFreeness.free_localizedModule_powers_mul Γ(S, U₀)
        Γ(F, V i.1.1) (ff i) (∏ j ∈ Finset.univ.erase i, ff j) (hffree i)
      rwa [Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h1

end AlgebraicGeometry
