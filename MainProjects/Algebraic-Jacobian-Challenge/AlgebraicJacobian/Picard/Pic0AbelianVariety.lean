/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.IdentityComponent
import AlgebraicJacobian.Picard.TangentSpaceDualNumbers
import AlgebraicJacobian.Picard.TangentSpaceIdentitySection
import AlgebraicJacobian.Genus

/-!
# `Pic⁰_{C/k}` as an abelian variety (A.3.iii–vii)

This file is the **iter-193 Pic0AbelianVariety** file-skeleton (NEW lane,
blueprint-doctor flagged orphan resolution for the iter-192 plan-phase chapter
`Picard_Pic0AbelianVariety.tex`). It packages the strategy phase A.3.iii–vi
substrate and the A.3.vii assembly into the load-bearing Route~A statement
`Pic⁰_{C/k}` is an abelian variety, the gate of `thm:nonempty_jacobianWitness`
for `g(C) ≥ 1` curves.

The chapter consumes the abstract identity-component substrate set up in
`Picard/IdentityComponent.lean` (`Pic⁰_{C/k}` as a clopen subgroup scheme of
finite type, geometrically irreducible, formation commuting with base change)
and adds the curve-specific input: the tangent-space isomorphism
`T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)`, the resulting smoothness of dimension `g` at
the origin (hence everywhere by translation), properness inherited from the
projectivity of `Pic⁰_{C/k}` for `C/k` geometrically normal, and the assembly
into an abelian variety in the sense of Milne §I.1.

## Status (run 0008, T5 session)

Proved sorry-free in this file: `grpObj` (the `GrpObj (Pic0Scheme C)`
structure, via `IdentityComponent.isSubgroupHomomorphism` +
`PicScheme.groupSchemeStructure`), `tangentSpaceCotangentDual`,
`geometricallyIrreducible` (specialisation of the sibling's
`isFiniteTypeGeometricallyIrreducible`, whose QC∧GeomIrred conjunct is the
remaining upstream sorry), the `isAbelianVariety` assembly, and the moved
`Pic0Scheme.isAbelianVariety` (blueprint pin `thm:pic_zero_is_abelian_variety`).

Remaining `sorry` bodies: `tangentSpaceIso` (Kleiman §5 Thm 5.11 — needs the
`Pic(C_ε) ≅ H¹(C_ε, O^×)` cocycle classification and the truncated-exponential
kernel computation; the algebra-level splitting is in sibling
`Picard/DualNumberUnits.lean`), `smooth`, `proper`.

The 5 blueprint-pinned declarations are:

1. `AlgebraicGeometry.Scheme.Pic0.tangentSpaceIso` (theorem, A.3.iii) — the
   canonical isomorphism `T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)` (Kleiman §5
   Thm.~`thm:tgtsp`). Packaged as an `AddEquiv` between the cotangent space
   `m_e/m_e²` at a `k`-rational identity-section point `e` and the project's
   first-cohomology `k`-module `Scheme.HModule k (Scheme.toModuleKSheaf C) 1`
   (from `Genus.lean`). The `k`-module structure on the cotangent space at a
   `k`-rational point is supplied as part of the existential bundle.
2. `AlgebraicGeometry.Scheme.Pic0.smooth` (theorem, A.3.iv) — `Pic⁰_{C/k}` is
   `Smooth` over `k`. Kleiman §5 Cor.~`cor:sm` + Cor.~`cor:ch0`
   (characteristic-zero) + Ex.~`ex:jac` (curve case).
3. `AlgebraicGeometry.Scheme.Pic0.proper` (theorem, A.3.v) — `Pic⁰_{C/k}` is
   `IsProper` over `k`. Kleiman §5 Thm.~`th:qpp&p` (projectivity upgrade for
   geometrically normal `C/k`).
4. `AlgebraicGeometry.Scheme.Pic0.geometricallyIrreducible` (theorem, A.3.vi)
   — `Pic⁰_{C/k}` is `GeometricallyIrreducible` over `k`. Specialisation of
   `IdentityComponent.isFiniteTypeGeometricallyIrreducible` (sibling) to
   `G = PicScheme C`. Kleiman §5 Prp.~`prp:pic0`.
5. `AlgebraicGeometry.Scheme.Pic0.isAbelianVariety` (theorem, A.3.vii) —
   `Pic⁰_{C/k}` is an abelian variety: `IsProper ∧ Smooth ∧
   GeometricallyIrreducible ∧ Nonempty (GrpObj _)`. Milne §I.1, p.~8
   (defining axioms) + Kleiman §5 Rmk.~`rmk:Jac`. Load-bearing A.3.vii gate
   of Route~A.

## Note on type expressivity

Following the project rule "Never weaken the type to dodge the proof", each
pinned declaration carries a substantive, non-tautological type:

- `tangentSpaceIso C` — existentially quantifies over a `k`-rational
  identity-section point `e : Spec k ⟶ (Pic0Scheme C).left` and a `k`-module
  structure on the cotangent space `m_e/m_e²` (the `k`-module structure
  arising via the `k`-algebra structure on the stalk at a `k`-rational point;
  for the file-skeleton this Module instance is bundled as part of the Σ').
  Bundles an `AddEquiv` between the cotangent space and the
  `H¹(C, 𝒪_C)`-as-`k`-module. The body is iter-194+ work.
- `smooth C`, `proper C`, `geometricallyIrreducible C` — genuine `Prop`-valued
  statements on the structural morphism `(Pic0Scheme C).hom : Pic⁰_{C/k} ⟶
  Spec k`, not tautological.
- `isAbelianVariety C` — assembles the conjunction of the four
  abelian-variety properties (proper, smooth, geometrically irreducible,
  group-object structure); not vacuous because each conjunct is a genuine
  property/structure on the (typed-sorry) `Pic0Scheme C`.

## Coordination with `Pic0Scheme`

The underlying `k`-scheme `Pic⁰_{C/k}` is supplied by
`AlgebraicGeometry.Scheme.Pic0Scheme C` from sibling
`Picard/IdentityComponent.lean` (`def:pic_zero_subscheme` in the blueprint).
We do not redefine the underlying scheme here; the `Pic0` namespace below
collects the curve-specific abelian-variety facts about `Pic0Scheme C`.

## References

Blueprint: `blueprint/src/chapters/Picard_Pic0AbelianVariety.tex`
(735 LOC, 5 pins). Sources:
- Kleiman, "The Picard scheme", §5, Thm.~`thm:tgtsp` (tangent space),
  Cor.~`cor:sm` + Cor.~`cor:ch0` (smoothness), Thm.~`th:qpp&p`
  (quasi-projectivity/projectivity), Prp.~`prp:pic0` (irreducibility),
  Rmk.~`rmk:Jac` (assembly to abelian scheme); arXiv:math/0504020.
- Milne, "Abelian Varieties" (course notes, 2008), §I.1, p.~8
  (definition of abelian variety) + Rmk. III.1.4(e) (dimension equals genus).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## §1. The `Pic0` namespace

The blueprint chapter pins five Lean declarations under the
`AlgebraicGeometry.Scheme.Pic0` namespace. Their underlying scheme
`Pic⁰_{C/k}` is `Pic0Scheme C` from sibling `Picard/IdentityComponent.lean`;
the declarations below collect the curve-specific abelian-variety facts
about `Pic0Scheme C` (tangent space at the identity, smoothness, properness,
geometric irreducibility, abelian-variety assembly). -/

namespace Pic0

/-- **`Pic⁰_{C/k}` is a `k`-group scheme** — the group-object structure on
the identity component of the Picard scheme, inherited from `Pic_{C/k}` via
the clopen inclusion `Pic⁰_{C/k} ↪ Pic_{C/k}`.

Since `Pic0Scheme C` unwinds definitionally to
`GroupScheme.IdentityComponent (PicScheme C)` (run-0008 FGA rewire), this is
`GroupScheme.IdentityComponent.isSubgroupHomomorphism` applied to
`G = PicScheme C`, whose `GrpObj` instance is
`PicScheme.groupSchemeStructure` (Yoneda transport of the abelian-group
structure of the relative Picard presheaf) and whose local finiteness is the
`PicSchemeLocallyOfFiniteType` carrier (Kleiman §4 Thm `th:main`(1)). -/
theorem grpObj {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (GrpObj (Pic0Scheme C)) :=
  GroupScheme.IdentityComponent.isSubgroupHomomorphism (PicScheme C)

/-! ### §1b. Harvested helper lemmas (from GitHub PR #1, Alex Nguyen)

Sorry-free scheme-general and `Pic⁰_{C/k}`-specific helpers adapted from the
PR: the `k`-rationality residue-field identification, finite-dimensionality of
the cotangent space over a field, the pointed dual-number tangent-space API,
the separatedness / local-finite-type / quasi-compactness transports of the
identity-component substrate, and the fpqc-descent reduction of universal
closedness. Each `Pic⁰`-specific helper carries the file's standard instance
hypotheses `[HasPicScheme C] [PicScheme.PicSchemeLocallyOfFiniteType C]` (rather
than the PR's `haveI := instHasPicScheme C` pattern, which needs the absent
`[HasRationalPoint C]`), exactly as every other pinned declaration here. -/

/-- **Sorry-free, scheme-general.** A section `e : Spec k ⟶ X` of a scheme over
`Spec k` is a `k`-rational point, so the residue field at `e` is canonically
`k`. The section `e` and structure map `π` induce residue-field maps
`sbar : κ(e) → κ(pt)` and `pbar : κ(pt') → κ(e)` with
`pbar ≫ sbar = (e ≫ π).residueFieldMap default`, an iso because `e ≫ π = 𝟙`
is an open immersion; hence `sbar` is a split epi, and being a field
homomorphism it is a mono, so `sbar` is an isomorphism
(`isIso_of_mono_of_isSplitEpi`). The base residue-field identification is
discharged by composing `Scheme.Spec.residueFieldIso` with
`Ideal.algEquivResidueFieldOfField`. -/
theorem residueFieldIso_of_section_over_field {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (e : Spec (.of k) ⟶ X.left)
    (hsec : e ≫ X.hom = 𝟙 (Spec (.of k))) :
    Nonempty (X.left.residueField (e.base default) ≅ CommRingCat.of k) := by
  set sbar := e.residueFieldMap default with hsbar
  set pbar := X.hom.residueFieldMap (e.base default) with hpbar
  have hc : (e ≫ X.hom).residueFieldMap default = pbar ≫ sbar :=
    residueFieldMap_comp e X.hom default
  haveI : IsOpenImmersion (e ≫ X.hom) := by rw [hsec]; infer_instance
  haveI : IsIso (pbar ≫ sbar) :=
    hc ▸ (inferInstance : IsIso ((e ≫ X.hom).residueFieldMap default))
  haveI : IsSplitEpi sbar :=
    ⟨⟨inv (pbar ≫ sbar) ≫ pbar, by rw [Category.assoc, IsIso.inv_hom_id]⟩⟩
  haveI : Mono sbar :=
    ConcreteCategory.mono_of_injective sbar sbar.hom.injective
  haveI : IsIso sbar := isIso_of_mono_of_isSplitEpi sbar
  obtain ⟨hbase⟩ : Nonempty ((Spec (.of k)).residueField default ≅ CommRingCat.of k) := by
    let x : Spec (.of k) := default
    refine ⟨Scheme.Spec.residueFieldIso (.of k) default ≪≫ ?_⟩
    exact
      ((Ideal.algEquivResidueFieldOfField (k := k) x.asIdeal).toRingEquiv.toCommRingCatIso).symm
  exact ⟨asIso sbar ≪≫ hbase⟩

/-- **Sorry-free, scheme-general.** For a scheme locally of finite type over a
field, the cotangent space at any point is finite-dimensional over the residue
field — the local-Noetherianity input dimension arguments need. -/
theorem finiteDimensional_cotangentSpace_of_locallyOfFiniteType {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] (x : X.left) :
    FiniteDimensional (IsLocalRing.ResidueField (X.left.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (X.left.presheaf.stalk x)) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  infer_instance

/-- **Pointed dual-number points of `X` at `e`, over `Spec k`.** The
`k[ε]`-valued points of `X` lying over the closed point of `Spec k[ε]` and
landing at `e`; the functor-of-points model of the Zariski tangent space at
`e`. A named restatement of the anonymous subtype
`overDualNumberSectionEquivCotangentSpaceDual` targets, kept for readability
at the call sites below. -/
def pointedDualNumberPoints {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (e : Spec (.of k) ⟶ X.left) :=
  {g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left //
      g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
        ∧ g.base (IsLocalRing.closedPoint (DualNumber k)) = e.base default}

/-- **Axiom-clean.** The `k`-rational identity-section point of `Pic⁰_{C/k}`:
the lift of the Picard scheme's identity section `MonObj.one` through the open
immersion `Pic⁰_{C/k} ↪ Pic_{C/k}`, i.e. the sibling's
`GroupScheme.identityComponentSection` specialised to `G = PicScheme C`
(transported along the definitional identification
`Pic0Scheme C = GroupScheme.IdentityComponent (PicScheme C)`). This is the
`e`-witness of the Σ'-bundle in `tangentSpaceIso`. -/
noncomputable def identitySection {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Spec (.of k) ⟶ (Pic0Scheme C).left :=
  GroupScheme.identityComponentSection (PicScheme C)

/-- **Axiom-clean.** The identity-section point is a genuine section of the
structural morphism: `identitySection C ≫ (Pic0Scheme C).hom = 𝟙 (Spec k)`.
Transport of the sibling's `identityComponentSection_isSection`. -/
theorem identitySection_isSection {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    identitySection C ≫ (Pic0Scheme C).hom = 𝟙 (Spec (.of k)) :=
  GroupScheme.identityComponentSection_isSection (PicScheme C)

/-- **Axiom-clean.** The Stacks 0B28 dictionary at the identity point: pointed
dual-number points of `Pic⁰_{C/k}` at `e` biject with `κ(e)`-linear functionals
on the cotangent space `m_e/m_e²`. Direct specialisation of
`overDualNumberSectionEquivCotangentSpaceDual`
(`Picard/TangentSpaceIdentitySection.lean`) to `e = identitySection C`; the two
points `(identitySection C).base default` and
`(identitySection C).base (IsLocalRing.closedPoint k)` are bridged by
`Subsingleton (Spec k)`, the same idiom `tangentSpaceCotangentDual` uses. -/
theorem pointedDualNumberPoints_equiv_cotangentSpaceDual {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃
      Module.Dual
        (IsLocalRing.ResidueField
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
        (IsLocalRing.CotangentSpace
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))) := by
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  exact ⟨overDualNumberSectionEquivCotangentSpaceDual (Pic0Scheme C)
    (identitySection_isSection C) (congrArg _ (Subsingleton.elim _ _))⟩

/-- **Sorry-free source (carries the FGA existential's `sorryAx`).** The Picard
scheme `Pic_{C/k}` is separated over `k`. Kleiman delivers this as part of the
§4 representability package ("Then `Pic_{X/k}` is separated, ..."); its home is
the strengthened `HasPicScheme` existential in `FGAPicRepresentability.lean`,
which now bundles `IsSeparated X.hom` as its third conjunct; this helper is the
direct `Classical.choose_spec` extraction (same content as the global
`PicScheme.isSeparated` instance) consumed by the `isSeparated` assembly. -/
theorem picScheme_isSeparated {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    IsSeparated (PicScheme C).hom :=
  (HasPicScheme.has_pic_scheme (C := C)).choose_spec.2.2

/-- **Axiom-clean.** Separatedness of `Pic⁰_{C/k}` over `k`: the structural
morphism factors as the clopen inclusion `Pic⁰_{C/k} ↪ Pic_{C/k}` (an open
immersion by the sibling's axiom-clean
`IdentityComponent.isOpenSubgroupScheme`, hence a monomorphism, hence
separated) followed by the separated `(PicScheme C).hom`
(`picScheme_isSeparated`); separatedness is stable under composition. This is
the `IsSeparated` conjunct of the pinned `proper`. -/
theorem isSeparated {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    IsSeparated (Pic0Scheme C).hom := by
  haveI : IsSeparated (PicScheme C).hom := picScheme_isSeparated C
  obtain ⟨⟨f, hopen, -⟩⟩ :=
    GroupScheme.IdentityComponent.isOpenSubgroupScheme (PicScheme C)
  haveI := hopen
  change IsSeparated (GroupScheme.IdentityComponent (PicScheme C)).hom
  rw [← Over.w f]
  infer_instance

/-- **Axiom-clean.** `Pic⁰_{C/k}` is locally of finite type over `k`: the first
(sorry-free) conjunct of the sibling's
`IdentityComponent.isFiniteTypeGeometricallyIrreducible`, transported along the
definitional identification. The `LocallyOfFiniteType` conjunct of the pinned
`proper`. -/
theorem locallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    LocallyOfFiniteType (Pic0Scheme C).hom :=
  (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicScheme C)).1

/-- **Closed at this file's level (residual content in the sibling's typed
sorry).** `Pic⁰_{C/k}` is quasi-compact over `k`: the second conjunct of the
sibling's `IdentityComponent.isFiniteTypeGeometricallyIrreducible` (Kleiman §5
Lem.~`lem:agps`~(3): `α(U × U) = G⁰` is the image of the affine, hence
quasi-compact, `U × U`). Not needed for the `proper` assembly (Mathlib's
`IsProper` derives quasi-compactness from universal closedness) but recorded
for the blueprint's finite-type chain. -/
theorem quasiCompact {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    QuasiCompact (Pic0Scheme C).hom :=
  (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicScheme C)).2.1

/-- **Sorry-free.** Universal closedness of `Pic⁰_{C/k}` descends from its base
change to the algebraic closure `Spec k̄ → Spec k`. That base-change map is
faithfully flat and quasi-compact (a field extension `k → k̄` is injective and
flat, so `Spec.map` of it is surjective and flat; being a map of affines it is
quasi-compact), and `UniversallyClosed` is fpqc-local on the base (Stacks 02KS;
EGA IV₂ 2.6.4). The pinned Mathlib packages exactly this descent as the
`@[stacks 02KS]` instance
`descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`
(`Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`), so the closure is a
one-line `of_pullback_snd_of_descendsAlong` application — the same
`MorphismProperty` descent pattern `smooth_of_grpObj` uses, with the three
`Surjective`/`Flat`/`QuasiCompact` facts about `Spec.map (algebraMap k k̄)`
supplied by `inferInstance`. -/
theorem universallyClosed_of_baseChange {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : UniversallyClosed (pullback.snd (Pic0Scheme C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    UniversallyClosed (Pic0Scheme C).hom := by
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

/-- **Dual-number points of `Pic⁰_{C/k}` at the identity are the cotangent
dual** (Kleiman §5 Thm.~`thm:tgtsp`, LHS). Given the `k`-group-scheme
structure on `Pic0Scheme C` (supplied by `Pic0.grpObj`), the identity section
`e : Spec k ⟶ Pic⁰_{C/k}` hits a `k`-rational point, and the over-`Spec k`
dual-number points of `Pic⁰_{C/k}` at `e` — the Zariski tangent space
`T₀ Pic⁰_{C/k}` in its functor-of-points form — form the `κ(e)`-linear dual
of the cotangent space `m_e/m_e²`.

This is the geometric half of `tangentSpaceIso`; composing with the
`H¹(C, 𝒪_C)`-identification of `Dual (m_e/m_e²)` (gated on the `AJC.picrep`
representability cone) closes `thm:pic0_tangent_space_iso`. -/
theorem tangentSpaceCotangentDual {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (Σ' (e : Spec (.of k) ⟶ (Pic0Scheme C).left),
      (e ≫ (Pic0Scheme C).hom = 𝟙 (Spec (.of k))) ×'
      ({g : Spec (CommRingCat.of (DualNumber k)) ⟶ (Pic0Scheme C).left //
          g ≫ (Pic0Scheme C).hom
              = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
            ∧ g.base (IsLocalRing.closedPoint (DualNumber k)) = e.base default} ≃
        Module.Dual
          (IsLocalRing.ResidueField ((Pic0Scheme C).left.presheaf.stalk (e.base default)))
          (IsLocalRing.CotangentSpace
            ((Pic0Scheme C).left.presheaf.stalk (e.base default))))) := by
  obtain ⟨i⟩ := grpObj C
  letI := i
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  exact ⟨GroupScheme.identitySection (Pic0Scheme C),
    GroupScheme.identitySection_comp (Pic0Scheme C),
    overDualNumberSectionEquivCotangentSpaceDual (Pic0Scheme C)
      (GroupScheme.identitySection_comp (Pic0Scheme C))
      (congrArg _ (Subsingleton.elim _ _))⟩

/-- **Typed sorry: the Picard/deformation comparison from pointed dual-number
points to `H¹(C, 𝒪_C)`.**

This is the genuinely missing geometric bridge behind
`tangentSpaceDualEquivH1`: once the tangent space at the identity has been
presented as pointed dual-number points of `Pic⁰_{C/k}`, this lemma turns that
pointed first-order deformation space into `Scheme.HModule k
(Scheme.toModuleKSheaf C) 1`.

The missing theorem, in natural-language form, is:
"For a smooth proper geometrically integral curve `C/k`, the first-order
deformations of the identity line bundle on `C` are classified by
`H¹(C, 𝒪_C)`, functorially in the dual-number thickening." -/
theorem pointedDualNumberPoints_addCommGroup {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hPointsDual :
      Nonempty
        (pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃
          Module.Dual
            (IsLocalRing.ResidueField
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            (IsLocalRing.CotangentSpace
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))))) :
    Nonempty
      (Σ' (_inst : AddCommGroup (pointedDualNumberPoints (Pic0Scheme C) (identitySection C))),
        Module.Dual
            (IsLocalRing.ResidueField
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            (IsLocalRing.CotangentSpace
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
          ≃+ pointedDualNumberPoints (Pic0Scheme C) (identitySection C)) := by
  /-
  Intended proof:
  - choose the equivalence packaged by `hPointsDual`;
  - transport the additive-group structure from the displayed `Module.Dual`
    onto `pointedDualNumberPoints (Pic0Scheme C) (identitySection C)`;
  - upgrade the chosen equivalence to an `AddEquiv`.
  -/
  sorry

/-- **Typed sorry: pointed dual-number points identify with the first-order
Picard deformation carrier.**

This is the representability/kernel half of the tangent-space comparison:
evaluate the Picard representability equivalence at `Spec k[ε]`, restrict to
the identity fiber, and package the resulting first-order deformation object as
an additive group `K`. Concretely `K` should be the kernel of the restriction
map `Pic(C_ε) → Pic(C)`. -/
theorem pointedDualNumberPoints_equiv_firstOrderPicardDeformationCarrier {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    [AddCommGroup (pointedDualNumberPoints (Pic0Scheme C) (identitySection C))] :
    Nonempty
      (Σ' (K : Type (u + 1)), AddCommGroup K ×
        Nonempty (pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃+ K)) := by
  /-
  Intended proof:
  - evaluate `(representable C).homEquiv` at `Spec k[ε]`;
  - identify the identity-pointed fiber with the first-order deformations of
    the identity line bundle, i.e. the kernel of `Pic(C_ε) → Pic(C)`;
  - let `K` be that kernel, equipped with its inherited additive group
    structure from the Picard group law.
  -/
  sorry

/-- **Typed sorry: the Picard/deformation comparison from pointed dual-number
points to `H¹(C, 𝒪_C)`.**

This is the genuinely missing geometric bridge behind
`tangentSpaceDualEquivH1`: once the tangent space at the identity has been
presented as pointed dual-number points of `Pic⁰_{C/k}`, this lemma turns that
pointed first-order deformation space into `Scheme.HModule k
(Scheme.toModuleKSheaf C) 1`.

The missing theorem, in natural-language form, is:
"For a smooth proper geometrically integral curve `C/k`, the first-order
deformations of the identity line bundle on `C` are classified by
`H¹(C, 𝒪_C)`, functorially in the dual-number thickening." -/
theorem firstOrderPicardDeformationCarrier {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hPointsDual :
      Nonempty
        (pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃
          Module.Dual
            (IsLocalRing.ResidueField
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            (IsLocalRing.CotangentSpace
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))))) :
      Nonempty
        (Σ' (K : Type (u + 1)), AddCommGroup K ×
        Nonempty
          (Module.Dual
              (IsLocalRing.ResidueField
                ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
              (IsLocalRing.CotangentSpace
                ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            ≃+ K)) := by
  obtain ⟨instPts, hDualPoints⟩ := pointedDualNumberPoints_addCommGroup C hPointsDual
  letI := instPts
  obtain ⟨K, hK, hPointsK⟩ :=
    pointedDualNumberPoints_equiv_firstOrderPicardDeformationCarrier C
  letI := hK
  obtain ⟨hPointsK⟩ := hPointsK
  exact ⟨⟨K, hK, ⟨hDualPoints.trans hPointsK⟩⟩⟩

/-- **Typed sorry: the first-order Picard deformation group is `H¹(C, 𝒪_C)`.**

This isolates the cohomological half of the tangent-space comparison. Starting
from the first-order Picard deformation carrier `K` produced above, one
computes `K ≃+ H¹(C, 𝒪_C)` by the truncated exponential sequence on the dual
number thickening `C_ε`. -/
theorem firstOrderPicardDeformationCarrier_equiv_H1 {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hCarrier :
      Nonempty
        (Σ' (K : Type (u + 1)), AddCommGroup K ×
          Nonempty
            (Module.Dual
                (IsLocalRing.ResidueField
                  ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
                (IsLocalRing.CotangentSpace
                  ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
              ≃+ K))) :
    Nonempty
      (Σ' (K : Type (u + 1)), AddCommGroup K ×
        Nonempty
          (Module.Dual
              (IsLocalRing.ResidueField
                ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
              (IsLocalRing.CotangentSpace
                ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            ≃+ K) ×
        Nonempty (K ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1)) := by
  /-
  Intended proof:
  - unpack `hCarrier` as the additive group `K` of first-order deformations;
  - compute `K ≃+ H¹(C, 𝒪_C)` using the split truncated exponential sequence
    `0 → 𝒪_C → 𝒪^×_{C_ε} → 𝒪^×_C → 1`;
  - repackage the original carrier data together with this `H¹`-comparison.
  -/
  sorry

/-- **Typed sorry: the Picard/deformation comparison from pointed dual-number
points to `H¹(C, 𝒪_C)`.**

This is the genuinely missing geometric bridge behind
`tangentSpaceDualEquivH1`: once the tangent space at the identity has been
presented as pointed dual-number points of `Pic⁰_{C/k}`, this lemma turns that
pointed first-order deformation space into `Scheme.HModule k
(Scheme.toModuleKSheaf C) 1`.

The missing theorem, in natural-language form, is:
"For a smooth proper geometrically integral curve `C/k`, the first-order
deformations of the identity line bundle on `C` are classified by
`H¹(C, 𝒪_C)`, functorially in the dual-number thickening." -/
theorem firstOrderPicardDeformationGroup {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hPointsDual :
      Nonempty
        (pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃
          Module.Dual
            (IsLocalRing.ResidueField
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            (IsLocalRing.CotangentSpace
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))))) :
    Nonempty
      (Σ' (K : Type (u + 1)), AddCommGroup K ×
        Nonempty
          (Module.Dual
              (IsLocalRing.ResidueField
                ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
              (IsLocalRing.CotangentSpace
                ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            ≃+ K) ×
        Nonempty (K ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1)) := by
  obtain ⟨hCarrier⟩ := firstOrderPicardDeformationCarrier C hPointsDual
  obtain ⟨hCarrierH1⟩ := firstOrderPicardDeformationCarrier_equiv_H1 C ⟨hCarrier⟩
  exact ⟨hCarrierH1⟩

/-- **Typed sorry: the Picard/deformation comparison from pointed dual-number
points to `H¹(C, 𝒪_C)`.**

This is the genuinely missing geometric bridge behind
`tangentSpaceDualEquivH1`: once the tangent space at the identity has been
presented as pointed dual-number points of `Pic⁰_{C/k}`, this lemma turns that
pointed first-order deformation space into `Scheme.HModule k
(Scheme.toModuleKSheaf C) 1`.

The missing theorem, in natural-language form, is:
"For a smooth proper geometrically integral curve `C/k`, the first-order
deformations of the identity line bundle on `C` are classified by
`H¹(C, 𝒪_C)`, functorially in the dual-number thickening." -/
theorem tangentSpaceDualEquivH1_of_pointedDualNumberPoints {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hPointsDual :
      Nonempty
        (pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃
          Module.Dual
            (IsLocalRing.ResidueField
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            (IsLocalRing.CotangentSpace
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))))) :
    Nonempty
      (Module.Dual
          (IsLocalRing.ResidueField
            ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
          (IsLocalRing.CotangentSpace
            ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
        ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  let T0Dual :=
    Module.Dual
      (IsLocalRing.ResidueField
        ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
      (IsLocalRing.CotangentSpace
        ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
  let H1 := Scheme.HModule k (Scheme.toModuleKSheaf C) 1
  obtain ⟨⟨K, hK, hT0DualK, hKH1⟩⟩ := firstOrderPicardDeformationGroup C hPointsDual
  letI := hK
  obtain ⟨hT0DualK⟩ := hT0DualK
  obtain ⟨hKH1⟩ := hKH1
  exact ⟨(show T0Dual ≃+ H1 from hT0DualK.trans hKH1)⟩

/-- **Typed sorry: the Kleiman §5 tangent/cohomology comparison at the
identity section, in dual form.**

This is the genuine deformation-theoretic heart of Kleiman §5 Thm.~`thm:tgtsp`.
It packages the comparison

`Dual (m_e/m_e²) ≃ H¹(C, 𝒪_C)`

at the identity point `e = identitySection C`. The intended Lean proof uses
only already-established generic tangent-space infrastructure plus one missing
Picard/deformation bridge:

1. use `pointedDualNumberPoints_equiv_cotangentSpaceDual C` to identify
   pointed dual-number points of `Pic⁰_{C/k}` at the identity with
   `Dual (m_e/m_e²)`;
2. evaluate the representability equivalence `(representable C).homEquiv` at
   `Spec k[ε]` to identify those pointed dual-number points with
   `ker (Pic(C_ε) → Pic(C))`;
3. compute that kernel as `H¹(C, 𝒪_C)` via the split truncated exponential
   sequence from `Picard/DualNumberUnits.lean`.

The missing Lean API is therefore the Picard-functor/cohomology comparison,
not more tangent-space algebra. -/
theorem tangentSpaceDualEquivH1 {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty
      (Module.Dual
          (IsLocalRing.ResidueField
            ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
          (IsLocalRing.CotangentSpace
            ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
        ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  let T0Dual :=
    Module.Dual
      (IsLocalRing.ResidueField
        ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
      (IsLocalRing.CotangentSpace
        ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
  -- Step 1: reuse the already-built tangent-space dictionary at the identity.
  -- This is the scheme-general input coming from dual numbers and cotangent
  -- spaces, and it tells us that the functor-of-points tangent model of
  -- `Pic⁰_{C/k}` lands in `T0Dual`.
  have hPointsDual :
      Nonempty (pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃ T0Dual) := by
    simpa [T0Dual] using pointedDualNumberPoints_equiv_cotangentSpaceDual C
  obtain ⟨hPicardDeformation⟩ := tangentSpaceDualEquivH1_of_pointedDualNumberPoints C hPointsDual
  simpa [T0Dual] using hPicardDeformation

/-- **Typed sorry: finite-dimensional self-duality for the cotangent space at
the identity, once the local geometric inputs are supplied.**

This separates the purely linear-algebraic remainder from the geometric
bookkeeping in `cotangentSpaceEquivDual`. After proving that the cotangent
space is finite-dimensional over the residue field and that the residue field
comes from a `k`-rational point, only the standard noncanonical self-duality of
a finite-dimensional vector space remains. -/
theorem cotangentSpaceEquivDual_of_finiteDimensional {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (hFinite :
      FiniteDimensional
        (IsLocalRing.ResidueField
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
        (IsLocalRing.CotangentSpace
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))))
    (hResidue :
      Function.Bijective
        (algebraMap k
          (IsLocalRing.ResidueField
            ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))))) :
    Nonempty
      (IsLocalRing.CotangentSpace
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))
        ≃+
          Module.Dual
            (IsLocalRing.ResidueField
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            (IsLocalRing.CotangentSpace
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))) := by
  /-
  Intended proof:
  - let `R := (Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)`;
  - let `κ := IsLocalRing.ResidueField R`;
  - let `V := IsLocalRing.CotangentSpace R`;
  - let `ek : k ≃+* κ := residueFieldEquivOfBijective (R := R) hResidue`;
  - choose a basis of the finite-dimensional `κ`-vector space `V`;
  - construct the dual basis and the resulting linear equivalence
    `V ≃ₗ[κ] Module.Dual κ V`;
  - forget linearity to obtain the required `AddEquiv`.

  The concrete theorem I am looking for, if it already exists in Mathlib, is a
  standard finite-dimensional self-duality statement:
  "every finite-dimensional vector space over a field is noncanonically
  linearly equivalent to its dual."
  -/
  let R := (Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)
  let κ := IsLocalRing.ResidueField R
  let V := IsLocalRing.CotangentSpace R
  let _ek : k ≃+* κ := residueFieldEquivOfBijective (R := R) hResidue
  let _hFinite : FiniteDimensional κ V := by simpa [R, κ, V] using hFinite
  sorry

/-- **Typed sorry: finite-dimensional self-duality of the cotangent space at
the identity.**

The current theorem `tangentSpaceEquiv` is phrased on the cotangent space
`m_e/m_e²` itself, while the tangent-space dictionary naturally lands on its
dual. For the file skeleton we therefore package the noncanonical additive
equivalence

`m_e/m_e² ≃ Dual (m_e/m_e²)`.

The intended proof is pure finite-dimensional linear algebra after the local
geometry has been supplied:

1. `finiteDimensional_cotangentSpace_of_locallyOfFiniteType` gives finite
   dimensionality at the identity point;
2. `identitySection_isSection C` gives the `k`-rationality needed to identify
   the residue field with `k`;
3. choose a basis and transport the basis/dual-basis equivalence to an
   `AddEquiv`. -/
theorem cotangentSpaceEquivDual {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty
      (IsLocalRing.CotangentSpace
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))
        ≃+
          Module.Dual
            (IsLocalRing.ResidueField
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
            (IsLocalRing.CotangentSpace
              ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))) := by
  let x := (identitySection C).base default
  let R := (Pic0Scheme C).left.presheaf.stalk x
  let κ := IsLocalRing.ResidueField R
  let V := IsLocalRing.CotangentSpace R
  -- Step 1: the cotangent space at the identity is finite-dimensional over
  -- its residue field because `Pic⁰_{C/k}` is locally of finite type over `k`.
  have hFinite : FiniteDimensional κ V := by
    simpa [x, R, κ, V] using
      finiteDimensional_cotangentSpace_of_locallyOfFiniteType (X := Pic0Scheme C) x
  -- Step 2: the identity section lands at a `k`-rational point, so the
  -- residue field at that point is canonically identified with `k`.
  have hResidue : Function.Bijective (algebraMap k κ) := by
    have hsec : identitySection C ≫ (Pic0Scheme C).hom = 𝟙 (Spec (.of k)) :=
      identitySection_isSection C
    haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum k))
    simpa [x, R, κ] using
      (bijective_algebraMap_residueField_of_section (X := Pic0Scheme C)
        (e := identitySection C) (he := hsec)
        (x := x) (hx := congrArg _ (Subsingleton.elim _ _)))
  -- Step 3: finite-dimensional linear algebra over a field gives a
  -- noncanonical self-duality `V ≃ Dual V`. The only missing API here is a
  -- packaged theorem producing this equivalence from `hFinite` (and, if one
  -- wants the scalar field literally to be `k`, transporting scalars across
  -- `residueFieldEquivOfBijective (R := R) hResidue`).
  obtain ⟨hSelfDual⟩ := cotangentSpaceEquivDual_of_finiteDimensional C hFinite hResidue
  simpa [x, R, κ, V] using hSelfDual

/-- **Typed sorry: the Kleiman §5 tangent/cohomology comparison at the
identity section.**

This isolates the genuinely curve-specific input behind
`tangentSpaceIso`. The intended proof reuses the already-built scheme-general
helpers in this file and splits into the following top-level steps:

1. Use `identitySection C` and `identitySection_isSection C` to pin the
   `k`-rational origin of `Pic⁰_{C/k}`.
2. Use `tangentSpaceCotangentDual C` / `pointedDualNumberPoints_equiv_cotangentSpaceDual C`
   to identify dual-number tangent vectors with the dual of the cotangent
   space (Stacks 0B28 dictionary).
3. Compare those pointed dual-number points with first-order deformations of
   line bundles on `C`, hence with `H¹(C, 𝒪_C)` via the truncated exponential
   sequence and the Picard-functor semantics.

Step 3 is the real Kleiman Thm. 5.11 content and still needs the
representability semantics currently missing from the `picSharp` stub, so we
package exactly that gap here. -/
theorem tangentSpaceEquiv {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (IsLocalRing.CotangentSpace
        ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))
      ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  -- Assemble the two genuine subproblems:
  -- `m/m² ≃ Dual (m/m²)` by finite-dimensional linear algebra, followed by
  -- `Dual (m/m²) ≃ H¹(C, 𝒪_C)` by the Picard/deformation comparison.
  obtain ⟨hCotangentDual⟩ := cotangentSpaceEquivDual C
  obtain ⟨hDualH1⟩ := tangentSpaceDualEquivH1 C
  exact ⟨hCotangentDual.trans hDualH1⟩

/-- **Tangent space at the identity: `T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)`.**

The Kleiman §5 Thm.~`thm:tgtsp` tangent-space isomorphism. For a smooth
proper geometrically integral curve `C/k`, the Zariski tangent space at the
identity of `Pic⁰_{C/k}` is canonically isomorphic to the first sheaf
cohomology `H¹(C, 𝒪_C)`.

In Lean (skeleton form): we bundle existentially over a `k`-rational
identity-section point `e : Spec k ⟶ (Pic0Scheme C).left` and a `k`-module
structure on the cotangent space `m_e/m_e²` (the natural `k`-module structure
arising from the `k`-algebra structure on the stalk at a `k`-rational point;
for the file-skeleton this instance is supplied via Σ' to avoid hard-coding
a global instance prematurely). The substantive content is an `AddEquiv`
between the cotangent space and the project's `H¹(C, 𝒪_C)` module
`Scheme.HModule k (Scheme.toModuleKSheaf C) 1`.

A k-LinearEquiv refinement (iter-194+) replaces the `AddEquiv` once the
`k`-module structure on the cotangent space is consistently threaded through
downstream consumers; the underlying additive group structure is enough for
the dimension corollary `dim_k T₀ Pic⁰ = dim_k H¹ = g(C)`. -/
theorem tangentSpaceIso {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (Σ' (e : Spec (.of k) ⟶ (Pic0Scheme C).left),
      IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk (e.base default))
        ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  -- The existential witness is the canonical identity section of `Pic⁰_{C/k}`.
  refine ⟨identitySection C, ?_⟩
  -- The only remaining content is the Kleiman tangent/cohomology comparison
  -- at that distinguished point.
  obtain ⟨hEqv⟩ := tangentSpaceEquiv C
  exact hEqv

/-- **Typed sorry: the at-the-origin smoothness input.**

This packages the genuinely geometric part of the smoothness proof: prove that
the identity of `Pic⁰_{C/k}` has an open neighbourhood on which the structure
morphism is smooth. The intended argument is exactly the blueprint one:

1. compare the tangent dimension at the identity with `H¹(C, 𝒪_C)` using
   `tangentSpaceEquiv C`;
2. identify `dim_k H¹(C, 𝒪_C)` with `genus C`;
3. convert the resulting dimension equality into smoothness at the origin
   (Cartier in characteristic `0`, unobstructedness / `H²(C, 𝒪_C) = 0` on a
   curve in general).

The missing ingredients here are honest geometry rather than bookkeeping, so
we keep them concentrated in this single helper. -/
theorem smoothAtIdentity {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    ∃ U : (Pic0Scheme C).left.Opens,
      (identitySection C).base default ∈ U ∧ Smooth (U.ι ≫ (Pic0Scheme C).hom) := by
  /-
  Proof sketch to formalise later:
  - `obtain ⟨hT⟩ := tangentSpaceEquiv C`.
  - compare `Module.finrank` on both sides of `hT`;
  - identify the RHS with `genus C`;
  - invoke the curve-specific smoothness criterion at the identity.
  -/
  sorry

/-- **Typed sorry: smoothness propagates from the identity.**

Once `Pic⁰_{C/k}` is smooth on an open neighbourhood of the identity,
translation by geometric points carries that open neighbourhood to one around
every other point. This is the "group action spreads smoothness everywhere"
step from the blueprint. -/
theorem smooth_of_smoothAtIdentity {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C]
    (h : ∃ U : (Pic0Scheme C).left.Opens,
      (identitySection C).base default ∈ U ∧ Smooth (U.ι ≫ (Pic0Scheme C).hom)) :
    Smooth (Pic0Scheme C).hom := by
  /-
  Proof sketch to formalise later:
  - base change to `k̄` and use the identity-component base-change theorem;
  - translate the smooth neighbourhood of `0` to a smooth neighbourhood of an
    arbitrary geometric point;
  - conclude because smoothness is local on the source.
  -/
  sorry

/-- **Smoothness of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is smooth over `k` (Kleiman §5 Cor.~`cor:sm` + Cor.~`cor:ch0` in
characteristic zero + Ex.~`ex:jac` for the curve case).

The proof (iter-194+): smoothness at the identity propagates to smoothness
everywhere by translation (Pic⁰ is a `k`-group scheme, so multiplication by
any `λ ∈ Pic⁰(k̄)` is an automorphism). At the identity, smoothness reduces
to the inequality
`dim_0 Pic⁰_{C/k} ≤ dim_k T₀ Pic⁰_{C/k} = dim_k H¹(C, 𝒪_C) = g(C)`
(`tangentSpaceIso`) becoming an equality. For a smooth proper curve this
equality holds: in characteristic zero by Cartier's theorem (every
`k`-group scheme is smooth), in positive characteristic by the curve-specific
vanishing `H²(C, 𝒪_C) = 0` (the obstruction to lifting tangent vectors). -/
theorem smooth {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Smooth (Pic0Scheme C).hom := by
  -- First prove smoothness near the identity.
  have h0 : ∃ U : (Pic0Scheme C).left.Opens,
      (identitySection C).base default ∈ U ∧ Smooth (U.ι ≫ (Pic0Scheme C).hom) :=
    smoothAtIdentity C
  -- Then spread that neighbourhood to all points by translation.
  exact smooth_of_smoothAtIdentity C h0

/-- **Typed sorry: the universal-closedness half of properness.**

This isolates the genuinely non-formal part of the properness proof. The
surrounding file already proves the other `IsProper` ingredients
(`isSeparated`, `locallyOfFiniteType`) sorry-free, so it is enough to package
Kleiman's projectivity argument as universal closedness here. -/
theorem universallyClosed {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    UniversallyClosed (Pic0Scheme C).hom := by
  /-
  Proof sketch to formalise later:
  - obtain quasi-projectivity of `Pic⁰_{C/k}` from Kleiman's theorem;
  - after base change to `k̄`, reduce to ruling out a nontrivial linear part;
  - use the Chevalley--Rosenlicht structure theorem plus the normality of the
    curve product to exclude nonconstant maps `𝔾_m → Pic⁰`;
  - descend universal closedness back along the algebraic-closure extension,
    using `universallyClosed_of_baseChange`.
  -/
  sorry

/-- **Properness of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is proper over `k` (Kleiman §5 Thm.~`th:qpp&p`; a smooth proper
curve is geometrically normal, hence the projectivity upgrade applies).

The proof (iter-194+): `Pic⁰_{C/k}` is quasi-projective (Kleiman §5
Thm.~`th:qpp&p`, first conclusion); to upgrade to projective (hence proper)
we use the Chevalley–Rosenlicht structure theorem to reduce to ruling out
non-constant `k̄`-morphisms `𝔾_m → Pic⁰_{C/k̄}`. The latter follows from
normality of `C ×_k 𝔾_m` and Hartshorne II Ex.~6.15 (invertible sheaves on
a normal integral scheme are sheaves of Cartier divisors). -/
theorem proper {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    IsProper (Pic0Scheme C).hom := by
  -- `IsProper` is assembled from its three structural constituents.
  letI : IsSeparated (Pic0Scheme C).hom := isSeparated C
  letI : LocallyOfFiniteType (Pic0Scheme C).hom := locallyOfFiniteType C
  letI : UniversallyClosed (Pic0Scheme C).hom := universallyClosed C
  infer_instance

/-- **Geometric irreducibility of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is geometrically irreducible over `k` (Kleiman §5 Prp.~`prp:pic0`,
specialisation of the abstract identity-component substrate
`IdentityComponent.isFiniteTypeGeometricallyIrreducible` of
`Picard/IdentityComponent.lean` to `G = PicScheme C`).

The proof: apply `GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible`
to `G = PicScheme C` (locally of finite type by the
`PicSchemeLocallyOfFiniteType` carrier); `IdentityComponent (PicScheme C)`
is `Pic0Scheme C` definitionally. The specialisation is complete here; the
remaining mathematical obligation (Kleiman's translate-cover argument, EGA
IV₂ 4.5.8/4.6.1) lives in the sibling's
`isFiniteTypeGeometricallyIrreducible` sorry. -/
theorem geometricallyIrreducible {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    GeometricallyIrreducible (Pic0Scheme C).hom :=
  (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicScheme C)).2.2

/-- **`Pic⁰_{C/k}` is an abelian variety (A.3.vii assembly).**

For a smooth proper geometrically integral curve `C/k`, the identity
component `Pic⁰_{C/k}` is an abelian variety over `k`: the underlying
`k`-scheme is smooth (`Pic0.smooth`), proper (`Pic0.proper`), and
geometrically irreducible (`Pic0.geometricallyIrreducible`), and it carries
a `k`-group-scheme structure inherited from `Pic_{C/k}` via the inclusion
`Pic⁰_{C/k} ↪ Pic_{C/k}`
(`GroupScheme.IdentityComponent.isSubgroupHomomorphism`). Commutativity is
automatic (Milne §I.1, Cor.~1.4).

Milne §I.1, p.~8: "A complete connected group variety is called an abelian
variety." This is the load-bearing A.3.vii gate of Route~A for
`thm:nonempty_jacobianWitness`.

The proof assembles the four conjuncts: `proper` (this file), `smooth`
(this file), `geometricallyIrreducible` (this file), and the
`Nonempty (GrpObj (Pic0Scheme C))` slot from `Pic0.grpObj` (this file,
via `GroupScheme.IdentityComponent.isSubgroupHomomorphism` applied to
`G = PicScheme C`). The assembly itself is sorry-free; the remaining
obligations live in the `smooth` / `proper` conjuncts and the
geometric-irreducibility substrate. -/
theorem isAbelianVariety {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    IsProper (Pic0Scheme C).hom ∧ Smooth (Pic0Scheme C).hom ∧
      GeometricallyIrreducible (Pic0Scheme C).hom ∧
      Nonempty (GrpObj (Pic0Scheme C)) :=
  ⟨proper C, smooth C, geometricallyIrreducible C, grpObj C⟩

end Pic0

namespace Pic0Scheme

/-- **`Pic⁰_{C/k}` is an abelian variety** — the `Pic0Scheme`-namespace form
pinned by the blueprint node `thm:pic_zero_is_abelian_variety`
(`Picard_IdentityComponent.tex`). Moved here (run 0008) from sibling
`Picard/IdentityComponent.lean` so it can consume the per-conjunct theorems
of this chapter; it is literally `Pic0.isAbelianVariety`. -/
theorem isAbelianVariety {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    IsProper (Pic0Scheme C).hom ∧ Smooth (Pic0Scheme C).hom ∧
      GeometricallyIrreducible (Pic0Scheme C).hom ∧
      Nonempty (GrpObj (Pic0Scheme C)) :=
  Pic0.isAbelianVariety C

end Pic0Scheme

end Scheme

end AlgebraicGeometry
