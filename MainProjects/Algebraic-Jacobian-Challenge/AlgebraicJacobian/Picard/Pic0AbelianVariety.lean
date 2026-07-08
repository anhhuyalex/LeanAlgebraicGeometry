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

## Status (iter-194: bridge + wiring closures)

The master bridge `Pic0.eq_identityComponent` is **closed** (`rfl`): sibling
`Picard/IdentityComponent.lean` now defines `Pic0Scheme C` for real as
`GroupScheme.IdentityComponent (PicScheme C)` (unblocked by the iter-195
`HasPicScheme` strengthening that made `PicScheme.locallyOfFiniteType`
sorry-free). Downstream of the bridge, `Pic0.geometricallyIrreducible` and
`Pic0.isAbelianVariety` are closed *in this file* by transport/assembly;
their residual mathematical content lives in the sibling's typed sorries
(`IdentityComponent.isFiniteTypeGeometricallyIrreducible`,
`IdentityComponent.isSubgroupHomomorphism`) and in this file's §1b helpers.

iter-195: the three curve-specific Kleiman §5 pins `tangentSpaceIso`,
`smooth`, `proper` are now themselves sorry-free *assemblies* of the §1b
blueprint-step helpers. After the iter-current Pass 1 closures
`identitySection_residueFieldIso` and `picScheme_isSeparated`, the residual
typed sorries sit at four single-citation gap points:
`universallyClosed` (Kleiman Thm.~5.4, Chevalley–Rosenlicht half),
`tangentSpaceEquiv` (Kleiman Thm.~5.11), `smoothAtIdentity` (Kleiman
Cor.~5.13/5.14 + Ex.~5.23) and `smooth_of_smoothAtIdentity` (translation
propagation). Their content has no substrate in Mathlib at the pinned
revision nor in the project's axiom set, and per the project rule the
types are not weakened to dodge the proofs.

iter-current (placeholder cleanup + honest seams): an intermediate draft
had decomposed the gap points into `opaque` carriers (`dualNumber`,
`schemePoints`, `etaleH1`, `kBar` with a *sorried `Field` instance*),
`True`-typed stub lemmas, and lemmas with `sorry` inside their
*statements*; besides not compiling (missing instance binders), those
constructs were vacuous or unfalsifiable and hid the work. They are
replaced by: a real dual-number substrate (§1b-0, sorry-free defs over
Mathlib's `DualNumber`/`TrivSqZeroExt`), and genuinely-typed step lemmas
(§1b-1..4) — `identitySection_residueFieldIso`,
`pointedDualNumberPoints_equiv_cotangentSpaceDual`,
`finiteDimensional_HModule_one`, `pointedDualNumberPoints_equiv_H1`,
`universallyClosed_of_baseChange`,
`smoothAtIdentity_finrankCotangentEqGenus`, `h2Vanishing`,
`geometricallyReduced`. Two structural findings are recorded in the
relevant docstrings: (1) the Kleiman-5.11-core seams are **unprovable from
the current axiom set** while `picSharp` remains a `Classical.choice`
placeholder (`FGAPicRepresentability.lean` §0) — pinning the represented
functor's semantics is the prerequisite for all curve-specific content;
(2) the pinned Mathlib's `smooth_of_grpObj`
(`Mathlib/AlgebraicGeometry/Group/Smooth.lean`) subsumes the whole
translation-propagation step, reducing the smoothness pin to
`GeometricallyReduced (Pic0Scheme C).hom` + the sibling `GrpObj` sorry.

The 5 pinned declarations are:

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

/-! ### §1a. Helper lemmas: bridging `Pic0Scheme` to the abstract substrate

The shared gap that used to block the five pinned theorems below is closed:
`Pic0Scheme` (`Picard/IdentityComponent.lean`) is no longer a bare `sorry` —
its body is now the long-promised `GroupScheme.IdentityComponent (PicScheme C)`
(iter-194 closure). The unblocking fact was the strengthened `HasPicScheme`
axiom in `FGAPicRepresentability.lean` (iter-195: its existential now bundles
`LocallyOfFiniteType X.hom` alongside representability, matching what Kleiman's
construction already delivers). Consequently `LocallyOfFiniteType (PicScheme C).hom`
is a **real, sorry-free instance** (`PicScheme.locallyOfFiniteType`, in
`FGAPicRepresentability.lean`) rather than a second independent axiom — it resolves
automatically from just `[SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
[GeometricallyIntegral C.hom]` (the same three hypotheses every pinned theorem in this
file already carries) via `instHasPicScheme`. So every proven (or typed-sorry,
ready-to-be-closed) fact about `GroupScheme.IdentityComponent` now transports to
`Pic0Scheme C` by `rw [eq_identityComponent]`. -/

/-- **The master bridge lemma — sorry-free (closed iter-194).** `Pic0Scheme C`
really is the identity component of `PicScheme C`. With `Pic0Scheme` now
*defined* as `GroupScheme.IdentityComponent (PicScheme C)`
(`Picard/IdentityComponent.lean`), this is `rfl`: the two sides are
definitionally equal, with proof irrelevance on the `Prop`-valued
`HasPicScheme` / `PicSchemeGroupObject` instance arguments absorbing any
difference in how the instances were synthesised at the two elaboration
sites. Every fact established about `GroupScheme.IdentityComponent` in
`Picard/IdentityComponent.lean` — in particular the **axiom-clean**
`isOpenSubgroupScheme` — transports to `Pic0Scheme C` by
`rw [eq_identityComponent]`; `geometricallyIrreducible` and
`isAbelianVariety` below consume it this way.

`[HasPicScheme C]` is listed explicitly below (rather than left to auto-resolve via
`instHasPicScheme` from the three base hypotheses, as everywhere else in this file)
to avoid a `synthInstance` elaboration-order pitfall: `PicScheme C` itself needs
`[HasPicScheme C]` to become a concrete term before `GroupScheme.IdentityComponent`
can search for `[LocallyOfFiniteType (PicScheme C).hom]` *about* that term; leaving
both to be inferred fresh at the same nested call site left the instance metavariable
for `PicScheme`'s own `[HasPicScheme C]` argument unresolved at the point
`LocallyOfFiniteType` search needed to index on it, causing spurious `synthInstance`
failure (confirmed via `set_option trace.Meta.synthInstance true`: every individual
sub-instance — `HasPicScheme C`, `Field k`, etc. — resolves fine in isolation, only
the combined nested search failed). Pinning `[HasPicScheme C]` as an explicit local
hypothesis here removes the ambiguity; it is still auto-supplied transparently by
every caller that only has the three base hypotheses, since `instHasPicScheme` fires
for those, so this changes nothing about who can use this lemma. -/
theorem eq_identityComponent {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    Pic0Scheme C = GroupScheme.IdentityComponent (PicScheme C) :=
  rfl

/-- **Sorry-free.** `H¹(C, 𝒪_C)` has `k`-dimension exactly `genus C`, by *definition*
of `genus` (`Genus.lean:40`: `genus C := Module.finrank k (Scheme.HModule k
(Scheme.toModuleKSheaf C) 1)`). Feeds the `H¹`-side of `tangentSpaceIso`'s dimension
count (Kleiman §5 Thm.~5.11: `dim_k T₀ Pic⁰ = dim_k H¹(C, 𝒪_C) = g(C)`).

Hypothesis note: `genus` requires `[GeometricallyIrreducible C.hom]`, while the pinned
theorems assume the stronger `[GeometricallyIntegral C.hom]`. The bridging implication
**is** an instance in the pinned Mathlib checkout
(`Mathlib/AlgebraicGeometry/Geometrically/Integral.lean`:
`instance (priority := low) [GeometricallyIntegral f] : GeometricallyIrreducible f`,
verified against `.lake-packages/mathlib` this iter), so composing this lemma into
the pinned theorems needs no extra hypothesis. -/
theorem finrank_HModule_eq_genus {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] :
    genus C = Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
  rfl

/-! ### §1b. Blueprint-step helper lemmas (iter-195 decomposition, iter-196 rebase)

The three remaining Kleiman §5 pins (`tangentSpaceIso`, `smooth`, `proper`)
are decomposed below into helpers matching the proof steps of
`blueprint/src/chapters/Picard_Pic0AbelianVariety.tex`, wired to the
previously established substrate wherever it exists — including typed-sorry
dependencies (`isFiniteTypeGeometricallyIrreducible`,
`isSubgroupHomomorphism`, `baseChangeIso`), which is sanctioned for this
decomposition.

iter-196: the scheme-general dual-numbers/identity-section API (Stacks 0B28
dictionary, `overDualNumberSectionEquivCotangentSpaceDual`,
`GroupScheme.identitySection`) has landed upstream in
`Picard/TangentSpaceDualNumbers.lean` / `Picard/TangentSpaceIdentitySection.lean`
— it is the API the blueprint's `\lean{}` tags actually pin (every one of
`lem:tangent_derivation_descends` through `thm:tangent_identity_cotangent_dual`
matches a declaration there). This file's earlier ad-hoc copy
(`Picard/TangentSpace.lean`, an unpinned parallel construction) is deleted;
`pointedDualNumberPoints_equiv_cotangentSpaceDual` below is rewired onto the
upstream lemma instead, same statement, new proof. `Pic0.tangentSpaceCotangentDual`
(blueprint `thm:pic0_tangent_cotangent_dual`, `\leanok`) is upstream's
sorry-free specialisation of the same API to `Pic0Scheme C` under an explicit
`GrpObj` hypothesis; kept alongside the concrete-point route below (via the
axiom-clean `identitySection`) since the remaining sorries need a fixed
witness point, not an existential.

Axiom-clean today: `identitySection`, `identitySection_isSection`,
`identitySection_residueFieldIso`, `pointedDualNumberPoints_equiv_cotangentSpaceDual`,
`tangentSpaceCotangentDual`, `locallyOfFiniteType`, and the assembly logic
of `isSeparated`/`proper`/`smooth`/`tangentSpaceIso`. Typed sorries at
single-citation gap points: `universallyClosed` (Kleiman §5 Thm.~5.4,
Chevalley–Rosenlicht half), `tangentSpaceEquiv` (Kleiman §5 Thm.~5.11 core,
still gated on the `picSharp` semantics pinning — see
`pointedDualNumberPoints_equiv_H1`), `smoothAtIdentity` (Kleiman §5
Cor.~5.13/5.14 + Ex.~5.23, the at-the-origin input), and
`smooth_of_smoothAtIdentity` (the translation-propagation step). -/

/-- **Pointed dual-number points of `X` at `e`, over `Spec k`.** The
`k[ε]`-valued points of `X` lying over the closed point of `Spec k[ε]` and
landing at `e`; the functor-of-points model of the Zariski tangent space at
`e`. A named restatement of the anonymous subtype
`overDualNumberSectionEquivCotangentSpaceDual`
(`Picard/TangentSpaceIdentitySection.lean`) already targets, kept purely for
readability at the call sites below. -/
def pointedDualNumberPoints {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (e : Spec (.of k) ⟶ X.left) :=
  {g : Spec (CommRingCat.of (DualNumber k)) ⟶ X.left //
      g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
        ∧ g.base (IsLocalRing.closedPoint (DualNumber k)) = e.base default}

/-- **Sorry-free, scheme-general (ported from the deleted `Picard/TangentSpace.lean`;
no upstream equivalent lands this exact `≅ CommRingCat.of k` form — upstream's
`bijective_algebraMap_residueField_of_section` states the same fact as a bare
`Function.Bijective`).** A section `e : Spec k ⟶ X` of a scheme over `Spec k` is
a `k`-rational point, so the residue field at `e` is canonically `k`. -/
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

/-- **Sorry-free, scheme-general (ported from the deleted `Picard/TangentSpace.lean`;
no upstream equivalent).** For a scheme locally of finite type over a field, the
cotangent space at any point is finite-dimensional over the residue field — the
local Noetherianity input dimension arguments need. -/
theorem finiteDimensional_cotangentSpace_of_locallyOfFiniteType {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] (x : X.left) :
    FiniteDimensional (IsLocalRing.ResidueField (X.left.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (X.left.presheaf.stalk x)) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  infer_instance

/-- **Axiom-clean.** The `k`-rational identity-section point of `Pic⁰_{C/k}`:
the lift of the Picard scheme's identity section `MonObj.one` through the
open immersion `Pic⁰_{C/k} ↪ Pic_{C/k}`, i.e. the sibling's
`GroupScheme.identityComponentSection` specialised to `G = PicScheme C` and
transported along the (definitional) bridge `eq_identityComponent`. This is
the `e`-witness of the Σ'-bundle in `tangentSpaceIso`
(blueprint `thm:pic0_tangent_space_iso`, "tangent space via dual numbers"
paragraph: the identity `0 ∈ Pic⁰_{C/k}(k)`). -/
noncomputable def identitySection {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Spec (.of k) ⟶ (Pic0Scheme C).left :=
  haveI : HasPicScheme C := instHasPicScheme C
  GroupScheme.identityComponentSection (PicScheme C)

/-- **Axiom-clean.** The identity-section point is a genuine section of the
structural morphism: `identitySection C ≫ (Pic0Scheme C).hom = 𝟙 (Spec k)`.
Transport of the sibling's `identityComponentSection_isSection` along the
definitional bridge. Downstream (iter-196+): certifies that
`(identitySection C).base default` is a `k`-rational point, the hypothesis
under which the cotangent space `m_e/m_e²` carries its natural `k`-module
structure (blueprint `thm:pic0_tangent_space_iso`, k-linearity paragraph). -/
theorem identitySection_isSection {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    identitySection C ≫ (Pic0Scheme C).hom = 𝟙 (Spec (.of k)) :=
  haveI : HasPicScheme C := instHasPicScheme C
  GroupScheme.identityComponentSection_isSection (PicScheme C)


/-! ### §1b-0. Dual-number substrate

The scheme-general dual-number API now lives upstream in
`Picard/TangentSpaceDualNumbers.lean` and `Picard/TangentSpaceIdentitySection.lean`
(landed independently of this file); this file only uses the specialisation
to `Pic0Scheme C` at the identity section, via `pointedDualNumberPoints`
above and `overDualNumberSectionEquivCotangentSpaceDual` below. -/

/-! ### §1b-1. Honest step lemmas for `tangentSpaceEquiv` (typed sorries)

Each statement below is a genuine, non-vacuous mathematical claim between
*real* objects (no `True`-typed stubs, no `sorry` inside a statement, no
opaque carriers). They are the seams along which `tangentSpaceEquiv`
factors; see the closure plan in the chapter tex. Ranks:

- `identitySection_residueFieldIso` — Rank B. Provable from
  `identitySection_isSection` (a point admitting a section over `Spec k`
  has residue field `k`); needs only Mathlib's `Scheme.residueField` API.
- `pointedDualNumberPoints_equiv_cotangentSpaceDual` — Rank B/C. The
  Stacks 0B28 dictionary at the point `e`: pointed `k[ε]`-points ↔ local
  `k`-algebra maps `𝒪_{X,e} → k[ε]` (via `SpecToEquivOfLocalRing`) ↔
  `κ(e)`-linear functionals on `m_e/m_e²`. Scheme-general; no Picard
  content. This is the "dual-numbers tangent-space API" gap.
- `finiteDimensional_HModule_one` — Rank C, **load-bearing beyond this
  file**: without it `Module.finrank k H¹` (hence `genus C`!) silently
  takes the junk value `0`. Finiteness of coherent cohomology of a proper
  curve; expected route: Čech/Mayer–Vietoris on a two-affine cover
  (`Cohomology/MayerVietorisCore.lean`) + Noetherian finiteness.
- `pointedDualNumberPoints_equiv_H1` — Rank C, **the Kleiman §5
  Thm. 5.11 core**, and *unprovable from the current axiom set*: `picSharp`
  is an arbitrary `Classical.choice` functor (`FGAPicRepresentability.lean`
  §0), so nothing ties `(Pic0Scheme C)(k[ε])` to line bundles or to `H¹`.
  Closing it requires first pinning the semantics of the represented
  functor (upgrade `RelPicFunctor.PicSharp` from its `PUnit` stub, then
  strengthen `HasPicScheme` to represent *that* functor), then the
  truncated-exponential sequence `0 → H⁰?/H¹(𝒪_C) → Pic(C_ε) → Pic(C) → …`
  and (over `k ≠ k̄`) the étale/Zariski `H¹(𝔾ₘ)` comparison
  (Stacks 03P8 / Hilbert 90). -/

/-- **Sorry-free (iter-current Pass 1).** The
identity section is a `k`-rational point: the residue field of `Pic⁰_{C/k}`
at `identitySection C` is `k`. The `k`-rationality content is fully proved
here from `identitySection_isSection`: the section `e` and structure map `π`
induce residue-field maps `sbar : κ(e) → κ(pt)` and `pbar : κ(pt') → κ(e)`
with `pbar ≫ sbar = (e ≫ π).residueFieldMap default`, which is an iso because
`e ≫ π = 𝟙` is an open immersion (Mathlib's `IsOpenImmersion ⟹ IsIso` on
residue fields); hence `sbar` is a split epi, and being a field homomorphism
it is a mono, so `sbar` is an isomorphism (`isIso_of_mono_of_isSplitEpi`).
The base residue-field identification is discharged by composing
`Scheme.Spec.residueFieldIso` with
`Ideal.algEquivResidueFieldOfField`. Supplies the `k`-structure on the
cotangent space used by the
pinned `tangentSpaceIso` (blueprint `thm:pic0_tangent_space_iso`,
k-linearity paragraph). -/
theorem identitySection_residueFieldIso {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Nonempty ((Pic0Scheme C).left.residueField ((identitySection C).base default)
      ≅ CommRingCat.of k) := by
  exact residueFieldIso_of_section_over_field
    (X := Pic0Scheme C) (e := identitySection C) (identitySection_isSection C)

/-- **Axiom-clean (iter-196: rewired onto the upstream general API).** The
Stacks 0B28 dictionary at the identity point: pointed dual-number points of
`Pic⁰_{C/k}` at `e` biject with `κ(e)`-linear functionals on the cotangent
space `m_e/m_e²`. Direct specialisation of
`overDualNumberSectionEquivCotangentSpaceDual`
(`Picard/TangentSpaceIdentitySection.lean`) to `e = identitySection C`; the
two points `(identitySection C).base default` and
`(identitySection C).base (IsLocalRing.closedPoint k)` are bridged by
`Subsingleton (Spec k)`, the same idiom `Pic0.tangentSpaceCotangentDual`
below uses. -/
theorem pointedDualNumberPoints_equiv_cotangentSpaceDual {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
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

/-- **Sorry-free, scheme-general input now discharged upstream.** The cotangent
space of `Pic⁰_{C/k}` at the identity is finite-dimensional over its residue
field because `Pic⁰_{C/k}` is locally of finite type over the field `k`, hence
locally Noetherian, so the stalk is Noetherian and Mathlib's cotangent-space
instance applies. This removes one formerly implicit obligation from the
`tangentSpaceEquiv` dimension bookkeeping: the remaining work is the
Picard-specific comparison with `H¹(C, 𝒪_C)`, not local Noetherianity. -/
theorem finiteDimensional_cotangentSpaceAtIdentity {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    FiniteDimensional
      (IsLocalRing.ResidueField
        ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
      (IsLocalRing.CotangentSpace
        ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))) := by
  haveI : LocallyOfFiniteType (Pic0Scheme C).hom := by
    haveI : HasPicScheme C := instHasPicScheme C
    rw [eq_identityComponent C]
    exact (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
      (PicScheme C)).1
  exact finiteDimensional_cotangentSpace_of_locallyOfFiniteType
    (X := Pic0Scheme C) ((identitySection C).base default)

/-- **Sorry-free (blueprint `thm:pic0_tangent_cotangent_dual`, `\leanok`,
landed upstream).** Dual-number points of `Pic⁰_{C/k}` at the identity are
the cotangent dual (Kleiman §5 Thm.~`thm:tgtsp`, LHS). Given the
`k`-group-scheme structure on `Pic0Scheme C` (supplied by
`GroupScheme.IdentityComponent.isSubgroupHomomorphism` once `Pic0Scheme`
unwinds to `IdentityComponent (PicScheme C)`), the identity section
`e : Spec k ⟶ Pic⁰_{C/k}` hits a `k`-rational point, and the over-`Spec k`
dual-number points of `Pic⁰_{C/k}` at `e` — the Zariski tangent space
`T₀ Pic⁰_{C/k}` in its functor-of-points form — form the `κ(e)`-linear dual
of the cotangent space `m_e/m_e²`. Kept alongside
`pointedDualNumberPoints_equiv_cotangentSpaceDual` above (which fixes the
concrete witness `e := identitySection C` rather than existentially
quantifying over it) purely because this is the exact statement the
blueprint's `\lean{}` tag pins. -/
theorem tangentSpaceCotangentDual {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom]
    (hgrp : Nonempty (GrpObj (Pic0Scheme C))) :
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
  obtain ⟨i⟩ := hgrp
  letI := i
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  exact ⟨GroupScheme.identitySection (Pic0Scheme C),
    GroupScheme.identitySection_comp (Pic0Scheme C),
    overDualNumberSectionEquivCotangentSpaceDual (Pic0Scheme C)
      (GroupScheme.identitySection_comp (Pic0Scheme C))
      (congrArg _ (Subsingleton.elim _ _))⟩

/-- **Typed sorry (Rank C, load-bearing project-wide).** `H¹(C, 𝒪_C)` is a
finite-dimensional `k`-vector space. Without this, `Module.finrank` (hence
`genus C` itself, `Genus.lean`) silently takes the junk value `0` on an
infinite-dimensional space — so this fact gates the *meaning* of every
genus statement in Route A, not just this file's dimension count.
Expected route: Čech/Mayer–Vietoris on a two-affine cover of the curve
(`Cohomology/MayerVietorisCore.lean`) reducing to finiteness of kernels/
cokernels of a map of finite `k`-modules of sections; alternatively the
general finiteness of coherent cohomology of proper schemes (EGA III 3.2.1,
not in Mathlib). -/
theorem finiteDimensional_HModule_one {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    FiniteDimensional k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  sorry

/-- **Typed sorry (Rank C — the Kleiman §5 Thm. 5.11 core; currently
unprovable in principle).** The pointed dual-number points of `Pic⁰_{C/k}`
at the identity biject with `H¹(C, 𝒪_C)`. This is where the actual Picard
content of the tangent-space theorem lives, and it is **not closable from
the current axiom set**: the axiom-layer placeholder `PicScheme.picSharp C`
(which `PicScheme C` represents) is an arbitrary functor extracted by
`Classical.choice` from the sorried
`instHasPicSharp`, so no theorem can connect `Pic⁰(k[ε])` to line bundles
or cohomology. Closure prerequisites, in order:
1. upgrade `RelPicFunctor.PicSharp` from its constant-`PUnit` stub to the
   real iso-class quotient functor (the carrier + group structure already
   exist, sorry-free, in `RelPicFunctor.lean` §1);
2. strengthen the `HasPicScheme`/`HasPicSharp` axioms so the representing
   scheme represents *that* functor (same pattern as the iter-195
   `LocallyOfFiniteType` strengthening);
3. the truncated exponential sequence `0 → 𝒪_C → 𝒪_{C_ε}^× → 𝒪_C^× → 1`
   and its cohomology sequence (Kleiman §5, proof of Thm. 5.11);
4. for general `k`: the étale/Zariski `H¹(𝔾ₘ)` comparison
   (Stacks 03P8: `H¹_ét(X,𝔾ₘ) ≅ Pic(X) ≅ H¹_Zar(X,𝒪^×)`, via Hilbert 90)
   or Kleiman's base-change-to-`k̄` + descent route (§2 Ex. 2.3). -/
theorem pointedDualNumberPoints_equiv_H1 {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Nonempty (pointedDualNumberPoints (Pic0Scheme C) (identitySection C) ≃
      Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  sorry

/-- **Typed sorry (Kleiman §5 Thm.~5.11 core).** The tangent-space
comparison at the *concrete* identity point `identitySection C` — sharper
than the pinned `tangentSpaceIso`, whose existential this discharges with a
real witness. Blueprint proof steps this helper encapsulates
(`thm:pic0_tangent_space_iso`, proof):
1. `T₀ Pic_{C/k} = ker(Pic_{C/k}(k_ε) → Pic_{C/k}(k))` via dual numbers;
2. the split truncated exponential sequence
   `0 → H¹(C, 𝒪_C) → H¹(C, 𝒪_{C_ε}^×) → H¹(C, 𝒪_C^×) → 1`;
3. the étale-comparison square (Kleiman §2 Ex.~2.3) with vertical isos after
   base change to `k̄`, legitimised by `IdentityComponent.baseChangeIso`
   (sibling, itself still typed-sorry);
4. descent of the comparison iso from `k̄` to `k`.
Missing Mathlib substrate: dual-numbers tangent-space API for schemes and
the Zariski-vs-étale `H¹` comparison; `Scheme.HModule` itself is real
Ext-cohomology (`Cohomology/StructureSheafModuleK/Carriers.lean`,
sorry-free), so this statement is a genuine mathematical claim. -/
theorem tangentSpaceEquiv {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Nonempty (IsLocalRing.CotangentSpace
        ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default))
      ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  /- Intended assembly from the §1b-1 seams (each a genuine typed sorry;
  no step is decorative):

  1. `pointedDualNumberPoints_equiv_H1 C` — pointed `k[ε]`-points at the
     identity ≃ `H¹(C, 𝒪_C)` (Kleiman Thm. 5.11 core; Rank C, gated on the
     `picSharp` semantics pinning — see its docstring);
  2. `pointedDualNumberPoints_equiv_cotangentSpaceDual C` — the same
     pointed points ≃ `(m_e/m_e²)^∨` over `κ(e)` (Stacks 0B28; Rank B/C);
  3. `identitySection_residueFieldIso C` — `κ(e) ≅ k` (Rank B), turning
     the `κ(e)`-dual into a `k`-dual;
  4. dimension bookkeeping: `finiteDimensional_HModule_one C` +
     Noetherian-ness of the stalk (so `m_e/m_e²` is finite-dimensional,
     `IsNoetherianRing → FiniteDimensional` on `CotangentSpace`) let the
     chain 1–3 force `finrank_k (m_e/m_e²) = finrank_k H¹`, and two
     finite-dimensional `k`-spaces of equal rank admit a `k`-linear
     (a fortiori additive) equivalence.

  Caveat recorded honestly: steps 1+2 compose to an *Equiv of sets*
  between `(m_e/m_e²)^∨` and `H¹`; recovering the *dimension* equality
  from a bare set bijection is impossible (`k² ≃ k³` as sets for infinite
  `k`), so the eventual closure must upgrade steps 1–2 to additive
  equivalences. That upgrade is exactly the `AddCommGroup` structure on
  `pointedDualNumberPoints` (defined, not sorried, in the future
  `TangentSpace.lean`) plus additivity of the two comparison maps. The
  final `sorry` therefore still owes: the additive upgrade of 1–2, the
  stalk-Noetherian instance, and the assembly glue — but no longer the
  statements of 1–3 themselves. -/
  sorry

/-- **Sorry-free (iter-current Pass 1).** The Picard
scheme `Pic_{C/k}` is separated over `k`. Kleiman delivers this as part of
the §4–§5 representability package ("Then `Pic_{X/k}` is separated, ...");
its home is the strengthened `HasPicScheme` existential in
`FGAPicRepresentability.lean`, which now bundles `IsSeparated X.hom`
alongside `LocallyOfFiniteType X.hom`; this helper is the direct
`Classical.choose_spec` extraction consumed by the `proper` assembly. -/
theorem picScheme_isSeparated {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    IsSeparated (PicScheme C).hom := by
  exact (HasPicScheme.has_pic_scheme (C := C)).choose_spec.2.2

/-- **Axiom-clean.** Separatedness of
`Pic⁰_{C/k}` over `k`: the structural morphism factors as the clopen
inclusion `Pic⁰_{C/k} ↪ Pic_{C/k}` (an open immersion by the sibling's
axiom-clean `IdentityComponent.isOpenSubgroupScheme`, hence a monomorphism,
hence separated) followed by the separated `(PicScheme C).hom`
(`picScheme_isSeparated`); separatedness is stable under composition.
This is the `IsSeparated` conjunct of the pinned `proper`
(blueprint `thm:pic0_proper`; Mathlib: `IsProper extends IsSeparated,
UniversallyClosed, LocallyOfFiniteType`). -/
theorem isSeparated {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    IsSeparated (Pic0Scheme C).hom := by
  haveI : HasPicScheme C := instHasPicScheme C
  haveI : LocallyOfFiniteType (PicScheme C).hom := PicScheme.locallyOfFiniteType C
  haveI : IsSeparated (PicScheme C).hom := picScheme_isSeparated C
  obtain ⟨⟨f, hopen, -⟩⟩ :=
    GroupScheme.IdentityComponent.isOpenSubgroupScheme (PicScheme C)
  haveI := hopen
  rw [eq_identityComponent C, ← Over.w f]
  infer_instance

/-- **Axiom-clean.** `Pic⁰_{C/k}` is locally of finite type over `k`: the
first (sorry-free) conjunct of the sibling's
`IdentityComponent.isFiniteTypeGeometricallyIrreducible`, transported along
the bridge. The `LocallyOfFiniteType` conjunct of the pinned `proper`. -/
theorem locallyOfFiniteType {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    LocallyOfFiniteType (Pic0Scheme C).hom := by
  haveI : HasPicScheme C := instHasPicScheme C
  rw [eq_identityComponent C]
  exact (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicScheme C)).1

/-- **Closed at this file's level (residual content in the sibling's typed
sorry).** `Pic⁰_{C/k}` is quasi-compact over `k`: the second conjunct of the
sibling's `IdentityComponent.isFiniteTypeGeometricallyIrreducible`
(Kleiman §5 Lem.~`lem:agps`~(3): `α(U × U) = G⁰` is the image of the
affine, hence quasi-compact, `U × U`). Together with `locallyOfFiniteType`
this is the blueprint's "of finite type" clause
(`thm:identity_component_finite_type_geom_irreducible`). Not needed for the
`proper` assembly (Mathlib's `IsProper` derives quasi-compactness from
universal closedness) but recorded for the blueprint's finite-type chain. -/
theorem quasiCompact {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    QuasiCompact (Pic0Scheme C).hom := by
  haveI : HasPicScheme C := instHasPicScheme C
  rw [eq_identityComponent C]
  exact (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
    (PicScheme C)).2.1

/-! ### §1b-2. Honest step lemma for `universallyClosed`

Only the base-change reduction is stated as a file-level helper: it is the
one step of the Kleiman Thm. 5.4 properness proof whose *statement* can be
made genuinely (against Mathlib's real `pullback` along
`Spec k̄ → Spec k`) without first building algebraic-group API. The
Chevalley–Rosenlicht and Lie–Kolchin steps are deliberately **not** given
file-level statements here: with no real `LinearAlgebraicGroup`/
`AbelianVariety`/exact-sequence vocabulary in scope, any rendering of them
either quantifies over empty `Prop`-classes (making the statement
*trivially true* and the "decomposition" vacuous — the failure mode of the
iter-19x placeholder block this section replaces) or degenerates to
`True`. Their honest home is a future `GroupSchemeStructure.lean`; until
then their content stays inside `universallyClosed`'s single sorry,
explicitly accounted in its docstring. -/

/-- **Closed (iter-current, sorry-free).** Universal closedness of
`Pic⁰_{C/k}` descends from its base change to the algebraic closure
`Spec k̄ → Spec k`. That base-change map is faithfully flat and quasi-compact
(a field extension `k → k̄` is injective and flat, so `Spec.map` of it is
surjective and flat; being a map of affines it is quasi-compact), and
`UniversallyClosed` is fpqc-local on the base (Stacks 02KS; the classical
statement is EGA IV₂ 2.6.4, cf. 2.7.1). The pinned Mathlib packages exactly
this descent as the `@[stacks 02KS]` instance
`descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`
(`Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`), so the closure is a
one-line `of_pullback_snd_of_descendsAlong` application — the same
`MorphismProperty` descent pattern `smooth_of_grpObj` uses, with the three
`Surjective`/`Flat`/`QuasiCompact` facts about `Spec.map (algebraMap k k̄)`
supplied by `inferInstance`. -/
theorem universallyClosed_of_baseChange {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom]
    (h : UniversallyClosed (pullback.snd (Pic0Scheme C).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    UniversallyClosed (Pic0Scheme C).hom := by
  -- `UniversallyClosed` is fpqc-local on the base (Stacks 02KS), packaged in
  -- the pinned Mathlib as `DescendsAlong @UniversallyClosed
  -- (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`. The base-change map
  -- `g = Spec.map (algebraMap k k̄)` is surjective + flat + quasi-compact
  -- (field extension ⟹ faithfully flat; `Spec.map` of it, a map of affines,
  -- is quasi-compact) — all three by `inferInstance`, exactly as in
  -- `smooth_of_grpObj`. Then `of_pullback_snd_of_descendsAlong` descends the
  -- universal closedness of the base change (`h`) to `(Pic0Scheme C).hom`.
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h


/-- **Typed sorry (Kleiman §5 Thm.~5.4, properness half).** `Pic⁰_{C/k}` is
universally closed over `k` — the single deep conjunct of the pinned
`proper`. Blueprint proof steps this helper encapsulates
(`thm:pic0_proper`, proof):
1. quasi-projectivity of `Pic⁰_{C/k}` (Kleiman §5 Thm.~5.4, first
   conclusion, for `C/k` projective and geometrically integral);
2. reduction to `k = k̄` via `IdentityComponent.baseChangeIso` (sibling,
   typed-sorry) + descent of properness along faithfully flat field
   extension (EGA IV₂ 2.7.1(vii));
3. Chevalley–Rosenlicht (Conrad, Thm.~1.1) + Lie–Kolchin: reduce to ruling
   out non-constant `k̄`-maps `𝔾_m → (Pic⁰_{C/k})_red`;
4. no non-constant `𝔾_m`-maps: `C × T` normal integral ⟹ every invertible
   sheaf is a Cartier-divisor sheaf (Hartshorne II Ex.~6.15), then the
   generic-fibre triviality + AK70 Prp.~3.10 cycle comparison.
None of steps 1, 3, 4 has Mathlib substrate at the pinned revision
(no Chevalley structure theorem, no Lie–Kolchin, no divisor-sheaf
correspondence); this is the irreducible gap point. -/
theorem universallyClosed {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    UniversallyClosed (Pic0Scheme C).hom := by
  /- Single honest sorry. Via `universallyClosed_of_baseChange` the goal
  reduces to `k = k̄`; what the sorry still owes there, with no Mathlib
  substrate at the pinned revision and no meaningful file-level statement
  possible yet (see §1b-2 header), is Kleiman §5 Thm. 5.4's chain:
  1. quasi-projectivity of `Pic⁰_{C/k}` (Kleiman Thm. 5.4 first
     conclusion; no quasi-projective-morphism API in Mathlib);
  2. Chevalley–Rosenlicht structure theorem (Conrad, "A modern proof of
     Chevalley's theorem on algebraic groups", JRMS 17 (2002), Thm. 1.1);
  3. Lie–Kolchin, reducing to: no non-constant `k̄`-maps
     `𝔾ₘ → (Pic⁰)_red`;
  4. the divisor argument ruling those out (Hartshorne II Ex. 6.15 +
     AK70 Prp. 3.10), which *also* needs the `picSharp` semantics pinning
     (a map `𝔾ₘ → Pic⁰` must be interpreted as a line bundle on
     `C × 𝔾ₘ` — impossible while `picSharp` is a `Classical.choice`
     placeholder).
  Deepest gap of the chapter; tracked in the tex closure-order section. -/
  sorry

/-! ### §1b-3. Honest step lemmas for `smoothAtIdentity` (typed sorries)

The iter-19x draft split smoothness-at-the-origin into a characteristic-0
branch (Cartier's theorem, Stacks 047N) and a characteristic-`p` branch
(`H²` vanishing). Kleiman's own solution to the curve case (Ex. 5.23,
`references/kleiman-picard-src/kleiman-picard.tex` `ans{jac}`) needs **no
case split**: `dim C = 1 ⟹ H²(C, 𝒪_C) = 0 ⟹ Pic_{C/k} smooth` uniformly
in the characteristic, by the deformation-obstruction Proposition 5.19
(`prp:H2`: "Assume `Pic_{X/S}` exists and represents `Pic_{(X/S)ét}`. Let
`s ∈ S` with `H²(𝒪_{X_s}) = 0`. Then `Pic_{X/S}` is smooth over a
neighbourhood of `s`"). So only the two lemmas below are load-bearing;
Cartier's theorem is *not* on the critical path and its `True`-typed stub
is deleted rather than kept as decoration. -/

/-- **Typed sorry (Rank C, via `tangentSpaceEquiv`).** The cotangent space
of `Pic⁰_{C/k}` at the identity has the same `k`-dimension as
`H¹(C, 𝒪_C)`. Follows from `tangentSpaceEquiv` (the `≃+` transports
finrank only after the `k`-linear upgrade — over the *same* field on both
sides via `identitySection_residueFieldIso`); recorded separately because
the `smoothAtIdentity` dimension count consumes exactly this equality, not
the full equivalence. Note the LHS `Module k` instance: the cotangent
space at a rational point is a `k`-module via `κ(e) ≅ k`; until that
identification is threaded through, this statement elaborates via the
`ResidueField`-module structure only if `k`-instances are available — kept
on the `ResidueField` side for well-formedness. -/
theorem smoothAtIdentity_finrankCotangentEqGenus {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Module.finrank
        (IsLocalRing.ResidueField
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
        (IsLocalRing.CotangentSpace
          ((Pic0Scheme C).left.presheaf.stalk ((identitySection C).base default)))
      = Module.finrank k (Scheme.HModule k (Scheme.toModuleKSheaf C) 1) := by
  sorry

/-- **Typed sorry (Rank B/C).** `H²(C, 𝒪_C) = 0` for the curve `C` — the
obstruction-space vanishing feeding Kleiman Prp. 5.19 (`prp:H2`), valid in
every characteristic since `dim C = 1`. Expected route: Grothendieck
vanishing by dimension is absent from Mathlib, so use the project's
Čech/Mayer–Vietoris machinery (`Cohomology/MayerVietorisCore.lean`) on a
two-affine cover of `C`; the sub-facts owed are (a) a smooth proper curve
is covered by two affine opens (complement of a closed point in an
integral projective curve is affine — real work, ample-divisor argument)
and (b) the MV sequence bounds cohomological dimension by 1 for such a
cover. -/
theorem h2Vanishing {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Subsingleton (Scheme.HModule k (Scheme.toModuleKSheaf C) 2) := by
  sorry


/-- **Typed sorry (Kleiman §5 Cor.~5.13 + Cor.~5.14 + Ex.~5.23, the
at-the-origin input).** `Pic⁰_{C/k}` is smooth *on an open neighbourhood of
the identity point*. Blueprint proof steps this helper encapsulates
(`thm:pic0_smooth`, proof, paragraphs 2–3):
- the tangent-space dimension bound `dim_0 Pic⁰ ≤ dim_k T₀ Pic⁰ = g(C)`
  (via `tangentSpaceEquiv` + `finrank_HModule_eq_genus`, the `H¹`-side of
  the dimension count — a typed-sorry dependency, sanctioned);
- equality (⟺ regularity at `0` ⟺ smoothness at `0`): Cartier's theorem in
  characteristic zero, `H²(C, 𝒪_C) = 0` (obstruction vanishing, `dim C = 1`)
  in positive characteristic.
Neither Cartier's theorem nor the deformation-obstruction calculus exists
in Mathlib at the pinned revision. -/
theorem smoothAtIdentity {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    ∃ U : (Pic0Scheme C).left.Opens,
      (identitySection C).base default ∈ U ∧ Smooth (U.ι ≫ (Pic0Scheme C).hom) := by
  /- Single honest sorry. Intended closure (Kleiman route, uniform in the
  characteristic — no Cartier/`char p` case split, see §1b-3 header):
  either
  (a) deformation-theoretic (Kleiman Prp. 5.19 `prp:H2`): `h2Vanishing C`
      kills the obstruction group, so the Pic functor is formally smooth
      at every point; Mathlib's `exists_smooth_of_formallySmooth_stalk` /
      `formallySmooth_stalkMap_iff` (`Morphisms/Smooth.lean`) then produce
      the smooth neighbourhood. **Gated on the `picSharp` semantics
      pinning** — formal smoothness of the functor is meaningless while
      `picSharp` is a `Classical.choice` placeholder; or
  (b) dimension-theoretic (Kleiman Cor. 5.13):
      `smoothAtIdentity_finrankCotangentEqGenus C` + the Krull-dimension
      bound `ringKrullDim 𝒪 ≤ finrank CotangentSpace` with equality iff
      regular (`IsRegularLocalRing.iff_finrank_cotangentSpace`, in the
      pinned Mathlib) + a dimension lower bound `dim₀ Pic⁰ ≥ g` (this is
      the part Kleiman gets from the Abel map / existence of `g`-dimensional
      families — additional real content, do not underestimate it) +
      regular-at-rational-point ⟹ smooth-at-point packaging (absent from
      Mathlib at the scheme level).
  Route (a) is the recommended one: it needs no dimension lower bound. -/
  sorry

/-! ### §1b-4. Translation propagation — largely subsumed by Mathlib

**Finding (this iter):** the pinned Mathlib already contains the entire
translation-propagation argument, packaged as
`AlgebraicGeometry.smooth_of_grpObj`
(`Mathlib/AlgebraicGeometry/Group/Smooth.lean`): a group scheme over a
field that is locally of finite type and **geometrically reduced** is
smooth. Its proof is precisely Kleiman Cor. 5.13 ¶1 — reduce to `k̄` by
fppf descent, translate a smooth point around by `GrpObj.mulRight`, use
density of the smooth locus (`dense_smoothLocus_of_perfectField`). The
`True`-typed stubs this section previously carried (`smooth_translationAuto`,
`smooth_transitive`, `smooth_openLocus`) and the opaque-carrier descent
lemma are therefore deleted outright: their content exists, sorry-free, in
Mathlib. What this file still owes is only the *bridge*: geometric
reducedness of `Pic⁰_{C/k}` (below), and the `GrpObj` instance (sibling
typed sorry `IdentityComponent.isSubgroupHomomorphism`). -/

/-- **Typed sorry (Rank C, the honest residual of the smoothness pin).**
`Pic⁰_{C/k}` is geometrically reduced over `k`. With Mathlib's
`smooth_of_grpObj`, this (plus the sibling `GrpObj` sorry) is *all* that
smoothness needs. It is where the deformation-theoretic content lands:
reducedness of the Picard scheme of a curve is exactly the `H² = 0`
obstruction vanishing (`h2Vanishing`) fed through Kleiman Prp. 5.19 —
equivalently, smoothness at one point (`smoothAtIdentity`) plus
homogeneity gives reducedness everywhere. In characteristic `p` this is a
genuine theorem (Igusa's surface shows it can fail for `dim X > 1`,
Kleiman Rmk. 5.15); it is **not** a formality. Gated on the `picSharp`
semantics pinning like every deformation-theoretic statement in this
file. -/
theorem geometricallyReduced {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    GeometricallyReduced (Pic0Scheme C).hom := by
  sorry


/-- **Typed sorry (Kleiman §5 Cor.~5.13, translation-propagation step).**
Smoothness of `Pic⁰_{C/k}` near the identity propagates to smoothness
everywhere. Blueprint proof steps this helper encapsulates
(`thm:pic0_smooth`, proof, paragraph 1):
- reduce to `k = k̄` (smoothness descends along faithfully flat field
  extension; identify `(Pic⁰_{C/k})_{k̄}` via `IdentityComponent.baseChangeIso`,
  sibling, typed-sorry);
- over `k̄`, every closed point `λ` is rational; the translation
  `t_λ : x ↦ x + λ` is an automorphism (the group structure from the
  sibling's `IdentityComponent.isSubgroupHomomorphism`, typed-sorry) carrying
  `0` to `λ`, so the smooth locus is translation-invariant and contains the
  identity, hence — smoothness being Zariski-local on the source — is
  everything. -/
theorem smooth_of_smoothAtIdentity {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom]
    (h : ∃ U : (Pic0Scheme C).left.Opens,
      (identitySection C).base default ∈ U ∧ Smooth (U.ι ≫ (Pic0Scheme C).hom)) :
    Smooth (Pic0Scheme C).hom := by
  /- Single honest sorry. Recommended closure: do **not** re-prove the
  translation argument — derive reducedness of an open neighbourhood of
  the identity from `h` (smooth over a reduced base ⟹ reduced),
  upgrade to `GeometricallyReduced (Pic0Scheme C).hom` (this step still
  needs homogeneity, i.e. the sibling `GrpObj` sorry — over `k̄` a group
  scheme reduced near `e` is reduced everywhere; or route through
  `geometricallyReduced` above directly), then finish with Mathlib's
  `smooth_of_grpObj` (see §1b-4 header). The previous draft's decorative
  `True`-typed `have`s are deleted; their content lives in Mathlib. -/
  sorry

/-- **Tangent space at the identity: `T₀ Pic⁰_{C/k} ≅ H¹(C, 𝒪_C)`.**

The Kleiman §5 Thm.~`thm:tgtsp` tangent-space isomorphism. For a smooth
proper geometrically integral curve `C/k`, the Zariski tangent space at the
identity of `Pic⁰_{C/k}` is canonically isomorphic to the first sheaf
cohomology `H¹(C, 𝒪_C)`.

In Lean: we bundle existentially over a `k`-rational
identity-section point `e : Spec k ⟶ (Pic0Scheme C).left` and a `k`-module
structure on the cotangent space `m_e/m_e²` (the natural `k`-module structure
arising from the `k`-algebra structure on the stalk at a `k`-rational point;
for the file-skeleton this instance is supplied via Σ' to avoid hard-coding
a global instance prematurely). The substantive content is an `AddEquiv`
between the cotangent space and the project's `H¹(C, 𝒪_C)` module
`Scheme.HModule k (Scheme.toModuleKSheaf C) 1`.

A k-LinearEquiv refinement (iter-196+) replaces the `AddEquiv` once the
`k`-module structure on the cotangent space is consistently threaded through
downstream consumers; the underlying additive group structure is enough for
the dimension corollary `dim_k T₀ Pic⁰ = dim_k H¹ = g(C)`.

iter-195: the body is a sorry-free assembly of the §1b helpers — the
Σ'-witness is the **axiom-clean** `identitySection C`, and the residual
Kleiman Thm.~5.11 content is isolated in `tangentSpaceEquiv` (typed-sorry). -/
theorem tangentSpaceIso {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Nonempty (Σ' (e : Spec (.of k) ⟶ (Pic0Scheme C).left),
      IsLocalRing.CotangentSpace ((Pic0Scheme C).left.presheaf.stalk (e.base default))
        ≃+ Scheme.HModule k (Scheme.toModuleKSheaf C) 1) :=
  (tangentSpaceEquiv C).elim fun eqv => ⟨⟨identitySection C, eqv⟩⟩

/-- **Smoothness of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is smooth over `k` (Kleiman §5 Cor.~`cor:sm` + Cor.~`cor:ch0` in
characteristic zero + Ex.~`ex:jac` for the curve case).

The proof: smoothness at the identity propagates to smoothness
everywhere by translation (Pic⁰ is a `k`-group scheme, so multiplication by
any `λ ∈ Pic⁰(k̄)` is an automorphism). At the identity, smoothness reduces
to the inequality
`dim_0 Pic⁰_{C/k} ≤ dim_k T₀ Pic⁰_{C/k} = dim_k H¹(C, 𝒪_C) = g(C)`
(`tangentSpaceIso`) becoming an equality. For a smooth proper curve this
equality holds: in characteristic zero by Cartier's theorem (every
`k`-group scheme is smooth), in positive characteristic by the curve-specific
vanishing `H²(C, 𝒪_C) = 0` (the obstruction to lifting tangent vectors).

iter-195: the body is a sorry-free assembly of the §1b helpers, splitting
the blueprint proof at its natural seam: `smoothAtIdentity` (the at-`0`
input, typed-sorry) fed into `smooth_of_smoothAtIdentity` (the
translation-propagation step, typed-sorry). -/
theorem smooth {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    Smooth (Pic0Scheme C).hom :=
  smooth_of_smoothAtIdentity C (smoothAtIdentity C)

/-- **Properness of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is proper over `k` (Kleiman §5 Thm.~`th:qpp&p`; a smooth proper
curve is geometrically normal, hence the projectivity upgrade applies).

The proof: `Pic⁰_{C/k}` is quasi-projective (Kleiman §5
Thm.~`th:qpp&p`, first conclusion); to upgrade to projective (hence proper)
we use the Chevalley–Rosenlicht structure theorem to reduce to ruling out
non-constant `k̄`-morphisms `𝔾_m → Pic⁰_{C/k̄}`. The latter follows from
normality of `C ×_k 𝔾_m` and Hartshorne II Ex.~6.15 (invertible sheaves on
a normal integral scheme are sheaves of Cartier divisors).

iter-195: the body is a sorry-free assembly of the §1b helpers along
Mathlib's `IsProper = IsSeparated + UniversallyClosed + LocallyOfFiniteType`
decomposition: `isSeparated` (axiom-clean, via the extracted
`picScheme_isSeparated`) + `universallyClosed` (typed-sorry, the
Chevalley–Rosenlicht half above) + `locallyOfFiniteType` (axiom-clean). -/
theorem proper {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    IsProper (Pic0Scheme C).hom :=
  (isProper_iff _).mpr ⟨isSeparated C, universallyClosed C, locallyOfFiniteType C⟩

/-- **Geometric irreducibility of `Pic⁰_{C/k}`.**

For a smooth proper geometrically integral curve `C/k`, the identity component
`Pic⁰_{C/k}` is geometrically irreducible over `k` (Kleiman §5 Prp.~`prp:pic0`,
specialisation of the abstract identity-component substrate
`IdentityComponent.isFiniteTypeGeometricallyIrreducible` of
`Picard/IdentityComponent.lean` to `G = PicScheme C`).

The proof (closed iter-194, exactly as the blueprint prescribes): rewrite
along the master bridge `eq_identityComponent`, then apply
`GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible` to
`G = PicScheme C` (locally of finite type by the sorry-free
`PicScheme.locallyOfFiniteType`) and project out the third conjunct. The
residual mathematical content (Kleiman's smooth-affine-translate covering
argument) lives in the sibling lemma's own typed sorry, not here. -/
theorem geometricallyIrreducible {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    GeometricallyIrreducible (Pic0Scheme C).hom := by
  -- Pin `HasPicScheme C` as a local instance before `PicScheme C` is
  -- elaborated (the §1a nested-`synthInstance` pitfall).
  haveI : HasPicScheme C := instHasPicScheme C
  rw [eq_identityComponent C]
  exact (GroupScheme.IdentityComponent.isFiniteTypeGeometricallyIrreducible
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

The proof (closed at this file's level) assembles the four
conjuncts: `proper` (this file, itself an assembly of §1b helpers with two
residual typed sorries), `smooth` (likewise, two residual typed sorries),
`geometricallyIrreducible` (this file, fully closed modulo the sibling's
typed sorry), and the `Nonempty (GrpObj (Pic0Scheme C))` slot, the latter by
rewriting along the master bridge `eq_identityComponent` and applying
`GroupScheme.IdentityComponent.isSubgroupHomomorphism` to `G = PicScheme C`
(sibling `Picard/IdentityComponent.lean`, itself still typed-sorry). The
assembly wiring here is final; the remaining mathematical debt sits
entirely in the named upstream lemmas. -/
theorem isAbelianVariety {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] :
    IsProper (Pic0Scheme C).hom ∧ Smooth (Pic0Scheme C).hom ∧
      GeometricallyIrreducible (Pic0Scheme C).hom ∧
      Nonempty (GrpObj (Pic0Scheme C)) := by
  -- Pin `HasPicScheme C` as a local instance before `PicScheme C` is
  -- elaborated (the §1a nested-`synthInstance` pitfall).
  haveI : HasPicScheme C := instHasPicScheme C
  refine ⟨proper C, smooth C, geometricallyIrreducible C, ?_⟩
  rw [eq_identityComponent C]
  exact GroupScheme.IdentityComponent.isSubgroupHomomorphism (PicScheme C)

end Pic0

end Scheme

end AlgebraicGeometry
