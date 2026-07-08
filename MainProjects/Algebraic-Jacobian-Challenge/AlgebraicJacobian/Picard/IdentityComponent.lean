/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.FGAPicRepresentability
import AlgebraicJacobian.Picard.GeometricallyConnectedSection
import AlgebraicJacobian.Genus

/-!
# The identity component of the Picard scheme (A.3)

This file is the **A.3** sub-build chapter for the project's positive-genus arm
of `nonempty_jacobianWitness`. It scaffolds the abstract identity-component
substrate for a `k`-group scheme locally of finite type and specialises it to
`G = Pic_{C/k}`, packaging:

1. the open-and-closed subgroup-scheme structure of the identity component,
2. the degree map `Pic_{C/k}(k) → ℤ`,
3. the abelian-variety identification of `Pic⁰_{C/k}` (the Jacobian variety
   of `C` when `C/k` is a smooth proper geometrically integral curve of
   positive genus).

## Status (run 0009, T6 session)

The §1 group-scheme substrate is fully proved: `IdentityComponent`,
`isOpenSubgroupScheme`, `isSubgroupHomomorphism` (Yoneda subgroup-presheaf
route), `isFiniteTypeGeometricallyIrreducible` (run 0009: Kleiman's
translation argument over the algebraic closure — closed-point translation
via `GrpObj.mulRight` and `pointEquivClosedPoint`, Jacobson density,
EGA I 6.1.10, then descent along the surjective base-change projection via
`baseChangeIso`; the previous claim that this needed EGA IV₂ 4.6.1-type
input absent from Mathlib was stale) and `baseChangeIso` are sorry-free.
Remaining sorries (3): `degree` / `finrank_eq_genus` /
`kPoints_iff_kerDegree` of §3–§4, which inherit the typed-sorry FGA
representability foundation (`Picard/FGAPicRepresentability.lean`) and
cannot be axiom-clean before `AJC.picrep` lands.
`Pic0Scheme.isAbelianVariety` MOVED to sibling
`Picard/Pic0AbelianVariety.lean` (run 0008), where it is assembled from
the per-conjunct theorems of that chapter.

The 5 blueprint-pinned declarations are:

1. `AlgebraicGeometry.GroupScheme.IdentityComponent` (def, ~5 LOC) — the
   **identity component** `G^0` of a `k`-group scheme `G` locally of finite
   type, as a `k`-scheme (an `Over (Spec k)`-object). Abstract substrate
   reusable outside the Picard context; not yet in Mathlib.
2. `AlgebraicGeometry.GroupScheme.IdentityComponent.isOpenSubgroupScheme`
   (theorem, ~10 LOC) — the bundled statement that `G^0` is an open and
   closed subscheme of `G` via an open immersion `G^0 ↪ G`.
3. `AlgebraicGeometry.Scheme.Pic0Scheme` (def, ~5 LOC) — the **identity
   component of the Picard scheme** `Pic⁰_{C/k}`, obtained by applying
   `IdentityComponent` to `G = PicScheme C`.
4. `AlgebraicGeometry.Scheme.PicScheme.degree` (def, ~5 LOC) — the **degree
   map** `Pic_{C/k}(k) → ℤ`, extracting the leading coefficient of the
   Hilbert polynomial of a representing invertible sheaf relative to a fixed
   degree-one polarisation `O_C(1)`.
5. `AlgebraicGeometry.Scheme.Pic0Scheme.isAbelianVariety` (theorem, ~10 LOC)
   — the **abelian-variety identification** of `Pic⁰_{C/k}`: smooth, proper,
   geometrically irreducible `k`-group scheme of dimension `g(C)` --- the
   Jacobian variety of `C`.

## Note on type expressivity

Following the project rule "Never weaken the type to dodge the proof", each
pinned declaration carries a substantive, non-tautological type:

- `IdentityComponent G : Over (Spec (.of k))` — a `k`-scheme, not the
  tautological `G` itself.
- `IdentityComponent.isOpenSubgroupScheme G` — asserts the *existence* of an
  open immersion morphism `IdentityComponent G ⟶ G` whose underlying map of
  schemes is both an open and a closed immersion (clopen subscheme).
- `Pic0Scheme C : Over (Spec (.of k))` — a `k`-scheme.
- `PicScheme.degree C : (Spec (.of k) ⟶ (PicScheme C).left) → ℤ` —
  a genuine function from `k`-points to `ℤ`, not a constant.
- `Pic0Scheme.isAbelianVariety C` — asserts the conjunction of the four
  abelian-variety properties (proper, smooth, geometrically irreducible,
  group-object structure); not vacuous because each conjunct is a genuine
  property/structure on the (typed-sorry) `Pic0Scheme C`.

## References

Blueprint: `blueprint/src/chapters/Picard_IdentityComponent.tex` (560 LOC,
5 pins). Sources:
- Kleiman, "The Picard scheme", §5, Lem.~`lem:agps` (identity component
  substrate) + Prp.~`prp:pic0` (specialisation to `Pic_{C/k}`) +
  Thm.~`th:qpp&p` (quasi-projectivity/projectivity) + Cor.~`cor:sm`
  (smoothness/dimension) + Ex.~`ex:jac` + Rmk.~`rmk:Jac`
  (arXiv:math/0504020 pp. 36, 38, 47, 50–51);
- Milne, "Abelian Varieties" (course notes, 2008), §III.1
  (def. of abelian variety, p. 8; dimension equals genus, Rmk. III.1.4(e),
  p. 86).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## §1. The identity component of a group scheme — abstract substrate

The identity component is an abstract feature of `k`-group schemes locally of
finite type. We package the definition + open-and-closed-subgroup-scheme
structure in the `GroupScheme` namespace so they are reusable outside the
Picard context.

In this project, a "`k`-group scheme" is encoded as an
`Over (Spec (.of k))`-object `G` carrying a `[GrpObj G]` instance (the
group-object structure in the over-category). The locally-of-finite-type
hypothesis is the `[LocallyOfFiniteType G.hom]` instance on the structural
morphism to the base.

Blueprint references: `def:identity_component_group_scheme` +
`thm:identity_component_open_subgroup` (Kleiman §5 Lem.~`lem:agps`). -/

namespace GroupScheme

/-- Helper (iter-188): in a **Noetherian** topological space `α`, the set of
connected components is finite.

Proof: the map `irreducibleComponents α → ConnectedComponents α` sending each
irreducible component `C` to the connected component of an arbitrary chosen
point of `C` is well-defined (because `C` is preconnected, hence contained in
a single connected component) and surjective (because every point lies in
some irreducible component, namely `irreducibleComponent x`, which is a
subset of `connectedComponent x`). The source is finite by
`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`, so the
target is finite by `Finite.of_surjective`. -/
private lemma noetherianSpace_finite_connectedComponents
    {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α] :
    Finite (ConnectedComponents α) := by
  classical
  have hfin : (irreducibleComponents α).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  haveI : Finite ↥(irreducibleComponents α) := hfin.to_subtype
  refine Finite.of_surjective
    (fun C : ↥(irreducibleComponents α) =>
      (ConnectedComponents.mk : α → ConnectedComponents α)
        ((C.property : Maximal IsIrreducible C.val).prop.nonempty.some)) ?_
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  rw [ConnectedComponents.coe_eq_coe]
  refine (connectedComponent_eq ?_).symm
  exact irreducibleComponent_subset_connectedComponent
    (isIrreducible_irreducibleComponent (x := x)).nonempty.some_mem

/-- Helper (iter-188): in a **Noetherian** topological space `α`, each
connected component is open.

Proof: `ConnectedComponents α` is totally disconnected
(`ConnectedComponents.totallyDisconnectedSpace`), hence T1
(`TotallyDisconnectedSpace.t1Space`), and finite by
`noetherianSpace_finite_connectedComponents`. A finite T1 space is discrete
(`Finite.instDiscreteTopology`), so the singleton
`{ConnectedComponents.mk x}` is open in the quotient. The preimage of this
singleton under the continuous quotient map `ConnectedComponents.mk` is
`connectedComponent x` (`connectedComponents_preimage_singleton`), which is
therefore open. -/
private lemma noetherianSpace_isOpen_connectedComponent
    {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α]
    (x : α) :
    IsOpen (connectedComponent x) := by
  haveI : Finite (ConnectedComponents α) := noetherianSpace_finite_connectedComponents
  haveI : DiscreteTopology (ConnectedComponents α) := inferInstance
  have h := (isOpen_discrete
    ({(ConnectedComponents.mk x : ConnectedComponents α)} : Set _)).preimage
    ConnectedComponents.continuous_coe
  rwa [connectedComponents_preimage_singleton] at h

/-- Helper (iter-188): the **`LocallyConnectedSpace` instance** for the
underlying topological space of a `k`-scheme `G.left` whose structural
morphism `G.hom : G.left ⟶ Spec k` is locally of finite type.

The substantive content is EGA I 6.1.9: a locally Noetherian topological
space has open connected components — equivalently, is locally connected.
Pushed through the chain: `Spec k` is Noetherian (a field has Noetherian
spectrum); `LocallyOfFiniteType G.hom + IsLocallyNoetherian (Spec k) ⟹
IsLocallyNoetherian G.left` (Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`); and the
implication `IsLocallyNoetherian X ⟹ LocallyConnectedSpace X.toTopCat`
is the iter-188 project-side helper (`noetherianSpace_finite_connectedComponents`
+ `noetherianSpace_isOpen_connectedComponent`).

The classical proof: each point `y ∈ G.left` has an open affine
neighbourhood `W = Spec R` with `R` Noetherian, hence `|W|` is a Noetherian
topological space; in a Noetherian space, each `connectedComponent y` is
clopen (finite irreducible components ⟹ finite connected components ⟹
finite T1 quotient ⟹ discrete quotient ⟹ singletons clopen in quotient ⟹
preimages clopen). Pulled back along the open inclusion `W ↪ G.left`,
this gives an open connected neighbourhood of `y` inside any open `F`
containing `y`. -/
private instance identityComponent_locallyConnectedSpace
    {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [LocallyOfFiniteType G.hom] :
    LocallyConnectedSpace G.left := by
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x F hF
  -- Extract an open neighbourhood `T ⊆ F` of `x`.
  obtain ⟨T, hTF, hT, hxT⟩ := mem_nhds_iff.mp hF
  -- Find an affine open `W ⊆ T` with `x ∈ W`.
  obtain ⟨W, hW, hxW, hWT⟩ :=
    exists_isAffineOpen_mem_and_subset (X := G.left) (U := ⟨T, hT⟩) hxT
  haveI : IsNoetherianRing Γ(G.left, W) :=
    IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  haveI hNoethW : TopologicalSpace.NoetherianSpace ↥W :=
    noetherianSpace_of_isAffineOpen W hW
  -- Inside `W` (Noetherian) the connected component of `x` is open; its image
  -- under the open inclusion `W ↪ G.left` is the connected open neighbourhood
  -- we want.
  let xW : ↥W := ⟨x, hxW⟩
  refine ⟨(Subtype.val : ↥W → G.left) '' connectedComponent xW, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact hTF (hWT z.2)
  · exact W.isOpen.isOpenMap_subtype_val _
      (noetherianSpace_isOpen_connectedComponent xW)
  · exact ⟨xW, mem_connectedComponent, rfl⟩
  · exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn

/-- The image of the identity section `e : Spec k → G` (well-defined as a
single point of `|G|` because `Spec k` is a topological singleton). -/
private noncomputable def identitySectionPoint
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] : G.left :=
  ((MonObj.one (X := G)).left.base :
      ↥(Spec (.of k)) → G.left) (default : Spec (.of k))

/-- Helper (iter-186; iter-187 closed): the **clopen carrier `Set`** of
the identity component of a `k`-group scheme `G` locally of finite type,
packaged as a `G.left.Opens`. The carrier set is `connectedComponent x`
for `x = e(*)` the image of the identity section
(`identitySectionPoint G`); openness is `isOpen_connectedComponent` which
needs the `identityComponent_locallyConnectedSpace` instance above
(EGA I 6.1.9). -/
private noncomputable def identityComponentCarrier {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    G.left.Opens :=
  ⟨connectedComponent (identitySectionPoint G), isOpen_connectedComponent⟩

/-- The **identity component** `G^0` of a `k`-group scheme `G` locally of
finite type.

Encoded as a `k`-scheme: an object of `Over (Spec (.of k))`, carrying the
intended substantive identity "this is the connected component of `|G|`
containing the identity section `e`, equipped with the open-subscheme
structure inherited from `G`". The associated open immersion
`IdentityComponent G ⟶ G` is the content of
`IdentityComponent.isOpenSubgroupScheme`.

iter-186 body: built from the `identityComponentCarrier G` helper — the
open subscheme of `G` whose underlying topological space is the connected
component of `|G|` through the image of the identity section. The
structure morphism is the inherited `(identityComponentCarrier G).ι ≫ G.hom`.
The substantive content (the actual carrier `Set`, plus its openness from
EGA I 6.1.9: locally Noetherian spaces have open connected components)
lives in the typed-sorry body of `identityComponentCarrier`. -/
noncomputable def IdentityComponent {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    Over (Spec (.of k)) :=
  Over.mk ((identityComponentCarrier G).ι ≫ G.hom)

/-- **The identity component is an open and closed subgroup scheme.**

The bundled statement of Kleiman §5 Lem.~`lem:agps`~(3): the identity
component `G^0 = IdentityComponent G` of a `k`-group scheme `G` locally of
finite type comes with a morphism `IdentityComponent G ⟶ G` (in
`Over (Spec (.of k))`) whose underlying scheme morphism is both an open
immersion and a closed immersion (i.e. the inclusion of a clopen
subscheme).

The full Kleiman conclusion also packages the group-subscheme property (the
inclusion is a homomorphism of `k`-group schemes), finite-type-ness over `k`
(`LocallyOfFiniteType` + quasi-compactness), geometric irreducibility, and
base-change-commutation. Those refinements live as separate instances /
follow-up lemmas in iter-186+; the file-skeleton pins only the clopen
open-immersion conclusion as a Nonempty-witness.

iter-186 body: the inclusion morphism is `Over.homMk (identityComponentCarrier G).ι`,
with the over-category compatibility holding by definition of
`IdentityComponent G`. The `.left` of this morphism is
`(identityComponentCarrier G).ι`, an open immersion by the global
`Scheme.Opens.instIsOpenImmersionι` instance. For the closed-immersion
half we apply `IsClosedImmersion.of_isPreimmersion` to the open immersion
and reduce to `IsClosed (↑(identityComponentCarrier G) : Set _)`, which holds
because the carrier is a connected component and connected components are
closed. This theorem is now axiom-clean. -/
theorem IdentityComponent.isOpenSubgroupScheme {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    Nonempty {f : IdentityComponent G ⟶ G //
        IsOpenImmersion f.left ∧ IsClosedImmersion f.left} := by
  -- Over-category compatibility for the underlying open immersion.
  have hcomp : (identityComponentCarrier G).ι ≫ G.hom = (IdentityComponent G).hom := by
    simp [IdentityComponent]
  -- The over-morphism witness.
  let f : IdentityComponent G ⟶ G :=
    Over.homMk (U := IdentityComponent G) (V := G) (identityComponentCarrier G).ι hcomp
  refine ⟨⟨f, ?_, ?_⟩⟩
  · -- `f.left = (identityComponentCarrier G).ι` (definitionally; `Over.homMk_left` simp).
    -- An open immersion by `Scheme.Opens.instIsOpenImmersionι`.
    change IsOpenImmersion (identityComponentCarrier G).ι
    infer_instance
  · -- `f.left = (identityComponentCarrier G).ι` is a preimmersion (open immersion ⟹
    -- immersion ⟹ preimmersion). Its range is the carrier set (`Scheme.Opens.range_ι`),
    -- and closure of that connected subset is itself (Kleiman §5 Lem.~`lem:agps`~(3):
    -- the connected component through the identity is closed in `|G|`).
    change IsClosedImmersion (identityComponentCarrier G).ι
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    -- The carrier set is `connectedComponent (identitySectionPoint G)`, which is
    -- closed by `isClopen_connectedComponent.1` (with the
    -- `identityComponent_locallyConnectedSpace` instance providing the closedness
    -- half of EGA I 6.1.9: connected components of a locally Noetherian topological
    -- space are clopen).
    change IsClosed (connectedComponent (identitySectionPoint G))
    exact isClopen_connectedComponent.1

/-! ### iter-192 Lane A.3.i: identity-component substrate

Per `analogies/lane-a3i-isconnected-prod.md`, the substrate for the
group-structure inheritance and base-change-commutation arguments is
Stacks Tag 04KU / EGA IV₂ 4.5.14 (a connected `k`-scheme with a
`k`-rational section is geometrically connected) combined with Mathlib's
`ConnectedSpace (pullback f g)` instance for
`[GeometricallyConnected f] [UniversallyOpen f] [ConnectedSpace Y]`.

This iter (Lane A.3.i): we add the AXIOM-CLEAN
`identityComponentCarrier_connectedSpace` helper below (the carrier is
connected by construction). The full Stacks 04KU bridge
"`ConnectedSpace X` + section ⟹ `GeometricallyConnected f`" is now
PROVED project-side (run 0005 session 0007, T5) in the sibling module
`Picard/GeometricallyConnectedSection.lean` and consumed by
`geometricallyConnected_of_connected_of_section` below, so the
geometric-connectedness substrate is axiom-clean. Built on top of it,
`isSubgroupHomomorphism` (group-structure inheritance) and `baseChangeIso`
(clopen-image identification) are now both axiom-clean, and (run 0009, T6)
`isFiniteTypeGeometricallyIrreducible` is closed as well — see the
"Run 0009 (T6)" section below — so the §1 substrate is fully sorry-free.

Below: `baseChangeIso` closes via
`CategoryTheory.Over.grpObjMkPullbackSnd` together with the carrier
identification `fst⁻¹(G⁰) = (G_K)⁰` (clopen ⊇, preconnected-range ⊆). -/

/-- Helper (iter-192 Lane A.3.i, axiom-clean): the **identity component
carrier** has connected underlying topological space.

The carrier is defined as `connectedComponent (identitySectionPoint G)`
in `|G|` (a `G.left.Opens`), and its subspace topology coincides with the
open-subscheme topology; the subspace is connected because the connected
component is preconnected (Mathlib's `isPreconnected_connectedComponent`)
and nonempty (contains the identity point `identitySectionPoint G`). -/
private instance identityComponentCarrier_connectedSpace
    {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    ConnectedSpace ((identityComponentCarrier G : G.left.Opens) : Type _) := by
  haveI : PreconnectedSpace ((identityComponentCarrier G : G.left.Opens) : Type _) :=
    Subtype.preconnectedSpace isPreconnected_connectedComponent
  exact ⟨⟨⟨identitySectionPoint G, mem_connectedComponent⟩⟩⟩

/-- Helper (iter-192 Lane A.3.i, axiom-clean): the **identity component**
`IdentityComponent G` has connected underlying topological space.

By definition `(IdentityComponent G).left` is the open subscheme
`identityComponentCarrier G : G.left.Opens` regarded as a scheme; its
underlying topological space coincides definitionally with the carrier's
subspace topology, so `ConnectedSpace` transports via
`identityComponentCarrier_connectedSpace` above.

Downstream this combines with the (pending) Stacks 04KU substrate
`GeometricallyConnected (IdentityComponent G).hom` plus Mathlib's
`ConnectedSpace (pullback f g)` instance for
`[GeometricallyConnected f] [UniversallyOpen f] [ConnectedSpace Y]`
to give the key "`G⁰ ×_k G⁰` is connected" substrate for Kleiman's
group-structure inheritance argument in `isSubgroupHomomorphism`. -/
private instance identityComponent_connectedSpace
    {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    ConnectedSpace (IdentityComponent G).left := by
  change ConnectedSpace ((identityComponentCarrier G : G.left.Opens) : Type _)
  infer_instance

/-- **Stacks 04KV / EGA IV₂ 4.5.14**: a connected `k`-scheme with a `k`-rational
section is geometrically connected.

Given a morphism `f : X ⟶ Spec k` from a `ConnectedSpace`-typed scheme `X`
admitting a section `s : Spec k ⟶ X` (i.e. `s ≫ f = 𝟙`), the morphism `f` is
geometrically connected: for any field extension `K/k`, the pullback
`X ×_{Spec k} Spec K` is connected.

CLOSED (run 0005 session 0007, T5): the full Stacks 04KV/037Q descent substrate
now lives in the sibling module `Picard/GeometricallyConnectedSection.lean`
(tensor products of field extensions over an algebraically closed field are
domains + the open/closed/singleton-fiber clopen descent argument), and this
helper is a direct application. Axiom-clean. -/
private theorem geometricallyConnected_of_connected_of_section
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (s : Spec (.of k) ⟶ X) (hsf : s ≫ f = 𝟙 _)
    [ConnectedSpace X] :
    GeometricallyConnected f :=
  geometricallyConnected_of_connectedSpace_of_section f s hsf

/-- The range-containment hypothesis for `IsOpenImmersion.lift` used to build
the section `identityComponentSection G` below: the image of the identity
section `MonObj.one.left : Spec k ⟶ G.left` lies in the carrier of the
identity component (a singleton image `{identitySectionPoint G}` contained
in `connectedComponent (identitySectionPoint G) = identityComponentCarrier G`). -/
private lemma identityComponentSection_range_subset
    {k : Type u} [Field k] (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    Set.range ((MonObj.one (X := G)).left : Spec (.of k) ⟶ G.left).base ⊆
      Set.range (identityComponentCarrier G).ι.base := by
  rw [Scheme.Opens.range_ι]
  let f : ↥(Spec (.of k)) → G.left := (MonObj.one (X := G)).left.base
  change Set.range f ⊆ _
  rintro y ⟨x, rfl⟩
  have hx : x = default := Subsingleton.elim _ _
  rw [hx]
  -- `f default = identitySectionPoint G` (by definition of
  -- `identitySectionPoint`); the carrier underlying set is
  -- `connectedComponent (identitySectionPoint G)`.
  exact mem_connectedComponent

-- (iter-current) de-privatised: consumed by `Scheme.Pic0.identitySection`
-- in the sibling `Picard/Pic0AbelianVariety.lean` (the `e`-witness of the
-- `tangentSpaceIso` Σ'-bundle).
noncomputable def identityComponentSection
    {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    Spec (.of k) ⟶ (IdentityComponent G).left :=
  @IsOpenImmersion.lift (identityComponentCarrier G).toScheme (Spec (.of k))
    G.left (identityComponentCarrier G).ι
    ((MonObj.one (X := G)).left : Spec (.of k) ⟶ G.left)
    inferInstance (identityComponentSection_range_subset G)

/-- Helper (iter-193 Lane A.3.i, axiom-clean): the **identity section lift is
a section of `(IdentityComponent G).hom`**.

Composing `identityComponentSection G` with `(IdentityComponent G).hom`
returns the identity on `Spec k`, by `IsOpenImmersion.lift_fac` plus the
over-compatibility `MonObj.one.left ≫ G.hom = 𝟙` (the terminal of
`Over (Spec k)` has `.hom = 𝟙 (Spec k)` definitionally). -/
lemma identityComponentSection_isSection
    {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    identityComponentSection G ≫ (IdentityComponent G).hom = 𝟙 (Spec (.of k)) := by
  -- `(IdentityComponent G).hom = (identityComponentCarrier G).ι ≫ G.hom`
  -- (definitionally, by the `IdentityComponent` def).
  change identityComponentSection G ≫ (identityComponentCarrier G).ι ≫ G.hom = _
  rw [← Category.assoc]
  -- `identityComponentSection G ≫ (identityComponentCarrier G).ι = MonObj.one.left`
  -- by `IsOpenImmersion.lift_fac` (after unfolding the `identityComponentSection`
  -- def to expose the `IsOpenImmersion.lift` head).
  rw [show identityComponentSection G ≫ (identityComponentCarrier G).ι =
        ((MonObj.one (X := G)).left : Spec (.of k) ⟶ G.left) from
      IsOpenImmersion.lift_fac _ _ (identityComponentSection_range_subset G)]
  -- Now: `(MonObj.one (X := G)).left ≫ G.hom = 𝟙 (Spec (.of k))`.
  -- This is the over-morphism compatibility: for the terminal of
  -- `Over (Spec k)`, `(MonObj.one).w` says
  -- `MonObj.one.left ≫ G.hom = (𝟙_).hom = 𝟙 (Spec k)` (defeq).
  exact (MonObj.one (X := G)).w

/-- Lemma (iter-193 Lane A.3.i; AXIOM-CLEAN since run 0005 session 0007
closed `geometricallyConnected_of_connected_of_section`): the structural
morphism `(IdentityComponent G).hom` is **geometrically connected**.

**iter-194 demotion (per lean-auditor iter-193 must-fix): no longer a
`private instance` but a `private theorem`.** The earlier instance shape
silently propagated a `sorryAx` axiom into every downstream typeclass
search that happened to resolve `GeometricallyConnected (IdentityComponent
G).hom` — a soundness exposure. Downstream consumers should now invoke
this lemma explicitly via `letI := identityComponent_geometricallyConnected G`.

Derived from:
- `identityComponent_connectedSpace`: `ConnectedSpace (IdentityComponent G).left`
  (axiom-clean iter-192).
- `identityComponentSection_isSection`: existence of a section
  `Spec k ⟶ (IdentityComponent G).left` (axiom-clean iter-193).
- `geometricallyConnected_of_connected_of_section`: Stacks 04KU helper
  (axiom-clean since run 0005 session 0007 via
  `Picard/GeometricallyConnectedSection.lean`).

Downstream consumers can
chain `letI := identityComponent_geometricallyConnected G` with
`UniversallyOpen` of `Spec k → Spec k` (which holds via
`[IsIntegral Y] [Subsingleton Y] ⟹ UniversallyOpen f`) to derive
`ConnectedSpace (pullback (IdentityComponent G).hom g)` for any
`g : Y ⟶ Spec (.of k)` from a `ConnectedSpace Y`. -/
private theorem identityComponent_geometricallyConnected
    {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    GeometricallyConnected (IdentityComponent G).hom :=
  geometricallyConnected_of_connected_of_section
    (IdentityComponent G).hom (identityComponentSection G)
    (identityComponentSection_isSection G)

/-! ### Session 0011 (run 0005, T5): the inherited group structure on `G⁰`

Kleiman §5 Lem.~`lem:agps`~(3)(b): the clopen identity component `G⁰` of a
`k`-group scheme `G` locally of finite type inherits the group structure of
`G`. Strategy (Yoneda): the subfunctor of `Hom(-, G)` of morphisms whose
set-theoretic image lands in the identity-component carrier is a presheaf of
*subgroups* — closure under `mul`/`inv` is Kleiman's connectedness argument
(`G⁰ ×ₖ G⁰` is connected, via `identityComponent_geometricallyConnected` +
Mathlib's connected-pullback instance, so its image under the group law is a
connected subset through `e`, hence contained in the connected component).
This subfunctor is represented by `IdentityComponent G` (factorisation
through the open immersion `G⁰ ↪ G` via `IsOpenImmersion.lift`), so
`GrpObj.ofRepresentableBy` equips `IdentityComponent G` with the
group-object structure. -/

open MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

section SubgroupStructure

variable {k : Type u} [Field k] (G : Over (Spec (.of k)))
  [GrpObj G] [LocallyOfFiniteType G.hom]

/-- The inclusion `G⁰ ⟶ G` as an over-category morphism (the same underlying
open immersion `(identityComponentCarrier G).ι` as in
`IdentityComponent.isOpenSubgroupScheme`). -/
private noncomputable def identityComponentInclusion : IdentityComponent G ⟶ G :=
  Over.homMk (identityComponentCarrier G).ι rfl

/-- Composition with a fixed morphism only shrinks the set-theoretic image. -/
private lemma range_comp_left_subset {A B C' : Over (Spec (.of k))} (a : A ⟶ B) (b : B ⟶ C') :
    Set.range ⇑(a ≫ b).left ⊆ Set.range ⇑b.left := by
  rintro _ ⟨t, rfl⟩
  exact ⟨a.left.base t, by simp⟩

/-- The image of the unit section lands in the identity-component carrier. -/
private lemma range_one_left_subset :
    Set.range ⇑(MonObj.one (X := G)).left ⊆ (identityComponentCarrier G : Set G.left) := by
  have h := identityComponentSection_range_subset G
  rwa [Scheme.Opens.range_ι] at h

/-- The image of the inclusion is contained in the identity-component carrier. -/
private lemma range_inclusion_left_subset :
    Set.range ⇑(identityComponentInclusion G).left ⊆
      (identityComponentCarrier G : Set G.left) := by
  show Set.range ⇑(identityComponentCarrier G).ι ⊆ (identityComponentCarrier G : Set G.left)
  exact (Scheme.Opens.range_ι _).le

/-- Range hypothesis for the `IsOpenImmersion.lift` factorisation below. -/
private lemma identityComponentFactor_range {T : Over (Spec (.of k))} (f : T ⟶ G)
    (hf : Set.range ⇑f.left ⊆ (identityComponentCarrier G : Set G.left)) :
    Set.range ⇑f.left ⊆ Set.range ⇑(identityComponentCarrier G).ι := by
  rw [Scheme.Opens.range_ι]; exact hf

/-- A morphism `T ⟶ G` whose set-theoretic image lands in the
identity-component carrier factors through the open immersion `G⁰ ↪ G`. -/
private noncomputable def identityComponentFactor {T : Over (Spec (.of k))} (f : T ⟶ G)
    (hf : Set.range ⇑f.left ⊆ (identityComponentCarrier G : Set G.left)) :
    T ⟶ IdentityComponent G :=
  Over.homMk
    (@IsOpenImmersion.lift (identityComponentCarrier G).toScheme T.left G.left
      (identityComponentCarrier G).ι f.left inferInstance
      (identityComponentFactor_range G f hf))
    (by
      change _ ≫ (identityComponentCarrier G).ι ≫ G.hom = T.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac (identityComponentCarrier G).ι f.left
        (identityComponentFactor_range G f hf)]
      exact Over.w f)

private lemma identityComponentFactor_comp {T : Over (Spec (.of k))} (f : T ⟶ G)
    (hf : Set.range ⇑f.left ⊆ (identityComponentCarrier G : Set G.left)) :
    identityComponentFactor G f hf ≫ identityComponentInclusion G = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (identityComponentCarrier G).ι f.left
    (identityComponentFactor_range G f hf)

/-- The unit of `G`, viewed as a morphism into the identity component. -/
private noncomputable def identityComponentOne :
    𝟙_ (Over (Spec (.of k))) ⟶ IdentityComponent G :=
  Over.homMk (identityComponentSection G) (identityComponentSection_isSection G)

private lemma identityComponentOne_comp :
    identityComponentOne G ≫ identityComponentInclusion G = MonObj.one (X := G) := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (identityComponentCarrier G).ι
    (MonObj.one (X := G)).left (identityComponentSection_range_subset G)

omit [LocallyOfFiniteType G.hom] in
/-- `1 · 1 = 1` in diagrammatic form for the unit object. -/
private lemma lift_one_one_mul :
    lift (MonObj.one (X := G)) (MonObj.one (X := G)) ≫ MonObj.mul (X := G) =
      MonObj.one (X := G) := by
  have h1 : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G) = MonObj.one (X := G) := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  simpa [Hom.mul_def, h1] using mul_one (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G)

omit [LocallyOfFiniteType G.hom] in
/-- The unit is fixed by inversion: `e⁻¹ = e` in diagrammatic form. -/
private lemma one_comp_inv :
    MonObj.one (X := G) ≫ GrpObj.inv (X := G) = MonObj.one (X := G) := by
  have h1 : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G) = MonObj.one (X := G) := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  simpa [Hom.inv_def, h1] using (inv_one : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G)⁻¹ = 1)

/-- `G⁰ ×ₖ G⁰` is connected (EGA IV₂ 4.5.8, via geometric connectedness of
`G⁰` and universal openness of morphisms to the spectrum of a field). -/
private lemma identityComponent_tensor_connectedSpace :
    ConnectedSpace (IdentityComponent G ⊗ IdentityComponent G).left := by
  letI := identityComponent_geometricallyConnected G
  haveI : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : UniversallyOpen (IdentityComponent G).hom := inferInstance
  exact inferInstanceAs
    (ConnectedSpace ↥(pullback (IdentityComponent G).hom (IdentityComponent G).hom))

/-- **Core closure lemma (mul)**: the image of `G⁰ ×ₖ G⁰` under the group law
of `G` is contained in the identity-component carrier (a connected set
through the identity point is contained in its connected component). -/
private lemma range_tensor_mul_subset :
    Set.range ⇑(((identityComponentInclusion G ⊗ₘ identityComponentInclusion G) ≫
        MonObj.mul (X := G)).left) ⊆ (identityComponentCarrier G : Set G.left) := by
  haveI := identityComponent_tensor_connectedSpace G
  have hmor : lift (identityComponentOne G) (identityComponentOne G) ≫
      ((identityComponentInclusion G ⊗ₘ identityComponentInclusion G) ≫
        MonObj.mul (X := G)) = MonObj.one (X := G) := by
    rw [← Category.assoc, lift_map, identityComponentOne_comp, lift_one_one_mul]
  have hmem : identitySectionPoint G ∈ Set.range ⇑(((identityComponentInclusion G ⊗ₘ
      identityComponentInclusion G) ≫ MonObj.mul (X := G)).left) := by
    have h0 : identitySectionPoint G ∈ Set.range ⇑(MonObj.one (X := G)).left :=
      ⟨(default : ↥(Spec (CommRingCat.of k))), rfl⟩
    rw [← hmor] at h0
    exact range_comp_left_subset _ _ h0
  have hsub := (isPreconnected_range (Scheme.Hom.continuous _)).subset_connectedComponent hmem
  simpa [identityComponentCarrier] using hsub

/-- **Core closure lemma (inv)**: the image of `G⁰` under the inversion of `G`
is contained in the identity-component carrier. -/
private lemma range_inclusion_inv_subset :
    Set.range ⇑((identityComponentInclusion G ≫ GrpObj.inv (X := G)).left) ⊆
      (identityComponentCarrier G : Set G.left) := by
  have hmor : identityComponentOne G ≫
      identityComponentInclusion G ≫ GrpObj.inv (X := G) = MonObj.one (X := G) := by
    rw [← Category.assoc, identityComponentOne_comp, one_comp_inv]
  have hmem : identitySectionPoint G ∈
      Set.range ⇑((identityComponentInclusion G ≫ GrpObj.inv (X := G)).left) := by
    have h0 : identitySectionPoint G ∈ Set.range ⇑(MonObj.one (X := G)).left :=
      ⟨(default : ↥(Spec (CommRingCat.of k))), rfl⟩
    rw [← hmor] at h0
    exact range_comp_left_subset _ _ h0
  have hsub := (isPreconnected_range (Scheme.Hom.continuous _)).subset_connectedComponent hmem
  simpa [identityComponentCarrier] using hsub

/-- The subgroup of `Hom(T, G)` of morphisms landing in the identity-component
carrier (Kleiman §5 Lem.~`lem:agps`~(3)(b), Yoneda form). -/
private noncomputable def identityComponentSubgroup (T : Over (Spec (.of k))) :
    Subgroup (T ⟶ G) where
  carrier := {f | Set.range ⇑f.left ⊆ (identityComponentCarrier G : Set G.left)}
  one_mem' := by
    show Set.range ⇑(1 : T ⟶ G).left ⊆ _
    rw [(Hom.one_def : (1 : T ⟶ G) = _)]
    exact (range_comp_left_subset _ _).trans (range_one_left_subset G)
  mul_mem' := by
    intro f g hf hg
    show Set.range ⇑(f * g).left ⊆ _
    have hfac : f * g =
        lift (identityComponentFactor G f hf) (identityComponentFactor G g hg) ≫
          ((identityComponentInclusion G ⊗ₘ identityComponentInclusion G) ≫
            MonObj.mul (X := G)) := by
      conv_rhs => rw [← Category.assoc, lift_map,
        identityComponentFactor_comp G f hf, identityComponentFactor_comp G g hg]
      exact Hom.mul_def f g
    rw [hfac]
    exact (range_comp_left_subset _ _).trans (range_tensor_mul_subset G)
  inv_mem' := by
    intro f hf
    show Set.range ⇑f⁻¹.left ⊆ _
    have hfac : f⁻¹ = identityComponentFactor G f hf ≫
        (identityComponentInclusion G ≫ GrpObj.inv (X := G)) := by
      conv_rhs => rw [← Category.assoc, identityComponentFactor_comp G f hf]
      exact Hom.inv_def f
    rw [hfac]
    exact (range_comp_left_subset _ _).trans (range_inclusion_inv_subset G)

/-- The presheaf of groups `T ↦ {f : T ⟶ G | im f ⊆ G⁰}`. -/
private noncomputable def identityComponentSubgroupFunctor :
    (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (identityComponentSubgroup G T.unop)
  map {T T'} φ := GrpCat.ofHom
    { toFun := fun f => ⟨φ.unop ≫ f.1, (range_comp_left_subset _ _).trans f.2⟩
      map_one' := Subtype.ext (by
        show φ.unop ≫ (1 : T.unop ⟶ G) = (1 : T'.unop ⟶ G)
        simp only [Hom.one_def]
        rw [← Category.assoc, comp_toUnit])
      map_mul' := fun f g => Subtype.ext (by
        show φ.unop ≫ (f.1 * g.1) = (φ.unop ≫ f.1) * (φ.unop ≫ g.1)
        simp only [Hom.mul_def]
        rw [← Category.assoc, comp_lift]) }
  map_id T := by
    ext f
    exact Category.id_comp _
  map_comp {T T' T''} φ ψ := by
    ext f
    exact Category.assoc _ _ _

/-- The natural bijection `(T ⟶ G⁰) ≃ {f : T ⟶ G | im f ⊆ G⁰}`. -/
private noncomputable def identityComponentHomEquiv (T : Over (Spec (.of k))) :
    (T ⟶ IdentityComponent G) ≃ ↥(identityComponentSubgroup G T) where
  toFun u := ⟨u ≫ identityComponentInclusion G,
    (range_comp_left_subset _ _).trans (range_inclusion_left_subset G)⟩
  invFun f := identityComponentFactor G f.1 f.2
  left_inv u := by
    apply Over.OverMorphism.ext
    exact (IsOpenImmersion.lift_uniq (identityComponentCarrier G).ι
      (u ≫ identityComponentInclusion G).left _ u.left rfl).symm
  right_inv f := Subtype.ext (identityComponentFactor_comp G f.1 f.2)

/-- `IdentityComponent G` represents the subgroup presheaf. -/
private noncomputable def identityComponentRepresentableBy :
    (identityComponentSubgroupFunctor G ⋙ forget GrpCat).RepresentableBy
      (IdentityComponent G) where
  homEquiv {T} := identityComponentHomEquiv G T
  homEquiv_comp {T T'} f g := by
    apply Subtype.ext
    show (f ≫ g) ≫ identityComponentInclusion G = f ≫ (g ≫ identityComponentInclusion G)
    exact Category.assoc _ _ _

end SubgroupStructure

/-- **The identity component inclusion is a group-scheme homomorphism.**

Kleiman §5 Lem.~`lem:agps`~(3) conclusion (b): the clopen subscheme `G^0`
inherits a `k`-group-scheme structure from `G`, and the inclusion morphism
`G^0 ↪ G` (from `IdentityComponent.isOpenSubgroupScheme`) is compatible
with the group laws on source and target. The statement-level pin asserts
the existence of the inherited `GrpObj` structure; the compatibility of
the inclusion with the group operations is the substantive content of
Kleiman's argument (the product `G^0 ×_k G^0` is connected by
EGA IV₂ 4.5.8; the group-multiplication map sends this connected subset
containing the identity into the connected component `G^0`).

CLOSED (run 0005, session 0011): via `GrpObj.ofRepresentableBy` applied to
the subgroup presheaf `identityComponentSubgroupFunctor` — the group
structure on `Hom(T, G⁰)` is the subgroup of `Hom(T, G)` of morphisms
landing in the carrier, with closure under `mul`/`inv` provided by the
connectedness core lemmas `range_tensor_mul_subset` /
`range_inclusion_inv_subset` above. The induced group law on `G⁰` is by
construction compatible with the inclusion (the Yoneda equivalence is
`u ↦ u ≫ identityComponentInclusion G`). -/
theorem IdentityComponent.isSubgroupHomomorphism {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    Nonempty (GrpObj (IdentityComponent G)) :=
  ⟨GrpObj.ofRepresentableBy (IdentityComponent G) (identityComponentSubgroupFunctor G)
    (identityComponentRepresentableBy G)⟩

/-! ### Run 0009 (T6): finite type + geometric irreducibility of `G⁰`

Kleiman §5 Lem.~`lem:agps`~(3) conclusion (c). The former header claim that
this needs EGA IV₂ 4.6.1 reduced-fiber-product input absent from Mathlib was
stale: Mathlib v4.31 templates Kleiman's translation argument (closed-point
translation via `GrpObj.mulRight`, closed points ↔ rational points via
`pointEquivClosedPoint`, Jacobson density of closed points) in
`Mathlib/AlgebraicGeometry/Group/Smooth.lean`
(`smooth_of_grpObj_of_isAlgClosed`), and we adapt that pattern here.

Layer structure:
1. `irreducibleSpace_of_connectedSpace_of_nhds` — EGA I 6.1.10 in topological
   form: a connected space in which every point has an irreducible open
   neighbourhood is irreducible.
2. `identityComponent_irreducibleSpace_of_isAlgClosed` /
   `identityComponent_compactSpace_of_isAlgClosed` — the geometric core over
   an algebraically closed field: translate a nonempty irreducible (resp.
   quasi-compact affine) open through every closed point using the inherited
   group structure of `G⁰` (`isSubgroupHomomorphism`), then sweep up the
   non-closed points by Jacobson density.
3. `identityComponent_compactSpace` /
   `identityComponent_geometricallyIrreducible` (placed after
   `baseChangeIso` below) — descent to an arbitrary base field along the
   surjective projection from the base change to the algebraic closure,
   using `baseChangeIso` to identify `(G_K̄)⁰` with the base change of `G⁰`.

The blueprint-pinned theorem `isFiniteTypeGeometricallyIrreducible` is
assembled after `baseChangeIso` (its statement is unchanged). -/

/-- **EGA I 6.1.10** (topological form): a connected topological space in
which every point admits an irreducible open neighbourhood is irreducible.

Proof: let `Z` be the irreducible component of some point. For `z ∈ Z` pick
an irreducible open `V ∋ z`; then `Z ∩ V` is nonempty, so
`Z ⊆ closure (Z ∩ V) ⊆ closure V` (a nonempty open subset of a
preirreducible set is dense in it); `closure V` is irreducible, so
maximality of `Z` forces `closure V = Z`, whence `V ⊆ Z` and `Z` is open.
Components are always closed, so the nonempty clopen `Z` is everything by
connectedness. -/
private lemma irreducibleSpace_of_connectedSpace_of_nhds
    {α : Type*} [TopologicalSpace α] [ConnectedSpace α]
    (h : ∀ x : α, ∃ V : Set α, IsOpen V ∧ x ∈ V ∧ IsIrreducible V) :
    IrreducibleSpace α := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  have hZmem : Maximal IsIrreducible (irreducibleComponent x₀) :=
    irreducibleComponent_mem_irreducibleComponents x₀
  have hZopen : IsOpen (irreducibleComponent x₀) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨V, hVopen, hzV, hVirr⟩ := h z
    have h1 : irreducibleComponent x₀ ⊆ closure V :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen hZmem.prop.2 hVopen
        ⟨z, hz, hzV⟩).trans (closure_mono Set.inter_subset_right)
    have h2 : closure V = irreducibleComponent x₀ :=
      hZmem.eq_of_superset hVirr.closure h1
    exact mem_nhds_iff.mpr ⟨V, h2 ▸ subset_closure, hVopen, hzV⟩
  have hZuniv : irreducibleComponent x₀ = Set.univ :=
    (isClopen_iff.mp ⟨isClosed_irreducibleComponent, hZopen⟩).resolve_left
      (Set.Nonempty.ne_empty ⟨x₀, mem_irreducibleComponent⟩)
  haveI : PreirreducibleSpace α := ⟨hZuniv ▸ hZmem.prop.2⟩
  exact ⟨⟨x₀⟩⟩

/-- The structural morphism of the identity component is locally of finite
type: it is the composite of the open immersion `G⁰ ↪ G` with `G.hom`. -/
private theorem identityComponent_locallyOfFiniteType
    {k : Type u} [Field k] (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    LocallyOfFiniteType (IdentityComponent G).hom := by
  change LocallyOfFiniteType ((identityComponentCarrier G).ι ≫ G.hom)
  infer_instance

/-- Existence of a nonempty irreducible open subset of `|G⁰|`: inside any
affine open `W` (a Noetherian space, since `G⁰` is locally Noetherian over
the field `k`), the complement of the union of the irreducible components of
`W` other than a fixed one is open, nonempty, and contained in that fixed
irreducible component (Stacks 0052 (3)); its image under the open embedding
`W ↪ G⁰` is the required open. -/
private lemma identityComponent_exists_isOpen_nonempty_isIrreducible
    {k : Type u} [Field k] (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    ∃ U : Set (IdentityComponent G).left,
      IsOpen U ∧ U.Nonempty ∧ IsIrreducible U := by
  haveI : LocallyOfFiniteType (IdentityComponent G).hom :=
    identityComponent_locallyOfFiniteType G
  haveI : IsLocallyNoetherian (IdentityComponent G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (IdentityComponent G).hom
  obtain ⟨x₀⟩ : Nonempty (IdentityComponent G).left := inferInstance
  obtain ⟨W, hW, hx₀W, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := (IdentityComponent G).left) (U := ⊤)
    (TopologicalSpace.Opens.mem_top x₀)
  haveI : IsNoetherianRing Γ((IdentityComponent G).left, W) :=
    IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  haveI : TopologicalSpace.NoetherianSpace ↥W := noetherianSpace_of_isAffineOpen W hW
  obtain ⟨o, hoopen, hone, hoZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent (⟨x₀, hx₀W⟩ : ↥W))
      (irreducibleComponent_mem_irreducibleComponents _)
  have hoirr : IsIrreducible o :=
    ⟨hone, (isIrreducible_irreducibleComponent
      (x := (⟨x₀, hx₀W⟩ : ↥W))).2.open_subset hoopen hoZ⟩
  exact ⟨(Subtype.val : ↥W → (IdentityComponent G).left) '' o,
    W.isOpen.isOpenMap_subtype_val _ hoopen, hone.image _,
    hoirr.image _ continuous_subtype_val.continuousOn⟩

/-- Composing a rational point with the right-translation isomorphism
computes the Hom-group product: `p ≫ (· * q) = p * q` for
`p q : 𝟙_ ⟶ A`. -/
private lemma comp_mulRight_hom {k : Type u} [Field k]
    {A : Over (Spec (.of k))} [GrpObj A]
    (p q : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    p ≫ (GrpObj.mulRight q).hom = p * q := by
  rw [Hom.mul_def, GrpObj.mulRight_hom, comp_lift_assoc, Category.comp_id,
    ← Category.assoc, toUnit_unique (p ≫ toUnit A) (𝟙 _), Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **Kleiman §5 Lem.~`lem:agps`~(3)(c), irreducibility core over an
algebraically closed field**: over `K = K̄` the identity component `G⁰` is
irreducible. Translate one nonempty irreducible open `U` (which exists by
`identityComponent_exists_isOpen_nonempty_isIrreducible`) through each
closed point `z` via the translation isomorphism `x ↦ x·g⁻¹·z` (with `g` a
closed point of `U`, so that the translate contains `z`); Jacobson density
sweeps up the non-closed points; conclude by EGA I 6.1.10 and connectedness
of `G⁰`. -/
private theorem identityComponent_irreducibleSpace_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : Over (Spec (.of K))) [GrpObj G] [LocallyOfFiniteType G.hom] :
    IrreducibleSpace (IdentityComponent G).left := by
  letI : GrpObj (IdentityComponent G) :=
    Classical.choice (IdentityComponent.isSubgroupHomomorphism G)
  haveI : LocallyOfFiniteType (IdentityComponent G).hom :=
    identityComponent_locallyOfFiniteType G
  haveI : JacobsonSpace (IdentityComponent G).left :=
    LocallyOfFiniteType.jacobsonSpace (IdentityComponent G).hom
  obtain ⟨U, hUopen, hUne, hUirr⟩ :=
    identityComponent_exists_isOpen_nonempty_isIrreducible G
  obtain ⟨g, hgU, hgc⟩ := nonempty_inter_closedPoints hUne hUopen.isLocallyClosed
  let g' : 𝟙_ (Over (Spec (.of K))) ⟶ IdentityComponent G :=
    Over.homMk _ ((pointEquivClosedPoint (IdentityComponent G).hom).symm ⟨g, hgc⟩).2
  have hg' : ∀ a, g'.left a = g := fun a => by simp [g', pointEquivClosedPoint]
  let pt : ↥(𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    (default : ↥(Spec (CommRingCat.of K)))
  have hcover : ∀ z ∈ closedPoints (IdentityComponent G).left,
      ∃ V : Set (IdentityComponent G).left, IsOpen V ∧ z ∈ V ∧ IsIrreducible V := by
    intro z hzc
    let z' : 𝟙_ (Over (Spec (.of K))) ⟶ IdentityComponent G :=
      Over.homMk _ ((pointEquivClosedPoint (IdentityComponent G).hom).symm ⟨z, hzc⟩).2
    have hz' : ∀ a, z'.left a = z := fun a => by simp [z', pointEquivClosedPoint]
    -- the right-translation `x ↦ x·(g⁻¹·z)`, an automorphism sending `g` to `z`
    let τ : IdentityComponent G ⟶ IdentityComponent G :=
      (GrpObj.mulRight (A := IdentityComponent G) (g'⁻¹ * z')).hom
    haveI hτiso : IsIso τ :=
      inferInstanceAs (IsIso (GrpObj.mulRight (A := IdentityComponent G) (g'⁻¹ * z')).hom)
    haveI : IsIso τ.left :=
      inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map τ))
    have hτ : g' ≫ τ = z' := by
      rw [show g' ≫ τ =
          g' ≫ (GrpObj.mulRight (A := IdentityComponent G) (g'⁻¹ * z')).hom from rfl,
        comp_mulRight_hom]
      exact mul_inv_cancel_left g' z'
    have hτl : g'.left ≫ τ.left = z'.left := by
      simpa using
        congrArg (fun q : 𝟙_ (Over (Spec (.of K))) ⟶ IdentityComponent G => q.left) hτ
    have hτ' : τ.left g = z := by
      calc τ.left g = τ.left (g'.left pt) := by rw [hg' pt]
        _ = (g'.left ≫ τ.left) pt := (Scheme.Hom.comp_apply _ _ _).symm
        _ = z'.left pt := by rw [hτl]
        _ = z := hz' pt
    exact ⟨⇑τ.left '' U, τ.left.isOpenEmbedding.isOpenMap _ hUopen,
      ⟨g, hgU, hτ'⟩, hUirr.image _ (Scheme.Hom.continuous τ.left).continuousOn⟩
  have hsUopen : IsOpen (⋃₀ {V : Set (IdentityComponent G).left |
      IsOpen V ∧ IsIrreducible V}) :=
    isOpen_sUnion fun _ hV => hV.1
  have hsU : ⋃₀ {V : Set (IdentityComponent G).left | IsOpen V ∧ IsIrreducible V} =
      Set.univ := by
    by_contra hne
    obtain ⟨w, hw, hwc⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
      hsUopen.isClosed_compl.isLocallyClosed
    obtain ⟨V, hV1, hV2, hV3⟩ := hcover w hwc
    exact hw ⟨V, ⟨hV1, hV3⟩, hV2⟩
  refine irreducibleSpace_of_connectedSpace_of_nhds fun x => ?_
  have hx : x ∈ ⋃₀ {V : Set (IdentityComponent G).left |
      IsOpen V ∧ IsIrreducible V} := by
    rw [hsU]; trivial
  obtain ⟨V, ⟨hV1, hV3⟩, hxV⟩ := hx
  exact ⟨V, hV1, hxV, hV3⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Kleiman §5 Lem.~`lem:agps`~(3)(c), quasi-compactness core over an
algebraically closed field**: over `K = K̄` the identity component `G⁰` is
quasi-compact. Let `W ∋ e` be an affine open. For a closed point `z`, the
preimage `χ_z⁻¹(W)` of `W` under the "division" morphism `χ_z : x ↦ x⁻¹·z`
contains `z` (because `χ_z(z) = e ∈ W`), so it meets `W` in a nonempty open
(`G⁰` is irreducible by the previous lemma), which contains a closed point
`g` by Jacobson density; then `u := g⁻¹·z` is a rational point landing in
`W` and `z = g·u` lies in the image of the multiplication
`m : W ×_K W ⟶ G⁰`. So the compact `m(W ×_K W)` contains all closed points;
finitely many affine opens cover it, and by Jacobson density they cover
everything. -/
private theorem identityComponent_compactSpace_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : Over (Spec (.of K))) [GrpObj G] [LocallyOfFiniteType G.hom] :
    CompactSpace (IdentityComponent G).left := by
  letI : GrpObj (IdentityComponent G) :=
    Classical.choice (IdentityComponent.isSubgroupHomomorphism G)
  haveI : LocallyOfFiniteType (IdentityComponent G).hom :=
    identityComponent_locallyOfFiniteType G
  haveI : JacobsonSpace (IdentityComponent G).left :=
    LocallyOfFiniteType.jacobsonSpace (IdentityComponent G).hom
  haveI : IrreducibleSpace (IdentityComponent G).left :=
    identityComponent_irreducibleSpace_of_isAlgClosed G
  -- an affine open around the identity point
  obtain ⟨W, hW, heW, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := (IdentityComponent G).left) (U := ⊤)
    (TopologicalSpace.Opens.mem_top (identitySectionPoint (IdentityComponent G)))
  haveI hWc : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW.isCompact
  haveI : QuasiCompact (W.ι ≫ (IdentityComponent G).hom) :=
    HasAffineProperty.iff_of_isAffine.mpr hWc
  let UW : Over (Spec (.of K)) := Over.mk (W.ι ≫ (IdentityComponent G).hom)
  let ιU : UW ⟶ IdentityComponent G := Over.homMk W.ι rfl
  let m : UW ⊗ UW ⟶ IdentityComponent G :=
    (ιU ⊗ₘ ιU) ≫ MonObj.mul (X := IdentityComponent G)
  haveI : CompactSpace (UW ⊗ UW).left :=
    inferInstanceAs (CompactSpace ↥(pullback (W.ι ≫ (IdentityComponent G).hom)
      (W.ι ≫ (IdentityComponent G).hom)))
  let pt : ↥(𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    (default : ↥(Spec (CommRingCat.of K)))
  -- all closed points lie in the image of `m`
  have hmem : ∀ z ∈ closedPoints (IdentityComponent G).left,
      z ∈ Set.range ⇑m.left := by
    intro z hzc
    let z' : 𝟙_ (Over (Spec (.of K))) ⟶ IdentityComponent G :=
      Over.homMk _ ((pointEquivClosedPoint (IdentityComponent G).hom).symm ⟨z, hzc⟩).2
    have hz' : ∀ a, z'.left a = z := fun a => by simp [z', pointEquivClosedPoint]
    -- the "division" morphism `x ↦ x⁻¹·z`
    let χ : IdentityComponent G ⟶ IdentityComponent G :=
      GrpObj.inv (X := IdentityComponent G) ≫
        (GrpObj.mulRight (A := IdentityComponent G) z').hom
    have hχ : ∀ p : 𝟙_ (Over (Spec (.of K))) ⟶ IdentityComponent G,
        p ≫ χ = p⁻¹ * z' := fun p => by
      rw [show p ≫ χ = (p ≫ GrpObj.inv (X := IdentityComponent G)) ≫
            (GrpObj.mulRight (A := IdentityComponent G) z').hom from
          (Category.assoc _ _ _).symm,
        ← Hom.inv_def, comp_mulRight_hom]
    have hone : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ IdentityComponent G) =
        MonObj.one (X := IdentityComponent G) := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    -- `χ` sends `z` to the identity point, which lies in `W`
    have hχz : χ.left z = identitySectionPoint (IdentityComponent G) := by
      have h1 : z'.left ≫ χ.left = (MonObj.one (X := IdentityComponent G)).left := by
        simpa using
          congrArg (fun q : 𝟙_ (Over (Spec (.of K))) ⟶ IdentityComponent G => q.left)
            ((hχ z').trans (by rw [inv_mul_cancel, hone]))
      calc χ.left z = χ.left (z'.left pt) := by rw [hz' pt]
        _ = (z'.left ≫ χ.left) pt := (Scheme.Hom.comp_apply _ _ _).symm
        _ = (MonObj.one (X := IdentityComponent G)).left pt := by rw [h1]
        _ = identitySectionPoint (IdentityComponent G) := rfl
    have hχzW : χ.left z ∈ (W : Set (IdentityComponent G).left) := hχz ▸ heW
    -- a closed point in `W ∩ χ⁻¹(W)`
    have hinter : ((W : Set (IdentityComponent G).left) ∩
        ⇑χ.left ⁻¹' (W : Set (IdentityComponent G).left)).Nonempty :=
      nonempty_preirreducible_inter W.isOpen
        (W.isOpen.preimage (Scheme.Hom.continuous χ.left)) ⟨_, heW⟩ ⟨z, hχzW⟩
    obtain ⟨g, ⟨hgW, hgE⟩, hgc⟩ := nonempty_inter_closedPoints hinter
      (W.isOpen.inter
        (W.isOpen.preimage (Scheme.Hom.continuous χ.left))).isLocallyClosed
    let g' : 𝟙_ (Over (Spec (.of K))) ⟶ IdentityComponent G :=
      Over.homMk _ ((pointEquivClosedPoint (IdentityComponent G).hom).symm ⟨g, hgc⟩).2
    have hg' : ∀ a, g'.left a = g := fun a => by simp [g', pointEquivClosedPoint]
    -- `u := g⁻¹·z` is a rational point landing in `W`
    have hu : ∀ a, (g'⁻¹ * z').left a = χ.left g := fun a => by
      have h1 : g'.left ≫ χ.left = (g'⁻¹ * z').left := by
        simpa using
          congrArg (fun q : 𝟙_ (Over (Spec (.of K))) ⟶ IdentityComponent G => q.left)
            (hχ g')
      calc (g'⁻¹ * z').left a = (g'.left ≫ χ.left) a := by rw [h1]
        _ = χ.left (g'.left a) := Scheme.Hom.comp_apply _ _ _
        _ = χ.left g := by rw [hg' a]
    -- factor `g'` and `u := g'⁻¹ * z'` through `W`
    have hrg : Set.range ⇑g'.left ⊆ Set.range ⇑W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro - ⟨a, rfl⟩
      rw [hg' a]; exact hgW
    have hru : Set.range ⇑(g'⁻¹ * z').left ⊆ Set.range ⇑W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro - ⟨a, rfl⟩
      rw [hu a]; exact hgE
    let gW : 𝟙_ (Over (Spec (.of K))) ⟶ UW :=
      Over.homMk (IsOpenImmersion.lift W.ι g'.left hrg) (by
        show IsOpenImmersion.lift W.ι g'.left hrg ≫
          W.ι ≫ (IdentityComponent G).hom = _
        rw [← Category.assoc, IsOpenImmersion.lift_fac W.ι g'.left hrg]
        exact Over.w g')
    let uW : 𝟙_ (Over (Spec (.of K))) ⟶ UW :=
      Over.homMk (IsOpenImmersion.lift W.ι (g'⁻¹ * z').left hru) (by
        show IsOpenImmersion.lift W.ι (g'⁻¹ * z').left hru ≫
          W.ι ≫ (IdentityComponent G).hom = _
        rw [← Category.assoc, IsOpenImmersion.lift_fac W.ι (g'⁻¹ * z').left hru]
        exact Over.w (g'⁻¹ * z'))
    have hgWι : gW ≫ ιU = g' := by
      apply Over.OverMorphism.ext
      exact IsOpenImmersion.lift_fac W.ι g'.left hrg
    have huWι : uW ≫ ιU = g'⁻¹ * z' := by
      apply Over.OverMorphism.ext
      exact IsOpenImmersion.lift_fac W.ι (g'⁻¹ * z').left hru
    have hfin : lift gW uW ≫ m = z' := by
      show lift gW uW ≫ (ιU ⊗ₘ ιU) ≫ MonObj.mul (X := IdentityComponent G) = z'
      rw [← Category.assoc, lift_map, hgWι, huWι, ← Hom.mul_def]
      exact mul_inv_cancel_left g' z'
    refine ⟨(lift gW uW).left pt, ?_⟩
    have h1 : (lift gW uW).left ≫ m.left = z'.left := by
      simpa using
        congrArg (fun q : 𝟙_ (Over (Spec (.of K))) ⟶ IdentityComponent G => q.left) hfin
    calc m.left ((lift gW uW).left pt)
        = ((lift gW uW).left ≫ m.left) pt := (Scheme.Hom.comp_apply _ _ _).symm
      _ = z'.left pt := by rw [h1]
      _ = z := hz' pt
  -- finitely many affine opens cover the image of `m`, hence all closed
  -- points; Jacobson density then covers everything
  have hSc : IsCompact (Set.range ⇑m.left) :=
    isCompact_range (Scheme.Hom.continuous m.left)
  have haff : ∀ x : (IdentityComponent G).left,
      ∃ V : (IdentityComponent G).left.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := (IdentityComponent G).left) (U := ⊤) (TopologicalSpace.Opens.mem_top x)
    exact ⟨V, hV, hxV⟩
  choose Vs hVaff hVmem using haff
  have hcovU : Set.range ⇑m.left ⊆
      ⋃ x : (IdentityComponent G).left, (Vs x : Set (IdentityComponent G).left) :=
    fun y _ => Set.mem_iUnion.mpr ⟨y, hVmem y⟩
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover
    (fun x : (IdentityComponent G).left => (Vs x : Set (IdentityComponent G).left))
    (fun x => (Vs x).isOpen) hcovU
  have hVuniv : ⋃ x ∈ t, (Vs x : Set (IdentityComponent G).left) = Set.univ := by
    by_contra hne
    obtain ⟨w, hw, hwc⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
      (isOpen_biUnion fun i _ => (Vs i).isOpen).isClosed_compl.isLocallyClosed
    exact hw (ht (hmem w hwc))
  exact ⟨hVuniv ▸ t.isCompact_biUnion fun i _ => (hVaff i).isCompact⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Formation of the identity component commutes with base change.**

Kleiman §5 Lem.~`lem:agps`~(3) conclusion (d): for any field extension
`K/k`, the natural comparison map `(G^0)_K → (G_K)^0` is an isomorphism of
`K`-schemes. The proof: `G^0` is geometrically connected as a connected
scheme with a `k`-rational point (EGA IV₂ 4.5.14), so its base change
`(G^0)_K` remains connected; it is also open and closed in `G_K`, so
coincides with the identity component `(G_K)^0`.

The statement-level pin asserts existence of: a `K`-group-scheme structure
on the base change `G ×_{Spec k} Spec K` (with appropriate
locally-of-finite-type instance), and an isomorphism on underlying schemes
identifying the two iterated constructions.

CLOSED (run 0005, session 0011): the `_grpInst` slot via
`CategoryTheory.Over.grpObjMkPullbackSnd`, the `_locFTInst` slot via
Mathlib's base-change stability of `LocallyOfFiniteType`, and the iso slot
(Stacks 04KS / EGA IV₂ 4.5.16) by the carrier identification
`fst⁻¹(G⁰-carrier) = (G_K)⁰-carrier` inside `|G ×ₖ Spec K|`:

- `⊆` (connectedness): `fst⁻¹(carrier)` is the image of the open immersion
  `pullback ι fst`, whose source is connected because
  `pullback (IdentityComponent G).hom φ` is connected — Mathlib's
  connected-pullback instance fed by
  `identityComponent_geometricallyConnected` and universal openness of
  morphisms to the spectrum of a field — and it contains the identity
  point of `G_K` (which lies over `e` by the base-change compatibility of
  the unit of `grpObjMkPullbackSnd`);
- `⊇` (clopen): `fst⁻¹(carrier)` is clopen and contains the identity point
  of `G_K`, hence contains its connected component.

The isomorphism is `IsOpenImmersion.isoOfRangeEq` composed with the
pasting isomorphism `pullbackRightPullbackFstIso`. -/
theorem IdentityComponent.baseChangeIso {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom]
    (K : Type u) [Field K] [Algebra k K] :
    let φ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k K))
    let G_K : Over (Spec (CommRingCat.of K)) :=
      Over.mk (CategoryTheory.Limits.pullback.snd G.hom φ)
    Nonempty (Σ' (_grpInst : GrpObj G_K)
                 (_locFTInst : LocallyOfFiniteType G_K.hom),
      (IdentityComponent G_K).left ≅
        CategoryTheory.Limits.pullback (IdentityComponent G).hom φ) := by
  intro φ G_K
  -- `GrpObj G_K` via the category-theoretic base-change lemma
  -- `CategoryTheory.Over.grpObjMkPullbackSnd`. The instance bridge
  -- `[GrpObj G] ⟹ [GrpObj (Over.mk G.hom)]` is by defeq (`G = Over.mk G.hom`
  -- when `G` is an over-category object whose right component is the unique
  -- inhabitant of `Discrete PUnit`). `letI` (not `haveI`) so the group
  -- structure stays definitionally transparent for the carrier computation.
  letI hG : GrpObj (Over.mk G.hom) := ‹GrpObj G›
  letI hGK_grp : GrpObj G_K := CategoryTheory.Over.grpObjMkPullbackSnd
  -- `LocallyOfFiniteType G_K.hom`: `G_K.hom = pullback.snd G.hom φ` is the
  -- base change of `G.hom` along `φ`; `LocallyOfFiniteType` is stable
  -- under base change (Mathlib instance).
  haveI hGK_lft : LocallyOfFiniteType G_K.hom :=
    (inferInstance : LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.hom φ))
  refine ⟨⟨hGK_grp, hGK_lft, ?_⟩⟩
  -- §1: connectivity substrate.
  letI := identityComponent_geometricallyConnected G
  haveI : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : Subsingleton ↥(𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : UniversallyOpen (IdentityComponent G).hom := inferInstance
  haveI : ConnectedSpace ↥(Spec (CommRingCat.of K)) := connectedSpace_spec_of_isDomain K
  haveI hP : ConnectedSpace ↥(pullback (IdentityComponent G).hom φ) := inferInstance
  haveI hP' : ConnectedSpace ↥(pullback ((identityComponentCarrier G).ι ≫ G.hom) φ) := hP
  haveI hQ : ConnectedSpace
      ↥(pullback (identityComponentCarrier G).ι (pullback.fst G.hom φ)) :=
    ((pullbackRightPullbackFstIso G.hom φ
      (identityComponentCarrier G).ι).hom.homeomorph.connectedSpace_iff).mpr hP'
  -- §2: the identity point of `G_K` lies over the identity point of `G`
  -- (base-change compatibility of the unit of `grpObjMkPullbackSnd`).
  have hεfst : (Functor.LaxMonoidal.ε (Over.pullback φ)).left ≫
      pullback.fst (𝟙_ (Over (Spec (CommRingCat.of k)))).hom φ = φ := by
    have hcond : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of k)))).hom φ =
        pullback.snd (𝟙_ (Over (Spec (CommRingCat.of k)))).hom φ ≫ φ := by
      simpa using pullback.condition
        (f := (𝟙_ (Over (Spec (CommRingCat.of k)))).hom) (g := φ)
    rw [hcond, CategoryTheory.Over.ε_pullback_left, ← Category.assoc]
    erw [IsIso.inv_hom_id]
    rw [Category.id_comp]
  have hfst : ⇑(pullback.fst G.hom φ) (identitySectionPoint G_K) =
      identitySectionPoint G := by
    have h1 := congrArg
      (fun m : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G_K =>
        ⇑m.left.base (default : ↥(Spec (CommRingCat.of K))))
      (CategoryTheory.Over.grpObjMkPullbackSnd_one (f := G.hom) (g := φ))
    calc ⇑(pullback.fst G.hom φ) (identitySectionPoint G_K)
        = ⇑(pullback.fst G.hom φ)
            (⇑(MonObj.one (X := G_K)).left.base
              (default : ↥(Spec (CommRingCat.of K)))) := rfl
      _ = ⇑(pullback.fst G.hom φ)
            (⇑(Functor.LaxMonoidal.ε (Over.pullback φ) ≫
              (Over.pullback φ).map (MonObj.one (X := Over.mk G.hom))).left.base
              (default : ↥(Spec (CommRingCat.of K)))) :=
          congrArg (⇑(pullback.fst G.hom φ)) h1
      _ = ⇑(pullback.lift
            (pullback.fst (𝟙_ (Over (Spec (CommRingCat.of k)))).hom φ ≫
              (MonObj.one (X := Over.mk G.hom)).left)
            (pullback.snd (𝟙_ (Over (Spec (CommRingCat.of k)))).hom φ)
            (by rw [Category.assoc, Over.w (MonObj.one (X := Over.mk G.hom))]
                exact pullback.condition) ≫
            pullback.fst (Over.mk G.hom).hom φ).base
            (⇑(Functor.LaxMonoidal.ε (Over.pullback φ)).left.base
              (default : ↥(Spec (CommRingCat.of K)))) := rfl
      _ = ⇑(pullback.fst (𝟙_ (Over (Spec (CommRingCat.of k)))).hom φ ≫
            (MonObj.one (X := Over.mk G.hom)).left).base
            (⇑(Functor.LaxMonoidal.ε (Over.pullback φ)).left.base
              (default : ↥(Spec (CommRingCat.of K)))) := by
          rw [pullback.lift_fst]
      _ = ⇑(MonObj.one (X := Over.mk G.hom)).left.base
            (⇑((Functor.LaxMonoidal.ε (Over.pullback φ)).left ≫
              pullback.fst (𝟙_ (Over (Spec (CommRingCat.of k)))).hom φ).base
              (default : ↥(Spec (CommRingCat.of K)))) := rfl
      _ = ⇑(MonObj.one (X := Over.mk G.hom)).left.base
            (⇑φ.base (default : ↥(Spec (CommRingCat.of K)))) :=
          congrArg
            (fun m : (𝟙_ (Over (Spec (CommRingCat.of K)))).left ⟶
                Spec (CommRingCat.of k) =>
              ⇑(MonObj.one (X := Over.mk G.hom)).left.base
                (⇑m.base (default : ↥(Spec (CommRingCat.of K))))) hεfst
      _ = ⇑(MonObj.one (X := Over.mk G.hom)).left.base
            (default : ↥(Spec (CommRingCat.of k))) :=
          congrArg (⇑(MonObj.one (X := Over.mk G.hom)).left.base)
            (Subsingleton.elim _ _)
      _ = identitySectionPoint G := rfl
  -- §3: the two carriers coincide as subsets of `|G_K|`.
  have hclopenG : IsClopen (identityComponentCarrier G : Set G.left) := by
    show IsClopen (connectedComponent (identitySectionPoint G))
    exact ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
  have hrange : Set.range
        ⇑(pullback.snd (identityComponentCarrier G).ι (pullback.fst G.hom φ)) =
      ⇑(pullback.fst G.hom φ) ⁻¹' (identityComponentCarrier G : Set G.left) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    simp
  have hset : ⇑(pullback.fst G.hom φ) ⁻¹' (identityComponentCarrier G : Set G.left) =
      (identityComponentCarrier G_K : Set G_K.left) := by
    apply Set.Subset.antisymm
    · -- preimage ⊆ carrier: the preimage is a connected set through `e_{G_K}`.
      have hmem : identitySectionPoint G_K ∈
          ⇑(pullback.fst G.hom φ) ⁻¹' (identityComponentCarrier G : Set G.left) :=
        Set.mem_preimage.mpr (by rw [hfst]; exact mem_connectedComponent)
      rw [← hrange] at hmem ⊢
      exact (isPreconnected_range
        (Scheme.Hom.continuous _)).subset_connectedComponent hmem
    · -- carrier ⊆ preimage: the preimage is clopen and contains `e_{G_K}`.
      show connectedComponent (identitySectionPoint G_K) ⊆ _
      refine IsClopen.connectedComponent_subset
        (hclopenG.preimage (Scheme.Hom.continuous _)) ?_
      exact Set.mem_preimage.mpr (by rw [hfst]; exact mem_connectedComponent)
  -- §4: assemble the isomorphism.
  have hrangeEq : Set.range ⇑(identityComponentCarrier G_K).ι =
      Set.range ⇑(pullback.snd (identityComponentCarrier G).ι (pullback.fst G.hom φ)) := by
    rw [Scheme.Opens.range_ι, hrange, hset]
  exact IsOpenImmersion.isoOfRangeEq (identityComponentCarrier G_K).ι
      (pullback.snd (identityComponentCarrier G).ι (pullback.fst G.hom φ)) hrangeEq ≪≫
    pullbackRightPullbackFstIso G.hom φ (identityComponentCarrier G).ι

set_option backward.isDefEq.respectTransparency false in
/-- Descent of quasi-compactness from the algebraic closure: `|G⁰|` is
compact for any base field `k`, since the projection from the base change to
`K̄ = AlgebraicClosure k` is surjective and `(G_K̄)⁰ ≅ (G⁰)_K̄` is compact by
the algebraically closed core lemma
`identityComponent_compactSpace_of_isAlgClosed` transported along
`baseChangeIso`. -/
private theorem identityComponent_compactSpace
    {k : Type u} [Field k] (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    CompactSpace (IdentityComponent G).left := by
  obtain ⟨⟨grpb, lftb, isob⟩⟩ := IdentityComponent.baseChangeIso G (AlgebraicClosure k)
  letI := grpb
  haveI := lftb
  haveI h1 : CompactSpace ↥(pullback (IdentityComponent G).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
    @Homeomorph.compactSpace _ _ _ _
      (identityComponent_compactSpace_of_isAlgClosed _) isob.hom.homeomorph
  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : Nonempty ↥(Spec (CommRingCat.of (AlgebraicClosure k))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (AlgebraicClosure k)))
  constructor
  rw [← range_eq_univ (pullback.fst (IdentityComponent G).hom
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))]
  exact isCompact_range (Scheme.Hom.continuous _)

set_option backward.isDefEq.respectTransparency false in
/-- Descent of irreducibility: `(IdentityComponent G).hom` is geometrically
irreducible. For any field extension `K/k`, the base change `(G⁰)_K`
receives a surjective projection from `(G⁰)_K̄` (`K̄ = AlgebraicClosure K`,
via the pasting isomorphism for iterated pullbacks), and `(G⁰)_K̄ ≅ (G_K̄)⁰`
is irreducible by the algebraically closed core lemma
`identityComponent_irreducibleSpace_of_isAlgClosed` transported along
`baseChangeIso`; irreducibility passes along surjective continuous maps. -/
private theorem identityComponent_geometricallyIrreducible
    {k : Type u} [Field k] (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    GeometricallyIrreducible (IdentityComponent G).hom := by
  constructor
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  obtain ⟨⟨grpL, lftL, isoL⟩⟩ := IdentityComponent.baseChangeIso G (AlgebraicClosure K)
  letI := grpL
  haveI := lftL
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq k K (AlgebraicClosure K)]
  haveI h1 : IrreducibleSpace ↥(pullback (IdentityComponent G).hom
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
    rw [← hφ]
    exact isoL.hom.homeomorph.irreducibleSpace_iff.mp
      (identityComponent_irreducibleSpace_of_isAlgClosed _)
  haveI h2 : IrreducibleSpace ↥(pullback
      (pullback.snd (IdentityComponent G).hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) :=
    (pullbackLeftPullbackSndIso (IdentityComponent G).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (AlgebraicClosure K))))).hom.homeomorph.irreducibleSpace_iff.mpr h1
  haveI : Subsingleton ↥(Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : Nonempty ↥(Spec (CommRingCat.of (AlgebraicClosure K))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (AlgebraicClosure K)))
  exact (pullback.fst (pullback.snd (IdentityComponent G).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap K (AlgebraicClosure K))))).surjective.irreducibleSpace
    (Scheme.Hom.continuous _)

/-- **The identity component is of finite type and geometrically irreducible.**

Kleiman §5 Lem.~`lem:agps`~(3) conclusion (c): the open subgroup `G^0` of
a `k`-group scheme `G` locally of finite type is itself
locally-of-finite-type-plus-quasi-compact (i.e., of finite type) over `k`,
and is geometrically irreducible. The proof reduces (after base change to
`\bar k`) to picking a nonempty irreducible open subset `U ⊆ G^0`; the
translates `zg⁻¹U` give an open cover of the closed points of `G^0` by
irreducible neighbourhoods, extended to all points by Jacobson density, so
with connectedness this gives irreducibility globally (EGA I 6.1.10). The
image `α(W × W) ⊆ G^0` of an affine open `W ∋ e` under the group law is
quasi-compact and contains all closed points, so finitely many affine opens
cover `G^0` and `G^0` is quasi-compact.

CLOSED (run 0009, T6): `LocallyOfFiniteType` as before (open immersion
composed with `G.hom`); `QuasiCompact` via `identityComponent_compactSpace`
(Kleiman's product trick over the algebraic closure + Jacobson density +
descent along the surjective base-change projection) together with the
affine-target characterisation of quasi-compactness;
`GeometricallyIrreducible` via `identityComponent_geometricallyIrreducible`
(translation of an irreducible open through all closed points over the
algebraic closure, EGA I 6.1.10, and descent along the surjective
projection from the algebraic closure of each field extension). -/
theorem IdentityComponent.isFiniteTypeGeometricallyIrreducible
    {k : Type u} [Field k]
    (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] :
    LocallyOfFiniteType (IdentityComponent G).hom ∧
      QuasiCompact (IdentityComponent G).hom ∧
      GeometricallyIrreducible (IdentityComponent G).hom := by
  refine ⟨identityComponent_locallyOfFiniteType G, ?_,
    identityComponent_geometricallyIrreducible G⟩
  haveI h : CompactSpace (IdentityComponent G).left := identityComponent_compactSpace G
  exact HasAffineProperty.iff_of_isAffine.mpr h

end GroupScheme

/-! ## §2. The identity component of the Picard scheme

We specialise the abstract identity-component substrate to
`G = PicScheme C`, the Picard scheme of a smooth proper geometrically
integral curve `C/k` (from sibling `Picard/FGAPicRepresentability.lean`).

Blueprint reference: `def:pic_zero_subscheme` (Kleiman §5 opening + Prp.
`prp:pic0`). -/

namespace Scheme

/-- The **identity component of the Picard scheme** `Pic⁰_{C/k}`.

Defined as the identity component
`GroupScheme.IdentityComponent (PicScheme C)` of the Picard scheme
`Pic_{C/k}` (from sibling `Picard/FGAPicRepresentability.lean`,
`AlgebraicGeometry.Scheme.PicScheme`). By
`GroupScheme.IdentityComponent.isOpenSubgroupScheme`, `Pic⁰_{C/k}` is an
open and closed subgroup scheme of `Pic_{C/k}` of finite type over `k`,
geometrically irreducible, and its formation commutes with extension of the
base field.

Run 0008: the body is REAL — it unwinds to
`GroupScheme.IdentityComponent (PicScheme C)`, as the iter-186 docstring
promised. The two ingredients landed with the run-0008 FGA rewire: the
group structure `GrpObj (PicScheme C)` is genuinely proved (Yoneda
transport, `PicScheme.groupSchemeStructure`), and local finiteness is the
new typed-sorry carrier `PicSchemeLocallyOfFiniteType` (true by Kleiman §4
Thm `th:main`(1)). Consequently all the §1 substrate theorems
(`isOpenSubgroupScheme`, `isSubgroupHomomorphism`,
`identityComponent_geometricallyConnected`, `baseChangeIso`) now apply to
`Pic⁰_{C/k}` definitionally. -/
noncomputable def Pic0Scheme {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Over (Spec (.of k)) :=
  GroupScheme.IdentityComponent (PicScheme C)

/-! ## §3. The degree map

The disjoint-union structure of `Pic_{C/k}` (a disjoint union of open
quasi-projective `k`-subschemes, indexed by Hilbert polynomial via
`PicScheme.smoothProperQuotient`) stratifies its `T`-points by the leading
coefficient of the Hilbert polynomial of a representing invertible sheaf
relative to a fixed degree-one polarisation. On `k`-points this gives the
**degree map** `Pic_{C/k}(k) → ℤ`.

Blueprint reference: `def:divisor_degree_pic` (Milne III.1, p.~88). -/

namespace PicScheme

/-- The **degree map** `Pic_{C/k}(k) → ℤ`.

Sends a `k`-point `λ ∈ Pic_{C/k}(k)` --- a morphism
`Spec k ⟶ (PicScheme C).left` --- to the leading coefficient of the
Hilbert polynomial of a representing invertible sheaf `L` on `C` (relative
to a fixed degree-one polarisation `O_C(1)`). By Riemann--Roch,
`χ(C, L ⊗ O_C(n)) = n · deg L + 1 - g`, so the degree is the leading
coefficient of `Φ_L(n)`, well-defined on the isomorphism class `[L]` and on
the `k`-point `λ` (because `PicScheme C` represents the étale-sheafified
relative Picard functor).

The degree map is a group homomorphism for the additive structure on
`Pic_{C/k}(k)` (tensor product on `L`) and the standard `(ℤ, +)`. The full
group-homomorphism refinement / functoriality in `k` lives as a follow-up
lemma in iter-186+; the file-skeleton pins only the underlying function.

iter-186+: the body extracts the representing invertible sheaf from
`(PicScheme.representable C)`, forms its Hilbert polynomial via the project's
Hilbert-polynomial machinery (sibling `Picard/QuotScheme.lean`), and returns
the leading coefficient. For the iter-185 file-skeleton the body is a typed
`sorry`. -/
noncomputable def degree {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C] :
    (Spec (.of k) ⟶ (PicScheme C).left) → ℤ :=
  sorry

end PicScheme

/-! ## §4. `Pic⁰_{C/k}` is an abelian variety

The terminal statement of the chapter identifies `Pic⁰_{C/k}` with an
abelian variety of dimension `g(C)` --- the Jacobian variety of `C`. In
this project, "abelian variety" is the conjunction of the four properties
`[GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]`
threaded through `AlgebraicJacobian.AbelianVarietyRigidity` and consumed by
`AlgebraicJacobian.Albanese.AlbaneseUP`.

Blueprint reference: `thm:pic_zero_is_abelian_variety` (Kleiman §5
Ex.~`ex:jac` + Rmk.~`rmk:Jac`; cf. Milne §I.1, Rmk. III.1.4(e)). -/

namespace Pic0Scheme

/- `Pic0Scheme.isAbelianVariety` (blueprint pin
`thm:pic_zero_is_abelian_variety`) MOVED (run 0008, T5) to sibling
`Picard/Pic0AbelianVariety.lean`, where it is assembled sorry-free from the
per-conjunct theorems `Pic0.proper` / `Pic0.smooth` /
`Pic0.geometricallyIrreducible` / `Pic0.grpObj` of that chapter. -/

/-- **Dimension of `Pic⁰_{C/k}` equals the genus of `C`.**

Milne~§III.1, Rmk.~1.4(e): "The dimension of `J` is the genus of `C`".
For a smooth proper geometrically integral curve `C/k` of genus
`g = g(C)`, the topological Krull dimension of the underlying scheme of
`Pic⁰_{C/k}` equals `g(C)`. By Kleiman~§5 Cor.~`cor:sm`, the inequality
`dim Pic_{C/k} ≤ dim_k H¹(C, O_C)` is always an equality at points where
`Pic_{C/k}` is smooth, and for smooth proper curves
(`SmoothOfRelativeDimension 1 C.hom`) the identity component is smooth
(Kleiman~§5 Ex.~`ex:jac`), so the dimension equals `dim_k H¹(C, O_C) = g(C)`
by `def:genus`. -/
theorem finrank_eq_genus {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    topologicalKrullDim (Pic0Scheme C).left = (AlgebraicGeometry.genus C : WithBot ℕ∞) :=
  sorry

/-- **`k`-points of `Pic⁰_{C/k}` are the kernel of the degree map.**

Milne~§III.1, p.~88: `Pic⁰(C)` is the group of isomorphism classes of
invertible sheaves of degree zero on `C`. For a smooth proper geometrically
integral curve `C/k`, a `k`-point `λ ∈ Pic_{C/k}(k)` lies in the image of
the inclusion `Pic⁰_{C/k} ↪ Pic_{C/k}` (the inclusion of
`def:pic_zero_subscheme`, packaged here via the existence of the
inclusion morphism) if and only if `degree C λ = 0`.

The statement-level pin packages two pieces: existence of the inclusion
morphism `Pic⁰_{C/k} ⟶ Pic_{C/k}` (extracted from
`IdentityComponent.isOpenSubgroupScheme` once `PicScheme C` has the
`GrpObj` + `LocallyOfFiniteType` instances), together with the
characterisation of `k`-points factoring through it as those with degree
zero. -/
theorem kPoints_iff_kerDegree {k : Type u} [Field k]
    (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
    [GeometricallyIntegral C.hom] [HasPicScheme C]
    [PicScheme.PicSchemeLocallyOfFiniteType C] :
    Nonempty (Σ' (inc : (Pic0Scheme C).left ⟶ (PicScheme C).left),
      ∀ (lambda : Spec (.of k) ⟶ (PicScheme C).left),
        (∃ mu : Spec (.of k) ⟶ (Pic0Scheme C).left, mu ≫ inc = lambda) ↔
          PicScheme.degree C lambda = 0) :=
  sorry

end Pic0Scheme

end Scheme

end AlgebraicGeometry
