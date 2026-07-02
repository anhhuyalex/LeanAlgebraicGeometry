# Analogy: Identity-component substrate — `G^0 × G^0` connectedness and `GrpObj` inheritance

## Mode
cross-domain-inspiration

## Slug
lane-a3i-isconnected-prod

## Iteration
191

## Structural problem (abstracted)

For a group object `G` in `Sch/k` with connected identity component `G^0 ⊂ G`
carrying a `k`-rational point (the identity section), we need (i) the
underlying topological space of the fiber-product `G^0 ×_k G^0` to be
connected (substrate for showing the multiplication morphism restricts to
`G^0 → G^0 → G^0`), and (ii) the structure of a group object on `G^0`
inherited from `G` via an open immersion. Sub-question (i) is the
EGA IV₂ 4.5.8 step that has blocked four iters of project work; sub-question
(ii) is a bridging issue between the project's `Over.mk (pullback.snd _ _)`
shape and Mathlib's `asOver M S` shape via `OverClass`.

## Failed approaches (from directive)

- iter-186/187: scaffold `isSubgroupHomomorphism` as a sorry, defer to
  helpers. Blocked because the helper itself needs the connected-product
  substrate, which is the actual gap.
- iter-188: full topology-side closure of `identityComponent_locallyConnectedSpace`
  via EGA I 6.1.9 (locally Noetherian ⟹ locally connected). Succeeded
  because that step is purely topological. The 4.5.8 step is geometric
  (needs a hypothesis upgrading "connected" to "geometrically connected"),
  so the topology-side recipe doesn't extend.
- iter-189: explicit `change` unfold of `(IdentityComponent G).hom` cleared
  `LocallyOfFiniteType` inline. The other two conjuncts (`QuasiCompact`,
  `GeometricallyIrreducible`) require the group-action argument, which
  needs the substrate.

## Analogues found

Ranked by porting cost (lowest first).

### Analogue: `Mathlib.AlgebraicGeometry.Geometrically.Connected` — the `ConnectedSpace (pullback f g)` instance

- **Domain**: algebraic geometry / scheme theory (same general area, different
  sub-file). Cite: `Mathlib/AlgebraicGeometry/Geometrically/Connected.lean:100-102`
  at SHA b80f22719410.

- **Same structural problem there**: Given a morphism `f : X ⟶ S` of schemes
  that is geometrically connected and universally open, and another morphism
  `g : Y ⟶ S` whose source `Y` is a connected topological space, the
  scheme-theoretic fiber product `X ×ₛ Y` is again a connected topological
  space. This is the direct algebro-geometric realization of EGA IV₂ 4.5.8
  ("product of geometrically connected schemes is connected").

- **Technique**: The instance is one rewriting step away from the lemma
  `GeometricallyConnected.connectedSpace` (same file, line 89), which says
  that a geometrically connected morphism with open underlying map and
  connected target has a connected source. The pullback case is obtained
  from this lemma by base-changing along `g`: the second projection
  `pullback.snd : X ×ₛ Y ⟶ Y` inherits `GeometricallyConnected` from `f`
  (line 53, stability under base change), inherits `IsOpenMap` because
  pullback of universally-open is open (`UniversallyOpen.snd`, line 86 of
  `UniversallyOpen.lean`), and `Y` is the connected target. So the instance
  is two lines of inferInstance plumbing on top of the
  `GeometricallyConnected.connectedSpace` lemma — which itself is a
  three-line preimage-of-connected argument.

- **Mapping to project**: Take `f = g = (IdentityComponent G).hom : G^0 ⟶ Spec k`.
  Specialize to `Y = G^0` (which the project already exhibits as a
  `ConnectedSpace` because `(identityComponentCarrier G)` is defined as the
  topological connected component of the identity point and the open-subscheme
  topology coincides with the subspace topology). The instance then
  produces `ConnectedSpace ↥(pullback (IdentityComponent G).hom (IdentityComponent G).hom)`,
  which **is** the substrate needed for `isSubgroupHomomorphism`.

- **Premises the project still has to discharge**:
  1. `UniversallyOpen (IdentityComponent G).hom`. This auto-derives from
     `Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean:149-150`,
     which declares `[IsIntegral Y] [Subsingleton Y] → UniversallyOpen f`
     as a low-priority instance. Spec of a field is integral and a
     subsingleton, so both premises hold for `Y = Spec (.of k)`. **Zero
     project-side LOC** — `inferInstance` should fire.
  2. `ConnectedSpace ↥(IdentityComponent G).left`. Comes free from the
     definition `(identityComponentCarrier G) = connectedComponent ⟨identitySectionPoint G⟩`
     plus the standard `Scheme.Opens.instIsOpenImmersionι` topology
     coincidence. **~5 project-side LOC** to assemble the instance.
  3. **`GeometricallyConnected (IdentityComponent G).hom`** — this is the
     genuine substrate gap. Mathlib does NOT have a "connected scheme with
     a k-rational section ⟹ geometrically connected" lemma at b80f227
     (EGA IV₂ 4.5.14 / Stacks 04KU). See "Porting cost" below.

- **Porting cost**: medium. The Mathlib substrate is already in place — the
  pullback-connected instance is FREE. The remaining work is **one**
  project-side helper, `geometricallyConnected_of_connected_of_section`, of
  shape: given `f : X ⟶ Spec k` with `ConnectedSpace X` and a morphism
  `s : Spec k ⟶ X` with `s ≫ f = 𝟙 _`, conclude `GeometricallyConnected f`.
  Realistic estimate: **80–120 LOC** (matches the iter-189 prover's original
  ~80-150 LOC estimate, but here the LOC is concentrated in ONE clean
  abstract helper instead of spread across pullback-connectedness machinery
  the project would have had to build itself). The classical proof
  (Stacks 04KV) descends a hypothetical disconnection of `X_K` to a
  disconnection of `X` by exploiting the section: a clopen partition
  `X_K = U ⊔ V` would force the K-rational point pulled from the section to
  land in exactly one of `U, V`, and the image in `X` would be a clopen
  partition whose nonemptiness is witnessed by the section. The proof is
  short on paper but needs Mathlib bridging for "base-change clopen
  partition descends along surjective faithfully-flat" — that is the bulk
  of the LOC.

- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Mathlib.CategoryTheory.Monoidal.Cartesian.Over.grpObjMkPullbackSnd`

- **Domain**: category theory (cartesian monoidal). Cite:
  `Mathlib/CategoryTheory/Monoidal/Cartesian/Over.lean:311-313` at SHA
  b80f22719410.

- **Same structural problem there**: Given a morphism `f : X ⟶ S` such that
  `Over.mk f` carries a `GrpObj` instance, the pullback morphism
  `pullback.snd f g : pullback f g ⟶ T` (for any `g : T ⟶ S`) carries a
  `GrpObj` instance on `Over.mk (pullback.snd f g)`. This is the
  base-change-preserves-group-object statement, stated in maximal
  generality (any cartesian monoidal category with pullbacks; specializing
  to `Sch` is automatic).

- **Technique**: The construction goes through the
  `(Over.pullback g).mapGrp.obj` functor, which is the categorical
  formulation of "base change preserves group objects" via the
  functoriality of `mapGrp` (the functor from grouplike objects in one
  cartesian category to grouplike objects in another, induced by a
  product-preserving functor). The proof is one line of functor-image
  unfolding — no scheme-specific content.

- **Mapping to project**: The project's `IdentityComponent.baseChangeIso`
  needs `GrpObj G_K` for `G_K := Over.mk (pullback.snd G.hom φ)`. The
  iter-190 directive worried that Mathlib's
  `Scheme.GrpObjAsOverPullback` (`Pullbacks.lean:808`) is stated in terms
  of `asOver M S` rather than `Over.mk`, and would require explicit
  `OverClass` adapters to consume. **The directive's worry is incorrect** —
  Mathlib has the more elementary lemma `grpObjMkPullbackSnd` at the
  category-theory level whose conclusion is *literally*
  `GrpObj (Over.mk (pullback.snd f g))`, the project's exact shape. The
  scheme-side `GrpObjAsOverPullback` is just the `asOver`-wrapped
  re-export of this; consuming `grpObjMkPullbackSnd` directly avoids the
  OverClass bridging entirely.

- **Porting cost**: low. ~10-20 LOC to apply the lemma directly in
  `baseChangeIso`: `instance grpObjGK : GrpObj G_K := grpObjMkPullbackSnd`
  (with appropriate explicit binding of `f = G.hom`, `g = φ`). The
  premise `[GrpObj (Over.mk G.hom)]` is satisfied because `G` itself is
  an `Over (Spec k)` and `Over.mk G.hom = G` definitionally for any `G`
  constructed via `Over.mk` (which the project does throughout). If
  the project's `G` is *not* constructed via `Over.mk` in the relevant
  call site, a single `Over.mk G.hom = G` defeq or `Over.isoMk_refl`
  rewrite bridges them.

- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Mathlib.Topology.Algebra.Group.Basic.Subgroup.connectedComponentOfOne`

- **Domain**: topology / topological groups (distant from the project's
  scheme setting, but EXACT same structural shape: connected component of
  identity in a group object yields a sub-group-object).
  Cite: `Mathlib/Topology/Algebra/Group/Basic.lean:740-745` (the definition)
  and `:718-727` (the multiplication-stability proof
  `mul_mem_connectedComponent_one`) and `:729-736` (the inverse-stability
  proof `inv_mem_connectedComponent_one`), at SHA b80f22719410.

- **Same structural problem there**: For a topological group `G`, the
  connected component of the identity is a subgroup. The closure operations
  (multiplication, inversion) preserve it.

- **Technique** — this is the *interesting* analogue, because Mathlib's
  proof technique *sidesteps* the "product of two connected sets is
  connected" question entirely. For multiplication, instead of arguing
  "(conn cpt of 1) × (conn cpt of 1) is connected, its image under mul
  is connected, contains 1, hence ⊆ (conn cpt of 1)", Mathlib uses
  ONE-COORDINATE-AT-A-TIME continuity. The proof of
  `mul_mem_connectedComponent_one` (line 719) takes `g, h ∈ cc 1` and:
  rewrites `cc 1 = cc g` (using `g ∈ cc 1`); shows `g ∈ cc (g*h)` by
  applying continuity of `x ↦ g·x` (a single-variable continuous map!) to
  the path inside `cc h` from `1` to `h`, producing a path inside `cc (g*h)`
  from `g·1 = g` to `g·h`; concludes `cc g = cc (g*h)` and hence
  `g*h ∈ cc g = cc 1`. Mul stability without ever forming a product
  topology argument.

- **Mapping to project**: The technique **does not directly port to the
  scheme setting**. Reason: in topology, the connected component of a point
  is a subset of the underlying space, so "(g, h) ↦ g·h sends cc(1) × cc(1)
  into cc(1)" is a set-theoretic claim about pointwise multiplication on the
  underlying space. In the scheme setting, the corresponding set-theoretic
  claim would be about `|G^0| × |G^0|` and pointwise multiplication on `|G|`
  — but the underlying topological space of the *scheme* `G^0 ×_k G^0` is
  strictly larger than `|G^0| × |G^0|` over non-algebraically-closed `k`
  (it contains additional "generic" points whose images in `|G|` do not
  factor through pointwise mul). So the one-coordinate-continuity trick
  cannot replace the substrate. **But the analogue still gives the project
  an architectural insight**: define the project's `GrpObj G^0` via
  *carrier-level* multiplication-stability and *scheme-level* base change
  separately, treating "G^0 is closed under mul as a set in |G|" and
  "G^0 ×_k G^0 → G factors through G^0 as a scheme morphism" as separate
  obligations. The set-level obligation IS closable by the topological-group
  trick (the path on `|G|` from `e·e` to `(e·h)` runs through `e ∈ |G^0|`'s
  open neighbourhoods and stays in `|G^0|` because `|G^0|` is the connected
  component of `e`). The scheme-level obligation reduces to the
  substrate analogue above.

- **Porting cost**: high. The technique is structurally beautiful but does
  not eliminate the substrate need in the scheme case. **The value is
  *architectural***: if the project is willing to refactor
  `isSubgroupHomomorphism` to separately establish (a) the set-theoretic
  closure of |G^0| under |μ| (which the topological-group trick CAN
  provide; this is what `mul_mem_connectedComponent_one` literally proves
  about |G| viewed as a topological space carrying a topological-group
  structure inherited from the scheme), and (b) the scheme-level factoring
  through G^0, the project gets (a) for ~20 LOC by direct port and (b) is
  what the substrate analogue above closes. The net cost is the same; the
  win is conceptual clarity (the burden is concentrated on the substrate
  alone, not entangled with mul-stability).

- **Verdict**: PARTIAL_ANALOGUE — technique informs architecture but
  cannot replace the substrate.

## Top suggestion

The planner should prioritize the **first analogue**:
`Mathlib/AlgebraicGeometry/Geometrically/Connected.lean:100-102`, plus
`Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean:149-150`. These
two instances together provide the entire EGA IV₂ 4.5.8 substrate the
project has been planning to build — for FREE. The only remaining gap is
**`GeometricallyConnected (IdentityComponent G).hom`**, which reduces to a
single project-side helper:

> `geometricallyConnected_of_connected_of_section : ∀ {X : Scheme} {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (s : Spec (.of k) ⟶ X), s ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f`

This helper is **Stacks 04KU / EGA IV₂ 4.5.14**, ~80–120 LOC, ONE file,
ONE declaration. The first call site is
`AlgebraicJacobian/Picard/IdentityComponent.lean` at `isSubgroupHomomorphism`
(line 332), where after the helper closes the substrate the project should
be able to factor `μ : G^0 ×_k G^0 → G` through G^0 by the standard
"continuous image of connected containing identity ⊆ connected component
of identity" argument.

**For the second sub-problem** (`GrpObj` inheritance via base change), the
planner should use `grpObjMkPullbackSnd` from
`Mathlib/CategoryTheory/Monoidal/Cartesian/Over.lean:312` directly,
**not** the scheme-side `GrpObjAsOverPullback` wrapper. The category-theory
version's conclusion is the project's exact `Over.mk (pullback.snd ...)`
shape, dodging the `OverClass` bridging the iter-190 directive flagged.
~10-20 LOC of plumbing in `baseChangeIso`.

**Total project-side build**: ~100–140 LOC across two files. This is
COMPARABLE to (and possibly less than) the iter-189 prover's original
80-150 LOC estimate for `Scheme.isConnected_pullback_of_isGeometricallyConnected`
— but concentrated in ONE clean abstract helper plus minor plumbing,
rather than a custom pullback-connectedness substrate the project would
otherwise have had to write from scratch.
