# Analogy: Stacks 037Q iff-direction / Stacks 04KU section criterion for geometric connectedness

## Mode
api-alignment (with cross-domain-inspiration follow-on, since no
direct Mathlib alignment exists)

## Slug
lane-a3i-stacks-04kv

## Iteration
195

## Question

Lane A.3.i (`AlgebraicJacobian/Picard/IdentityComponent.lean`) needs
the helper
`geometricallyConnected_of_connected_of_section : ∀ {X : Scheme}
{k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (s : Spec (.of k) ⟶ X),
s ≫ f = 𝟙 _ → [ConnectedSpace X] → GeometricallyConnected f`
(Stacks 04KU / EGA IV₂ 4.5.14). The iter-194 prover restructured the
body to expose the residual gap precisely:
`ConnectedSpace ↥(pullback f (Spec.map (ofHom (algebraMap k K))))`
with `Nonempty` of the pullback already in hand via the base-changed
section. The iter-194 plan-phase elevated the iff-direction of
Stacks 037Q to a first-class blueprint lemma
(`lem:geometricallyConnected_of_connected_of_section` in
`Picard_IdentityComponent.tex`). Iter-195 progress-critic flags Lane
A.3.i CHURNING-regressive (sorry count 5 → 7 → 8 → 9 over four
iters; helpers added without sorry-elimination).

## Project artifact(s)
- `AlgebraicJacobian/Picard/IdentityComponent.lean:382-479` —
  `geometricallyConnected_of_connected_of_section` (the residual
  sorry, post iter-194 restructure).
- `AlgebraicJacobian/Picard/IdentityComponent.lean:540-574` —
  `identityComponent_geometricallyConnected` consumer (downstream).
- `AlgebraicJacobian/Picard/IdentityComponent.lean:637-707` —
  `IdentityComponent.baseChangeIso` consumer (downstream).
- `blueprint/src/chapters/Picard_IdentityComponent.tex:208-266` —
  blueprint statement + proof sketch.

## Decisions identified

### Decision: API for "connected + k-rational section ⟹ geometrically connected" (Stacks 04KU)

- **Mathlib idiom**: there is NO Mathlib idiom for this implication
  at SHA b80f227. Mathlib's
  `Mathlib.AlgebraicGeometry.Geometrically.Connected` provides the
  `class GeometricallyConnected (f : X ⟶ Y) : Prop` (line 39-41) and
  the FORWARD direction `GeometricallyConnected.connectedSpace`
  (`Geometrically/Connected.lean:89-92`):
  `[GeometricallyConnected f] [ConnectedSpace S] (hf : IsOpenMap f)
  ⟹ ConnectedSpace X`. The REVERSE direction "ConnectedSpace X +
  k-rational section ⟹ GeometricallyConnected" is **not** in
  Mathlib. The closest neighbouring lemmas
  (`GeometricallyConnected.iff_geometricallyConnected_fiber`
  line 108-110, base-change preservation lines 50-54, etc.) cover
  the predicate's stability/decomposition, not the substrate
  criterion.
- **Project's current path**: the project's
  `geometricallyConnected_of_connected_of_section` is the project's
  intended formulation — exactly the missing Mathlib lemma. The
  iter-194 body uses Mathlib's
  `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms`
  (`Geometrically/Basic.lean:136-144`) to reduce the predicate to a
  pullback-connectedness statement parametrised by `[Field K]
  [Algebra k K]`. The residual `sorry` then sits at the precise
  Stacks 037Q gap surface.
- **Gap**: divergent-by-necessity. The project's signature IS the
  correct Mathlib-shape lemma; what is missing is the body
  (substrate Stacks 037Q / 04KV / 04KU), not the API.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**.

### Decision: API for "k alg-closed in Γ(X,O_X) ⟺ X geometrically connected" (Stacks 037Q iff-direction)

- **Mathlib idiom**: NOT in Mathlib at SHA b80f227. Mathlib has the
  `algebraicClosure F E : IntermediateField F E` construction
  (`Mathlib/FieldTheory/AlgebraicClosure.lean:39-41`,
  `@[stacks 09GI]`), and the iff `IsAlgClosed.algebraicClosure_eq_bot_iff`
  for the special case `E = algebraic closure of F`, but NO bridge
  from "`algebraicClosure k (Γ(X, O_X)) = ⊥`" (or equivalently,
  "the inclusion `k ↪ Γ(X, O_X)` has only `k` as algebraic
  subextension") to `GeometricallyConnected (X ⟶ Spec k)`.
- **Project's current path**: the iter-194 prover left a comment
  pointing at this gap; no direct project-side path attempts it.
- **Gap**: NEEDS_MATHLIB_GAP_FILL on Mathlib's side; consumer-side
  the project doesn't try this route.

### Decision: API for "GeometricallyConnected iff connected on finite separable" (Stacks 04KV)

- **Mathlib idiom**: NOT in Mathlib at SHA b80f227. Mathlib has
  `GeometricallyConnected.iff_geometricallyConnected_fiber`
  (`Connected.lean:108-110`) — fiberwise characterization — but no
  reduction "geometrically connected ⟺ connected on every finite
  separable base change". The proof in the Stacks Project uses
  Galois-fixed-point arguments on `Spec(k' ⊗_k K)` for `K`
  algebraically closed; Mathlib has the field-theoretic Galois
  machinery (`IsGalois`, `normalClosure`, …) but it is **not**
  wired into the scheme side.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**.

### Decision: API for "k alg-closed in K, k'/k finite separable ⟹ K ⊗_k k' is a domain (hence field)"

- **Mathlib idiom (closest)**: `Algebra.TensorProduct.isField_of_isAlgebraic`
  (`Mathlib/FieldTheory/LinearDisjoint.lean:698-711`):
  `(K : Type*) [Field K] [Algebra F K] [IsDomain (E ⊗[F] K)]
  (halg : Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F K)
  : IsField (E ⊗[F] K)`.  This already does the IsDomain ⟹ IsField
  step assuming one side is algebraic, but it **takes `IsDomain
  (E ⊗ K)` as a hypothesis**. The substrate side
  `Subalgebra.LinearDisjoint.isDomain_of_injective`
  (`Mathlib/RingTheory/LinearDisjoint.lean`) needs `IsDomain` on
  BOTH `E` and `K`, plus a `LinearDisjoint` witness; the project
  hypothesis ("k alg-closed in K" + "k'/k finite separable") does
  NOT directly fit either input shape.
- **Project's current path**: the iter-194 comments name this gap.
  No attempted instantiation.
- **Gap**: NEEDS_MATHLIB_GAP_FILL — Mathlib has the IsDomain ⟹
  IsField half, but not the substrate "k alg-closed in K + k'/k
  finite separable ⟹ IsDomain (K ⊗ k')". This is the classical
  "purely transcendental / separable" linear-disjointness fact.

### Decision: API for "descent of clopen partitions along faithfully flat surjective" (Stacks 02LB)

- **Mathlib idiom (closest)**:
  `AlgebraicGeometry.Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact`
  (`Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`):
  `MorphismProperty.DescendsAlong (@Surjective) (@Surjective ⊓ @Flat
  ⊓ @QuasiCompact)`. This is `IsQuotientMap`-like descent at the
  morphism-property level (specifically, the `Surjective`
  property descends along fpqc covers). But the project doesn't
  need property descent — it needs *clopen* descent of an
  individual scheme along its FPQC base change. The Mathlib
  `Mathlib/Topology/Homeomorph/Lemmas.lean:572-580`
  `Topology.IsCoinducing.connectedComponentsHomeomorph` (a
  topological-side lemma) is a strong building block: a coinducing
  map with connected fibers induces a `π₀`-homeomorphism. Bridging
  it to the AlgGeom setting requires "Spec K → Spec k is
  coinducing on the underlying-space level after base change", plus
  "the fibres of `pullback f g → X` are connected" — both of which
  reduce to the Stacks 037Q gap.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL on the AlgGeom side; the
  topological building block already exists.

## Project-side substrate path (if the project ships its own helper)

Two route choices, both substantial:

### Route A — direct Stacks 04KU via descent of clopen partitions
- Project formalizes "for `X` connected and `s : Spec k ⟶ X` a
  section of `f : X ⟶ Spec k`, the base-changed `pullback f g` for
  `g : Spec K ⟶ Spec k` is connected".
- Prerequisites: image-of-clopen-along-projection-is-clopen for the
  projection `pullback f g → X`. This is FALSE in general (e.g.
  `Spec C → Spec R` doesn't send arbitrary clopen partitions to
  clopens of Spec R); the classical proof reduces to FINITE
  SEPARABLE extensions where Galois descent gives the property.
- Realistic build: **300-500 LOC**. The reduction to finite
  separable is Stacks 04KV (~150 LOC), Galois descent on Spec is
  ~200 LOC, the section-injection-into-clopen argument is ~50 LOC.
- Risk: substantial Mathlib substrate to assemble; high chance of
  needing further Mathlib-side gaps (e.g. functoriality of
  `Spec` on Galois extensions).

### Route B — via Stacks 037Q (alg-closed-in iff geometric-connectedness)
- Project formalizes:
  - (i) "k alg-closed in K + k'/k finite separable ⟹ IsDomain
    (K ⊗_k k')" (~80 LOC, uses
    `Subalgebra.LinearDisjoint` machinery in
    `Mathlib/RingTheory/LinearDisjoint.lean`).
  - (ii) "section `s : Spec k ⟶ X` ⟹ k alg-closed in Γ(X, O_X)"
    (~40 LOC, using the section's pullback on global sections as a
    k-algebra retraction).
  - (iii) Stacks 04KV "geom. connected iff connected on every
    finite separable" (~150 LOC).
  - (iv) Stacks 037Q "(k alg-closed in Γ(X,O_X) + connected) ⟹
    geom. connected" (~80 LOC, glues (i)+(iii)).
  - (v) Combine (ii)+(iv) into 04KU.
- Realistic build: **350-450 LOC** across 3-4 files. Still
  Mathlib-PR-sized.
- Advantage: each step is a discrete Mathlib-mergeable lemma, and
  (i)+(ii) by themselves close OTHER potential Mathlib gaps.

## Cross-domain analogues (read this section if the planner is
considering an *avoidance* strategy at the consumer sites)

### Analogue: topological group `connectedComponent_one_subgroup`
- Domain: topology / topological groups.
- Cite: `Mathlib/Topology/Algebra/Group/Basic.lean:718-745`
  (`mul_mem_connectedComponent_one`,
  `inv_mem_connectedComponent_one`, and the resulting subgroup
  structure on the connected component of `1`).
- **Same structural problem** in that setting: showing the
  connected component of identity in a group object is closed under
  the group operations. The technique is a one-coordinate-at-a-time
  continuity argument that SIDESTEPS forming `cc(1) × cc(1)`.
- **Mapping**: at the SET level (i.e. on `|G^0|` as a subset of
  `|G|`), the project's `isSubgroupHomomorphism` consumer COULD use
  this technique to derive `μ(|G^0| × |G^0|) ⊆ |G^0|` without
  forming `G^0 ×_k G^0`. **HOWEVER**, the scheme-level
  factorization `μ|_{G^0 ×_k G^0} : G^0 ×_k G^0 → G^0` requires the
  underlying-topological-space of `G^0 ×_k G^0` to be in the
  preimage of `G^0` under `μ`. Over non-algebraically-closed `k`,
  `|G^0 ×_k G^0|` is STRICTLY LARGER than `|G^0| × |G^0|` (it
  contains generic points of components not coming from products of
  points). So the set-level technique alone does not close the
  scheme-level statement.
- The **way to use this analogue**: combine it with a DENSITY
  argument — `|G^0| × |G^0|` (or the image of `Spec(\bar k)`-points,
  which IS in `|G^0|^2` after base change) is dense in
  `|G^0 ×_k G^0|`, and `μ⁻¹(G^0)` is an open-and-closed subset of
  `G^0 ×_k G^0` (since `G^0 ↪ G` is clopen and `μ` is continuous),
  so it contains the closure of `|G^0| × |G^0|`, which is the
  whole space. **But density of `\bar k`-points in a finite-type
  scheme over `k`** is also a Mathlib gap (cf. Stacks 020M /
  Hilbert's Nullstellensatz scheme-side) — albeit a smaller one
  than the Stacks 04KU substrate.
- **Porting cost**: medium-high if pursued. ~120-200 LOC for the
  density bridge.
- **Verdict**: PARTIAL_ANALOGUE — technique informs a possible
  avoidance route but does not replace the substrate.

### Analogue: `Topology.IsCoinducing.connectedComponentsHomeomorph`
- Domain: pure topology.
- Cite: `Mathlib/Topology/Homeomorph/Lemmas.lean:572-580`.
- **Same structural problem** in pure topology: a coinducing map
  with connected fibres induces a `π₀`-equivalence. This is the
  topological core of Stacks 02LB-style descent.
- **Mapping**: combine with `Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`'s
  surjective-fpqc descent: Spec K → Spec k is an fpqc cover (when
  K/k is a field extension), so the projection `pullback f g → X`
  IS coinducing as a topological map. The MISSING premise is "the
  fibres are connected" — for fibre over `x ∈ X`, the fibre is
  `Spec(K ⊗_k κ(x))`, generally not connected over non-Galois
  extensions.
- **Verdict**: PARTIAL_ANALOGUE — building block for the substrate,
  but does not close it directly.

### Analogue: Boolean-algebra-of-clopens / `IsConnected` ⟺ idempotent-trivial
- Domain: order theory / Boolean algebra / commutative algebra.
- Cite: `Mathlib/Topology/Connected/Basic.lean` (the standard
  `connectedSpace_iff_subsingleton_clopen`-style lemmas) +
  `Mathlib/Algebra/Ring/Idempotents.lean` for the algebra ↔ topology
  correspondence under Spec.
- **Same structural problem**: `Spec R` is connected iff the only
  idempotents of `R` are `0, 1`. Base change `Spec(R ⊗_k K)` has
  idempotents `idemp(R) ⊗ idemp(K)` plus Galois-twists. With `s`
  providing a `k`-retraction `R → k`, the "lift" of an idempotent
  in `R ⊗_k K` to `k ⊗_k K = K` lands at `0` or `1`. This is the
  Stacks 037Q argument re-expressed as "no non-trivial idempotent
  survives the retraction".
- **Mapping**: this is essentially Route B (i)+(ii)+(iv) above,
  but stated in pure algebra. Mathlib has the idempotent / clopen
  correspondence but no "section preserves idempotent triviality
  under base change" packaging.
- **Verdict**: PARTIAL_ANALOGUE — reframes the substrate but does
  not pre-build it.

## Recommendation

This is a **NEEDS_MATHLIB_GAP_FILL** situation across four
discrete Mathlib gaps (Stacks 037Q iff-direction, Stacks 04KU,
Stacks 04KV, field-tensor-product corollary). Three options for
the planner:

1. **(Recommended) Park Lane A.3.i, file Mathlib PR for Stacks
   04KU upstream.** The four gap pieces are independently
   Mathlib-mergeable; landing Stacks 04KU upstream (~350 LOC, Route
   B above) closes the substrate in one place. Lane A.3.i
   reactivates as a 0-10 LOC re-export shim once the upstream
   lemma lands. Recommended because: (a) Mathlib's
   `GeometricallyConnected` API is already in shape to accept the
   lemma; (b) the lemma has dozens of downstream consumers across
   AlgGeom and is genuinely owed to Mathlib; (c) the project's
   four-iter CHURNING is a clear signal that project-side
   construction is too expensive.

2. **Project-side Route B build (350-450 LOC across 3-4 files,
   3-5 iters).** Acceptable if the project is willing to absorb
   the Mathlib gap. The substrate lemmas should be written in
   `AlgebraicJacobian/Picard/IdentityComponent_StacksSubstrate.lean`
   (new file, separate from the consumer) so they can be lifted to
   a Mathlib PR cleanly after landing project-side. Estimated
   timeline: iter-196 builds (i)+(ii) of Route B (field-side ~80
   LOC + section-retract ~40 LOC); iter-197 builds (iii) of
   Route B (Stacks 04KV ~150 LOC); iter-198 glues (iv)+(v) into
   `geometricallyConnected_of_connected_of_section` (~80 LOC).

3. **USER-escalate.** Recommended only if the user has a strong
   preference for one of the routes or wants to know about the
   Mathlib PR option. Otherwise option 1 (park + upstream) is the
   clearer default given the four-iter CHURNING and the substantial
   substrate gap.

Whichever option the planner chooses, do NOT continue iter-196
prover work inside `IdentityComponent.lean` on the current
substrate — the iter-189..iter-194 CHURNING signal is exactly that
the sorry-helper is not closable inline because the substrate is
upstream. The iter-195 prover should be redirected to a different
lane (or to a substrate-construction lane, per option 2).
