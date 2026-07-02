# Analogy: Mathlib LOC cost of M3 — building a positive-genus `JacobianWitness`

## Slug
m3-route-audit

## Iteration
123

## Question

For an arbitrary smooth proper geometrically irreducible curve `C` over a
field `k` with `genus C ≥ 1`, what is the cumulative LOC of upstream
Mathlib work the project would need to contribute (or backfill in-tree)
in order to discharge the existential `positiveGenusWitness` —
equivalently, the higher-genus case of `nonempty_jacobianWitness`
(`AlgebraicJacobian/Jacobian.lean:176`)?

The question is asked over two prescribed construction routes (FGA via
Picard, and symmetric-power via Stein factorisation), with a tiebreaker
on cross-utility for general Mathlib AG infrastructure, and a hard
escalation rule at the 5000-LOC mark.

## Project artifact(s)
- `AlgebraicJacobian/Jacobian.lean:143-179` — `JacobianWitness` bundled
  structure and `nonempty_jacobianWitness` sorry, the M3 target.
- `AlgebraicJacobian/Jacobian.lean:49-114` — `IsAlbanese` predicate and
  `IsAlbanese.unique` (positive-genus need only the existence of one
  Albanese witness).
- `AlgebraicJacobian/Genus.lean:65-68` — the project's working definition
  `genus C := Module.finrank k (H¹(C, O_C))`, which constrains Route B's
  RR formulation.

## Mathlib snapshot used

Mathlib package shipped with this project's lake manifest (b80f227
neighbourhood). Concretely:

- `AlgebraicGeometry/` directory contents: `AffineScheme`, `AffineSpace`,
  `EllipticCurve/{Affine,DivisionPolynomial,Jacobian,Projective}`,
  `Geometrically/{Connected,Integral,Irreducible}`, `Group/{Abelian,Smooth}`,
  `IdealSheaf`, `Modules/{Presheaf,Sheaf,Tilde}`,
  `Morphisms/{Affine,…,Proper,QuasiCompact,…,Smooth,SmoothFiber,…}`,
  `ProjectiveSpectrum`, `Sites/{BigZariski,…,Representability,Etale,Fpqc}`,
  `ZariskisMainTheorem`, `ValuativeCriterion`.
- Searches verified the **absence** of: `PicardScheme`, `PicardFunctor`,
  `HilbertScheme`, `HilbertFunctor`, `QuotScheme`, `QuotFunctor`,
  `SymmetricPower` on schemes, `Scheme.action` / scheme-level group
  action, `Scheme` quotient by a finite group, `RiemannRoch`, Cartier or
  Weil divisor on a general scheme (`EllipticCurve.Jacobian` is the
  Weierstrass model, not a general divisor theory), `BrillNoether`,
  `SteinFactorization`, `RelativeSpec` / `Spec_Y` of a quasi-coherent
  algebra, `R^if_*` higher direct image, `Functor.Monoidal` on
  `SheafOfModules.pullback`, and `Module.Invertible` lifted to sheaves.

What **does** exist (relevant partials):

- `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`
  (`Mathlib.AlgebraicGeometry.Sites.Representability:201-203`): the general
  "locally representable Zariski sheaf is representable" tool (Stacks 01JJ).
  Both routes consume this once they have produced their local data.
- `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`
  (`Mathlib.AlgebraicGeometry.Group.Abelian:128-144`, tag 0BFD):
  proper geometrically integral group scheme over a field is commutative.
- `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed`
  (`Mathlib.AlgebraicGeometry.Group.Smooth:38`): reduced locally-of-finite-type
  group scheme over algebraically closed `k` is smooth — usable to upgrade
  smoothness of the candidate Jacobian after geometric base change.
- `AlgebraicGeometry.finite_appTop_of_universallyClosed`
  (`Mathlib.AlgebraicGeometry.Morphisms.Proper:154`): the **0-th case** of
  Stein factorisation — `Γ(X, ⊤)` is finite over `K` for integral
  universally closed `X / Spec K`.
- `AlgebraicGeometry.Flat`
  (`Mathlib.AlgebraicGeometry.Morphisms.Flat`) — flat morphisms exist as a
  class; sheaf-of-modules flatness does not.
- `SheafOfModules.Presentation` and `Presentation.IsFinite`
  (`Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent:44-57`):
  finite presentations of sheaves of modules over a general ringed site;
  the abstract notion is in place but it is **not lifted to a typeclass
  `QuasiCoherent` / `IsCoherent` on `SheafOfModules`** in the form Stacks
  03DL or 01BD specify, nor is there a `Scheme.QuasiCoherent` or
  `Scheme.IsCoherent` namespace.
- `Subgroup.connectedComponentOfOne`
  (`Mathlib.Topology.Algebra.Group.Basic:740`): identity-component as a
  `Subgroup` for **topological** groups; **no** scheme-level analog
  (i.e. no reduced closed subgroup-scheme structure on `G^0 ⊆ G` for a
  locally-of-finite-type `k`-group scheme).
- `CommRing.Pic` (`Mathlib.RingTheory.PicardGroup:407-408`): ring-level
  Picard *group* via `Shrink (Skeleton (SemimoduleCat R))ˣ`. The scheme
  analog is the project's `AlgebraicJacobian/Picard/*` (post-iter-109),
  **not** Mathlib's. There is no Picard *scheme* in either place.

## Decisions identified

Per the directive the "decision" surface is "which of the two strategy
routes does the project pick?", decomposed into a per-piece LOC count
plus tiebreakers. The structure below follows that.

### Route A — Picard scheme via FGA

#### Piece A1: Hilbert scheme representability for projective schemes

- **Mathlib idiom**: `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`
  (Stacks 01JJ) is the general gluing tool. The **specific** Hilbert /
  Quot representability theorems (Stacks 0DPA, 0DPB) are absent. There
  are no `HilbertFunctor` / `HilbertScheme` / `QuotFunctor` / `QuotScheme`
  declarations anywhere in `.lake/packages/mathlib/Mathlib/`.
- **Partial infrastructure present**:
  - Locally-representable-implies-representable
    (`...Sites.Representability:201`).
  - The Zariski big site and sheaf condition (`...Sites.BigZariski`).
  - Properness, finite type, finite presentation, flat morphisms as
    `MorphismProperty` (`...Morphisms.{Proper,FinitePresentation,Flat,…}`).
  - `ProjectiveSpectrum` of a graded ring (`...ProjectiveSpectrum/`).
  - Abstract finite-presentation of `SheafOfModules`
    (`...ModuleCat.Sheaf.Quasicoherent`).
- **The gap proper**:
  1. **Quasi-coherent sheaves on a scheme**: define the typeclass
     `Scheme.QuasiCoherent` for a `SheafOfModules X.ringSheaf` (matching
     Stacks 01BD) and supply the affine/Tilde calibration; build the
     `qcoh(X)` abelian category. ~400-500 LOC.
  2. **Coherent sheaves on Noetherian schemes** + finite-presentation
     equivalence. ~300-400 LOC.
  3. **Flatness module-side**: `Module.Flat` lifted to `SheafOfModules`,
     and the morphism flatness `RingHom.Flat` lifted to flatness of
     pullback functors. ~200-300 LOC.
  4. **Hilbert functor**: the Yoneda-style "flat closed subschemes with
     fixed Hilbert polynomial" presheaf; sheaf condition for the fpqc
     topology (or, more cheaply, just the Zariski sheaf condition).
     ~400-600 LOC.
  5. **Grothendieck flattening stratification** (Stacks 052F, 0BFR — the
     hard step): every coherent sheaf becomes flat after passing to a
     finite locally-closed stratification of the base. This is the
     load-bearing technical theorem for Hilbert/Quot representability.
     ~1500-2200 LOC. (Stacks devotes a substantial chunk of "More on
     Flatness" to this; Mathlib has nothing comparable.)
  6. **Hilbert scheme representability for `ℙ^N`** via Grothendieck's
     construction (use flattening to produce relatively-flat subschemes,
     then glue via `LocalRepresentability`). ~600-900 LOC.

  **Subtotal A1**: ~3400-4900 LOC.

- **Cross-utility**: **HIGH**. Quasi-coherent + coherent + flattening +
  Hilbert is the foundation for every moduli-theoretic statement in
  algebraic geometry. The first three sub-pieces (quasi-coherent,
  coherent, sheaf-flatness) are unconditionally desirable in Mathlib and
  could plausibly be PR'd independent of the Jacobian project.

#### Piece A2: Quot scheme representability

- **Mathlib idiom**: same `LocalRepresentability` framework. `Quot`
  generalises Hilbert by replacing "closed subscheme" with "quotient
  sheaf of a fixed coherent sheaf". If A1's Hilbert construction is
  available, the additional work is:
  1. **Quot functor** for a fixed coherent sheaf `F` on `ℙ^N`. ~400-600 LOC.
  2. **Sheaf condition + flattening reuse**: leverage A1.5; the new
     content is bookkeeping around `F` instead of `O`. ~300-500 LOC.
  3. **Representability via local data + Hilbert**: ~400-600 LOC.

  **Subtotal A2 (post-A1)**: ~1100-1700 LOC.

  If Hilbert were *not* built first, Quot alone would still need ~80% of
  A1's work plus its own ~1100, i.e. ~4000+. Treat Hilbert as the
  natural prerequisite.

- **Cross-utility**: **HIGH**. Quot is the universal moduli object
  underlying coherent-sheaf moduli, Hilbert, and Picard. Same Mathlib-PR
  attractiveness as A1.

#### Piece A3: Identity-component `G^0 ⊆ G` as a closed subgroup scheme

- **Mathlib idiom**: Mathlib has `Subgroup.connectedComponentOfOne`
  (`Mathlib.Topology.Algebra.Group.Basic:740`) for **topological** groups
  as a `Subgroup` on the underlying point set. The scheme-theoretic
  analog — `G^0 ⊆ G` as a *reduced closed subscheme* carrying its own
  group-scheme structure — is **absent**. The Picard *scheme* of `C` is
  in general not connected; the Jacobian is the connected component of
  the identity, so this piece is load-bearing for Route A even after
  representability of the full Picard scheme is settled.
- **Partial infrastructure present**:
  - `GrpObj` for objects of `Over (Spec (.of k))`
    (`Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_`).
  - Group-scheme commutativity under proper geometrically integral
    (`...Group.Abelian:128`).
  - Smoothness from `IsReduced + LocallyOfFinitePresentation`
    (`...Group.Smooth:38`).
  - Topological connected components on the underlying space of a
    scheme (via `TopCat`).
  - Reduced closed subscheme `(IdealSheafData/`) construction with
    associated `subschemeι`.
- **The gap proper**:
  1. **Connected components of `G.left` are open** for `G` locally of
     finite type over a field (uses `JacobsonSpace`, already in
     Mathlib). ~150-200 LOC.
  2. **Distinguished open + closed component containing the identity**
     as a reduced closed subscheme of `G`, packaged as a
     `Scheme.Opens`-and-reduced-closed structure. ~200-300 LOC.
  3. **Group-scheme structure** on `G^0`: `μ`, `inv`, `η` restrict
     because they're continuous and send connected components to
     connected components. ~300-400 LOC.
  4. **Geometric irreducibility / smoothness inheritance** (needs the
     dimension-of-component theorem and base-change closure).
     ~200-300 LOC.

  **Subtotal A3**: ~850-1200 LOC.

- **Cross-utility**: **MEDIUM-HIGH**. Identity-component-as-closed-subgroup
  is the entry point for the structure theory of algebraic groups
  (Chevalley decomposition, abelian-variety quotients). Independent of
  the Jacobian project, this is a clean Mathlib PR target.

**Route A cumulative LOC**: A1 + A2 + A3 ≈
**~5350-7800 LOC** (using A1 = 3400-4900, A2 = 1100-1700, A3 = 850-1200).

A point estimate: **~6500 LOC** is a reasonable midpoint.

---

### Route B — Symmetric powers + Stein factorisation

#### Piece B1: Symmetric powers `Sym^n X` with smoothness

- **Mathlib idiom**: there is **no** `Sym^n` for schemes anywhere in
  `Mathlib.AlgebraicGeometry.*`. `SymmetricPower` exists in
  `LinearAlgebra.TensorPower.Symmetric` (the linear-algebraic
  construction, totally unrelated). Mathlib has no `Scheme.action`
  typeclass, no group-action-on-scheme infrastructure, and no scheme
  quotient by a finite group.
- **Partial infrastructure present**:
  - Finite products of schemes (via `CartesianMonoidalCategory` /
    pullbacks).
  - `Finset.symm` / `Equiv.Perm` and `SymmetricGroup` at the type level.
  - Quotients by finite group actions at the *ring* level
    (invariant subrings); the affine case `Spec R^G` is reachable from
    existing material.
- **The gap proper**:
  1. **Action of a finite group on a scheme** as a structured typeclass
     (`Scheme.MulAction G X` style). ~250-400 LOC.
  2. **Affine quotient `Spec (R^G)`** + the universal property
     (Stacks 03AP, 04AD). ~500-700 LOC.
  3. **Global quotient `X / G`** for a finite group acting on a scheme,
     glued from affine charts (requires the action to permute a covering
     family; for the `S_n` action on `X^n` this needs the symmetric
     stratification of `X^n`). ~800-1200 LOC.
  4. **Smoothness of `Sym^n C` for `C` a smooth curve**
     (Fogarty / Hartshorne-Mumford): the action is **not free** (the
     fixed locus is the big diagonal), so the quotient is not étale on
     `X^n`; nonetheless `Sym^n C` is smooth as a special property of
     1-dimensional `X`. This proof is delicate (typically via local
     Lüroth-style coordinates / SGA-1-style descent). ~600-1200 LOC.
  5. **Abel-Jacobi map `Sym^g(C) ⟶ Pic^g(C)`** in the symmetric-power
     model (depends on B2 + B3 for the target). ~200-300 LOC.

  **Subtotal B1**: ~2350-3800 LOC.

- **Cross-utility**: **LOW-MEDIUM**. Sym-powers and finite-group-quotients
  are useful (Chow groups, intersection theory, equivariant geometry),
  but the **specific result needed for Jacobians** — smoothness of
  `Sym^n C` for `n = g` and `C` a curve — is highly curve-specialised.
  The general finite-group-quotient infrastructure (B1.1–B1.3) has
  meaningful Mathlib utility on its own; B1.4 is narrow.

#### Piece B2: Stein factorisation

- **Mathlib idiom**: not present. The 0-dimensional **global** case is in
  `AlgebraicGeometry.finite_appTop_of_universallyClosed`
  (`...Morphisms.Proper:154`): for integral `X / Spec K` universally
  closed and locally of finite type, `Γ(X, ⊤)` is finite over `K`. This
  gives the constant-Hom case but not the relative version.
- **Partial infrastructure present**:
  - `Scheme.Modules.pushforward` (presheaf-of-modules pushforward,
    `...Modules.Sheaf:167`); but no coherence-preservation theorem.
  - `Scheme.Hom.appTop` and proper-morphism `Γ`-finiteness for the
    global case.
  - Properness, separated, finite-type, finite morphisms as
    `MorphismProperty`.
  - `Spec` as a (contravariant) functor `CommRingCat ⥤ Scheme`; but
    **no `RelativeSpec` / `Spec_Y` of a quasi-coherent algebra** —
    the construction that produces a scheme `Spec_Y A` from a
    quasi-coherent `O_Y`-algebra `A` is absent.
- **The gap proper**:
  1. **Coherent direct image** (Stacks 02O5 / 0205): if `f : X → Y` is
     proper between Noetherian schemes and `F` is coherent on `X`, then
     `R^i f_* F` is coherent on `Y`. This depends on Quasi-coherent +
     Coherent + Čech infrastructure. The 0-th case (`f_*`) suffices for
     Stein, and is itself sizeable. ~1200-1800 LOC just for `i = 0`.
  2. **Relative Spec functor**: `Spec_Y : QcohAlg(Y)^op ⥤ Sch/Y`,
     adjunction with global-sections-as-algebra. This is **the missing
     basic constructor** for Stein and several other moduli operations.
     ~700-1100 LOC.
  3. **Stein factorisation proper**: package the above as
     `X → Spec_Y(f_*O_X) → Y` with the connected-fibres / finite
     factorisation property (Stacks 03GX). ~300-500 LOC.

  **Subtotal B2**: ~2200-3400 LOC.

- **Cross-utility**: **HIGH**. Coherent direct image (B2.1) and relative
  Spec (B2.2) are foundational and would be Mathlib-welcome PRs in
  their own right (relative Spec is also needed by Route A: every
  affine map factors through `Spec_Y` of its image algebra). Stein
  factorisation per se (B2.3) is narrower but cheap once B2.1–B2.2 land.

#### Piece B3: Riemann-Roch + Brill-Noether (curve side)

- **Mathlib idiom**: not present in any usable form. The
  `EllipticCurve/` subtree is the Weierstrass-equation model and is
  **not** a general divisor / line-bundle / RR theory; it does not
  generalise to higher genus. There is no Cartier or Weil divisor on a
  general scheme, no `Pic^d`, no degree map, no Riemann-Roch, and no
  Brill-Noether anywhere in Mathlib.
- **Partial infrastructure present**:
  - The project's `Scheme.HModule k _ 1`
    (`AlgebraicJacobian/Cohomology/StructureSheafModuleK.lean`)
    computes `H¹(C, O_C)` as a `ModuleCat k`. This is the definition of
    `genus C` and is the **anchor** for any RR statement the project
    can use. Any Mathlib-side RR formulation must be reconciled with
    this definition.
  - `Module.finrank`, `FiniteDimensional` in Mathlib.
- **The gap proper**:
  1. **Cartier divisors on a scheme**: invertible-section / order-of-
     vanishing infrastructure, with the smooth-curve specialisation
     where Cartier and Weil agree. ~400-600 LOC.
  2. **Weil divisors on a smooth curve** + equivalence and the
     class-group identification with `Pic(C)`. ~400-600 LOC.
  3. **Degree of a divisor** on a smooth proper curve over `k`
     (via the residue-field-degree weighted sum). ~250-350 LOC.
  4. **Finiteness of `dim_k H^0(C, L)` and `dim_k H^1(C, L)`** for every
     line bundle `L` (needs Čech cohomology for coherent sheaves on a
     proper curve — this leans on B2.1's coherent direct image
     specialised to `Y = Spec k`). ~400-700 LOC.
  5. **Riemann-Roch**:
     `h^0(D) - h^1(D) = deg D + 1 - g` (Stacks 0BSC).
     Either via Serre duality (more infrastructure, especially the
     dualising sheaf) or via the additivity / induction-on-points
     proof. ~500-800 LOC; +400-700 LOC if a working Serre-duality
     formalism (cf. `analogies/serre-duality.md`) is required as an
     intermediate.
  6. **Brill-Noether-style surjectivity / smoothness**: the AJ map
     `Sym^g(C) → Pic^g(C)` is birational and surjective, so its image
     (after Stein-factorisation B2.3) is a proper smooth variety
     `Pic^g(C)`. ~400-700 LOC.
  7. **Translation `Pic^g(C) → Pic^0(C) = Jac(C)` via a fixed point
     and abelian-variety structure** (group law from the symmetric-
     power-of-points addition). ~300-500 LOC.

  **Subtotal B3**: ~2650-4250 LOC (low end if Serre duality is finessed,
  high end if a full dualising-sheaf is built; the project's existing
  `analogies/serre-duality.md` argues that the cheap path still costs
  several hundred LOC).

- **Cross-utility**: **MEDIUM**. Cartier / Weil / Pic for curves is
  broadly useful. RR itself is curve-specialised but is one of the most
  desirable Mathlib targets in its own right. The downstream
  Brill-Noether content is narrow.

**Route B cumulative LOC**: B1 + B2 + B3 ≈
**~7200-11450 LOC** (B1 = 2350-3800, B2 = 2200-3400, B3 = 2650-4250).

A point estimate: **~9000 LOC** is a reasonable midpoint.

---

### Cross-route shared dependencies

A non-trivial fraction of Route A and Route B overlap:
- Quasi-coherent + Coherent sheaves on schemes (A1.1, A1.2; B2.1, B3.4):
  ~700-1000 LOC, shared.
- Coherent direct image (A1.4–6 reuses A1's flattening, B2.1 reuses
  proper-pushforward): partially shared but the *theorems* differ.
- Relative Spec (B2.2) is independently useful and would also support
  Route A's affine-map handling.

So a project that pursues *both* routes simultaneously saves ~1000-1500
LOC vs. summing the route estimates; this does not change the
> 5000-LOC verdict for either route.

---

### Decision: route choice and escalation

- **Mathlib idiom**: neither route is "what Mathlib does" — Mathlib does
  not yet construct any Picard / Jacobian / Albanese object for a
  general curve. The closest existing Mathlib construction is the
  Weierstrass-equation `EllipticCurve` for genus 1, which is not the
  Jacobian and does not generalise.
- **Project's current path**: defer the existence
  (`nonempty_jacobianWitness`) as a single named sorry, treating both
  routes as out-of-scope for the autonomous loop and routing the work
  to an external Mathlib PR.
- **Gap**: NEEDS_MATHLIB_GAP_FILL on either route, with the gap
  unambiguously larger than the strategy's hard escalation threshold.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**, with escalation to the user
  for an external-PR routing decision (per STRATEGY.md's
  > 5000-LOC fallback rule).

## Recommendation

**Both routes exceed 5000 LOC of upstream Mathlib work** — Route A
midpoint ≈ 6500 LOC, Route B midpoint ≈ 9000 LOC. The project's
strategy mandates escalation in this case.

If the user wants a route ranking despite both being over-budget,
**Route A is preferred** for two reasons that are independent of the
LOC count:

1. **Cross-utility is higher**: Route A's three gating pieces
   (quasi-coherent + coherent, Hilbert / Quot representability,
   identity-component subgroup scheme) are all in the top tier of
   "Mathlib AG infrastructure that's been wanted for years". Route B's
   `Sym^n C` smoothness (B1.4), the RR formula (B3.5), and the
   Brill-Noether step (B3.6) are more curve-specialised, and `Sym^n`
   quotient infrastructure is narrower than Hilbert/Quot.
2. **Route A's gating pieces compose with the project's existing
   `AlgebraicJacobian/Picard/*` arc**: the project already ships a
   ring-level Picard group (`LineBundle X := (Skeleton X.Modules)ˣ` via
   `CommRing.Pic` analogy; see `analogies/c1-route.md`). Route A's
   Picard *scheme* extends this naturally; Route B sidesteps the
   project's Picard arc entirely and adds a parallel Sym-power /
   AJ-map infrastructure.

**Smallest upstream-PR-extractable pieces** (each well under 1500 LOC,
each self-contained as a Mathlib PR independent of the rest of the
Jacobian project):

- **Relative Spec functor** (Route B piece B2.2, ~700-1100 LOC):
  `Spec_Y : QcohAlg(Y)^op ⥤ Sch/Y` with the standard adjunction.
  Useful for both routes (it's a strict prerequisite for Stein, and a
  natural intermediate for affine-map factorisation in any FGA work);
  Mathlib reviewers would welcome this as standalone. **Highest
  recommend.**
- **Identity-component of a `k`-group scheme as a closed subgroup
  scheme** (Route A piece A3, ~850-1200 LOC): generalises
  `Subgroup.connectedComponentOfOne` to schemes; needed for both routes
  (B's Pic^g → Jac translation also needs it). Standalone PR.
- **Quasi-coherent + Coherent typeclass for `Scheme.SheafOfModules`**
  (Route A piece A1.1–A1.2, ~700-900 LOC): definitional layer with
  affine/Tilde calibration; opens the door to *both* coherent direct
  image (B2.1) and Hilbert representability (A1.6).

**Alternative routes** noted but not pursued:

- *Route C — Chevalley-decomposition assist*: define the Jacobian as
  the abelian-variety quotient of the connected component of an
  algebraic-group envelope (the symmetric-power image quotiented by
  its linear part). Requires Chevalley's structure theorem for
  connected algebraic groups, which itself bottoms out in identity-
  component (A3) + linear-algebraic-group infrastructure. **Not
  materially cheaper.**
- *Route D — Étale-local linearisation*: construct the Albanese via
  the étale fundamental group / period map. Even larger; not
  algebraically self-contained in Mathlib's current state.
- *Route E — defer indefinitely*: keep `nonempty_jacobianWitness` as
  the single named gap and ship the higher-genus Jacobian as a
  conditional theorem in `archon-protected.yaml`. This is the
  **status quo** and is honest accounting. It is **not** a
  formalisation route, it's the absence of one.

**Therefore the iter-124 plan agent should**:

1. Surface this audit to the user as an external-PR routing
   decision.
2. Default to **Route A** in any user-facing summary on cross-utility
   grounds, **but flag explicitly** that Route A is
   ~6500 LOC and Route B is ~9000 LOC, both well above the 5000-LOC
   escalation threshold.
3. Optionally propose a **partial extraction PR** to Mathlib —
   "Relative Spec functor" is the cleanest standalone item and would
   accelerate either route.
4. If the user authorises continued in-project work, the
   ordering A1.1 → A1.2 → B2.2 (Relative Spec) → A3 makes both
   routes incrementally easier without committing to either, since
   each of these four pieces is needed by both routes.
