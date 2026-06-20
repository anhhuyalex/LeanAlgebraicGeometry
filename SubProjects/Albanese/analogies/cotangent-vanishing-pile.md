# Analogy: Mathlib coverage of the shared cotangent-vanishing pile (M2.a C.2.d + M2.d-alt)

## Slug
cotangent-vanishing-pile-iter126

## Iteration
126

## Question

What is current Mathlib's coverage of the **shared cotangent-vanishing
pile** that gates both M2.a body closure and the M2.d-alt genus-0
identification alternative? For each of the four pieces:

(i) Abelian-variety cotangent triviality `Ω_{A/k}` trivial of rank `dim A`;
(ii) scheme-level `df = 0 ⇒ f` factors through `Spec k`;
(iii) characteristic-`p` handling (Frobenius iteration / Mumford / lifting to char 0);
(iv) Serre duality on a smooth proper curve (M2.d-alt-only).

What does Mathlib already have, what's missing, what's the per-piece
project-internal LOC build estimate, what's the recommended build order,
and (for piece iii) which of the three options is most cost-effective?

## Project artifact(s)

- `blueprint/src/chapters/RigidityKbar.tex:57-78` — § "The shared
  cotangent-vanishing Mathlib pile" decomposes the pile into pieces
  (i)-(iv) with directive's per-piece estimate 200-400 LOC each.
- `blueprint/src/chapters/Jacobian.tex:332-348` — § C.2.d "Key classical
  input" with the two-proof options (Pic⁰ vs cotangent-bundle route).
- `AlgebraicJacobian/RigidityKbar.lean:75-87` — iter-126 scaffolded
  `rigidity_over_kbar` named declaration with `sorry` body.
- `AlgebraicJacobian/Rigidity.lean:45-67` (hypothesis history) — notes the
  Frobenius pitfall in char `p` that motivated scheme-level (not
  topological) equality in `Scheme.Over.ext_of_eqOnOpen`.
- `analogies/serre-duality.md` (iter-110) — pre-existing analogy on Serre
  duality. **Verdict still binds**: NEEDS_MATHLIB_GAP_FILL, 3000-8000 LOC
  for honest closure. **Used here verbatim for piece (iv).**
- `analogies/cotangent-presheaf-design.md` (iter-120) — pre-existing
  analogy noting Mathlib b80f227 has **no scheme-level cotangent
  presheaf or sheaf**; project's `relativeDifferentialsPresheaf` is the
  only off-the-shelf path. **Materially affects piece (i) estimate.**

## Decisions identified

The directive asks one design question but compresses **five** orthogonal
decisions: four piece-by-piece decisions on Mathlib's coverage (i)-(iv)
plus a fifth meta-decision on build order and (for piece iii) the
choice among the three characteristic-`p` options.

### Decision (i): Abelian-variety cotangent triviality

- **Mathlib idiom (closest)**: Mathlib `b80f227` ships
  `Mathlib/AlgebraicGeometry/Group/{Abelian,Smooth}.lean` (both 2026,
  Yang+Merten). The two declarations:
  - `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`
    (`Group/Abelian.lean:128-145`, with `@[stacks 0BFD]`) — a proper
    geometrically integral group scheme over a field is commutative.
  - `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed`
    (`Group/Smooth.lean:38-60`) — a reduced locally-of-finite-type group
    scheme over an algebraically closed field is smooth.

  Both use `[GrpObj G]` over `Over (Spec (.of K))` and rely on the
  `Stacks 0BFD` machinery. **Neither produces a cotangent statement.**
  - **No `AbelianVariety.cotangent_trivial` / `GroupScheme.Omega_trivial`.**
  - **No left-invariant differential infrastructure for `GrpObj`.**
  - **No `LieAlgebra`-of-a-group-scheme construction**: searches for
    `Lie[Aa]lgebra.*[Gg]roupObj`, `[Tt]angentSpace.*[Gg]roup`,
    `[Ii]dentity.*[Tt]angent` all return zero hits.
  - **No `AbelianVariety` type at all**: search for
    `AbelianVariety|abelian_variety` returns no files.

  Even the cotangent **sheaf** on a general scheme is missing in Mathlib
  (per `analogies/cotangent-presheaf-design.md` decision 1): the closest
  is `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`
  (abstract category-theoretic, no scheme-side bridge) and the project's
  own `relativeDifferentialsPresheaf` (presheaf, not sheaf; with the
  bridge cost documented in `cotangent-presheaf-design.md`).

- **Project's proposed path** (directive): build
  `AlgebraicGeometry.AbelianVariety.cotangent_trivial` or
  `AlgebraicGeometry.GroupScheme.Omega_trivial` at 200-400 LOC.

- **Gap**: NEEDS_MATHLIB_GAP_FILL with **directive estimate materially
  too low**. The realistic chain of work is:
  1. Either consume the project's presheaf-level `relativeDifferentialsPresheaf`
     (and accept the presheaf-vs-sheaf bridge cost noted in
     `cotangent-presheaf-design.md`) or build the scheme-level cotangent
     **sheaf** first (a Mathlib gap in its own right that the project
     has already deferred; cf. `Differentials.lean:877` Serre-duality
     deferral).
  2. Define the Lie algebra of a `GrpObj` as the cotangent at the
     identity (i.e. `(η[G])^* Ω_{G/k}` finitely generated free of rank
     `dim G`). Mathlib has no `Lie[Aa]lgebra.GrpObj` precedent.
  3. Construct left-invariant translations via `GrpObj.mulRight` (which
     **does** exist; `Group/Smooth.lean:50-51` uses it) and show they
     globalise the Lie-algebra-at-identity to a global frame of `Ω_{G/k}`.
  4. Conclude `Ω_{G/k}` is free of rank `dim G` (locally free + trivial
     monodromy/frame = free).

  Pieces 2-4 are themselves multi-hundred-LOC each at the
  presheaf-of-modules level the project consumes; piece 1 is the
  multi-thousand-LOC sheaf-level cotangent gap.

- **Cost of divergence**: under directive's 200-400 LOC estimate, the
  body cannot honestly close — the prerequisites (cotangent sheaf, Lie
  algebra, mulRight-globalisation) alone exceed that budget. Realistic
  estimate: **800-1500 LOC** for piece (i) alone, conditional on
  consuming the project's existing presheaf-level
  `relativeDifferentialsPresheaf` (which the project has already
  committed to) rather than building the sheaf-level cotangent first.
  **+800-2000 LOC** if the project additionally needs the scheme-level
  cotangent **sheaf** (e.g. if the C.2.d statement requires
  `H⁰(C, f^* Ω_{A/k})` on the sheaf level rather than the presheaf
  level; the C.2.d argument as currently sketched in `Jacobian.tex:342-346`
  uses `H⁰` of the relative cotangent, which is presheaf-or-sheaf-agnostic
  on affine opens but sheaf-cohomology-sensitive on the global section).

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (no idiom to align with);
  **directive's 200-400 LOC estimate is materially low**; realistic
  estimate **800-1500 LOC** assuming the project's presheaf-level
  cotangent is the input. Recommendation: build via Lie-algebra-of-GrpObj
  + mulRight-globalisation, working at the presheaf level the project
  already uses, and **explicitly avoid** committing to the sheaf-level
  global-section statement until pieces (i)+(ii)+(iii) are integrated
  and the actual C.2.d residual is known.

### Decision (ii): scheme-level `df = 0 ⇒ f` factors through `Spec k`

- **Mathlib idiom (partial)**: Mathlib has a **ring-level typeclass-form
  partial idiom** at `Mathlib/RingTheory/Derivation/DifferentialRing.lean:62-70`:
  ```lean
  class Differential.ContainConstants (A B : Type*) [CommRing A]
      [CommRing B] [Algebra A B] [Differential B] : Prop where
    protected mem_range_of_deriv_eq_zero {x : B} (h : x′ = 0) :
        x ∈ (algebraMap A B).range
  ```
  This is the **only** ring-level "derivation kernel = base ring" idiom
  in Mathlib b80f227 (only consumer:
  `Mathlib/FieldTheory/Differential/Liouville.lean`). **Crucially, it
  is a typeclass-interface, not a proven theorem**: there is no instance
  `[CharZero B] [IsIntegralDomain B] [Algebra A B] [Differential B] ⇒
  ContainConstants A B`. The ring-level char-0 fact (kernel of the
  exterior derivative on a char-0 integral domain over `k` is exactly
  `k`) is NOT proven in Mathlib.

  At the **scheme level**:
  - `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified` defines
    `FormallyUnramified` for scheme morphisms (equivalent to `Ω_{X/Y} = 0`);
    used in `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean` as part of
    `Étale = Smooth + Unramified`. **This is the wrong direction**: it
    captures `Ω_{X/Y} = 0`, not `Ω_{X/Y} ≠ 0` with `df = 0`. Not
    applicable to our piece (ii).
  - **No scheme-level "morphism with zero differential is constant"**
    declaration exists. Searches for
    `[Cc]onstant.*[Dd]ifferential`, `Scheme.*[Cc]onst`,
    `factors_through_terminal_of_diff_zero` all return zero hits.

- **Project's proposed path** (directive): build
  `AlgebraicGeometry.Morphism.isConst_of_diff_zero` or
  `Scheme.factors_through_terminal_of_diff_zero` at 200-400 LOC.

- **Gap**: divergent-with-cost on the naming side (the project should
  ALIGN with Mathlib's existing `Differential.ContainConstants`
  typeclass for the ring-level fact, registering an instance
  `[CharZero B] [Algebra A B] [IsIntegralDomain B] ⇒ ContainConstants A B`,
  and then derive the scheme-level statement on top). On the scheme
  side, it is NEEDS_MATHLIB_GAP_FILL — no precedent exists.

- **Cost of divergence (if project ignores `ContainConstants`)**: API
  fragmentation with `Mathlib.FieldTheory.Differential.Liouville`
  (the only other `ContainConstants` consumer in Mathlib). Bridge
  lemmas would be needed if any future project chapter wants to
  combine the project's char-0-rigidity lemma with a Liouville-style
  consumer. Easy to avoid by adopting the typeclass form upfront.

- **Verdict**: **ALIGN_WITH_MATHLIB** on the ring-level fact (use
  `Differential.ContainConstants`); **NEEDS_MATHLIB_GAP_FILL** on the
  scheme-level lift. Estimate: 100-200 LOC for the ring-level instance
  + 150-300 LOC for the scheme-level lift via `relativeDifferentialsPresheaf`
  and `Scheme.Over.ext_of_eqOnOpen` (the iter-125 refactored rigidity
  lemma) for the "scheme morphism agreeing on a non-empty open is
  determined" promotion. Realistic estimate: **250-500 LOC** for piece (ii).

### Decision (iii): characteristic-`p` handling

- **Mathlib coverage of the three options**:

  **Option A: Frobenius iteration** — Mathlib has:
  - `Mathlib/Algebra/CharP/Frobenius.lean:30-110+` —
    `frobenius R p`, `iterateFrobenius R p n`, with key lemma
    `iterateFrobenius_def : iterateFrobenius R p n x = x^p^n` (line 34)
    and `coe_iterateFrobenius` (line 43-44).
  - These are **ring-level only**. The **scheme-level absolute
    Frobenius** `F : X → X` is NOT packaged as a `Scheme.Hom` in
    Mathlib. Searches for `absoluteFrobenius`, `geometricFrobenius`,
    `relativeFrobenius`, scheme-side Frobenius patterns all return zero
    hits.
  - **However**, the project's own `Rigidity.lean:48-55` already
    explicitly grapples with the scheme-level Frobenius issue
    (Frobenius is `id` topologically but not on stalks) — that
    discussion is exactly the right design context to build a
    scheme-level Frobenius on top of `frobenius R p`.

  **Option B: Mumford's no-rational-curves argument** — Mathlib has:
  - **Zero infrastructure**. Searches for `no.*rational.*curve`,
    `noRationalCurve`, `rational.*curve.*abelian` all return zero hits.
  - This option would require building "an abelian variety contains no
    proper rational curves in char `p`" from scratch — itself a
    multi-thousand-LOC undertaking, since it transitively requires
    the cotangent / `Pic⁰` machinery the project is trying to avoid.

  **Option C: Lifting to char 0 via Witt vectors** — Mathlib has:
  - Extensive ring-level Witt vector infrastructure
    (`Mathlib/RingTheory/WittVector/{Basic,Defs,Frobenius,Compare,
    Complete,Identities,IsPoly,Teichmuller,...}.lean`).
  - **No scheme-level Witt vector functor**: no `Scheme.WittVector`,
    no "lift a smooth proper scheme from char `p` to char 0 via Witt
    vectors" declaration. Search for `Witt.*[Ll]ift`, `[Ll]ift.*Witt`,
    `cotangent.*[Ww]itt`, `deformation` all return zero hits.
  - Even the Cohen ring (the residue-field-pinned complete DVR of
    mixed characteristic) is absent: search for `[Cc]ohen.*[Rr]ing`
    returns zero hits.
  - Building the scheme-level Witt vector functor + smooth deformation
    + descent of the conclusion would be a **multi-thousand-LOC** chain
    — analogous in scope to building Hilbert schemes (which the project
    has already deferred).

- **Recommendation among the three**: **Option A (Frobenius
  iteration)** is decisively the most cost-effective:
  - It has the strongest existing Mathlib ring-level base
    (`frobenius` / `iterateFrobenius` are first-class) on which to
    erect a thin scheme-level wrapper (~200-300 LOC).
  - It composes cleanly with piece (ii): factor `f` as `f = f̃ ∘ F^n`
    where `f̃` has zero differential by construction; conclude
    constancy of `f̃` from piece (ii); descend constancy to `f` using
    smoothness of `Y` and surjectivity of `F^n` (the latter is the
    Frobenius-of-perfect-base statement, which Mathlib has via
    `Mathlib.FieldTheory.Perfect`).
  - Options B and C each carry standalone multi-thousand-LOC costs
    that exceed the entire pile budget.

- **Project's proposed path** (directive): "200-400 LOC for whichever
  option is chosen". The directive asks the analogist to choose.

- **Gap**: NEEDS_MATHLIB_GAP_FILL (the scheme-level Frobenius is
  absent), but with a **shipped ring-level base to consume**. Recommend
  ALIGN_WITH_MATHLIB on the `frobenius`/`iterateFrobenius` ring-level
  shape (don't redefine; consume `Mathlib.Algebra.CharP.Frobenius`
  directly).

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** for the scheme-level
  Frobenius packaging + iteration argument. **Recommend Option A
  (Frobenius iteration)** decisively over Options B and C. Realistic
  estimate: **300-600 LOC** for piece (iii) via Option A. (Slightly
  above the directive's 200-400 because the scheme-level Frobenius
  packaging is a sub-piece in its own right; cf. the project's
  `Rigidity.lean` Frobenius discussion that already establishes the
  design need.)

### Decision (iv): Serre duality on a smooth proper curve

- **Mathlib idiom**: **NONE**. The pre-existing analogy
  `analogies/serre-duality.md` (iter-110) has the verbatim verdict:
  - Search for `SerreDuality` / `serre_duality` returns **zero hits**
    in Mathlib.
  - Search for `DualizingSheaf`, `canonical[Bb]undle`, trace morphism
    for proper morphisms, coherent cohomology of proper schemes,
    Riemann-Roch, Riemann-Hurwitz: **all zero hits**.
  - "The entire Serre-duality stack is a structural absence in
    Mathlib's algebraic geometry, comparable in scope to the
    Hilbert/Quot scheme gap that drives the project's C3 deferral."

  Pre-existing project recommendation (`serre-duality.md` § "Recommendation"):
  **Defer `serre_duality_genus` indefinitely as a named Mathlib-gap
  sorry**, joining the existing named gaps in the project's end-state
  disclosure surface. LOC estimate for honest closure: **3,000-8,000 LOC**.

- **Project's proposed path** (directive): build at 200-400 LOC.

- **Gap**: NEEDS_MATHLIB_GAP_FILL with **directive estimate
  wildly underscoped**. The 3000-8000 LOC estimate of `serre-duality.md`
  is two-orders-of-magnitude above the directive's 200-400.

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** with **strong recommendation
  to DEFER**: piece (iv) is only used by M2.d-alt (genus-0
  identification alternative), not by M2.a's C.2.d. Per the directive's
  own scoping ("Used only by M2.d-alt, not by M2.a's C.2.d"), piece (iv)
  is **standalone for M2.d-alt** and outside the M2.a critical path.
  The pre-existing `serre-duality.md` deferral verdict should be
  reaffirmed: piece (iv) is **not part of the iter-129+ shared-pile
  build**; M2.d-alt's piece (iv) is **deferred indefinitely**.

  Alternative: if M2.d-alt is also given up (in favour of M2.d via
  Riemann-Roch, which is even more expensive per
  `STRATEGY.md:188`), the project keeps the existing two-named-gap
  posture (`JacobianWitness` + `serre_duality_genus`). The iter-126
  recommended posture is: M2.d-alt is the route, but piece (iv) is
  **deferred as a named gap inside M2.d-alt**, the same posture as
  `serre_duality_genus` at `Differentials.lean:877` today.

### Decision (v) [meta]: build order

- **Dependencies**:
  - Piece (ii) consumes piece (i) (needs `Ω_{Y/k}` to be trivial to
    conclude `df = 0` from `H⁰(X, f^* Ω_{Y/k}) → H⁰(X, Ω_{X/k}) = 0`).
  - Piece (iii) consumes piece (ii) (Frobenius iteration arranges
    `df = 0` after the right iterate, then applies piece (ii)).
  - Piece (i) and piece (iv) are independent of each other.
  - Piece (iv) is independent of (i)-(iii); only consumed by M2.d-alt's
    genus-0 identification.

- **Recommended build order for M2.a critical path**:
  1. **Piece (i)** first (iter-129+). 800-1500 LOC.
  2. **Piece (ii)** second (iter-131+ realistic). 250-500 LOC.
  3. **Piece (iii)** third (iter-133+ realistic). 300-600 LOC via
     Frobenius iteration (Option A).
  4. **Total realistic for M2.a critical path**: **1350-2600 LOC**,
     materially above the directive's "800-1500 LOC total" estimate
     (which conflated the four pieces' costs).

- **Piece (iv)**: **NOT part of iter-129+ shared-pile build**. Defer
  as named gap; document in `STRATEGY.md` under the existing
  `serre_duality_genus` named-gap entry. M2.d-alt's body closure
  honestly cannot land within the project's autonomous-iter budget.

- **Verdict**: PROCEED on the (i) → (ii) → (iii) sequencing for M2.a.
  Re-classify piece (iv) per `serre-duality.md` as deferred.

## Recommendation

The directive's scoping has **two material gaps** that the iter-129+
build directives must correct:

1. **Piece (i) under-scoped 4× (200-400 LOC → 800-1500 LOC).** The
   abelian-variety cotangent triviality is not a single lemma but a
   chain: Lie-algebra-of-GrpObj definition + mulRight-globalisation +
   trivialisation of the relative cotangent presheaf, all on top of the
   project's existing `relativeDifferentialsPresheaf` (and accepting the
   presheaf-vs-sheaf bridge cost from
   [[cotangent-presheaf-design]]). This is **the dominant cost driver**
   of the M2.a critical path; under-estimating it would propagate to
   wrong iter-by-iter prover lane sizing in iter-129+.

2. **Piece (iv) wildly under-scoped 10-40× (200-400 LOC → 3000-8000
   LOC) AND should be DEFERRED, not built.** Per
   [[serre-duality]] verdict from iter-110, Mathlib's Serre-duality
   stack is a structural absence at Hilbert/Quot-scheme scope.
   M2.d-alt's piece (iv) should be parked as a named-gap deferral
   inside M2.d-alt, mirroring the existing
   `Differentials.lean:877` `serre_duality_genus` named deferral. The
   iter-129+ shared-pile build is **pieces (i)+(ii)+(iii) only**, the
   M2.a critical path.

The directive's pieces (ii) and (iii) estimates (200-400 LOC) are in
range with a slight overshoot:
- **Piece (ii)**: align with `Differential.ContainConstants`
  typeclass at the ring level (the only Mathlib idiom; one existing
  consumer in `Liouville.lean`), then scheme-level lift via project's
  `Scheme.Over.ext_of_eqOnOpen`. Realistic: 250-500 LOC.
- **Piece (iii)**: Frobenius iteration (Option A) is decisively the
  right pick over Mumford / Witt-lifting (Options B/C), which each
  carry standalone multi-thousand-LOC dependencies. Build a thin
  scheme-level Frobenius wrapper on top of `frobenius` /
  `iterateFrobenius` from `Mathlib.Algebra.CharP.Frobenius`, then
  iterate-then-apply-piece-(ii)-then-descend-via-smoothness. Realistic:
  300-600 LOC.

**Build order**:
- iter-129+ (piece i, ~800-1500 LOC, 4-8 iters)
- → iter-133+ (piece ii, ~250-500 LOC, 1-3 iters)
- → iter-135+ (piece iii, ~300-600 LOC, 2-3 iters)
- → iter-138+ (M2.a body closure assembly, ~50-150 LOC, 1 iter)

**Total honest M2.a critical-path build**: **iter-138 to iter-145+**
(rather than iter-129+ to iter-138 implied by the directive's
collapsed 800-1500 LOC estimate). This puts honest **M2 closure at
iter-150+**, in line with `STRATEGY.md:492`'s "iter-152 to iter-170+"
range.

**Per-piece naming idiom recommendations (final naming TBD by prover
lane, but with strong align-with-Mathlib pulls)**:

- Piece (i): `AlgebraicGeometry.GrpObj.omega_free` and
  `AlgebraicGeometry.GrpObj.omega_rank_eq_dim`, **not**
  `AlgebraicGeometry.AbelianVariety.cotangent_trivial` — the directive's
  candidate names presuppose an `AbelianVariety` namespace that doesn't
  exist in Mathlib (search confirmed no `AbelianVariety` file). The
  Mathlib idiom is `GrpObj` (see `Group/Abelian.lean` and `Group/Smooth.lean`,
  which use `GrpObj G` over `Over (Spec (.of K))`); the project should
  follow that.
- Piece (ii): align ring-level with
  `Differential.ContainConstants` typeclass; scheme-level name should
  follow Mathlib's `Scheme.Over.ext_of_eqOnOpen` pattern (project-already-
  refactored iter-125), e.g.
  `AlgebraicGeometry.Scheme.Over.ext_of_diff_zero` rather than
  `isConst_of_diff_zero` — the project's iter-125 rigidity refactor
  already established the `ext_of_*` pattern as the right project idiom.
- Piece (iii): build a thin scheme-side
  `AlgebraicGeometry.Scheme.absoluteFrobenius` (or `Scheme.frobenius`)
  on top of `frobenius R p` for affine pieces, glued via the standard
  cover construction. Don't redefine Mathlib's ring-level `frobenius`.

## Severity

**high-stakes** — the persistent file
`analogies/cotangent-vanishing-pile.md` will be re-read by every
iter-129+ build lane. The two material corrections above (piece (i)
under-scoping, piece (iv) deferral) are the critical inputs that must
land in iter-127+ blueprint chapters and STRATEGY.md sequencing,
**before** the iter-129+ build lanes commit to the directive's
under-scoped LOC budgets.
