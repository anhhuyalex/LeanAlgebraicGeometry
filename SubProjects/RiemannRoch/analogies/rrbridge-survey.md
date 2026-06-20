# Analogy: Mathlib backing for `genusZero_curve_iso_P1` (the "RR bridge")

## Mode
api-alignment

## Slug
rrbridge

## Iteration
168

## Question

The progress-critic iter-168 raised a dispatch CHALLENGE: is
`genusZero_curve_iso_P1` (`AlgebraicJacobian/AbelianVarietyRigidity.lean:1135`)
dispatchable as a parallel Lane B prover lane this iter, or does it require
upstream chapter expansion / multi-iter Mathlib sub-build first? In particular:

- (Q1) Does Mathlib have a Riemann–Roch for curves?
- (Q2) Does Mathlib have Weil/Cartier divisors, a degree map `Pic → ℤ`,
  a `Mor(C, ℙ¹)` classification, or Hurwitz/Castelnuovo at scheme level?
- (Q3) Of the four Hartshorne IV.1.3.5 ingredients — (i) divisor of a closed
  point, (ii) RR dimension formula, (iii) linear equivalence, (iv) "rational
  ⟹ ≅ ℙ¹" — which are in Mathlib at scheme level?
- (Q4) If not dispatchable, what upstream chapter / Mathlib infrastructure
  must the planner schedule?
- (Q5) Is `Nonempty (C ≅ ProjectiveLineBar kbar)` the right Lean shape?

## Project artifact(s)

- `AlgebraicJacobian/AbelianVarietyRigidity.lean:1135` — current statement
  `genusZero_curve_iso_P1 : … (_hgenus : genus C = 0) : Nonempty (C ≅ ProjectiveLineBar kbar)`
  with `sorry` body.
- `AlgebraicJacobian/AbelianVarietyRigidity.lean:1160` — the only consumer
  `rigidity_genus0_curve_to_grpScheme`, which `obtain ⟨φ⟩ := genusZero_curve_iso_P1 _hgenus`
  and transports `f` along `φ`.
- `AlgebraicJacobian/Genus.lean:40` — project's `genus C := Module.finrank k
  (Scheme.HModule k (Scheme.toModuleKSheaf C) 1)` (project's own `ModuleCat k`-flavoured
  `H¹(C, O_C)`).
- `blueprint/src/chapters/AbelianVarietyRigidity.tex:1448–1501` — the
  `prop:genusZero_curve_iso_P1` block plus `rmk:genusZero_iso_subbuild`
  ("Mathlib has no Riemann–Roch theorem for curves, no divisor class group
  machinery at this level, and no ℙ¹-classification of rational curves").

## Decisions identified

### Decision 1: Is there a Mathlib Riemann–Roch theorem to invoke?

- **Mathlib idiom**: There is *no* Riemann–Roch theorem for algebraic curves
  at scheme level. LSP probes:
  - `lean_leansearch "Riemann-Roch theorem for curves"` returns only
    Weierstrass-curve polynomial-degree results
    (`Mathlib.AlgebraicGeometry.EllipticCurve.*`), nothing geometric.
  - `lean_loogle "RiemannRoch"` returns **no hits**.
  - `lean_leansearch "scheme genus zero rational curve P1"` returns only
    `WeierstrassCurve.Projective.*` (elliptic-curve point arithmetic).
  - `lean_leansearch "smooth proper curve dimension cohomology"` returns
    `IsSmoothOfRelativeDimension`, `H1Cotangent` — definitions, no theorems.
  - The only "RR-shaped" data in Mathlib is in
    `Mathlib.Analysis.Meromorphic.Divisor` (`MeromorphicOn.divisor` —
    analytic, normed-field-valued, not algebraic), and inside
    `WeierstrassCurve.*` (division polynomials of *elliptic* curves —
    not curves of genus 0).
- **Project's path**: `prop:genusZero_curve_iso_P1` proof block cites
  Hartshorne IV.1.3.5 directly (RR on `D = P − Q`, then Hartshorne II.6.10.1
  to upgrade `P ∼ Q` to a degree-1 map to ℙ¹). The Lean body is
  `sorry`-stubbed pending a sub-build.
- **Gap**: divergent-with-cost — but the divergence is *upstream*, not a
  project misdesign. Mathlib has no RR; there is no idiom to align with.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision 2: Is divisor / Pic / degree machinery available?

- **Mathlib idiom**: All four required pieces are *absent* at scheme level:
  - **Weil/Cartier divisors on a scheme**: ABSENT. `lean_loogle "Divisor"`
    returns no hits. The only `divisor` is `MeromorphicOn.divisor`
    (`Mathlib.Analysis.Meromorphic.Divisor`), which is the order function of
    a meromorphic function on a subset of a normed field — *not* a
    formal-sum-of-codim-1-cycles on a scheme.
  - **Picard group of a scheme**: ABSENT. `CommRing.Pic R`
    (`Mathlib.RingTheory.PicardGroup`) is *ring-level only* (invertible
    `R`-modules under tensor product). There is no `AlgebraicGeometry.Scheme.Pic`
    in Mathlib (the project once had a `Scheme.Pic` scaffold in
    `.archon/lanes/{kimi,anthropic,deepseek}/AlgebraicJacobian/Picard/LineBundle.lean`
    but those snapshots are *project-internal experimental code*, not
    Mathlib — they were never landed).
  - **Degree map `Pic → ℤ` for a curve**: ABSENT (precondition `Scheme.Pic`
    missing).
  - **`Mor(C, ℙ¹)` ≅ "degree-1 line bundle + 2 sections" classification**:
    ABSENT. Mathlib's closest tool is `AlgebraicGeometry.Proj.fromOfGlobalSections`
    (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`), which packages
    "two compatible degree-1 global sections of the graded ring give a
    morphism into `Proj 𝒜`". The project ALREADY uses this in
    `Genus0BaseObjects.{zeroPt,onePt,inftyPt}` to build *k̄-points* of ℙ¹.
    It does *not* extend to the divisor-theoretic "degree-1 line bundle
    on C induces a map C → ℙ¹" — that requires divisor → line-bundle, line
    bundle → global sections, RR on H⁰, all absent.
  - **Hurwitz / Castelnuovo**: ABSENT.
  - **Function field of an irreducible scheme**: PRESENT —
    `AlgebraicGeometry.Scheme.functionField` (`Mathlib.AlgebraicGeometry.FunctionField`).
    Useful for a function-field-theoretic route but not by itself
    enough.
  - **Rational maps**: PRESENT — `AlgebraicGeometry.Scheme.RationalMap`
    (`Mathlib.AlgebraicGeometry.Birational.RationalMap`). Domain
    of definition, extension along reduced/separated targets, etc.
    Adjacent to Hartshorne II.6.10.1's "rational ⟹ ≅ ℙ¹" but doesn't
    package the conclusion.
- **Project's path**: The project has NOT built a divisor stack — it
  deliberately demoted Route A (the FGA/Pic representability engine) off
  the genus-0 critical path (see iter-163 memory
  `[[route-c-cube-not-needed-iter163]]`). The project's only line-bundle-shaped
  artifact is the older `.archon/lanes/.../Picard/LineBundle.lean`
  scaffolds (project-internal experimental code, never landed and now
  abandoned per `M3` audit).
- **Gap**: divergent-with-cost — the gap is *deliberate*. The project
  committed to Route C precisely *because* Route A (Pic/divisor/RR)
  was an unbounded sub-build. The cost of NOT having this stack is
  exactly the present situation: `genusZero_curve_iso_P1` has no
  honest in-project closure.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (the gap is the *committed
  trade-off*; closure requires either a sub-build or a sidestep).

### Decision 3: Per-Hartshorne-piece audit (Q3)

For each piece of Hartshorne's IV.1.3.5 proof:

| Hartshorne ingredient | Mathlib status |
|---|---|
| (i) Divisor `P − Q` of two closed points on a curve | ABSENT — no `WeilDivisor`/`CartierDivisor` on a scheme. |
| (ii) RR dimension formula `l(D) − l(K − D) = deg D + 1 − g` | ABSENT — no RR theorem. |
| (iii) Linear equivalence `D ∼ D'` of divisors | ABSENT — precondition (divisors) missing. |
| (iv) "X rational ⟹ X ≅ ℙ¹" (Hartshorne II.6.10.1 / I.6.12) | ABSENT — `RationalMap` exists but the classification "complete nonsingular curve birational to ℙ¹ ⟹ ≅ ℙ¹" is not packaged. Would need scheme-level normalisation + the equivalence "smooth proper curve ≅ DVR-valuation-ring patching". |

- **Verdict**: every one of (i)–(iv) is NEEDS_MATHLIB_GAP_FILL.

### Decision 4: Cheapest Mathlib-supportable variant of "genus-0 ⟹ ≅ ℙ¹"

What CAN Mathlib support TODAY?

- The project's `genus C = 0` unfolds (via the `Scheme.HModule k F 1`
  layer at `AlgebraicJacobian/Cohomology/StructureSheafModuleK.lean`) to
  `Module.finrank k (H¹(C, O_C)) = 0`, which together with finite-
  dimensionality (Serre, *queued* in the project per `Genus.tex
  §Genus_status`) gives `H¹(C, O_C) = 0` as a `k`-vector space.
- That alone is *not* enough to recover `C ≅ ℙ¹`. Each of the classical
  routes blocks:
  - **Divisor-theoretic (Hartshorne IV.1.3.5)**: blocked by all four
    pieces above.
  - **Direct `Proj.fromOfGlobalSections` construction**: would require
    producing two compatible degree-1 sections of some line bundle on
    C. The project has `pointOfVec`-style maps from a unit-vector data
    into `Proj` of `MvPolynomial (Fin 2) k̄`, but those *take ℙ¹ as
    target*; they do not produce maps *from* C into ℙ¹.
  - **Function-field / valuation-theoretic** (smooth proper curve
    determined by `k(C)`; for genus 0 the function field is rational
    `k̄(t)` ⟹ ≅ ℙ¹): requires the scheme/normalization equivalence
    "smooth proper curve over k̄ ↔ finitely-generated field extension
    of trdeg 1" — present in Hartshorne I.6 but ABSENT in Mathlib.
  - **Pic⁰ group scheme**: this is Route A, deliberately deferred.
  - **Direct via Albanese**: circular (this lemma is what feeds the
    genus-0 Albanese witness).

- **Conclusion**: there is no Mathlib-supported route TODAY. The
  cheapest variant of `C ≅ ℙ¹` Mathlib supports is *trivial*: it
  supports `ProjectiveLineBar kbar ≅ ProjectiveLineBar kbar` (the
  identity). It does not bridge `genus C = 0` to that.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision 5: Lean signature shape (Q5)

- **Current**: `theorem genusZero_curve_iso_P1 … (_hgenus : genus C = 0)
  : Nonempty (C ≅ ProjectiveLineBar kbar)`
- **Consumer use** (`AlgebraicJacobian/AbelianVarietyRigidity.lean:1174`):
  `obtain ⟨φ⟩ := genusZero_curve_iso_P1 _hgenus; set g := φ.inv ≫ f; …`.
  The consumer destructs `Nonempty`, extracts `φ`, and transports a
  morphism along `φ`. The choice of `φ` is irrelevant downstream
  (`morphism_P1_to_grpScheme_const g` exhibits an `a₀` for *any*
  such `g`).
- **Alternative shapes considered**:
  - `(p : 𝟙_ ⟶ C) → (C ≅ ProjectiveLineBar kbar)` carrying the
    point: the consumer ALREADY has a `k̄`-point `p` of `C`, and a
    pointed iso (`φ.hom ∘ p = ℙ¹.zeroPt`) would shorten the basepoint-
    pinning step. But the consumer's basepoint-pinning is currently
    one short `calc` step (`toUnit_unique` + `Category.id_comp`), so
    the simplification is marginal.
  - `(C ≅ ProjectiveLineBar kbar) ⊕ (genus C > 0)` (genus-stratified):
    redundant — `_hgenus : genus C = 0` already discriminates.
  - Direct conclusion (skip the iso): `(f : C ⟶ A) → … → f = toUnit C
    ≫ η[A]` (i.e. fold the whole `rigidity_genus0_curve_to_grpScheme`
    body into a single lemma). This would *avoid* `genusZero_curve_iso_P1`
    as a standalone — but it does NOT avoid its mathematical content;
    the proof would still need to reduce to the ℙ¹ case somewhere.
- **Mathlib idiom**: `Nonempty (X ≅ Y)` is the standard "X is
  isomorphic to Y" shape in `CategoryTheory` (cf.
  `Mathlib.CategoryTheory.IsoClass`, `Nonempty (X ⟶ Y)` for
  "morphism exists" patterns). The current shape *is* idiomatic.
- **Verdict**: PROCEED. The signature is correctly shaped.

## Recommendation

`genusZero_curve_iso_P1` is **NOT dispatchable as a Lane B prover lane this
iter**. Every one of the four Hartshorne IV.1.3.5 ingredients — divisor of a
closed point, RR dimension formula, linear equivalence, "rational ⟹ ≅ ℙ¹" —
is absent from Mathlib at scheme level, with no isolated piece reachable
without the prerequisites of the others. There is no Mathlib-supported
shortcut around the RR-style sub-build.

The planner has four real options:

1. **(Preferred) Schedule a blueprint-writer expansion of
   `prop:genusZero_curve_iso_P1` into a divisor-theoretic sub-build**
   under a new chapter section (e.g. `\section{Riemann–Roch on a
   curve (genus-0 case)}`). This makes the gap concrete and
   sub-divisible. Estimated 30–60 iters of prover work on top of the
   blueprint expansion. *Cost*: large; *benefit*: keeps the iso
   axiom-clean and re-usable, and the divisor stack feeds Route A
   (positive-genus Albanese) if it is ever revisited.

2. **Defer to upstream Mathlib**: track Mathlib's nascent Pic / divisor
   activity (the present `CommRing.Pic` / `MeromorphicOn.divisor` /
   `Scheme.RationalMap` are visible threads). Pin
   `genusZero_curve_iso_P1` as an explicit named gap in the blueprint
   (already done in `rmk:genusZero_iso_subbuild`). Continue to ship
   the rest of the chain as axiom-clean *modulo* this single named
   gap, and budget zero iters on it. *Cost*: leaves the headline
   `rigidity_genus0_curve_to_grpScheme` carrying `sorryAx`; *benefit*:
   no project-internal time spent.

3. **Sidestep via a different proof structure that does not reduce to
   ℙ¹**. Mathlib's available primitives — `rigidity_lemma`,
   `rigidity_eqOn_dense_open`, `ext_of_eqOnOpen`,
   `Proj.fromOfGlobalSections` — only let us *consume* a ℙ¹-iso, not
   produce one. The 𝔾ₘ-scaling shortcut needs ℙ¹'s scaling
   automorphism, which a generic genus-0 curve does NOT carry until
   it is identified with ℙ¹. A `df = 0` route exists in char 0 but is
   the project's *demoted fallback* (route (a)) and breaks in char p,
   contradicting the char-free commitment in `thm:rigidity_genus0_curve_to_AV`.
   No char-free sidestep is known. *Cost*: research-bounded;
   *benefit*: speculative.

4. **User-authorised `axiom` declaration** for `genusZero_curve_iso_P1`
   with the matching Hartshorne IV.1.3.5 citation. *Cost*: violates
   the project's axiom-clean target; *benefit*: unblocks `rigidity_genus0_curve_to_grpScheme`
   and the genus-0 Albanese witness.

**My recommendation**: option (2) — defer to upstream Mathlib AND
formalize the gap as the project's *named* RR gap in the chapter (the
blueprint already does this at `rmk:genusZero_iso_subbuild`; no extra
work). Concretely, the planner should NOT open a Lane B prover lane on
this lemma this iter; should NOT escalate it to "dispatchable"; should
keep it on the "named gap" list alongside the M3 Albanese gap (per
`analogies/m3-route-audit.md`). If user explicitly authorises an axiom
(option 4), do so with the Hartshorne IV.1.3.5 citation; otherwise the
genus-0 headline `rigidity_genus0_curve_to_grpScheme` will carry a
propagated `sorryAx` through this lemma until upstream lands a divisor
stack. The signature shape (Decision 5) is correct as-is — do NOT
refactor.

## Persistent file
- `analogies/rrbridge-survey.md` — this file, captured for future iters.
