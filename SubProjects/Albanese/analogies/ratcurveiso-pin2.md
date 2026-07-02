# Analogy: Pin 2 — `morphism_degree_via_pole_divisor` (Hartshorne II.6.9 / IV §2)

## Mode
api-alignment

## Slug
ratcurveiso-pins (Pin 2)

## Iteration
181

## Question

Does Mathlib have either of (a) `Scheme.Hom.degree` for a morphism between
smooth proper curves over a field, (b) the pullback of a Weil divisor
`f^*D` on a scheme, (c) the Hartshorne II.6.9 identity
`deg(f^*D) = deg(f) · deg(D)`? If yes, the project should align with the
Mathlib idiom for
`AlgebraicGeometry.Scheme.morphism_degree_via_pole_divisor`
(`AlgebraicJacobian/RiemannRoch/RationalCurveIso.lean:296-306`).

## Project artifact(s)

- `AlgebraicJacobian/RiemannRoch/RationalCurveIso.lean:296-306` —
  `theorem morphism_degree_via_pole_divisor` with body `sorry`. The
  statement asserts `∃ (d : ℕ) (D : C.left.WeilDivisor), 0 < d ∧
  Scheme.WeilDivisor.degree D = (d : ℤ)` for a non-constant
  `φ : C ⟶ ProjectiveLineBar k̄`.
- `AlgebraicJacobian/RiemannRoch/WeilDivisor.lean:92-298` — the
  project-bespoke `Scheme.PrimeDivisor`, `Scheme.WeilDivisor`,
  `Scheme.WeilDivisor.degree`, `Scheme.WeilDivisor.principal` (all
  `sorry`-bodied skeletons).

## Decisions identified

Three coupled decisions:

1. Does Mathlib already define the *degree of a morphism* between
   schemes (or specifically between integral / smooth-proper-curve
   schemes)?
2. Does Mathlib define the *Weil-divisor pullback* `f^* : Div(Y) → Div(X)`
   for a (suitable) morphism of schemes?
3. Does Mathlib offer the multiplicativity-of-degree formula
   `deg(f^*D) = deg(f) · deg(D)`?

### Decision 1: degree of a morphism between schemes

- **Mathlib idiom**: NONE. Search confirms Mathlib has no
  `Scheme.Hom.degree`, no `Morphism.degree`, no
  `AlgebraicGeometry.FunctionField.transcendenceDegree`. The closest is:
  - `Mathlib.AlgebraicGeometry.FunctionField` —
    `AlgebraicGeometry.Scheme.functionField (X : Scheme) [IrreducibleSpace X] : CommRingCat`
    (the field at the generic point, abbreviation `K(X)`).
  - `Mathlib.AlgebraicGeometry.FunctionField:instIsFractionRing...` —
    when `X` is integral, `IsFractionRing (X.presheaf.stalk x) X.functionField`.
  - `Mathlib.AlgebraicGeometry.Morphisms.Finite` — `IsFinite f` /
    `IsFinite.iff_isProper_and_isAffineHom`.
  - `Mathlib.AlgebraicGeometry.RationalMap` — `Scheme.RationalMap`,
    `ofFunctionField` / `fromFunctionField`.
  - `Mathlib.FieldTheory.SeparableDegree.Field.finSepDegree`,
    `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic.IntermediateField.adjoin.finrank`,
    `Module.finrank` over a field extension.

  So the **field-theoretic ingredient** for "degree of a finite morphism
  of integral schemes" — namely `[K(C) : K(C')]` via
  `Module.finrank C'.functionField C.functionField` — is present, but the
  *bridge* (i.e. wrap "finrank of the function-field extension" as a
  named `Scheme.Hom.degree` with the multiplicativity API) is absent.

- **Project's current path**: define the degree implicitly inside the
  existence statement `∃ d, 0 < d ∧ D.degree = (d : ℤ)`. The `d` here is
  conceptually `[K(C) : k̄(ℙ¹)]` but the lemma never names a separate
  `degree_of_morphism` definition.

- **Gap**: divergent-and-isolated. Mathlib has neither a `degree` API
  for `Scheme.Hom` nor a Weil-divisor type for schemes — the project
  could not "align" even if it tried. The current statement (existence
  of a positive-degree divisor) is the right substantive content given
  the project-bespoke `Scheme.WeilDivisor` type.

- **Cost of divergence**: zero, because no Mathlib API exists to
  fragment with. The eventual *body* of the lemma will route through
  `Module.finrank C'.functionField C.functionField` + the
  project's own `WeilDivisor.pullback` (to be built) + a coordinate-by-
  coordinate identification.

- **Verdict**: **PROCEED**. Mathlib has no scheme-level morphism-degree
  API to align with; the project's statement is the correct shape.

### Decision 2: Weil-divisor pullback `f^* : Div(Y) → Div(X)`

- **Mathlib idiom**: NONE for schemes. The only "divisor pullback" in
  Mathlib is for the complex-analytic case:
  - `Mathlib.Analysis.Meromorphic.Divisor.MeromorphicOn.divisor` (complex
    analytic; takes a meromorphic function on `U ⊆ 𝕜` and produces a
    divisor).

  For affine commutative rings Mathlib has:
  - `Mathlib.RingTheory.PicardGroup.CommRing.Pic` (the Picard group as an
    isomorphism class of invertible modules) — but this is for a single
    commutative ring, not for a scheme, and it does not expose a
    "divisor of a function" or pullback API.

  The most directly relevant Mathlib infrastructure for the eventual
  body is:
  - `Mathlib.NumberTheory.RamificationInertia.Basic.Ideal.sum_ramification_inertia`
    (for a finite extension of Dedekind domains, the sum
    `Σ_{P over p} e(P|p) · f(P|p) = [L:K]`). This is the algebraic
    incarnation of Hartshorne II.6.9 specialised to Dedekind bases.
  - `Mathlib.NumberTheory.RamificationInertia.Basic.Ideal.finrank_quotient_map`
    (the closely related `finrank` identity).

- **Project's current path**: `Scheme.WeilDivisor.pullback` does NOT
  exist in `WeilDivisor.lean` yet; the iter-178+ body of Pin 2 is
  expected to introduce a project-private pullback construction (per
  the lemma's docstring comment at L283-292).

- **Gap**: divergent-and-isolated. Same reason as Decision 1: Mathlib
  has no scheme-level WeilDivisor to pull back.

- **Cost of divergence**: zero now; non-zero once the project starts
  building. The natural body uses `Ideal.sum_ramification_inertia` on
  each affine chart (pick an affine open `Spec A ⊂ C'` covering `∞`,
  then the preimage `Spec B ⊂ C` is finite over `Spec A` with
  `A → B` Dedekind-of-Dedekind, and `Σ_{Q over P} e(Q|P) · f(Q|P) = d`).
  This is `~50-100 LOC` glue around the existing Mathlib lemma.

- **Verdict**: **PROCEED** (with `Ideal.sum_ramification_inertia` as
  the body-engine for iter-178+).

### Decision 3: multiplicativity of degree

- **Mathlib idiom**: `Mathlib.NumberTheory.RamificationInertia.Basic`
  (`sum_ramification_inertia`, `ramificationIdx_mul_inertiaDeg_of_isLocalRing`)
  is the algebraic statement. There is no scheme-level wrapper.
- **Verdict**: **PROCEED** (consume the ring-level statement inside
  the body).

## Recommendation

Both the **signature** and the eventual **body** for Pin 2 are
project-bespoke — Mathlib has the algebraic atom
(`Ideal.sum_ramification_inertia` in
`Mathlib.NumberTheory.RamificationInertia.Basic`) but no scheme-level
divisor / morphism-degree wrapper to align with. The iter-178+ planner
should:

1. Keep the current signature of `morphism_degree_via_pole_divisor` (it
   is the right substantive content given the project-bespoke
   `Scheme.WeilDivisor`).
2. Plan to introduce a private `Scheme.WeilDivisor.pullback` (or a
   one-shot pole-divisor construction `Scheme.Hom.poleDivisor` for
   `φ : C ⟶ ℙ¹`) inside `RationalCurveIso.lean` or
   `WeilDivisor.lean`.
3. Reduce the multiplicativity-of-degree identity through
   `Ideal.sum_ramification_inertia` on a chosen affine cover (the
   only point of contact with Mathlib). Budget: ~80-150 LOC for the
   pullback + the per-chart Dedekind-domain bridge.

No Mathlib **upstream PR** is required — this is genuine new
infrastructure that Mathlib lacks, not a re-implementation. If the
project ever exports a `Scheme.WeilDivisor.pullback`-style API, it
*would* be worth a future Mathlib PR (Stacks tags 02RW, 02RX, 0AX5
cover this material), but that is out of scope for the iter-181/182
plan.

## Possible Mathlib gap-fill (informational, not blocking)

For the eventual upstream PR (post-project), the following would close
the gap in Mathlib:

- `AlgebraicGeometry.Scheme.Hom.degree : (f : X ⟶ Y) [IsIntegral X]
  [IsIntegral Y] [IsFinite f] [LocallyOfFiniteType f] : ℕ`
  defined as `Module.finrank Y.functionField X.functionField`.
- `AlgebraicGeometry.Scheme.WeilDivisor` (currently project-bespoke).
- `AlgebraicGeometry.Scheme.WeilDivisor.pullback (f : X ⟶ Y) [IsFinite f] :
  Y.WeilDivisor →+ X.WeilDivisor`.
- `Scheme.WeilDivisor.degree_pullback` (Hartshorne II.6.9):
  `(f^*D).degree = f.degree * D.degree`.

The project must not block on any of these — the in-tree route is the
correct call for iter-181/182.
