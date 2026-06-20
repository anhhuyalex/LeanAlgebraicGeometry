# Analogy: SES → long exact sequence of right-derived functors (dimension shift)

## Mode
api-alignment

## Slug
p4-derived-les

## Iteration
003

## Question
To build "an acyclic resolution computes the right-derived functor" (Leray
acyclicity, Stacks 015E) at the level of `CategoryTheory.Functor.rightDerived n`,
the kernel step is a dimension shift across a SES `0 → A → J → Z → 0` (J right-G-
acyclic) producing `(R^k G)(Z) ≅ (R^{k+1} G)(A)` (k ≥ 1) and
`(R^1 G)(A) ≅ coker(G J → G Z)`. This needs a SES → LES of right-derived functors.
Is the explicit horseshoe (`InjectiveResolution.ofShortExact`) the cheapest Mathlib-
aligned path, or does Mathlib already provide SES → LES of derived functors another
way (derived-category triangle, snake on a single resolution, or an Ext-level LES
that specializes to `rightDerived`)?

## Project artifact(s)
- `blueprint/src/chapters/Cohomology_AcyclicResolution.tex` — whole chapter;
  `lem:injective_resolution_of_ses` (horseshoe), `lem:acyclic_dimension_shift`
  (kernel), `lem:acyclic_resolution_computes_derived` (Leray 015E).
- Target Lean: `Functor.IsRightAcyclic`, `InjectiveResolution.ofShortExact`,
  `Functor.rightDerivedShiftIsoOfAcyclic`, `Functor.rightDerivedIsoOfAcyclicResolution`.

## Decisions identified

### Decision: how to obtain the SES → LES of `Functor.rightDerived n G`

- **Mathlib idiom**: There is **no** SES → LES for `Functor.rightDerived n`. The
  closest analogues are NOT applicable:
  - *Ext LES* (`Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean`,
    `covariantSequence` / `contravariantSequence`, `covariant_sequence_exact₁/₂/₃`).
    These are built from the cohomological functors `preadditiveCoyoneda` /
    `preadditiveYoneda` applied to `triangleOfSES`'s homology sequence. They derive
    the LES of `Ext^n(X, –)` / `Ext^n(–, Y)` — i.e. of **derived Hom** — NOT of a
    general additive functor `G`. The project's `G = f_*` is not a Hom-functor, so
    this LES cannot be specialized to it. (`Ext.lean` defines `Ext` as
    `Abelian.Ext`, derived from `Hom` in the derived category — orthogonal to a
    user-supplied `G`.)
  - *Derived-category triangulated route* (`triangleOfSES` +
    `triangleOfSES_distinguished` in
    `Mathlib/Algebra/Homology/DerivedCategory/ShortExact.lean`, plus
    `Pretriangulated.homologySequence_exact₁/₂/₃`). This gives the LES for a
    triangulated functor between derived categories. To feed `Functor.rightDerived n
    G` into it one needs the bridge
    `F.rightDerived n ≅ Hⁿ ∘ F.rightDerivedFunctorPlus ∘ Q` with
    `F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`.
    **That bridge does not exist** — it is an explicit TODO in the module docstring
    of `Mathlib/CategoryTheory/Abelian/RightDerived.lean` (lines 40–47):
    "refactor `Functor.rightDerived` … when the necessary material enters mathlib:
    derived categories, injective/projective derivability structures, existence of
    derived functors from derivability structures. Eventually … redefined using
    `F.rightDerivedFunctorPlus`." Building it requires the injective derivability
    structure + existence-of-derived-functor machinery (the
    `CategoryTheory/Localization/DerivabilityStructure/*` + `Functor/Derived/*`
    framework) AND a comparison theorem — far more than the horseshoe.
- **Project's current path**: build `InjectiveResolution.ofShortExact` (dual
  Horseshoe Lemma) → apply G degreewise (split ⇒ preserved) → complex-level homology
  LES (`ShortComplex.ShortExact.δ/homology_exact₁/₂/₃`, present in
  `Mathlib/Algebra/Homology/HomologySequence.lean:282–314`) → transport along
  `InjectiveResolution.isoRightDerivedObj` (present).
- **Gap**: NEEDS_MATHLIB_GAP_FILL. The LES is genuinely absent for general `G`; the
  horseshoe is one self-contained way to manufacture it. The two "shortcut"
  alternatives are each strictly more expensive (Ext: wrong generality, unusable;
  derived-category: an explicitly-deferred Mathlib TODO).
- **Cost of divergence (if any)**: none — the horseshoe is the *cheaper* gap. The
  derived-category route would force the project to build (or wait for) the entire
  `rightDerivedFunctorPlus` bridge.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (horseshoe is the right gap).

### Decision: shape of `IsRightAcyclic`

- **Mathlib idiom**: vanishing predicates over an object are `class … : Prop`
  (cf. `Injective`, `Projective` in
  `Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean`). The companion
  vanishing fact is `Functor.isZero_rightDerived_obj_injective_succ` which states
  `IsZero ((F.rightDerived (n+1)).obj J)` for injective `J` — i.e. the
  index-shifted form `∀ k, IsZero ((R^{k+1} G) J)`.
- **Project's current path**: blueprint `def:right_acyclic` adopts exactly the
  index-shifted vanishing `(R^{k+1} G)(J) = 0 ∀ k`.
- **Gap**: identical (good). A `class IsRightAcyclic (G) (J) : Prop` wrapping
  `∀ k, IsZero ((G.rightDerived (k+1)).obj J)` mirrors Mathlib, and an `instance`
  deriving it for injectives from `isZero_rightDerived_obj_injective_succ` is free.
- **Verdict**: PROCEED (align field shape with the `isZero …_succ` quantifier).

## Recommendation

Scaffold the **horseshoe** (`InjectiveResolution.ofShortExact`) — it is the right,
necessary, self-contained project-side gap, not a detour. Do NOT scaffold a derived-
category route: its prerequisite (`rightDerivedFunctorPlus` + injective derivability
structure) is an open Mathlib TODO and dwarfs the horseshoe. Do NOT try to specialize
the Ext LES: it is derived-Hom-specific and cannot see a general `G = f_*`.

Concrete scaffold shape for the horseshoe and downstream:
1. `IsRightAcyclic G J : Prop` as a `class` = `∀ k, IsZero ((G.rightDerived (k+1)).obj J)`;
   instance for `[Injective J]` via `isZero_rightDerived_obj_injective_succ`.
2. `InjectiveResolution.ofShortExact` — the hard part. Build `I_B` degreewise as
   `I_A.cocomplex.X n ⊞ I_C.cocomplex.X n` (biproduct ⇒ injective) with the
   **twisted** differential `[[d_A, τ], [0, d_C]]`; the off-diagonal `τ` and the
   augmentation `B → I_B^0` are produced stage-by-stage by the injective lifting
   property (`Injective.factorThru` against the relevant monos). Model the recursion
   on the existing `InjectiveResolution.ofCocomplex` / `exact_f_d` /
   `ofCocomplex_exactAt_succ` machinery
   (`Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean:270–352`). Prove
   degreewise-split SES of complexes `0 → I_A → I_B → I_C → 0` and that `I_B`
   resolves `B` (exactness via the complex homology LES on the split SES).
   Expose the output as a `ShortComplex (CochainComplex C ℕ)` that `.ShortExact`.
3. `rightDerivedShiftIsoOfAcyclic` — apply `G` to the degreewise-split SES (additive
   `G` preserves split SES: use `ShortComplex.Splitting.map` /
   `Functor.mapShortComplex` on the per-degree splitting), get a `ShortExact` of
   `CochainComplex D ℕ`, feed `HomologySequence.δ` + `homology_exact₁/₂/₃`, transport
   each `Hⁿ(G(I_•))` to `(Rⁿ G)(•)` via `isoRightDerivedObj`, then kill the acyclic
   `(R^{≥1} G)(J)` terms.

Feasibility note: the genuinely hard Lean sub-task is the twisted differential `τ`
and proving `I_B` is a resolution — a dependent recursion over `ℕ`. This is the
dominant risk and should get its own prover objective, scaffolded as a standalone
lemma chain (per-degree `τ`, chain-map laws, exactness) rather than one monolithic
definition. One cheap simplification to peel off first: the **injective-middle**
dimension shift (`0 → A → Q → A' → 0`, `Q` injective) needs NO horseshoe — it is a
re-indexing of a single injective resolution of `A` (shift `I_A^{≥1}`) and follows
from `isoRightDerivedObj` + `isZero_rightDerived_obj_injective_succ`. It does NOT
discharge the acyclic-middle case the cosyzygy SESs require, so it cannot replace the
horseshoe — but it is a useful warm-up / sanity lemma and may shorten the base degree.
