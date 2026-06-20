# Analogy: Pin 3 — `iso_of_degree_one` (Hartshorne I.6.12 / Stacks 0AVX)

## Mode
api-alignment

## Slug
ratcurveiso-pins (Pin 3)

## Iteration
181

## Question

Does Mathlib have either of (a) a "degree-1 morphism is iso" lemma for
smooth proper curves, (b) `IsBirational` for scheme morphisms with the
"birational ⟹ iso for smooth proper schemes" specialisation, (c)
Zariski's main theorem at a level the project can consume directly? If
yes, the project should align with the Mathlib idiom for
`AlgebraicGeometry.Scheme.iso_of_degree_one`
(`AlgebraicJacobian/RiemannRoch/RationalCurveIso.lean:356-369`).

## Project artifact(s)

- `AlgebraicJacobian/RiemannRoch/RationalCurveIso.lean:356-369` —
  `theorem iso_of_degree_one` with body `sorry`. The statement asserts
  `Nonempty (C ≅ C')` from `φ : C ⟶ C'` non-constant + the existence of
  a ring iso `C'.left.functionField ≃+* C.left.functionField`.

## Decisions identified

Two coupled decisions:

1. Does Mathlib have a `IsBirational` predicate or the specialised
   theorem "birational ⟹ iso for smooth proper integral schemes (or
   curves)"?
2. Does Mathlib have any wrapper of Zariski's main theorem / Hartshorne
   III.11.4 / Stacks 0AVX at the curve level?

### Decision 1: birational ⟹ iso (for smooth proper curves)

- **Mathlib idiom**: NONE for the named theorem. Search confirms no
  `IsBirational`, no `Hartshorne.III_11_4`, no `ZariskiMainTheorem`,
  no "degree-1 ⟹ iso" specialisation. The closest Mathlib has:

  - `Mathlib.AlgebraicGeometry.Normalization` —
    `Scheme.Hom.toNormalization f` and the instance
    `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom`
    (`QuasiCompact f` + `QuasiSeparated f` + `IsIntegralHom f` ⟹
    `IsIso (Scheme.Hom.toNormalization f)`). The normalisation =
    the target when the target is already normal. Smooth ⟹ regular ⟹
    normal in dim 1, so this lemma is *almost* what is needed — but it
    proves the *normalisation map* is an iso, not the original morphism.
    Bridging it would need to identify `Scheme.Hom.normalization f` with
    `C` itself (under the smooth-proper-curve hypothesis) and route the
    final iso through the normalisation universal property.

  - `Mathlib.AlgebraicGeometry.RationalMap`:
    `Scheme.RationalMap.ofFunctionField`,
    `Scheme.RationalMap.fromFunctionField`. These give the rational-map
    side of "function-field iso ⟹ birational map", but the *extension
    of a rational map to a morphism* (the "smooth-target / proper-source
    extension" theorem) is also absent from Mathlib for the
    smooth-proper-curve setting.

  - `Mathlib.AlgebraicGeometry.OpenImmersion.isIso_iff_stalk_iso` /
    `isIso_iff_isIso_stalkMap`: `f` is iso iff `f.base` is iso *and*
    each stalk map is iso. This is the cleanest Mathlib criterion to
    reduce the goal to (stalks + topological iso).

  - `Mathlib.AlgebraicGeometry.Morphisms.IsIso.isomorphisms_eq_stalkwise`
    / `isIso_iff_isOpenImmersion_and_surjective` — alternative
    iso criteria via stalks + open immersion / surjective.

  - `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.isIso_of_isClosedImmersion_of_surjective`:
    closed immersion + surjective + reduced target ⟹ iso. This is a
    convenient hammer when the morphism is closed-image.

- **Project's current path**: the lemma takes the function-field iso as
  a hypothesis (`Nonempty (C'.left.functionField ≃+* C.left.functionField)`)
  and outputs `Nonempty (C ≅ C')`. The lemma body is `sorry` and the
  docstring (L342-352) lays out two routes: (a) the coherent-sheaf
  argument (`φ_* O_C` is a coherent `O_{C'}`-module of generic rank 1,
  inclusion `O_{C'} ↪ φ_* O_C` is an iso of rank-1 torsion-free sheaves
  on a Dedekind base), (b) the equivalence-of-categories argument
  (smooth proj curves ≃ function fields).

- **Gap**: divergent-and-isolated. Mathlib does not package
  "birational ⟹ iso for smooth proper curves" as a named lemma. The
  closest is `instIsIsoToNormalizationOfIsIntegralHom`, but it proves
  iso of the normalisation map, not of the original morphism. The
  bridge from there to Pin 3 is non-trivial:
  - Show `φ : C ⟶ C'` is finite (proper + locally-finite-type +
    quasi-finite via the degree-1 hypothesis collapsed at the generic
    point; alternatively, finite-on-each-affine-chart via integral
    closure). Mathlib has `IsFinite.iff_isProper_and_isAffineHom`, so
    once affine-hom is established, finiteness follows.
  - Show `Scheme.Hom.normalization φ = C` (i.e. the normalisation of
    `φ` is `C` itself, since `C` is normal/smooth). Then
    `Scheme.Hom.toNormalization φ : C ⟶ normalization φ` is an iso,
    and `fromNormalization : normalization φ ⟶ C'` is the integral
    closure inclusion `O_{C'} ↪ O_C` viewed as a morphism of schemes.
  - Under the degree-1 hypothesis (function-field iso), the integral
    closure `O_{C'} ↪ O_C` becomes the identity, so `fromNormalization`
    is an iso (and `φ = toNormalization ≫ fromNormalization` is then
    a composition of isos).

- **Cost of divergence**: medium. The Mathlib normalisation lemma
  exists but the bridging argument (identify the normalisation of `φ`
  with `C` via smoothness; show the degree-1 hypothesis collapses the
  integral closure to identity) is ~80-150 LOC of new project
  infrastructure.

- **Verdict**: **PROCEED** (with `instIsIsoToNormalizationOfIsIntegralHom`
  + `IsFinite.iff_isProper_and_isAffineHom` as a candidate body
  strategy; a coherent-rank-1 sheaf strategy is the alternative,
  arguably cleaner but requires more sheaf-cohomology API the project
  has not exposed). Final route choice is iter-178+ planner's call.

### Decision 2: signature shape — function-field iso hypothesis

- **Mathlib idiom**: when stating "morphism induces iso on function
  fields", Mathlib's convention is to state things in terms of
  `Scheme.functionField` as a `CommRingCat` (it's the *literal* field
  at the generic point, not a `Field` type-synonym). The induced
  function-field map for a `φ : X ⟶ Y` of integral schemes would be the
  composite
  `Y.functionField → Y.presheaf.stalk (φ.base ξ_X) →[stalkMap]→
   X.presheaf.stalk ξ_X → X.functionField`
  using `germToFunctionField` + `IsFractionRing.lift`. There is no
  named `Scheme.Hom.functionFieldMap` in Mathlib — this is a small
  derived definition the project would write inline.

- **Project's current path**: the lemma takes an *abstract* ring iso
  `Nonempty (C'.left.functionField ≃+* C.left.functionField)` as a
  hypothesis, NOT specifically the iso induced by `φ`. This is a
  deliberate weakening (per the docstring L334-341): "the existence
  wrapper matches the file-skeleton's substantive-but-non-tautological-
  type discipline without committing prematurely to a specific Mathlib
  formulation of the canonical function-field map."

- **Gap**: divergent-with-cost (mild). The hypothesis is *strictly
  weaker* than needed for the iter-178+ body to extract a useful
  birational map: any ring iso `K(C') ≃+* K(C)` will do, but the
  birational-extension argument needs the iso induced by `φ` itself.
  Concretely, the existence hypothesis tells you nothing about how
  the abstract field iso relates to `φ`'s action on the generic point.

- **Cost of divergence**: medium. The iter-178+ body will need to
  *strengthen* the hypothesis (or replace it with a non-constancy +
  degree-from-field-extension formulation) before the
  normalisation-based argument can proceed.

- **Verdict**: **DIVERGE_INTENTIONALLY**, but flag for re-statement
  during iter-178+ body work. The current existence hypothesis is a
  file-skeleton placeholder; the planner should anticipate refining
  it to either (a) "`φ` induces a function-field iso" (using the
  canonical stalk-map-at-generic-point construction inline), or
  (b) "`φ` has function-field-extension degree 1"
  (`Module.finrank C'.functionField C.functionField = 1`).

## Recommendation

Both decisions land **PROCEED**: Mathlib has no
"birational ⟹ iso for smooth proper curves" theorem, no `IsBirational`,
no Zariski's main theorem wrapper at the curve level. The project's
in-tree route is the correct call.

For the iter-178+ body, the planner should:

1. Plan to **refine the hypothesis** of `iso_of_degree_one` from
   "abstract function-field iso" to "function-field map induced by
   `φ` is iso" — this is needed to make the birational argument go
   through. Either by adding a wrapper `Scheme.Hom.functionFieldMap`
   (8-15 LOC: composite of stalkMap-at-generic-point and
   IsFractionRing.lift) or by replacing the existence hypothesis
   with `Module.finrank C'.functionField C.functionField = 1`.
2. Plan the body via the **normalisation route**:
   - Reduce to `φ` finite (proper + quasi-finite ⟹ finite via
     `IsFinite.iff_isProper_and_isAffineHom`; quasi-finiteness comes
     from the degree-1 hypothesis collapsing each fibre).
   - Use `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom` to get
     `Scheme.Hom.toNormalization φ : C ⟶ normalization φ` is an iso.
   - Identify `normalization φ = C'` via smoothness of `C'` (smooth
     proper curve over algebraically closed field ⟹ regular ⟹
     normal). The integral closure `O_{C'} ↪ φ_* O_C` is then an
     equality under the degree-1 hypothesis.
   - Compose to extract `C ≅ C'`.

Budget: ~80-150 LOC for the body, of which ~30-50 LOC is the
"normalisation of `φ` = C' under smooth/normal" bridge.

Alternative route (sheaf-cohomology): show `O_{C'} ↪ φ_* O_C` is iso
of coherent rank-1 torsion-free sheaves on a smooth proper Dedekind
base. Cleaner conceptually but requires more sheaf API the project has
not exposed.

## Possible Mathlib gap-fill (informational, not blocking)

For a future upstream PR, the following would close the gap in Mathlib:

- `AlgebraicGeometry.Scheme.Hom.functionFieldMap : (f : X ⟶ Y)
  [IsIntegral X] [IsIntegral Y] [IsDominant f] :
  Y.functionField →+* X.functionField`.
- `AlgebraicGeometry.Scheme.IsBirational : (f : X ⟶ Y) → Prop` and the
  theorem "smooth + proper + integral + birational ⟹ iso" (Hartshorne
  III.11.4 / Stacks 0AVX).
- `AlgebraicGeometry.Scheme.Hom.isIso_of_finrank_functionField_one`:
  a degree-1 finite morphism of integral schemes is iso.

The project must not block on any of these — the in-tree route is the
correct call for iter-181/182.
