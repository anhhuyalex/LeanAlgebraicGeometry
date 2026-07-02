/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Albanese.CodimOneExtension

/-!
# Milne Theorem 3.2: a rational map from a nonsingular variety to an abelian
variety extends (A.4.c)

This file is the **A.4.c** file-skeleton sub-build chapter for the project's
positive-genus arm of `nonempty_jacobianWitness`. It packages the single
theorem of Milne's *Abelian Varieties* §I.3, Theorem 3.2:
**a rational map from a nonsingular variety to an abelian variety extends,
uniquely, to a regular morphism**. This is the input that the Albanese
universal-property build (A.4.d, `Albanese/AlbaneseUP.lean`) consumes when
promoting the symmetric-product rational map
`C^{(g)} ⇢ A` to a regular morphism `J → A`.

Milne's proof is two lines: combine Theorem 3.1 (the codim-$\geq 2$ extension
result for rational maps from a normal variety to a complete variety —
project-side `thm:codim_one_extension` of
`Albanese/CodimOneExtension.lean`, A.4.a) with Lemma 3.3 (the
pure-codim-$1$ indeterminacy structure for rational maps into a group variety
— project-side `lem:milne_codim1_indeterminacy` of the same chapter). The
combination forces the indeterminacy locus of `f` to be simultaneously of
codimension `≥ 2` and pure codimension `1`, hence empty, so `f` is everywhere
defined.

## Status (iter-175 Lane J file-skeleton)

This file is the **iter-175 Lane J** file-skeleton: the single pinned
declaration carries the intended substantive type signature (matching the
blueprint `\lean{...}` pin in
`chapters/Albanese_Thm32RationalMapExtension.tex` line 50) with a `sorry`
body. The body is iter-176+ work, gated on the sibling chapters
`Albanese/CodimOneExtension.lean` (A.4.a) and
`Albanese/AuslanderBuchsbaum.lean` (A.4.b) landing their substantive
statements.

The 1 pinned declaration is:

1. `AlgebraicGeometry.Scheme.RationalMap.extend_to_av` (theorem, ~10 LOC)
   — Milne Theorem 3.2: for `X` a smooth (= nonsingular) variety over an
   algebraically closed field `k̄`, `A` an abelian variety over `k̄`, and
   `f : X ⇢ A` a rational map, there exists a *unique* regular morphism
   `g : X ⟶ A` whose induced rational map equals `f`.

## Note on type expressivity

The signature is encoded against Mathlib's existing
`AlgebraicGeometry.Scheme.RationalMap` (a partial-map equivalence class on
dense opens) and `Scheme.Hom.toRationalMap` (the canonical "regular morphism
yields a rational map" coercion). The substantive claim is the existence
and uniqueness of a `g : X.left ⟶ A.left` with `g.toRationalMap = f`. The
type is non-tautological: the existence is the content of Milne 3.2;
uniqueness is the standard reduced-and-separated agreement principle
(`AlgebraicGeometry.ext_of_isDominant`).

## Abelian-variety conventions

Throughout the project (cf. `AbelianVarietyRigidity.lean`, `Jacobian.lean`),
an **abelian variety over `k̄`** is encoded as an object
`A : Over (Spec (.of k̄))` carrying the four instances:

- `[GrpObj A]` (group-object structure on the over-category),
- `[IsProper A.hom]` (complete),
- `[Smooth A.hom]` (nonsingular),
- `[GeometricallyIrreducible A.hom]` (geometrically irreducible).

A **nonsingular variety over `k̄`** (in the convention of
`blueprint/src/chapters/Albanese_Thm32RationalMapExtension.tex` §1) is an
object `X : Over (Spec (.of k̄))` carrying:

- `[Smooth X.hom]`,
- `[GeometricallyIrreducible X.hom]`,
- `[IsSeparated X.hom]`,
- `[LocallyOfFiniteType X.hom]`,
- `[IsIntegral X.left]`,
- `[IsReduced X.left]`.

These four-plus-two instances will normally be supplied by `inferInstance` at
the call site.

## References

Blueprint: `blueprint/src/chapters/Albanese_Thm32RationalMapExtension.tex`
(250 LOC, 1 pin). Source: Milne, *Abelian Varieties*, §I.3, Theorem 3.2,
p. 17 (`references/abelian-varieties.pdf`, PDF page 23).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

namespace RationalMap

/-! ## Milne Theorem 3.2 — rational maps to an abelian variety extend

Let `k̄` be an algebraically closed field. Let `X` be a nonsingular variety
over `k̄` (smooth, geometrically irreducible, separated, locally of finite
type, integral, reduced). Let `A` be an abelian variety over `k̄`
(a group object that is proper, smooth, and geometrically irreducible). For
every rational map `f : X ⇢ A` there is a *unique* regular morphism
`g : X ⟶ A` whose induced rational map equals `f`.

Milne's argument (`Albanese_Thm32RationalMapExtension.tex` §1.4, Theorem 3.2):
let `U ⊆ X` be a maximal open of definition of `f` and `Z := X ∖ U`.
By the codim-$\geq 2$ extension theorem (Theorem 3.1, project-side
`thm:codim_one_extension`) the closed subset `Z` has codimension `≥ 2`.
By the pure-codim-$1$ indeterminacy lemma for maps into a group variety
(Lemma 3.3, project-side `lem:milne_codim1_indeterminacy`), `Z` is either
empty or of pure codimension `1`. Both conditions force `Z = ∅`, so `U = X`
and `f` admits a regular representative on all of `X`. Uniqueness is the
standard reduced-and-separated agreement principle (cf.
`AlgebraicGeometry.ext_of_isDominant`): two regular morphisms `X ⟶ A` that
agree on a dense open of `X` agree everywhere.

Blueprint reference: `thm:rational_map_to_av_extends` (Milne, *Abelian
Varieties*, Theorem 3.2, §I.3, p. 17). The pin in the chapter is at
`Albanese_Thm32RationalMapExtension.tex` line 50.

iter-176+ proof skeleton:
1. Pick a `PartialMap` representative `φ : X.PartialMap A` of `f` (using
   `Scheme.RationalMap.toPartialMap`, which exists for `X` reduced and `A`
   separated; both hold from the abelian-variety + variety instances).
2. Show `φ.domain = ⊤` by combining `thm:codim_one_extension` (codim `≥ 2`
   complement) with `lem:milne_codim1_indeterminacy` (complement empty or
   pure codim `1`).
3. Read off `g := φ.hom` (the morphism on the full domain) and verify
   `g.toRationalMap = f`.
4. Uniqueness: two `g₁, g₂ : X ⟶ A` with `g₁.toRationalMap = g₂.toRationalMap`
   agree on a dense open of `X`, so by
   `AlgebraicGeometry.ext_of_isDominant` and reducedness of `X` they agree
   everywhere. -/

/-- **A scheme smooth over an algebraically closed field is reduced**
(Stacks `056S`/`033B` over `k̄`). Used to derive `IsReduced A.left` in
`av_isIntegral_of_smooth_geomIrred` below.

**CLOSED (run 0002, T3 session 0021)** — no longer a typed sorry. The former
Mathlib gap is discharged by the project-side
`isReduced_of_smooth_of_isAlgClosed` in `Albanese/CodimOneExtension.lean`
(§3.B Step B.e): stalks are localisations of standard-smooth `k̄`-algebras,
whose maximal-ideal localisations are regular local (Step B.d′) hence domains
(`RingTheory.CohenMacaulay.isDomain_of_regularLocal`, Stacks `00NP` in
`AuslanderBuchsbaum.lean`), and reducedness is checked at maximal
localisations then transported to stalks and glued. The hypothesis is
accordingly strengthened from `[Field kbar]` to `[Field kbar] [IsAlgClosed
kbar]` (its unique consumer `av_isIntegral_of_smooth_geomIrred` already
assumes algebraic closure). Axiom-clean. -/
private theorem isReduced_of_smooth_over_field
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (A : Over (Spec (.of kbar)))
    [Smooth A.hom] :
    IsReduced A.left :=
  isReduced_of_smooth_of_isAlgClosed A

/-- **Iter-180 Lane G split (1/2): integrality of the abelian variety.**

For an abelian variety `A` over an algebraically closed field `k̄` —
encoded in the project as `A : Over (Spec (.of k̄))` carrying
`[GrpObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIrreducible A.hom]` —
the underlying scheme `A.left` is integral.

**Derivation.** The proof has three steps:

1. `Spec k̄` is a singleton scheme (Mathlib instance
   `Scheme.instUniqueCarrierCarrierCommRingCatSpecOf` provides `Unique`,
   which yields both `Subsingleton` and `Nonempty`).
2. `GeometricallyIrreducible A.hom + Spec k̄ a single point ⟹ IrreducibleSpace A.left`
   via Mathlib's `GeometricallyIrreducible.irreducibleSpace_of_subsingleton`.
3. `IrreducibleSpace + IsReduced ⟹ IsIntegral` via Mathlib's
   `isIntegral_of_irreducibleSpace_of_isReduced`.

The implication `Smooth A.hom ⟹ IsReduced A.left` — formerly the substantive
Mathlib gap of this helper — is now supplied project-side by
`isReduced_of_smooth_over_field` (backed by
`isReduced_of_smooth_of_isAlgClosed` in `Albanese/CodimOneExtension.lean`),
so this helper is **axiom-clean** as of run 0002, T3 session 0021.

This is the iter-180 Lane G refactor of the iter-179 helper
`av_isIntegral_and_codimOneFree`, splitting its `IsIntegral A.left`
conjunct into a self-contained named lemma that does not depend on the
rational map `f`. -/
private theorem av_isIntegral_of_smooth_geomIrred
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    (A : Over (Spec (.of kbar)))
    [GrpObj A] [IsProper A.hom] [Smooth A.hom]
    [GeometricallyIrreducible A.hom] :
    IsIntegral A.left := by
  -- Step 1: `Spec k̄` has a unique point (Mathlib instance
  -- `Scheme.instUniqueCarrierCarrierCommRingCatSpecOf`); both
  -- `Subsingleton` and `Nonempty` follow.
  haveI : Subsingleton (Spec (.of kbar) : Scheme.{u}) := inferInstance
  haveI : Nonempty (Spec (.of kbar) : Scheme.{u}) := inferInstance
  -- Step 2: geometric irreducibility over a singleton base gives `IrreducibleSpace`.
  haveI : IrreducibleSpace A.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.hom
  -- Step 3: smoothness over the algebraically closed base field forces
  -- reducedness of the source (`isReduced_of_smooth_over_field`, closed in
  -- run 0002 session 0021 via `isReduced_of_smooth_of_isAlgClosed`).
  haveI : IsReduced A.left := isReduced_of_smooth_over_field A
  exact isIntegral_of_irreducibleSpace_of_isReduced A.left

/-- **Iter-180 Lane G split (2/2): codim-1-indeterminacy-freeness from
Milne's two-input argument.**

For a rational map `f : X ⇢ A` from a nonsingular variety `X` to an
abelian variety `A` over an algebraically closed field `k̄`, every
codim-1 point of `X` lies in `f.domain` (`CodimOneFree f`).

**Derivation (Milne, *Abelian Varieties*, proof of Theorem 3.2, §I.3, p. 17).**
Two project-side inputs combine to force the indeterminacy locus empty:

1. `indeterminacy_pure_codim_one_into_grpScheme` (Milne Lemma 3.3 in
   `Albanese/CodimOneExtension.lean`): for a rational map from a smooth
   integral variety to a *group* variety, the indeterminacy locus is
   either empty or pure codim 1.
2. The *codim-≥2 conclusion* of Milne Theorem 3.1 (the unbundled half of
   `extend_of_codimOneFree_of_smooth` in `Albanese/CodimOneExtension.lean`):
   for a rational map from a nonsingular variety to a complete variety,
   the indeterminacy locus has codim `≥ 2`.

Combining (1) ∨ (2): pure codim 1 contradicts codim `≥ 2`, so the
indeterminacy locus is empty; trivially every point — and in particular
every codim-1 point — lies in `f.domain`, so `CodimOneFree f`.

**Status (run-0006 T6, second session).** The codim-≥2 conclusion of Milne
3.1 is the standalone lemma `indeterminacy_codimGe2_of_smooth_of_complete`
in `Albanese/CodimOneExtension.lean`, now **proved axiom-clean** (valuative
criterion of properness at the DVR stalk + Mathlib rational-map
spreading-out). It requires `f` to be a rational map *over `k̄`*
(hypothesis `hover`, Milne's ambient assumption), which this helper and its
consumers thread through. This helper's body is `sorry`-free: branch 2
derives the contradiction `2 ≤ coheight x = 1` directly from that lemma;
the remaining gap of this chain is Milne Lemma 3.3
(`indeterminacy_pure_codim_one_into_grpScheme`).

This is the iter-180 Lane G refactor's split: the `CodimOneFree f`
conjunct is split off into a self-contained named lemma with the
substantive missing content localised here. -/
private theorem av_codimOneFree_of_indeterminacy
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom]
    [GeometricallyIrreducible A.hom]
    (f : X.left.RationalMap A.left)
    (hover : f.compHom A.hom = X.hom.toRationalMap) :
    CodimOneFree f := by
  -- **Iter-182 structural refactor.** Materialise the variety-package
  -- instances on `A.left` needed by Milne Lemma 3.3
  -- (`indeterminacy_pure_codim_one_into_grpScheme`): `IsIntegral` from the
  -- split helper `av_isIntegral_of_smooth_geomIrred`; `IsReduced` from
  -- `isReduced_of_isIntegral`; `IsSeparated` from `IsProper`;
  -- `LocallyOfFiniteType` from `Smooth`.
  haveI : IsIntegral A.left := av_isIntegral_of_smooth_geomIrred A
  haveI : IsReduced A.left := inferInstance
  haveI : IsSeparated A.hom := inferInstance
  haveI : LocallyOfFiniteType A.hom := inferInstance
  -- Apply Milne Lemma 3.3: the indeterminacy locus is empty or every point
  -- of it lies in the closure of a codim-1 generic point.
  have hdisj := indeterminacy_pure_codim_one_into_grpScheme f hover
  intro x hx
  rcases hdisj with hempty | hpure
  · -- **Branch 1 (CLOSED).** Empty indeterminacy locus: every point of `X`
    -- — in particular `x` — lies in `f.domain` (no codim-1 obstruction).
    by_contra hnotin
    have hxZ : x ∈ indeterminacyLocus f := hnotin
    rw [hempty] at hxZ
    exact hxZ.elim
  · -- **Branch 2 (CLOSED, run-0006 T6).** The codim-≥2 conclusion of
    -- Milne 3.1 (`indeterminacy_codimGe2_of_smooth_of_complete`, the
    -- unbundled Step-1 half of `extend_of_codimOneFree_of_smooth`, now
    -- exposed as a standalone lemma in `Albanese/CodimOneExtension.lean`)
    -- contradicts `coheight x = 1` for a codim-1 point of the indeterminacy
    -- locus, so `x ∈ f.domain`. (The pure-codim-1 disjunct of Milne 3.3 is
    -- not needed once the codim-≥2 conclusion is available.)
    by_contra hnotin
    have h2 := indeterminacy_codimGe2_of_smooth_of_complete f hover x hnotin
    rw [hx] at h2
    norm_num at h2

/-- **Iter-182 documentation helper: branch-1 of `av_codimOneFree_of_indeterminacy`.**
The empty-indeterminacy branch of Milne Lemma 3.3 closes `CodimOneFree`
without depending on the codim-≥2 conclusion of Milne 3.1. Exposed as a
standalone lemma so the structural split survives any future refactor of
the parent helper. Axiom-clean. -/
private theorem codimOneFree_of_indeterminacyLocus_eq_empty
    {X Y : Scheme.{u}} {f : X.RationalMap Y}
    (h : indeterminacyLocus f = ∅) : CodimOneFree f := by
  intro x _
  by_contra hnotin
  have hxZ : x ∈ indeterminacyLocus f := hnotin
  rw [h] at hxZ
  exact hxZ.elim

/-- **Iter-179 Lane E + iter-180 Lane G: the two missing project inputs
for `extend_to_av`.**

The conjunction of the two named iter-180 Lane G splits:
`av_isIntegral_of_smooth_geomIrred` (the `IsIntegral A.left` conjunct, with
its former `IsReduced A.left` Mathlib gap now closed axiom-clean) and
`av_codimOneFree_of_indeterminacy` (the `CodimOneFree f` conjunct, with its
codim-≥2-from-Milne-3.1 gap isolated).

This wrapper preserves the iter-179 call-site API (`extend_to_av` invokes
the conjunction in one `obtain`) while routing the proof to the two
narrower lemmas. The body itself is axiom-clean — all substantive content
is localised in the two split helpers above. -/
private theorem av_isIntegral_and_codimOneFree
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom]
    [GeometricallyIrreducible A.hom]
    (f : X.left.RationalMap A.left)
    (hover : f.compHom A.hom = X.hom.toRationalMap) :
    IsIntegral A.left ∧ CodimOneFree f :=
  ⟨av_isIntegral_of_smooth_geomIrred A,
    av_codimOneFree_of_indeterminacy f hover⟩

/-- **Milne Theorem 3.2 — a rational map from a nonsingular variety to an
abelian variety extends, uniquely, to a regular morphism.**

For `X` a nonsingular variety over an algebraically closed field `k̄`, and
`A` an abelian variety over `k̄`, every rational map `f : X ⇢ A` has a
*unique* regular extension `g : X ⟶ A` (i.e. `g.toRationalMap = f`).

This is the input the Albanese universal-property build
(`Albanese/AlbaneseUP.lean`, A.4.d) consumes when promoting the
symmetric-product rational map `C^{(g)} ⇢ A` to a regular morphism
`J → A`.

**Iter-179 Lane E body.** The proof is the standard one-line reduction of
Milne's two-line argument:

1. Apply `extend_of_codimOneFree_of_smooth` (Milne Theorem 3.1, project-side
   `thm:codim_one_extension` in `Albanese/CodimOneExtension.lean`): given a
   `CodimOneFree` rational map from a smooth integral variety to a complete
   variety, the map extends uniquely to a regular morphism. This requires
   the variety-package instances on `A.left` (separated, locally of finite
   type, integral, reduced) in addition to the four AV instances supplied
   by the caller.

2. Discharge `CodimOneFree f` by invoking the helper
   `av_isIntegral_and_codimOneFree`, which combines
   `indeterminacy_pure_codim_one_into_grpScheme` (Milne Lemma 3.3 — pure
   codim 1 or empty indeterminacy for grpScheme targets) with the codim-≥2
   half of Milne 3.1 (`indeterminacy_codimGe2_of_smooth_of_complete`,
   proved axiom-clean in `Albanese/CodimOneExtension.lean`; the remaining
   math content of this chain is Milne Lemma 3.3).

3. Materialize the remaining variety-package instances on `A.left`:
   `IsSeparated A.hom` from `IsProper A.hom` (Mathlib instance),
   `LocallyOfFiniteType A.hom` from `Smooth A.hom` (Mathlib instance),
   `IsReduced A.left` from `IsIntegral A.left` (Mathlib instance
   `isReduced_of_isIntegral`).

The proof body therefore introduces NO new inline `sorry`: all missing
content is concentrated in the single named helper above. -/
theorem extend_to_av
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {X : Over (Spec (.of kbar))}
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] [IsReduced X.left]
    {A : Over (Spec (.of kbar))}
    [GrpObj A] [IsProper A.hom] [Smooth A.hom]
    [GeometricallyIrreducible A.hom]
    (f : X.left.RationalMap A.left)
    (hover : f.compHom A.hom = X.hom.toRationalMap) :
    ∃! (g : X.left ⟶ A.left), g.toRationalMap = f := by
  -- Step 3: materialise the missing variety-package instances on A.left.
  haveI : IsSeparated A.hom := inferInstance
  haveI : LocallyOfFiniteType A.hom := inferInstance
  obtain ⟨hint, hcod⟩ := av_isIntegral_and_codimOneFree f hover
  haveI := hint
  haveI : IsReduced A.left := inferInstance
  -- Steps 1–2: apply Milne Theorem 3.1 with the `CodimOneFree` discharged.
  exact extend_of_codimOneFree_of_smooth f hover hcod

end RationalMap

end Scheme

end AlgebraicGeometry
