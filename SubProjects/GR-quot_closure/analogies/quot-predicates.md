# Analogy: QUOT predicate shapes — Mathlib idiom alignment

## Mode
api-alignment

## Slug
quot-predicates

## Iteration
004

## Question
For the two project-side predicates needed by the Quot functor and Grassmannian
foundations — (1) "coherent sheaf with schematic support proper over the base" and
(2) "rank-`d` locally free `SheafOfModules`" — determine for each whether Mathlib
already supplies it, the recommended Mathlib-aligned Lean shape, the exact Mathlib
declarations to build on, and the cost of a parallel choice.

## Project artifact(s)
- `blueprint/src/chapters/Picard_QuotScheme.tex` `def:quot_functor` (L422-494) — the
  Quot functor classifies `T`-flat coherent quotients `q : E_T ↠ F` whose **schematic
  support is proper over `T`**; `def:grassmannian_scheme` (L504-564) classifies rank-`d`
  **locally free** quotients; `Grass(V,d)` is *defined* as `Quot^{d,O_S}_{V/S/S}`.
- `AlgebraicJacobian/Picard/QuotScheme.lean` — `hilbertPolynomial`, `QuotFunctor`,
  `Grassmannian`, `Grassmannian.representable` are all typed `sorry` skeletons keyed on
  `X.Modules = SheafOfModules X.ringCatSheaf`; "coherent" is meant to be encoded as
  `[F.IsQuasicoherent]` + `[F.IsFiniteType]` (per `thm:generic_flatness`), but the
  proper-support and rank-`d`-local-freeness conditions are not yet expressed.

## Decisions identified

### Decision 1a: How to express "schematic support of a `Scheme.Modules` object"

- **Mathlib idiom**: Mathlib has the *target* closed-subscheme-of-vanishing machinery but
  NOT the support of a sheaf of modules.
  - `AlgebraicGeometry.Scheme.IdealSheafData` — structure of ideal sheaves
    (`Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:65`).
  - `AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals (I : ∀ U : X.affineOpens, Ideal Γ(X,U))`
    (`…/IdealSheaf/Basic.lean:104`) — builds an ideal sheaf from an affine-local ideal
    assignment.
  - `AlgebraicGeometry.Scheme.Hom.ker (f : X ⟶ Y) : IdealSheafData Y`
    (`…/IdealSheaf/Basic.lean:689`), defined `ofIdeals fun U ↦ RingHom.ker (f.app U).hom`
    — the **exact template** for an annihilator ideal sheaf.
  - `AlgebraicGeometry.Scheme.IdealSheafData.subscheme : Scheme`
    (`…/IdealSheaf/Subscheme.lean:452`) and
    `…IdealSheafData.subschemeι : I.subscheme ⟶ X` (`…/Subscheme.lean:472`); the inclusion
    is `IsPreimmersion` + `QuasiCompact` (`…/Subscheme.lean:484,488`), i.e. a closed
    immersion onto `I.support`.
  - `AlgebraicGeometry.Scheme.IdealSheafData.support : Closeds X`
    (`…/IdealSheaf/Basic.lean:327`); `range_subschemeι : Set.range I.subschemeι = I.support`
    (`…/Subscheme.lean:493`).
  - `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal (Z : Closeds X) : IdealSheafData X`
    (`…/IdealSheaf/Basic.lean:563`) — the reduced induced structure on a closed set.
  - Ring-level support primitives that the affine-local assignment is built from:
    `Module.annihilator R M` (`Mathlib/RingTheory/Ideal/Colon.lean`, used throughout) and
    `Module.support R M : Set (PrimeSpectrum R)` (`Mathlib/RingTheory/Support.lean`).
  - **Absent**: any `support`/`annihilatorIdealSheaf` for `SheafOfModules` /
    `Scheme.Modules`. A whole-tree grep for a sheaf-level module support returns nothing;
    the only `support` in `AlgebraicGeometry` is `IdealSheafData.support` and `Hom.support_ker`.
- **Project's current path**: not yet expressed (the `.lean` skeleton drops the condition).
- **Gap**: divergent-and-wrong if hand-rolled as a bare `Set`/topological-only support, or
  as `Unit`; the schematic-support primitive itself is genuinely **missing upstream**.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL for the support primitive — build
  `Scheme.Modules.annihilator : X.Modules → X.IdealSheafData` by mirroring `Hom.ker`
  (`ofIdeals fun U ↦ Module.annihilator _ (Γ(F,U) as a Γ(X,U)-module)`), then
  `schematicSupport F := (F.annihilator).subscheme` with closed immersion
  `(F.annihilator).subschemeι`.

### Decision 1b: How to express "support proper over `S`"

- **Mathlib idiom**: `AlgebraicGeometry.IsProper`
  (`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:42`), a `MorphismProperty Scheme`
  `@[mk_iff] class IsProper extends IsSeparated, UniversallyClosed, LocallyOfFiniteType`,
  equal to `(@IsSeparated ⊓ @UniversallyClosed) ⊓ @LocallyOfFiniteType` (`isProper_eq`).
  It already carries `RespectsIso`, `IsStableUnderComposition`, `IsMultiplicative`,
  **`IsStableUnderBaseChange`** (`Proper.lean:68`) and `IsZariskiLocalAtTarget` instances.
- **Project's current path**: directive proposes phrasing it via `MorphismProperty IsProper`
  applied to `support ↪ X → S` — this is correct.
- **Gap**: identical to the idiom (use `IsProper`); the only project work is *which*
  morphism to feed it.
- **Verdict**: ALIGN_WITH_MATHLIB — the predicate is
  `def Scheme.Modules.HasProperSupport (f : X ⟶ S) (F : X.Modules) : Prop :=`
  `IsProper ((F.annihilator).subschemeι ≫ f)`. Do NOT re-derive a bespoke
  "universally-closed + separated + finite-type support" bundle; reuse `IsProper` so the
  base-change instance (`IsProper.isStableUnderBaseChange`) discharges Nitsure's
  "properness preserved by base change" needed for the Quot functor's pullback action.

### Decision 2: Shape of "rank-`d` locally free `SheafOfModules`"

- **Directive premise correction**: the note "`IsLocallyFree` is upstream-only /
  rank-agnostic at the pin" is **inaccurate**. A whole-Mathlib grep for
  `IsLocallyFree|isLocallyFree|LocallyFree` returns **zero** hits. There is no
  rank-agnostic sheaf-level local-freeness to extend — the predicate is fully absent at
  the `SheafOfModules` level.
- **Mathlib idiom (object predicates on `SheafOfModules`)**: all witnessed by `Nonempty`/`∃`
  of *local data*, as `Prop` classes, each also exposing an `ObjectProperty` abbrev:
  - `SheafOfModules.IsQuasicoherent (M) : Prop` :=
    `Nonempty (QuasicoherentData M)` (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:249`).
  - `SheafOfModules.IsFiniteType (M) : Prop` :=
    `∃ σ : M.LocalGeneratorsData, σ.IsFiniteType` (`…/Sheaf/Generators.lean:130`).
  - `SheafOfModules.IsFinitePresentation (M) : Prop` :=
    `∃ σ : QuasicoherentData M, σ.IsFinitePresentation` (`…/Sheaf/Quasicoherent.lean:262`).
  - Free model: `SheafOfModules.free (I : Type u) : SheafOfModules R := ∐ (fun _ : I ↦ unit R)`
    and `SheafOfModules.freeFunctor`, with `mapFree`/`freeHomEquiv` for pullback of free
    sheaves (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean`).
- **Ring-level constant-rank idiom (closest verbatim)**: there is NO bundled
  `Module.IsFiniteLocallyFree`/`LocallyFreeOfRank`. "Finite locally free" = `Module.Finite`
  + `Module.Projective` (equiv. `Module.FinitePresentation` + `Module.Flat`); the free locus
  is `Module.freeLocus R M : Set (PrimeSpectrum R)` with
  `freeLocus_eq_univ_iff : freeLocus = univ ↔ Projective` (FinitePresentation), and constant
  rank is `Module.rankAtStalk M : PrimeSpectrum R → ℕ`
  (`Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean:186`) being a constant function
  (`isLocallyConstant_rankAtStalk` for finite-presentation + flat). I.e. "rank `d`" =
  `Module.rankAtStalk M = fun _ ↦ d`, NOT a packaged predicate.
- **Project's current path**: not yet expressed.
- **Gap**: divergent-and-wrong if built as a parallel `IsLocallyFree` + a fabricated
  sheaf-level `rankAtStalk = d` conjunction (the sheaf-level `rankAtStalk` also does not
  exist, so that route doubles the gap-fill).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL, but the *shape* is dictated by the existing idiom.
  Define a single `Prop` class
  `SheafOfModules.IsLocallyFreeOfRank (M : SheafOfModules R) (r : ℕ) : Prop`
  (or on `X.Modules`) witnessed by the existence of local data — an open cover on which `M`
  restricts to `free (Fin r)` — exactly paralleling `IsQuasicoherent`/`IsFinitePresentation`'s
  `Nonempty (local data)` shape and building on `SheafOfModules.free`. The rank is a
  parameter carried by the local model `free (Fin r)`, NOT a separate rank field; if the
  iso data is needed downstream, split it `…Data` (data) / `Is…` (Prop) as Mathlib does for
  `QuasicoherentData`/`IsQuasicoherent`. Expose `isLocallyFreeOfRank r : ObjectProperty …`
  for consistency.

## Recommendation

Both predicates are genuinely absent upstream, but neither is a free-form invention: each
must be assembled from existing Mathlib primitives along the established idiom.

Predicate 1 = two layers. (i) **Support primitive** (gap-fill): mirror
`AlgebraicGeometry.Scheme.Hom.ker`'s `IdealSheafData.ofIdeals fun U ↦ RingHom.ker …`
construction to define `Scheme.Modules.annihilator : X.Modules → X.IdealSheafData`
(`ofIdeals fun U ↦ Module.annihilator …`), giving `schematicSupport F := (F.annihilator).subscheme`
with the canonical closed immersion `(F.annihilator).subschemeι`. (ii) **Proper-over-S layer**
(align): `HasProperSupport f F := IsProper ((F.annihilator).subschemeι ≫ f)`, reusing
`AlgebraicGeometry.IsProper` so `IsStableUnderBaseChange` discharges the base-change clause
the Quot functor's functoriality requires.

Predicate 2: a single `Prop` class `IsLocallyFreeOfRank M r`, witnessed by `Nonempty` of
local-trivialization data against `SheafOfModules.free (Fin r)`, copying the
`IsQuasicoherent`/`IsFinitePresentation` pattern verbatim and reusing
`SheafOfModules.free`/`freeFunctor`/`mapFree`. Do not introduce a separate rank-agnostic
`IsLocallyFree` plus a sheaf-`rankAtStalk` conjunction (both would be new, and the param-on-
`free (Fin r)` form is the idiom).

**Cost of a parallel choice.** Predicate 1: a bespoke set-only support loses the
closed-immersion instances (`subschemeι` is `IsPreimmersion`+`QuasiCompact` for free), the
`IdealSheafData.comap`/`comapIso` functoriality the Quot pullback action needs, and the
`IsProper` base-change instance — forcing hand-proved bridge lemmas for every base change in
the Quot functor. Predicate 2: a local-freeness not phrased through `free`/`freeFunctor`
cannot consume `mapFree`/`freeHomEquiv` for pulling back the tautological quotient, and —
because the blueprint *defines* `Grass(V,d) = Quot^{d,O_S}_{V/S/S}` — a parallel rank-`d`
predicate forces a bridge lemma `IsLocallyFreeOfRank d ↔ (flat ∧ properSupport ∧ hilbertPoly = d)`
on `X = S` to reconcile the Grassmannian's two descriptions.
