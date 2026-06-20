# Analogy: relativeDifferentialsPresheaf ↔ algebra-Kähler bridge — API shape

## Slug
relative-differentials-presheaf-bridge

## Iteration
121

## Question

How should the bridge between the presheaf-section module of
`AlgebraicGeometry.Scheme.relativeDifferentialsPresheaf` and the
appLE-algebra Kähler module `Ω[B/A]` on an affine chart be designed
in Lean? Three decisions: (1) statement shape (`LinearEquiv` vs
`ModuleCat.Iso` vs PresheafOfModules natural iso); (2) `IsLocalization`
packaging for `A → A_colim`; (3) cofinality argument packaging for
"directed colimit over `M`-localizations equals localization at `M`".

## Project artifact(s)

- `AlgebraicJacobian/Differentials.lean:49-52` —
  `relativeDifferentialsPresheaf` definition (presheaf-level pullback
  + `relativeDifferentials'`).
- `AlgebraicJacobian/Differentials.lean:58-64` —
  `relativeDifferentialsPresheaf_obj_kaehler` (`rfl` identification
  of sections with `CommRingCat.KaehlerDifferential` of the
  inverse-image-presheaf map).
- `AlgebraicJacobian/Differentials.lean:91-109` —
  `smooth_locally_free_omega` (algebra-Kähler form, closed iter-120).
- `blueprint/src/chapters/Differentials.tex § sec:bridge` — the new
  in-scope theorem block (Theorem
  `thm:relativeDifferentialsPresheaf_iso_kaehler_appLE`) with
  sub-lemmas `lem:appLE_isLocalization`,
  `lem:kaehler_localization_subsingleton`,
  `lem:kaehler_quotient_localization_iso`.

## Decisions identified

### Decision 1: Statement shape of the bridge — `LinearEquiv` (`≃ₗ[B]`), `ModuleCat.Iso`, or `PresheafOfModules` natural iso?

- **Mathlib idiom**: bridges of the shape "Kähler module of one
  algebra structure ↔ Kähler module of a related algebra structure"
  are packaged as **`LinearEquiv`** decorated with `@[simps! apply]`.
  The directly analogous Mathlib precedent is
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`
  (`Mathlib.RingTheory.Etale.Kaehler`,
  `.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean:37-46`):
  ```
  def KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      [Algebra.FormallyEtale S T] : T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]
  ```
  packaged as a `LinearEquiv` (with `@[simps! apply]`), proved via
  `LinearEquiv.ofBijective` against
  `KaehlerDifferential.mapBaseChange`. The associated `ModuleCat.Iso`
  form is freely derivable via `LinearEquiv.toModuleIso`
  (`Mathlib.Algebra.Category.ModuleCat.Basic:277`) and the explicit
  categorical equivalence
  `(X ≃ₗ[R] Y) ≅ (ModuleCat.of R X ≅ ModuleCat.of R Y)` at the same
  file:301.

  An adjacent `IsLocalizedModule`-instance form is also provided:
  `KaehlerDifferential.isLocalizedModule_map`
  (same file, line 63) is an `instance`, not a `LinearEquiv`,
  because it consumes via typeclass.
- **Project's path (proposed)**: `LinearEquiv`-form theorem
  `relativeDifferentialsPresheaf_iso_kaehler_appLE` (per the
  blueprint's Theorem
  `thm:relativeDifferentialsPresheaf_iso_kaehler_appLE`). The
  identifier suffix `_iso_` is slightly misleading (the value is a
  `LinearEquiv`, not an `Iso`) but the canonical shape `≃ₗ[B]` from
  the blueprint statement matches the Mathlib precedent.
- **Gap**: divergent-equivalent on naming (`_iso_` vs `_equiv_`);
  identical on shape if `LinearEquiv` is chosen.
- **Verdict**: **ALIGN_WITH_MATHLIB**. Package as
  `≃ₗ[B]` (LinearEquiv) with `@[simps]`. Optional: also expose a
  `ModuleCat.Iso` form as a tiny corollary
  (`relativeDifferentialsPresheaf_obj_isoKaehler := ... .toModuleIso`)
  if downstream consumers will want the categorical form; otherwise
  defer until needed.

  DO NOT package as a global `PresheafOfModules` natural iso this
  iter. The current downstream consumer `smooth_locally_free_omega`
  is pointwise (one chart at a time), and a global natural iso would
  add naturality-square work for no current value. If a future
  consumer (e.g. cotangent exact sequence of a composition) needs
  the global form, it can be lifted by composing the pointwise iso
  with the affine restriction maps — and even then the right Mathlib
  framing is a `PresheafOfModules.isoMk` from pointwise iso data.

  Suggested rename: `relativeDifferentialsPresheaf_equiv_kaehler_appLE`
  (matches Mathlib `tensorKaehlerEquivOfFormallyEtale` and
  `KaehlerDifferential.linearMapEquivDerivation` naming).

### Decision 2: `IsLocalization` packaging for `A → A_colim` — instance, predicate-on-existing-algebra, or `AlgEquiv`?

- **Mathlib idiom**: when a section ring of a presheaf carries a
  canonical algebra structure determined by parameters, Mathlib
  packages "section ring is a localization" as a **bare `theorem`**
  giving an `IsLocalization M T` predicate on the existing algebra
  structure, NOT as an `AlgEquiv L ≃ₐ[A] T` to a specific localization
  term. The directly analogous Mathlib precedent is
  `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`
  (`Mathlib.AlgebraicGeometry.AffineScheme`,
  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/AffineScheme.lean`,
  around line 640):
  ```
  theorem IsAffineOpen.isLocalization_basicOpen
      (hU : IsAffineOpen U) (f : Γ(X, U)) :
      IsLocalization.Away f Γ(X, X.basicOpen f)
  ```
  parameterised by `hU : IsAffineOpen U`. The companion
  `AlgebraicGeometry.isLocalization_away_of_isAffine`
  (`AffineScheme.lean:664`) is the same fact stated as an **instance**
  for the `[IsAffine X]` global case (no extra `IsAffineOpen U`
  hypothesis needed).

  The unique-up-to-iso lemmas in `Mathlib.RingTheory.Localization.Basic`
  (`IsLocalization.isLocalization_iff_of_isLocalization`,
  `IsLocalization.algHom_subsingleton`) provide the `AlgEquiv` form
  on demand from the `IsLocalization` predicate — i.e., Mathlib's
  convention is "store the predicate, derive the AlgEquiv when
  needed", not vice versa.
- **Project's path (proposed)**: blueprint Lemma
  `lem:appLE_isLocalization` (`AlgebraicGeometry.Scheme.appLE_isLocalization`)
  is shaped as `IsLocalization M A_colim`, which matches Mathlib's
  `IsAffineOpen.isLocalization_basicOpen` exactly. Parameters: `f`,
  `U`, `V`, `e`, `hU : IsAffineOpen U`, `hV : IsAffineOpen V`. The
  `M` submonoid is defined as
  `{g ∈ A : (f.appLE U V e).hom g ∈ B^×}`.
- **Gap**: identical. The blueprint's chosen shape is the Mathlib
  idiom verbatim.
- **Verdict**: **ALIGN_WITH_MATHLIB**. Use the bare-theorem form
  giving `IsLocalization M A_colim` under `IsAffineOpen U`,
  `IsAffineOpen V`, `V ≤ f⁻¹U` hypotheses. Do **not** also state an
  `AlgEquiv` — it would be a parallel API that no current consumer
  needs, and `IsLocalization.algEquiv`-style uniqueness lemmas
  produce it on demand.

  Mathlib name hint: an existing companion lemma
  `AlgebraicGeometry.appLE_eq_away_map`
  (`AffineScheme.lean:669`) lives in
  `AlgebraicGeometry.IsAffineOpen` namespace style; the project may
  consider naming `IsAffineOpen.appLE_isLocalization` rather than
  `Scheme.appLE_isLocalization` to match Mathlib's namespacing.

### Decision 3: Cofinality argument packaging for "directed colimit over `M`-localizations is the localization at `M`"

- **Mathlib idiom**: the canonical predicate is
  `CategoryTheory.Functor.Final`
  (`Mathlib.CategoryTheory.Functor.Final`); for filtered/cofiltered
  cones use `CategoryTheory.IsFiltered` /
  `CategoryTheory.IsCofiltered`. The closest directly applicable
  precedent for "scheme structure sheaf as colimit over basic
  opens" is
  `AlgebraicGeometry.Scheme.AffineZariskiSite.isColimitCocone`
  (`Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski:343`), which
  builds an explicit cocone and proves `IsColimit` by a local-to-global
  argument using `IsZariskiLocalAtTarget`.

  **For "directed colimit of `Aᵢ → A_g` localizations equals `A_M`",
  Mathlib has NO off-the-shelf lemma.** Searches via `lean_leansearch`,
  `lean_loogle`, and `lean_local_search` for
  `IsLocalization.colim_isLocalization`,
  `IsLocalization.iSup`,
  `Localization.colimit_*`, etc., return nothing.

  The Mathlib-idiomatic workhorse for the upgrade step is instead
  `IsLocalization.of_le`
  (`Mathlib.RingTheory.Localization.Defs`):
  ```
  theorem IsLocalization.of_le (M : Submonoid R) {S : ...}
      [Algebra R S] [IsLocalization M S] (N : Submonoid R)
      (h₁ : M ≤ N) (h₂ : ∀ r ∈ N, IsUnit (algebraMap R S r)) :
      IsLocalization N S
  ```
  which extends an `IsLocalization M S` witness to an
  `IsLocalization N S` witness over a larger submonoid `N` whose
  elements all become units. This is the right framing for
  `appLE_isLocalization`: prove it for a single `g ∈ M` first (which
  is `IsAffineOpen.isLocalization_basicOpen`), bootstrap the join
  via cocone universality, then upgrade to the full `M` via
  `IsLocalization.of_le`.
- **Project's path (proposed)**: blueprint M1.b argues cofinality
  of `{D(g) : g ∈ M}` in the cone `{W : f V ⊆ W ⊆ S}`, identifies
  each `Γ(S, D(g))` with `A_g` via `isLocalization_basicOpen`,
  then claims `colim_{g ∈ M} A_g = A_M`. The third step
  ("colim of localizations is the localization at M") is the
  genuine gap with no Mathlib closure.
- **Gap**: **divergent-with-cost**. The blueprint phrases the
  argument as a `colim`-comparison, which suggests reaching for
  `Functor.Final` + `colimitIso`. But this path requires building a
  cofinality witness against the `TopCat.Presheaf.pullback` colimit
  cone, which is unwieldy because the cone is over `(Opens S)ᵒᵖ`
  with the filter condition `f V ⊆ W`. The cleaner Mathlib-aligned
  path skips the explicit `colim`-comparison entirely.
- **Cost of divergence (if pursued as colim-comparison)**:
  ~200-400 LOC including: cofinality witness for
  `{D(g) : g ∈ M} ↪ {W : f V ⊆ W ⊆ S}`, identification of the
  colimit-of-`A_g` with `A_M`, transfer to the
  `TopCat.Presheaf.pullback`-shaped colimit.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** on the colim-of-localizations
  fact AS STATED, but the project should **avoid the colim-comparison
  framing entirely**. Recommended re-framing:

  1. **Construct the canonical map `A_M → A_colim` directly** by
     universal property of `Localization M` (or `IsLocalization M
     L`-universality applied to `A_colim` after showing every `g ∈ M`
     becomes a unit in `A_colim`).
  2. **Construct the inverse `A_colim → A_M`** by colimit-cocone
     universality of `A_colim`: for each open `W` with `f V ⊆ W ⊆ U`,
     pick a basic open `D(g) ⊆ W` with `appLE g ∈ B^×` (this is the
     ONE non-trivial topological/algebraic step); use the
     localization map `Γ(S, W) → Γ(S, D(g)) = A_g → A_M`; check
     compatibility on overlaps via uniqueness of localization maps
     (`IsLocalization.algHom_subsingleton`).
  3. **Verify the composite is the identity** using
     `IsLocalization.ringHom_ext` on both sides.
  4. **Conclude `IsLocalization M A_colim`** by
     `IsLocalization.isLocalization_iff_of_ringEquiv` (or
     `IsLocalization.of_le` after upgrading from a single `g`-step).

  This re-framing converts the cofiltered-colimit-comparison problem
  (which has no Mathlib closure) into a `Functor`-universal-property
  computation (which has full Mathlib closure). Estimated cost:
  100-250 LOC, comparable to but no worse than the colim-comparison
  framing.

  Auxiliary observation that simplifies M1.b: the project's
  `A_colim = ((TopCat.Presheaf.pullback CommRingCat f.base).obj
  S.presheaf).obj (op V)` is, by definition, a colimit of `S.presheaf
  .obj (op W)` over `W ⊇ f V`. Mathlib provides cocone-leg morphisms
  `S.presheaf.obj (op W) → A_colim` via `colimit.ι` directly; the
  project doesn't have to handle the `IsLocallyDirected` / coequalizer
  setup itself.

## Auxiliary finding: M1.c is NOT a Mathlib gap

The blueprint's `lem:kaehler_localization_subsingleton` (M1.c)
claims:

> Mathlib b80f227 has **no off-the-shelf** bare lemma for ‘Ω[L/A]
> is subsingleton when A → L is a localization’; the closest is
> `Algebra.IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential`
> (which requires the much stronger `IsStandardSmoothOfRelativeDimension 0`).
> This M1.c sub-lemma is therefore a genuine Mathlib gap-fill.

This claim is **incorrect**. The composition

```
[IsLocalization M L]
  → (Algebra.FormallyUnramified.of_isLocalization M : Algebra.FormallyUnramified A L)
  → (Algebra.FormallyUnramified.subsingleton_kaehlerDifferential : Subsingleton Ω[L⁄A])
```

is fully formalized in `Mathlib.RingTheory.Unramified.Basic` (theorem
at line 303, class instance field at line 57-59). One-line proof:

```lean
example {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L] : Subsingleton Ω[L⁄A] :=
  have : Algebra.FormallyUnramified A L :=
    Algebra.FormallyUnramified.of_isLocalization M
  inferInstance
```

**Verdict on M1.c**: **ALIGN_WITH_MATHLIB / ZERO_LOC.** Drop M1.c
as a standalone lemma; inline the two-line consequence at the M1.d
call site. The blueprint's "candidate Mathlib home" remark and the
~10-30 LOC budget should be replaced with a citation of
`Algebra.FormallyUnramified.of_isLocalization`.

## Auxiliary finding: M1.d is short, not a gap, and not best stated via `KaehlerDifferential.isLocalizedModule_map`

The blueprint's `lem:kaehler_quotient_localization_iso` (M1.d)
correctly identifies the second-fundamental-sequence argument, and
its citation of `KaehlerDifferential.isLocalizedModule_map` is one
valid path. A more direct path, closer to Mathlib's idiom in
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`
(Etale/Kaehler.lean:37-46), is:

```lean
example {A L B : Type*} [CommRing A] [CommRing L] [CommRing B]
    [Algebra A L] [Algebra L B] [Algebra A B] [IsScalarTower A L B]
    (M : Submonoid A) [IsLocalization M L] :
    Ω[B⁄A] ≃ₗ[B] Ω[B⁄L] := by
  have : Subsingleton Ω[L⁄A] := -- via FormallyUnramified.of_isLocalization
    have : Algebra.FormallyUnramified A L :=
      Algebra.FormallyUnramified.of_isLocalization M
    inferInstance
  refine LinearEquiv.ofBijective (KaehlerDifferential.map A L B B) ⟨?_, ?_⟩
  · -- injective: from exact_mapBaseChange_map + subsingleton left term
    sorry
  · -- surjective: from KaehlerDifferential.map_surjective
    sorry
```

Estimated body: 10-30 LOC, all using existing Mathlib lemmas.
**Verdict on M1.d**: **ALIGN_WITH_MATHLIB / SMALL_LOC.** Use
`KaehlerDifferential.exact_mapBaseChange_map` +
`KaehlerDifferential.map_surjective` +
`FormallyUnramified.of_isLocalization`. The Mathlib pattern from
`tensorKaehlerEquivOfFormallyEtale` is the closest precedent.

## Auxiliary finding: M1.e is the `rfl`-identification, already in place

The blueprint's M1.e step asserts that the presheaf section
`(relativeDifferentialsPresheaf f).presheaf.obj (op V)` is
definitionally `CommRingCat.KaehlerDifferential (φ'.app V)`, where
`φ'` is the transposed inverse-image map. This is the existing
`relativeDifferentialsPresheaf_obj_kaehler` lemma at
`Differentials.lean:58-64`, proved by `rfl`.

In Lean, the `rfl`-identification translates to a *definitional*
equality of types, so the bridge `LinearEquiv` is constructed on
`Ω[B/A_colim]` and the project's
`relativeDifferentialsPresheaf_iso_kaehler_appLE` consumer
trivially casts via the `rfl` lemma — or even more cleanly, by
choosing the right `letI` / `change` setup at the call site so the
section's underlying type is *already* `Ω[B/A_colim]` modulo `rfl`.

**Verdict on M1.e**: **PROCEED.** No new infrastructure.

## Recommendation

**Top-level verdict**: PROCEED with the iter-121 implementation,
applying the alignments below.

### Concrete API shape to ship

```lean
namespace AlgebraicGeometry.IsAffineOpen

-- M1.a (definition, not theorem): the submonoid
noncomputable def appLE_unitSubmonoid {X S : Scheme.{u}} (f : X ⟶ S)
    {U : S.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : Submonoid Γ(S, U) :=
  letI := (Scheme.Hom.appLE f U V e).hom.toAlgebra
  { carrier := { g | IsUnit (algebraMap Γ(S, U) Γ(X, V) g) }
    mul_mem' := ...
    one_mem' := ... }

-- M1.b: the load-bearing lemma. Bare theorem giving IsLocalization
-- predicate. Mirrors IsAffineOpen.isLocalization_basicOpen.
theorem appLE_isLocalization {X S : Scheme.{u}} (f : X ⟶ S)
    {U : S.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(S, U) _ :=
      -- the canonical algebra structure from the colim cocone leg
      ...
    IsLocalization (appLE_unitSubmonoid f e hU hV)
      (((TopCat.Presheaf.pullback CommRingCat f.base).obj
        S.presheaf).obj (.op V)) := ...

end AlgebraicGeometry.IsAffineOpen

namespace AlgebraicGeometry.Scheme

-- M1.c+M1.d combined: an inline use of FormallyUnramified +
-- exact_mapBaseChange_map. No standalone lemma needed.

-- M1.e: the bridge, packaged as a LinearEquiv.
noncomputable def relativeDifferentialsPresheaf_equiv_kaehler_appLE
    {X S : Scheme.{u}} (f : X ⟶ S)
    {U : S.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(S, U) Γ(X, V) :=
      (Scheme.Hom.appLE f U V e).hom.toAlgebra
    ((relativeDifferentialsPresheaf f).presheaf.obj (.op V)) ≃ₗ[Γ(X, V)]
      Ω[Γ(X, V) ⁄ Γ(S, U)] := ...

end AlgebraicGeometry.Scheme
```

### Concrete refactoring for blueprint Differentials.tex § sec:bridge

1. **Drop `lem:kaehler_localization_subsingleton` as a standalone
   lemma.** Replace its statement-block with an inline citation of
   `Algebra.FormallyUnramified.of_isLocalization` at the M1.c
   usage point inside the main theorem's proof. Reduces blueprint
   verbosity, accurately reports Mathlib status, and saves a
   `\lean{...}` declaration.

2. **Reshape `lem:kaehler_quotient_localization_iso` to follow the
   `tensorKaehlerEquivOfFormallyEtale` template.** State as a
   bare `LinearEquiv` `Ω[B⁄A] ≃ₗ[B] Ω[B⁄L]` under `[IsLocalization
   M L]`. Body: 10-30 LOC. This can also be the project's first
   Mathlib contribution since the lemma is general and Mathlib
   currently has the F-étale variant but not the L-only-on-base
   variant.

3. **Reshape `lem:appLE_isLocalization` argument to use
   `IsLocalization.of_le` + cocone universal property**, NOT a
   `Functor.Final` cofinality argument. Adjust the M1.b prose to
   match the Recommendation Decision 3 plan.

4. **Rename the main bridge theorem from
   `relativeDifferentialsPresheaf_iso_kaehler_appLE` to
   `relativeDifferentialsPresheaf_equiv_kaehler_appLE`** to match
   Mathlib's `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`
   naming (LinearEquiv → `Equiv` suffix). Reduces future-confusion
   about the underlying type.

5. **Consider relocating `appLE_isLocalization` under
   `AlgebraicGeometry.IsAffineOpen`** rather than
   `AlgebraicGeometry.Scheme`, to namespace-align with the existing
   Mathlib `IsAffineOpen.isLocalization_basicOpen`.

### Risk and scope estimate

- **M1.c, M1.d, M1.e together**: ~30-50 LOC of in-file work, all
  using off-the-shelf Mathlib lemmas. Low risk.
- **M1.b (the load-bearing step)**: 100-250 LOC, comprising
  - the unit-submonoid `M` definition (~10 LOC),
  - the canonical algebra structure on `A_colim` (~15 LOC, mostly
    bookkeeping from the colim cocone leg),
  - the cocone-universality argument that every `g ∈ M` becomes a
    unit in `A_colim` (~30-60 LOC; this is where the cofinality
    content lives, but as a `Functor`-universal-property
    computation rather than a `Functor.Final` lemma),
  - the inverse construction via `IsLocalization.of_le` plus
    section-by-section maps (~50-100 LOC).
  Estimated 2-4 prover iters at typical pace, comparable to but no
  worse than the colim-comparison framing.

### Mathlib contribution candidate

The most extractable upstream contribution from this iter is **the
re-framed `lem:kaehler_quotient_localization_iso` as a
`LinearEquiv`**, generalising
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` to the
"only the lower step is formally unramified" case. Name suggestion:
`KaehlerDifferential.mapEquiv_of_formallyUnramified_base` or
`KaehlerDifferential.equivOfFormallyUnramified`. The
`appLE_isLocalization` argument, while load-bearing for the project,
is too specifically scheme-morphism-shaped for a clean Mathlib PR;
defer that contribution until after the M1 milestone closes locally.

## Cross-references to prior analogies

- [[cotangent-presheaf-design]] (iter-120) — original analysis of
  the trade-off between presheaf-level `pullback` and sheafified
  inverse image; concluded `NEEDS_MATHLIB_GAP_FILL` on the bridge.
  This iter (121) commits to building the bridge as a project-local
  lemma and prescribes the API shape.
- [[affine-basis-sheaf-bridge]] (iter-114) — adjacent gap on
  sheaf-condition descent from affine basis; out-of-loop-scope per
  the project's strategic decision. The current bridge does NOT
  require closing the sheaf-bridge gap because it operates pointwise
  on a single affine chart.

## Iter-123 tactical addendum

Concrete tactical patterns encountered while proving
`isUnit_appLE_unitSubmonoid_in_colim` (Step 0 of M1.b, closed
iter-122) and prescribed for the iter-123 prover writing Steps 1+2+3+4
of `appLE_isLocalization`. All patterns reproduced in-situ at
`Differentials.lean:239,267` with `lean_multi_attempt`.

### Pattern A — Lan functor `map_comp` rewriting

**Symptom**: `rw [Functor.map_comp]` and `simp only [Functor.map_comp]`
both fail on
`((TopCat.Presheaf.pullback CommRingCat f.base).obj S.presheaf).map (g₁ ≫ g₂)`
inside a tactic block that uses `set Acolim := ...` and `set cleg :=
...` aliases, even though the pattern syntactically matches. Root
cause: `rw`'s higher-order unification cannot abstract over
`?self : C ⥤ D` when `C = (Opens X)ᵒᵖ` and the functor body involves
a `Lan` whose underlying colimit term is opaque, AND the aliases
hide enough of the type structure to prevent motive resolution.

**Canonical workaround**:
```lean
have hmc : ((TopCat.Presheaf.pullback CommRingCat f.base).obj P).map (g₁ ≫ g₂) =
    ((TopCat.Presheaf.pullback CommRingCat f.base).obj P).map g₁ ≫
    ((TopCat.Presheaf.pullback CommRingCat f.base).obj P).map g₂ :=
  Functor.map_comp _ _ _
erw [hmc]
```

`erw` succeeds because it allows definitional unfolding during
unification. The pre-prove is needed because `Functor.map_comp _ _ _`
inferred its arguments from the LHS shape, side-stepping the motive
issue.

**Cheaper alternative when available**: avoid the `set` aliases for
sub-terms that participate in the rewrite. Use `let` definitions
inside the proof body or inline the alias's body at the use site.

### Pattern B — `IsLocalization` constructor shape

When proving `IsLocalization N T` for a fresh `(N, T)` pair (no
existing `IsLocalization` on `T`), the **only** Mathlib constructor
that doesn't pre-require `IsLocalization _ T` is the three-piece
characterisation `isLocalization_iff` (Defs.lean:110):

```
IsLocalization M S ↔
  (∀ y : M, IsUnit (algebraMap R S y)) ∧
  (∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1) ∧
  (∀ {x y : R}, algebraMap R S x = algebraMap R S y → ∃ c : M, c * x = c * y)
```

Every `IsLocalization.of_le`, `IsLocalization.atUnits`,
`IsLocalization.isLocalization_of_algEquiv`, etc. requires an existing
`IsLocalization` somewhere upstream. The blueprint's 4-step plan is
the canonical pattern (Steps 1-3 build the AlgEquiv via the two
direction maps; Step 4 invokes `isLocalization_of_algEquiv`). The
alternative `rw [isLocalization_iff]; refine ⟨_, _, _⟩` saves the
AlgEquiv bookkeeping but requires the same mathematical content
(cofinality / basic-open cover).

### Pattern C — `algebraMap`-from-`.toAlgebra` unification

For an algebra structure `letI : Algebra R S := i.toAlgebra` with
`i : R →+* S`, the Mathlib lemma
`RingHom.algebraMap_toAlgebra` (Defs.lean:212) proves
`@algebraMap R S _ _ i.toAlgebra = i := rfl`. In practice:

- `exact h : IsUnit (i g)` against a goal `IsUnit (algebraMap R S g)`
  **succeeds** — Lean's term-level unification handles the
  `i.toAlgebra`-to-`algebraMap` equality automatically.
- `change IsUnit (i g)` **succeeds** — Lean's change tactic handles
  the definitional equality.
- `rw [show algebraMap R S g = i g from rfl]` **fails** — `rw` can't
  pattern-match `(algebraMap _ _) g` against itself when the
  underscore positions are motive-dependent.

**Recommendation**: prefer `exact` direct, fall back to `change`,
avoid the `rw [... from rfl]` workaround entirely.

### Pattern D — Inner unit naturality with `(𝟭 _).obj _` decoration

For an adjunction `F ⊣ G : C ⥤ D ⊣ D ⥤ C`, the unit is `unit : 𝟙 ⟶ G
∘ F` and `unit.app X : (𝟭 _).obj X ⟶ G.obj (F.obj X)`. The
**outer naturality** `Adjunction.unit_naturality` (Basic.lean:282) is
`@[simp]` and uses `dsimp%` to strip the `(𝟭 _).obj` decoration:

```
adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y
```

The **inner naturality** — for an adjunction of endofunctors of
presheaves like `pullback ⊣ pushforward` — `(adj.unit.app
S.presheaf).naturality (homOfLE _).op` produces a square whose LHS
involves `((𝟭 _).obj S.presheaf).map (homOfLE _).op` rather than the
plain `S.presheaf.map (homOfLE _).op`. There is no Mathlib lemma
that eliminates this decoration at the inner level.

**Canonical workaround**: `simpa using (adj.unit.app
S.presheaf).naturality _`. The `simpa` strips the `(𝟭 _).obj`
decoration via `dsimp` rules on `Functor.id`. Used pervasively in
Mathlib's `CategoryTheory/Sheaves/`.

