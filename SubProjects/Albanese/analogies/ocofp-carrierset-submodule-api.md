# Analogy: `carrierSet → Submodule → presheaf → sheaf` API alignment for `lineBundleAtClosedPoint`

## Mode
api-alignment

## Slug
ocofp-carrierset-submodule-api

## Iteration
185

## Question

The project has been blocked for ~18 iters on completing the
`carrierSet (Set K(C)) → carrierSubmodule (Submodule kbar K(C)) → presheaf →
isSheaf → Sheaf J (ModuleCat kbar)` chain inside
`RiemannRoch/OCofP.lean` for the Hartshorne subsheaf-of-`K_C` direct
construction of `lineBundleAtClosedPoint`. The iter-185 progress-critic
verdict is CHURNING + OVER_BUDGET. The directive asks four questions:

1. Is there a Mathlib idiom for "subsheaf of `K(C)` cut out by an order
   condition" that the project should ALIGN to (vs. building stepwise)?
2. What is the right Mathlib API for the three `Submodule` closure proofs
   (`0`, `+`, `kbar • _`)? Is the project's `Scheme.RationalMap.order`
   aligned to it, or parallel to it?
3. Should the sheaf property go via stalk-locality (the iter-183 plan)
   or via the constant-sheaf-restriction `isSheaf_iff_isSheaf_forget`
   pattern (the project's existing `toModuleKSheaf` template)?
4. Is `Scheme.RationalMap.order` (`WithZero.log ∘ Ring.ordFrac`) a
   parallel API to Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation`,
   and should the project align?

## Project artifact(s)
- `AlgebraicJacobian/RiemannRoch/OCofP.lean:153-166` — `lineBundleAtClosedPoint.carrierSet` (iter-183 axiom-clean `Set`).
- `AlgebraicJacobian/RiemannRoch/OCofP.lean:181-192` — `lineBundleAtClosedPoint.carrierSet_mono` (iter-183 monotonicity).
- `AlgebraicJacobian/RiemannRoch/OCofP.lean:224-233` — `lineBundleAtClosedPoint` (typed `sorry` body).
- `AlgebraicJacobian/RiemannRoch/WeilDivisor.lean:152-156` — `Scheme.RationalMap.order` (project's `WithZero.log ∘ Ring.ordFrac` ℤ-valued projection).
- `AlgebraicJacobian/RiemannRoch/WeilDivisor.lean:173-186` — `Scheme.IsRegularInCodimensionOne` carrier class (currently exports only `Ring.KrullDimLE 1`).
- `AlgebraicJacobian/Cohomology/StructureSheafModuleK/SheafProperty.lean:32-44` — `toModuleKPresheaf_isSheaf` + `toModuleKSheaf` (the project's existing `Sheaf J (ModuleCat kbar)`-construction template that the recipe will mirror).

## Decisions identified

### Decision 1 — `Subpresheaf`/`Subsheaf` API for `Sheaf J (ModuleCat kbar)`-valued sheaves

- **Mathlib idiom**: There is **no** Mathlib subsheaf API at the right
  level. Concretely:
  - `CategoryTheory.Subpresheaf` / `CategoryTheory.Subfunctor`
    (`Mathlib.CategoryTheory.Subfunctor.Basic`) is the standard idiom
    for "subsheaf cut out by a per-open predicate" — but it ships
    **`Functor C (Type w)`-only**. There is no `ModuleCat R`-valued
    subpresheaf machinery; `CategoryTheory.Subpresheaf` is parameterised
    over `F : Functor Cᵒᵖ (Type w)`, period.
  - `SheafOfModules.subobject` / dual / kernel functors do not ship.
    `SheafOfModules R` is over a sheaf-of-rings `R`, a different
    category from `Sheaf J (ModuleCat kbar)` — and even there, no
    subobject-by-per-open-submodule API exists.
  - The Type-valued `Subfunctor.sheafify_isSheaf`
    (`Mathlib.CategoryTheory.Sites.Subsheaf`) computes the sheafification
    of a sub-presheaf but operates only on `Type`-valued targets.
- **Project's current path**: stepwise build (per-open
  `Set → Submodule → Functor → IsSheaf → Sheaf`), mirroring the
  project's existing `toModuleKPresheaf → toModuleKPresheaf_isSheaf →
  toModuleKSheaf` template (`StructureSheafModuleK/{Presheaf,SheafProperty}.lean`).
- **Gap**: divergent-equivalent at the *direct-build* level. Mathlib
  ships the same building blocks (`ModuleCat.of`, `Presheaf.IsSheaf`,
  `Presheaf.isSheaf_iff_isSheaf_forget`) but no shortcut for
  "subsheaf-of-`Sheaf J (ModuleCat kbar)`-from-per-open-submodules".
- **Verdict**: **PROCEED** with the stepwise direct build — there is no
  cheaper Mathlib idiom to ALIGN to here. The project's chosen
  `Sheaf J (ModuleCat kbar)` carrier matches `Scheme.HModule` and is the
  right target; the stepwise build is canonical for this carrier.

### Decision 2 — `Submodule` closure proofs (`0`, `+`, `kbar • _`)

The three closure proofs needed to upgrade `carrierSet U` to a
`Submodule kbar (X.functionField)`:

#### Decision 2a — Zero closure

- **Mathlib idiom**: `WithZero.log_zero : WithZero.log (0 : WithZero (Multiplicative M)) = 0`
  (`Mathlib.Algebra.GroupWithZero.WithZero`). Combined with the project's
  `order = WithZero.log ∘ ordFrac`, this gives `order Y 0 = 0` for every
  prime divisor `Y`. Hence `0 ≥ 0` (every off-`P` condition) and
  `-1 ≤ 0` (the at-`P` condition) trivially hold.
- **Project's current path**: not yet written.
- **Gap**: identical. The Mathlib lemma is one rewrite.
- **Verdict**: **ALIGN_WITH_MATHLIB** — use `WithZero.log_zero` +
  `MonoidHomClass.map_zero` (already implicit in `K →*₀ ℤᵐ⁰`).
  ~5 LOC.

#### Decision 2b — Addition closure

- **Mathlib idiom**: `Ring.ordFrac_add`
  (`Mathlib.RingTheory.OrderOfVanishing.Noetherian`) ships the
  non-archimedean inequality
  `min ((Ring.ordFrac R) x) ((Ring.ordFrac R) y) ≤ (Ring.ordFrac R) (x + y)`
  for `x + y ≠ 0` — but with the typeclass **`[IsDiscreteValuationRing R]`**,
  NOT `[Ring.KrullDimLE 1 R]`. This is mathematically tight: an
  arbitrary Krull-dim-≤-1 Noetherian commutative ring (e.g.
  `ℤ[x] / (x^2)`) has `Ring.ordFrac` defined via multiplicity, which is
  multiplicative but NOT non-archimedean.
- **Project's current path**: `Scheme.IsRegularInCodimensionOne` ships
  only `Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)` (WeilDivisor L173-186),
  not `IsDiscreteValuationRing`. So `Ring.ordFrac_add` is **NOT
  invocable** as-is. The project would have to either prove the
  non-archimedean inequality from scratch (~30-50 LOC of bespoke
  argument, re-deriving Hartshorne 6.2 from `Ring.ordFrac` semantics)
  or upgrade the class.
- **Gap**: divergent-with-cost. The cost of NOT aligning:
  - 30-50 LOC of bespoke add-closure proof per closure, OR
  - Stuck with a typed `sorry` (the iter-183 outcome).
  - Plus: every downstream consumer of "`order` is a valuation" will
    need its own bespoke bridge, multiplying the bridge-lemma debt.
- **Verdict**: **ALIGN_WITH_MATHLIB** — strengthen
  `Scheme.IsRegularInCodimensionOne.out` to ship `IsDiscreteValuationRing
  (X.presheaf.stalk Y.point)` (and let `Ring.KrullDimLE 1` derive
  automatically). The class is currently *misnamed/under-strength*:
  Hartshorne's "regular in codim 1" *means* DVR stalks at prime
  divisors; the `Ring.KrullDimLE 1`-only export is a strictly weaker
  approximation that blocks the canonical Mathlib API. ~5-10 LOC to
  strengthen the class + auto-derive the Krull-dim instance.

  Once the class is upgraded, the add closure becomes ~10-15 LOC: case
  split on `f + g = 0` (trivial via `WithZero.log_zero`), else apply
  `Ring.ordFrac_add` followed by `WithZero.log` (the `WithZero.log` is
  monotonic on the nonzero part, so the `min` translates correctly).

#### Decision 2c — `kbar`-scalar closure

- **Mathlib idiom**: `Ring.ordFrac_le_smul`
  (`Mathlib.RingTheory.OrderOfVanishing.Noetherian`) ships
  `(Ring.ordFrac R) f ≤ (Ring.ordFrac R) (a • f)` for `a : S` with
  `(algebraMap S R) a ≠ 0`, given `[Algebra S R]` and
  `[IsScalarTower S R K]`. For `S = kbar`, `R = X.presheaf.stalk Y.point`,
  `K = X.functionField`:
  - `[Algebra kbar (X.presheaf.stalk Y.point)]` should be inferable from
    `C : Over (Spec (.of kbar))` via stalk-of-Spec-kbar-algebra.
  - `[IsScalarTower kbar (X.presheaf.stalk Y.point) X.functionField]`
    similarly.
  - For `c ≠ 0`, `algebraMap kbar (X.presheaf.stalk Y.point) c` is a
    UNIT in the stalk (since `kbar` is a field), so by
    `Ring.ordFrac_of_isUnit` the order is `0`, and the scalar action
    *preserves* (not just doesn't decrease) the order.
  - **NB**: `Ring.ordFrac_le_smul` works under `[Ring.KrullDimLE 1 R]`,
    no DVR-upgrade required for this lemma. So the scalar closure is
    cheap even *before* the Decision 2b class upgrade.
- **Project's current path**: not yet written.
- **Gap**: identical at the lemma level; mild instance-synthesis work
  needed to expose `[Algebra kbar (stalk Y.point)]` and the scalar-tower
  on a `Spec kbar`-scheme.
- **Verdict**: **ALIGN_WITH_MATHLIB** — use `Ring.ordFrac_le_smul` (or
  the `Ring.ordFrac_of_isUnit` + `map_mul` combination for an exact
  equality). ~5-10 LOC plus any missing scalar-tower instance.

### Decision 3 — Sheaf property: gluing-by-stalks vs `isSheaf_iff_isSheaf_forget`

- **Mathlib idiom**: `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`
  (`Mathlib.CategoryTheory.Sites.Sheaf`) reduces the sheaf condition for
  a `ModuleCat kbar`-valued presheaf to the sheaf condition for the
  underlying `Type`-valued presheaf (via the conservative
  `CategoryTheory.forget (ModuleCat kbar)`). The project's
  `toModuleKPresheaf_isSheaf` already uses this idiom verbatim
  (`StructureSheafModuleK/SheafProperty.lean:32-37`).

  For `lineBundleAtClosedPoint`, the `Type`-valued forget of the
  presheaf is `U ↦ ↥(carrierSubmodule U)`, a sub-Type-presheaf of the
  constant presheaf `U ↦ K(C)`. The constant presheaf at `K(C)` on an
  IRREDUCIBLE scheme `X` (which the project has via `IsIntegral C.left`)
  is automatically a sheaf — gluing rational functions over an open
  cover gives back the same rational function (a single element of the
  field `K(C)`). The sub-Type-presheaf inherits the sheaf condition:
  given matching `(fᵢ ∈ carrierSet Vᵢ)`, all `fᵢ` are the SAME
  `f ∈ K(C)` (forced by overlap-matching on an irreducible scheme), and
  `f ∈ carrierSet U` because every prime divisor `Q ∈ U` lies in some
  `Vᵢ`, so the per-`Q` order condition holds.
- **Project's current path**: iter-183 docstring (OCofP L143-144) plans
  "gluing-by-stalks principle (stalk-locality of the order conditions
  at each prime divisor)". This works but is the harder presentation —
  it builds the sheaf condition pointwise at every prime divisor.
- **Gap**: divergent-with-cost. The stalk-gluing route is ~80-150 LOC
  (iter-182 analogist's estimate; `ocofp-sheaf-internalhom.md` L242);
  the `isSheaf_iff_isSheaf_forget` route is ~30-50 LOC because it
  factors through the standing irreducibility hypothesis.
- **Verdict**: **ALIGN_WITH_MATHLIB** — use `isSheaf_iff_isSheaf_forget`
  mirroring `toModuleKPresheaf_isSheaf`. The two are mathematically
  equivalent; the `isSheaf_iff_isSheaf_forget` route halves the LOC and
  reuses a project-side proven template.

### Decision 4 — `Scheme.RationalMap.order` vs `IsDedekindDomain.HeightOneSpectrum.valuation`

- **Mathlib idiom**: Two distinct APIs:
  - `Ring.ordFrac : K →*₀ WithZero (Multiplicative ℤ)`
    (`Mathlib.RingTheory.OrderOfVanishing`) — a monoid-with-zero hom
    parameterised by a Noetherian, Krull-dim-≤-1 commutative ring `R`,
    its fraction field `K`. Does NOT carry a non-archimedean inequality
    in general; works for any `Ring.KrullDimLE 1`.
  - `IsDedekindDomain.HeightOneSpectrum.valuation : K → WithZero (Multiplicative ℤ)`
    (`Mathlib.RingTheory.DedekindDomain.AdicValuation`) — a full
    `Valuation` (with built-in non-archimedean inequality), parameterised
    by an `IsDedekindDomain R` and a height-one prime. Requires
    Dedekind-ness on the *global* ring `R`.
- **Project's current path**:
  `Scheme.RationalMap.order Y f := WithZero.log (Ring.ordFrac (stalk Y.point) f)`
  (WeilDivisor L152-156). This is the `WithZero.log`-projected `ℤ`-valued
  version of `Ring.ordFrac`, applied stalk-by-stalk.
- **Gap**: **NOT a parallel API**. The project's `order` aligns with
  `Ring.ordFrac` (the right per-stalk Krull-dim-1 entry point) plus a
  cosmetic ℤ-projection. It is *not* parallel to
  `IsDedekindDomain.HeightOneSpectrum.valuation` — that API would
  require an `IsDedekindDomain` instance on the whole stalk (not a
  per-stalk local property; cf. an integral scheme regular in codim 1
  whose stalks at codim-2 points are not DVRs). The project's choice
  of factoring through `Ring.ordFrac` is right at the granularity
  level: per-stalk Krull-dim-1 is the natural hypothesis the carrier
  class encodes, and the stalks at prime divisors are DVRs (which is
  Hartshorne's `(*)`).
- **Verdict**: **PROCEED** on the API choice. The work to do is NOT a
  refactor of `Scheme.RationalMap.order`; it is the Decision 2b class
  upgrade so that the project's per-stalk Krull-dim-1 hypothesis is
  strengthened to DVR-ness (which is what "regular in codim 1" actually
  means in classical AG, and what unlocks `Ring.ordFrac_add` and the
  rest of the DVR-specific `Ring.ordFrac` API at
  `Mathlib.RingTheory.OrderOfVanishing.Noetherian`).

## Recommendation

### Verdict summary

| Decision | Verdict | Severity |
|---|---|---|
| 1: Subsheaf-of-ModuleCat idiom | PROCEED | informational |
| 2a: Zero closure | ALIGN_WITH_MATHLIB | major |
| 2b: Add closure (+ class upgrade) | ALIGN_WITH_MATHLIB | critical |
| 2c: Scalar closure | ALIGN_WITH_MATHLIB | major |
| 3: Sheaf property route | ALIGN_WITH_MATHLIB | critical |
| 4: `RationalMap.order` API alignment | PROCEED | informational |

The route is **not** blocked by a missing Mathlib idiom or a parallel-API
trap. It is blocked by a single under-strength carrier-class field
(`Scheme.IsRegularInCodimensionOne.out` exports `Ring.KrullDimLE 1`
instead of `IsDiscreteValuationRing`) and by the iter-183 plan choosing
the harder of two sheaf-property routes (stalk-gluing instead of
forget-to-Type-then-trivial-on-irreducible-scheme).

### Concrete iter-186 recipe (5 steps, ~105 LOC total)

**Step 1 — Class upgrade** (~10 LOC, edit `WeilDivisor.lean:171-186`):

Replace the `out : ... Ring.KrullDimLE 1 ...` field with
`out : ∀ Y : Scheme.PrimeDivisor X, IsDiscreteValuationRing (X.presheaf.stalk Y.point)`.
Add an instance synthesising `Ring.KrullDimLE 1` from
`IsDiscreteValuationRing` (Mathlib's `IsDiscreteValuationRing.TFAE` /
`IsDedekindDomain` chain provides this — DVR ⟹ PID ⟹ Krull-dim-≤-1).

Note: this affects the existing `Scheme.RationalMap.order` users
(`principal`, `principal_hom`, `principal_degree_zero`, the
`globalSections_iff_*` helpers, etc.), but all consumers currently take
`[Scheme.IsRegularInCodimensionOne X]` as a class hypothesis, so the
class-field rewrite propagates automatically without any signature change
downstream.

**Step 2 — `carrierSubmodule`** (~25 LOC, new declaration after
`carrierSet_mono` in `OCofP.lean`):

```lean
private noncomputable def lineBundleAtClosedPoint.carrierSubmodule
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))} [IsIntegral C.left]
    [IsLocallyNoetherian C.left]
    [Scheme.IsRegularInCodimensionOne C.left]
    (P : C.left) (hPcoh : Order.coheight P = 1)
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    Submodule kbar C.left.functionField where
  carrier := lineBundleAtClosedPoint.carrierSet P hPcoh U
  zero_mem' := by
    -- order Y 0 = WithZero.log 0 = 0; both `0 ≥ 0` and `-1 ≤ 0` hold.
    refine ⟨fun Q _ _ => ?_, fun _ => ?_⟩
    · simp [Scheme.RationalMap.order, map_zero, WithZero.log_zero]
    · simp [Scheme.RationalMap.order, map_zero, WithZero.log_zero]
  add_mem' := by
    -- case-split on f + g = 0 (trivial via WithZero.log_zero), else
    -- apply Ring.ordFrac_add (DVR-shipped by Step 1) + WithZero.log
    -- monotonicity on the nonzero part.
    rintro f g ⟨hf₁, hf₂⟩ ⟨hg₁, hg₂⟩
    refine ⟨fun Q hQU hQP => ?_, fun hPU => ?_⟩
    · ... -- use `Ring.ordFrac_add` after the case-split
    · ... -- same pattern at P
  smul_mem' := by
    -- For c : kbar, algebraMap kbar (stalk) c is a unit when c ≠ 0;
    -- Ring.ordFrac_of_isUnit gives order = 0; order Y (c • f) = order Y f.
    -- For c = 0, c • f = 0 reduces to zero_mem'.
    rintro c f ⟨hf₁, hf₂⟩
    ...
```

**Step 3 — Presheaf functor** (~30 LOC, new declaration):

```lean
private noncomputable def lineBundleAtClosedPoint.presheaf
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))} [IsIntegral C.left]
    [IsLocallyNoetherian C.left]
    [Scheme.IsRegularInCodimensionOne C.left]
    (P : C.left) (hPcoh : Order.coheight P = 1) :
    (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ ⥤ ModuleCat.{u} kbar where
  obj U := ModuleCat.of kbar ↥(carrierSubmodule P hPcoh U)
  map {U V} f := ModuleCat.ofHom <|
    Submodule.inclusion (carrierSet_mono P hPcoh
      (CategoryTheory.leOfHom f.unop))
  map_id U := by ext ⟨x, _⟩; rfl
  map_comp _ _ := by ext ⟨x, _⟩; rfl
```

**Step 4 — Sheaf property via `isSheaf_iff_isSheaf_forget`** (~40 LOC):

Mirror `toModuleKPresheaf_isSheaf` (`SheafProperty.lean:32-37`):

```lean
private lemma lineBundleAtClosedPoint.presheaf_isSheaf
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))} [IsIntegral C.left]
    [IsLocallyNoetherian C.left]
    [Scheme.IsRegularInCodimensionOne C.left]
    (P : C.left) (hPcoh : Order.coheight P = 1) :
    Presheaf.IsSheaf (Opens.grothendieckTopology C.left.toTopCat)
      (lineBundleAtClosedPoint.presheaf P hPcoh) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget (ModuleCat.{u} kbar))]
  -- Now goal: the Type-valued forget of `presheaf P hPcoh` is a sheaf.
  -- The forget is `U ↦ ↥(carrierSubmodule U) ⊆ K(C)`.
  -- For each cover {Vᵢ} of U and matching family (fᵢ ∈ carrierSet Vᵢ),
  -- all fᵢ are equal in K(C) (overlap-matching + irreducibility), so
  -- f := f₁ ∈ K(C) is the unique extension; f ∈ carrierSet U because
  -- every Q ∈ U lies in some Vᵢ where the per-Q order condition holds.
  ...
```

The body uses `IsIntegral C.left → IrreducibleSpace C.left.toTopCat`
(Mathlib instance) to force "overlap matching ⟹ same `f ∈ K(C)`" via
density of nonempty opens; then the per-`Q` condition holds because
every prime divisor `Q ∈ U` is in some `Vᵢ`.

**Step 5 — Bundle** (~5 LOC, replace `OCofP.lean:224-233` `sorry`):

```lean
noncomputable def lineBundleAtClosedPoint
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))} [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIrreducible C.hom] [IsIntegral C.left]
    [IsLocallyNoetherian C.left]   -- already in the namespace section
    [Scheme.IsRegularInCodimensionOne C.left]  -- already in scope
    (P : C.left) (hP : IsClosed ({P} : Set C.left))
    (hPcoh : Order.coheight P = 1) :
    Sheaf (Opens.grothendieckTopology C.left.toTopCat)
      (ModuleCat.{u} kbar) :=
  ⟨lineBundleAtClosedPoint.presheaf P hPcoh,
   lineBundleAtClosedPoint.presheaf_isSheaf P hPcoh⟩
```

(The signature already takes `hP`, `hPcoh`; `IsLocallyNoetherian` +
`IsRegularInCodimensionOne` need to be added as class hypotheses on the
top-level `lineBundleAtClosedPoint` def — they're already on the
helpers `globalSections_iff_*` so the propagation is uniform.)

### LOC + risk summary

| Step | LOC | Risk | Mathlib-blocking |
|------|-----|------|-------------------|
| 1: class upgrade (`Ring.KrullDimLE 1 → IsDiscreteValuationRing`) | ~10 | low | none — `IsDiscreteValuationRing.toIsLocalRing` + DVR ⟹ KrullDimLE 1 are Mathlib-shipped |
| 2: `carrierSubmodule` (zero/add/smul closures) | ~25 | low | none after Step 1 |
| 3: `presheaf` functor + restrictions | ~30 | low | none |
| 4: `presheaf_isSheaf` via `isSheaf_iff_isSheaf_forget` | ~40 | medium | none — uses `IsIntegral → IrreducibleSpace` and the standard subsheaf-of-constant-sheaf argument |
| 5: bundle | ~5 | trivial | none |
| **Total** | **~110** | medium | none — all in-project |

### What NOT to do

- **Do NOT** define `carrierSubmodule` by manual reproof of the
  non-archimedean inequality on `Ring.ordFrac` for `KrullDimLE 1`-only
  stalks. That inequality is **mathematically false** in that generality
  (any `Ring.KrullDimLE 1` Noetherian ring; e.g. `ℤ[x]/(x^2)`). The
  only correct path is to upgrade the carrier class to ship
  `IsDiscreteValuationRing` (which IS true for regular-in-codim-1
  schemes — that is what `(*)` means in Hartshorne).
- **Do NOT** pivot to `IsDedekindDomain.HeightOneSpectrum.valuation`
  for the carrier-set definition. That API requires `IsDedekindDomain`
  on the whole ring, which is a *global* property, not a per-stalk
  property. The project's per-stalk Krull-dim-1 + DVR-upgrade approach
  is the right granularity.
- **Do NOT** go via stalk-gluing for the sheaf property. The
  `isSheaf_iff_isSheaf_forget` route reuses the project's existing
  template and halves the LOC.
- **Do NOT** add a new file (e.g. `IdealSheafDual.lean` — already
  flagged by iter-182 analogist `ocofp-sheaf-internalhom.md` Decision 4
  as `DIVERGE_INTENTIONALLY`). All five recipe steps stay in
  `OCofP.lean` + a 10-LOC edit in `WeilDivisor.lean`.

### Cost of NOT acting

If iter-186 does not execute this recipe and continues the iter-183
trajectory of adding ad-hoc helpers in K-iters:

- The DVR-class upgrade (Step 1) blocks every existing typed `sorry`
  in `OCofP.lean` (carrier upgrade, `globalSections_iff_mp`,
  `globalSections_iff_mpr`, `h1_vanishing_genusZero`,
  `dim_eq_two_of_genusZero`, `exists_nonconstant_genusZero`). Without
  Step 1, the bespoke `Ring.ordFrac_add`-replacement work needed to
  close add-closure alone is ~30-50 LOC of project-bespoke valuation
  derivation, plus a parallel-API-tax for every future consumer.
- The sheaf-property route choice (Step 4 via
  `isSheaf_iff_isSheaf_forget`) saves ~50-100 LOC over the
  stalk-gluing route. Without it, the sheaf-property step alone is
  ~100 LOC of bespoke gluing, vs. ~40 LOC for the forget-route.
- Cumulative under-budget cost over the next 3-5 iters: ~80-150 LOC of
  parallel work, plus the API-fragmentation cost (every future
  `lineBundleAtDivisor`-style consumer will have to bridge between
  `Ring.ordFrac` and the project's bespoke valuation reproof).
