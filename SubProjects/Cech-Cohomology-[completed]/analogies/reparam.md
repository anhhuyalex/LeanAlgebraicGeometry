# Analogy: re-parameterizing the free-Čech resolution + sheaf-of-modules local section surjectivity

## Mode
api-alignment

## Slug
reparam

## Iteration
030

## Question
Two API questions before committing prover budget:
1. Re-parameterize the free-Čech resolution in `FreePresheafComplex.lean` from
   `(𝒰 : X.OpenCover) [Finite 𝒰.I₀]` to `{ι : Type} [Finite ι] (U : ι → Opens X)`. Does
   Mathlib already have a Čech/nerve/coverage construction indexed by a raw family of opens to
   align with? Does a free-Yoneda Čech resolution *need* the family to cover the whole space?
2. For `surj_of_vanishing`: given an epimorphism `g : M ⟶ N` of `X.Modules`, a section
   `t ∈ N(V)`, produce a cover `{W_i}` of `V` and lifts `s_i ∈ M(W_i)` with `g(s_i) = t|_{W_i}`.
   What is the Mathlib idiom, and can the cover be refined to basic/affine opens?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/FreePresheafComplex.lean:129,135,165,207,276,288,346` —
  `coverOpen`, `coverInterOpen`, `cechFreeSimplicial`, `cechFreePresheafComplex`, `cechFreeAug`,
  `coverStructurePresheaf`, `cechFreeComplexAug` (free side, indexed by `X.OpenCover`).
- `AlgebraicJacobian/Cohomology/PresheafCech.lean:303,334` — `sectionCechCosimplicial`,
  `sectionCechComplex {ι : Type u} (U : ι → Opens X)` (section side, **already raw-family**).
- `AlgebraicJacobian/Cohomology/CechBridge.lean:658` — `ses_cech_h1` (takes local lifts
  `sLoc i`/`hlift` over cover members `U i` as **hypotheses**).
- `AlgebraicJacobian/Cohomology/CechToCohomology.lean:309,331` — `CovDatum = Σ ι, ι → Opens X`
  (**already raw-family**); `BasisCovSystem.surj_of_vanishing`.

## Decisions identified

### Decision Q1-A: index the free-Čech resolution by a raw family `U : ι → Opens X`

- **Mathlib idiom**: Mathlib's Čech complexes are indexed by a **raw family of objects**, with
  **no covering hypothesis**:
  - `CategoryTheory.cechComplexFunctor` — `Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean:65`
    (Joël Riou, 2026). `variable [HasFiniteProducts C] [Preadditive A] {ι : Type w} (U : ι → C)`;
    `cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ`. Degree-`n` term is
    `∏_{x : Fin (n+1) → ι} P(∏_a U (x a))` — exactly the project's `sectionCechComplex` shape
    (products = `⨅` in `Opens X`). **The family `U` is arbitrary; nothing requires it to cover.**
  - `CategoryTheory.Limits.FormalCoproduct.cech` /  `.cechFunctor` /  `.power` —
    `Mathlib/CategoryTheory/Limits/FormalCoproducts/Cech.lean:186,194,34`. The
    coproduct-side (free) Čech simplicial object of a formal coproduct of objects `U j`
    (`j : ι`); degree-`n` is the formal coproduct over `i : Fin (n+1) → ι` of products
    `∏_a U (i a)`. This is precisely the *index structure* of the project's `cechFreeSimplicial`
    (degree `p` = `∐_{σ : Fin(p+1)→ι} freeYoneda(⨅ U(σ k))`).
  - `Arrow.cechNerve` — `Mathlib/AlgebraicTopology/CechNerve.lean:56` — Čech nerve of a *single
    morphism* (iterated fibre products). DIFFERENT construction (indexed by the cover map
    `∐U_i → X`, not by a family of opens); not an alignment target.
- **Project's current path**: free side indexed by `X.OpenCover`; section side and `CovDatum`
  already raw-family `(U : ι → Opens X)`. `coverOpen 𝒰 i = (𝒰.f i).opensRange` adapts.
- **Gap**: divergent-with-cost (free side is the lone `X.OpenCover`-indexed outlier).
- **Cost of divergence**: the free side cannot be fed a raw family directly — every caller must
  fabricate an `X.OpenCover` wrapper, an impedance mismatch with the raw-family section side
  (`sectionCechComplex`, `ses_cech_h1`) and `CechToCohomology`'s `CovDatum`/`BasisCovSystem`.
  `X.OpenCover` additionally drags in `OpenCover.iSup_opensRange : ⨆ = ⊤`
  (`Mathlib/AlgebraicGeometry/Cover/Open.lean:65`), a covering constraint the resolution never uses.
- **Verdict**: ALIGN_WITH_MATHLIB — re-parameterize to `{ι} [Finite ι] (U : ι → Opens X)`,
  keep `X.OpenCover` as a thin wrapper passing `coverOpen 𝒰`. This matches Mathlib's
  `cechComplexFunctor`/`FormalCoproduct.cech` *and* the project's own section side.

### Decision Q1-B: does a free-Yoneda Čech resolution need the family to cover the whole space?

- **Mathlib idiom**: NO. `cechComplexFunctor` and `FormalCoproduct.cech` take an arbitrary
  family with no covering / `iSup = ⊤` hypothesis. The Čech construction is purely combinatorial
  in the family + its finite intersections.
- **Project's current path / reasoning**: the augmentation target `image(cechFreeAug)` is the
  "locally `O_X` on `⨆ U_i`, else `0`" presheaf; objectwise quasi-iso is contractible when
  `I₁(V) = {i : V ≤ U_i} ≠ ∅` and zero when empty — purely about `V` vs `⨆ U_i`, never `⊤`.
- **Gap**: identical (the project's cover-agnostic reasoning matches Mathlib precedent).
- **Verdict**: PROCEED — re-parameterization is sound; `[Finite ι]` is the only needed
  hypothesis (finite coproducts of shape `Fin(p+1) → ι` and evaluation-preserves-coproduct as a
  finite colimit; also the downstream protected `cech_computes_higherDirectImage` finiteness).
  Note `cechComplexFunctor` needs only `HasFiniteProducts C` (not `Finite ι`) because it uses
  *products*; the free side needs `Finite ι` because it uses *finite coproducts/evaluation*.

### Decision Q1-C: replace the bespoke `cechFreeSimplicial` with `FormalCoproduct.cech`?

- **Mathlib idiom**: `FormalCoproduct.cech` + a functor `FormalCoproduct (Opens X) → X.PresheafOfModules`
  (sending `∐ U_i ↦ ⊕ freeYoneda(U_i)`) would reconstruct `cechFreeSimplicial` from library parts.
- **Project's current path**: bespoke `cechFreeSimplicial`/`cechFreePresheafComplex`, **already
  built, axiom-clean, with `cechFreeComplex_quasiIso` proven** (memory: p3b-freecomplex-built,
  p3b-engine-complex-built).
- **Gap**: divergent-with-cost, but the cost of *aligning now* (rebuilding the quasi-iso, engine
  homotopy, hom-identification on top of `FormalCoproduct`) far exceeds the cost of keeping it.
- **Verdict**: DIVERGE_INTENTIONALLY — keep the proven bespoke construction; record the parallel
  API. `cechComplexFunctor` (section side) is likewise a parallel to the already-proven
  `sectionCechComplex`; do not refactor proven code. Revisit only if a future Mathlib bump exposes
  a `FormalCoproduct`-based comparison that subsumes the bridge work.

### Decision Q2-A: idiom for "epi of `X.Modules` ⟹ local section surjectivity"

- **Mathlib idiom**: `CategoryTheory.Presheaf.IsLocallySurjective J f` (class) —
  `Mathlib/CategoryTheory/Sites/LocallySurjective.lean:94` — `imageSieve f s ∈ J U` for every
  section `s`. Companions: `imageSieve` (49), `imageSieve_mem` (97), `localPreimage` (81),
  `app_localPreimage` (87, `f.app _ (localPreimage …) = G.map g.op s`). Topological specialization:
  `TopCat.Presheaf.IsLocallySurjective` — `Mathlib/Topology/Sheaves/LocallySurjective.lean:61`,
  defeq to `Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)`, with the **exact
  target form**:
  `isLocallySurjective_iff` (line 64):
  `IsLocallySurjective T ↔ ∀ U t, ∀ x ∈ U, ∃ V ≤ U, (∃ s, T.app s = t|_V) ∧ x ∈ V`
  — a per-point neighborhood with a local lift, which assembles into a cover `{V_x}` of `U`.
  Module wrapper: `PresheafOfModules.IsLocallySurjective` —
  `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean:190`.
  epi ⟺ locally-surjective for `Sheaf J A` (concrete `A`):
  `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'` — `Mathlib/CategoryTheory/Sites/EpiMono.lean:123`;
  topological version `TopCat.Sheaf.isLocallySurjective_iff_epi` —
  `Mathlib/Topology/Sheaves/LocallySurjective.lean:125`.
- **Project's current path**: `ses_cech_h1` (CechBridge:658) already takes the local lifts
  `sLoc i : G(U_i)` + `hlift` as *hypotheses*; the affine `BasisCovSystem.surj_of_vanishing`
  instantiation must *produce* them. No idiom is currently chosen for that production.
- **Gap**: divergent-with-cost (if produced ad hoc) vs. align (use `IsLocallySurjective`).
- **Verdict**: ALIGN_WITH_MATHLIB — obtain `Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
  ((Scheme.Modules.toPresheaf X).map S.g)`, then extract the lifts via
  `TopCat.Presheaf.isLocallySurjective_iff` to feed `ses_cech_h1`'s `sLoc`/`hlift`.

### Decision Q2-B: the bridge `Epi (X.Modules) ⟹ IsLocallySurjective` — what's actually missing

- **Verified in Lean (iter-030)**: for `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat` ALL the
  hypotheses of `isLocallySurjective_iff_epi'` are present as instances:
  `HasSheafify`, `HasSheafCompose (forget _)`, `Balanced`, `WEqualsLocallyBijective`,
  `HasFunctorialSurjectiveInjectiveFactorization`. So
  `Sheaf.isLocallySurjective_iff_epi'` is directly usable on the underlying Ab-sheaf morphism.
- **The single genuine gap**: `(SheafOfModules.toSheaf X.ringCatSheaf).PreservesEpimorphisms`
  (equivalently `Epi g → Epi (toSheaf.map g)`) is **NOT** an available instance (verified:
  `infer_instance` fails). `toSheaf` is known `Additive`, `Faithful`, `PreservesFiniteLimits`
  (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean:118`) but NOT `PreservesFiniteColimits`.
  `Scheme.Modules.toPresheaf`/`toPresheafOfModules` is a **right adjoint**
  (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:67`) so does NOT preserve epi/colimits on its own;
  the epi must be transferred at the **sheaf** level via `toSheaf`. Mathematically `toSheaf`
  (underlying abelian sheaf) IS exact (kernels/cokernels of sheaves of modules are computed on the
  underlying abelian sheaves, stalkwise), so the fact is true — it is simply unpackaged in Mathlib.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (small, project-local) — prove
  `(toSheaf).PreservesEpimorphisms` (route: show `PreservesFiniteColimits`/right-exactness of the
  underlying-abelian-sheaf functor, or transfer epi through the sheafification adjunction). Once it
  lands, the rest is two `rw`/`exact` steps + `isLocallySurjective_iff`. Alternative route avoiding
  it: stalks — `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks`
  (`Mathlib/Topology/Sheaves/LocallySurjective.lean:80`) + epi-on-stalks; but that needs the same
  exactness fact phrased stalkwise, so the `toSheaf` epi-preservation lemma is the cheapest.

### Decision Q2-C: refine the cover to basic/affine opens

- **Mathlib idiom**: `Scheme.isBasis_affineOpens (X) : Opens.IsBasis X.affineOpens`
  (`Mathlib/AlgebraicGeometry/AffineScheme.lean:297`); `isBasis_basicOpen (X) [IsAffine X]`
  (line 317). Refine any open cover `{V_x}` to basic/affine opens via
  `Opens.IsBasis.exists_subset_of_mem_open` (used at AffineScheme.lean:617,996).
- **Verdict**: PROCEED — the `{V_x}` cover from `isLocallySurjective_iff` can be shrunk to
  affine/basic opens contained in each `V_x` (restricting the lift along `W ≤ V_x`), matching the
  standard-cover faces `BasisCovSystem.faces_mem` consumes.

## Recommendation

**Q1**: re-parameterize `FreePresheafComplex.lean` to `{ι : Type} [Finite ι] (U : ι → Opens X)`,
keeping `X.OpenCover` callers as one-line wrappers passing `coverOpen 𝒰`. This is endorsed by
Mathlib's raw-family `cechComplexFunctor`/`FormalCoproduct.cech` (no covering hypothesis) and by
the project's own already-raw-family section side; it removes the `OpenCover`/raw-family impedance
mismatch and the spurious `⨆ = ⊤` constraint. Keep the bespoke `cechFreeSimplicial` (proven
axiom-clean) rather than rebuilding on `FormalCoproduct.cech`.

**Q2**: produce the `ses_cech_h1` local-lift inputs through `Presheaf.IsLocallySurjective`
+ `TopCat.Presheaf.isLocallySurjective_iff`, refined to affine opens via `Scheme.isBasis_affineOpens`.
The only new obligation is the bridge lemma `(SheafOfModules.toSheaf X.ringCatSheaf).PreservesEpimorphisms`
(`Epi g → Epi (toSheaf.map g)`); every other instance and lemma in the chain already exists.
A prover should target, in order:
1. `lemma toSheaf_preservesEpi` (or instance) — `Epi g (X.Modules) → Epi ((SheafOfModules.toSheaf _).map g)`.
2. `Sheaf.isLocallySurjective_iff_epi' _ |>.mpr` → `Sheaf.IsLocallySurjective (toSheaf.map g)`
   (defeq `Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) ((Scheme.Modules.toPresheaf X).map g)`).
3. `TopCat.Presheaf.isLocallySurjective_iff` to extract per-point `(V, s)` lifts; assemble the
   cover `{V_x}` (refined via `Scheme.isBasis_affineOpens`) into `ses_cech_h1`'s `sLoc`/`hlift`.
