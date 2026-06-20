# Analogy: the two "deep categorical bridge" residuals of P5a

## Mode
api-alignment

## Slug
deepbridge

## Iteration
054

## Question
Two ACTIVE prover lanes have each collapsed to a "deep categorical bridge" residual (the same
family that has kept `CechAcyclic.affine` open). Find the Mathlib idiom for each so the next lane
builds the aligned version. (1) Lane 1 `cechAugmented_exact`: from a `Homotopy (𝟙 C) 0` on a
section cochain complex of `AddCommGrp`, get `IsZero (C.homology p)`, and the cleanest way to
obtain that homotopy (incl. whether `ExtraDegeneracy` applies). (2) Lane 2 open-immersion
`f_*`-acyclicity: identify objectwise homology of a pushed-forward injective resolution with the
`Ext`-based absolute cohomology presheaf.

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/CechAugmentedResolution.lean:164-180` — the `hSec` `sorry`: residual
  `IsZero (((GV.mapHomologicalComplex cc).obj Kp).homology p)`, `GV = toPresheaf ⋙ evaluation(op V)`,
  `Kp = (forget ⋙ restrictScalars α).mapHomologicalComplex (cechAugmentedComplex 𝒰 F)`, `V ≤ coverOpen 𝒰 i`.
- `AlgebraicJacobian/Cohomology/HigherDirectImagePresheaf.lean:131-167` — `pushforwardResolutionPresheafComplex`
  and `higherDirectImage_iso_sheafify_presheafHomology`; the hand-off identifying
  `(pushforwardResolutionPresheafComplex f I).homology n` (at `V`) with `V ↦ Hⁿ(f⁻¹V, G)`.
- `AlgebraicJacobian/Cohomology/AbsoluteCohomology.lean:30-71` — `jShriekOU`, `absoluteCohomology p U F
  := Ext (jShriekOU U) F p`, and corepresentability `jShriekOU_homEquiv : (jShriekOU U ⟶ F) ≃+ Γ(U,F)`.
- `AlgebraicJacobian/Cohomology/CechAcyclic.lean:136-461` — `CombinatorialCech.combHomotopy`/`combHomotopy_spec`
  (`d∘h+h∘d=id`) and the dependent port `depDiff_exact`.
- `AlgebraicJacobian/Cohomology/FreePresheafComplex.lean:83-100` — the project's OWN axiom-clean
  objectwise-contracting-homotopy precedent (`cechFreeComplex_quasiIso`), explicitly via
  `HomologicalComplex.Homotopy`, explicitly NOT via `ExtraDegeneracy`.

## Decisions identified

### Decision 1a: `Homotopy (𝟙 C) 0` ⟹ `IsZero (C.homology p)` — which exact lemma?
- **Mathlib idiom (CONFIRMED, real).** There is **no** single packaged lemma; the idiom is a 3-lemma
  combo, all present:
  - `Homotopy.homologyMap_eq (ho : Homotopy f g) (i) [HasHomology…] : homologyMap f i = homologyMap g i`
    — `Mathlib.Algebra.Homology.Homotopy`.
  - `HomologicalComplex.homologyMap_id (K) (i) : homologyMap (𝟙 K) i = 𝟙 (K.homology i)` and
    `HomologicalComplex.homologyMap_zero (K L) (i) : homologyMap 0 i = 0` —
    both `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`.
  - `IsZero.iff_id_eq_zero (X) : IsZero X ↔ 𝟙 X = 0` — `Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`
    (the project ALREADY uses this in `isZero_of_faithful_preservesZeroMorphisms`).
  So, given `h : Homotopy (𝟙 C) 0`:
  `(IsZero.iff_id_eq_zero _).mpr (by rw [← HomologicalComplex.homologyMap_id, h.homologyMap_eq p,
  HomologicalComplex.homologyMap_zero])`.
- **Refuted candidates.** `HomotopyEquiv.homologyIso` — does NOT exist by that name. The packaged
  alternative `HomotopyCategory.isZero_quotient_obj_iff : IsZero ((quotient).obj C) ↔ Nonempty (Homotopy
  (𝟙 C) 0)` (`Mathlib.Algebra.Homology.HomotopyCategory`) gives `IsZero` only in the HOMOTOPY category;
  recovering `IsZero (C.homology p)` then needs `homologyFunctorFactors`-style plumbing — MORE work than
  the direct combo. `homotopyEquivalences_le_quasiIso` (`Mathlib.Algebra.Homology.QuasiIso`) +
  `HomologicalComplex.isZero_zero` also works (HomotopyEquiv C 0 ⟹ quasiIso to 0 ⟹ homology ≅ homology 0
  = 0) but is heavier.
- **Gap**: identical — no parallel API. **Verdict: PROCEED** (use the 3-lemma combo).

### Decision 1b: obtaining the `Homotopy` — direct field-build vs concrete-complex+`combHomotopy_spec`; ExtraDegeneracy?
- **ExtraDegeneracy: REFUTED by variance (do NOT use).** The ONLY `ExtraDegeneracy` in Mathlib is
  `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`
  (`Mathlib.AlgebraicTopology.ExtraDegeneracy`): it yields a `HomotopyEquiv (AlternatingFaceMapComplex.obj
  (drop X)) ((ChainComplex.single₀ C).obj (point X))` — a **ChainComplex** (homological, simplicial FACE
  maps). The project's `cechAugmentedComplex` is a **CochainComplex** (`ComplexShape.up ℕ`, alternating
  COFACE). No cosimplicial/cochain `ExtraDegeneracy` exists. Confirms project memory + the explicit
  DEAD-END notes in both `CechAcyclic.lean:57-59` and `FreePresheafComplex.lean:98-99`.
- **Aligned idiom (CONFIRMED via project's OWN precedent).** Build a `HomologicalComplex.Homotopy (𝟙 D) 0`
  DIRECTLY on the concrete section cochain complex `D`, exactly as the axiom-clean
  `cechFreeComplex_quasiIso` does (FreePresheafComplex.lean:83-100, "Package as `HomologicalComplex.Homotopy`").
  The two directive sub-routes COINCIDE in practice: you cannot fill the `Homotopy.hom` fields of the
  abstract `(GV.mapHomologicalComplex cc).obj Kp` without concrete maps, and the concrete maps ARE the
  prepend homotopy `combHomotopy i_fix`; its relation field is discharged by `combHomotopy_spec`
  (`d∘h + h∘d = id`, CechAcyclic.lean:172). So the recipe is route (ii): (a) identify
  `(GV.mapHomologicalComplex cc).obj Kp` with the concrete cochain complex `D = ∏_σ Γ(coverInter σ ⊓ V, F)`
  via `Functor.mapHomologicalComplex` naturality + a degreewise iso; (b) build `Homotopy (𝟙 D) 0` from
  `combHomotopy`/`combHomotopy_spec`; (c) close with the 1a combo.
- **Coefficient note (which combinatorial core).** Because `V ≤ coverOpen 𝒰 i_fix`, the prepended index
  satisfies `coverInter (cons i_fix σ) ⊓ V = coverInter σ ⊓ V` (as `V ≤ U_{i_fix}`), so the PREPEND map on
  sections is the identity. This is the "`c = id`" specialisation of the dependent core
  (`CombinatorialCech.Dependent.depDiff_exact`, `hu` trivial), or — if the per-`V` term is modelled with a
  single constant group — the constant `combHomotopy_spec` directly. Prover's choice; both cores are
  already axiom-clean. This is why the file comment calls it "F-agnostic, cover-agnostic".
- **Gap**: the section-complex IDENTIFICATION (step a) is the SAME L1-bridge family as `CechAcyclic.affine`
  (see `[[l1-bridge]]`): `Functor.mapHomologicalComplex` naturality + per-degree `Γ(V,-)`-of-products iso.
  The `Homotopy` packaging itself is free.
  **Verdict: PROCEED on the packaging idiom (`HomologicalComplex.Homotopy` + `combHomotopy_spec` + 1a combo);
  NEEDS_MATHLIB_GAP_FILL only for the section-complex identification (project L1 work, not a Mathlib call).**

### Decision 2a: objectwise homology of `F.mapHomologicalComplex I.cocomplex` ↔ `rightDerived n`/`Ext`
- **Mathlib idiom (CONFIRMED, real, ALREADY USED).**
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj (I : InjectiveResolution X) (F) [F.Additive] (n) :
  (F.rightDerived n).obj X ≅ (homologyFunctor D (up ℕ) n).obj ((F.mapHomologicalComplex (up ℕ)).obj
  I.cocomplex)` — `Mathlib.CategoryTheory.Abelian.RightDerived`. The project already consumes this at
  HigherDirectImagePresheaf.lean:164. So `(F.mapHomologicalComplex I.cocomplex).homology n ≅
  (F.rightDerived n).obj X` is settled.
- **Evaluation-at-`V` commutes (CONFIRMED).** `evaluation` of presheaves is exact ((co)limits objectwise),
  hence `[Additive] [PreservesHomology]`; the project already applies its `Functor.mapHomologyIso'` to
  `GV` (CechAugmentedResolution.lean:173) and to `sheafification`. Not a gap.
- **Gap**: identical. **Verdict: PROCEED.**

### Decision 2b: `Ext^n(X,Y)` (inj. res. of 2nd arg) ↔ `Hⁿ(Hom(X, I^•))` (cohomology of Hom-into-resolution)
- **Mathlib idiom (CONFIRMED, real — this is THE bridge).**
  - `CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass (R : InjectiveResolution Y) {n} :
    Ext X Y n ≃+ CochainComplex.HomComplex.CohomologyClass ((CochainComplex.singleFunctor C 0).obj X)
    R.cochainComplex ↑n` — `Mathlib.CategoryTheory.Abelian.Injective.Ext` (plain `Equiv`:
    `extEquivCohomologyClass`).
  - `CochainComplex.HomComplex.homologyAddEquiv (K L) (n) : ↑(HomologicalComplex.homology (K.HomComplex L)
    n) ≃+ CohomologyClass K L n` — `Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology`.
  - Compose ⟹ `Ext X Y n ≃+ Hⁿ(Hom((singleFunctor 0).obj X, R.cochainComplex))`, i.e.
    **`Ext^n(X,Y) = Hⁿ(Hom(X, I^•))`** with `I^•` an injective resolution of `Y` (the SECOND argument) —
    exactly the requested H⁰=Hom + derived-functor-agree statement, packaged.
- **Closing the project hand-off.** With `X = jShriekOU (f⁻¹V)`, `Y = G`:
  the degree-`k` Hom group `Hom(jShriekOU(f⁻¹V), I^k)` is identified with `Γ(f⁻¹V, I^k) = (f_* I^k)(V)` by
  the project's corepresentability `jShriekOU_homEquiv : (jShriekOU U ⟶ F) ≃+ Γ(U,F)`
  (AbsoluteCohomology.lean:50). Degreewise + naturally ⟹ the Hom-complex IS (iso to) the section/pushforward
  complex `(pushforwardResolutionPresheafComplex f I)(V)`, so `Ext^n(jShriek(f⁻¹V),G) ≅
  (pushforwardResolutionPresheafComplex f I).homology n` at `V`. This closes HigherDirectImagePresheaf.lean:131-157.
- **Reindexing friction (minor, Mathlib supplies the iso).** `Ext`/`HomComplex` use the ℤ-indexed
  `R.cochainComplex : CochainComplex C ℤ`; `isoRightDerivedObj` and the project's
  `pushforwardResolutionPresheafComplex` use the ℕ-indexed `I.cocomplex : CochainComplex C ℕ`. Bridge:
  `CategoryTheory.InjectiveResolution.cochainComplexXIso (R) (n:ℤ) (k:ℕ) (h:↑k=n) : R.cochainComplex.X n ≅
  R.cocomplex.X k` — `Mathlib.CategoryTheory.Abelian.Injective.Extend`. Also `R.ι'`,
  `instIsStrictlyGECochainComplex…`, `instIsLE…` for the extension bookkeeping.
- **`rightDerived ↔ Ext` is NOT a separately-needed bridge.** Both frameworks compute as `Hⁿ` over the
  SAME injective resolution: `(pushforward f).rightDerived` applied to `I.cocomplex` gives the section
  complex via `f_* I = Γ(f⁻¹·, I)`; `Ext` of `jShriekOU` gives Hom-into-resolution = sections via
  corepresentability. They agree precisely because `Γ(f⁻¹V,-) = Hom(jShriekOU(f⁻¹V), -)`. The meeting point
  is corepresentability, already built — no abstract `rightDerived = Ext` comparison lemma is forced.
- **Gap**: divergent-equivalent — two derived-functor frameworks (`rightDerived` for `Rⁱf_*`, `Ext` for
  absolute `H^p`) but their agreement rides on the existing `jShriekOU_homEquiv`, not a new lemma.
  **Verdict: PROCEED** (use `extAddEquivCohomologyClass` ∘ `homologyAddEquiv` + `jShriekOU_homEquiv` +
  `cochainComplexXIso`).

## Recommendation
Both residuals are **PROCEED with off-the-shelf Mathlib idioms**, NOT new-infrastructure walls.

- **Lane 1 (`cechAugmented_exact` `hSec`):** the `Homotopy ⟹ IsZero` step is the 3-lemma combo
  `Homotopy.homologyMap_eq` + `homologyMap_id` + `homologyMap_zero` + `IsZero.iff_id_eq_zero`. Obtain the
  homotopy by mirroring the project's OWN `cechFreeComplex_quasiIso` precedent: identify
  `(GV.mapHomologicalComplex cc).obj Kp` with a concrete `∏_σ Γ(coverInter σ ⊓ V, F)` cochain complex,
  then `HomologicalComplex.Homotopy (𝟙 D) 0` whose `hom` fields are `combHomotopy i_fix`, relation via
  `combHomotopy_spec`. Do NOT route through `ExtraDegeneracy` (wrong variance — chain vs cochain — no
  cosimplicial dual). The only residual is the L1-style section-complex identification (`[[l1-bridge]]`).
- **Lane 2 (open-immersion `f_*`-acyclicity hand-off):** keep absolute cohomology as `Ext^n(jShriekOU U, G)`
  (already shipped). Bridge to the presheaf homology via `extAddEquivCohomologyClass` ∘
  `homologyAddEquiv.symm` (giving `Ext^n ≅ Hⁿ(Hom(X[0], I^•))`), then the project's corepresentability
  `jShriekOU_homEquiv` degreewise to turn the Hom-complex into the section/pushforward complex, with
  `cochainComplexXIso` matching ℕ/ℤ indexing. `isoRightDerivedObj` (already used) handles the
  `rightDerived` side. No `rightDerived = Ext` comparison lemma is needed.

## Related analogies
- [[l1-bridge]] — the section/Čech-term identification (`Functor.mapHomologicalComplex` naturality + per-`V`
  product iso) that Lane 1's homotopy step still needs; same family.
- [[absolute-cohomology]] — establishes `H^p(U,F) := Ext^p(jShriekOU U, F)` and the corepresentability
  `jShriekOU_homEquiv` that Lane 2's bridge consumes.

---
*Iteration: 054*
