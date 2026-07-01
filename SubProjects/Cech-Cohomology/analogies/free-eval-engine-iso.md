# Analogy: free-complex differential match + Homotopy→QuasiIso packaging

## Mode
api-alignment

## Slug
freeeval

## Iteration
022

## Question
The Mathlib-aligned idiom for (1) a degreewise iso of `HomologicalComplex` whose terms are
coproducts pinned on injections, (2) pushing `evaluation` through `∐`, (3) turning the
contracting homotopy `dh+hd=id` into `QuasiIso` of the augmentation, and (4) whether the
hand-rolled `FreeCechEngine` should be replaced by `AlgebraicTopology.ExtraDegeneracy`.

## Project artifact(s)
- `FreePresheafComplex.lean:201` — `cechFreePresheafComplex` (chain cplx, deg `p` = `∐_{σ:Fin(p+1)→I₀} freeYoneda(U_σ)`).
- `FreePresheafComplex.lean:340` — `cechFreeComplexAug` : `K(𝒰)• ⟶ (single₀).obj (coverStructurePresheaf 𝒰)`.
- `FreePresheafComplex.lean:414` — `quasiIso_of_evaluation` (objectwise reduction, axiom-clean).
- `FreePresheafComplex.lean:452` — `FreeCechEngine.combDifferential` (raises Fin-arity; the Čech *coboundary*).
- `FreePresheafComplex.lean:477` — `combHomotopy_spec` (`dh+hd=id`).
- `FreePresheafComplex.lean:543` — `combDifferential_exact` (**`Function.Exact`**, already proven).
- `FreePresheafComplex.lean:574` — `cechFreeEval_X` (evaluation-preserves-coproduct iso; **already** `PreservesCoproduct.iso`).
- `FreePresheafComplex.lean:594/612` — `freeYonedaEval_isZero_of_not_le` / `freeYonedaEval_iso_of_le`.
- `CechAcyclic.lean:1247` — `sectionCech_isZero_homology_of_objD_exact` (the in-project homotopy→homology **precedent**).

## Decisions identified

### Decision: degreewise iso of a coproduct-termed `HomologicalComplex` (Q1)

- **Mathlib idiom**: `HomologicalComplex.Hom.isoOfComponents`
  (`Mathlib.Algebra.Homology.HomologicalComplex`):
  `(f : ∀ i, C₁.X i ≅ C₂.X i) → (hf : ∀ i j, c.Rel i j → (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom := by cat_disch) → C₁ ≅ C₂`.
  Companions `isoOfComponents_hom_f` / `isoOfComponents_inv_f` (the degreewise `.hom.f i = (f i).hom`).
  The `comm` for a coproduct-termed differential is discharged on injections:
  `Limits.Sigma.hom_ext` (already used in-file at lines 167/293/625), then
  `Limits.Sigma.ι_comp_map'` / `Limits.Sigma.ι_map` / `Limits.Sigma.ι_desc`
  (`Mathlib.CategoryTheory.Limits.Shapes.Products`).
- **Project's current path**: not yet built (`cechFreeEvalEngineIso` never attempted).
- **Gap**: identical — this is exactly the idiom to use.
- **Verdict**: ALIGN_WITH_MATHLIB.

The per-degree iso itself factors as
`(eval V).obj (K(𝒰)_p)  ≅[cechFreeEval_X]  ∐_{σ:Fin(p+1)→I₀} (eval V).obj(freeYoneda U_σ)
   ≅[drop-zeros]  ∐_{σ : V≤U_σ} (eval V).obj(freeYoneda U_σ)
   ≅[whiskerEquiv + freeYonedaEval_iso_of_le]  ∐_{σ:Fin(p+1)→I₁(V)} O_X(V) = C•_p`.

- The reindex `{σ:Fin(p+1)→I₀ | V≤U_σ} ≃ (Fin(p+1)→I₁(V))` + per-summand iso is
  **`CategoryTheory.Limits.Sigma.whiskerEquiv`** (`e : J≃K`, `w : ∀ j, g(e j)≅f j`),
  with `freeYonedaEval_iso_of_le` as `w`.
- **drop-zeros** (∐ over `Fin(p+1)→I₀` ≅ ∐ over the surviving subtype, complement summands
  `IsZero` by `freeYonedaEval_isZero_of_not_le`) has **no single Mathlib lemma**. `whiskerEquiv`
  needs a *bijection* of index types, which the I₀→survivors restriction is not. Build it by hand:
  `Sigma.desc`/`Sigma.ι` + `Sigma.hom_ext`, using `(freeYonedaEval_isZero_of_not_le …).eq_zero_of_src`
  to kill complement injections (pattern already in `isZero_sigma_of_forall_isZero`, line 621).
  This small iso is the only piece of Q1 without a named lemma.

### Decision: evaluation through `∐` + `mapHomologicalComplex` (Q2)

- **Mathlib idiom**: `Limits.PreservesCoproduct.iso F f : F.obj (∐ f) ≅ ∐ (fun b => F.obj (f b))`
  given `PreservesColimitsOfShape (Discrete _) F`.
- **Project's current path**: **already done** — `cechFreeEval_X` (line 574) is literally
  `PreservesCoproduct.iso _ _` under
  `PresheafOfModules.Finite.evaluation_preservesFiniteColimits` (`𝒰.I₀` finite ⇒ `Fin(p+1)→I₀` finite).
- **Gap**: identical. No need to thread `mapHomologicalComplex` by hand:
  `((F.mapHomologicalComplex c).obj K).X p` is defeq `F.obj (K.X p)` and its `.d` is `F.map (K.d)`,
  so feeding `cechFreeEval_X p` per degree into `isoOfComponents` is the whole story.
  (There is no need for `preservesColimitIso`/`ι_preservesColimitsIso_hom` — `PreservesCoproduct.iso`
  is the discrete-shape specialization the project already picked.)
- **Verdict**: PROCEED (already aligned).

### Decision: contracting homotopy ⟹ QuasiIso packaging (Q3)

Two valid Mathlib routes; the project should prefer the second because it is the project's own
axiom-clean precedent and directly consumes the already-proven `combDifferential_exact`.

- **Route A (HomotopyEquiv)**: `HomotopyEquiv.quasiIso_hom`
  (`Mathlib.Algebra.Homology.QuasiIso`) is an **instance**: given `e : HomotopyEquiv K L`,
  `QuasiIso e.hom` is automatic (there is *no* `HomotopyEquiv.toQuasiIso` / `Homotopy.toQuasiIso`
  lemma — it is the instance). Cost: you must first repackage `combHomotopy`/`combHomotopy_spec`
  into a genuine `HomologicalComplex.Homotopy` structure (degreewise `hom` components + the
  `comm` relation) and exhibit both maps of the equivalence. This is real repackaging work that
  duplicates what `combDifferential_exact` already encodes.

- **Route B (Function.Exact — RECOMMENDED, mirrors `CechAcyclic.sectionCech_isZero_homology_of_objD_exact`)**:
  positive-degree vanishing of `C•` via
  `HomologicalComplex.exactAt_iff_isZero_homology`  (CechAcyclic.lean:1254)
  → `HomologicalComplex.exactAt_iff'`  (`K.exactAt j ↔ (K.sc' i j k).Exact`)
  → `CategoryTheory.ShortComplex.moduleCat_exact_iff_function_exact`
     (`Mathlib.Algebra.Homology.ShortComplex.ModuleCat` — the ModuleCat analogue of the
      `ab_exact_iff_function_exact` used on the section side)
  → feed `FreeCechEngine.combDifferential_exact`.
  Degree-0 `H₀(C•) ≅ M` (= `O_𝒰(V)`) from `combHomotopy_spec` at `n=0`.
  Read off degree-0 via `ChainComplex.toSingle₀Equiv` (already used at line 343) /
  `ChainComplex.of` for building `C•` with `combDifferential_comp` (d²=0).

- **Transfer to the evaluated augmentation**: build
  `e : Arrow.mk ((eval V).mapHC.map (cechFreeComplexAug 𝒰)) ≅ Arrow.mk (combAug)` from
  `cechFreeEvalEngineIso` (source square) + the degree-0 target iso `coverStructurePresheaf(V) ≅ M`,
  then `quasiIso_of_arrow_mk_iso` / `quasiIso_iff_of_arrow_mk_iso`
  (`Mathlib.Algebra.Homology.QuasiIso`; also the instance
  `HomologicalComplex.instRespectsIsoQuasiIso`) transports `QuasiIso combAug` to the evaluated
  augmentation. Finally `quasiIso_of_evaluation` (line 414, already axiom-clean) lifts per-`V`
  to the presheaf statement.
- **Verdict**: ALIGN_WITH_MATHLIB (Route B), with Route A noted as the fallback.

### Decision: engine vs `ExtraDegeneracy` refactor (Q4)

- **Mathlib idiom considered**: `AlgebraicTopology.ExtraDegeneracy` /
  `SimplicialObject.Augmented` / `Rep.standardComplex` (bar resolution).
- **Project's current path**: hand-rolled `FreeCechEngine` (constant-coeff contracting homotopy),
  axiom-clean and reused (`combDifferential`, `combHomotopy`, `combHomotopy_spec`,
  `combDifferential_comp`, `combDifferential_exact`).
- **Gap**: divergent-and-justified. `ExtraDegeneracy` has been investigated and rejected **twice**
  in this codebase: `FreePresheafComplex.lean:92-93` ("DEAD END — do NOT route through
  `SimplicialObject.Augmented.ExtraDegeneracy`. That interface has a different index convention")
  and `CechAcyclic.lean:58` ("Do NOT route through Mathlib's simplicial `ExtraDegeneracy` (wrong
  variance — chain vs. cochain — and no cosimplicial dual exists in Mathlib)"). The per-`V`
  evaluated object is a *coproduct of `ModuleCat`s*, not literally a Mathlib (co)simplicial object
  with the right variance; wiring it into `ExtraDegeneracy` would require first reconstructing the
  augmented simplicial object and matching its index convention — strictly more work than the
  engine, which already exists and is axiom-clean.
- **Cost of NOT refactoring**: none beyond keeping ~100 lines of `FreeCechEngine` (already paid).
  Cost of refactoring: re-deriving the contraction through an interface twice-found inapplicable,
  discarding axiom-clean code.
- **Verdict**: DIVERGE_INTENTIONALLY — commit to the engine route.

## Recommendation

Build `cechFreeEvalEngineIso` with `HomologicalComplex.Hom.isoOfComponents`, per-degree iso =
`cechFreeEval_X p` (≅ already `PreservesCoproduct.iso`) ≫ a hand-built *drop-zeros* iso (kill
`V≰U_σ` summands via `freeYonedaEval_isZero_of_not_le` + `Sigma.hom_ext`) ≫ `Sigma.whiskerEquiv`
with `freeYonedaEval_iso_of_le`, landing on `C•_p = ∐_{Fin(p+1)→I₁(V)} O_X(V)`. Prove the `comm`
square on `Sigma.ι` with `Sigma.hom_ext` + `Sigma.ι_comp_map'`/`ι_desc`.

**The genuine bottleneck is the differential variance match, not the packaging.** The free chain
differential *lowers* Fin-arity (`σ ↦ σ∘δ_i`, faces) while `combDifferential` *raises* it
(`fun σ => Σ_j (-1)^j t(σ∘j.succAbove)`); they reconcile on the finite biproduct `∐ M = ∏ M`
(self-dual over a finite index) where the injection-indexed face differential
`ι_σ ↦ Σ_i (-1)^i (incl) ≫ ι_{σ∘δ_i}` is exactly the transpose of `combDifferential`, and
`δ_i.toOrderHom = Fin.succAbove i`. Prove the match degreewise on `Sigma.ι` (this is the line the
directive flagged). Then package QuasiIso via **Route B** (`exactAt_iff'` +
`moduleCat_exact_iff_function_exact` + `combDifferential_exact`, mirroring
`sectionCech_isZero_homology_of_objD_exact`), transfer with `quasiIso_of_arrow_mk_iso`, and lift
with `quasiIso_of_evaluation`. Do **not** refactor onto `ExtraDegeneracy`.
