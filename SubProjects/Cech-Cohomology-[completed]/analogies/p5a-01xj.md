# Analogy: P5a Čech↔higher-direct-image comparison layer (Stacks 01XJ + acyclicity)

## Mode
api-alignment

## Slug
p5a-01xj

## Iteration
011

## Question
For the P5a layer (the four to-be-built lemmas `higherDirectImage_isSheafify_presheafCohomology`,
`cechAugmented_exact`, `higherDirectImage_openImmersion_comp`, `cechTerm_pushforward_acyclic`),
what is Mathlib's idiom, where does the proposed shape risk a parallel API, and what is the cost of
misalignment? Give a self-contained route that does NOT rely on the (dropped) presheaf δ-functor
formalism.

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/HigherDirectImage.lean:47` — `higherDirectImage f i F =
  ((pushforward f).rightDerived i).obj F`, needs `[HasInjectiveResolutions X.Modules]`.
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean:771` — `cech_computes_higherDirectImage`
  (PROTECTED, frozen sig), proved by **Route A**: augmented Čech complex is a termwise
  `f_*`-acyclic resolution → feed P4 `rightDerivedIsoOfAcyclicResolution`.
- `AlgebraicJacobian/Cohomology/AcyclicResolution.lean:893` — `Functor.rightDerivedIsoOfAcyclicResolution`
  (project P4 engine, the consumer of the P5a outputs); `:155` `Functor.IsRightAcyclic`.
- `AlgebraicJacobian/Cohomology/CechAcyclic.lean:74` — `CechAcyclic.affine` (P3, affine standard-cover
  vanishing, the bottom of the `cechAugmented_exact` reduction; `sorry`).
- blueprint `Cohomology_CechHigherDirectImage.tex` blocks `:1455`, `:1433`, `:1519`, `:1610`.

## Key Mathlib map (verified via source, paths under `…/mathlib/Mathlib/`)
- `CategoryTheory.Sheaf.H (n)` — `CategoryTheory/Sites/SheafCohomology/Basic.lean:58`. Sheaf
  cohomology `Hⁿ` of an abelian sheaf, defined as `Ext` from the constant sheaf `ℤ`. **Only for
  `Sheaf J AddCommGrpCat`**, with `[HasSheafify]`+`[HasExt]`.
- `CategoryTheory.Sheaf.cohomologyPresheafFunctor (n)` / `cohomologyPresheaf` / `Sheaf.H'` —
  `…/Basic.lean:90,99,105`. **`cohomologyPresheaf F n : Cᵒᵖ ⥤ AddCommGrpCat` is literally the
  presheaf `U ↦ Hⁿ(U, F)`** and `Sheaf.H' F n X = Hⁿ(X, F)`. This is the exact shape 01XJ's
  `V ↦ Hⁱ(f⁻¹V, F)` wants — but in `Sheaf J AddCommGrpCat`, not `SheafOfModules`.
- `CategoryTheory.Sheaf.Γ` — `CategoryTheory/Sites/GlobalSections.lean:64`. Global-sections functor
  (right adjoint of constant sheaf). `Sheaf.H` is defined via `Ext`, NOT as `Γ.rightDerived`; no
  `Sheaf.H ≅ Γ.rightDerived` comparison is shipped.
- `CategoryTheory.Sites.SheafCohomology.cechComplexFunctor` — `…/SheafCohomology/Cech.lean:65`. A Čech
  complex *of a presheaf valued in A* over a family `U : ι → C`. Generic site Čech, not the relative
  scheme construction.
- `AlgebraicGeometry.Scheme.Modules` — `AlgebraicGeometry/Modules/Sheaf.lean:37` = `SheafOfModules
  X.ringCatSheaf`. `Abelian X.Modules` (`:48`), `pushforward` (`:151`, `Additive` `:182`, right
  adjoint `:181`), forgetful `toPresheaf : X.Modules ⥤ TopCat.Presheaf Ab X` (`:72`),
  `pushforwardComp : pushforward f ⋙ pushforward g ≅ pushforward (f≫g)` with
  `_hom_app_app = 𝟙` by `rfl` (`:210,214`).
- `SheafOfModules.toSheaf` / evaluation **preserve finite limits** —
  `Algebra/Category/ModuleCat/Sheaf/Limits.lean:98,118`. Sheafification is a left adjoint, so also
  preserves colimits ⇒ preserves homology. This is the engine behind "cohomology sheaf =
  sheafify(objectwise cohomology)".
- `Functor.PreservesInjectiveObjects` + `preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`
  — `CategoryTheory/Preadditive/Injective/Preserves.lean:30,49`. Right adjoint of a mono-preserving
  (exact) functor preserves injectives. Gives "`(j_s)_*` preserves injectives" (pullback/restriction
  is exact) for the acyclic-resolution argument.
- **ABSENT (verified by exhaustive grep):** no Grothendieck/Leray spectral sequence,
  no `R(g∘f)_* ≅ Rg_* ∘ Rf_*`, no `Functor.rightDerived` of a *composite of functors*; no
  `HasInjectiveResolutions`/`EnoughInjectives`/`IsGrothendieckAbelian` instance for any sheaf-of-modules
  category; no sheaf cohomology specialised to `TopCat`/schemes; no module-valued absolute cohomology.
  (`NatTrans.rightDerived_comp` exists but is derived-of-`α≫β` for nat-trans, not functor composition.)

## Decisions identified

### Decision 1 (Q1): Absolute cohomology `Hⁱ(f⁻¹V, F)` of an O_X-module over an open
- **Mathlib idiom**: `Sheaf.H' F i V` / `cohomologyPresheaf` (`…/SheafCohomology/Basic.lean:105,99`)
  for `Sheaf J AddCommGrpCat`; `Sheaf.Γ` (`GlobalSections.lean:64`). There is **no** `Hⁱ(open, F)`
  for `Scheme.Modules`/`SheafOfModules`.
- **Project's path (proposed)**: a bespoke `…presheafCohomology` over `O_X`-modules.
- **Gap**: divergent-with-cost. The Mathlib notion lives in a *different category* (AddCommGrp-valued
  site sheaves), so it is not a drop-in, but a freshly-named module cohomology would fork it.
- **Cost of divergence**: a parallel cohomology theory with zero lemmas — restriction-compatibility,
  Serre vanishing on affines, "cohomology unchanged under `j_*` along an open immersion", and the
  basis-local vanishing criterion would all have to be re-proved from scratch and could never consume
  Mathlib's `Sheaf.H`/`Ext` machinery.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL. Surrogates, in order of preference: (i) **avoid materialising a
  standalone `Hⁱ(open,F)`** — see Recommendation; (ii) if one is needed, define it as the
  underlying-abelian-sheaf cohomology via `toPresheaf`/`TopCat.Sheaf Ab` + Mathlib `Sheaf.H'` (plus the
  standard "O_X-module cohomology = abelian-sheaf cohomology" comparison); (iii) `(Γ_X-Modules.rightDerived i)`
  in `X.Modules`, requiring `[HasInjectiveResolutions X.Modules]`.

### Decision 2 (Q2): `Rⁱf_* = sheafify(V ↦ Hⁱ(f⁻¹V, F))` (01XJ)
- **Mathlib idiom**: none direct. The reusable building block is **"cohomology sheaf = sheafify of the
  objectwise/presheaf cohomology"**, available because sheafification (`SheafOfModules.toSheaf`,
  `…/Sheaf/Limits.lean:118`; evaluation `:98`) preserves finite limits and (being a left adjoint)
  colimits, hence preserves homology; `X.Modules` is `Abelian`.
- **Project's path**: blueprint proof builds the comparison "directly from injective resolutions"; the
  δ-functor sentence in block `:1511–1516` is now obsolete.
- **Gap**: divergent-with-cost only if forked; otherwise NEEDS_GAP_FILL (build).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL. Build via objectwise-homology + sheafification-preserves-homology;
  do **not** route through a δ-functor / universal-derived-functor characterisation.

### Decision 3 (Q3): Derived composition + open-immersion `(j_s)_*`-acyclicity
- **Mathlib idiom**: **no Grothendieck spectral sequence / `R(g∘f)_* = Rg_*∘Rf_*` exists** (verified
  absent). The project's blueprint route for `higherDirectImage_openImmersion_comp` part (2) already
  **avoids** it: it builds the `f_*`-acyclic resolution `j_* I^•` and invokes the project's P4
  `rightDerivedIsoOfAcyclicResolution` (`AcyclicResolution.lean:893`). Mathlib hook for "`(j_s)_*`
  preserves injectives": `preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`
  (`Injective/Preserves.lean:49`), since pullback/restriction is exact.
- **Gap**: the *math* (relative affine vanishing, `R^q j_* = 0`) is not in Mathlib.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL for the vanishing; **ALIGN on the route** — acyclic-resolution
  comparison, not a spectral sequence. Do not block P5a on a Grothendieck SS; do not build a bespoke
  `R(g∘f)` comparison when `pushforwardComp` (`rfl`) + P4 already give `f_*∘(j_s)_* = (g_s)_*`.

### Decision 4 (Q4): Augmented Čech complex of sheaves is exact (`cechAugmented_exact`)
- **Mathlib idiom**: `HomologicalComplex.ExactAt` / `QuasiIso` (state "exact in positive degrees" /
  "augmentation is a quasi-iso to `F[0]`"); no Čech-resolution-of-sheaves API. Exactness is local →
  reduce stalkwise / over an affine basis to the project's P3 `CechAcyclic.affine`
  (`CechAcyclic.lean:74`).
- **Relation to P3b**: P3b's `cechFreePresheafComplex` (free presheaves of modules, for the
  injective-acyclicity lane) is a **different object**; `cechAugmented_exact` is the sheaf-side complex
  `Cᵖ = ∏ (j_s)_*(F|_{U_s})` and bottoms out at P3 (affine vanishing), **not** P3b. They must stay
  distinct; no fork as long as the names/types distinguish presheaf-free vs sheaf-pushforward complexes.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (build with the `ExactAt`/`QuasiIso` idiom).

### Decision 5 (Q5): Parallel-API risk on the `…presheafCohomology` name
- **Risk**: `\lean{…higherDirectImage_isSheafify_presheafCohomology}` and any materialised
  `presheafCohomology` object fork Mathlib's `Sheaf.cohomologyPresheaf`/`Sheaf.H'`.
- **Verdict**: ALIGN_WITH_MATHLIB *direction*: if a presheaf-cohomology object is named at all, it
  should be (defeq to) the underlying-abelian-sheaf `cohomologyPresheaf`, or the lemma should be stated
  without a standalone object (Recommendation). The four `\lean{}` *names* are fine as project lemmas;
  the danger is only if they introduce a new **definition** of cohomology rather than a new **theorem**.

## Recommendation
Lock P5a as the lane that supplies the two hypotheses of the already-built P4
`rightDerivedIsoOfAcyclicResolution`: `cechAugmented_exact` ⟶ `hexact : ∀ n, K.ExactAt (n+1)`, and
`cechTerm_pushforward_acyclic` ⟶ `[∀ n, (pushforward f).IsRightAcyclic (Cᵖ)]`. That keeps the entire
comparison inside the project's existing acyclic-resolution engine and needs **no** Grothendieck
spectral sequence, **no** δ-functor, and **no** Mathlib sheaf-cohomology import.

For the 01XJ content, prefer the *narrowest* form the consumer actually needs: a **basis-local
vanishing criterion** `(pushforward f).rightDerived k G ≅ 0  ⇔  for every affine V, the k-th homology
of the A-module complex `(f_* I^•)(V) = I^•(f⁻¹V)` vanishes`, proved from "cohomology sheaf =
sheafify(objectwise homology)" (Decision 2 engine: `SheafOfModules.toSheaf` finite-limit-preserving,
`X.Modules` abelian) + "a sheaf is 0 iff its sections vanish on a basis". This avoids ever defining a
standalone module-valued `Hⁱ(open,F)` (Decision 1's fork) — the only absolute cohomology that appears
is `Hᵏ` of an explicit complex of `ModuleCat`, which Mathlib already has. If a self-contained
`Hⁱ(f⁻¹V,F)` object is later wanted for the blueprint statement, realise it through `toPresheaf` +
Mathlib `Sheaf.H'`, never as a new cohomology definition.

For `cechTerm_pushforward_acyclic`, exploit two Mathlib/project levers to shrink the work: the product
`Cᵖ = ∏ (j_s)_*(F|_{U_s})` reduces to a single factor (acyclicity is closed under products), and
`pushforward f ⋙ (j_s)_* = (g_s)_*` holds by `pushforwardComp` (`rfl`), so the factor's `f_*`-acyclicity
is exactly `(g_s)_*`-acyclicity of `F|_{U_s}` — reducible by the basis-local criterion + Serre vanishing
on affines (`lem:affine_serre_vanishing`). The irreducible analytic core that Mathlib does not supply is
that one Serre-vanishing/local-on-base step; everything categorical around it is already present.

Cross-lane note (not a blocker): all of P5a inherits `[HasInjectiveResolutions X.Modules]`, for which
**Mathlib provides no instance** — only the P3b lane (enough-injectives via Grothendieck-abelian
presheaves) can eventually discharge it. P5a can and should proceed with it as a hypothesis, matching
`higherDirectImage`'s existing signature.
