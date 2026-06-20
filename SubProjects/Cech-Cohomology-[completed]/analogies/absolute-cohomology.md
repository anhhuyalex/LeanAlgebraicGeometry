# Analogy: absolute sheaf cohomology `H^p(U, F)` for module sheaves + its LES

## Mode
api-alignment

## Slug
abscohom-025

## Iteration
025

## Question
What is the canonical Mathlib idiom to express `H^p(U, F)` (absolute sheaf cohomology
of an `O_X`-module restricted to an open `U`) such that (i) it agrees with derived
global sections, (ii) it carries a long exact sequence for a SES of module sheaves,
and (iii) `H^n(U, I) = 0` for injective `I`, `n > 0`? Evaluate Route α (derived global
sections via `Functor.rightDerived`), Route β (`CategoryTheory.Sheaf.H` + forget), and
Route γ (Čech colimit). The strategy suspects Route β is the cheap path — confirm/refute.

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/HigherDirectImage.lean:48` — `higherDirectImage f i F := ((pushforward f).rightDerived i).obj F`, gated on `[HasInjectiveResolutions X.Modules]`. The project's existing derived-functor idiom.
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean:672` — `cech_computes_higherDirectImage` (frozen/protected, body `sorry`); its Route A uses the Leray acyclic-resolution lemma, NOT any LES.
- `AlgebraicJacobian/Cohomology/HigherDirectImagePresheaf.lean` — 01XJ presheaf engine; also uses no LES.
- Blueprint `Cohomology_CechHigherDirectImage.tex` + `references/stacks-cohomology.tex:1696` (`lemma-cech-vanish-basis`, tag 01EO): the dimension-shift proof that genuinely *requires* a sheaf-cohomology LES of `0→F→I→Q→0` plus `H^n(U,I)=0`. This is the first place in the project a derived-functor LES is needed.

## Decisions identified

### Decision: how to realize `H^p(U,F)` so the 01EO LES + injective vanishing are cheap

- **Mathlib idiom**: **Absolute sheaf cohomology = `Ext` of the structure sheaf**.
  Sheaf cohomology over `U` is `Γ(U,-) = Hom_{Mod(O_U)}(O_U, -)`, hence
  `H^p(U,F) = Ext^p(O_U, F|_U)` (equivalently `Ext^p_{O_X}(j_! O_U, F)`). Mathlib's
  `Abelian.Ext` packages exactly the three required facts:
  - **LES (second variable, covariant)**: `CategoryTheory.Abelian.Ext.covariant_sequence_exact₁/₂/₃`
    and `Ext.covariantSequence` / `Ext.covariantSequence_exact`
    (`Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean:62,82,100,124,140,148,155`).
    For `hS : S.ShortExact` (a SES `0→S.X₁→S.X₂→S.X₃→0`) and a *fixed* first
    argument `X`, this is the long exact sequence of `Ext^n(X, S.Xᵢ)` with connecting
    map `hS.extClass.postcomp`. Requires only `[Abelian C] [HasExt.{w} C]`.
  - **Injective vanishing**: `CategoryTheory.Abelian.Ext.eq_zero_of_injective`
    (`.../Ext/EnoughInjectives.lean:99`): `(e : Ext X I (n+1)) → e = 0` for `[Injective I]`,
    needs only `[HasExt.{w} C]`. With first arg `j_! O_U` (or `O_U`) and second arg the
    injective `O_X`-module `I`, this is `H^{n+1}(U,I)=0` verbatim — and it needs ONLY the
    second argument injective, so no "restriction-preserves-injectives" lemma is forced
    if you keep `I` in the role of the second Ext argument.
  - **`H^0 = Γ`**: `Ext.homEquiv₀ : Ext X Y 0 ≃ (X ⟶ Y)` and `Ext.addEquiv₀`
    (`.../Ext/Basic.lean:223,319`): degree-0 Ext is `Hom`, and `Hom(O_U,F|_U)=Γ(U,F)`.
  - **Availability of `HasExt`**: unconditional via `CategoryTheory.HasExt.standard : HasExt.{max u v} C`
    (`.../Ext/Basic.lean:93`); also an *instance* `IsGrothendieckAbelian.hasExt`
    (`Mathlib/CategoryTheory/Abelian/GrothendieckCategory/HasExt.lean:36`) when the
    category is Grothendieck abelian. `SheafOfModules.{v} R` is `Abelian`
    (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.lean:40`); `X.Modules` already has
    `HasInjectiveResolutions` assumed throughout the project.
- **Project's current path**: none shipped for absolute cohomology. The project's
  derived-functor idiom is `Functor.rightDerived` (`higherDirectImage`). The strategy
  *proposed* Route β (`Sheaf.H` + forget) as the cheap path.
- **Gap**: divergent-with-cost for the *rightDerived* form of Route α; the Ext
  realization is the aligned idiom for the LES.
- **Cost of divergence (if a non-Ext route is chosen)**:
  - **Route α via `Functor.rightDerived`** (`(Γ(U,-)).rightDerived p`): injective
    vanishing is free (`Functor.isZero_rightDerived_obj_injective_succ`,
    `Mathlib/CategoryTheory/Abelian/RightDerived.lean:151`), but **Mathlib has NO long
    exact sequence for `Functor.rightDerived`**. Verified: nothing in
    `Abelian/RightDerived.lean` or anywhere ties `rightDerived` to a SES/LES/triangle.
    Building it = re-deriving the derived-category→`rightDerived` bridge (SES ⟹
    distinguished triangle in `D^b` ⟹ apply `RF` ⟹ homology LES, then identify
    `H^n(RF(-)) ≅ rightDerived n`). Multi-hundred-LOC; it literally reconstructs what
    `Abelian.Ext` already packages. **AVOID.**
  - **Route β (`CategoryTheory.Sheaf.H` + forget)**: **REFUTED.** `Sheaf.H` /
    `Sheaf.cohomology` / `H^n` on `Sheaf J AddCommGrp` **does not exist** in Mathlib
    (`lean_local_search "Sheaf.H"` returns only `Sheaf.Hom.*` morphism lemmas; no
    AddCommGrp-valued sheaf-cohomology object anywhere). Choosing β = building the entire
    abelian-sheaf cohomology theory + forgetful-functor injective/LES transport from
    scratch. The suspected cheap path is the most expensive. **AVOID.**
  - **Route γ (Čech colimit, `H^p := colim_𝒰 Ȟ^p(𝒰,F)`)**: viable fallback reusing
    project infra (`sectionCechComplex` + homology; `ses_cech_h1` partly done). LES
    obtainable from the SES-of-Čech-complexes via `HomologicalComplex`/`ShortComplex`
    homology sequence + filtered-colimit exactness (Grothendieck/AB5). But it forces
    restating the downstream `affine_serre_vanishing` / `H^k(f^{-1}V,G)` consumers in
    colim-Čech form, and reproves 01EO by hand instead of consuming a packaged theory.
    Medium-high cost.
- **Verdict**: **ALIGN_WITH_MATHLIB** — realize Route α's derived global sections **as
  `Abelian.Ext`**, not as `Functor.rightDerived`. The LES requirement is the bottleneck
  and Ext is the *only* route where Mathlib supplies it off the shelf.

## Recommendation

Commit to **`H^p(U, F) := Ext^p(𝒪_U, F|_U)`** (sheaf cohomology = Ext of the structure
sheaf), realized with `CategoryTheory.Abelian.Ext` in the module-sheaf category. Concretely:

- Realize "sections over `U`" via the open subscheme `U`'s module category and the
  Mathlib restriction `AlgebraicGeometry.Scheme.Modules.restrictFunctor`
  (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:319`, with
  `Γ(M.restrict f, U) = Γ(M, f ''ᵁ U)`), with first Ext-argument the structure sheaf as
  a module over itself. `HasExt` is free (`HasExt.standard`).
- 01EO LES: instantiate `Ext.covariantSequence_exact` / `covariant_sequence_exact₁/₂/₃`
  at fixed first argument `𝒪_U` and the SES `0→F→I→Q→0`.
- `H^n(U,I)=0`: `Ext.eq_zero_of_injective` (keep the injective `O_X`-module `I` as the
  *second* Ext argument so the vanishing needs nothing about restriction; if you instead
  use `Ext^p(𝒪_U, I|_U)` you additionally need "open-immersion restriction preserves
  injectives", which the downstream `open_immersion_pushforward_comp` is already shaped
  to provide).
- `H^0(U,F) ≅ Γ(U,F)`: `Ext.homEquiv₀`/`addEquiv₀` plus `Hom(𝒪_U,-) ≅ Γ(U,-)`
  (degree-0 plumbing via `PresheafOfModules.evaluation`).

Note this introduces a *second* derived-functor framework (Ext / derived category)
alongside the project's `Functor.rightDerived` for `Rⁱf_*`, but **no bridge lemma between
them is forced**: `cech_computes_higherDirectImage` uses the Leray acyclic-resolution
lemma (not a LES), and the absolute `H^p(U,-)` appears only in 01EO and the affine-Serre
vanishing. The one place the two frameworks must eventually meet is the
affine-acyclicity step (`H^i(affine, qcoh)=0` ⟹ Čech terms are `f_*`-acyclic, Stacks
`lemma-quasi-coherence-higher-direct-images-application`); that comparison exists
regardless of how `H^p` is realized, so it does not weigh against the Ext choice.

Fallback if `Ext` smallness/universe bookkeeping over `SheafOfModules` proves painful:
Route γ (Čech colimit) reusing the existing section-Čech infra. Never Route β.
