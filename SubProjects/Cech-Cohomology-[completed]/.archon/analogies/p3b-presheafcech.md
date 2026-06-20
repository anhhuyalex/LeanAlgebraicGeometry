# Analogy: presheaf-level Čech machinery for `O_X`-modules (P3b bridge)

## Mode
api-alignment

## Slug
p3b-presheafcech

## Iteration
011

## Question

For the seven scaffolds of the P3b "injective `O_X`-modules are Čech-acyclic"
bridge (`cechFreePresheafComplex`, `cechComplex_hom_identification`,
`cechFreeComplex_quasiIso`, `presheafModules_enoughInjectives`,
`cech_delta_functor_presheaves`, `injective_cech_acyclic`, plus the P3 re-sign of
`CechAcyclic.affine`): what is Mathlib's idiom (existing API to reuse, or the
construction path if absent), does the proposed name/shape risk a parallel API,
and what is the cost of misalignment?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean` — the whole P3b block
  is *about to be scaffolded* (nothing shipped yet). Existing anchors:
  `CechComplex` (`:737`, relative complex in `S.Modules`), `CechAcyclic.affine`
  (`:764`, the P3 sorry, NOT protected), `cech_computes_higherDirectImage`
  (`:801`, PROTECTED).
- `blueprint/.../Cohomology_CechHigherDirectImage.tex` §"Presheaf-level Čech
  machinery" (`def:cech_free_presheaf_complex`, `lem:cech_complex_hom_identification`,
  `lem:cech_free_complex_quasi_iso`, `lem:presheaf_modules_enough_injectives`,
  `lem:cech_delta_functor_presheaves`, `lem:injective_cech_acyclic`).

## Mathlib ground truth (verified via LSP this iter)

The project's sheaf side is `X.Modules = SheafOfModules X.ringCatSheaf`
(`Mathlib.AlgebraicGeometry.Modules.Sheaf`). The presheaf side already exists:

- **`PresheafOfModules R`** for `R : Cᵒᵖ ⥤ RingCat` (`Mathlib.Algebra.Category.ModuleCat.Presheaf`).
  `Abelian` (`PresheafOfModules.instAbelian`) and `Preadditive` instances present.
  For a scheme there is the abbreviation **`X.PresheafOfModules`**
  (`= PresheafOfModules X.ringCatSheaf.val`, site `(Opens ↥X)ᵒᵖ`).
- **`Scheme.Modules.toPresheafOfModules X : X.Modules ⥤ X.PresheafOfModules`** — the
  `Mod ↪ PMod` inclusion, **a right adjoint**
  (`...instIsRightAdjointPresheafOfModulesToPresheafOfModules`).
- **`PresheafOfModules.sheafificationAdjunction (α : R₀ ⟶ R.val)`**
  (`...Presheaf.Sheafification`): `sheafification α ⊣ (forget R) ⋙ restrictScalars α`.
  For a scheme `α = 𝟙` and this is the `sheafification ⊣ inclusion` pair.
- **`PresheafOfModules.free R : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules R`** with
  **`PresheafOfModules.freeAdjunction R : free R ⊣ toPresheaf R ⋙ whiskeringRight … (forget Ab)`**
  (`...Presheaf.Free`). `freeObjDesc`/`freeHomEquiv` give the hom-set bijection.
- **`PresheafOfModules.evaluation R X : PresheafOfModules R ⥤ ModuleCat (R.obj X)`** —
  the exact "sections over `X`" functor.
- **`CategoryTheory.Injective.injective_of_adjoint (adj : L ⊣ R) (J) [Injective J]
  [L.PreservesMonomorphisms] : Injective (R.obj J)`**
  (`...Preadditive.Injective.Basic`); plus
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`
  (`...Injective.Preserves`) and `Adjunction.map_injective`.
- **`IsGrothendieckAbelian.enoughInjectives`** (instance) and
  **`instIsGrothendieckAbelianModuleCat`** — present, as the directive said.
- **`Functor.rightDerived`** (`...Abelian.RightDerived`) needs
  `[HasInjectiveResolutions C]` + `F.Additive`; `rightDerivedZeroIsoSelf` identifies
  `R⁰F ≅ F` for left-exact `F`. Universal property machinery:
  `Functor.IsRightDerivedFunctor` (`...Functor.Derived.RightDerived`).

**Confirmed ABSENT (all `#synth`-failed in the project's universes):**
- `IsGrothendieckAbelian (PresheafOfModules R)` — and `IsGrothendieckAbelian (C ⥤ D)`
  for `D` Grothendieck is *also* absent (no functor-category transfer).
- `AB5 (PresheafOfModules R)` (exactness of filtered colimits) — absent.
- `EnoughInjectives (PresheafOfModules R)` / `HasInjectiveResolutions (PresheafOfModules R)` — absent.
- Present, by contrast: `HasColimits` and `HasFilteredColimits` for `PresheafOfModules R`.
- No `j_!` extension-by-zero for presheaves/sheaves of modules; no Čech complex of
  presheaves of modules; no Čech-exactness/contractibility lemma.

## Decisions identified

### Decision 1: `cechFreePresheafComplex` — category + the `j_!` shriek

- **Mathlib idiom**: the category is **`X.PresheafOfModules`** (no parallel needed).
  For the shriek: Mathlib has **no** `j_!` extension-by-zero for presheaves of
  modules, BUT it has the canonical representing-object machine
  **`PresheafOfModules.free`**. The blueprint summand
  `(j_{i_0…i_p})_! (O_X|_{U_{i_0…i_p}})` is, up to canonical iso, exactly
  **`(PresheafOfModules.free R).obj (yoneda.obj U_{i_0…i_p})`**: on `V` it is the
  free `R(V)`-module on `Hom(V,U)` = `R(V)` if `V ⊆ U`, else `0` — precisely
  extension-by-zero of `O_X|_U`. Its defining property
  `Hom(free(yoneda U), F) ≅ F(U)` is `freeAdjunction` + Yoneda. `yoneda` on
  `Opens ↥X` is verified to typecheck (`Opens ↥X ⥤ (Opens ↥X)ᵒᵖ ⥤ Type u`).
- **Project's proposed path**: a definition named `cechFreePresheafComplex` building
  `⨁ (j_…)_! O|_{U_…}` "with the alternating Čech differential". The blueprint prose
  introduces a bespoke `j_!` ("the shriek functor … `(j_!G)(W)=G(W)` if `W⊆U` else 0").
- **Gap**: divergent-with-cost **iff** a bespoke `j_!`/extension-by-zero functor is
  authored. ALIGNED iff `j_!(O|_U)` is realized as `free(yoneda U)`.
- **Cost of divergence**: a hand-rolled `j_!` is a parallel API to `free`. It would
  need its own adjunction-with-restriction lemma to recover
  `Hom(j_! O|_U, F) = F(U)` (decision 2) — duplicating `freeAdjunction` — and its own
  functoriality for the index-dropping maps. Using `free` gives both for free: the
  differentials are `free.map` of the representable index-dropping maps
  `yoneda(U_{i_0…i_{p+1}}) → yoneda(U_{i_0…î_j…})` (inclusion of opens), and the
  Yoneda identity is one adjunction iso.
- **Verdict**: ALIGN_WITH_MATHLIB on the building blocks (`X.PresheafOfModules`,
  `free`, `yoneda`, `evaluation`); NEEDS_MATHLIB_GAP_FILL for the assembled complex
  object (no Čech-of-presheaf-modules complex exists). Build it as a
  `ChainComplex X.PresheafOfModules ℕ` (degree `p` = `⨁_{I^{p+1}} free(yoneda U_…)`,
  homological/chain variance per the blueprint's `K(𝒰)_•`). Do NOT introduce a
  named `j_!`.

### Decision 2: `cechComplex_hom_identification` — `Hom(K_•, F) = Č•(𝒰,F)`

- **Mathlib idiom**: `(freeAdjunction R).homEquiv (yoneda.obj U) F` composed with the
  Yoneda section iso (`yonedaEquiv` / representable sections) gives
  `Hom_{PMod}(free(yoneda U), F) ≅ F(U)` naturally in `F`. The "shriek–restriction
  adjunction termwise" the directive asks for **is** `freeAdjunction` (the left
  adjoint of "underlying presheaf of types"), not a separate `j_! ⊣ restriction`.
  Take the product/`⨁`-`Hom` over multi-indices and match differentials.
- **Project's proposed path**: `cechComplex_hom_identification : Hom(K_•,F) = Č•(𝒰,F)`.
- **Gap**: divergent-with-cost on one point — **which `Č•`**. The project already has
  `CechComplex` (`:737`) = the **relative** complex `∏ (f|_{U_…})_* (F|_{U_…})` in
  `S.Modules` (pushforward along `f`). The blueprint's `Č•(𝒰,F)` here is the
  **sections** complex `∏ F(U_{i_0…i_p})` of `O_X(U)`-modules — a *different, simpler*
  object. `Hom(K_•, F)` lands in `O_X(U)`-modules, not `S.Modules`.
- **Cost of divergence**: if `cechComplex_hom_identification` is stated against the
  relative `CechComplex`, the types won't line up and a bridge between "section Čech
  complex" and "relative pushforward Čech complex" gets invented — a parallel `Č•`.
  Recommendation: introduce the **presheaf section Čech complex** `Č•(𝒰,F)` as its own
  `CochainComplex (ModuleCat (O_X U)) ℕ` (or as `(evaluation _ (op U)).mapHomologicalComplex`
  applied to nothing — it is literally the `Hom`-complex), and reconcile with the
  relative `CechComplex` only where actually needed downstream.
- **Verdict**: ALIGN_WITH_MATHLIB (use `freeAdjunction` + Yoneda; reuse `evaluation`),
  with a FLAG to keep the section-`Č•` and the relative-`CechComplex` distinct rather
  than forking a third notion.

### Decision 3: `cechFreeComplex_quasiIso` — `K_•` resolves `O_𝒰[0]`

- **Mathlib idiom**: none specific. Exactness of a complex of presheaves is checked
  objectwise (`PresheafOfModules` (co)limits and homology are objectwise); the
  sectionwise extended complex over each `W` is contractible by the explicit homotopy
  `h(s)_{i_0…} = (i_0=i_fix) s_{i_1…}`. Mathlib has `Homotopy`/`HomotopyEquiv` and
  `Preadditive`/homology API but not this Čech contractibility. (`ExtraDegeneracy`
  exists but is simplicial/chain and has the same global-`i_fix` mismatch noted in
  `p3-localisation.md`; do not route through it.)
- **Gap**: divergent-and-necessary (no idiom).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL. Build the sectionwise contracting homotopy.

### Decision 4: `presheafModules_enoughInjectives`

- **Mathlib idiom**: the intended `IsGrothendieckAbelian.enoughInjectives` engine is
  real, BUT the prerequisite `IsGrothendieckAbelian (PresheafOfModules R)` is **absent**,
  and there is **no functor-category transfer** (`IsGrothendieckAbelian (C ⥤ D)` for
  `D` Grothendieck is also absent), and **`AB5 (PresheafOfModules R)` is absent**. Only
  `HasColimits`/`HasFilteredColimits` are present. So the cheap "instance already
  there" hope is false.
- **Project's proposed path**: derive enough-injectives from Grothendieck-abelian.
- **Gap**: divergent-and-necessary, **and expensive**.
- **Cost**: the cheapest real path is `IsGrothendieckAbelian.mk` supplying (i) `AB5`
  (objectwise from `ModuleCat`'s AB5 — needs an objectwise-filtered-colimit-exactness
  argument), (ii) a separating family (the `free(yoneda U)` objects separate), plus
  LocallySmall. That is a multi-lemma build. **KEY STRATEGIC NOTE:** this lemma is
  **NOT on the critical path to `injective_cech_acyclic`** (decision 6) — see below —
  so the project should weigh building it at all.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (high cost; reconsider necessity).

### Decision 5: `cech_delta_functor_presheaves`

- **Mathlib idiom**: `Functor.rightDerived` exists but **requires
  `HasInjectiveResolutions (PresheafOfModules R)`**, i.e. it *depends on decision 4*.
  The universal-δ-functor/effaceability identification (`Ȟ^p ≅ R^p Ȟ^0`) is NOT a
  packaged Mathlib theorem in usable form: `IsRightDerivedFunctor` is
  localization-flavored and matching Čech cohomology to it is substantial. Mathlib's
  cohomological-δ-functor universality API is thin.
- **Gap**: divergent-and-necessary, expensive, and **chained behind decision 4**.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (high cost; also not needed for decision 6).

### Decision 6: `injective_cech_acyclic`

- **Mathlib idiom (two independent parts):**
  1. *injective sheaf ⟹ injective presheaf*: ALIGNED — apply
     **`Injective.injective_of_adjoint`** to `sheafificationAdjunction` (left adjoint
     `sheafification`, right adjoint = the inclusion `toPresheafOfModules`), with
     `sheafification.PreservesMonomorphisms` (it is exact). Exactly the Stacks
     "right adjoint of an exact left adjoint preserves injectives".
  2. *the vanishing itself*: it follows **directly** from decisions 2+3 + injectivity,
     WITHOUT decisions 4 or 5. `K_• → O_𝒰` is an exact augmented complex (decision 3);
     for injective `I`, `Hom(-,I)` is exact, so `Hom(K_•,I) = Č•(𝒰,I)` (decision 2) is
     exact in positive degrees. This is the Stacks proof of `lemma-injective-trivial-cech`
     and it does **not** invoke the δ-functor identification.
- **Gap**: ALIGNED on part 1; part 2 is light gap-fill once 2+3 exist.
- **Verdict**: ALIGN_WITH_MATHLIB on the injective-transfer; the rest is gap-fill that
  bypasses decisions 4–5.

### Decision 7: P3 re-sign of `CechAcyclic.affine`

- **Mathlib idiom**: locked in `analogies/p3-localisation.md`. Re-sign to carry
  `(s : ι → Γ(X,O_X)) (hs : Ideal.span (Set.range s) = ⊤)` and obtain the cover via
  `(Scheme.affineOpenCoverOfSpanRangeEqTop s hs).openCover : X.OpenCover`, fed into the
  (general-`OpenCover`) `CechComplex`. The same `(s,hs)` bundle drives
  `exact_of_isLocalized_span`. The protected `cech_computes_higherDirectImage` and
  `CechComplex` keep their general signatures.
- **Verdict**: PROCEED (confirmed; idiomatic feed is `.openCover`).

## Recommendation

Build the P3b block on Mathlib's **existing** presheaf-of-modules API, not a parallel
one. (1) Category = `X.PresheafOfModules`. (2) The blueprint's `j_!(O_X|_U)` must be
`(PresheafOfModules.free _).obj (yoneda.obj U)` — do **not** author a bespoke
extension-by-zero functor; that is the single highest parallel-API risk, because it
would duplicate `freeAdjunction` (the very thing decision 2 needs) and `free`'s
functoriality. (3) `cechComplex_hom_identification` = `freeAdjunction.homEquiv` +
Yoneda + `evaluation`; state it against a *new presheaf section* `Č•(𝒰,F)` of
`O_X(U)`-modules, kept distinct from the existing relative `CechComplex`. (4)
`injective_cech_acyclic` should be routed through `Injective.injective_of_adjoint`
(`sheafificationAdjunction`) + the direct "exact `Hom(-,I)` kills positive Čech
cohomology" argument, which needs only the free-complex resolution (decisions 2–3) and
**bypasses `presheafModules_enoughInjectives` (4) and `cech_delta_functor_presheaves`
(5)**. Decisions 4 and 5 are genuine Mathlib gaps with real cost (no Grothendieck
instance for presheaves of modules, no functor-category transfer, no AB5, and
`rightDerived` is gated on enough-injectives); since the headline result (6) does not
need them, treat 4–5 as optional and deprioritize them. Decision 7 is the already-locked
P3 re-sign. Risk order: **1 (bespoke `j_!`) > 2 (forked `Č•`) > 4,5 (expensive,
possibly-unnecessary gaps) > 3,6 (aligned gap-fill) > 7 (confirmed)**.
