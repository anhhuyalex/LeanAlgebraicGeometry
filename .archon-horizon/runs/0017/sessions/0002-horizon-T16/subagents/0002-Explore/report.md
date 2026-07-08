# Port Plan: Stacks-01EO Čech↔Derived Comparison, `X.Modules` → `𝒮 := Sheaf(Opens.grothendieckTopology X.toTopCat)(ModuleCat k)`

All paths relative to `/home/Axel/LeanAlgebraicGeometry-Horizon/MainProjects/Algebraic-Jacobian-Challenge` unless marked `MATHLIB:`. Mathlib root: `/home/Axel/LeanAlgebraicGeometry-Horizon/.lake-packages/mathlib/Mathlib`.

---

## A. Template inventory (dependency order)

### A.0 Upstream dependencies of `CechBridge.lean` (must be ported first — the "hard" 2357+730 LOC substrate)

| Name | file:line | Role | `X.Modules`-specific ingredients |
|---|---|---|---|
| `freeYoneda` | `AlgebraicJacobian/Cohomology/FreePresheafComplex.lean:125` | `Opens X ⥤ X.PresheafOfModules`, `V ↦ free(yoneda V)` | `PresheafOfModules.free`, `X.ringCatSheaf.obj` |
| `coverOpen`, `coverInterOpen` | `FreePresheafComplex.lean:129,135` | cover-member / multi-index intersection opens | `X.OpenCover`, `𝒰.f i` |
| `cechFreeSimplicial` | `FreePresheafComplex.lean:165` | simplicial object of coproducts of `freeYoneda` | `X.PresheafOfModules` |
| `cechFreePresheafComplex` | `FreePresheafComplex.lean:207` | the free Čech **chain** complex `K(𝒰)_•` | ditto |
| `freeYonedaAug`, `cechFreeAug` | `FreePresheafComplex.lean:230,276` | augmentation `K(𝒰)_0 → O_𝒰` | ditto |
| `coverStructurePresheaf` | `FreePresheafComplex.lean:288` | the presheaf `O_𝒰` "structure sheaf of the cover" (degree-`0`-concentrated target) | ditto |
| `cechFreeComplexAug` | `FreePresheafComplex.lean:346` | augmented chain complex `K(𝒰)_• → O_𝒰[0]` | ditto |
| `combDifferential`/`combHomotopy`/`combDifferential_exact` etc. | `FreePresheafComplex.lean:458-580` | **pure combinatorics** — contracting homotopy for the free Čech resolution | none (already coefficient-agnostic; ports verbatim) |
| `cechFreeEval_X`,`cechEngineD`,`cechEngineComplexAug`,… (the bulk, 580-1439) | `FreePresheafComplex.lean:580-1439` | sectionwise (objectwise) evaluation of `K(𝒰)_•` at an open `V`, contraction, `cechEngineComplexAug_quasiIso` | `X.PresheafOfModules` colimits computed objectwise, `PresheafOfModules.evaluation` |
| `cechFreeComplex_quasiIso` | `FreePresheafComplex.lean:1439` | **the resolution theorem**: `K(𝒰)_• → O_𝒰[0]` is a quasi-iso | assembles all of the above |
| `…Fam` mirror (cover-agnostic, arbitrary finite family) | `FreePresheafComplex.lean:1472-2357`, culminating `cechFreeComplex_quasiIsoFam:2341` | same theorem with no covering hypothesis | ditto |
| `injective_toPresheafOfModules` | `PresheafCech.lean:216` | **injective sheaf ⟹ injective presheaf**, via `Injective.injective_of_adjoint (PresheafOfModules.sheafificationAdjunction (𝟙 _))` | `PresheafOfModules.sheafificationAdjunction`, needs a hand-proved `PreservesMonomorphisms` instance on `PresheafOfModules.sheafification` |
| `freeYonedaHomEquiv`/`_apply`/`freeYonedaHomAddEquiv` | `PresheafCech.lean:245,256,274` | `Hom(free(yoneda V), F) ≃+ F(V)` (corepresentability of sections) | `PresheafOfModules.freeHomEquiv`, `yonedaEquiv` |
| `sectionCechCosimplicial` | `PresheafCech.lean:303` | hand-built cosimplicial object `[p] ↦ ∏_σ F(⨅ U(σk))` | `X.PresheafOfModules`, `Ab`-valued |
| `sectionCechComplex` | `PresheafCech.lean:337` | `Č•(𝒰,F) := alternatingCofaceMapComplex.obj sectionCechCosimplicial` | ditto |
| `sectionCechProductEquiv`,`sectionCechFaceRestr`,`sectionCech_objD_apply`,`sectionCech_isZero_homology_of_objD_exact` | `CechAcyclic.lean:1505,1570,1582,1531` | coordinatization of the abstract product/differential into pointwise section data | `ToType`, `ConcreteCategory.hom`, `F.presheaf` |

### A.1 `AlgebraicJacobian/Cohomology/CechBridge.lean` (1118 LOC)

| Name | file:line | Role (01EO label) | `X.Modules`-specific ingredients |
|---|---|---|---|
| `homCechCosimplicial` | `CechBridge.lean:136` | `Hom(K(𝒰)_•,F)` as cosimplicial `Ab` (helper) | `preadditiveYoneda.obj F`, `cechFreeSimplicial` |
| `homCechComplex` | `CechBridge.lean:149` | alternating-coface complex of the above (helper) | ditto |
| `homCechSectionIsoApp` | `CechBridge.lean:162` | per-degree iso `Hom(K(𝒰)_n,F) ≅ Č^n(𝒰,F)` | `freeYonedaHomAddEquiv`, `opCoproductIsoProduct`, `piComparison` |
| `pi_mapIso_hom_eq`, `homCechSectionIsoApp_hom_π`, `freeYonedaHomAddEquiv_naturality` (private) | 174,181,204 | naturality plumbing (helpers) | as above |
| `homCechSectionCosimplicialIso` | `CechBridge.lean:230` | cosimplicial nat-iso `Hom(K(𝒰)_•,F) ≅ Č•(𝒰,F)` (helper) | ditto |
| `cechComplex_hom_identification` | `CechBridge.lean:266` | **cochain-complex iso** `Hom(K(𝒰)_•,F) ≅ Č•(𝒰,F)` (helper, blueprint `lem:cech_complex_hom_identification`) | assembles above |
| `homCechCosimplicial_δ`, `homCechComplex_d_eq` (private) | 289,300 | `Hom(-,F)` of opposite face complex = coface hom complex (helper) | `HomologicalComplex.op`, `preadditiveYoneda` |
| `homCechComplexMapOpIso` | `CechBridge.lean:341` | `homCechComplex 𝒰 F ≅ Hom(-,F)(K(𝒰)_•ᵒᵖ)` (helper) | ditto |
| `sectionCechComplexMapOpIso` | `CechBridge.lean:363` | `Hom(-,F)(K(𝒰)_•ᵒᵖ) ≅ Č•(𝒰,F)` — the single bridging iso the acyclicity proof transports across (helper) | composes above |
| `preadditiveYoneda_obj_preservesFiniteColimits_of_injective` (instance) | `CechBridge.lean:401` | **generic abelian-category fact**: `Hom(-,I)` exact for injective `I` | none — general `{C} [Abelian C]`, ports verbatim |
| `quasiIso_map_preadditiveYoneda_of_injective` | `CechBridge.lean:421` | `Hom(-,I)` carries quasi-isos to quasi-isos (helper) | none — general, ports verbatim |
| `sectionCech_objD_exact_of_isZero_homology` | `CechBridge.lean:459` | homology-vanishing ⟹ objD-exactness (**L2 pre-req** for coboundary extraction) | `sectionCechComplex`, `sectionCechCosimplicial` |
| `sectionCech_one_coboundary_of_isZero_homology` | `CechBridge.lean:498` | Čech-`H¹`-vanishing ⟹ 1-cocycles are coboundaries (**heart of `ses_cech_h1`**, i.e. L1's surjectivity ingredient) | ditto |
| `restr_trans`,`restr_inj_of_eq`,`restr_op_unique`,`restr_g'_transport`,`fι_sectionCechFaceRestr`,`coverConst_iInf`,`coverPair_iInf`,`pair_comp_δ0/1` (private) | 552-635 | restriction bookkeeping for `ses_cech_h1` | `X.PresheafOfModules`, `Opens X` |
| **`ses_cech_h1`** | `CechBridge.lean:659` (proof to 826) | **L1's surjectivity step** (Stacks `lemma-ses-cech-h1`): SES `0→F→G→H→0` + `Ȟ¹(U,F)=0` + local lifts ⟹ global lift | `TopCat.Presheaf.IsSheaf`, `isSheafUniqueGluing`, section-level sheaf gluing on `X.toTopCat` |
| `injective_cech_acyclic` | `CechBridge.lean:874` (**base case** feeding **L4**) | **injective ⟹ Čech-acyclic**: op-transport `quasiIso_map_preadditiveYoneda_of_injective` of `cechFreeComplexAug` through `sectionCechComplexMapOpIso` | consumes `cechFreeComplex_quasiIso`, `injective_toPresheafOfModules`, `sectionCechComplexMapOpIso` — i.e. the **entire A.0 substrate** |
| `homCech…Fam` / `injective_cech_acyclicFam` mirror | `CechBridge.lean:936-1116`, top theorem 1078 | cover-agnostic (arbitrary finite family, no covering hyp.) mirror of the whole file | mirrors the `…Fam` mirror in A.0 |

### A.2 `AlgebraicJacobian/Cohomology/AbsoluteCohomology.lean` (171 LOC) — **Form-B absolute cohomology**

| Name | file:line | Role | `X.Modules`-specific ingredients |
|---|---|---|---|
| `hasExtModules` (local instance) | `AbsoluteCohomology.lean:25` | `HasExt.{u+1,u,u+1} X.Modules := HasExt.standard _` | needs `HasExt.standard` because `X.Modules` has **no** `IsGrothendieckAbelian`/`EnoughInjectives` instance |
| **`jShriekOU`** | `AbsoluteCohomology.lean:30` | the corepresenting object `j_!O_U` — "extension by zero of `O_X|_U`" — `sheafification(free(yoneda U))` | `PresheafOfModules.sheafification`, `PresheafOfModules.free`, `X.ringCatSheaf.obj` |
| `sheafificationHomAddEquiv` | `AbsoluteCohomology.lean:36` | sheafification-adjunction hom-bijection as `AddEquiv` | `PresheafOfModules.sheafificationAdjunction` |
| `jShriekOU_homEquiv` | `AbsoluteCohomology.lean:50` | `Hom(jShriekOU U,F) ≃+ F(U)` (corepresentability of sections, **`H⁰≅Γ` engine**) | composes above with `freeYonedaHomAddEquiv` |
| **`absoluteCohomology`** | `AbsoluteCohomology.lean:56` | `H^p(U,F) := Ext^p(jShriekOU U,F)` — the carrier | `Ext`, `jShriekOU` |
| `absoluteCohomologyZeroAddEquiv` | `AbsoluteCohomology.lean:63` | `H⁰(U,F) ≅ Γ(U,F)` (**`H⁰≅Γ`**) | `Ext.homEquiv₀` + `jShriekOU_homEquiv` |
| `absoluteCohomology_eq_zero_of_injective` | `AbsoluteCohomology.lean:76` | **injective-vanishing wrapper** (`Ext.eq_zero_of_injective`) | thin wrapper, no `X.Modules` specifics |
| `absoluteCohomology_covariant_exact₁/₂/₃` | `AbsoluteCohomology.lean:83,93,102` | thin `Ext.covariant_sequence_exact₁/₂/₃` wrappers at `jShriekOU U` | thin wrapper, no specifics |
| `homEquiv₀_comp_mk₀`, `freeYonedaHomEquiv_naturality`, `sheafificationHomAddEquiv_naturality`, `jShriekOU_homEquiv_naturality` (private) | 115,124,137,147 | naturality of the `H⁰≅Γ` iso in the coefficient sheaf | as above |
| `absoluteCohomologyZeroAddEquiv_naturality` | `AbsoluteCohomology.lean:162` | naturality of `H⁰≅Γ` (used by base case L3's surjectivity transfer) | as above |

### A.3 `AlgebraicJacobian/Cohomology/CechToCohomology.lean` (434 LOC) — **the L1/L2/L3/L4 assembly**

| Name | file:line | Role (01EO label) | `X.Modules`-specific ingredients |
|---|---|---|---|
| `sectionCechCosimplicialMap`,`sectionCechCosimplicialFunctor`,`sectionCechComplexFunctor`,`sectionCechComplexMap` | `CechToCohomology.lean:34,50,85,91` | **hand-built functoriality of `sectionCechComplex` in the coefficient presheaf** | `X.PresheafOfModules`, `PresheafOfModules.toPresheaf` — ***PORT SHORTCUT: unnecessary in 𝒮, see §B*** |
| `cechCohomology` | `CechToCohomology.lean:99` | named accessor `Ȟ^p(U,F) := (sectionCechComplex U F).homology p` | `X.PresheafOfModules` |
| `pi_π_map_apply`(private), `shortExact_piMap` | `CechToCohomology.lean:105,114` | **AB4\*: product of SES in `Ab` is SES** (generic) | none — `{J:Type u}{S:J→ShortComplex Ab}`, ports verbatim (or reuse for `ModuleCat k`) |
| `faceShortComplex` | `CechToCohomology.lean:163` | per-face-`σ` short complex of section groups | `X.PresheafOfModules`, `PresheafOfModules.toPresheaf` |
| `sectionCechComplexShortComplex` | `CechToCohomology.lean:174` | SES of Čech cochain complexes `0→Č(F)→Č(I)→Č(Q)→0` | ditto |
| **`cechComplex_shortExact_of_basis`** | `CechToCohomology.lean:196` | **L1**: per-face SES ⟹ SES of Čech complexes | `HomologicalComplex.shortExact_of_degreewise_shortExact` (generic) + `shortExact_piMap` |
| **`cechHomology_quotient_vanishing`** | `CechToCohomology.lean:213` | **L2, abstract homological core**: SES of cochain complexes, `X₂`,`X₁` acyclic in positive degree ⟹ `X₃` acyclic | **fully generic** — `T : ShortComplex (CochainComplex Ab u ℕ)`, uses `ShortComplex.ShortExact.δIso` (generic) |
| `quotient_cech_vanishing_of_basis` | `CechToCohomology.lean:228` | **L2**, instantiated at `sectionCechComplexShortComplex` | `X.PresheafOfModules` (only via the instantiation) |
| `sectionsFunctor` | `CechToCohomology.lean:242` | `Γ(V,-): X.Modules ⥤ Ab`, left-exact | `Scheme.Modules.toPresheafOfModules`, `PresheafOfModules.toPresheaf`, `evaluation` |
| `faceShortComplex_shortExact_of_sheaf_ses` | `CechToCohomology.lean:253` | per-face SES **from a sheaf SES + surjectivity hyp** (feeds L1) | ditto, `PreservesFiniteLimits (sectionsFunctor V)` |
| **`absoluteCohomology_one_eq_zero_of_basis`** | `CechToCohomology.lean:284` | **L3, base case** `H¹(U,F)=0`: injective-vanishing + `H⁰`-surjectivity via covariant Ext LES | `AbsoluteCohomology` wrappers (`jShriekOU`, `Ext`) |
| `CovDatum`,`BasisCovSystem`,`HasVanishingHigherCech` | `CechToCohomology.lean:309,323,346` | data packaging conditions (1)–(3) of 01EO | `X.Modules`, `TopologicalSpace.Opens X`, `cechCohomology` (via `Scheme.Modules.toPresheafOfModules`) |
| `injSES`,`injSES_shortExact` (private) | `CechToCohomology.lean:361,365` | `0→F→I→I/F→0` for `I=Injective.under F` | **gated on `[EnoughInjectives X.Modules]`** — ***THIS is the un-instantiable gate; PORT FIX: `EnoughInjectives 𝒮` is free*** |
| **`absoluteCohomology_eq_zero_of_basis`** | `CechToCohomology.lean:376` | **L4, dimension-shift induction** — the inductive core | consumes `injSES` + L1 + L2 + L3 + covariant Ext LES, all `X.Modules`-flavored |
| **`cech_eq_cohomology_of_basis`** | `CechToCohomology.lean:429` | **the 01EO target**, thin assembly of L4 | ditto, still gated on `[EnoughInjectives X.Modules]` |

---

## B. The analogue dictionary

| `X.Modules` ingredient | Constant-`k` analogue | **Exists already?** |
|---|---|---|
| `jShriekOU U := sheafification(free(yoneda U))` (`AbsoluteCohomology.lean:30`) | `freeSheafOn U := (presheafToSheaf _ _).obj ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k)).obj U)` — this exact term appears **inline** inside `Scheme.HModule'` (`StructureSheafModuleK/Carriers.lean:104-105`) but **there is no standalone named `def`**. **PORT TASK**: extract a named `def freeSheafOn (U) : 𝒮 := (presheafToSheaf _ _).obj (…)` so `HModule'` becomes `Ext (freeSheafOn X) F n` — a one-line refactor, then the 01EO chain can be phrased against `freeSheafOn` exactly as `jShriekOU`. | Data exists inline; name does **not** exist — trivial extraction. |
| `Hom(jShriekOU U,F) ≃+ F(U)` (`jShriekOU_homEquiv`, `AbsoluteCohomology.lean:50`) | `HModule'_zero_linearEquiv : HModule' k F 0 X ≃ₗ[k] (freeSheafOn X ⟶ F)` (`Carriers.lean:120-129`) — **this is `Ext.linearEquiv₀` composed with the corepresentability**, i.e. **exactly** the `H⁰≅Γ` half of `jShriekOU_homEquiv`. What's missing is the *un-Ext'd* corepresentability `Hom_𝒮(freeSheafOn U, F) ≃ₗ[k] F(U)` itself (the analogue of `freeYonedaHomAddEquiv` composed with `sheafificationHomAddEquiv`). **PORT TASK**: build via `sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat k)` `.homEquiv` ∘ `(yoneda-free adjunction)` — same two-step composite as `AbsoluteCohomology.lean:36-53`, using generic `sheafificationAdjunction` (`MATHLIB Sites/Sheafification.lean:81`) in place of `PresheafOfModules.sheafificationAdjunction`. | `H⁰`-level `LinearEquiv` exists (`HModule'_zero_linearEquiv`); the underlying non-`Ext`'d Hom-corepresentability does **not** exist as a named lemma — build ~20-30 LOC. |
| Čech complex functoriality in coefficient (`sectionCechComplexFunctor`, `CechToCohomology.lean:85`) | **Free**: Mathlib's `cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` (`MATHLIB CategoryTheory/Sites/SheafCohomology/Cech.lean:65`) is **already** a functor of the presheaf argument, built as `cosimplicialObjectFunctor E ⋙ alternatingCofaceMapComplex A` (`Cech.lean:53,43`). Project's `Scheme.cechCochain`/`Scheme.cechCohomology` (`Carriers.lean:562-578`) is `(cechComplexFunctor 𝒰).obj (sheafToPresheaf.obj F)` — apply `(cechComplexFunctor 𝒰).map (sheafToPresheaf.map φ)` for any `φ : F ⟶ G` to get the SES-of-complexes step **for free**, no hand-rolled `sectionCechCosimplicialMap`/`_Functor` needed. | **Fully present**, superior to the `X.Modules` version — the entire `sectionCechCosimplicialMap`/`Functor`/`sectionCechComplexFunctor`/`Map` block (`CechToCohomology.lean:34-94`, ~60 LOC) is **not needed** in the port. |
| Homology LES of a SES of cochain complexes (feeds L2) | Same generic Mathlib lemmas, applicable verbatim since they are stated for arbitrary abelian `C`: `ShortComplex.ShortExact.δIso` (`MATHLIB Algebra/Homology/HomologySequence.lean:362`), `HomologicalComplex.shortExact_of_degreewise_shortExact` (`MATHLIB Algebra/Homology/HomologicalComplexAbelian.lean:56`). The project's `cechHomology_quotient_vanishing` (`CechToCohomology.lean:213`) is **already stated generically** over `CochainComplex Ab.{u} ℕ`; the constant-`k` port only needs `CochainComplex (ModuleCat.{u} k) ℕ` substituted (or reuse the `Ab`-valued statement after `forget₂`). | Present (generic Mathlib); the project's own `cechHomology_quotient_vanishing` is *also* already category-generic in shape and can be re-instantiated almost verbatim at `ModuleCat k`. `shortExact_piMap` (`CechToCohomology.lean:114`, AB4\* for `Ab`) needs either a `ModuleCat k` sibling or routing through `forget₂ (ModuleCat k) Ab`. |
| `injective_toPresheafOfModules` (sheaf-injective ⟹ presheaf-injective) | **Much easier**: `Injective.injective_of_adjoint (sheafificationAdjunction J (ModuleCat k)) I : Injective ((sheafToPresheaf J _).obj I)` fires **immediately** because Mathlib already supplies `instance [HasSheafify J A] : PreservesFiniteLimits (presheafToSheaf J A)` (`MATHLIB Sites/Sheafification.lean:76`, unconditionally on any small site `J` and any `A`) — `PreservesFiniteLimits ⟹ PreservesMonomorphisms` is automatic, no hand-proved instance needed (contrast `PresheafCech.lean:216-225`, which needed an explicit `haveI : PreservesMonomorphisms (PresheafOfModules.sheafification …)`). | **Present generically** — this whole lemma becomes a **one-liner** in the port. |
| `injective_cech_acyclic` (injective ⟹ Čech-acyclic) | **No Mathlib shortcut** — needs the full free-Čech-resolution machinery (§A.0) rebuilt at the level of `(Opens X.toTopCat)ᵒᵖ ⥤ ModuleCat k` presheaves, with `PresheafOfModules.free`↦`yoneda ⋙ ModuleCat.free k`, `PresheafOfModules.freeAdjunction`↦ composite of `yoneda`-Yoneda-lemma with the `ModuleCat.free k ⊣ forget` adjunction, `X.ringCatSheaf.obj`↦ (nothing, coefficients are constant `k`). This is the single biggest chunk of new project-local work (see §D). | **Absent** — must be rebuilt; combinatorial contracting-homotopy core (`combDifferential`/`combHomotopy`, `FreePresheafComplex.lean:458-580`) is coefficient-agnostic and ports with essentially zero change. |
| `Ext.eq_zero_of_injective` / covariant LES | Same Mathlib lemmas, apply verbatim once `HasExt.{u} 𝒮` / `HasExt.{u+1} 𝒮` are instances (they are — §C). | **Present**, no gap. |
| `EnoughInjectives X.Modules` (missing, forces the whole L4/top theorem to carry it as a hypothesis) | `EnoughInjectives 𝒮` — **proved instance**, `AlgebraicJacobian/RiemannRoch/Adelic/CechComparisonGate.lean:123-126` (`enoughInjectives_moduleKSheaf`, `inferInstance` from `IsGrothendieckAbelian`). | **Present** — this is the whole point of the port: `injSES`/L4/`cech_eq_cohomology_of_basis` become **unconditional**. |
| `ses_cech_h1` (L1 surjectivity engine via sheaf gluing) | Needs a `Sheaf`-side analogue of `TopCat.Presheaf.IsSheaf.isSheafUniqueGluing` applied to `F.obj : (Opens X)ᵒᵖ ⥤ ModuleCat k`-as-`AddCommGrpCat`-presheaf plus the constant-`k` `sectionCechFaceRestr`/`sectionCechProductEquiv` coordinatization of `cechComplexFunctor`'s cosimplicial object. | **Partially present**: `Sheaf.isSheaf`/gluing API on `ModuleCat`-valued sheaves exists generically in Mathlib (`Presheaf.IsSheaf.isSheafUniqueGluing` after `forget₂`/`sheafToPresheaf`), but the **coordinatization lemmas** (`sectionCechProductEquiv`, `sectionCechFaceRestr`, `sectionCech_objD_apply`, `sectionCech_one_coboundary_of_isZero_homology`) analogous to `CechAcyclic.lean:1505-1613`/`CechBridge.lean:459-527` must be rebuilt against Mathlib's `FormalCoproduct`-based `cechComplexFunctor` cosimplicial object rather than the project's hand-rolled `sectionCechCosimplicial`. |

---

## C. Mathlib bricks for the port

**(1) Ext vanishing on injective target.**
- `Abelian.Ext.eq_zero_of_injective [HasExt.{w} C] {X I : C} {n : ℕ} [Injective I] (e : Ext X I (n+1)) : e = 0` — `MATHLIB Algebra/Homology/DerivedCategory/Ext/EnoughInjectives.lean:100`.
- `Abelian.Ext.subsingleton_of_injective [HasExt.{w} C] (X I : C) [Injective I] (n : ℕ) : Subsingleton (Ext.{w} X I (n+1))` — same file, immediately below.
- Used identically by `AlgebraicJacobian/Cohomology/AbsoluteCohomology.lean:76-78`; **transfers verbatim** to `C := 𝒮`.

**(2) Covariant Ext long exact sequence for a `ShortComplex.ShortExact`.**
- `Abelian.Ext.covariant_sequence_exact₁ {n₁} (x₁ : Ext X S.X₁ n₁) (hx₁ : x₁.comp (Ext.mk₀ S.f) _ = 0) {n₀} (hn₀ : n₀+1=n₁) : ∃ x₃, x₃.comp hS.extClass hn₀ = x₁` — `MATHLIB Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean:143`.
- `covariant_sequence_exact₂` — `ExactSequences.lean:151`.
- `covariant_sequence_exact₃` — `ExactSequences.lean:158`.
- (Primed forms `covariant_sequence_exact₁'/₂'/₃'` at lines 103,63,84 are the `ComposableArrows`-level source these are built from.)
- Project's `absoluteCohomology_covariant_exact₁/₂/₃` (`AbsoluteCohomology.lean:83,93,102`) are thin wrappers at fixed first argument `jShriekOU U`; the port wraps at `freeSheafOn U` instead — **same three Mathlib names, zero change**.
- Also needed generically: `Ext.mk₀`, `Ext.homEquiv₀`, `Ext.comp_assoc`, `Ext.mk₀_comp_mk₀`, `Ext.mk₀_add`, `Ext.mk₀_homEquiv₀_apply`, `Ext.zero_comp`, `Ext.comp_zero`, `Ext.linearEquiv₀` — all category-generic, already exercised by the project's own `HModule'_zero_linearEquiv` (`Carriers.lean:129`) and `absoluteCohomology_one_eq_zero_of_basis`'s proof (`CechToCohomology.lean:284-303`), so the exact call pattern is already validated in-tree for both flavors.

**(3) `EnoughInjectives` + `HasExt` instances for `Sheaf J (ModuleCat k)` — confirmed present, project already proved/cited:**
- `IsGrothendieckAbelian.{v} (Sheaf J A)` instance: `MATHLIB CategoryTheory/Abelian/GrothendieckAxioms/Sheaf.lean:73` (unnamed instance, for `{C : Type v} [SmallCategory.{v} C] (J) (A) [Abelian A] [IsGrothendieckAbelian.{v} A] [HasSheafify J A]`).
- `EnoughInjectives C` from `IsGrothendieckAbelian.{v} C`: `MATHLIB CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean:379` (`instance enoughInjectives`).
- `HasExt.{w} C` from `IsGrothendieckAbelian.{w} C`: `MATHLIB CategoryTheory/Abelian/GrothendieckCategory/HasExt.lean` (`instance IsGrothendieckAbelian.hasExt`).
- Project citations, already proved and named:
  - `AlgebraicGeometry.Adelic.isGrothendieckAbelian_moduleKSheaf` — `RiemannRoch/Adelic/CechComparisonGate.lean:114-117`.
  - `enoughInjectives_moduleKSheaf` — `CechComparisonGate.lean:123-126`.
  - `hasExt_moduleKSheaf` (`HasExt.{u}`) — `CechComparisonGate.lean:130-132`.
  - `hasExt_succ_moduleKSheaf` (`HasExt.{u+1}`) — `CechComparisonGate.lean:136-138`.
  - Also `AlgebraicGeometry.Cohomology.instHasExt_Sheaf_Opens_ModuleCatK` (via `HasExt.standard`) — `StructureSheafModuleK/Presheaf.lean:110-115`, and `instHasSheafify_Opens_ModuleCatK` — `Presheaf.lean:100-104`.
  - All **confirmed instantiable today** — no project-local proof obligation remains for gate 3.

**(4) `presheafToSheaf` preserves finite limits/monomorphisms — generic in Mathlib, no project-local proof needed (contrast the `X.Modules` `toSheaf_preservesFiniteColimits`/`toSheaf_preservesEpimorphisms`):**
- `instance [HasSheafify J A] : PreservesFiniteLimits (presheafToSheaf J A)` — `MATHLIB CategoryTheory/Sites/Sheafification.lean:76`. Fully generic over any small site `J : GrothendieckTopology C` and any `A` (with `HasSheafify J A`) — **no** restriction to sheaves-of-modules-over-a-sheaf-of-rings, unlike the project's `toSheaf_preservesFiniteColimits`/`_preservesEpimorphisms` (`AffineSerreVanishing.lean:119-157`), whose signature is `{R : Sheaf J RingCat} [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] : PreservesFiniteColimits (SheafOfModules.toSheaf R)` — that pair is about the **colimit**-side forgetful functor `SheafOfModules → Sheaf` (needed because `X.Modules = SheafOfModules O_X` sits over a *sheaf of rings*, not over a fixed field). **The port does not need this pair at all** — `𝒮`'s objects already *are* `Sheaf J (ModuleCat k)`, there is no intermediate "sheaf of modules over a sheaf of rings" forgetful functor to push finite-colimit-preservation through. The relevant fact for the port (injective transport, §B row 4) needs only the *finite-limit* side, which Mathlib gives unconditionally at `Sheafification.lean:76`.
- Companion: `sheafificationAdjunction J A : presheafToSheaf J A ⊣ sheafToPresheaf J A` — `Sheafification.lean:81`, `def sheafToPresheaf` L.≈32, generic.
- `Injective.injective_of_adjoint {L ⊣ R} (J : D) [Injective J] : Injective (R.obj J)` — `MATHLIB CategoryTheory/Preadditive/Injective/Basic.lean:195`, category-generic (this is exactly the lemma the project's `injective_toPresheafOfModules` already calls, `PresheafCech.lean:224`).

**(5) `cechComplexFunctor` and its constituents.**
- `CategoryTheory.cechComplexFunctor {ι} (U : ι → C) : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ := FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech` — `MATHLIB CategoryTheory/Sites/SheafCohomology/Cech.lean:65`, requires `[HasFiniteProducts C] [Preadditive A]` (and `[HasProducts.{w} A]` ambient).
- `FormalCoproduct.cochainComplexFunctor E := cosimplicialObjectFunctor E ⋙ AlgebraicTopology.alternatingCofaceMapComplex A` — `Cech.lean:53`.
- `FormalCoproduct.cosimplicialObjectFunctor E := evalOp C A ⋙ (whiskeringLeft _ _ _).obj E.rightOp` — `Cech.lean:43`.
- Extra-degeneracy precedent (relevant only for the *affine* Serre-vanishing branch, not directly for 01EO): `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` — `MATHLIB AlgebraicTopology/ExtraDegeneracy.lean:328`; `Limits.FormalCoproduct.extraDegeneracyCech` — `MATHLIB CategoryTheory/Limits/FormalCoproducts/ExtraDegeneracy.lean:92`.

**(6) Homology-LES machinery for the SES-of-complexes step (L2), generic in `CochainComplex C ℕ` for any abelian `C`:**
- `ShortComplex.ShortExact.δIso (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j)) : S.X₃.homology i ≅ S.X₁.homology j` — `MATHLIB Algebra/Homology/HomologySequence.lean:362`.
- `HomologicalComplex.shortExact_of_degreewise_shortExact` — `MATHLIB Algebra/Homology/HomologicalComplexAbelian.lean:56`.
- `HomologicalComplex.exactAt_iff_isZero_homology`, `.exactAt_iff'`, `ShortComplex.ab_exact_iff_function_exact` — same generic-abelian-category API the project already uses at `sectionCech_objD_exact_of_isZero_homology` (`CechBridge.lean:459-481`).

---

## D. Structure recommendation

### D.1 Proposed file split (constant-`k` port, new directory `AlgebraicJacobian/Cohomology/StructureSheafModuleK/Cech/` or siblings of `StructureSheafModuleK/`)

| New file | Mirrors | Est. LOC | Contents |
|---|---|---|---|
| `FreeSheafCorep.lean` | `AbsoluteCohomology.lean` §1 + extraction from `Carriers.lean:99-129` | 80-150 | Named `freeSheafOn (X : C) : 𝒮`; the un-Ext'd corepresentability `Hom_𝒮(freeSheafOn X, F) ≃ₗ[k] F.obj.obj (op X)` (Yoneda + `sheafificationAdjunction`); redefine `HModule'` in terms of `freeSheafOn` (or leave `Carriers.lean` as-is and just add the missing corepresentability lemma there). |
| `FreeCechResolution.lean` | `FreePresheafComplex.lean` (2357 LOC) | **900-1400** | The dominant cost. `K(U)_• : ChainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat k) ℕ` built from `⨁_σ (yoneda ⋙ ModuleCat.free k).obj (V_σ)`; augmentation to a "cover structure presheaf"; the contracting-homotopy combinatorics (`combDifferential`/`combHomotopy`/`combDifferential_exact`, `FreePresheafComplex.lean:458-580`, ports **almost verbatim** — coefficient-agnostic) driving `cechFreeComplex_quasiIso`-analogue. |
| `InjectiveCechAcyclic.lean` | `PresheafCech.lean` + `CechBridge.lean` §"Hom(-,I) exact" + §"injective_cech_acyclic" | 250-400 | `injective_sheafToPresheaf` (one-liner via §C.4/§B row-4 — *much shorter* than `injective_toPresheafOfModules`); `Hom(-,F)`-exactness-for-injective instance (reuse `preadditiveYoneda_obj_preservesFiniteColimits_of_injective`, `CechBridge.lean:401`, verbatim, it's already category-generic); the Čech-hom-identification iso (mirrors `cechComplex_hom_identification`/`homCechComplexMapOpIso`/`sectionCechComplexMapOpIso`, `CechBridge.lean:136-368`) against `cechComplexFunctor`'s cosimplicial object instead of hand-rolled `sectionCechCosimplicial`; the top theorem `injective_cech_acyclic`. |
| `CechCoordinates.lean` | `PresheafCech.lean:303-339` + `CechAcyclic.lean:1505-1613` | 150-250 | `sectionCechProductEquiv`/`sectionCechFaceRestr`/`sectionCech_objD_apply`/`sectionCech_isZero_homology_of_objD_exact`/`sectionCech_one_coboundary_of_isZero_homology`, rebuilt against `Scheme.cechCochain`/`(cechComplexFunctor 𝒰).obj`'s cosimplicial object (i.e. `FormalCoproduct.cosimplicialObjectFunctor`) rather than a hand-rolled `sectionCechCosimplicial`. |
| `SesCechH1.lean` | `CechBridge.lean:542-828` (`ses_cech_h1` + restriction bookkeeping) | 250-350 | Direct structural port; swap `X.PresheafOfModules`/`TopCat.Presheaf.IsSheaf` for `𝒮`'s sheaf-gluing API (generic `Presheaf.IsSheaf.isSheafUniqueGluing` after composing with `sheafToPresheaf`/`forget₂`). |
| `CechToCohomologyK.lean` | `CechToCohomology.lean` (434 LOC) | 250-350 | **Shorter than the original** — drop `sectionCechCosimplicialMap`/`Functor`/`sectionCechComplexFunctor`/`Map` (§B row 3: free via `cechComplexFunctor`'s built-in functoriality); keep `faceShortComplex`, `sectionCechComplexShortComplex`/`cechComplex_shortExact_of_basis` (L1), `cechHomology_quotient_vanishing`/`quotient_cech_vanishing_of_basis` (L2, near-verbatim reuse), `absoluteCohomology_one_eq_zero_of_basis`-analogue (L3), `BasisCovSystem`/`HasVanishingHigherCech`/`absoluteCohomology_eq_zero_of_basis`/`cech_eq_cohomology_of_basis`-analogue (L4) — **and here `injSES`/`injSES_shortExact` become *unconditional* instances, dropping `[EnoughInjectives 𝒮]` from every downstream signature**, since it's an `inferInstance`. |
| **Total port estimate** | | **~1900-2900 LOC** | vs. ~4400 LOC of the `X.Modules` original (`CechBridge.lean` 1118 + `AbsoluteCohomology.lean` 171 + `CechToCohomology.lean` 434 + `FreePresheafComplex.lean` 2357 + `PresheafCech.lean` 342 + `CechAcyclic.lean`'s relevant 1505-1613 slice ≈ 4300+, minus large savings from §B rows 3-4 and §C.4). |

This is consistent with the independent estimate in `analogies/cech-koszul-precedent.md` (~300-450 LOC) for the **affine-only, spanning-family** route via `exact_of_isLocalized_span`/extra-degeneracy — that is a *cheaper alternative* to Branch A/B above but only closes the *affine* case (needed for gate 4 / Serre vanishing on `D(f)`), not the fully general basis-comparison `cech_eq_cohomology_of_basis`. If the near-term goal is only **gate 4** (`IsAffineHModuleVanishing`, per `CechComparisonGate.lean:64-78`), the localization route is materially cheaper than porting the whole 01EO chain; if the goal is the **general** Stacks-01EO statement (arbitrary basis/cover system, matching the `X.Modules` capstone), the full port above is required.

### D.2 The 3 hardest lemmas to port

**1. `injective_cech_acyclic` (`CechBridge.lean:874`, base-case ingredient of L3/via `BasisCovSystem.injective_acyclic`).**
Proof strategy to mirror (10 lines):
1. Build the free Čech chain complex of presheaves `K(U)_p = ⨁_{σ:Fin(p+1)→ι} free(yoneda(V_σ))` (analogue: `⨁_σ (yoneda ⋙ ModuleCat.free k).obj V_σ`), with differential the alternating sum of face maps induced by inclusions `V_{σ} ≤ V_{σ∘δᵢ}`.
2. Show the augmentation `K(U)_• → O_U[0]` (`O_U` = "presheaf that is `⊕_{i:V_i⊇V} k`-ish structure of the cover", concretely `coverStructurePresheaf`-analogue) is a quasi-iso, via the *sectionwise* contracting homotopy: fix `i_fix` with `V ⊆ U_{i_fix}`, homotopy `h(s)_{i₀,…,iₚ} = [i₀ = i_fix]·s_{i₁,…,iₚ}`, check `dh+hd=id` (`combHomotopy_spec`/`combDifferential_exact`, `FreePresheafComplex.lean:483-580`, coefficient-agnostic, ports verbatim).
3. Show `(sheafToPresheaf J _).obj I` is injective in the presheaf category, for `I` injective in `𝒮` — **one-liner** via `Injective.injective_of_adjoint (sheafificationAdjunction J (ModuleCat k)) I`, using Mathlib's free `PreservesFiniteLimits (presheafToSheaf J A)` instance (§C.4) — this step is **much shorter** than the `X.Modules` analogue `injective_toPresheafOfModules`.
4. `Hom(-,I_pshf)` is exact (`preadditiveYoneda_obj_preservesFiniteColimits_of_injective`, `CechBridge.lean:401`, category-generic, reuse verbatim).
5. Apply `Hom(-,I_pshf)` to the quasi-iso augmentation ⟹ quasi-iso of `Hom`-complexes; identify `Hom(K(U)_•,I_pshf)` with the section Čech complex `Č•(U,I)` (analogue of `cechComplex_hom_identification`/`homCechComplexMapOpIso`) — this identification against Mathlib's `cechComplexFunctor` cosimplicial object (rather than a hand-rolled one) is genuinely new plumbing (~150-250 LOC) but structurally the same shape as `CechBridge.lean:121-369`.
6. Conclude: source complex is `Hom(-,I)` of a degree-0-concentrated complex ⟹ zero in positive degree ⟹ transport across the quasi-iso to `Č•(U,I)`'s positive-degree homology (exact tail of `CechBridge.lean:874-911`, structurally verbatim).

**2. `ses_cech_h1` (`CechBridge.lean:659-826`, L1's surjectivity ingredient — Stacks `lemma-ses-cech-h1`).**
Proof strategy (10 lines): given SES `0→F→G→H→0` and local lifts `sLoc i ∈ G(Uᵢ)` of `s∈H(⨆Uᵢ)`, form the degree-1 cochain of pairwise differences `dGcoord σ = sLoc(σ1)|_σ - sLoc(σ0)|_σ`; show `gπ` kills it (LES exactness on sections, from `hπι`/`hker`); lift the killed cochain into `F` pointwise (`hker`); show the lift is a genuine 1-cocycle in `F` (transport the `d²=0` identity of `G`'s cochain through the mono `fι`); apply `Ȟ¹(U,F)=0` to extract a 0-cochain `t` with `dt` = the lift (`sectionCech_one_coboundary_of_isZero_homology`); correct `sLoc` by `fι(t)` to get a genuinely compatible family; glue via `TopCat.Presheaf.IsSheaf.isSheafUniqueGluing` on `G`; check the glued section maps to `s` by separatedness of `H`. **Port cost**: mechanical (swap `X.PresheafOfModules`/its restriction API for `𝒮`'s `sheafToPresheaf`/`forget₂`-composed presheaf and Mathlib's generic sheaf-gluing lemma), but the sheer bookkeeping volume (7 private helper lemmas, `CechBridge.lean:552-635`) means this is a **large, low-conceptual-risk, high-LOC** port item — budget ~250-350 LOC.

**3. The Čech-hom-identification `cechComplex_hom_identification`/`homCechComplexMapOpIso`/`sectionCechComplexMapOpIso` (`CechBridge.lean:121-369`).**
This is the piece with the **least direct Mathlib precedent for the new setting**, because it must reconcile two different presentations of "the Čech complex": (a) Mathlib's `cechComplexFunctor`'s `FormalCoproduct`-based cosimplicial object (used to define `Scheme.cechCochain`/`Scheme.cechCohomology`, `Carriers.lean:562-578`, the target the whole port must land on) versus (b) the free-presheaf-resolution's own natural cosimplicial presentation `Hom(K(U)_•,F)` (built from `Sigma.ι`/`opCoproductIsoProduct`/`piComparison`, mirroring `homCechSectionIsoApp`, `CechBridge.lean:162-254`). The `X.Modules` proof needed this because `sectionCechComplex` was **hand-rolled** to match `K(𝒰)_•`'s shape by construction; in the port, the target complex `Scheme.cechCochain` is fixed externally by `cechComplexFunctor`, so the identification must instead show `Hom(K(U)_•, F) ≅ (cechComplexFunctor U).obj (sheafToPresheaf.obj F)` degreewise (`Hom(⊕_σ free(yoneda V_σ), F) ≅ ∏_σ F(V_σ)`, matching `FormalCoproduct.mk _ U`.cech's degree-`p` object `U.power (Fin(p+1))`), then check differential-intertwining against `FormalCoproduct`'s coface maps rather than the project's own `homOfLE`-based ones. Budget ~150-250 LOC of genuinely new work; recommend prototyping the degree-0 and degree-1 cases by hand first (`lean_multi_attempt`/`lean_goal` against `FormalCoproduct.mk`'s unfolding) before committing to the general-`n` proof, since the `FormalCoproduct`/`SimplicialObject` API's defeq behavior around `U.power`/`E.rightOp` is unfamiliar territory for this codebase (no prior project usage found).
