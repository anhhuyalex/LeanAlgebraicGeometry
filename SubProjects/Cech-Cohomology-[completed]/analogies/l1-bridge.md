# Analogy: the L1 categorical→module bridge for `CechAcyclic.affine`

## Mode
api-alignment

## Slug
l1bridge

## Iteration
017

## Question
Is the **L1 bridge** — identifying `IsZero ((CechComplex f 𝒰 F).homology p)` with the
`Function.Exact` of localised `R`-module maps that the (now-done) combinatorial cores
`CombinatorialCech.depDiff_exact` / `combDifferential_exact` consume — a real,
composable Mathlib path on today's Mathlib, i.e. dispatchable as a single
mathlib-build prover lane THIS iter? Confirm/refute each of the four sub-APIs.

## Architecture under question (read first)
`CechAcyclic.affine` (`CechAcyclic.lean:74`) proves
`IsZero ((CechComplex f 𝒰 F).homology p)` for `p ≥ 1`, where (from
`CechHigherDirectImage.lean`):

- `CechComplex f 𝒰 F = relativeCechComplexOfNerve f (CechNerve 𝒰 F)` (L737) lives in
  **`S.Modules = SheafOfModules` on `S`**, NOT in `ModuleCat R`.
- `relativeCechComplexOfNerve f N` (L712) = `alternatingCofaceMapComplex` of
  `((CosimplicialObject.whiskering …).obj (pushforward f)).obj (drop N)` — i.e. it
  applies the **outer `pushforward f`** (`f : Spec R ⟶ S`, `[IsAffineHom f]`) to the
  upstairs cosimplicial `(Spec R).Modules`-object, then takes the alternating coface
  complex.
- Each upstairs term is `pushPullObj F (D(s_σ) ↪ Spec R) = (incl)_* (incl)^* F` (L135).

So the bridge must cross **three** layers: (i) the outer `pushforward f` into `S.Modules`;
(ii) the sheaf-of-modules abelian structure of `(Spec R).Modules`; (iii) down to
`ModuleCat R` where `exact_of_isLocalized_span` + `depDiff_exact` live.

NOTE: `CechNerve`/`pushPullFunctor`/`CechComplex` are now fully CONSTRUCTED
(`pushPullMap_comp` closed at `CechHigherDirectImage.lean:627`); the only `sorry`s left
are `CechAcyclic.affine` and the protected `cech_computes_higherDirectImage`. The L3
cores (`CombinatorialCech.*`, both constant + dependent) are axiom-clean.

NOTE: the directive and the in-file comments reference `analogies/p3-localisation.md`,
which **does not exist** on disk (only this file, `cech-koszul-precedent.md`,
`finite-product-localisation-and-cech-r-linearity.md`, `p5a*.md`). Treat the L1/L2/L3
recipe in the `CechAcyclic.lean` header comment as the de-facto design of record.

## Decisions identified

### Decision Q1: Section over `D(g)` = away-localisation `M_g`; quasicoherent `F ≅ tilde (Γ F)`
- **Mathlib idiom — localisation half (CONFIRMED, real):**
  - `AlgebraicGeometry.tilde.toOpen` — `Tilde.lean:107`.
  - `instance (f : R) : IsLocalizedModule (.powers f) (tilde.toOpen M (basicOpen f)).hom`
    — `Tilde.lean:115` (`.of_linearEquiv` of `StructureSheaf.toOpenₗ`). **Exists exactly as
    the iter-016 prover reported.**
  - `AlgebraicGeometry.tilde.isUnit_algebraMap_end_basicOpen` — `Tilde.lean:182`. Exists.
  - `tilde.adjunction : tilde.functor R ⊣ moduleSpecΓFunctor` (`Tilde.lean:279`) with
    `instance : IsIso (tilde.adjunction).unit` (`Tilde.lean:306`): the unit
    `M ≅ Γ(tilde M)` is iso. `tilde.functor R` is `Full`+`Faithful`+`Additive`+
    `IsLeftAdjoint` (`Tilde.lean:315-318`).
  - `Scheme.Modules.fromTildeΓ` (`Tilde.lean:195`) is the counit `tilde (Γ F) ⟶ F`;
    `isIso_fromTildeΓ_iff` (`Tilde.lean:340`): `IsIso F.fromTildeΓ ↔ essImage (tilde.functor R) F`.
  - `isIso_fromTildeΓ_of_presentation (F) (P : F.Presentation) : IsIso F.fromTildeΓ`
    (`Tilde.lean:398`).
- **Project's needed path:** an arbitrary quasicoherent `F : (Spec R).Modules` ≅ `tilde (Γ F)`.
- **Gap — `divergent-with-cost` / NEEDS_MATHLIB_GAP_FILL (the affine QCoh≅Mod equivalence).**
  Mathlib has **no** lemma `IsQuasicoherent F → IsIso F.fromTildeΓ`. The only constructor
  (`isIso_fromTildeΓ_of_presentation`) needs a **global** `F.Presentation`, whereas
  `IsQuasicoherent` (`Quasicoherent.lean:249`) gives only **local** `QuasicoherentData`
  (a `CoversTop` family `X i` with a presentation of each `F.over (X i)`). Globalising a
  local presentation on the affine `Spec R` (= Stacks 01I8, `QCoh(Spec R) ≃ Mod R`) is
  genuine project-side work: ~100-150 LOC. This is the standard missing affine equivalence.
- **Verdict:** localisation building blocks PROCEED; the `F ≅ tilde (Γ F)` step is
  NEEDS_MATHLIB_GAP_FILL (buildable via the Mathlib-gradient, one lemma).

### Decision Q2: Restriction map = canonical localisation map
- **Mathlib idiom (CONFIRMED, real):**
  - `tilde.toOpen_res` (`Tilde.lean:111`): `toOpen M U ≫ (sheaf).map i.op = toOpen M V` —
    the restriction commutes with the `toOpen` localisation maps, so for two basic opens
    `D(g₂) ⊆ D(g₁)` the restriction equals the **canonical** localisation map between
    `M_{g₁}` and `M_{g₂}` by uniqueness of localisation maps
    (`IsLocalizedModule.lift`/`IsLocalizedModule.map`, `LocalizedModule/Basic.lean`).
  - `IsAffineOpen.isLocalization_of_eq_basicOpen` (`AffineScheme.lean:716`) installs the
    `IsLocalization.Away` algebra structure on `Γ(V)` for `V = X.basicOpen f`,
    `V ≤ U` affine. Already the workhorse in `finite-prod-loc`.
- **Verdict:** PROCEED. This is exactly the input the dependent coface/prepend maps
  `δ`/`c` of `depDiff_exact` need; no gap.

### Decision Q3: `IsZero (C.homology p)` (in `S.Modules`) ⇒ `Function.Exact` of R-module maps
- **Mathlib idioms (CONFIRMED, real, but only the endpoints):**
  - `exactAt_iff_isZero_homology` (`SingleHomology.lean:40`): `IsZero (C.homology p) ↔ C.ExactAt p`
    in any abelian category. General.
  - `ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`
    (`ModuleCat/Localization.lean:90`, `ModuleCat/Ulift.lean:76`) and
    `ShortComplex.moduleCat_exact_iff`: `ModuleCat`-exactness ↔ `Function.Exact`.
  - `exact_of_isLocalized_span` (`LocalProperties/Exactness.lean:173`) and
    `exact_of_localized_span` (`:211`): **both exist**, signatures verified — the L2 step,
    consuming per-spanning-element `Function.Exact` (exactly `depDiff_exact` /
    `combDifferential_exact`).
  - `alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex _ = F.mapHomologicalComplex … ⋙ …`
    (`AlternatingFaceMapComplex.lean:183`): an **additive functor commutes with the
    alternating(co)face complex**. So `CechComplex f 𝒰 F ≅ (pushforward f).mapHomologicalComplex Cᵤₚ`
    for the upstairs Čech complex `Cᵤₚ` in `(Spec R).Modules` — confirms Q4 factors out as
    `mapHomologicalComplex`.
- **Gap — the categorical→module identification (the BULK, NEEDS_MATHLIB_GAP_FILL):**
  There is **no** Mathlib lemma moving `IsZero homology` from `(Spec R).Modules` to
  `ModuleCat R`. `SheafOfModules.evaluation` / `moduleSpecΓFunctor` (= `Γ`) is a **right
  adjoint**; "Γ preserves homology on the affine" is precisely affine-exactness — circular
  to assume. The clean, non-circular route is the **equivalence-on-essImage** trick:
  - identify each upstairs term as `essImage (tilde.functor R)` (Q1) and each upstairs
    differential as `tilde.functor` of a localisation map (Q2), so
    `Cᵤₚ ≅ tilde.functor.mapHomologicalComplex D` for a module complex `D = ∏_σ M_{s_σ}`;
  - on `essImage (tilde.functor R)`, `Γ` is the inverse equivalence (unit iso), so it
    **reflects** `IsZero homology`; hence `IsZero (Cᵤₚ.homology p) ↔ IsZero (D.homology p)`;
  - `IsZero (D.homology p) ↔ Function.Exact` via `exactAt_iff_isZero_homology` +
    `moduleCat_exact_iff`, then feed L2 `exact_of_isLocalized_span` + L3 `depDiff_exact`.
  Constructing this identification (terms + differentials + the `δ`/`c` maps and the
  `hu`/`hsh`/`hcomm` compatibilities from `IsLocalizedModule.Away`) is the genuine new
  infrastructure: ~250-400 LOC. None of it is a one-liner Mathlib call.
- **Verdict:** endpoints PROCEED; the identification is NEEDS_MATHLIB_GAP_FILL (large).

### Decision Q4: the outer `pushforward f` along `f : Spec R ⟶ S`, `[IsAffineHom f]`
- **Mathlib status (CONFIRMED ABSENT):** `Scheme.Modules.pushforward f` is `IsRightAdjoint`
  (`Modules/Sheaf.lean:181`) ⇒ preserves limits/**kernels** but NOT cokernels/**homology**.
  There is **no** `PreservesFiniteColimits`/exactness instance for `pushforward f`, and **no**
  affine-pushforward-exactness or affine quasicoherent-cohomology-vanishing anywhere in
  `Mathlib/AlgebraicGeometry/` (grep empty).
- **Consequence:** since `CechComplex f 𝒰 F ≅ (pushforward f).mapHomologicalComplex Cᵤₚ`
  (Q3), reducing `IsZero (homology p)` downstairs to the upstairs `IsZero (Cᵤₚ.homology p)`
  needs `pushforward f` to **preserve homology**, i.e. affine-pushforward exactness on
  quasicoherent modules (Stacks 01XF / 02KC). This is a genuine Mathlib gap and a non-trivial
  theorem to build from scratch.
- **Cheapest sidestep:** `CechAcyclic.affine` is **NOT** in `archon-protected.yaml` (only
  `cech_computes_higherDirectImage` is). Its statement bakes in `pushforward f` by the
  planner's choice. The pushforward is **inessential to the affine-vanishing content** — the
  vanishing is a statement about `Cᵤₚ` upstairs. Options, cheapest first:
  1. **Reformulate** `CechAcyclic.affine` (or add a private upstairs lemma it reduces to) to
     state `IsZero (Cᵤₚ.homology p)` for the upstairs `(Spec R).Modules` Čech complex, and let
     the `cech_computes_higherDirectImage` consumer apply `pushforward` exactness where it is
     actually available/needed (the terms there are used for `f_*`-acyclicity of a resolution,
     a different shape). **Flag to the mathematician** — needs sign-off since it changes a
     non-protected signature.
  2. Build affine-pushforward exactness as its own lemma (large; not recommended this iter).
- **Verdict:** NEEDS_MATHLIB_GAP_FILL **or** reformulate the (unprotected) statement; this is
  the single most decisive blocker for "close L1 in one lane".

## Recommendation

**Overall: NOT-FEASIBLE-YET as a single mathlib-COMPOSE lane this iter.** The localisation
engine (Q1 basics, Q2, L2 `exact_of_isLocalized_span`, L3 `depDiff_exact`) is confirmed real
and composable. But closing the bridge end-to-end requires **two genuine new-infrastructure
constructions absent from Mathlib** — the affine `F ≅ tilde (Γ F)` equivalence (Q1) and the
affine `pushforward f` exactness or its sidestep (Q4) — **plus** the large categorical→module
identification of terms and differentials (Q3). A prover told to "fill the L1 bridge" would hit
the same wall and burn a 3rd iter. The pieces ARE buildable one lemma at a time (Mathlib
gradient), so the right move is to **decompose into sub-lanes**, not dispatch a monolithic L1.

**Recommended sub-lane sequencing (each independently statable, lowest-risk first):**
1. **Sub-lane Q4-decision (CHEAPEST, do first, needs mathematician sign-off):** decide whether
   `pushforward f` belongs in `CechAcyclic.affine`'s statement. If the affine-vanishing core is
   restated upstairs in `(Spec R).Modules` (no `pushforward f`), the whole Q4 gap evaporates and
   the lane shrinks dramatically. This is a planning/owner decision, not a prove task.
2. **Sub-lane β (Q1 globalisation, ~100-150 LOC):** `IsQuasicoherent F → IsIso F.fromTildeΓ` on
   `Spec R` — globalise `QuasicoherentData` to a global `F.Presentation`, then
   `isIso_fromTildeΓ_of_presentation`. Self-contained, Mathlib-gradient.
3. **Sub-lane γ (Q3 identification, ~250-400 LOC, the bulk):** identify the upstairs Čech
   complex with `tilde.functor.mapHomologicalComplex (∏_σ M_{s_σ})`; build `δ`/`c` and
   `hu`/`hsh`/`hcomm` from the `IsLocalizedModule (.powers …)` instances (Q1/Q2); use the
   equivalence-on-essImage to reflect `IsZero homology`; feed `exact_of_isLocalized_span` +
   `depDiff_exact`.

## Do the prior designs still hold?
- **`cech-koszul-precedent.md` (iter-059):** the **localisation/L2 engine** holds —
  `exact_of_isLocalized_span` (`:173`), `IsLocalizedModule.map_exact`,
  `isLocalization_of_eq_basicOpen` (`:716`) all confirmed present. BUT that file was written for
  the OLD `toModuleKSheaf` / `ModuleCat k` / `cechComplexFunctor` architecture and recommends
  routing acyclicity through Mathlib's `ExtraDegeneracy.homotopyEquiv` /
  `FormalCoproduct.extraDegeneracyCech`. **The project has SINCE replaced that with the
  from-scratch `CombinatorialCech` cores** (the `CechAcyclic.lean` header explicitly says "Do
  NOT route through Mathlib's simplicial `ExtraDegeneracy` (wrong variance … no cosimplicial
  dual)"). So that precedent's *acyclicity-engine* recommendation is **superseded**; only its
  *local-to-global* (`exact_of_isLocalized_span`) recommendation survives.
- **`finite-product-localisation-and-cech-r-linearity.md` (iter-106):** `IsLocalizedModule.pi`
  (`IsBaseChangePi:93`), the per-coord `IsLocalization.Away` → `IsLocalizedModule` adapter, and
  `LinearEquiv.exact_iff` all still hold and are exactly what sub-lane γ needs to build the `δ`
  family over the product terms. The R-linearity (Q2 of that file) headache does **not** recur
  here, because the dependent core `depDiff_exact` already lives in plain `R`-modules — the
  current architecture sidestepped the `ModuleCat k` post-hoc-linearity trap.

## Related analogies
- [[cech-koszul-precedent]] — localisation engine still valid; ExtraDegeneracy route superseded.
- [[finite-prod-loc]] — `IsLocalizedModule.pi` + Away-adapter feed sub-lane γ's `δ` maps.

---
*Iteration: 017*
