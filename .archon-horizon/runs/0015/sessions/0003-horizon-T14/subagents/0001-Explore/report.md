I now have a complete, precise map. Here is the exhaustive report.

---

# Mathlib `Proj 𝒜` (ℕ-graded) structure-sheaf / basic-open API

Two files carry the API. Paths below are the project's copy under `.lake-packages/`; the `.shared-packages/` copy is byte-identical modulo a few line offsets.

- `…/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean` — namespace `AlgebraicGeometry.Proj`, the **user-facing** graded-`ℕ` API. Ambient context (lines 44–47): `{σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]`. This is exactly your `𝒜 : ℕ → Submodule …` case.
- `…/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean` — namespace `AlgebraicGeometry.ProjectiveSpectrum.Proj`, the **underlying/internal** construction (notation `A⁰_ f := Away 𝒜 f`, `pbo f := ProjectiveSpectrum.basicOpen 𝒜 f`, `Proj| pbo f`).
- `…/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean` — `ProjectiveSpectrum.basicOpen` and its lattice lemmas.
- `…/RingTheory/GradedAlgebra/HomogeneousLocalization.lean` — `Away`, `awayMap`, `mapId`.

**IMPORTANT naming caveat:** there are TWO `awayToSection`s. `AlgebraicGeometry.Proj.awayToSection` (Basic.lean:135) is the wrapper you want; `AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection` (Scheme.lean:592) is the internal definition it delegates to. Likewise `Proj.basicOpen` (Basic) vs `ProjectiveSpectrum.basicOpen` (Topology).

---

## 1. `Proj.basicOpen` and its lattice API

All in `Basic.lean`, namespace `AlgebraicGeometry.Proj`, with `(f g : A)` explicit:

- **`AlgebraicGeometry.Proj.basicOpen`** — Basic.lean:54
  `def basicOpen (𝒜 : ℕ → σ) (f : A) : (Proj 𝒜).Opens := ProjectiveSpectrum.basicOpen 𝒜 f`
  D₊(f) as an open of the scheme `Proj 𝒜`.

- **`AlgebraicGeometry.Proj.basicOpen_mul`** — Basic.lean:69 ✅ EXISTS
  `theorem basicOpen_mul : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g`
  D₊(fg) = D₊(f) ⊓ D₊(g). (delegates to `ProjectiveSpectrum.basicOpen_mul`.)

- **`AlgebraicGeometry.Proj.basicOpen_mono`** — Basic.lean:72 ✅ EXISTS (this is your "D₊(fg) ≤ D₊(f)" via divisibility)
  `theorem basicOpen_mono (hfg : f ∣ g) : basicOpen 𝒜 g ≤ basicOpen 𝒜 f`
  Divisibility ⇒ reverse ⊆ on basic opens. Used throughout as `basicOpen_mono 𝒜 f x ⟨g, hx⟩ : basicOpen 𝒜 x ≤ basicOpen 𝒜 f` when `hx : x = f * g`.

- **`AlgebraicGeometry.Proj.basicOpen_pow`** — Basic.lean:66 ✅ EXISTS
  `@[simp] theorem basicOpen_pow (n) (hn : 0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f`

- **`AlgebraicGeometry.Proj.basicOpen_one`** — Basic.lean:62: `basicOpen 𝒜 1 = ⊤`.
- **`AlgebraicGeometry.Proj.basicOpen_zero`** — Basic.lean:64: `basicOpen 𝒜 0 = ⊥`.
- **`AlgebraicGeometry.Proj.mem_basicOpen`** — Basic.lean:58: `x ∈ basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal`.
- **`AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj`** — Basic.lean:75.
- **`AlgebraicGeometry.Proj.isBasis_basicOpen`** — Basic.lean:79.
- **`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`** / `…_eq_top'` — Basic.lean:86 / 97 (irrelevant-ideal-span ⇒ D₊(fᵢ) cover ⊤).

There is NO explicit `Proj.basicOpen_mul_le_left` in the `AlgebraicGeometry.Proj` namespace — but the **topology-level** versions exist (used via `basicOpen_mono`):
- `ProjectiveSpectrum.basicOpen_mul` — Topology.lean:360
- `ProjectiveSpectrum.basicOpen_mul_le_left` — Topology.lean:363 : `basicOpen 𝒜 (f*g) ≤ basicOpen 𝒜 f`
- `ProjectiveSpectrum.basicOpen_mul_le_right` — Topology.lean:367
- `ProjectiveSpectrum.basicOpen_pow` — Topology.lean:372.

---

## 2. `Proj.awayToSection`

- **`AlgebraicGeometry.Proj.awayToSection`** — Basic.lean:135
  `def awayToSection (𝒜 : ℕ → σ) (f : A) : CommRingCat.of (Away 𝒜 f) ⟶ Γ(Proj 𝒜, basicOpen 𝒜 f)`
  It is a **`CommRingCat` morphism** (`⟶`), i.e. a bundled ring hom in `CommRingCat`; `.hom` gives the underlying `RingHom`. Maps the degree-0 away localization `A⁰_f = Away 𝒜 f` into sections over D₊(f). Delegates to the internal one.

- Internal: **`AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection`** — Scheme.lean:592
  `def awayToSection (f) : CommRingCat.of (A⁰_ f) ⟶ (structureSheaf 𝒜).1.obj (op (pbo f))`
  Built as `CommRingCat.ofHom { toFun s := ⟨fun x ↦ HomogeneousLocalization.mapId 𝒜 (…) s, …⟩, map_add', map_mul', map_zero', map_one' }` — a genuine bundled ring hom (all four ring-hom fields discharged).
  - `awayToSection_apply` — Scheme.lean:616 (value formula via `IsLocalization.map`).
  - `awayToSection_germ` — Scheme.lean:608 (compatibility with germs/`stalkIso'`).

Related maps:
- **`AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToΓ`** — Scheme.lean:632
  `def awayToΓ (f) : CommRingCat.of (A⁰_ f) ⟶ LocallyRingedSpace.Γ.obj (op <| Proj| pbo f)` = `awayToSection ≫ presheaf.map (homOfLE …).op`.
- **`AlgebraicGeometry.Proj.basicOpenToSpec`** — Basic.lean:141
  `def basicOpenToSpec (f) : (basicOpen 𝒜 f).toScheme ⟶ Spec (.of <| Away 𝒜 f)` = `(basicOpen 𝒜 f).toSpecΓ ≫ Spec.map (awayToSection 𝒜 f)`.

---

## 3. ★ THE KEY QUESTION — restriction naturality of `awayToSection` across `A_f → A_{fg}` ★

**YES, it exists, exactly in the shape you asked for.**

**`AlgebraicGeometry.Proj.awayMap_awayToSection`** — Basic.lean:222, `@[reassoc]`

Ambient (Basic.lean:218–219): `variable {f}` then `{m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') {x : A} (hx : x = f * g)`. Effective signature (only `g_deg` and `hx` are actually needed):

```
theorem awayMap_awayToSection
    {m' : ℕ} {f g x : A} (g_deg : g ∈ 𝒜 m') (hx : x = f * g) :
    CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜 g_deg hx) ≫ awayToSection 𝒜 x
      = awayToSection 𝒜 f
          ≫ (Proj 𝒜).presheaf.map (homOfLE (basicOpen_mono 𝒜 f x ⟨g, hx⟩)).op
```

Read this literally: pushing a degree-0 fraction from `A⁰_f` into `A⁰_x = A⁰_{fg}` via `HomogeneousLocalization.awayMap` and then taking its section over D₊(fg) **equals** taking its section over D₊(f) and then restricting along the presheaf restriction map for the inclusion `D₊(fg) ≤ D₊(f)`. This is precisely "`awayToSection f x` restricted to D₊(fg) = `awayToSection (fg) (image of x)`". Being `@[reassoc]`, there is also `awayMap_awayToSection_assoc`.

Downstream naturality lemmas built on it (all Basic.lean, all `@[reassoc]`):
- **`AlgebraicGeometry.Proj.basicOpenToSpec_SpecMap_awayMap`** — Basic.lean:240
  `basicOpenToSpec 𝒜 x ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) = (Proj 𝒜).homOfLE (basicOpen_mono 𝒜 f x ⟨g, hx⟩) ≫ basicOpenToSpec 𝒜 f` — the Spec-side square.
- **`AlgebraicGeometry.Proj.SpecMap_awayMap_awayι`** — Basic.lean:248
  `Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) ≫ awayι 𝒜 f f_deg hm = awayι 𝒜 x (…) (…)` — the open-immersion factorization D₊(fg) → D₊(f) → Proj.

No other spelling ("`awayToΓ`/`toOpen`/`awayι` restriction to a smaller basic open") exists separately — `awayMap_awayToSection` is THE lemma, and everything else is derived from it.

---

## 4. The iso `D₊(f) ≅ Spec (A_f)` and its naturality

All in `Basic.lean`, requiring `f` homogeneous of positive degree: `variable {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)` (Basic.lean:155).

- **`AlgebraicGeometry.Proj.basicOpenIsoSpec`** — Basic.lean:161, `@[simps! -isSimp hom]`
  `noncomputable def basicOpenIsoSpec (f_deg : f ∈ 𝒜 m) (hm : 0 < m) : (basicOpen 𝒜 f).toScheme ≅ Spec (.of <| Away 𝒜 f)`
  Direction: **D₊(f) ⟶ Spec (A_f)** on `.hom` (= `basicOpenToSpec 𝒜 f`, via `basicOpenIsoSpec_hom`). This is THE `D₊(f) ≅ Spec A_f`.
- **`AlgebraicGeometry.Proj.basicOpenIsoAway`** — Basic.lean:176, `@[simps! -isSimp hom]`
  `CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, basicOpen 𝒜 f)` — ring-level iso (`asIso (awayToSection 𝒜 f)`), i.e. `awayToSection` is an iso for homogeneous positive-degree `f`.
- **`AlgebraicGeometry.Proj.awayι`** — Basic.lean:186
  `noncomputable def awayι (f_deg : f ∈ 𝒜 m) (hm : 0 < m) : Spec (.of <| Away 𝒜 f) ⟶ Proj 𝒜` = `(basicOpenIsoSpec …).inv ≫ (basicOpen 𝒜 f).ι`. The open immersion Spec(A_f) → Proj. `instance : IsOpenImmersion (awayι …)` at Basic.lean:193; `opensRange_awayι` (:196) says its range is `basicOpen 𝒜 f`.
- `basicOpenIsoSpec_inv_ι` — Basic.lean:190 (`@[reassoc]`): `(basicOpenIsoSpec …).inv ≫ (basicOpen 𝒜 f).ι = awayι …`.
- `basicOpenToSpec_app_top` — Basic.lean:144; `awayι_toSpecZero` — Basic.lean:206.

**Naturality of this iso w.r.t. inclusion of basic opens — YES, and additionally the pullback identification:**
- `basicOpenToSpec_SpecMap_awayMap` (Basic.lean:240) and `SpecMap_awayMap_awayι` (Basic.lean:248), above.
- **`AlgebraicGeometry.Proj.pullbackAwayιIso`** — Basic.lean:256
  `noncomputable def pullbackAwayιIso (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') (hx : x = f * g) : Limits.pullback (awayι 𝒜 f f_deg hm) (awayι 𝒜 g g_deg hm') ≅ Spec (.of <| Away 𝒜 x)`
  — "D₊(f) ×[Proj 𝒜] D₊(g) ≅ D₊(fg)". This is the **two-fold-overlap identification** for the Proj basic-open cover.
  - `pullbackAwayιIso_hom_awayι` (:265), `pullbackAwayιIso_hom_SpecMap_awayMap_left/right` (:272/:279), `pullbackAwayιIso_inv_fst/snd` (:289/:295) — all `@[reassoc (attr := simp)]`, expressing the fst/snd legs as `Spec.map (awayMap …)`.
- `awayι_preimage_basicOpen` — Basic.lean:301: `awayι 𝒜 f f_deg hm ⁻¹ᵁ basicOpen 𝒜 g = PrimeSpectrum.basicOpen (Away.isLocalizationElem f_deg g_deg)`.
- The affine open cover: `affineOpenCoverOfIrrelevantLESpan` (Basic.lean:321), `affineOpenCover` (Basic.lean:336).

Internal Scheme.lean analogues (over `A⁰_ f`, not needed if you use the `AlgebraicGeometry.Proj` layer): `ProjectiveSpectrum.Proj.toSpec` (Scheme.lean:653, `(Proj| pbo f) ⟶ Spec (A⁰_ f)`), `isIso_toSpec` (:818), `projIsoSpec` (:835). Note: there is **no** `Proj.awayToSpec`, `Proj.awayιIso`, `Proj.toSpec`, or `Proj.awayIso` under the `AlgebraicGeometry.Proj` namespace — the names are exactly `basicOpenToSpec`, `basicOpenIsoSpec`, `basicOpenIsoAway`, `awayι`.

---

## 5. `HomogeneousLocalization.Away` and the map `A_f → A_{fg}`

`HomogeneousLocalization.lean`, ambient `{ι σ A}` graded (`[AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜]`):

- **`HomogeneousLocalization.Away`** — line 601
  `abbrev Away (𝒜 : ι → σ) (f : A) := HomogeneousLocalization 𝒜 (Submonoid.powers f)`
  The degree-0 away localization `A⁰_f`.
  - `Away.mk 𝒜 hf n x hx` — line 609 (the fraction `x / fⁿ`); `Away.val_mk` (:613); `Away.mk_surjective` (:618).

- **`HomogeneousLocalization.awayMap`** — line 820 ← THE canonical `A_f → A_{fg}` map
  Ambient (line 776): `{e : ι} {f g : A} (hg : g ∈ 𝒜 e) {x : A} (hx : x = f * g)`.
  `def awayMap (𝒜 : ι → σ) (hg : g ∈ 𝒜 e) (hx : x = f * g) : Away 𝒜 f →+* Away 𝒜 x`
  A `RingHom`, "taking `a/fⁱ ↦ a·gⁱ/(fg)ⁱ`". Requires `g` homogeneous (`hg`) and `x = f*g` (`hx`).
  - `awayMap_mk` — line 863 (`@[simp]`): `awayMap 𝒜 hg hx (Away.mk 𝒜 hf n a ha) = Away.mk 𝒜 (hx ▸ mul_mem_graded hf hg) n (a*gⁿ) (…)`.
  - `val_awayMap` — line 837; `val_awayMap_mk` — line 849 (`… = Localization.mk (a*gⁱ) ⟨xⁱ, …⟩`).
  - `awayMap_fromZeroRingHom` — line 842 (commutes with `𝒜 0`).
  - **`HomogeneousLocalization.awayMapₐ`** — line 855: the same map as an `𝒜 0`-algebra hom `Away 𝒜 f →ₐ[𝒜 0] Away 𝒜 x` (`awayMapₐ_apply` :859).
  - `Away.isLocalization_mul` — line 883: with `awayMap`'s algebra structure, `Away 𝒜 x` is the localization of `Away 𝒜 f` away from `Away.isLocalizationElem` (line 877). This is what makes `awayMap` a genuine localization inclusion.

- Also (general functoriality, different signature): **`HomogeneousLocalization.mapId`** — line 694
  `abbrev mapId (𝒜) {P Q : Submonoid A} (h : P ≤ Q) : HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization 𝒜 Q := map (.id _) h`
  (`map` at line 671). `awayToSection` is defined pointwise via `mapId 𝒜 (Submonoid.powers_le.mpr x.2)`.
  There is also `HomogeneousLocalization.Away.map` (line 724, functoriality along a graded ring hom `g : 𝒜 →+*ᵍ ℬ`) — a *different* map (`Away 𝒜 f →+* Away ℬ (g f)`), not the localization-inclusion you want.

There is **no** `HomogeneousLocalization.mapAway`; the name is `awayMap` (ring) / `awayMapₐ` (algebra).

---

## 6. Does `awayToSection` respect `*`, `1`, `^`?

**Yes.** `ProjectiveSpectrum.Proj.awayToSection` (Scheme.lean:592) is `CommRingCat.ofHom` of a bundled `RingHom` whose `map_mul'` (:604), `map_one'` (:606), `map_add'` (:603), `map_zero'` (:605) are all provided; hence it preserves `+, *, 0, 1` and therefore `^` (and `Units.map` applies, as the project does). The wrapper `Proj.awayToSection` (Basic.lean:135) inherits this. The presheaf restriction `(Proj 𝒜).presheaf.map _` is a `CommRingCat` morphism (ring hom) too, so the composite in `awayMap_awayToSection` is a ring hom on both sides — products and powers are preserved. There is no single named "`awayToSection_pow`"; it follows from `map_pow`/`map_mul` applied to `(awayToSection …).hom`.

---

## Project-side findings (grep under `AlgebraicJacobian/`)

- **The project already uses `Proj.awayToSection` and builds an overlap ring hom** — `AlgebraicJacobian/Picard/SerreTwist.lean`:
  - `Proj.awayToSection (homogeneousSubmodule n (ULift ℤ)) (X i * X j)` at SerreTwist.lean:196, inside
  - **`SerreTwist.overlapRingHom`** — SerreTwist.lean:190
    `def overlapRingHom (i j : n) : Away (homogeneousSubmodule n (ULift ℤ)) (X i * X j) →+* Γ(pullback ((basicOpenCover n).f i) ((basicOpenCover n).f j), ⊤)`
    = `(overlapHom i j).appTop.hom.comp ((Proj.basicOpen … (X i*X j)).topIso.inv.hom).comp (Proj.awayToSection … (X i*X j)).hom`.
    This is the project's existing bridge from the degree-0 away ring `A⁰_{XᵢXⱼ}` to sections on the scheme-theoretic overlap — but it routes through `overlapHom` (an `IsOpenImmersion.lift` into `D₊(XᵢXⱼ)`, SerreTwist.lean:179) and `.appTop`, NOT through `awayMap`/`awayMap_awayToSection`. `overlapUnit` (:200), `overlapUnit_self` (:243), `twistTransition` (:249), `twistTransition_self` (:261, "C1"), `twistTransition_cocycle` (:302, "C2") sit on top.
  - `Proj.basicOpen_mul` is used at SerreTwist.lean:156 (`range_overlap_le`).
- `Proj.basicOpen` cover machinery: `AlgebraicJacobian/Picard/SerreTwist.lean:71,96–101,154–171` (`basicOpenCover`).
- **No project use of `awayMap_awayToSection`, `HomogeneousLocalization.awayMap`, `Proj.awayι`, `Proj.pullbackAwayιIso`, `Proj.basicOpenIsoSpec`, or `Proj.basicOpenToSpec` was found.** The `basicOpenIsoSpecAway`/`specBasicOpen` occurrences in `AlgebraicJacobian/Cohomology/*` (CechTermAcyclic, AffineSerreVanishing, QcohRestrictBasicOpen, QcohTildeSections) and the many `PrimeSpectrum.basicOpen_mul` uses are for the **affine `Spec` / `PrimeSpectrum`** basic-open theory, NOT the `Proj` graded theory — different API, do not confuse them.
- **Triple-overlap helpers in the project are purely ring-theoretic (Grassmannian), not Proj-sheaf.** `AlgebraicJacobian/Picard/GrassmannianCells.lean` (lines 292–1110) has `triple-overlap transition maps` `Θ_{I,J}`, cocycle `Φ = id`, etc., over localized matrix rings — unrelated to `awayToSection`. `SerreTwist.twistTransition_cocycle` (the Proj "C2") does not currently use any `awayMap`-based triple-overlap identification; it works at the level of `overlapUnit`/`pullbackBaseChangeTransport`.

**Bottom line for a Proj basic-open cover restriction/triple-overlap identification:** the ready-made Mathlib building block is `AlgebraicGeometry.Proj.awayMap_awayToSection` (Basic.lean:222) together with `HomogeneousLocalization.awayMap` (HomogeneousLocalization.lean:820) and `Proj.pullbackAwayιIso` (Basic.lean:256); the project has not yet wired these in (it uses the `overlapHom`/`appTop` route in SerreTwist instead).
