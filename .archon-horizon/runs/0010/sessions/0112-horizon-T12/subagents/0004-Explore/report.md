I now have a comprehensive picture. Here is the structured report.

---

# CoherentSheafFlat: producers, consumers, and the `compHom` handling recipe

## 0. The predicate and its `letI Module.compHom` idiom

`Scheme.CoherentSheafFlat` — `AlgebraicJacobian/Picard/FlatteningStratification.lean:1416`:

```lean
def CoherentSheafFlat {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Prop :=
  ∀ {U : S.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U),
    letI : Module Γ(S, U) Γ(F, V) := Module.compHom _ (f.appLE U V e).hom
    Module.Flat Γ(S, U) Γ(F, V)
```

Every proof site opens with `intro U hU V hV eV` and immediately re-establishes the very same instance locally with `letI : Module Γ(...) Γ(...) := Module.compHom _ (f.appLE U V e).hom` so the goal's `Module.Flat` typechecks against a named instance. The entire engineering problem in this codebase is that this `compHom` instance is definitionally distinct from (a) the native `Γ(X,V)`-module, (b) the `compHom` instance for a different `appLE` witness, and (c) `Module.Flat` obtained over another ring — and every bridge below exists to reconcile those.

There are **six reusable infrastructure lemmas** that all sites route through; I quote them first, then give the per-site table.

---

## 1. Infrastructure lemmas for the `compHom` instance

### 1a. `appLE` elementwise coherence (fibre-side and base-side)
`GenericFlatnessGeometric.lean:89` (`appLE_res_apply`) and `:99` (`appLE_base_res_apply`). These are the workhorses that discharge the `IsScalarTower` obligation when two `appLE`s land on nested opens:

```lean
private lemma appLE_res_apply {S X : Scheme.{u}} (p : X ⟶ S) {U : S.Opens}
    {W W' : X.Opens} (e : W ≤ p ⁻¹ᵁ U) (h : W' ≤ W) (u : Γ(S, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((p.appLE U W e).hom u) =
      (p.appLE U W' (h.trans e)).hom u := by
  have h1 := congrArg (fun (φ : Γ(S, U) ⟶ Γ(X, W')) => φ.hom u)
    (Scheme.Hom.appLE_map (f := p) e (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h1
```
```lean
private lemma appLE_base_res_apply {S X : Scheme.{u}} (p : X ⟶ S) {U U' : S.Opens}
    {W : X.Opens} (h : U' ≤ U) (e' : W ≤ p ⁻¹ᵁ U') (e : W ≤ p ⁻¹ᵁ U) (u : Γ(S, U)) :
    (p.appLE U' W e').hom ((S.presheaf.map (homOfLE h).op).hom u) =
      (p.appLE U W e).hom u := by
  ... simpa ... using (Scheme.Hom.map_appLE (f := p) e' (homOfLE h).op) ...
```
(FlatteningStratificationUniversal.lean has a twin `appLE_base_res_apply'` used at `:338`.)

### 1b. `flat_sections_congr` — transfer `Module.Flat` across an equality of opens
`GenericFlatnessGeometric.lean:110`. Used whenever `D(c) = D(c')` etc. force two different `compHom` instances on the same carrier:
```lean
private theorem flat_sections_congr {S X : Scheme.{u}} (p : X ⟶ S) (F : X.Modules)
    {U₀ : S.Opens} {O₁ O₂ : X.Opens} (hEq : O₁ = O₂)
    (e₁ : O₁ ≤ p ⁻¹ᵁ U₀) (e₂ : O₂ ≤ p ⁻¹ᵁ U₀)
    (h : letI : Module Γ(S, U₀) Γ(F, O₁) := Module.compHom _ (p.appLE U₀ O₁ e₁).hom
         Module.Flat Γ(S, U₀) Γ(F, O₁)) :
    letI : Module Γ(S, U₀) Γ(F, O₂) := Module.compHom _ (p.appLE U₀ O₂ e₂).hom
    Module.Flat Γ(S, U₀) Γ(F, O₂) := by
  subst hEq; exact h
```
The `subst` collapses the two `appLE` witnesses (proof-irrelevance of the `≤`).

### 1c. `flat_compHom_congr` — transfer `Module.Flat` between `compHom` and the native structure along a pointwise-identity ring map
`FlatteningStratificationUniversal.lean:136`. This is the bridge for `𝟙 T`, where `(𝟙 T).appLE W W e` is pointwise `id` but not defeq to `id`:
```lean
private lemma flat_compHom_congr {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] (f : R →+* R) (hf : ∀ r, f r = r) :
    (letI : Module R M := Module.compHom M f
     Module.Flat R M) ↔ Module.Flat R M := by
  have h : (Module.compHom M f : Module R M) = ‹Module R M› :=
    Module.ext' _ _ fun r m => by show f r • m = r • m; rw [hf r]
  exact (congrArg (fun i : Module R M => @Module.Flat R M _ _ i) h).to_iff
```
Paired with `id_appLE_apply` (`FlatteningStratificationUniversal.lean:150`: `((𝟙 T).appLE W W e).hom r = r` via `Scheme.id_appLE`).

### 1d. `Module.Flat.of_isLocalizedModule_algebra` — mixed-base flatness stability (fibre-side localization)
`GenericFlatnessGeometric.lean:131`. This is the key new Mathlib-style lemma that lets a fibre-side localization (`Γ(F,D(β)) → Γ(F,D(c))`) preserve flatness over the *base* ring:
```lean
theorem _root_.Module.Flat.of_isLocalizedModule_algebra {R B : Type v} [CommRing R]
    [CommRing B] [Algebra R B] (p : Submonoid B) {N N' : Type v} [AddCommGroup N]
    [Module R N] [Module B N] [IsScalarTower R B N] [AddCommGroup N'] [Module R N']
    [Module B N'] [IsScalarTower R B N'] (g : N →ₗ[B] N') [IsLocalizedModule p g]
    [Module.Flat R N] : Module.Flat R N' := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ I
  rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := B)]
  rw [← IsLocalizedModule.map_lTensor (S := p) (g := g) (f := I.subtype)]
  exact IsLocalizedModule.map_injective p ... (Module.Flat.lTensor_preserves_injective_linearMap ...)
```

### 1e. `isLocalizedModule_powers_restrictScalars_of_algebraMap` — base-ring descent of a localization
`AlgebraicJacobian/Cohomology/QcohTildeSections.lean:664`. Converts `IsLocalizedModule (powers (algebraMap R A f)) φ` (over `A`) into `IsLocalizedModule (powers f) (φ.restrictScalars R)` (over `R`):
```lean
lemma isLocalizedModule_powers_restrictScalars_of_algebraMap
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N] (f : R) (φ : M →ₗ[A] N)
    (h : IsLocalizedModule (Submonoid.powers (algebraMap R A f)) φ) :
    IsLocalizedModule (Submonoid.powers f) (φ.restrictScalars R)
```

### 1f. `flat_of_ringHom_comp_bijective` — flatness across a bijective ring-map factorization (base-leg iso)
`GenericFlatnessGeometric.lean:1405`. Handles `ψ = φ ∘ ρ` with `ρ` bijective, via `Module.Flat.trans`:
```lean
private theorem flat_of_ringHom_comp_bijective {R R' O M : Type v} [CommRing R]
    [CommRing R'] [CommRing O] [AddCommGroup M] [Module O M] (ρ : R →+* R')
    (hρ : Function.Bijective ρ) (φ : R' →+* O) (ψ : R →+* O) (hψ : ψ = φ.comp ρ)
    (h : letI : Module R' M := Module.compHom M φ; Module.Flat R' M) :
    letI : Module R M := Module.compHom M ψ; Module.Flat R M := by
  subst hψ
  letI : Module R' M := Module.compHom M φ
  letI : Module R M := Module.compHom M (φ.comp ρ)
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Flat R R' := Module.Flat.of_linearEquiv
      ((LinearEquiv.ofBijective (Algebra.linearMap R R') (by rw [hcoe]; exact hρ)).symm)
  haveI : IsScalarTower R R' M := ⟨fun r r' m => by
      change φ (ρ r * r') • m = φ (ρ r) • (φ r' • m); rw [map_mul, mul_smul]⟩
  exact Module.Flat.trans R R' M
```

---

## 2. The canonical `compHom`/`IsScalarTower`/`Flat`-transfer recipe (verbatim template)

The idioms requested in (b)(i)–(iii) appear together most cleanly in `flat_section_chartBasic` (`GenericFlatnessGeometric.lean:164`). This is the exact template to imitate:

- **(i) introduce compHom module** — `GenericFlatnessGeometric.lean:176,188,198,232,241`:
```lean
letI : Module Γ(S, U₀) Γ(F, Wj) := Module.compHom _ (p.appLE U₀ Wj eWj).hom
letI : Module Γ(X, Wj) Γ(F, X.basicOpen β) :=
    Module.compHom _ (algebraMap Γ(X, Wj) Γ(X, X.basicOpen β))
```
- **(i′) the algebra on the ring side** — `:197,243`: `letI : Algebra Γ(S, U₀) Γ(X, Wj) := (p.appLE U₀ Wj eWj).hom.toAlgebra`
- **(ii) IsScalarTower via `of_algebraMap_smul`**, two flavours. Trivial (defeq) `:190,200,245`:
```lean
haveI : IsScalarTower Γ(X, Wj) Γ(X, X.basicOpen β) Γ(F, X.basicOpen β) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
```
Non-trivial (needs `appLE_res_apply`), `:202`:
```lean
haveI : IsScalarTower Γ(S, U₀) Γ(X, Wj) Γ(F, X.basicOpen β) :=
    IsScalarTower.of_algebraMap_smul (fun a n => by
      change (X.presheaf.map (homOfLE (X.basicOpen_le β)).op).hom
          ((p.appLE U₀ Wj eWj).hom a) • n
        = (p.appLE U₀ (X.basicOpen β) eβ).hom a • n
      rw [appLE_res_apply p eWj (X.basicOpen_le β) a])
```
- **(iii) transfer `Module.Flat`** across instances — several tools chained `:215–256`:
```lean
haveI hflatLoc : Module.Flat Γ(S, U₀) (LocalizedModule (Submonoid.powers g) Γ(F, Wj)) := by
    haveI : Module.Flat (Localization.Away g) (LocalizedModule ...) := inferInstance
    exact (Module.flat_iff_of_isLocalization (Localization.Away g)
      (Submonoid.powers g) (LocalizedModule ...)).mp this
haveI hflatNβ : Module.Flat Γ(S, U₀) Γ(F, X.basicOpen β) :=
    Module.Flat.of_linearEquiv
      (IsLocalizedModule.iso (Submonoid.powers g)
        ((Scheme.Modules.restrictBasicOpenₗ F β).restrictScalars Γ(S, U₀))).symm
...
haveI hflatC' : Module.Flat Γ(S, U₀) Γ(F, X.basicOpen c') :=
    Module.Flat.of_isLocalizedModule_algebra (Submonoid.powers c')
      (Scheme.Modules.restrictBasicOpenₗ F c')
exact flat_sections_congr p F hDc' ec' eO hflatC'
```
Base-ring descent step at `:209`:
```lean
haveI hlocA : IsLocalizedModule (Submonoid.powers g)
    ((Scheme.Modules.restrictBasicOpenₗ F β).restrictScalars Γ(S, U₀)) := by
  refine isLocalizedModule_powers_restrictScalars_of_algebraMap g _ ?_
  exact hlocB
```

The **two-base-exchange** finale (used at the end of `flat_section_pair` `:399` and `flat_section_of_affine_cover` `:1008`):
```lean
have h2 : Module.Flat Γ(S, S.basicOpen (aa x)) Γ(F, X.basicOpen r.1) :=
  (Module.flat_iff_of_isLocalization (R := Γ(S, U₀))
    Γ(S, S.basicOpen (aa x)) (Submonoid.powers (aa' x)) Γ(F, X.basicOpen r.1)).mpr hA
exact (Module.flat_iff_of_isLocalization (R := Γ(S, U))
    Γ(S, S.basicOpen (aa x)) (Submonoid.powers (aa x)) Γ(F, X.basicOpen r.1)).mp h2
```
with the two localizations provided by `hU.isLocalization_basicOpen (aa x)` (`:360`) and `hU₀.isLocalization_of_eq_basicOpen (aa' x) (homOfLE haU₀) (haa' x)` (`:372`), and the span glue `Module.flat_of_isLocalized_span` at `:342`.

`flat_section_pair` (`:269`) and `flat_section_of_affine_cover` (`:861`) are structurally identical twins of this recipe (base=`S`/fibre=`X` vs base=`T`/fibre=`Y`); the latter is the general "cover ⟹ all pairs" affine-locality engine.

---

## 3. Producer / consumer sites, by file

Legend: **P** = produces `CoherentSheafFlat`; **C** = consumes it (hypothesis); **B** = bridge (extracts `Module.Flat` from, or assembles into, the predicate).

### `AlgebraicJacobian/Picard/GenericFlatnessGeometric.lean`

| Decl | line | role | how `compHom`/`Flat` is handled |
|---|---|---|---|
| `genericFlatness_of_finite_sections` | 453 | P (raw `∀`-form, not the named predicate) | goal-level `letI ... Module.compHom ...` at `:461`; body = `flat_section_pair` (recipe §2). Per-chart `Algebra` via `.hom.toAlgebra` `:492`, tower `of_algebraMap_smul ... rfl` `:494`; freeness via `GenericFreeness.genericFlatnessAlgebraic` `:499` + `free_localizedModule_powers_mul` `:526` |
| `genericFlatness` | 534 | P | `= genericFlatness_of_finite_sections` |
| `flat_section_pullback_piece` | 748 | P (per-piece, base-change) | builds 5 `.toAlgebra` corners `:759–767`; towers via `of_algebraMap_eq' rfl` `:769` and a computed one using `Scheme.Hom.appLE_comp_appLE` `:782`; `Algebra.IsPushout` from `isPushout_appLE_pullback_piece` `:786`; closes with `Module.Flat.of_isPushout` `:813` fed `IsBaseChange` from `pullback_app_isoTensor_baseMap_sectionLinearEquiv` `:808` |
| `flat_section_of_affine_cover` | 861 | P/B (cover ⟹ all pairs) | full recipe §2; `Module.Flat.of_isLocalizedModule_algebra` `:976`, `flat_sections_congr` `:982`, double `flat_iff_of_isLocalization` `:1009,1012` |
| `coherentSheafFlat_of_iso` | 1077 | B (transport along `G ≅ G'`) | two `compHom` instances on `Γ(G,V)`,`Γ(G',V)` `:1080–1081`; `Module.Flat.of_linearEquiv` `:1083` with the equiv built from `Scheme.Modules.Hom.app e.inv/​e.hom` and `map_smul' := Scheme.Modules.Hom.app_smul e.inv` `:1102` |
| `flat_stratum_of_irreducible` | 1137 | **P** (first named-predicate producer) | assembles `hchart` (per-point flat pieces via `flat_section_pullback_piece` `:1320` + `flat_sections_congr` `:1335`), globalizes with `flat_section_of_affine_cover` `:1348` into `hallκ : CoherentSheafFlat ...` `:1339`, then `coherentSheafFlat_of_iso` along `pullbackComp` `:1386` |
| `coherentSheafFlat_of_comp_isIso` | 1434 | **C→P** (base-leg iso) | consumes `h : CoherentSheafFlat (q ≫ w)`; factors `q.appLE` via `Scheme.Hom.appLE_comp_appLE` `:1453`; closes with `flat_of_ringHom_comp_bijective` `:1460` (§1f), bijectivity from `ConcreteCategory.bijective_of_isIso` |
| `flatLocusReduction` | 1522 | **P** (Noetherian induction) | produces `∀ i, CoherentSheafFlat (pullback.snd π (ι i)) ...` `:1528`; the flat conjunct is discharged at `:1755` by `hΩflat c (St c) inf_le_left` (from `flat_stratum_of_irreducible`) and `h4' i'` (IH) |
| `flatLocusAssembly` | 1785 | **C→P** | destructures `flatLocusReduction` `:1795`, re-emits `hflat` unchanged `:1792` |
| `flatteningStratification` | 1831 | **C→P** | `= flatLocusReduction` conjuncts reordered `:1839` |
| `flatLocusStratification` | 1880 | **C→P** (to `𝟙 (S_ e)`) | for `e < card I`: `coherentSheafFlat_of_comp_isIso (𝟙 ...) (pullback.snd (𝟙 S) (ι₀ ...))` `:1977` + `Category.id_comp` `:1981`; for empty stratum `:1984`: builds `compHom` at `:1991`, `Module.Free.of_subsingleton'` `:1992` ⟹ `inferInstance` |
| `flatteningStratification.ofCurve` | 2021 | **C→P** | `= flatteningStratification (pullback.snd C.hom T.hom) F` |

### `AlgebraicJacobian/Picard/FlatteningStratificationUniversal.lean`

| Decl | line | role | notes |
|---|---|---|---|
| `flat_sections_of_coherentSheafFlat_id` | 160 | **B** (extract `Module.Flat Γ(T,W) Γ(G,W)` from `CoherentSheafFlat (𝟙 T)`) | `= (flat_compHom_congr ((𝟙 T).appLE W W (le_refl W)).hom (id_appLE_apply _)).mp (h hW hW (le_refl W))` — the canonical `𝟙 T` unwrapper |
| `coherentSheafFlat_id_of_charts` | 170 | **P** (charts ⟹ `𝟙 T`) | `= flat_section_of_affine_cover (𝟙 T) ...` wrapping each chart flat through `flat_compHom_congr ... .mpr` `:178` |
| `strataData_le_ker` | 287 | **C** | uses `flat_sections_of_coherentSheafFlat_id hflat hW` `:312` to get `Module.Flat Γ(T,W) ...`, feeding `relMatrix_eq_zero_of_flat` |
| `existsUnique_stratumLift` | 344 | **C** | passes `hflat` to `strataData_le_ker` `:355` |
| `coherentSheafFlat_stratum` | 374 | **P** (`𝟙 (stratum ...)`) | per-chart free-of-`relMatrix=0` `:417`, assembled by `coherentSheafFlat_id_of_charts` `:420` |
| `coherentSheafFlat_id_pullback` | 538 | **C→P** (flat stable under pullback, `𝟙`) | `flat_sections_of_coherentSheafFlat_id h hV` `:558` then `Module.Flat.of_linearEquiv eqv.symm` `:564` (base-change section equiv); reassembled via `flat_section_of_affine_cover (𝟙 T')` `:566` |
| `coherentSheafFlat_rankStratum` | 659 | **P** | `coherentSheafFlat_of_iso (𝟙 ...) (pullbackComp ...).app F` over `coherentSheafFlat_stratum` `:664` |
| `isOpen_pointRank_pullback_eq` | 704 | **C** | `flat_sections_of_coherentSheafFlat_id hflat hW` `:726` |
| `existsUnique_factor_rankStratum` | 770 | **C→P** | internally rebuilds `hflat_q : CoherentSheafFlat (𝟙 T) ...` via `coherentSheafFlat_of_iso` along `pullbackComp`/`pullbackCongr` `:794` |
| `flatLocusStratification_universal` | 878 | **P + C** | produces both the per-stratum `CoherentSheafFlat (𝟙 (S_ f))` (`= coherentSheafFlat_rankStratum` `:894`) **and** consumes a hypothesis `CoherentSheafFlat (𝟙 T) (pullback φ …)` in the universal-property clause `:886–888` |

### `AlgebraicJacobian/Picard/QuotFunctorDef.lean`

| Decl | line | role | notes |
|---|---|---|---|
| `CoherentSheafFlat.of_isPullback` | 414 | **P (base change) — but `sorry`** | body is literally `by sorry` at `:419`. Statement: from `IsPullback g' f' f g`, `hF : CoherentSheafFlat f F` ⟹ `CoherentSheafFlat f' ((pullback g').obj F)` |
| `QuotFamily.flat` (structure field) | 488 | **C** (datum) | `flat : CoherentSheafFlat (pullback.snd π T.hom) F` |
| `QuotFamily.pullbackAlong.flat` | 548 | **C→P** | `= CoherentSheafFlat.of_isPullback (quotBaseSquare π ψ) x.F _ x.flat hU hV e` (depends on the `sorry` above) |

Note: `Modules.HasProperSupport.of_isPullback` (`:427`) and `hilbertFunction_quotBaseMap` (`:445`) are also `sorry`, i.e. the base-change transport of the predicate is not yet proved — every downstream Quot-functor consumer inherits that gap.

---

## 4. Helper/bridging lemmas naming `appLE` (compositions ↔ `algebraMap`)

- `Scheme.Hom.appLE_comp_appLE` (Mathlib) is invoked to fold two `appLE`s into one across a scheme composition, at three load-bearing spots:
  - `flat_section_pullback_piece`, `GenericFlatnessGeometric.lean:782`:
    ```lean
    have h1 : iX.appLE US UX hUSX ≫ g.appLE UX (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_left =
        f.appLE US UT hUST ≫ iY.appLE UT (g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) inf_le_right := by
      rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact key (g ≫ iX) H.w.symm _ _
    ```
    used to prove the `IsScalarTower` via `of_algebraMap_eq' (by ... exact congrArg CommRingCat.Hom.hom h1)` `:771`.
  - `coherentSheafFlat_of_comp_isIso`, `GenericFlatnessGeometric.lean:1450`:
    ```lean
    have hfact : q.appLE U V eV =
        (inv w).appLE U ((inv w) ⁻¹ᵁ U) le_rfl ≫
          (q ≫ w).appLE ((inv w) ⁻¹ᵁ U) V eV' := by
      rw [Scheme.Hom.appLE_comp_appLE]; ... simp only [hmor]
    ```
- `.hom.toAlgebra` on an `appLE` is the universal way the base ring is turned into an algebra so `IsScalarTower.of_algebraMap_smul`/`of_algebraMap_eq'` become available — e.g. `(p.appLE U₀ Wj eWj).hom.toAlgebra` `:197`, `(iX.appLE US UX hUSX).hom.toAlgebra` `:759`, and the composite `((g.appLE …).hom.comp (iX.appLE …).hom).toAlgebra` `:766` (this is what makes the pushout square's diagonal an algebra, matched by `of_algebraMap_eq' rfl`).
- `appLE`↔`algebraMap` identifications used as `rfl`/`show`: e.g. `pointRank_pullback` `:263` `have h5 : algebraMap Γ(X, V) Γ(Y, W) = (g.appLE V W hWle).hom := rfl`; and `IsAffineOpen.comap_primeIdealOf_appLE` `:261`.
- `id_appLE_apply` (`FlatteningStratificationUniversal.lean:150`) is the `appLE`-of-identity bridge (`= r` via `Scheme.id_appLE` + `presheaf_map_self`), the input to `flat_compHom_congr`.
- `appLE_base_res_apply'` at `FlatteningStratificationUniversal.lean:338` (used in `strataData_le_ker` to rewrite `q.app U r` restricted to `W` as `q.appLE`).

---

## 5. GenericFreeness section: two-localization / base-change / freeness transports

Section header: `namespace GenericFreeness` at `FlatteningStratification.lean:201` (ends `:1379`). The recipe you can imitate lives in **`free_localizedModule_powers_mul`** (`:288`) — the canonical "enlarge the inverted element via a second localization + cancel base change" move. Full excerpt `:288–326`:

```lean
theorem free_localizedModule_powers_mul (A : Type*) (M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] (f g : A)
    (hf : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free (Localization.Away (f * g)) (LocalizedModule (Submonoid.powers (f * g)) M) := by
  haveI := hf
  letI : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away f)
      (P := Localization.Away (f * g)) f g).toAlgebra
  haveI : IsScalarTower A (Localization.Away f) (Localization.Away (f * g)) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away f)
        (P := Localization.Away (f * g)) f g a).symm
  have e_f : (Localization.Away f) ⊗[A] M ≃ₗ[Localization.Away f]
      LocalizedModule (Submonoid.powers f) M :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).equiv
  have e_fg : (Localization.Away (f * g)) ⊗[A] M ≃ₗ[Localization.Away (f * g)]
      LocalizedModule (Submonoid.powers (f * g)) M :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers (f * g)) (Localization.Away (f * g))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f * g)) M)).equiv
  have e_cancel : (Localization.Away (f * g)) ⊗[Localization.Away f]
      ((Localization.Away f) ⊗[A] M) ≃ₗ[Localization.Away (f * g)]
      (Localization.Away (f * g)) ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away f)
      (Localization.Away (f * g)) (Localization.Away (f * g)) M
  have e_congr : ... :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (Localization.Away (f * g)) (Localization.Away (f * g))) e_f
  exact Module.Free.of_equiv'
    (inferInstance : Module.Free (Localization.Away (f * g)) (... ⊗ ...))
    (e_congr.symm.trans (e_cancel.trans e_fg))
```

Precise pattern inventory in this section:
- **`(IsLocalization.Away.awayToAwayRight … f g).toAlgebra`** — `:296` (establishes `A_f → A_{fg}` as an algebra).
- **`IsScalarTower.of_algebraMap_eq`** with `IsLocalization.Away.awayToAwayRight_eq` — `:298–301` (the `A → A_f → A_{fg}` tower). (Contrast: the geometric file uses `of_algebraMap_smul`/`of_algebraMap_eq' rfl`; this algebraic section uses `of_algebraMap_eq` with the explicit `awayToAwayRight_eq`.)
- **`TensorProduct.AlgebraTensorModule.cancelBaseChange`** — `:314` (`A_{fg} ⊗_{A_f} (A_f ⊗_A M) ≅ A_{fg} ⊗_A M`).
- **`IsLocalizedModule.isBaseChange … .equiv`** — `:304,308` (identifies `A_f ⊗_A M ≅ LocalizedModule (powers f) M`).
- **`TensorProduct.AlgebraTensorModule.congr`** + **`Module.Free.of_equiv'`** — `:320,322` (transport freeness across the composed equiv).
- **`GenericallyFree.of_linearEquiv`** (`:329`) uses `IsLocalizedModule.iso … ∘ₗ e.toLinearMap` + `.extendScalarsOfIsLocalization (powers f) (Localization.Away f)` + `Module.Free.of_equiv'` `:335–340`.
- **`genericallyFree_of_exact`** (`:347`, the splicing/dévissage step): localizes a SES at `f₁*f₃`, using `free_localizedModule_powers_mul` on both ends (`:357,358`) then `IsLocalizedModule.map … .extendScalarsOfIsLocalization` (`:363`) and (further down) `ModuleCat.free_shortExact`.

Note there is **no** `Module.Flat.baseChange`, `Module.Flat.trans`, `IsLocalization.flat`, or `Localization.flat` inside the GenericFreeness section — this section works entirely in `Module.Free` and pushes flatness conversion downstream (into `flat_section_chartBasic`, via `Module.flat_iff_of_isLocalization` + `Module.Flat.of_linearEquiv`). `Module.Flat.trans` appears only in `flat_of_ringHom_comp_bijective` (`GenericFlatnessGeometric.lean:1427`), and `Module.Flat.baseChange` is name-checked only in docstrings (`GenericFlatnessGeometric.lean:552,679`). The genuine base-change flatness engine is `Module.Flat.of_isPushout` (`GenericFlatnessGeometric.lean:681`), which internally calls `Module.Flat.isBaseChange` + `Module.Flat.of_linearEquiv (hf.equiv.restrictScalars S).symm` (`:686–689`).

Domain-core reminders (same section, for completeness of the "Noether normalization" transports): `IsScalarTower.of_algebraMap_eq'` at `:752,1194`; `MvPolynomial.aeval` scalar-tower plumbing `:749,1193`; `IsScalarTower.algebraMap_apply` rewrites `:674,796`. The dévissage assembly is `genericallyFree_of_forall_quotient_prime` (`:827`) via `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`, with the extension case re-deriving `IsScalarTower A B Nᵢ` by `⟨fun a b n => by change (a • b) • n = algebraMap A B a • b • n; rw [Algebra.smul_def, mul_smul]⟩` (`:849–856`).

---

## 6. flatLocus proofs: how they bridge `compHom` flatness to localized flatness

The `flatLocus*` theorems (`flatLocusReduction :1522`, `flatLocusAssembly :1785`, `flatLocusStratification :1880`, and the moved-out `flatLocusStratification_universal` in FlatteningStratificationUniversal.lean:878) **do not themselves touch the `compHom` instance**. They consume the already-packaged `Scheme.CoherentSheafFlat` produced by the §1–§2 machinery and thread it verbatim. The bridging from `compHom` flatness to localized flatness happens one layer below them, in exactly these lemmas they (transitively) invoke:

- `flatLocusReduction` ← `flat_stratum_of_irreducible` ← `flat_section_of_affine_cover` (§2 recipe: `Module.Flat.of_isLocalizedModule_algebra`, `flat_sections_congr`, `Module.flat_iff_of_isLocalization` ×2, `Module.flat_of_isLocalized_span`) and ← `flat_section_pullback_piece` (`Module.Flat.of_isPushout`).
- `flatLocusStratification` ← `coherentSheafFlat_of_comp_isIso` (`flat_of_ringHom_comp_bijective` ⟹ `Module.Flat.trans`).
- `flatLocusStratification_universal` ← `coherentSheafFlat_rankStratum`/`coherentSheafFlat_stratum` (bridged through `flat_compHom_congr` in `flat_sections_of_coherentSheafFlat_id`, and `MatrixPresentation.free_of_relMatrix_eq_zero` for the free⟹flat step) and ← `existsUnique_factor_rankStratum`/`isOpen_pointRank_pullback_eq` on the consuming side, both of which unwrap via `flat_sections_of_coherentSheafFlat_id` (§1c) to obtain plain `Module.Flat Γ(T,W) Γ(_,W)`.

So the single reusable "compHom flatness → localized flatness" invocations to know are: `Module.flat_iff_of_isLocalization` (base exchange), `Module.Flat.of_isLocalizedModule_algebra` (fibre localization), `isLocalizedModule_powers_restrictScalars_of_algebraMap` (base descent), and `Module.flat_of_isLocalized_span` (span glue) — all in `flat_section_pair` / `flat_section_of_affine_cover`.

---

## 7. Exact signatures requested from `QuotScheme.lean`

### `restrictBasicOpenₗ` — the `LinearMap` (QuotScheme.lean:2587)
```lean
noncomputable def restrictBasicOpenₗ {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (f : Γ(X, U))
    [Module Γ(X, U) Γ(M, X.basicOpen f)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)] :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) where
  toFun := fun x => M.presheaf.map (homOfLE (X.basicOpen_le f)).op x
  map_add' := map_add _
  map_smul' := fun r x => by ... rw [Scheme.Modules.map_smul M ..., ← algebraMap_smul ...]; rfl
```
- **Over the ring**: `Γ(X, U)` (the section ring of the structure sheaf on the affine open `U`).
- **Source module**: `Γ(M, U)` (sections of `M` over `U`), native `Γ(X,U)`-module.
- **Target module**: `Γ(M, X.basicOpen f)` (sections of `M` over `D(f)`).
- **Required instance binders** (supplied by the caller, matching the `compHom` idiom): `[Module Γ(X, U) Γ(M, X.basicOpen f)]` and `[IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)]` — i.e. any `Γ(X,U)`-action on the target compatible via the scalar tower with its native `Γ(X, D(f))`-action and the algebra map `X.presheaf.map`. It is the map underlying `IsLocalizedModule`.
- Companion general-restriction map: `restrictₗ` (QuotScheme.lean:2571), `Γ(M, U) →ₗ[Γ(X, U)] Γ(M, V)` for any `i : V ⟶ U`, target carrying `Module.compHom _ (X.presheaf.map i.op).hom`.

### `isLocalizedModule_basicOpen` — the gap2 keystone (QuotScheme.lean:3033)
```lean
theorem isLocalizedModule_basicOpen (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    [Module Γ(X, U) Γ(M, X.basicOpen f)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)] :
    IsLocalizedModule (Submonoid.powers f) (restrictBasicOpenₗ M f) :=
  haveI := isQuasicoherent_pullback_fromSpec M hU
  isLocalizedModule_basicOpen_of_hP1 M hU
    (isIso_fromTildeΓ_of_isQuasicoherent ((Scheme.Modules.pullback hU.fromSpec).obj M)) f
```
Requires `[M.IsQuasicoherent]`, `hU : IsAffineOpen U`, and the same two instance binders as `restrictBasicOpenₗ`. Conclusion: the basic-open section restriction is `IsLocalizedModule (Submonoid.powers f)`.

### The quasi-compact variant actually used inside the flatness proofs (QuotScheme.lean:3441)
```lean
theorem isLocalizedModule_basicOpen_of_isCompact
    (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens}
    (hW : IsCompact (W : Set X)) (hsep : IsQuasiSeparated (W : Set X))
    (g : Γ(X, W))
    [Module Γ(X, W) Γ(M, X.basicOpen g)]
    [IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) Γ(M, X.basicOpen g)] :
    IsLocalizedModule (Submonoid.powers g) (restrictBasicOpenₗ M g)
```
This is the one every `flat_section_*` proof instantiates via `Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact F hW.isCompact hW.isQuasiSeparated r.1` (e.g. `GenericFlatnessGeometric.lean:194,239,329,917,973`). The affine-only `isLocalizedModule_basicOpen` (`hU.isCompact` implicit) is the one used in `FlatteningStratificationUniversal.lean:495` (`exists_presentationChart_mem`).

---

## 8. One caveat worth flagging

The **only base-change producer of the named predicate**, `CoherentSheafFlat.of_isPullback` (`QuotFunctorDef.lean:414`), is an unproved `sorry`. Every Quot-functor-level consumer of flatness (`QuotFamily.pullbackAlong.flat`, `QuotFunctorDef.lean:548`) rests on it. By contrast, the Nitsure §4 flattening-stratification chain in `GenericFlatnessGeometric.lean` / `FlatteningStratificationUniversal.lean` is self-contained and (per the in-file docstrings and the recipe above) sorry-free through `flatLocusStratification_universal`.
