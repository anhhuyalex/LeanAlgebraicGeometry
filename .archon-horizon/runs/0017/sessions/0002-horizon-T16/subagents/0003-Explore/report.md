# Scouting Report: Porting the Stacks-01EO Čech-Vanishing Seed to a General Scheme's Affine Opens

## 1. The algebraic heart — pure ring/module-level statement

**Home file: `AlgebraicJacobian/Cohomology/CechAcyclic.lean`** (NOT `TildeExactness.lean`/`AffineSerreVanishing.lean`/`QcohRestrictBasicOpen.lean`/`QcohTildeSections.lean` — those are downstream consumers/identification glue). The reusable algebraic core lives in `namespace SectionCechModule` (opens `CechLocalized AwayComparison`), variables `{R : Type u} [CommRing R] {ι : Type*} (s : ι → R) (M : Type u) [AddCommGroup M] [Module R M]`.

**Terms** (pure `R`-module data, no scheme/sheaf in sight):
- `CechAcyclic.lean:590` `CechLocalized.sprod {m} (σ : Fin m → ι) : R := ∏ k, s (σ k)` — the localizing element for a Čech multi-index.
- `CechAcyclic.lean:924` `abbrev SectionCechModule.dCoeff {m} (σ : Fin m → ι) : Type u := LocalizedModule (Submonoid.powers (sprod s σ)) M` — degree-`m` coefficient at multi-index `σ`.
- `CechAcyclic.lean:939` `noncomputable def dDiff (m : ℕ) : (∀ σ : Fin m → ι, dCoeff s M σ) →ₗ[R] (∀ σ : Fin (m+1) → ι, dCoeff s M σ)` — the alternating-sum-of-cofaces differential (`LinearMap.pi` of alternating sums of the away-localisation comparison maps `dCoface`).
- `CechAcyclic.lean:945` `dDiff_apply` unfolds it as `∑ j, (-1)^j • dCoface s M m σ j (t (σ ∘ j.succAbove))`.

**The three exactness theorems (module-level, no scheme):**

```
-- CechAcyclic.lean:1124
lemma SectionCechModule.dDiff_exact [Finite ι] (hs : Ideal.span (Set.range s) = ⊤) (m : ℕ) :
    Function.Exact (dDiff s M (m + 1)) (dDiff s M (m + 2))
```
This is *the* algebraic core: for a spanning family `s : ι → R`, the complex `∏_σ M_{s_σ}` (over `σ : Fin(m+1)→ι`) is exact in positive degrees, proved by `exact_of_isLocalized_span` + the localised combinatorial core `CombinatorialCech.depDiff_exact` (localise at each spanning `s r`, reduce to `CechLocalized.cechLocalized_exact`, `CechAcyclic.lean:755`).

```
-- CechAcyclic.lean:1165
lemma SectionCechModule.dDiff_exact_of_localizationAway [Finite ι] (f : R)
    (hmem : ∀ i, ∃ k, f ∣ s i ^ k)
    (hspan : Ideal.span (Set.range (fun i => algebraMap R (Localization.Away f) (s i))) = ⊤)
    (m : ℕ) :
    Function.Exact (dDiff s M (m + 1)) (dDiff s M (m + 2))
```
Route B (change of ring to `Localization.Away f`): `s` need only span the unit ideal after localising at `f` (each `sᵢ ∈ √f`); instantiates `dDiff_exact` over `R_f` and ladder-transports along `AwayComparison.isLocalizedModule_comp_away` (`CechAcyclic.lean:781`).

```
-- CechAcyclic.lean:1290  ← THE ONE TO REUSE for a general affine open
lemma SectionCechModule.dDiff_exact_of_affineCover [Finite ι]
    (S : Type u) [CommRing S] [Algebra R S]
    (hspan : Ideal.span (Set.range (fun i => algebraMap R S (s i))) = ⊤)
    (hloc : ∀ {n : ℕ} (σ : Fin (n + 1) → ι),
      IsLocalization (Submonoid.powers (sprod s σ))
        (Localization (Submonoid.powers (algebraMap R S (sprod s σ)))))
    (m : ℕ) :
    Function.Exact (dDiff s M (m + 1)) (dDiff s M (m + 2))
```
**This is exactly the level of generality the curve-side seed needs.** It is a statement about an abstract ring `R`, an `R`-module `M`, a family `s : ι → R`, and *any* `R`-algebra `S` (in practice `S := Γ(V, 𝒪)` for an affine open `V`) such that (a) the images `s i ↦ S` span the unit ideal of `S`, and (b) for every Čech multi-index `σ`, the `S`-localisation of `M ⊗_R S` at `sprod s σ`'s image is *simultaneously* an `R`-localisation of `M` at `powers (sprod s σ)` (`hloc`, encoding `D(s_σ) ⊆ V`). Route B1: instantiates `dDiff_exact` over `MS := TensorProduct R S M` with base change `bc := TensorProduct.mk R S M 1`, using `isLocalizedModule_baseChange_away` (`CechAcyclic.lean:883`, itself pure base-change algebra: `IsBaseChange.comp` + `isLocalizedModule_iff_isBaseChange`).

**Geometric wrappers** (`R := Γ(Spec R)`-level, still Spec-specific but consuming the above verbatim):
```
-- CechAcyclic.lean:1940
theorem sectionCech_homology_exact {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {ι : Type u} [Finite ι] (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    (p : ℕ) (hp : 1 ≤ p) :
    IsZero ((sectionCechComplex (fun i => PrimeSpectrum.basicOpen (s i))
      ((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M))).homology p)

-- CechAcyclic.lean:1973
theorem sectionCech_homology_exact_of_localizationAway ... (f : R)
    (hcov : (PrimeSpectrum.basicOpen f : (Spec R).Opens) = ⨆ i, PrimeSpectrum.basicOpen (s i))
    (p : ℕ) (hp : 1 ≤ p) : IsZero (... .homology p)

-- CechAcyclic.lean:2014
theorem sectionCech_homology_exact_of_affineCover ...
    (S : Type u) [CommRing S] [Algebra R S] (hspan) (hloc) (p : ℕ) (hp : 1 ≤ p) :
    IsZero (... .homology p)

-- CechAcyclic.lean:2073  ← the FULL Spec-side analogue of what you need on X
theorem sectionCech_homology_exact_of_affineOpen {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {ι : Type u} [Finite ι] (s : ι → R)
    (hV : IsAffineOpen (X := Spec R) (⨆ i, PrimeSpectrum.basicOpen (s i)))
    (p : ℕ) (hp : 1 ≤ p) :
    IsZero ((sectionCechComplex (fun i => PrimeSpectrum.basicOpen (s i))
      ((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M))).homology p)
```
`sectionCech_homology_exact_of_affineOpen` (`CechAcyclic.lean:2073–2124`) is *exactly* the pattern to replicate on a general `X`: it sets `S := Γ(V, 𝒪_{Spec R})` where `V = ⨆ᵢ D(sᵢ)`, discharges `hspan` from `hV.iSup_basicOpen_eq_self_iff` and `hloc` per-σ from `hV.isLocalization_of_eq_basicOpen` transported along an `AlgEquiv`.

**Bottom line for reuse on `X`:** you do *not* need to re-derive any Čech combinatorics. `SectionCechModule.dDiff_exact_of_affineCover` is 100% ring/module-theoretic and scheme-independent; the only new work is a geometric wrapper analogous to `sectionCech_homology_exact_of_affineOpen` that (i) identifies `Γ(X, X.basicOpen f)` (`f ∈ Γ(X,U)`, `U` affine ⊆ `X`) as an `R`-localisation of `M := Γ(U, 𝒪_X)` via `IsAffineOpen.isLocalization_of_eq_basicOpen`/`isLocalization_basicOpen`, and (ii) bridges to the *shape* of Čech complex you actually need (see §2/§3 — this is where care is needed because there are two non-defeq Čech complex flavours in the project).

---

## 2. The two Čech complex shapes — NOT literally the same terms

### (a) `sectionCechComplex`/`cechCohomology` — Ab-valued, `X.PresheafOfModules`

- `AlgebraicJacobian/Cohomology/PresheafCech.lean:303` `sectionCechCosimplicial {ι} (U : ι → Opens X) (F : X.PresheafOfModules) : CosimplicialObject Ab.{u}` with
  `obj n := ∏ᶜ (fun σ : Fin (n.len+1) → ι => F.presheaf.obj (op (⨅ k, U (σ k))))` — a *literal* order-theoretic infimum `⨅ k, U (σ k)` inside `F.presheaf.obj`.
- `PresheafCech.lean:337` `sectionCechComplex U F := (alternatingCofaceMapComplex Ab).obj (sectionCechCosimplicial U F) : CochainComplex Ab.{u} ℕ`.
- `CechToCohomology.lean:99` `cechCohomology U F p := (sectionCechComplex U F).homology p : Ab.{u}`.

### (b) `Scheme.cechCochain`/`Scheme.cechCohomology` — `ModuleCat k`-valued, via Mathlib's `cechComplexFunctor`

- `StructureSheafModuleK/Carriers.lean:562` `Scheme.cechCochain (C) (F : Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k)) (𝒰 : ι → Opens C.left.toTopCat) := (cechComplexFunctor 𝒰).obj ((sheafToPresheaf _ _).obj F) : CochainComplex (ModuleCat.{u} k) ℕ`.
- `:573` `Scheme.cechCohomology C F 𝒰 n := (Scheme.cechCochain C F 𝒰).homology n : ModuleCat.{u} k`.
- `:528`/`:541` the original (iter-012) structure-sheaf-specific `Scheme.cechCochain_OC`/`Scheme.cechCohomology_OC` with `F := Scheme.toModuleKSheaf C`; `:586–599` `Scheme.cechCochain_OC_eq`/`Scheme.cechCohomology_OC_eq` are `rfl`-provable definitional-unfolding bridges (they are just the `F := toModuleKSheaf C` specialisation, not a comparison to flavour (a)).
- `:612` `class Scheme.IsCechAcyclicCover F 𝒰` — `Subsingleton (Scheme.cechCohomology C F 𝒰 n)` for `n > 0` — the **target predicate** your seed presumably needs to instantiate.

### Mathlib's `cechComplexFunctor` (`Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`, read in full)

```
-- FormalCoproducts/Basic.lean, FormalCoproducts/Cech.lean, Sites/SheafCohomology/Cech.lean
cechComplexFunctor U : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ
  := FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk _ U).cech
  := cosimplicialObjectFunctor E ⋙ alternatingCofaceMapComplex A     -- E = (mk _ U).cech
```
Unwinding `evalOp`/`power`/`cech` (all in `FormalCoproducts/Basic.lean`, `FormalCoproducts/Cech.lean`): the degree-`n` term is
```
∏ᶜ (σ : Fin (n+1) → ι), P.obj (op (∏ᶜ k, U (σ k)))
```
where **both** `∏ᶜ` are *categorical* products (via `HasFiniteProducts C`), **not** literal `⨅`/`Pi.lift` over an order-theoretic meet the way `sectionCechCosimplicial` is. For `C = TopologicalSpace.Opens X` (a `CompleteLattice`), the categorical finite product coincides with `⨅` only up to the *propositional* (not `rfl`) equality `CategoryTheory.Limits.CompleteLattice.limit_eq_iInf` (`Mathlib/CategoryTheory/Limits/Lattice.lean:199`) — a `le_antisymm` proof, since `Opens X` is a thin/partial-order category (iso ⇒ equal by antisymmetry, but not definitionally).

**Confirmed empirically**: `AlgebraicJacobian/RiemannRoch/Adelic/Cokernel.lean:346` proves exactly this comparison by hand:
```
theorem prodOpens_eq_iInf {m : ℕ} (j : Fin m → ι) :
    (∏ᶜ ((FormalCoproduct.mk _ 𝒰).obj ∘ j) : TopologicalSpace.Opens C.left.toTopCat) = ⨅ i, 𝒰 (j i) :=
  le_antisymm (le_iInf fun a => (Limits.Pi.π ((FormalCoproduct.mk _ 𝒰).obj ∘ j) a).le) ...
```
— a real `le_antisymm` lemma, i.e. genuinely not `rfl`. This is the only place in the project comparing the two Čech-term shapes, and it is done bespoke inside `Cokernel.lean` for a specific `ULift (Fin 2)` two-element cover (`AffineCoverMVSquare`), not as a reusable general lemma.

**Index-universe (`ULift`) note:** `cechComplexFunctor` requires `U : ι → C` with `ι : Type w` and `HasFiniteProducts C`; the project instantiates it with `ι : Type u` directly in `Scheme.cechCochain`. Elsewhere (`AffineSerreVanishing.lean`, e.g. `:238,:377,:493`) the flavour-(a) Spec-side lemmas systematically use `ι := ULift.{u} (Fin n)` to land finite index families in `Type u` (universe-pinning discipline for `Ideal.span`/`Finite ι` arguments living in `Type u`); `Cokernel.lean`'s `AffineCoverMVSquare.coverFamily` uses `ULift.{u} (Fin 2)` for the same reason feeding `cechComplexFunctor`.

**Conclusion for §2**: **No comparison lemma between the two flavours exists in the project** beyond the ad-hoc `prodOpens_eq_iInf`/`prodOpens_fin_one`/`prodOpens_fin_two` family in `Cokernel.lean` (grep confirms `cechComplexFunctor` appears only in `Cokernel.lean` and `Carriers.lean`; `sectionCechCosimplicial`/`sectionCechComplex` appear only in `CechBridge.lean`/`PresheafCech.lean`/`CechAcyclic.lean`/`CechToCohomology.lean`/`CechSectionIdentification*.lean` — **zero file imports/references both families**). Building the seed for `Scheme.toModuleKSheaf`/`Scheme.cechCohomology` (flavour b) will require either (i) reproving the algebraic-heart exactness directly against flavour-(b)'s term shape (degreewise `∏ᶜ` in `ModuleCat k`, via `Concrete.productEquiv`/`Pi.map`, mirroring `sectionCechProductEquiv` at `CechAcyclic.lean:1505`, but for the categorical `∏ᶜ` rather than `⨅`), or (ii) building a general term-by-term iso `Scheme.cechCochain C F 𝒰 ≅ (Ab-or-ModuleK-valued sectionCechComplex-analogue)` using `prodOpens_eq_iInf`-style lemmas degreewise, then transporting exactness/vanishing across that iso (§3).

---

## 3. Vanishing transport tools

Two already-built patterns, both in-project, plus one core Mathlib fact:

1. **Ab-flavour, same-category iso transport** — `AffineSerreVanishing.lean:424`:
```
theorem cechCohomology_isZero_of_iso {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    {F G : X.PresheafOfModules} (e : F ≅ G) (p : ℕ)
    (h : IsZero (cechCohomology U F p)) : IsZero (cechCohomology U G p) :=
  h.of_iso ((HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℕ) p).mapIso
    ((sectionCechComplexFunctor U).mapIso e)).symm
```
This is the template: coefficient-presheaf iso ⇒ `sectionCechComplexFunctor`/`sectionCechCosimplicialFunctor` (`CechToCohomology.lean:85`/`:50`) mapIso ⇒ `HomologicalComplex.homologyFunctor _ _ p` mapIso ⇒ `IsZero.of_iso`. The analogous route for `ModuleCat k`-valued complexes/`Scheme.cechCohomology` would need a `ModuleCat`-valued `cechComplexFunctor`-mapIso from a sheaf-of-`k`-modules iso (Mathlib's `cechComplexFunctor` is already functorial in the coefficient presheaf `P : Cᵒᵖ ⥤ A`, so `(cechComplexFunctor 𝒰).mapIso` is directly available — no project-local reconstruction needed here, unlike flavour (a)).

2. **`IsZero ↔ Subsingleton` bridge for `ModuleCat`** — Mathlib, `Mathlib/Algebra/Category/ModuleCat/Basic.lean:253,377,384`:
```
theorem ModuleCat.isZero_of_subsingleton (M : ModuleCat R) [Subsingleton M] : IsZero M
theorem ModuleCat.subsingleton_of_isZero (h : IsZero M) : Subsingleton M
ModuleCat.isZero_iff_subsingleton : IsZero M ↔ Subsingleton M
```
This is exactly the bridge needed since `Scheme.IsCechAcyclicCover` (`Carriers.lean:612`) is phrased with `Subsingleton (Scheme.cechCohomology C F 𝒰 n)` rather than `IsZero`. Project precedent: `FreePresheafComplex.lean:607` already uses `ModuleCat.isZero_of_subsingleton` in exactly this direction.

3. **Generic `IsZero.of_iso`** (`CategoryTheory.Limits.IsZero.of_iso`, standard Mathlib) transports `IsZero` across any iso in any category — this is what both patterns above bottom out in; no forget₂-specific machinery was needed (the homology objects being compared always live in the *same* target category `Ab`/`ModuleCat k`, so no forget₂-reflects-zero argument shows up anywhere in the project). If you *do* need to cross categories (e.g. compare an `Ab`-valued homology object with a `ModuleCat k`-valued one via `forget₂`), the project's only precedent for `forget₂ (ModuleCat _) AddCommGrpCat` faithfulness/iso-reflection is `CechSectionIdentificationBase.lean:772` (`isLimitOfReflectsOfMapIsLimit (forget₂ (ModuleCat _) AddCommGrpCat) ...`) and `FreePresheafComplex.lean:408-410` (`Functor.map_isIso (forget₂ (ModuleCat _) Ab) _`) — i.e. `forget₂` reflects isos/limits (it's an equivalence onto its (additive, exact) essential image for a fixed ring), no bespoke "reflects zero objects" lemma exists but is derivable trivially from `forget₂`'s exactness (`isZero_of_subsingleton`/`subsingleton_of_isZero` transported along the forget₂'s underlying-type identification).

---

## 4. Basis/cofinality material and Mathlib generalisation lemmas for a general `X`

### `standard_cover_cofinal` (`AffineSerreVanishing.lean:167`)
```
theorem standard_cover_cofinal {R : CommRingCat.{u}} (f : R) {α : Type u}
    (W : α → (Spec R).Opens)
    (hcov : (PrimeSpectrum.basicOpen f : (Spec R).Opens) ≤ ⨆ a, W a) :
    ∃ (n : ℕ) (g : Fin n → R) (φ : Fin n → α),
      (PrimeSpectrum.basicOpen f : (Spec R).Opens) = ⨆ i, PrimeSpectrum.basicOpen (g i) ∧
      ∀ i, (PrimeSpectrum.basicOpen (g i) : (Spec R).Opens) ≤ W (φ i)
```
Spec-specific inputs used: `PrimeSpectrum.isCompact_basicOpen f`, `PrimeSpectrum.isTopologicalBasis_basic_opens`.

### `standard_cover_cofinal_affine` (`AffineSerreVanishing.lean:558`) — the D(f)→general-affine-open generalisation *already done* (Spec-side)
```
theorem standard_cover_cofinal_affine {R : CommRingCat.{u}} (V : (Spec R).Opens)
    (hV : IsAffineOpen V) {α : Type u} (W : α → (Spec R).Opens) (hcov : V ≤ ⨆ a, W a) :
    ∃ (n : ℕ) (g : Fin n → R) (φ : Fin n → α),
      V = ⨆ i, PrimeSpectrum.basicOpen (g i) ∧
      ∀ i, (PrimeSpectrum.basicOpen (g i) : (Spec R).Opens) ≤ W (φ i)
```
Only change from `standard_cover_cofinal`: `hK := hV.isCompact` (`IsAffineOpen.isCompact`) in place of `PrimeSpectrum.isCompact_basicOpen f`; same `isTopologicalBasis_basic_opens` + finite-subcover argument (identical proof shape, `V ⊓ W a` in place of `Uf ⊓ W a`). **This is the exact template to port to a general scheme `X`, affine open `U`**: the analogue needs `PrimeSpectrum.isTopologicalBasis_basic_opens` replaced by the basis-of-basic-opens-of-`U` statement `IsAffineOpen.isBasis_basicOpen` (used at `AffineScheme.lean:622`, `(isBasis_basicOpen U)`), and `PrimeSpectrum.basicOpen` replaced by `X.basicOpen (· : Γ(X,U))`.

### Mathlib v4.31 lemmas available for the port to a general `X`/affine `U` (all read in full from `Mathlib/AlgebraicGeometry/AffineScheme.lean` and `Mathlib/AlgebraicGeometry/Scheme.lean`)

- **`Scheme.basicOpen`** (`Scheme.lean:655`, section `BasicOpen`, `variable (X : Scheme) {V U : X.Opens} (f g : Γ(X, U))`): `X.basicOpen (f : Γ(X,U)) : X.Opens`, keyed on sections over an **arbitrary** `U` (not just `⊤`) — exactly matches what's needed.
  - `Scheme.lean:687` `X.basicOpen_le : X.basicOpen f ≤ U` (tagged `@[sheaf_restrict]`).
  - `Scheme.lean:677` `X.basicOpen_res (i : op U ⟶ op V) : X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f`.
  - `Scheme.lean:718` `X.basicOpen_mul : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g` — the "same-open sections" product formula (used exactly as `PrimeSpectrum.basicOpen_mul` is used in `CechAcyclic.lean:1434`/`basicOpen_sprod` on the Spec side; ports verbatim to `sprod` for `X.basicOpen`).
  - `Scheme.lean:736` `X.basicOpen_one : X.basicOpen (1 : Γ(X,U)) = U`.
  - `Scheme.lean:739` `instance algebra_section_section_basicOpen (f : Γ(X,U)) : Algebra Γ(X,U) Γ(X, X.basicOpen f) := (X.presheaf.map (homOfLE (basicOpen_le f)).op).hom.toAlgebra` — **already a synthesizable instance** for the restriction algebra (note: `sectionCech_homology_exact_of_affineOpen`'s docstring, `CechAcyclic.lean:2035`, claims "NOT a synthesizable instance" for the analogous `Algebra Γ(V) Γ(D a)` on `Spec R` — but the general-`X` `Scheme.basicOpen` API already provides it as an instance keyed on `X.basicOpen_le`; worth double-checking whether it fires automatically before reconstructing the ad-hoc `.toAlgebra` pattern).

- **`IsAffineOpen.basicOpen`** (`AffineScheme.lean:597`, `include hU`): `IsAffineOpen (X.basicOpen f)` for `hU : IsAffineOpen U`, `f : Γ(X,U)`.

- **`IsAffineOpen.isLocalization_basicOpen`** (`AffineScheme.lean:659`, `include hU`): `IsLocalization.Away f Γ(X, X.basicOpen f)` — the direct algebraic content: sections over `X.basicOpen f` are `Γ(X,U)_f`.

- **`IsAffineOpen.isLocalization_of_eq_basicOpen`** (`AffineScheme.lean:726`): `{V : X.Opens} (i : V ⟶ U) (e : V = X.basicOpen f) : @IsLocalization.Away _ _ f Γ(X,V) _ (X.presheaf.map i.op).hom.toAlgebra` — the exact lemma the Spec-side `sectionCech_homology_exact_of_affineOpen` (`CechAcyclic.lean:2073`) invokes for `hloc`.

- **`IsAffineOpen.iSup_basicOpen_eq_self_iff`** (`AffineScheme.lean:909`, `include hU`): `{s : Set Γ(X,U)} : ⨆ f : s, X.basicOpen (f : Γ(X,U)) = U ↔ Ideal.span s = ⊤` — **THE** "covering ⇔ spans unit ideal" criterion (name confirmed exactly). Companion: `IsAffineOpen.self_le_iSup_basicOpen_iff` (`:936`) is the `≤` form.

- **`IsAffineOpen.isCompact`** (`AffineScheme.lean:501`, `protected theorem`, `include hU`): `IsCompact (U : Set X)` — the quasi-compactness input `standard_cover_cofinal_affine` uses.

- **`IsAffineOpen.isBasis_basicOpen`** (used at `AffineScheme.lean:622`) — the "basic opens of `U` form a basis of `U`" fact, the general-`X` analogue of `PrimeSpectrum.isTopologicalBasis_basic_opens`, needed for the `exists_subset_of_mem_open` step of the cofinality proof.

- Instance `IsAffine.of_isIso`, `IsAffine X.basicOpen r` for `[IsAffine X]` (`AffineScheme.lean:608`, only for `⊤`-sections) vs. the general `IsAffineOpen.basicOpen` (works for any affine `U`, any `f : Γ(X,U)`) — use the latter for the curve case since `U` is a proper affine open, not all of `X`.

**Summary porting recipe for §4**: replace every `PrimeSpectrum.basicOpen`/`Spec R` occurrence in `standard_cover_cofinal_affine` with `X.basicOpen (· : Γ(X,U))`/`X`, `IsAffineOpen.isCompact` for quasi-compactness (already what `standard_cover_cofinal_affine` uses — no change needed there), and `IsAffineOpen.isBasis_basicOpen` in place of `PrimeSpectrum.isTopologicalBasis_basic_opens`. This is a mechanical, already-modeled port.

---

## 5. `Scheme.toModuleKSheaf` — definition and restriction-map relation to `O_C`

Split across three files (`StructureSheafModuleK/{Presheaf,SheafProperty,Carriers}.lean`).

**`Presheaf.lean:171` — the presheaf, `toModuleKPresheaf`:**
```
noncomputable def Scheme.toModuleKPresheaf (C : Over (Spec (CommRingCat.of k))) :
    (Opens C.left.toTopCat)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj U := ModuleCat.of k (C.left.presheaf.obj U)
  map {U V} f := ModuleCat.ofHom
    { toFun := fun x => (C.left.presheaf.map f).hom x
      map_add' := ...
      map_smul' := ... }   -- uses toModuleKSheaf.algebraMap_naturality
```
So **as a type/underlying group, `toModuleKPresheaf.obj U` is literally `Γ(C.left, U) = O_C(U)`**; the restriction map is `O_C`'s own presheaf restriction map `(C.left.presheaf.map f).hom`, merely re-packaged as a `k`-linear map (`ModuleCat.ofHom` wraps the *same* function, `map_smul'` proved via naturality of the algebra map, `map_add'` trivial). There is no separate "sheaf of `k`-modules" data beyond `O_C` — the `k`-module structure comes from the algebra map below.

**`Presheaf.lean:126,134` — the `k`-algebra structure on each `Γ(C,U)`:**
```
noncomputable def kToSection (C) (U) : CommRingCat.of k ⟶ C.left.presheaf.obj U :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.app ⊤ ≫ C.left.presheaf.map (homOfLE le_top).op
noncomputable instance algebraSection (C) (U) : Algebra k (C.left.presheaf.obj U) :=
  RingHom.toAlgebra (kToSection C U).hom
```
i.e. `algebraMap k Γ(C,U)` is the structure-morphism's global ring map `C.hom.app ⊤ : k → Γ(C,⊤)` restricted to `U`; `kToSection_naturality` (`:147`) and `algebraMap_naturality` (`:155`) show this is compatible with `O_C`'s own restriction maps, i.e. `toModuleKPresheaf`'s restriction maps *are* `O_C`'s restriction maps and they are `k`-algebra (hence `k`-linear) maps.

**`SheafProperty.lean:42` — the sheaf itself, `toModuleKSheaf`:**
```
noncomputable def toModuleKSheaf (C : Over (Spec (CommRingCat.of k))) :
    Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} k) :=
  ⟨toModuleKPresheaf C, toModuleKPresheaf_isSheaf C⟩
```
with `toModuleKSheaf_forgetCompare` (`:52`, `Iso.refl _`!) confirming `forget₂ (ModuleCat k) AddCommGrpCat` applied to `toModuleKSheaf C` is **literally equal** (not just isomorphic) to the pre-existing `AddCommGrpCat`-valued structure sheaf `toAbSheaf C.left`.

**No existing lemma computes `toModuleKSheaf` sections on basic opens or relates to localization** (grep for `toModuleKPresheaf.*basicOpen`/`toModuleKSheaf.*[Ll]ocaliz` across the whole project returns nothing). This is a genuine gap: to run the algebraic heart (§1) against `toModuleKSheaf`, you will need to establish, for `f ∈ Γ(U, O_C)` (`U` affine open of `C.left`), that `(toModuleKSheaf C).presheaf.obj (op (C.left.basicOpen f))` is (as a `k`-module) the localisation `(Γ(U,O_C))_f`, via `IsAffineOpen.isLocalization_basicOpen` composed with the definitional identity `toModuleKPresheaf.obj U = ModuleCat.of k (C.left.presheaf.obj U)` (`Presheaf.lean:197`, `@[simp] toModuleKPresheaf_obj`, `rfl`) — i.e. the `k`-module carrier of the sheaf is definitionally `O_C`'s carrier, so `IsLocalization.Away` transports for free at the type level; only the `k`-linearity of the localisation-comparison maps (`AwayComparison.comparison`) needs re-establishing in the `ModuleCat k` bundling.
