# Analogy: cheapest Mathlib-aligned route for the general-affine-open Čech vanishing seed `htilde`

## Mode
api-alignment

## Slug
genaffine-seed

## Iteration
057

## Question
For `M : ModuleCat R`, a finite family `g : Fin n → R` with `V := ⨆ᵢ D(gᵢ)` an AFFINE open of
`Spec R` (general — NOT assumed `= D(f)`), and `p > 0`, prove
`IsZero (cechCohomology (fun i => D(gᵢ)) ((toPresheafOfModules).obj (tilde M)) p)` — i.e. the residual
`htilde` of `affine_cech_vanishing_qcoh_general_of_tildeVanishing` (Need #2). Find the cheapest
Mathlib-aligned route; flag any parallel-API risk.

## Project artifact(s)
- `AffineSerreVanishing.lean:799–815` — `affine_cech_vanishing_qcoh_general_of_tildeVanishing`, whose
  `htilde` hypothesis is exactly this seed (`M = moduleSpecΓFunctor.obj F`).
- `CechAcyclic.lean:1868–1893` — `sectionCech_homology_exact_of_localizationAway`, the DONE `D(f)` case.
- `CechAcyclic.lean:1217–1321` — `SectionCechModule.dDiff_exact_of_localizationAway` (the module-core
  change-of-ring; the template to mirror).
- `CechAcyclic.lean:1177–1199` — `SectionCechModule.dDiff_exact` (full-span core, reused over `S`).
- `CechAcyclic.lean:1382–1387` — `qcohSectionsAwayLocalized` (R-side `Γ(D(gσ),~M) = M_{gσ}`).
- `CechAcyclic.lean:875–943` — `isLocalizedModule_comp_away` (the `D(f)` per-σ composite the general
  case must REPLACE by a base-change composite).

## Headline finding (read this first)

The seed reduces, through the **already-shipped** `SectionCechTilde` bridge (`sectionCechAbExact` ladder),
to positive-degree exactness of the *abstract module complex* `SectionCechModule.dDiff g M` over `R`.
This bridge is **independent of whether `V` is `D(f)` or a general affine open** — it is the same code
path that `sectionCech_homology_exact` / `_of_localizationAway` already use. So the ONLY new content is:

> **prove `Function.Exact (dDiff g M (m+1)) (dDiff g M (m+2))` for `V = ⨆ D(gᵢ)` affine.**

The cheapest sound way to get that exactness is **route B1 (change-of-ring to `S := Γ(V,𝒪)` via algebraic
base change `M_S := M ⊗_R S`)**, mirroring `dDiff_exact_of_localizationAway` *verbatim* with one swap:
the per-σ "this is a localization of `M` at `powers gσ`" instance changes from the away-composite
`isLocalizedModule_comp_away` to a **base-change composite** built from
`Mathlib.RingTheory.Localization.BaseChange` + `Mathlib.RingTheory.IsTensorProduct`. Everything else
(the `eσL`/`heσL`/`nat`/`E`/`sq` ladder, the reuse of `dDiff_exact` over `S`, the `sectionCechAbExact`
wrapper) is copy-paste from the `D(f)` case.

**Route C (no change of ring) is REJECTED.** `exact_of_localized_maximal` is circular: at a maximal ideal
`J ∉ V` the localized complex is the SAME positive-degree Čech-of-a-general-affine-cover problem over the
local ring `R_J` (the family `g/1` lands in the maximal ideal, no unit, complex non-zero), so there is no
base case. At `J ∈ V` it is contractible (fine), but the `J ∉ V` branch has no Mathlib-free discharge.
The `D(f)` case needed change-of-ring for the same reason; `V` general only changes the target ring from
`Localization.Away f` to `S = Γ(V)` (which is NOT a localization of `R`).

## Verified Lean names (with paths)

### A. The coordinate-ring identification `Γ(D(gσ)) = R_{gσ} = S_{ḡσ}`
- `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen (hU) (f) : IsLocalization.Away f Γ(X.basicOpen f)`
  — `Mathlib.AlgebraicGeometry.AffineScheme`. **[verified]** With `U := ⊤`, `f := gσ ∈ R = Γ(⊤)`:
  `Γ(D(gσ))` is `IsLocalization.Away gσ` over `R`.
- `AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen (hU) (f) (i : V' ⟶ U) (V' = X.basicOpen f)
  : IsLocalization.Away f Γ(V')` — same file. **[verified]** With `U := V`, `f := ḡσ ∈ Γ(V)`,
  `V' := D(gσ)`: `Γ(D(gσ))` is `IsLocalization.Away ḡσ` over `S = Γ(V)`.
- `AlgebraicGeometry.Scheme.basicOpen_res (X) (f) (i) : X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f`
  — `Mathlib.AlgebraicGeometry.Scheme`. **[verified]** Gives `(Spec R).basicOpen ḡσ = V ⊓ D(gσ) = D(gσ)`
  (`ḡσ` = restriction of `gσ` to `V`, and `D(gσ) ⊆ V`), the `heq` for `isLocalization_of_eq_basicOpen`.
- ⇒ `Γ(D(gσ))` is **simultaneously** `Away gσ` over `R` and `Away ḡσ` over `S`. Hence
  `IsLocalization (powers gσ) (Localization.Away ḡσ)` over `R` (transport the `R`-Away structure along the
  unique `S`-iso `Γ(D(gσ)) ≅ Localization.Away ḡσ`). **This is the geometric input** to the per-σ instance.

### B. Base-change toolkit (the module-side localization, route B1's only new ingredient)
- `IsLocalization.tensorProduct_isLocalizedModule (S_monoid) (A) [IsLocalization S_monoid A]
  : IsLocalizedModule S_monoid ((TensorProduct.mk R A M) 1)` — `Mathlib.RingTheory.Localization.BaseChange`.
  **[verified]**
- `isLocalizedModule_iff_isBaseChange (S_monoid) (A) [IsLocalization S_monoid A] (f)
  : IsLocalizedModule S_monoid f ↔ IsBaseChange A f` — same file. **[verified]**
- `IsLocalizedModule.isBaseChange (S_monoid) (A) [IsLocalization S_monoid A] (f) [IsLocalizedModule S_monoid f]
  : IsBaseChange A f` — same file. **[verified]**
- `TensorProduct.isBaseChange (R M S) : IsBaseChange S ((TensorProduct.mk R S M) 1)`
  — `Mathlib.RingTheory.IsTensorProduct`. **[verified]**
- `IsBaseChange.comp (hf : IsBaseChange S f) (hg : IsBaseChange T g) : IsBaseChange T (↑R g ∘ₗ f)`
  — `Mathlib.RingTheory.IsTensorProduct`. **[verified]** (transitivity of base change.)
- `IsLocalization.Away.tensorEquiv (S) (r) (A) [IsLocalization.Away r A]
  : TensorProduct R S A ≃ₐ[S] Localization.Away (algebraMap R S r)` — `…Localization.BaseChange`. **[verified]**
  (Alternative concrete iso if the `IsBaseChange` route hits a diamond.)

The per-σ instance (the analogue of `inst_comp` / `eσL` in `dDiff_exact_of_localizationAway`):
1. `(M ⊗_R S)` localized at `powers ḡσ` over `S` is `IsBaseChange (Localization.Away ḡσ)` of `M⊗_R S`
   [`IsLocalizedModule.isBaseChange`].
2. `M⊗_R S` is `IsBaseChange S` of `M` [`TensorProduct.isBaseChange`].
3. compose [`IsBaseChange.comp`] ⇒ the composite `M → (M⊗_R S)_{ḡσ}` is `IsBaseChange (Localization.Away ḡσ)`
   of `M`.
4. `IsLocalization (powers gσ) (Localization.Away ḡσ)` over `R` [section A, geometric transport].
5. `(isLocalizedModule_iff_isBaseChange (powers gσ) (Localization.Away ḡσ) _).mpr` ⇒ the composite is
   `IsLocalizedModule (powers gσ)` over `R`. Then `IsLocalizedModule.iso` gives, for free, the canonical
   `R`-linear iso `(M⊗_R S)_{ḡσ} ≅ M_{gσ} = dCoeff g M σ` (= `eσL σ`).

### C. No change-of-ring-free / no ready-made affine-vanishing
- `exact_of_localized_maximal (f) (g) (∀ J max, Exact (LocalizedModule.map J.primeCompl f) …)
  : Function.Exact f g` — `Mathlib.RingTheory.LocalProperties.Exactness`. **[verified]** — exists, but the
  per-`J` hypothesis at `J ∉ V` reduces to the same theorem over `R_J` (circular; see Headline).
- `exact_of_isLocalized_span (s) (span s = ⊤) …` — same file. **[verified]** — needs the localization
  elements to BE the family members (for contractibility) AND to span `⊤`; over `R` the `gᵢ` span `⊤` only
  if `V = Spec R`. This is exactly why change-of-base to `S` (where `ḡᵢ` span `⊤`) is forced.
- **No Mathlib "Hⁱ(affine, qcoh) = 0" / "Čech over a cover of an affine is exact"** at the section level
  exists; the project is building it. The quasi-coherent-on-affine module-section localization
  (`Γ(U,F) → Γ(D(f),F)` is `IsLocalizedModule (powers f)` for qcoh `F`, `U` affine) is **absent from
  Mathlib** for general qcoh sheaves (only the ring/structure-sheaf version `isLocalization_basicOpen`
  ships). This is what makes route B2 (sheaf-section `M_S := Γ(V,~M)`) expensive — it needs that missing
  lemma or the 01I8-style `~_R M|_V ≅ (V≅Spec S)^* ~_S M_S` sheaf iso (memory: `sheaf-iso-on-basis-plumbing`).

## Decisions identified

### Decision 1: change-of-ring to `S = Γ(V)` (B) vs no-change-of-ring (C)
- **Mathlib idiom**: exactness of a finitely-localised module complex is reduced by
  `exact_of_isLocalized_span` (localise at a *spanning* family) or `exact_of_localized_maximal` (localise at
  every maximal). The contractible-cover engine (`CechLocalized.cechLocalized_exact`, reused inside
  `dDiff_exact`) needs a UNIT in the family.
- **Gap**: C is divergent-and-circular — `exact_of_localized_maximal` at `J ∉ V` regenerates the same
  general-affine Čech problem over `R_J`. `exact_of_isLocalized_span` over `R` can't be applied (`gᵢ` don't
  span `⊤`). Both force change-of-base to a ring where `ḡᵢ` span `⊤`, i.e. `S = Γ(V)`.
- **Verdict**: **ALIGN_WITH_MATHLIB on route B** (change-of-ring to `S`); **reject route C**.

### Decision 2: realise `M_S` as `M ⊗_R S` (B1, algebraic) vs `Γ(V,~M)` (B2, sheaf sections)
- **Mathlib idiom**: base change of a module along a localization, and localization-commutes-with-base-change,
  are fully packaged in `Mathlib.RingTheory.Localization.BaseChange` + `IsTensorProduct`
  (`tensorProduct_isLocalizedModule`, `isLocalizedModule_iff_isBaseChange`, `IsBaseChange.comp`,
  `TensorProduct.isBaseChange`). The qcoh-module-section-on-affine localization (`Γ(V,~M) → Γ(D(gσ),~M)` is
  `IsLocalizedModule`) is NOT in Mathlib.
- **Gap**: B2 is divergent-with-cost — it needs the missing qcoh-affine module lemma or the expensive 01I8
  sheaf-iso plumbing (`sheaf-iso-on-basis-plumbing.md`, multi-iter). B1 is fully Mathlib-supported algebra.
- **Cost of B2**: ~150–300 LOC of sheaf-iso / qcoh-affine infrastructure (high risk; the project pivoted
  away from comparable sheaf-diamond work before). B1: ~30–50 LOC for the per-σ base-change instance.
- **Verdict**: **ALIGN_WITH_MATHLIB on B1** (algebraic base change); **DIVERGE from B2**.

### Decision 3: packaging — co-locate in `CechAcyclic.lean` (reuse private core) vs fresh file
- **Observation**: identical to the `D(f)` adjudication (`02kg-residual-changeofbase.md`, Decision 2). The
  new module-core `dDiff_exact_of_affineCover` and the wrapper `sectionCech_homology_exact_of_affineCover`
  belong INSIDE `CechAcyclic.lean` where `SectionCechModule.*` / `SectionCechTilde.*` are in scope. No
  `private → public` flip, no API change.
- **Verdict**: **PROCEED** — co-locate; `AffineSerreVanishing.lean` consumes the new public wrapper.

## Recommendation

Take **route B1**, co-located in `CechAcyclic.lean`, as a near-verbatim mirror of the shipped `D(f)` chain.
Concrete bridge-lemma decomposition (≈ 8–12 lemmas, ~230–320 LOC; riskiest item ⚠ flagged):

1. **`isAffineOpen → S, ḡ, hspan_S`** — set `S := Γ(V) = (Spec R).presheaf.obj (op V)`,
   `φ : R → S` the restriction, `ḡ i := φ (g i)`. Prove `Ideal.span (Set.range ḡ) = ⊤` in `S` from
   `⨆ D(gᵢ) = V` via `IsAffineOpen.isoSpec` (`V ≅ Spec S`) + the `D_S(ḡᵢ)`↔`D_R(gᵢ)` correspondence +
   `PrimeSpectrum.iSup_basicOpen_eq_top_iff` over `S` (mirror of `affine_cover_span_localizationAway`,
   `AffineServeVanishing.lean:402`). ~25–40 LOC. ⚠ the `isoSpec` basic-open correspondence is the fiddly bit.

2. **`isLocalization_Sḡσ_away_gσ`** — `IsLocalization (powers gσ) (Localization.Away ḡσ)` over `R`, from
   `isLocalization_basicOpen` (R-side, `U=⊤`) + `isLocalization_of_eq_basicOpen` (S-side) +
   `Scheme.basicOpen_res` + transport along the unique `S`-iso. ~15–25 LOC.

3. **`isLocalizedModule_baseChange_away` (NEW, the one genuinely new Mathlib-gap-fill)** — the per-σ
   composite `M → M⊗_R S → (M⊗_R S)_{ḡσ}` is `IsLocalizedModule (powers gσ)` over `R`, via the 5-step
   `IsBaseChange.comp` argument in section B above. ~30–50 LOC. ⚠ watch `IsScalarTower R S (Localization.Away ḡσ)`
   diamonds (cf. memory `rR-semiring-diamond-change-workaround.md`); the `IsBaseChange` route avoids most
   `∘ₗ`/`LinearMap.pi` rewriting, but if a diamond bites, fall back to the explicit
   `IsLocalization.Away.tensorEquiv` iso.

4. **`dDiff_exact_of_affineCover`** — mirror `dDiff_exact_of_localizationAway` (`CechAcyclic.lean:1217`)
   line-for-line with `Rf ⇝ S`, `Mf ⇝ M⊗_R S`, `g' ⇝ ḡ`, and `inst_comp` built from lemma 3 instead of
   `isLocalizedModule_comp_away`. The `eσL`/`heσL`/`nat`/`E`/`sq` ladder + final
   `Function.Exact.of_ladder_addEquiv_of_exact (E m) (E (m+1)) (E (m+2)) (sq m) (sq (m+1)) Hf` is unchanged;
   `Hf := dDiff_exact ḡ (M⊗_R S) hspan_S m`. ~90–120 LOC (mostly copy-paste).

5. **`sectionCechAbExact_affine`** — third copy of the `sectionCechAbExact` ladder
   (`CechAcyclic.lean:1775`/`1802`) feeding `dDiff_exact_of_affineCover`. ~25 LOC.

6. **`sectionCech_homology_exact_of_affineCover`** — public wrapper, mirror
   `sectionCech_homology_exact_of_localizationAway` (`CechAcyclic.lean:1868`): `IsZero (homology p)` from
   `sectionCech_isZero_homology_of_objD_exact _ _ q (sectionCechAbExact_affine …)`. Signature: takes
   `g : ι → R` + `IsAffineOpen (⨆ D(gᵢ))`. ~15–25 LOC.

7. **`affine_tildeVanishing_general` (in `AffineServeVanishing.lean`)** — private, mirror
   `affine_tildeVanishing` (`:491`); instantiates lemma 6 at `M := moduleSpecΓFunctor.obj F`,
   `ι := ULift (Fin n)`, discharging the `htilde` of `affine_cech_vanishing_qcoh_general_of_tildeVanishing`.
   Then `affine_cech_vanishing_qcoh_general` and `affine_serre_vanishing_general` follow unconditionally.
   ~10 LOC.

The single irreducible novelty over the `D(f)` case is lemma 3 (base-change localization), and it is fully
backed by `Mathlib.RingTheory.Localization.BaseChange`. No new sheaf infrastructure, no parallel API.
