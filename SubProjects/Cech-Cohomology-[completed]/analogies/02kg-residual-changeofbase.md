# Analogy: cheapest Mathlib-aligned route for the 02KG residual leaf (Čech vanishing over a *proper* `D(f)`)

## Mode
api-alignment

## Slug
iter050-residual

## Iteration
050

## Question
For an `R`-module `M`, `f : R`, a finite family `g : ι → R` with `D(f) = ⨆ᵢ D(gᵢ)`, and `p > 0`:
prove `Ȟᵖ({D(gᵢ)}, ~_R M) = 0`. The family `{gᵢ}` spans only `√(f)`, NOT `R` (proper `D(f)`),
so the shipped public `sectionCech_affine_vanishing` (which needs `span = ⊤` over `R`) does not apply
directly. Over `R_f = Localization.Away f` the images `{gᵢ/1}` DO span `⊤`
(`affine_cover_span_localizationAway`). Two formalization routes were proposed:
**(A) change-of-SPACE** (restrict `~_R M` along the scheme iso `Spec R_f ≅ D(f)`),
**(B) change-of-RING** (identify the two module Čech complexes algebraically). Adjudicate the cheaper.

## Project artifact(s)
- `CechAcyclic.lean:1587–1605` — public `sectionCech_homology_exact` / `sectionCech_affine_vanishing`
  (the spanning-`⊤` endpoint; `cechCohomology U F p := (sectionCechComplex U F).homology p`).
- `CechAcyclic.lean:874–1106` — `namespace SectionCechModule`: the **un-localised module complex**
  `D• = dDiff s M`, `dCoeff s M σ = LocalizedModule (powers (sprod s σ)) M = M_{sσ}`, and
  `dDiff_exact s M hs` (exactness, the ONLY place `hs : span = ⊤` is consumed) — proved via
  `exact_of_isLocalized_span (Set.range s) hs`. These are `private`-in-namespace.
- `CechAcyclic.lean:1330–1581` — `namespace SectionCechTilde`: the section-complex↔module-complex
  bridge `sectionToModuleAddEquiv` + `sectionCechCofaceMatch` + `sectionCechAbExact`
  (ladder via `Function.Exact.of_ladder_addEquiv_of_exact`). Also `private`-in-namespace.
- `CechAcyclic.lean:482–660` — PUBLIC `AwayComparison`: `Inverts`, `comparison`,
  `comparison_isLocalizedModule`, `comparison_comp`, `comparison_self`, `Inverts.of_dvd`. A generic
  change-of-localization-base functoriality for `IsLocalizedModule`, NOT tied to spanning.
- `AffineSerreVanishing.lean:402–453` — `affine_cover_span_localizationAway` (the `R_f` spanning fact)
  + `affine_cech_vanishing_qcoh_of_tildeVanishing` (the residual `htilde` is exactly a non-spanning-`g`
  instance of `sectionCech_homology_exact`).
- `QcohRestrictBasicOpen.lean:88–122,298–301` — `specAwayToSpec`, `modulesRestrictBasicOpen`,
  `modulesRestrictBasicOpenIso`, `specAwayToSpec_eq`, `presentationModulesRestrictBasicOpen`
  (route-A geometric packaging — but only a *presentation*, not a tilde-iso).

## Key Mathlib facts located
- `AlgebraicGeometry.basicOpenIsoSpecAway (f : R) : ↑(basicOpen f) ≅ Spec (CommRingCat.of (Localization.Away f))`
  — `Mathlib.AlgebraicGeometry.Restrict`. The `Spec R_f ≅ D(f)` iso EXISTS and is already wrapped by the project.
  Its companion `basicOpenIsoSpecAway_inv_homOfLE` ties the restriction `D(fg) ⊆ D(f)` to
  `IsLocalization.Away.awayToAwayRight` — i.e. the away-to-away section-comparison maps.
- `exact_of_isLocalized_span (s) (spn : Ideal.span s = ⊤) … : Function.Exact F G` from exactness after
  inverting each `r ∈ s` — `Mathlib.RingTheory.LocalProperties.Exactness`. **Requires `span = ⊤` in the
  BASE ring.** `{gᵢ}` does not span `R`; `{gᵢ, f}` has radical `√(f) ≠ ⊤`; so it can ONLY be run over `R_f`.
  This is the exact tool `dDiff_exact` already uses.
- **Mathlib has NO module/section Čech complex** (the project built `sectionCechComplex`), hence **no
  base-change functoriality** for it, and **no tilde-base-change lemma** `~_R M |_{D(f)} ≅ ~_{R_f} M_f`.
  The only relevant change-of-base primitives are `IsLocalizedModule` / `LocalizedModule.map` and the
  project's own public `AwayComparison.comparison` (a localization-transitivity functoriality).

## Decisions identified

### Decision 1: change-of-SPACE (A) vs change-of-RING (B)

- **Mathlib idiom**: "a property of a finitely-localised module complex that survives because it can be
  checked after inverting a *spanning set*" is `exact_of_isLocalized_span`
  (`Mathlib.RingTheory.LocalProperties.Exactness`); "the same module under two localisation bases" is
  `IsLocalizedModule` + localization transitivity (project's `comparison_isLocalizedModule`). Both are
  **ring-level**, not space-level. Mathlib pushes scheme cohomology computations down to these.
- **Both routes share an unavoidable algebraic core**: a degreewise iso `M_{gσ} ≅ (M_f)_{gσ}`
  (an `IsLocalizedModule`/`comparison` transitivity iso — `f` is invertible in `M_{gσ}` because
  `gσ ∈ √(f)`) that commutes with the alternating localisation differentials. Route A merely wraps this
  core in scheme-restriction + double section-group identification; route B applies it directly.
- **Route A's extra, genuinely-missing piece**: a *tilde base-change sheaf iso*
  `(pullback specAwayToSpec)(~_R M) ≅ ~_{R_f} M_f`. Mathlib lacks it; the project only has the
  **presentation-level** `presentationModulesRestrictBasicOpen`, not a clean module-sheaf iso. Building
  it is the painful 01I8-flavoured sheaf plumbing already flagged in memory
  (`sheaf-iso-on-basis-plumbing.md`, `rR-semiring-diamond-change-workaround.md`). Route A then ALSO needs
  a cross-*space* cochain iso (section groups over `⨅ₖ D_{R_f}(gσk/1)` vs `⨅ₖ D_R(gσk)` across the
  homeomorphism) — two copies of the `qcohSectionsAwayLocalized` work plus naturality.
- **Gap**: divergent-with-cost. Route A pays for a Mathlib-gap sheaf iso + double section-identification;
  route B pays only for the shared core + a same-shape ladder.
- **Verdict**: **ALIGN_WITH_MATHLIB on route B** (change-of-ring); **DIVERGE from route A**.

### Decision 2: must the `private` `SectionCechModule`/`SectionCechTilde` core be exposed (refactor)?

- **Observation**: the residual can be proved as a **new PUBLIC theorem added to `CechAcyclic.lean`
  itself**, inside `namespace AlgebraicGeometry` (and reusing the `SectionCechModule`/`SectionCechTilde`
  namespaces), where every `private` decl is in scope. `AffineSerreVanishing.lean` then consumes the new
  public theorem. **No `private → public` flip, no API surface change, no refactor.** The directive's
  privacy worry assumed the proof lived in `AffineSerreVanishing.lean`; co-locating it in `CechAcyclic.lean`
  dissolves the concern.
- **Concrete realization (lowest cost, mirrors existing code)**: add
  `sectionCech_homology_exact_of_localizationAway (M) (g : ι → R) (f : R)`
  `(hspan : Ideal.span (Set.range (fun i => algebraMap R (Localization.Away f) (g i))) = ⊤) (p) (hp)`,
  proved by a ladder `Function.Exact.of_ladder_addEquiv_of_exact` (exactly the shape of `sectionCechAbExact`
  at `CechAcyclic.lean:1577`) whose vertical AddEquivs are the degreewise `M_{gσ} ≅ (M_f)_{gσ}` from the
  public `AwayComparison` toolkit, and whose horizontal exact rows are `dDiff_exact (g/1) M_f hspan`
  **re-run over `R_f`** (the abstract `SectionCechModule` is `{R}[CommRing R]`-polymorphic, so instantiate
  `R := Localization.Away f`, `M := LocalizedModule (powers f) M`). The naturality square mirrors
  `cechCoface_dToCech` (`CechAcyclic.lean:941`).
- **Verdict**: **PROCEED** — no refactor required; co-locate the new public theorem in `CechAcyclic.lean`.

### Decision 3: is there a Mathlib change-of-base for the algebraic Čech/Koszul module complex?

- **Mathlib idiom**: none — Mathlib has no Čech/Koszul-of-a-module complex with base-change. The substitute
  is the project's public `AwayComparison` (change-of-localization-base for `IsLocalizedModule`) +
  `comparison_isLocalizedModule` (transitivity `M_a → M_{ab}`) + `exact_of_isLocalized_span`.
- **Gap**: upstream — Mathlib does not provide it.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (upstream, not a project failure). The project already owns the
  full substitute API; nothing new needs inventing.

## Recommendation

Take **route B (change-of-ring)**, realised as a new public theorem in `CechAcyclic.lean`:
`sectionCech_homology_exact_of_localizationAway`. Re-instantiate the existing, polymorphic
`SectionCechModule.dDiff_exact` over `R_f = Localization.Away f` with the `R_f`-spanning family `g/1`
(hypothesis from `affine_cover_span_localizationAway`), and transport positive-degree exactness back to
the `R`-side section Čech complex through a degreewise `M_{gσ} ≅ (M_f)_{gσ}` AddEquiv **ladder** built
from the public `AwayComparison.comparison` API — copying the structure of `sectionCechAbExact`
(`Function.Exact.of_ladder_addEquiv_of_exact`) verbatim, with a naturality square modelled on
`cechCoface_dToCech`. Then wrap with `IsZero`-of-`Function.Exact` exactly as `sectionCech_homology_exact`
does. Estimated ~120–200 LOC, ~5–8 bridge lemmas, **zero refactor**, **zero new sheaf infrastructure**,
high reuse of already-axiom-clean public machinery.

**Do NOT take route A.** It requires a tilde-base-change sheaf iso `~_R M|_{D(f)} ≅ ~_{R_f} M_f` that
Mathlib lacks and the project has only at presentation level, plus a cross-*space* section-group
identification — ~350–450 LOC including the 01I8-style sheaf-diamond plumbing the memory notes record as
expensive (`sheaf-iso-on-basis-plumbing.md`, `rR-semiring-diamond-change-workaround.md`). The
`Spec R_f ≅ D(f)` iso itself (`AlgebraicGeometry.basicOpenIsoSpecAway`) is cheap and present, but it is
not the bottleneck — the missing tilde-iso is.

The one fact route B leans on that needs its own one-line lemma: `gσ ∈ √(f)` (so `f` is invertible in
`M_{gσ}`, giving the `Inverts` witness for the `M_{gσ} ≅ (M_f)_{gσ}` iso). Derive it from `hcov`
(`D(gσ) = ⨅ₖ D(gσk) ⊆ D(f)`) via `PrimeSpectrum.basicOpen` ≤ and `… ≤ basicOpen f ↔ … ∈ √(f)`, the same
ingredient already used inside `affine_cover_span_localizationAway`.
