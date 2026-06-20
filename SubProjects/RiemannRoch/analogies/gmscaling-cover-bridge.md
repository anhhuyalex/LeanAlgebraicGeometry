# Analogy: cover-vs-`Proj.awayι` syntactic mismatch in `gmScalingP1_cover_X_iso`

## Mode
api-alignment

## Slug
gmscaling-cover-bridge

## Iteration
178

## Question
What Mathlib idiom retires the two TEMPORARY axioms
`gmScalingP1_chart_data_temp` and `gmScalingP1_collapse_at_zero_temp` in
`AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean` (iter-177 HARD STOP
corrective)? Specifically: how to rewrite `cover.openCover.f i` back to
`Proj.awayι _ (X_i) _ _` form so the chart-bridge proof body chasing
`pullbackSpecIso_hom_base` succeeds.

## Project artifact(s)
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:54-63` — `awayι_comp_PLB_hom` (axiom-clean since iter-173; generic in `f`).
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:105-108` — `gmScalingP1_cover` via `pullback₁`.
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:120-160` — `gmScalingP1_cover_X_iso` (the blocker; `match i with | ⟨0, _⟩ => … | ⟨1, _⟩ => …`).
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:175-194` — `gmScalingP1_chart` (axiom-clean def; uses the iso).
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:212-219` — `gmScalingP1_chart_data_temp` (TEMPORARY AXIOM, to be retired).
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:308-311` — `gmScalingP1_collapse_at_zero_temp` (TEMPORARY AXIOM, to be retired).
- `AlgebraicJacobian/Genus0BaseObjects/BareScheme.lean:175-221` — `projectiveLineBarAffineCover` via `Proj.affineOpenCoverOfIrrelevantLESpan` (the cover whose `.f i` we need to identify with `Proj.awayι _ (X i) _ _`).

## Decisions identified

### Decision 1: Is `Scheme.AffineOpenCover.openCover_f` + `Matrix.cons_val` the right idiom?

- **Mathlib idiom**: PARTIAL — `Scheme.AffineOpenCover.openCover_f`
  (`Mathlib.AlgebraicGeometry.Cover.Open`) gives `𝒰.openCover.f j = 𝒰.f j`
  by `rfl`. For `𝒰 = Proj.affineOpenCoverOfIrrelevantLESpan 𝒜 f f_deg hm hf`,
  the field `.f i` is **definitionally** `Proj.awayι 𝒜 (f i) (f_deg i) (hm i)`
  (verified: generic `i`-form is `rfl` after a `let cov := …` introduces the
  cover and `f_deg`/`hm` are bound names, not inline `by` tactics).
- **Subtle structural blocker**: when the index is written `⟨0, _⟩`
  (NOT canonical `(0 : Fin 2)`), Lean's elaborator does NOT reduce
  `(![X 0, X 1]) ⟨0, _⟩` to `X 0`. Concretely verified: `f_deg ⟨0, by omega⟩ = hf₀`
  fails with a Type mismatch error, while `f_deg (0 : Fin 2) = hf₀` is `rfl`.
  The reason: `⟨0, h⟩` carries a *metavariable* proof at elaboration time;
  the elaborator never instantiates the `Fin.cons`/`Matrix.cons` computation
  rule unless the index normalizes to a canonical `Fin.OfNat` form.
- **Compounding factor**: when `f_deg`/`hm` are built inline via
  `(fun i => by fin_cases i <;> simp [...])`, the kernel must `whnf` the
  tactic-built proof terms in addition to the index reduction, which times
  out at 200k heartbeats (verified) and even at 800k (verified).
- **Project's current path**: `gmScalingP1_cover_X_iso` matches on `i`
  via `match i with | ⟨0, _⟩ => … | ⟨1, _⟩ => …`. In each branch, the body
  references `MvPolynomial.X 0` / `MvPolynomial.X 1` directly — but the
  target type uses `MvPolynomial.X i`. The match equation `i = ⟨0, _⟩`
  doesn't trigger the `Matrix.cons_val_zero` reduction needed to unify
  `(cover.openCover.f i = Proj.awayι 𝒜 ((![X 0, X 1]) ⟨0, _⟩) …)` with
  `(Proj.awayι 𝒜 (X 0) …)` inside `pullback.congrHom`.
- **Gap**: divergent-with-cost. Mathlib has the idiom (`openCover_f` is
  the right path), but the project's `match-on-i` decoration of
  `gmScalingP1_cover_X_iso` causes the iso to be **specialised** in each
  branch in a way that breaks the `Matrix.cons` defeq chain.
- **Cost of the current divergence**: 6 iters of helper-bridge attempts
  (iter-172 → iter-177) failed to penetrate. iter-177 HARD STOP corrective
  admitted two project axioms.
- **Verdict**: **ALIGN_WITH_MATHLIB** — refactor `gmScalingP1_cover_X_iso`
  to be **uniform in `i`** (no `match`), so the bridge chain works
  generically and the `Matrix.cons_val` reduction happens INSIDE the cover's
  rfl-defeq, not at the `pullback.congrHom` boundary.

### Decision 2: Does Mathlib ship a `Proj.openCover` / `Proj.coverByCharts` that bypasses the issue?

- **Mathlib idiom**: PARTIAL.
  - `Proj.affineOpenCover` (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`):
    uses ALL homogeneous-degree-positive elements (not Fin-indexed); too coarse
    for the project's 2-chart setting.
  - `Proj.affineOpenCoverOfIrrelevantLESpan` (already used by the project):
    Fin-indexed, `.f i = Proj.awayι 𝒜 (f i) (f_deg i) (hm i)` by `rfl`.
  - `Proj.openCoverOfMapIrrelevantEqTop` / `Proj.openCoverOfMapIrreleventEqTop`:
    different shape (covers `X` from a `RingHom A → Γ(X, ⊤)`), not applicable.
- **Project's current path**: uses `Proj.affineOpenCoverOfIrrelevantLESpan`,
  which IS the right Mathlib idiom — the structural issue is downstream
  (the `match` in `gmScalingP1_cover_X_iso`), not the cover choice itself.
- **Gap**: identical (project uses the canonical Mathlib idiom).
- **Verdict**: **PROCEED** — no upstream refactor needed; the cover itself is
  Mathlib-aligned.

### Decision 3: Pivot estimate — uniform-in-`i` refactor of `gmScalingP1_cover_X_iso`

- **Refactor signature**:
  ```lean
  private noncomputable def gmScalingP1_cover_X_iso (kbar : Type u) [Field kbar] (i : Fin 2) :
      (gmScalingP1_cover kbar).X i ≅
        Spec (CommRingCat.of
          (TensorProduct kbar
            (HomogeneousLocalization.Away (projectiveLineBarGrading kbar)
              ((![MvPolynomial.X 0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) kbar) i))
            (GmRing kbar))) :=
    pullbackSymmetry _ _ ≪≫
      pullbackRightPullbackFstIso _ _ _ ≪≫
      pullback.congrHom
        (awayι_comp_PLB_hom kbar
          ((![MvPolynomial.X 0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) kbar) i)
          (-- hoist this f_deg proof to a top-level `noncomputable def` in BareScheme.lean
           projectiveLineBarAffineCover_fDeg kbar i))
        (show (Gm kbar).hom =
            Spec.map (CommRingCat.ofHom (algebraMap kbar (GmRing kbar))) from rfl) ≪≫
      pullbackSpecIso kbar _ (GmRing kbar)
  ```
  Key structural change: the iso target uses `((![X 0, X 1]) i)` instead of
  `(MvPolynomial.X i)`, eliminating the defeq pivot. Downstream, `chart_PLB_eq`
  does a fresh `fin_cases i` AFTER unfolding, with `Matrix.cons_val_zero`/`one`
  closing the chart-ring iso target — but now the bridge chain is uniform in
  `i`, so `pullbackSpecIso_hom_base` applies cleanly.
- **Required companion definition** (in `BareScheme.lean`, ~5-8 LOC):
  hoist the `f_deg : ∀ i, (![X 0, X 1]) i ∈ 𝒜 1` proof from the inline `by`
  tactic in `projectiveLineBarAffineCover` (currently `(fun i => by fin_cases i <;> simp [...])`)
  to a named `noncomputable def projectiveLineBarAffineCover_fDeg`. The
  `hm : ∀ i, 0 < (![1, 1]) i` similarly hoisted to
  `projectiveLineBarAffineCover_hm`. This makes the proof terms reduce
  cleanly without the kernel chasing tactic-built proof closures.
- **LOC delta estimate**:
  - Hoisted `f_deg`/`hm` defs in `BareScheme.lean`: ~12 LOC.
  - `gmScalingP1_cover_X_iso` body refactor (eliminate `match`): -20, +12 ⟹ net ~-8 LOC.
  - `gmScalingP1_chart` body: minor signature update for the iso target; ~+5 LOC.
  - `gmScalingP1_chart_PLB_eq` body retirement (was axiom, now proven): ~+35-50 LOC
    using the 10-step recipe from `analogies/chart-bridge-shared-helper.md` Decision 3.
  - `gmScalingP1_chart_agreement` body retirement: ~+30-50 LOC
    (Sub-task B from `chart-bridge-shared-helper.md`).
  - `gmScalingP1_collapse_at_zero` body retirement: ~+15-25 LOC
    (chart-1 ring-map computation; the chart-1 ring map sends `u ↦ u ⊗ λ`,
    and `zeroPt` factors through chart-1 at `u = 0`, so the composite
    evaluates to `zeroPt` independently of `λ`).
- **Total**: ~85-130 LOC across 5 lanes (within iter-177's ~80-150 estimate).
- **Verdict**: **PROCEED** with the uniform-in-`i` refactor.

### Decision 4: Alternative — valuative-criterion route to `ℙ¹ → A const` (bypass chart-bridge)

- **Mathlib idiom**: PARTIAL.
  - `AlgebraicGeometry.IsProper.of_valuativeCriterion`
    (`Mathlib.AlgebraicGeometry.ValuativeCriterion`): proves properness FROM
    the valuative criterion. We need the converse direction (use properness
    to extend a morphism), accessed via `ValuativeCriterion.existence`
    (extracts the existence half from `[IsProper]`).
  - `AlgebraicGeometry.Scheme.RationalMap` / `Scheme.PartialMap`
    (`Mathlib.AlgebraicGeometry.RationalMap`): framework for partial
    morphisms with `domain : X.Opens` and `dense_domain`. Has the SHAPE
    needed.
  - `AlgebraicGeometry.Proj.valuativeCriterion_existence_aux`
    (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`): proves the
    existence half OF the criterion FOR `Proj` (used in the project's
    `projectiveLineBar_isProper` derivation chain); not the converse.
- **What's MISSING in Mathlib**: there is no single shipped lemma of the
  form "if `f : U ⟶ Y` is a morphism from a dense open of a regular
  Noetherian scheme `X` to a proper scheme `Y`, and `X \ U` has codimension
  ≥ 1, then `f` extends uniquely to a morphism `X ⟶ Y`". This is
  exactly the content of Route A's `A.4.a Lemma 3.3 codim-1` lane
  (`AlgebraicJacobian/Albanese/CodimOneExtension.lean`, currently skeleton-only,
  Mathlib gap CRITICAL PATH per `STRATEGY.md`).
- **Project's current path**: chart-bridge route (option (c) Route C from
  iter-170). The valuative-criterion alternative was tracked as a
  pre-committed replacement candidate (STRATEGY.md Open Q) gated on
  iter-182 status review.
- **Gap**: divergent-and-wrong (the valuative-criterion alternative). The
  alternative requires building essentially the SAME infrastructure as
  Route A.4.a (which is the dominant positive-genus risk; substrate UNOWNED).
  For a genus-0 sub-case (extending `𝔸¹ → A` to `ℙ¹ → A`), the codim-1
  extension is a single DVR lift, not the full surface-divisor machinery
  Route A needs — but the project would still need:
    (i) Build `Scheme.PartialMap`-to-`Scheme.Hom` extension across a closed
        codim-1 reduced subscheme (here `{∞} ⊂ ℙ¹`),
    (ii) Apply `ValuativeCriterion.existence` (extracted from `[IsProper A]`)
         to the localised DVR `O_{ℙ¹, ∞}`, then
    (iii) Glue back to a morphism `ℙ¹ ⟶ A` (essentially
          `Scheme.Cover.glueMorphisms` of the affine chart + a Spec-of-DVR
          patch at `∞`).
  Step (i) is genuinely new project material; step (iii) is the SAME
  `Cover.glueMorphisms` blocker that's biting the chart-bridge route.
- **Cost of the valuative alternative**: ~80-130 LOC for steps (i)-(iii)
  PLUS the same `glueMorphisms` infrastructure cost (which the chart-bridge
  refactor already pays for). NET: no savings, plus a fresh
  `RationalMap`-extension lemma that's not Mathlib-shipped.
- **Verdict**: **DIVERGE_INTENTIONALLY** — stay on the chart-bridge route
  (Decisions 1-3 are the path). The valuative alternative was a sensible
  backup but does not eliminate the structural blocker; it just shifts it.

## Verdicts (summary)

| Decision | Verdict | Severity |
|---|---|---|
| (1) `openCover_f` + `Matrix.cons_val` recipe, but `match`-on-i defeats it | ALIGN_WITH_MATHLIB | critical |
| (2) `Proj.affineOpenCoverOfIrrelevantLESpan` is the right cover; project already uses it | PROCEED | informational |
| (3) Uniform-in-`i` refactor of `gmScalingP1_cover_X_iso` (~85-130 LOC) | PROCEED | informational |
| (4) Valuative-criterion alternative: no savings, shifts same blocker | DIVERGE_INTENTIONALLY | informational |

## Recommendation

**Land the uniform-in-`i` refactor of `gmScalingP1_cover_X_iso`**
(Decisions 1 + 3). The two TEMPORARY axioms retire via a 3-step refactor:

### Step 1 — Hoist tactic-built proof terms in `BareScheme.lean` (~12 LOC)

Add two top-level named defs that replace the inline `by` tactics in
`projectiveLineBarAffineCover`:

```lean
private noncomputable def projectiveLineBarAffineCover_fDeg
    (kbar : Type u) [Field kbar] :
    ∀ i, (![(MvPolynomial.X 0 : MvPolynomial (Fin 2) kbar), MvPolynomial.X 1]) i ∈
      projectiveLineBarGrading kbar ((![1, 1] : Fin 2 → ℕ) i) :=
  fun i => by
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
      MvPolynomial.isHomogeneous_X]

private lemma projectiveLineBarAffineCover_hm :
    ∀ i, 0 < (![1, 1] : Fin 2 → ℕ) i :=
  fun i => by fin_cases i <;> exact Nat.one_pos
```

Then refactor `projectiveLineBarAffineCover` to consume these by name
(instead of inline `by` tactics).

### Step 2 — Refactor `gmScalingP1_cover_X_iso` uniform in `i` (~ -8 LOC net)

Replace the `match i with | ⟨0, _⟩ => … | ⟨1, _⟩ => …` body with a
single uniform expression whose target type uses
`((![X 0, X 1]) i)` instead of `(MvPolynomial.X i)`. Pass the
hoisted `projectiveLineBarAffineCover_fDeg kbar i` as the
homogeneity witness to `awayι_comp_PLB_hom`. The post-`congrHom`
pullback is now uniformly
`pullback (Spec.map (algebraMap kbar (Away 𝒜 (![X 0, X 1] i)))) (Gm.hom)`,
so `pullbackSpecIso kbar _ _` applies generically.

### Step 3 — Retire the two temp axioms (~80-125 LOC across 3 bodies)

1. **`gmScalingP1_chart_PLB_eq`** (currently axiom-laundered):
   follow the 10-step recipe in `analogies/chart-bridge-shared-helper.md`
   Decision 3 (steps 1-10 listed there with verbatim Mathlib citations).
   With the uniform iso from Step 2, `pullbackSpecIso_hom_base` fires
   syntactically and the bridge chain closes generically.

2. **`gmScalingP1_chart_agreement`** (currently axiom-laundered, second
   conjunct): follow `chart-bridge-shared-helper.md` Sub-task B —
   diagonal cases via `CategoryTheory.Limits.fst_eq_snd_of_mono_eq`
   (since `(cover).f i` is `IsOpenImmersion`, hence mono); cross cases
   `(0,1)/(1,0)` via the algebraic identity `λ·u = (1/t)·λ` in
   `Localization.Away t ⊗[kbar] GmRing` (per `analogies/gmscaling-deep.md` Q4).

3. **`gmScalingP1_collapse_at_zero`** (currently axiom-laundered): once
   `gmScalingP1` is concrete, the chart-1 ring map sends `u ↦ u ⊗ λ` and
   `zeroPt` factors through chart-1 at `u = 0`, so the composite evaluates
   to `zeroPt` independently of `λ`. The proof chain: unfold
   `gmScalingP1`, apply `Cover.hom_ext` on the `cover` of
   `(ℙ¹ ⊗ Gm).left`, reduce on chart-1 to a ring-level identity in
   `MvPolynomial Unit kbar ⊗[kbar] GmRing` (sending the constant `0`
   under `MvPolynomial.eval₂Hom`'s `X ()`-binding).

### Reversal trigger

If Step 2 cannot eliminate the `pullbackSpecIso_hom_base` syntactic
mismatch even with the uniform-in-`i` refactor (e.g., the
`MvPolynomial Unit kbar ⊗[kbar] GmRing` chart-ring-iso's kbar-algebra
preservation surfaces a fresh unification issue), iter-179 falls back
to the **partial `Fin.cases` refactor**: keep the `match` in
`gmScalingP1_cover_X_iso` but use `Fin.cases` (which produces the
canonical `(0 : Fin 2)` index, not `⟨0, _⟩`) — see the experimental
finding below for verification that `(0 : Fin 2)` triggers the right
`Matrix.cons_val` reduction.

## Experimental verification (iter-178)

The diagnosis above was empirically verified via four `lean_run_code`
probes:

1. **Generic `i`-form is rfl-defeq**: when `f_deg`/`hm` are named
   hypotheses (not inline `by` tactics) and the index is left generic,
   `cov.openCover.f i = Proj.awayι 𝒜 ((![f₀, f₁]) i) (f_deg i) (hm i)`
   closes by `rfl`. ✓
2. **Canonical `0 : Fin 2` form is rfl-defeq**: when `f_deg` is a named
   hypothesis and the index is `(0 : Fin 2)`,
   `cov.openCover.f (0 : Fin 2) = Proj.awayι 𝒜 f₀ hf₀ Nat.one_pos`
   closes by `rfl` (proof irrelevance handles the proof-term mismatch
   between `hf₀` and `f_deg 0`). ✓
3. **`⟨0, _⟩` form fails**: when the same goal uses `⟨0, by omega⟩` as
   the index, `rfl` times out at 800k heartbeats. The elaborator does
   NOT unfold `(![f₀, f₁]) ⟨0, _⟩` to `f₀`. ✗
4. **Inline `by`-tactic in cover construction compounds the failure**:
   when `f_deg`/`hm` are built inline via `(fun i => by fin_cases i <;> ...)`,
   even Step 2's `simp [openCover_f, Fin.mk_zero', Matrix.cons_val_zero]`
   followed by `rfl` times out. ✗

The combination of (3) + (4) is precisely why the iter-176 analogist's
`simp [Fin.isValue, Fin.zero_eta]` recipe failed: the simp set normalized
the Fin indexing but didn't reach into the `f_deg`/`hm` tactic closures.

## What did NOT need to change

- `Proj.affineOpenCoverOfIrrelevantLESpan` choice (PROCEED — already canonical).
- `homogeneousLocalizationAwayIso` + `_algebraMap` companion (axiom-clean
  iter-174; ready to consume in Step 3 of the retirement).
- `awayι_comp_PLB_hom` (axiom-clean iter-173; generic in `f`, ready to
  consume in Step 2).
- `gmScalingP1_chart{0,1}_ringMap` (axiom-clean iter-167; consumed by the
  refactored `gmScalingP1_chart`).
- The valuative-criterion alternative (Decision 4 DIVERGE: shifts blocker,
  no savings).
