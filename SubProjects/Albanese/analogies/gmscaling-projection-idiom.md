# Analogy: collapsing inverse-projection chains through `asIso (pullback.map …)` mid-chain

## Mode
api-alignment

## Slug
gmscaling-projection-idiom

## Iteration
184

## Question

Joint consult for Lane B's 5-iter CHURNING route. After applying
`cancel_epi (gmScalingP1_cover_intersection_X_iso kbar).inv` (iter-183),
the cocycle goal `pullback.fst ((cover).f 0) ((cover).f 1) ≫ chart 0 =
pullback.snd … ≫ chart 1` lifts to a morphism equality over
`Spec ((Away (X 0 · X 1)) ⊗ GmRing)`. The substantive residual is to
collapse `iso.inv ≫ pullback.fst/snd` through the iso's 7-step
`Iso.trans`-chain and reduce to a `Spec.map` of a single ring map. 5
iter-183 attempts failed because the chain's STEP 4 uses
`asIso (pullback.map _ _ _ _ (𝟙) (Proj.pullbackAwayιIso _).hom (𝟙) _ _)`
and the `(asIso …).inv ≫ pullback.fst/snd` collapse step is not
served by any Mathlib simp lemma.

The Q1/Q2/Q3 from the iter-183 task_result asks:
- **Q1**: canonical idiom for collapsing
  `inv (pullback.map _ _ _ _ (𝟙) i₂ (𝟙) _ _) ≫ pullback.fst`?
- **Q2**: does Mathlib ship a simp lemma that fires through outer
  `pullback.map` / `pullback.congrHom` wraps?
- **Q3**: canonical "shared intersection chart" definition for cocycle
  via `Algebra.TensorProduct.map (awayMapₐ _) (AlgHom.id _)`?

## Project artifact(s)

- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:283-321` —
  `gmScalingP1_cover_intersection_X_iso` (the 7-step iso chain;
  STEP 4 = `asIso (pullback.map … (𝟙) (Proj.pullbackAwayιIso _).hom (𝟙) _ _)`).
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:382-397` —
  `gmScalingP1_chart_agreement_cross01` (the cocycle helper; iter-183
  body = `cancel_epi iso.inv` + `sorry`).
- `analogies/intersection-ring-cross01.md` — iter-182 prior recipe;
  the **Recipe 2** body at L294-328 is the failing route.

## Decisions identified

### Decision 1: `pullback.map ≫ pullback.fst/snd` HAS NO Mathlib simp lemma — project must build one

- **Mathlib state**:
  - `pullback.map` is an `abbrev` for `pullback.lift (fst ≫ i₁) (snd ≫ i₂) _`
    (`HasPullback.lean:267-271`).
  - `pullback.lift_fst` / `pullback.lift_snd` are `@[reassoc]` ONLY —
    NOT `@[simp]` (`HasPullback.lean:173-181`).
  - Consequence: `simp` does NOT collapse
    `pullback.map _ _ _ _ i₁ i₂ i₃ _ _ ≫ pullback.fst _ _` to
    `pullback.fst _ _ ≫ i₁`, even though the equation holds by
    `pullback.lift_fst` after unfolding `pullback.map`.
- **What Mathlib DOES ship at simp severity**:
  - `pullback.congrHom_inv` (`@[simp]`, `HasPullback.lean:354-359`) —
    unfolds `(pullback.congrHom h₁ h₂).inv` to
    `pullback.map _ _ _ _ (𝟙) (𝟙) (𝟙) _ _`.
  - `pullbackRightPullbackFstIso_inv_fst`,
    `pullbackRightPullbackFstIso_inv_snd_fst`,
    `pullbackRightPullbackFstIso_inv_snd_snd`
    (`@[reassoc (attr := simp)]`, `Pasting.lean:470-487`).
  - `pullbackLeftPullbackSndIso_inv_fst`, `_inv_snd_snd`,
    `_inv_fst_snd` (`Pasting.lean:536-552`).
  - `pullbackSymmetry_inv_comp_fst`, `_inv_comp_snd`
    (`HasPullback.lean:508-514`).
  - `Proj.pullbackAwayιIso_inv_fst`, `_inv_snd`
    (`@[reassoc (attr := simp)]`,
    `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:291-301`).
- **Project's current path**: iter-183 attempt 1 used a `simp only`
  set that included the `pullbackRightPullbackFstIso_inv_*`
  simp lemmas. The set did NOT include `Iso.inv_comp_eq` + `asIso_hom`
  + the missing `pullback.lift_fst/snd` triple needed to collapse
  the `asIso (pullback.map …)` step.
- **Gap**: divergent-with-cost. Mathlib has every iso-step's
  inv-fst/snd projection AS A SIMP LEMMA except the `pullback.map`
  one. The project hits the gap because its iso chain's STEP 4 uses
  `asIso (pullback.map …)` for the inner `pullbackAwayιIso` lift,
  which has no Mathlib simp coverage.
- **Cost of current divergence**: 5 iters of CHURNING (iter-179 →
  iter-183) on this single iso projection. iter-183 progress-critic
  triggered mandatory analyst consult.
- **Verdict**: **BUILD_PROJECT_HELPER** + iter-184 recipe.
  Add two project-side `@[reassoc (attr := simp)]` lemmas
  `pullback_map_fst` / `pullback_map_snd` (4 LOC each, body is
  `pullback.lift_fst _ _ _` / `pullback.lift_snd _ _ _`). With these
  in the local simp set, the iso chain collapses cleanly. This is a
  candidate for upstream Mathlib contribution (the `pullback.map`
  abbrev SHOULD have its own `≫ fst/snd` simp lemma; project
  contribution can stay local-only).

### Decision 2: `@[simps]` on the iso would NOT help — chain projections need explicit named lemmas

- **Mathlib idiom**: `@[simps! hom inv]` on an `Iso`-valued `def`
  generates `_hom` and `_inv` field-projection lemmas at the iso's
  STRUCTURE level. For an iso defined as `≪≫`-chain, the generated
  lemmas merely UNFOLD the chain — they do NOT pre-compute the
  inv-fst/snd projections through the chain.
- **Project's current path**: the iter-182 task_result's open
  question 2 asked whether `@[simps]` on the iso would auto-generate
  the projection lemmas.
- **Gap**: divergent-and-wrong (the `@[simps]` route would not
  help; iter-183 attempt 1 effectively tried the unfolded form).
- **Verdict**: **PROCEED** (do not add `@[simps]` to the iso).
  Add EXPLICIT named projection lemmas:
  ```lean
  @[reassoc (attr := simp)]
  lemma gmScalingP1_cover_intersection_X_iso_inv_fst
      (kbar : Type u) [Field kbar] :
      (gmScalingP1_cover_intersection_X_iso kbar).inv ≫
        pullback.fst ((gmScalingP1_cover kbar).f 0)
                     ((gmScalingP1_cover kbar).f 1) =
      <explicit Spec.map composition>

  @[reassoc (attr := simp)]
  lemma gmScalingP1_cover_intersection_X_iso_inv_snd
      (kbar : Type u) [Field kbar] :
      (gmScalingP1_cover_intersection_X_iso kbar).inv ≫
        pullback.snd ((gmScalingP1_cover kbar).f 0)
                     ((gmScalingP1_cover kbar).f 1) =
      <explicit Spec.map composition>
  ```
  Each body is closed via the full simp recipe documented in
  Decision 1 + Recipe 1 below.

### Decision 3: the "shared target" is the EXISTING `Spec ((Away (X 0 · X 1)) ⊗ GmRing)` — NO new tensor-of-algebras helper

- **Mathlib idiom**: `Algebra.TensorProduct.map` exists
  (`Mathlib.RingTheory.TensorProduct.Basic`) and would produce
  `(Away (X 0)) ⊗ GmRing →ₐ (Away (X 0 · X 1)) ⊗ GmRing` from
  `awayMap X1_deg rfl ⊗ AlgHom.id`. But this is NOT needed for the
  cocycle.
- **What's actually needed**: both `iso.inv ≫ pullback.fst ≫ chart 0`
  and `iso.inv ≫ pullback.snd ≫ chart 1` are morphisms
  `Spec ((Away (X 0 · X 1)) ⊗ GmRing) ⟶ Proj 𝒜`. They factor through
  the open immersion `Proj.awayι (X 0 · X 1)` (= mono). After
  applying `Proj.SpecMap_awayMap_awayι.symm` to each side to rewrite
  `Spec.map (rm_i) ≫ awayι (X i) = Spec.map (rm_i ≫ awayMap X_{1-i} rfl)
  ≫ awayι (X 0 · X 1)`, cancel_mono `awayι (X 0 · X 1)` reduces to
  ring-level equality.
- **Gap**: divergent-and-wrong (the iter-183 attempt 5 explored a
  new tensor-of-algebras construction; was reverted due to
  `Classical.choice` body pattern).
- **Verdict**: **PROCEED** — keep the existing `Spec ((Away (X 0 · X 1))
  ⊗ GmRing)` target. Reduce to ring algebra via
  `SpecMap_awayMap_awayι.symm` + cancel_mono + `algHom_ext` +
  `Away.isLocalization_mul` + `t · u = 1`.

## Mathlib API citations (verified iter-184)

All paths are inside `.lake/packages/mathlib/Mathlib/`:

- `pullback.map` — `CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:267-271` (abbrev for `pullback.lift`).
- `pullback.lift_fst` — same file `:173-176` (`@[reassoc]` ONLY).
- `pullback.lift_snd` — same file `:178-181` (`@[reassoc]` ONLY).
- `pullback.map_isIso` — same file `:336-344` (instance; inverse formula `pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _`).
- `pullback.congrHom_inv` — same file `:354-359` (`@[simp]`; unfolds to `pullback.map`).
- `pullbackSymmetry_inv_comp_fst` / `_snd` — same file `:508-514` (`@[reassoc (attr := simp)]`).
- `pullbackRightPullbackFstIso_inv_fst` / `_snd_fst` / `_snd_snd` — `Pullback/Pasting.lean:470-487` (`@[reassoc (attr := simp)]`).
- `pullbackLeftPullbackSndIso_inv_fst` / `_snd_snd` / `_fst_snd` — same file `:536-552` (`@[reassoc (attr := simp)]`).
- `Proj.pullbackAwayιIso_inv_fst` / `_inv_snd` — `AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:291-301` (`@[reassoc (attr := simp)]`).
- `Proj.SpecMap_awayMap_awayι` — same file `:250-255` (`@[reassoc]`).
- `HomogeneousLocalization.Away.isLocalization_mul` — `RingTheory/GradedAlgebra/HomogeneousLocalization.lean:883`.
- `IsLocalization.Away.mul_invSelf` — `RingTheory/Localization/Away/Basic.lean` (search).

## Empirical verification (iter-184, lean_run_code probes)

### Probe 1: `pullback.lift_fst` is NOT a simp lemma

```lean
@[reassoc]                  -- iter-184 confirmed: only `@[reassoc]`, no simp
theorem pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    pullback.lift h k w ≫ pullback.fst f g = h := limit.lift_π _ _
```

### Probe 2: the 4-lemma `rw` recipe closes the `asIso (pullback.map …)` step

```lean
example {C : Type*} [Category C] {W X Y S : C}
    (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₂ : Y ⟶ S) [HasPullback f₁ g₂]
    (i₂ : X ≅ Y) (eq₁ : f₁ ≫ 𝟙 _ = 𝟙 _ ≫ f₁) (eq₂ : f₂ ≫ 𝟙 _ = i₂.hom ≫ g₂) :
    (asIso (pullback.map f₁ f₂ f₁ g₂ (𝟙 _) i₂.hom (𝟙 _) eq₁ eq₂)).inv ≫
        pullback.fst f₁ f₂ =
      pullback.fst f₁ g₂ := by
  rw [Iso.inv_comp_eq, asIso_hom, pullback.lift_fst, Category.comp_id]
```

**Result**: closes axiom-clean, NO sorries. ✓ iter-184 verified.

### Probe 3: the `simp only` recipe ALSO closes (4 lemmas)

```lean
example … : … := by
  simp only [Iso.inv_comp_eq, asIso_hom, pullback.lift_fst, Category.comp_id]
```

**Result**: closes axiom-clean. ✓ iter-184 verified.

### Probe 4: project-side simp lemma works through `asIso (pullback.map)`

```lean
@[reassoc (attr := simp)]
lemma pullback_map_fst {C : Type*} [Category C] {W X Y Z S T : C}
    (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂ ≫ pullback.fst g₁ g₂ =
      pullback.fst f₁ f₂ ≫ i₁ :=
  pullback.lift_fst _ _ _

example … :
    (asIso (pullback.map f₁ f₂ f₁ g₂ (𝟙 _) i₂.hom (𝟙 _) (by simp) (by
       rw [Category.comp_id]; exact eq₂))).inv ≫
      pullback.snd f₁ f₂ = pullback.snd f₁ g₂ ≫ i₂.inv := by
  rw [Iso.inv_comp_eq, asIso_hom, ← Category.assoc, pullback_map_snd]; simp
```

**Result**: closes axiom-clean. ✓ iter-184 verified.

## Verdicts (summary)

| Decision | Verdict | Severity |
|---|---|---|
| (1) `pullback.map ≫ pullback.fst/snd` has no Mathlib simp lemma; project must build local helpers | BUILD_PROJECT_HELPER | critical |
| (2) `@[simps]` on iso would NOT help; use explicit named projection lemmas | PROCEED | informational |
| (3) "Shared target" stays as `Spec ((Away (X 0 · X 1)) ⊗ GmRing)` — no new tensor-of-algebras | PROCEED | informational |

## Recipes

### Recipe 1 (CORE — Lane B closure)

Add the two helper simp lemmas at the TOP of the namespace `AlgebraicGeometry`
section in `Genus0BaseObjects/GmScaling.lean` (between L41 and L54), OR in a
new helpers file `Genus0BaseObjects/PullbackMapSimp.lean` imported there:

```lean
/-- Projection simp lemma for `pullback.map`'s composition with `pullback.fst`.
Mathlib's `pullback.lift_fst` (which this body delegates to) is `@[reassoc]`
ONLY, so `simp` does NOT auto-fire on `pullback.map ≫ pullback.fst`. Adding
this local helper unblocks `Iso.trans`-chain projection collapsing for the
`gmScalingP1_cover_intersection_X_iso` chain (whose step 4 uses
`asIso (pullback.map …)`). Candidate for upstream Mathlib contribution. -/
@[reassoc (attr := simp)]
lemma pullback_map_fst_proj {C : Type*} [Category C] {W X Y Z S T : C}
    (f₁ : W ⟶ S) (f₂ : X ⟶ S) [Limits.HasPullback f₁ f₂] (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) [Limits.HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    Limits.pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂ ≫
        Limits.pullback.fst g₁ g₂ =
      Limits.pullback.fst f₁ f₂ ≫ i₁ :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullback_map_snd_proj {C : Type*} [Category C] {W X Y Z S T : C}
    (f₁ : W ⟶ S) (f₂ : X ⟶ S) [Limits.HasPullback f₁ f₂] (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) [Limits.HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    Limits.pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂ ≫
        Limits.pullback.snd g₁ g₂ =
      Limits.pullback.snd f₁ f₂ ≫ i₂ :=
  Limits.pullback.lift_snd _ _ _
```

### Recipe 2 (the two projection lemmas)

After Recipe 1's helpers are added, prove the two iso projection lemmas:

```lean
@[reassoc (attr := simp)]
private lemma gmScalingP1_cover_intersection_X_iso_inv_fst
    (kbar : Type u) [Field kbar] :
    (gmScalingP1_cover_intersection_X_iso kbar).inv ≫
      pullback.fst ((gmScalingP1_cover kbar).f (0 : Fin 2))
                   ((gmScalingP1_cover kbar).f (1 : Fin 2)) =
    -- The RHS is determined by the iso chain. Concretely it should be
    -- `Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map ...))`
    -- but the EXACT form falls out of the simp once the chain collapses;
    -- the prover should `change ?goal` AFTER running the simp body to
    -- see the precise form, then transcribe it.
    sorry := by
  unfold gmScalingP1_cover_intersection_X_iso
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc,
    pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd,
    pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
    pullbackRightPullbackFstIso_inv_fst, pullbackRightPullbackFstIso_inv_snd_fst,
    pullbackRightPullbackFstIso_inv_snd_snd,
    pullbackRightPullbackFstIso_hom_fst, pullbackRightPullbackFstIso_hom_snd,
    pullbackLeftPullbackSndIso_inv_fst, pullbackLeftPullbackSndIso_inv_snd_snd,
    pullbackLeftPullbackSndIso_inv_fst_snd,
    pullback.congrHom_inv, pullback.congrHom_hom,
    pullback_map_fst_proj, pullback_map_snd_proj,  -- Recipe 1 helpers
    pullback.lift_fst, pullback.lift_snd,           -- belt + braces
    Proj.pullbackAwayιIso_inv_fst, Proj.pullbackAwayιIso_inv_snd,
    Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left,
    Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right,
    Iso.inv_comp_eq, asIso_hom, asIso_inv,
    Category.id_comp, Category.comp_id]
  -- The simp pass should close most of the chain; the residual should
  -- be a Spec.map equality that you transcribe into the `sorry` RHS above.
  rfl  -- or whatever closes the residual
```

(Mirror for `_inv_snd`.)

**Prover strategy**: write the lemma with `RHS = ?_` (named hole), run the
simp body, then read the goal and transcribe the residual into the RHS.
This avoids the iter-183 attempt 5 "Classical.choice" pattern because the
RHS is now COMPUTED by simp, not GUESSED.

### Recipe 3 (cocycle closure)

With the two projection lemmas in hand, the cocycle proof becomes ~20 LOC:

```lean
private lemma gmScalingP1_chart_agreement_cross01 (kbar : Type u) [Field kbar] :
    pullback.fst ((gmScalingP1_cover kbar).f (0 : Fin 2))
        ((gmScalingP1_cover kbar).f (1 : Fin 2)) ≫
      gmScalingP1_chart kbar (0 : Fin 2) =
    pullback.snd ((gmScalingP1_cover kbar).f (0 : Fin 2))
        ((gmScalingP1_cover kbar).f (1 : Fin 2)) ≫
      gmScalingP1_chart kbar (1 : Fin 2) := by
  apply (cancel_epi (gmScalingP1_cover_intersection_X_iso kbar).inv).mp
  -- Both sides now have shape `iso.inv ≫ pullback.fst/snd ≫ chart i`.
  -- Apply the projection lemmas to collapse `iso.inv ≫ pullback.fst/snd`.
  simp only [← Category.assoc,
    gmScalingP1_cover_intersection_X_iso_inv_fst,
    gmScalingP1_cover_intersection_X_iso_inv_snd]
  -- Goal: `Spec.map (RHS_fst) ≫ chart 0 = Spec.map (RHS_snd) ≫ chart 1`.
  -- Unfold `chart i = iso_i.hom ≫ Spec.map (rm_i) ≫ awayι (X i)`.
  unfold gmScalingP1_chart
  -- Collapse Spec.map and awayι using SpecMap_awayMap_awayι:
  --   awayι (X i) = Spec.map (awayMap X_{1-i} rfl) ≫ awayι (X 0 · X 1)
  -- so both sides factor through awayι (X 0 · X 1).
  -- After cancel_mono awayι (X 0 · X 1), reduce to Spec.map equality.
  rw [← Proj.SpecMap_awayMap_awayι (projectiveLineBarGrading kbar)
        (projectiveLineBarAffineCover_fDeg kbar 0)
        (projectiveLineBarAffineCover_hm 0)
        (projectiveLineBarAffineCover_fDeg kbar 1) rfl,
      ← Proj.SpecMap_awayMap_awayι (projectiveLineBarGrading kbar)
        (projectiveLineBarAffineCover_fDeg kbar 1)
        (projectiveLineBarAffineCover_hm 1)
        (projectiveLineBarAffineCover_fDeg kbar 0) (mul_comm _ _)]
  rw [← cancel_mono (Proj.awayι (projectiveLineBarGrading kbar) _ _ _)]
  -- ... etc. Residual is ring-level `t · u = 1` via `IsLocalization.Away.mul_invSelf`.
  sorry  -- ~10 LOC of MvPolynomial.algHom_ext + Away.isLocalization_mul
```

### Reversal trigger

If Recipe 1's project-side `pullback_map_fst_proj` simp lemma causes
universe-resolution issues (because of the abstract `{C : Type*}`
declaration), restrict the helpers to `Scheme` directly:

```lean
@[reassoc (attr := simp)]
lemma pullback_map_fst_scheme
    {W X Y Z S T : Scheme.{u}}
    (f₁ : W ⟶ S) (f₂ : X ⟶ S) ... := ...
```

If even the restricted-to-`Scheme` form runs into instance synthesis
issues at the call site (the `gmScalingP1_cover_intersection_X_iso`
body has multiple `HasPullback` resolutions), iter-185 falls back to
"prove the two projection lemmas in **fully manual** style", using
`pullback.hom_ext` to reduce each `_inv_fst/snd = RHS` lemma to its
own fst/snd projection, then closing each with the explicit Mathlib
`pullback.lift_fst` (not via simp). LOC delta: +30-50 per lemma
(instead of +5-10 with the simp helpers).

## What did NOT need to change

- `gmScalingP1_cover_intersection_X_iso` definition (axiom-clean iter-182).
- `Proj.pullbackAwayιIso` choice (the right Mathlib idiom).
- `Proj.SpecMap_awayMap_awayι` choice (the right reassoc lemma).
- The `cancel_epi iso.inv` step (correct, retained from iter-183).
- The ring-level identity `λ · u = (1/t) · λ` reduction strategy
  (correct, will close via `Away.isLocalization_mul` once the iso
  chain collapses).

## Cost analysis

| Phase | LOC | Risk |
|---|---|---|
| Recipe 1 (2 simp helpers) | ~8 | very low (direct unfolds via `pullback.lift_fst/snd`) |
| Recipe 2 (2 projection lemmas) | ~30-40 each | low (simp set verified to fire on simpler cases) |
| Recipe 3 (cocycle body) | ~25-40 | medium (ring algebra; well-mapped via `Away.isLocalization_mul`) |
| **Total** | **~95-130** | **CAN CLOSE iter-184 single lane** |

The iter-183 task_result's "~40-80 LOC of cleanly-mappable simp/rewrite"
estimate was right in spirit but missing the Recipe 1 helpers, which add
~8 LOC and dispel the iso-chain blocker.

## Recommendation

**The iter-183 Lane B failure was a missing simp-lemma diagnostic, not
a structural strategy failure.** Mathlib has every iso-step's
inv-fst/snd projection as a simp lemma EXCEPT for `pullback.map` itself
(where `pullback.lift_fst/snd` are `@[reassoc]` only, not `@[simp]`).
Adding two project-side simp helpers (Recipe 1, ~8 LOC) unblocks the
chain collapse for the project's iso (whose step 4 is `asIso
(pullback.map …)`).

iter-184 should:

1. **Land Recipe 1** at the top of `Genus0BaseObjects/GmScaling.lean`
   (~8 LOC, axiom-clean).
2. **Land Recipe 2** — the two named projection lemmas for the iso
   (~60-80 LOC across both, axiom-clean).
3. **Re-fire `gmScalingP1_chart_agreement_cross01` via Recipe 3**
   (~25-40 LOC of cleanly-mappable rewrites + ring-level
   `IsLocalization.Away.mul_invSelf` for the `t · u = 1` residual).

**Total iter-184 Lane B**: ~95-130 LOC across 3 sub-tasks, all
axiom-clean if the Recipe 2 projection lemmas type-check (the
empirical probes 2-4 of this consult give high confidence).

If Recipe 1's `{C : Type*}` universe abstraction breaks instance
synthesis at the call site, restrict to `Scheme.{u}` (Reversal
trigger above). If Recipe 2's chain simp fails on the FULL 7-step
iso (despite working on isolated steps in the probes), fall back to
manual `pullback.hom_ext` decomposition (+30-50 LOC per lemma).
