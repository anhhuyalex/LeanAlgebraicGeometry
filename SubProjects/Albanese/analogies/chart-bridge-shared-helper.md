# Analogy: shared per-chart helper `gmScalingP1_chart_PLB_eq` closing the chart-bridge / over-coherence pair

## Mode
api-alignment

## Slug
chart-bridge-shared-helper

## Iteration
174

## Question

Is there a structural Mathlib idiom for "a morphism out of a glued cover factors through a `Spec.map (algebraMap kbar _)` to a target scheme via a per-chart shared certificate"? Concretely:

- Does Mathlib have `Scheme.Cover.glueMorphisms_comp`?
- Does Mathlib have `Cover.hom_ext_of_agreement` (≈ the iter-174 prover's name for the per-chart-certificate idiom)?
- If not, is the helper-budget = 0 sustainable, or is the recurring "chart-bridge specialisation" blocker a sign of a deeper Mathlib gap?

## Project artifact(s)
- `AlgebraicJacobian/Genus0BaseObjects.lean:796-805` — `awayι_comp_PLB_hom` (iter-173 axiom-clean step (a) sub-lemma; takes generic homogeneous degree-1 `f`).
- `AlgebraicJacobian/Genus0BaseObjects.lean:862-893` — `gmScalingP1_cover_X_iso kbar i` (iter-173 axiom-clean structural iso `(cover).X i ≅ Spec (Away_i ⊗[kbar] GmRing)`).
- `AlgebraicJacobian/Genus0BaseObjects.lean:908-927` — `gmScalingP1_chart kbar i` (axiom-clean chart scheme morphism, definitional form `iso.hom ≫ Spec.map (eval₂Hom.comp iso_alg) ≫ Proj.awayι`).
- `AlgebraicJacobian/Genus0BaseObjects.lean:944-950` — `gmScalingP1_chart_agreement` (top-level scaffold `sorry` — cocycle).
- `AlgebraicJacobian/Genus0BaseObjects.lean:961-990` — `gmScalingP1_over_coherence` (top-level scaffold `sorry` — `glued ≫ PLB.hom = (PLB ⊗ Gm).hom`).
- `AlgebraicJacobian/Genus0BaseObjects.lean:545-553` — `homogeneousLocalizationAwayIso` (`RingEquiv.ofRingHom` from `homogeneousLocalizationAwayToMvPoly` + `mvPolyToHomogeneousLocalizationAway`; *not* an `AlgEquiv`).

## Decisions identified

### Decision 1: Does Mathlib ship `Scheme.Cover.glueMorphisms_comp` or `Cover.hom_ext_of_agreement`?

- **Mathlib idiom**: PARTIAL. Mathlib has the *frame*, but not the named composite the iter-174 prover is searching for.
  - `AlgebraicGeometry.Scheme.Cover.hom_ext` (verbatim signature, `Mathlib.AlgebraicGeometry.Gluing:448`):
    ```lean
    theorem hom_ext (𝒰 : OpenCover.{v} X) {Y : Scheme} (f₁ f₂ : X ⟶ Y)
        (h : ∀ x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
    ```
    This is the closest existing analogue of `Cover.hom_ext_of_agreement`. It does NOT package "per-chart equation via a shared Spec-level certificate"; it just says "two morphisms agree iff per-chart". The certificate has to be supplied at every invocation.
  - `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms` (`Mathlib.AlgebraicGeometry.Gluing:457` — `@[reassoc (attr := simp)]`):
    ```lean
    theorem ι_glueMorphisms (𝒰 : OpenCover.{v} X) ...
        (x : 𝒰.I₀) : 𝒰.f x ≫ 𝒰.glueMorphisms f hf = f x
    ```
    The simp/reassoc form is essential — it turns "glued ≫ target" into per-chart `target_x` after applying `Cover.hom_ext`. **This IS the per-chart certificate idiom**, but at the level of unwinding `glueMorphisms`, not at the level of a target-side `Spec.map (algebraMap kbar _)` factorisation.

- **The two named lemmas the prover searched for**:
  - `Scheme.Cover.glueMorphisms_comp` — **NOT IN MATHLIB**. Searched via `lean_local_search "glueMorphisms_comp"` and grep — no matches. The natural form `(𝒰.glueMorphisms f hf) ≫ g = 𝒰.glueMorphisms (fun i ↦ f i ≫ g) ...` would require a *fresh* cocycle hypothesis on `f i ≫ g`, so the natural way to compose `glueMorphisms` with a target morphism is to `apply Cover.hom_ext` then `simp [ι_glueMorphisms_assoc]`. Mathlib doesn't bundle this — it's an idiom, not a named lemma.
  - `Cover.hom_ext_of_agreement` — **NOT IN MATHLIB** (also not searched-hit). The closest is bare `Cover.hom_ext`, which does NOT bundle a per-chart certificate.

- **There IS a Mathlib variant** at `Mathlib.AlgebraicGeometry.Cover.Directed.glueMorphismsOverOfLocallyDirected` (`Cover/Directed.lean:236-253`) that *does* bundle an `Over S` coherence (input `w : ∀ i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom`). But it requires `[𝒰.LocallyDirected]` — overkill for a 2-chart cover and irrelevant to our cover.

- **Gap**: divergent-equivalent. Mathlib *has* `Cover.hom_ext` + `ι_glueMorphisms` (the structural pair), but does NOT have a *single-lemma* form that bundles "glued ≫ target = ... via per-chart certificate". The project must apply both lemmas plus the per-chart Spec-level certificate inline.
- **Cost of divergence**: ~3-5 LOC per `gmScalingP1_over_coherence`-style call — the prover writes `apply Cover.hom_ext; intro i; simp only [ι_glueMorphisms_assoc]; exact <per-chart certificate>`. NOT a bridge lemma needed.
- **Verdict**: **PROCEED with `Cover.hom_ext` + `ι_glueMorphisms_assoc` + project-side per-chart certificate**.

### Decision 2: Does the iter-173 sketch's "single shared helper" close BOTH scaffolds?

- **What the iter-173 file proposed**: `gmScalingP1_chart_PLB_eq i : chart i ≫ PLB.hom = (cover).f i ≫ (PLB ⊗ Gm).hom`, claimed to close BOTH `gmScalingP1_over_coherence` AND `gmScalingP1_chart_agreement`.
- **Independent check**:
  - **For `gmScalingP1_over_coherence`**: YES — the helper exactly hits the per-chart equation after `Cover.hom_ext` + `ι_glueMorphisms_assoc`. Closure: ~3-5 LOC + the helper itself (~20-30 LOC).
  - **For `gmScalingP1_chart_agreement`**: PARTIAL — the cocycle is
    ```
    ∀ x y, pullback.fst ((cover).f x) ((cover).f y) ≫ chart x =
           pullback.snd _ _ ≫ chart y
    ```
    Both sides land in `ProjectiveLineBarScheme` (≠ `(PLB ⊗ Gm).hom`'s target `Spec kbar`). Post-composing both sides with `PLB.hom` makes the helper applicable, BUT that's NOT what the cocycle demands — the cocycle demands equality at the `ProjectiveLineBarScheme` level. So the helper does NOT close the cocycle directly.
    - **Diagonal cases `x = y`**: trivial via `CategoryTheory.Limits.fst_eq_snd_of_mono_eq` (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono:199`), since `(cover).f i = pullback.fst (pullback.fst PLB.hom Gm.hom) (Proj.awayι _ ...)` is `IsOpenImmersion` (hence mono) by `Mathlib.AlgebraicGeometry.OpenImmersion:544` (pullback of `Proj.awayι` along anything is `IsOpenImmersion`). Closure: 1-2 LOC.
    - **Cross cases `(0,1)` and `(1,0)`**: substantive algebraic content `λ·u = (1/t)·λ` in `Localization.Away t ⊗[kbar] GmRing` (per `analogies/gmscaling-deep.md` Q4). The shared helper is NOT directly applicable — the cross-chart agreement happens on the *intersection* of two charts, where the bridge isos (one for each chart) AND the chart ring maps both come into play.

- **Gap**: divergent-and-wrong (the iter-173 file). The "single helper closes both" framing was optimistic. The helper closes ONE scaffold (`over_coherence`) cleanly, and provides ZERO direct leverage for the cocycle cross cases.
- **Cost of misframing**: a single iter of misdirected prover effort (chasing "one helper to rule them all" when two distinct techniques are needed). Severity is high because the iter-173 file *recommended* a "single ~50-60 LOC helper" budget that does not exist.
- **Verdict**: **ALIGN_WITH_MATHLIB** on framing — the helper closes `over_coherence`; `chart_agreement` needs its own machinery. Split the iter-174 prover lane into TWO sub-tasks (instead of one unified helper):
  - **Sub-task A — `over_coherence`**: build the shared helper `gmScalingP1_chart_PLB_eq`, then close `over_coherence` via `Cover.hom_ext` + `ι_glueMorphisms_assoc` + helper. ~30-40 LOC total.
  - **Sub-task B — `chart_agreement`**: diagonal cases via `fst_eq_snd_of_mono_eq`; cross cases via the algebraic `λ·u = (1/t)·λ` identity (per `analogies/gmscaling-deep.md` Q4). ~40-60 LOC total.

### Decision 3: Concrete recipe for the shared helper `gmScalingP1_chart_PLB_eq` (`over_coherence` half)

- **Target signature**:
  ```lean
  private lemma gmScalingP1_chart_PLB_eq (kbar : Type u) [Field kbar] (i : Fin 2) :
      gmScalingP1_chart kbar i ≫ (ProjectiveLineBar kbar).hom =
      (gmScalingP1_cover kbar).f i ≫ ((ProjectiveLineBar kbar) ⊗ Gm kbar).hom
  ```

- **8-step lemma chain** (mapped to verbatim Mathlib citations):

  | # | Lemma | Cite | Purpose |
  |---|---|---|---|
  | 1 | `AlgebraicGeometry.Spec.map_comp` | `Mathlib.AlgebraicGeometry.Scheme:507` | `Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f` (contravariance). Used to merge / split `Spec.map`s. |
  | 2 | `awayι_comp_PLB_hom` (project) | `Genus0BaseObjects.lean:796` | `Proj.awayι _ f hf _ ≫ PLB.hom = Spec.map (algMap kbar (Away_f))` (existing). |
  | 3 | **NEW: `homogeneousLocalizationAwayIso_algebraMap`** (~5-10 LOC, project-side) | — | `(homogeneousLocalizationAwayIso kbar i).toRingHom.comp (algMap kbar Away_i) = algMap kbar (MvPolynomial Unit kbar)`. The kbar-algebra preservation of the iso. Derives from `aux_right` round-trip or by direct `unfold + MvPolynomial.ringHom_ext`. |
  | 4 | `MvPolynomial.eval₂Hom_C` | `Mathlib.Algebra.MvPolynomial.Eval` | `(eval₂Hom f g).comp C = f`, so `(eval₂Hom (algMap kbar T) val).comp (algMap kbar (MvPolynomial Unit kbar)) = algMap kbar T`. (`T = Away_i ⊗ GmRing`.) |
  | 5 | `AlgebraicGeometry.pullbackSpecIso_hom_base` | `Mathlib.AlgebraicGeometry.Pullbacks:766` | `pullbackSpecIso.hom ≫ Spec.map (algMap R (S ⊗[R] T)) = pullback.fst _ _ ≫ Spec.map (algMap R S)`. THE bridge identity. |
  | 6 | `CategoryTheory.Limits.pullback.congrHom_hom` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:349` (`@[simps! hom]`) | `pullback.congrHom_hom = pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _`. Composed with `pullback.fst`, gives `pullback.fst _ _` after a `𝟙` cancellation. |
  | 7 | `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting:459` | `.hom ≫ pullback.fst (f' ≫ f) g = pullback.fst f' (pullback.fst f g)`. |
  | 8 | `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `.hom ≫ pullback.fst _ _ = pullback.snd _ _`. |
  | 9 | `CategoryTheory.Limits.pullback.condition` | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `pullback.fst f g ≫ f = pullback.snd f g ≫ g`. |
  | 10 | `CategoryTheory.Over.tensorObj_hom` | `Mathlib.CategoryTheory.Monoidal.Cartesian.Over:62` | `(R ⊗ S).hom = pullback.fst R.hom S.hom ≫ R.hom` (recognizes RHS form). |

  (Listed 10 instead of 8 because the directive said "5-8" but the recipe genuinely needs them — none are bypassable.)

- **The proof chain** (in pseudocode, expand 1:1 to ~20-30 LOC of Lean):
  ```
  -- LHS = iso.hom ≫ Spec.map (eval₂Hom.comp iso_alg) ≫ Proj.awayι ≫ PLB.hom
  rw [Category.assoc]                                            -- bracket: iso.hom ≫ (Spec.map _ ≫ Proj.awayι ≫ PLB.hom)
  rw [awayι_comp_PLB_hom]                                        -- Proj.awayι ≫ PLB.hom → Spec.map (algMap kbar Away_i)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]                 -- Spec.map composite ≫ Spec.map algMap → Spec.map ((algMap) ≫ composite)
  -- New goal: iso.hom ≫ Spec.map (composite_ring_with_algMap) = RHS
  -- where composite_ring_with_algMap = algMap kbar Away_i ≫ (eval₂Hom.comp iso_alg)
  -- Use step (3) + step (4) to identify this with algMap kbar (Away_i ⊗ GmRing):
  rw [show (algMap kbar Away_i) ≫ eval₂Hom.comp iso_alg = algMap kbar (Away_i ⊗ GmRing) from by
    -- via homogeneousLocalizationAwayIso_algebraMap (step 3) and MvPolynomial.eval₂Hom_C (step 4):
    -- algMap kbar Away_i ≫ iso_alg = algMap kbar (Mv Unit kbar)  -- step 3
    -- then ≫ eval₂Hom = eval₂Hom.comp (algMap kbar (Mv Unit kbar)) = algMap kbar (Away_i ⊗ GmRing)  -- step 4
    ...]
  -- New goal: iso.hom ≫ Spec.map (algMap kbar (Away_i ⊗ GmRing)) = (cover).f i ≫ (PLB ⊗ Gm).hom
  -- Unfold iso = pullbackSymmetry ≫ pullbackRightPullbackFstIso ≫ pullback.congrHom ≫ pullbackSpecIso
  unfold gmScalingP1_cover_X_iso  -- or `simp only [gmScalingP1_cover_X_iso]`
  simp only [Iso.trans_hom, pullbackSpecIso_hom_base]            -- step 5: pullbackSpecIso.hom ≫ Spec.map (algMap R tensor) = pullback.fst _ _ ≫ Spec.map (algMap R S)
  -- LHS ≈ (pullbackSymmetry ≫ pullbackRightPullbackFstIso ≫ pullback.congrHom).hom
  --      ≫ pullback.fst (Spec.map (algMap kbar Away_i)) (Spec.map (algMap kbar GmRing))
  --      ≫ Spec.map (algMap kbar Away_i)
  simp only [pullback.congrHom_hom, pullback.map_fst,            -- step 6
             pullbackRightPullbackFstIso_hom_fst,                -- step 7
             pullbackSymmetry_hom_comp_fst]                      -- step 8
  -- LHS ≈ pullback.snd (pullback.fst PLB.hom Gm.hom) (Proj.awayι _ (X i) _ _) ≫ Spec.map (algMap kbar Away_i)
  -- Reverse step 2:
  rw [← awayι_comp_PLB_hom]                                      -- Spec.map (algMap kbar Away_i) → Proj.awayι ≫ PLB.hom
  -- LHS ≈ pullback.snd _ _ ≫ Proj.awayι ≫ PLB.hom
  -- pullback.snd _ _ ≫ Proj.awayι _ (X i) _ _ = pullback.fst _ _ ≫ pullback.fst PLB.hom Gm.hom (by pullback.condition):
  rw [← Category.assoc, pullback.condition]                      -- step 9 (note direction of fst vs snd)
  -- LHS ≈ (cover).f i ≫ pullback.fst PLB.hom Gm.hom ≫ PLB.hom
  -- RHS ≈ (cover).f i ≫ (PLB ⊗ Gm).hom; unfold via tensorObj_hom:
  rw [Over.tensorObj_hom]                                        -- step 10
  -- Both sides match. ✓
  ```
  (Note: the exact direction of `pullback.condition` and which side is `fst`/`snd` requires care; the analyst above traced `(cover).f i = pullback.fst _ _` and `pullback.snd ≫ Proj.awayι = pullback.fst ≫ pullback.fst PLB.hom Gm.hom` matches the project's `(cover).f i = pullback.fst` convention from `PreZeroHypercover.pullback₁`.)

- **Verdict**: **PROCEED with the 10-lemma chain**.

### Decision 4: The optimistic single-shot recipe in iter-173's `chart-bridge.md` — does it stand?

- **iter-173 sketch (steps 1-5)**:
  1. `Cover.hom_ext` on the cocycle pair-wise. ← **Wrong loop** (the cocycle is a *hypothesis* of `glueMorphisms`, not something `Cover.hom_ext` applies to). `Cover.hom_ext` reduces *over_coherence*'s equation, NOT the cocycle.
  2. Per-`i` case: reduce LHS to `iso_i.hom ≫ Spec.map (chartMap_i.comp (algMap kbar Away_i)) ≫ Proj.awayι` using `awayι_comp_PLB_hom`. ✓ for `over_coherence`; nonsense for cocycle.
  3. Show RHS via `tensorObj_hom`. ✓ for `over_coherence`.
  4. Use `pullbackSpecIso_hom_fst` + `pullbackRightPullbackFstIso_hom_fst` + `pullbackSymmetry_hom_comp_fst`. ← The right key lemma here is `pullbackSpecIso_hom_base` (NOT `pullbackSpecIso_hom_fst`), since we're aligning with `Spec.map (algMap kbar (S ⊗[kbar] T))`, not `Spec.map (algMap S (S ⊗[kbar] T))`.
  5. Combine. ✓ for `over_coherence`.

- **Structural mismatches in iter-173 sketch**:
  1. Step 1 misframed: applies to `over_coherence`, NOT the cocycle. The cocycle needs `fst_eq_snd_of_mono_eq` + algebraic content (`λ·u = (1/t)·λ`).
  2. Step 4's bridge identity is `pullbackSpecIso_hom_base` (which lands on `Spec.map (algMap R (S ⊗[R] T))`), not `pullbackSpecIso_hom_fst` (which lands on `Spec.map (includeLeftRingHom)`). The two differ by an additional `algMap S (S ⊗[R] T)` step; using `_hom_fst` forces a Spec.map-of-includeLeft detour that is unnecessary.
  3. Step (a) "kbar-linearity" — the iter-173 file *mentions* this is "via `MvPolynomial.eval₂Hom_C` + the iso's preservation of `algMap kbar` (which needs ~10 LOC)" but does NOT explicitly land the kbar-algebra preservation lemma for `homogeneousLocalizationAwayIso`. **This is the load-bearing missing sub-lemma**.

- **Verdict on iter-173 sketch**: ALIGN_WITH_MATHLIB on framing (i.e. *refine* the sketch); keep the proof chain skeleton but correct the misframings above.

## Verdicts (summary)

| Decision | Verdict | Severity |
|---|---|---|
| (1) Mathlib has no `glueMorphisms_comp` / `hom_ext_of_agreement`; has the structural pair `Cover.hom_ext` + `ι_glueMorphisms` | PROCEED | informational |
| (2) The shared helper closes `over_coherence` but NOT `chart_agreement` (cocycle needs its own machinery) | ALIGN_WITH_MATHLIB | critical |
| (3) 10-step concrete recipe for `gmScalingP1_chart_PLB_eq`; needs ONE new sub-lemma (`homogeneousLocalizationAwayIso_algebraMap`) | PROCEED | informational |
| (4) iter-173 sketch's steps 1, 4, and missing (a)-detail need refinement | ALIGN_WITH_MATHLIB | informational |

## Recommendation

**SPLIT the iter-174 prover lane into two sub-tasks**:

### Sub-task A — `gmScalingP1_over_coherence` (~30-40 LOC total)

1. **Land `homogeneousLocalizationAwayIso_algebraMap`** (~5-10 LOC, new sub-lemma):
   ```lean
   private lemma homogeneousLocalizationAwayIso_algebraMap (kbar : Type u) [Field kbar] (i : Fin 2) :
       (homogeneousLocalizationAwayIso kbar i).toRingHom.comp
           (algebraMap kbar (HomogeneousLocalization.Away (projectiveLineBarGrading kbar)
             (MvPolynomial.X i : MvPolynomial (Fin 2) kbar))) =
         algebraMap kbar (MvPolynomial Unit kbar) := by
     -- Use the round-trip aux_right OR direct ringHom_ext on the forward map via
     -- Localization.awayLift / chartEvalRingHom; the constants r ∈ kbar map via
     -- (forward ∘ kbarToAwayRingHom)(r) = chartEvalRingHom (C r) = C r = algebraMap kbar (Mv Unit kbar) r.
     ...
   ```
2. **Land `gmScalingP1_chart_PLB_eq`** (~20-30 LOC, the shared helper):
   ```lean
   private lemma gmScalingP1_chart_PLB_eq (kbar : Type u) [Field kbar] (i : Fin 2) :
       gmScalingP1_chart kbar i ≫ (ProjectiveLineBar kbar).hom =
       (gmScalingP1_cover kbar).f i ≫ ((ProjectiveLineBar kbar) ⊗ Gm kbar).hom := by
     unfold gmScalingP1_chart gmScalingP1_cover_X_iso
     fin_cases i  -- the iso is match-on-i; two parallel branches
     all_goals
       simp only [Iso.trans_hom, Category.assoc, awayι_comp_PLB_hom, ← Spec.map_comp,
         ← CommRingCat.ofHom_comp, RingHom.comp_assoc,
         homogeneousLocalizationAwayIso_algebraMap, MvPolynomial.eval₂Hom_C,
         pullbackSpecIso_hom_base, pullback.congrHom_hom, pullback.map_fst,
         pullbackRightPullbackFstIso_hom_fst, pullbackSymmetry_hom_comp_fst,
         Over.tensorObj_hom, pullback.condition_assoc]
     -- residual is a rfl on `Spec.map ((algMap kbar Away_i) ≫ composite) = Spec.map (algMap kbar tensor)`
     -- once the algebraMap chain is identified
   ```
3. **Close `gmScalingP1_over_coherence` body** (~3-5 LOC):
   ```lean
   lemma gmScalingP1_over_coherence (kbar : Type u) [Field kbar] :
       (gmScalingP1_cover kbar).glueMorphisms
           (gmScalingP1_chart kbar) (gmScalingP1_chart_agreement kbar) ≫
         (ProjectiveLineBar kbar).hom =
       ((ProjectiveLineBar kbar) ⊗ Gm kbar).hom := by
     refine Scheme.Cover.hom_ext (gmScalingP1_cover kbar) _ _ ?_
     intro i
     rw [Scheme.Cover.ι_glueMorphisms_assoc]
     exact gmScalingP1_chart_PLB_eq kbar i
   ```

### Sub-task B — `gmScalingP1_chart_agreement` (~40-60 LOC, INDEPENDENT of the helper)

```lean
lemma gmScalingP1_chart_agreement (kbar : Type u) [Field kbar] :
    ∀ x y : (gmScalingP1_cover kbar).I₀,
      pullback.fst ((gmScalingP1_cover kbar).f x) ((gmScalingP1_cover kbar).f y) ≫
          gmScalingP1_chart kbar x =
        pullback.snd ((gmScalingP1_cover kbar).f x) ((gmScalingP1_cover kbar).f y) ≫
          gmScalingP1_chart kbar y := by
  intro x y
  -- (cover).f i is IsOpenImmersion (pullback of Proj.awayι), hence Mono.
  haveI : Mono ((gmScalingP1_cover kbar).f x) := inferInstance
  haveI : Mono ((gmScalingP1_cover kbar).f y) := inferInstance
  fin_cases x <;> fin_cases y
  · -- (0,0) diagonal:
    rw [CategoryTheory.Limits.fst_eq_snd_of_mono_eq]
  · -- (0,1) cross: λ·u = (1/t)·λ algebra
    sorry  -- the cross-case algebra (per analogies/gmscaling-deep.md Q4)
  · -- (1,0) cross: symmetric of (0,1)
    sorry  -- by symmetry
  · -- (1,1) diagonal:
    rw [CategoryTheory.Limits.fst_eq_snd_of_mono_eq]
```

The cross cases (0,1)/(1,0) need the `λ·u = (1/t)·λ` algebraic content per `analogies/gmscaling-deep.md` Q4 — NOT covered by the shared helper. They use:
- The chart-bridge for *both* charts simultaneously (chart 0 + chart 1).
- `pullbackSpecIso` for the intersection ring `Away (X 0 · X 1) ⊗[kbar] GmRing`.
- The ring identity `(1/t) · λ = λ · u` in `Localization.Away t ⊗[kbar] GmRing`.

**Recommended deferral**: if iter-174 budget is tight, land Sub-task A (closes `over_coherence` axiom-clean) and leave `chart_agreement`'s cocycle cross cases as a top-level scaffold sorry for iter-175. The diagonal cases (1-2 LOC each via `fst_eq_snd_of_mono_eq`) can land trivially in iter-174 even if cross cases defer.

## Why the helper-budget = 0 framing is **sustainable** (no Mathlib gap)

The recurring "chart-bridge specialisation" blocker phrase across iter-172/173 is misleading: Mathlib DOES have all the pieces (`pullbackSpecIso_hom_base`, `pullbackRightPullbackFstIso_hom_fst`, `pullbackSymmetry_hom_comp_fst`, `pullback.congrHom_hom`, `Cover.hom_ext`, `ι_glueMorphisms`). What's missing is *one project-side sub-lemma* (`homogeneousLocalizationAwayIso_algebraMap`) — and that's a content-specific fact (the iso's kbar-algebra preservation), not a missing Mathlib bridge. A Mathlib mini-bridge for "chart Spec.map factor through algebraMap kbar" would NOT help downstream Cover.glueMorphisms invocations because every such invocation has its own ring map — the kbar-algebra preservation always requires content-specific verification.

**Verdict on the structural question**: the recurring blocker is NOT a Mathlib gap. It's a per-iter content-specific kbar-algebra-preservation lemma that the project must produce alongside each `homogeneousLocalizationAwayIso`-style iso. The iter-173 file's "single 30-LOC bridge" framing should have called this out; iter-174's split into sub-task A (`over_coherence`) + sub-task B (`chart_agreement`) is the right framing.
