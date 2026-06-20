# Analogy: bridging `pullback (pullback.fst PLB.hom Gm.hom) (Proj.awayι …)` to `Spec ((Away 𝒜 X_i) ⊗[kbar] GmRing)`

## Mode
api-alignment

## Slug
chart-bridge173

## Iteration
173

## Question
What is the right Mathlib idiom for the structural iso
```
(gmScalingP1_cover kbar).X i ≅ Spec ((HomogeneousLocalization.Away 𝒜 (X i)) ⊗[kbar] (GmRing kbar))
```
where `(gmScalingP1_cover kbar).X i = pullback (pullback.fst PLB.hom Gm.hom) (Proj.awayι 𝒜 (X i) _ _)`?

## Project artifact(s)
- `AlgebraicJacobian/Genus0BaseObjects.lean:91-95` — `algebraKbarAway` instance: `algebraMap kbar (Away 𝒜 f) = (fromZeroRingHom 𝒜 _) ∘ (algebraMap kbar (𝒜 0))`.
- `AlgebraicJacobian/Genus0BaseObjects.lean:110-114` — `PLB.hom = Proj.toSpecZero 𝒜 ≫ Spec.map (algebraMap kbar (𝒜 0))`.
- `AlgebraicJacobian/Genus0BaseObjects.lean:707-709` — `Gm.hom = Spec.map (CommRingCat.ofHom (algebraMap kbar (GmRing kbar)))` (def-equal — instance body).
- `AlgebraicJacobian/Genus0BaseObjects.lean:207-253` — `projectiveLineBarAffineCover kbar` built via `Proj.affineOpenCoverOfIrrelevantLESpan` on `![X 0, X 1]`; so `(projectiveLineBarAffineCover kbar).openCover.f i = Proj.awayι 𝒜 (X i) _ _`.
- `AlgebraicJacobian/Genus0BaseObjects.lean:823-826` — `gmScalingP1_cover := (projectiveLineBarAffineCover kbar).openCover.pullback₁ (pullback.fst PLB.hom Gm.hom)`. By `PreZeroHypercover.pullback₁` (`Mathlib/CategoryTheory/Sites/Hypercover/Zero.lean:97-101`), `X i := pullback f (E.f i)` and `f := pullback.fst _ _`.
- `AlgebraicJacobian/Genus0BaseObjects.lean:545-553` — `homogeneousLocalizationAwayIso : Away 𝒜 (X i) ≃+* MvPolynomial Unit kbar`, axiom-clean as of iter-172.
- `AlgebraicJacobian/Genus0BaseObjects.lean:845-847` — `gmScalingP1_chart kbar i : (gmScalingP1_cover kbar).X i ⟶ ProjectiveLineBarScheme kbar`, body = `sorry` (iter-172 leave-behind).

## Decisions identified

### Decision 1: Is there a canonical Mathlib iso `pullback (Spec.map f) (Spec.map g) ≅ Spec (A ⊗[R] B)`?

- **Mathlib idiom**: YES.
  ```lean
  noncomputable
  def pullbackSpecIso (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra R T] :
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅ Spec (.of <| S ⊗[R] T)
  ```
  Cite: `Mathlib.AlgebraicGeometry.Pullbacks.lean:702-708`.
  
  Orientation: `pullback … ≅ Spec …` (NOT the symmetric flipped form). API: `Algebra R S` and `Algebra R T` (so the `Spec.map`'s are of the *algebra maps*, not raw `RingHom`s). The companion lemmas exist in both `_inv_fst` / `_hom_fst` flavours (lines 716-769), so both directions are usable.
- **Project's current path**: the iter-172 prover blocked here because they were trying to use `pullbackSpecIso` directly on the abstract `pullback (pullback.fst PLB.hom Gm.hom) (Proj.awayι …)` shape, which does NOT match — `Proj.awayι` is not a `Spec.map (algebraMap …)`, and `pullback.fst PLB.hom Gm.hom` is itself a pullback projection. The prover correctly identified that *additional* pullback algebra is needed before `pullbackSpecIso` applies.
- **Gap**: identical (Mathlib has THE iso; project just needs to expose the right shape).
- **Cost of divergence**: n/a.
- **Verdict**: **PROCEED** — use `pullbackSpecIso` as the terminal step of a small composite iso.

### Decision 2: How to bridge from `pullback (pullback.fst PLB.hom Gm.hom) (Proj.awayι …)` to a pullback of two `Spec.map`s of the structure morphisms?

- **Mathlib idiom**: assemble three Mathlib isos sequentially. There is **no single direct lemma** for this iterated shape, but there is a *near-exact precedent*:

  ```lean
  -- Mathlib.AlgebraicGeometry.Cover.Open.lean:160-166
  def OpenCover.pullbackCoverAffineRefinementObjIso (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
      (𝒰.affineRefinement.openCover.pullback₁ f).X i ≅
        ((𝒰.X i.1).affineCover.pullback₁ (𝒰.pullbackHom f i.1)).X i.2 :=
    pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso _ _ _).symm ≪≫
      pullbackSymmetry _ _ ≪≫ asIso (pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _)
        (by simp [Cover.pullbackHom]) (by simp))
  ```
  
  This is Mathlib's archetype for transforming `OpenCover.pullback₁ f`-style covers via the pullback-pasting algebra: **`pullbackSymmetry` + `pullbackRightPullbackFstIso`**, exactly the same building blocks needed here.

  The two operative lemmas:
  
  - `pullbackSymmetry : pullback f g ≅ pullback g f`
    Cite: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback.lean:494-496`.
  
  - `pullbackRightPullbackFstIso : pullback f' (pullback.fst f g) ≅ pullback (f' ≫ f) g`
    Cite: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting.lean:451-456`.

- **Project's current path**: the prover stubbed `gmScalingP1_chart` as a bare `sorry`. No bridge lemma exists yet.
- **Gap**: divergent-equivalent — Mathlib has every necessary building block (`pullbackSymmetry`, `pullbackRightPullbackFstIso`, `pullbackSpecIso`, `Proj.awayι_toSpecZero`), but **no single-lemma form of the composite**. The project must build an `~30 LOC` in-project bridge lemma that assembles these.
- **Cost of building it**: none beyond the bridge lemma itself. The four ingredients compose definitionally.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** in the weak sense — Mathlib has the parts but not this assembly. Project builds a *named, reusable* bridge lemma (signature below).

### Decision 3: Identifying `Proj.awayι ≫ PLB.hom` with `Spec.map (algebraMap kbar (Away 𝒜 X_i))`.

- **Mathlib idiom**:
  ```lean
  -- Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic.lean:209-219
  lemma awayι_toSpecZero : awayι 𝒜 f f_deg hm ≫ toSpecZero 𝒜 =
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))
  ```
  Combined with `HomogeneousLocalization.algebraMap_eq` (`Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization.lean:512`):
  ```lean
  algebraMap (𝒜 0) (HomogeneousLocalization 𝒜 x) = fromZeroRingHom 𝒜 x
  ```
  and the project's `algebraKbarAway = Algebra.compHom _ (algebraMap kbar (𝒜 0))` (i.e. `algebraMap kbar (Away 𝒜 X_i) = (algebraMap (𝒜 0) (Away 𝒜 X_i)) ∘ (algebraMap kbar (𝒜 0))`):
  
  ```
  Proj.awayι ≫ PLB.hom 
    = Proj.awayι ≫ (Proj.toSpecZero ≫ Spec.map (algebraMap kbar (𝒜 0)))
    = (Proj.awayι ≫ Proj.toSpecZero) ≫ Spec.map (algebraMap kbar (𝒜 0))
    = Spec.map (fromZeroRingHom 𝒜 _) ≫ Spec.map (algebraMap kbar (𝒜 0))
    = Spec.map ((algebraMap kbar (𝒜 0)) ≫ fromZeroRingHom 𝒜 _)
    = Spec.map (algebraMap kbar (Away 𝒜 X_i))    -- via algebraKbarAway + algebraMap_eq
  ```
- **Gap**: identical (project's `algebraKbarAway` already aligns with Mathlib's `compHom` idiom).
- **Verdict**: **PROCEED**.

### Decision 4 (counter-design check): Is the project's `Scheme.OpenCover.pullback₁`-encoding the right Mathlib path?

- **Mathlib idiom**: YES — `OpenCover.pullback₁` is the standard Mathlib idiom for "pull a cover back along a morphism". `Mathlib.AlgebraicGeometry.Cover.Open.lean:160-180` and `Mathlib.AlgebraicGeometry.Cover.MorphismProperty.lean` both consume this exact shape. There's no cleaner alternative (e.g. `pullbackCoverOfLeft` exists but lands at the same `pullback₁` after `pullbackCoverOfLeftIsoPullback₁`, `Mathlib.CategoryTheory.Sites.Hypercover.Zero.lean:482-486`).
- **Project's current path**: matches.
- **Verdict**: **PROCEED** — no alternative encoding to migrate to.

## Verdicts (summary)

| Decision | Verdict | Severity |
|---|---|---|
| (1) `pullbackSpecIso` is the right tensor-pullback iso | PROCEED | informational |
| (2) Need a 30-LOC in-project bridge lemma assembling 3 Mathlib idioms | NEEDS_MATHLIB_GAP_FILL (weak) | informational |
| (3) `Proj.awayι ≫ PLB.hom = Spec.map (algebraMap kbar (Away 𝒜 X_i))` is a definitional chain | PROCEED | informational |
| (4) `OpenCover.pullback₁` is the right encoding | PROCEED | informational |

## Recommendation

The right strategy is **NOT** to refactor anything in the project, but to **build one named bridge lemma** assembling `pullbackSymmetry` + `pullbackRightPullbackFstIso` + a small `Proj.awayι ≫ PLB.hom`-rewrite + `pullbackSpecIso`. The bridge is a faithful Mathlib-style assembly (the precedent is `OpenCover.pullbackCoverAffineRefinementObjIso` at `Cover/Open.lean:160-166`), and once landed it makes `gmScalingP1_chart` a direct `Iso.inv ≫ Spec.map gmScalingP1_chart_i_ringMap ≫ Spec.map homogeneousLocalizationAwayIso.symm ≫ Proj.awayι` composition.

### Bridge recipe (concrete)

Place the following two declarations in `AlgebraicJacobian/Genus0BaseObjects.lean` *between* the `homogeneousLocalizationAwayIso` block (~L555) and the `(D) gmScalingP1` section (~L783). They are reusable beyond `gmScalingP1_chart` (any chart-side map on `(PLB ⊗ Gm).left` benefits).

**Sub-lemma (a) — the `Proj.awayι ≫ PLB.hom` collapse**:

```lean
/-- The composition `Proj.awayι 𝒜 (X i) _ _ ≫ PLB.hom` collapses to the structural
`Spec.map (algebraMap kbar (Away 𝒜 (X i)))`. Pure rewrite: `awayι_toSpecZero` +
`Spec.map_comp` + `algebraKbarAway` chain. -/
private lemma awayι_comp_PLB_hom (kbar : Type u) [Field kbar] (i : Fin 2) :
    Proj.awayι (projectiveLineBarGrading kbar)
        (MvPolynomial.X i : MvPolynomial (Fin 2) kbar)
        (MvPolynomial.isHomogeneous_X kbar i) Nat.one_pos ≫
      (ProjectiveLineBar kbar).hom =
    Spec.map (CommRingCat.ofHom (algebraMap kbar
      (HomogeneousLocalization.Away (projectiveLineBarGrading kbar)
        (MvPolynomial.X i : MvPolynomial (Fin 2) kbar))))
```

Proof sketch (~5-8 LOC):
```
change Proj.awayι _ _ _ _ ≫ Proj.toSpecZero _ ≫ Spec.map _ = _
rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
congr 1
ext r          -- reduce to RingHom equality
rfl            -- by algebraKbarAway = Algebra.compHom, plus algebraMap_eq
```
(The last `rfl` rests on `algebraMap kbar (Away …) = fromZeroRingHom _ _ ∘ algebraMap kbar (𝒜 0)`, which is the `algebraKbarAway` defeq.)

**Sub-lemma (b) — the chart-source iso (the bridge proper)**:

```lean
/-- The chart-`i` source of `gmScalingP1_cover` is canonically isomorphic to
`Spec ((Away 𝒜 X_i) ⊗[kbar] GmRing kbar)`. Built by composing `pullbackSymmetry`,
`pullbackRightPullbackFstIso`, the `awayι_comp_PLB_hom` rewrite, and `pullbackSpecIso`. -/
noncomputable def gmScalingP1_cover_X_iso (kbar : Type u) [Field kbar] (i : Fin 2) :
    (gmScalingP1_cover kbar).X i ≅
      Spec (CommRingCat.of (
        TensorProduct kbar
          (HomogeneousLocalization.Away (projectiveLineBarGrading kbar)
            (MvPolynomial.X i : MvPolynomial (Fin 2) kbar))
          (GmRing kbar)))
```

Proof sketch (~10-15 LOC, mirroring `OpenCover.pullbackCoverAffineRefinementObjIso`):
```
refine pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso _ _ _ ≪≫ ?_
-- now goal: pullback (Proj.awayι ≫ PLB.hom) Gm.hom ≅ Spec (.of (A ⊗[kbar] B))
refine (pullback.congrHom (awayι_comp_PLB_hom kbar i) rfl).trans ?_
-- now goal: pullback (Spec.map (algebraMap kbar A)) Gm.hom ≅ Spec (.of (A ⊗[kbar] B))
-- Gm.hom is DEFEQ to Spec.map (CommRingCat.ofHom (algebraMap kbar (GmRing kbar))).
exact pullbackSpecIso kbar
  (HomogeneousLocalization.Away (projectiveLineBarGrading kbar)
    (MvPolynomial.X i : MvPolynomial (Fin 2) kbar))
  (GmRing kbar)
```

(If `pullback.congrHom` does not exist verbatim, the same effect is `pullback.map _ _ _ _ (eqToHom rfl ≫ _) (𝟙 _) (𝟙 _)` plus a one-line `pullback.hom_ext` argument — Mathlib uses this idiom freely; see `Cover/Open.lean:163-166`. Or simply `eqToIso` after `change`.)

### iter-173 prover's concrete next step

In `Genus0BaseObjects.lean`:

1. **Land `awayι_comp_PLB_hom` and `gmScalingP1_cover_X_iso`** (the two declarations above) immediately before the `(D) gmScalingP1` section header (~L783).

2. **Replace the body of `gmScalingP1_chart` (L845-847)** with the composite:
   ```lean
   noncomputable def gmScalingP1_chart (kbar : Type u) [Field kbar] (i : Fin 2) :
       (gmScalingP1_cover kbar).X i ⟶ ProjectiveLineBarScheme kbar :=
     (gmScalingP1_cover_X_iso kbar i).hom ≫
       Spec.map (CommRingCat.ofHom <|
         match i with
         | 0 => gmScalingP1_chart0_ringMap kbar
         | 1 => gmScalingP1_chart1_ringMap kbar) ≫
       Spec.map (CommRingCat.ofHom (homogeneousLocalizationAwayIso kbar i).symm.toRingHom) ≫
       Proj.awayι (projectiveLineBarGrading kbar)
         (MvPolynomial.X i : MvPolynomial (Fin 2) kbar)
         (MvPolynomial.isHomogeneous_X kbar i) Nat.one_pos
   ```
   (Note: the `gmScalingP1_chart{0,1}_ringMap` have codomain `TensorProduct kbar (MvPolynomial Unit kbar) (GmRing kbar)` while the bridge lands at `Spec (… (Away 𝒜 (X i)) ⊗[kbar] GmRing kbar)`. So order matters: apply the **inverse** of `homogeneousLocalizationAwayIso ⊗ id` first, *then* the `chart_i_ringMap`. The match-on-`i` is because `chart0` and `chart1` differ by `λ` vs `λ⁻¹`. If a unified `chartι_ringMap` with `Fin 2` parameter is preferred, the prover should refactor `gmScalingP1_chart{0,1}_ringMap` into one declaration.)

3. **Sanity-check defeq with `lean_multi_attempt`** for the `Gm.hom = Spec.map (algebraMap kbar (GmRing kbar))` step. The project's `gmScheme_canOver` instance (L707-709) sets `hom := Spec.map (CommRingCat.ofHom (algebraMap kbar (GmRing kbar)))`, so this should be `rfl`. If it isn't, the prover inserts a single `show` step.

### Size estimate

- `awayι_comp_PLB_hom`: ~8 LOC.
- `gmScalingP1_cover_X_iso`: ~12 LOC.
- `gmScalingP1_chart` body refactor: ~10 LOC.

**Total: ~30 LOC. Within the directive's ≤30 LOC ceiling for the bridge lemma.** No splitting into sub-lemmas is required beyond the (a)/(b) decomposition already proposed.

### What did NOT need to change

- `pullback₁` encoding (PROCEED).
- `homogeneousLocalizationAwayIso` (already axiom-clean, ready to consume).
- `algebraKbarAway`, `kbarToAwayRingHom` instances (defeq-aligned).
- `gmScalingP1_chart0_ringMap` / `gmScalingP1_chart1_ringMap` (axiom-clean ring maps; the bridge just supplies the source-side iso for them).
