# Analogy: intersection-ring identification for the `gmScalingP1_cover` cross01 cocycle and `iotaGm_range_isOpen`

## Mode
api-alignment

## Slug
intersection-ring-cross01

## Iteration
182

## Question

Joint consult covering two routes blocked on the SAME upstream gap: the
`Away 𝒜 (X 0 * X 1)` intersection-ring identification for
`ProjectiveLineBar kbar = Proj ⟨k̄[X 0, X 1]⟩`.

1. **Route 1** — `GmScaling.lean` `gmScalingP1_chart_agreement_cross01` (L295).
2. **Route 3** — `AbelianVarietyRigidity.lean` `iotaGm_range_isOpen` (L98).

## Project artifact(s)

- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:295-308` — cross01 cocycle
  helper.
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:106-110` — `gmScalingP1_cover`
  via `pullback₁`.
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:124-141` — `gmScalingP1_cover_X_iso`
  (the per-chart iso to `Spec (Away 𝒜 (X i) ⊗ GmRing)`).
- `AlgebraicJacobian/AbelianVarietyRigidity.lean:98-106` — `iotaGm_range_isOpen`.
- `AlgebraicJacobian/Genus0BaseObjects/Points.lean:86-134` — `pointOfVec` and
  `zeroPt`/`onePt`/`inftyPt` (via `Proj.fromOfGlobalSections`).

## Decisions identified

### Decision 1: `HomogeneousLocalization.Away.isLocalization_mul` is in Mathlib and is the right idiom

- **Mathlib idiom**: `HomogeneousLocalization.Away.isLocalization_mul`
  (`.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:883`)
  packages: for `f ∈ 𝒜 d` (d ≠ 0) and `g ∈ 𝒜 e` and `x = f * g`,
  `Away 𝒜 x` is the localization of `Away 𝒜 f` at the image
  `Away.isLocalizationElem hf hg = g^d / f^e ∈ Away 𝒜 f` (L877).
- **Project's current path**: the iter-181 Lane B task_result correctly
  identified this lemma (lines 67–68 of the report) but treated it as a
  stand-alone Mathlib bridge to be threaded by hand.
- **Gap**: identical (the algebraic content is shipped).
- **Verdict**: **PROCEED** with `Away.isLocalization_mul`. No project
  helper is needed at the ring level — Decision 2 supersedes the ring
  step entirely.

### Decision 2 (the load-bearing one): Mathlib ALREADY ships the Spec-level intersection iso `Proj.pullbackAwayιIso`

- **Mathlib idiom**: `AlgebraicGeometry.Proj.pullbackAwayιIso`
  (`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:258-265`)
  is verbatim:

  ```lean
  noncomputable
  def pullbackAwayιIso :
      Limits.pullback (awayι 𝒜 f f_deg hm) (awayι 𝒜 g g_deg hm') ≅
        Spec (.of <| Away 𝒜 x) :=  -- where hx : x = f * g
    IsOpenImmersion.isoOfRangeEq ...
  ```

  Companion `reassoc (attr := simp)` lemmas (L268-302):
  - `pullbackAwayιIso_hom_awayι` (L268): `iso.hom ≫ awayι 𝒜 x _ _ =
    pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm`.
  - `pullbackAwayιIso_hom_SpecMap_awayMap_left` (L275): `iso.hom ≫
    Spec.map (ofHom (awayMap 𝒜 g_deg hx)) = pullback.fst _ _`.
  - `pullbackAwayιIso_hom_SpecMap_awayMap_right` (L282): `iso.hom ≫
    Spec.map (ofHom (awayMap 𝒜 f_deg ...)) = pullback.snd _ _`.
  - `pullbackAwayιIso_inv_fst` / `pullbackAwayιIso_inv_snd` (L291-301):
    the inverse projections in terms of `Spec.map (awayMap ...)`.

  Hover-verified end-to-end at iter-182 via `lean_run_code` (signatures
  reproduce identically; instances all resolve).

- **Project's current path**: iter-181 Lane B task_result claimed
  "the bridge `pullback ((cover).f 0) ((cover).f 1) ≅ Spec (...)` is not
  packaged in Mathlib as a single lemma" (report line 64). This is
  **incorrect at the inner pullback level** — Mathlib ships the iso
  `pullback (awayι X_0) (awayι X_1) ≅ Spec (Away 𝒜 (X 0 * X 1))` plus
  three `simp` lemmas that pin every projection. The project's missing
  step is the **pasting** that pushes this inner iso through the
  pullback over `(ℙ¹ ⊗ Gm).left = pullback PLB.hom Gm.hom`.

- **Gap**: divergent-with-cost (one iter of investigative dead-end
  attempts on `cancel_mono` / `unfold + simp` because the project
  treated the Mathlib gap as deeper than it is).

- **Cost of divergence (if any)**: the iter-181 task_result's "iter-182+
  estimate ~70-115 LOC" included ~25-40 LOC for "build the intersection
  ring iso explicitly" — that line is wasted work. Mathlib already
  ships the Spec-level iso AND the ring-level iso (via `awayMap`).

- **Verdict**: **ALIGN_WITH_MATHLIB** — discard the "build a project-side
  `Away_X0_X1_iso : Away 𝒜 (X 0 · X 1) ≃+* Localization.Away (chart-1 affine coord)`"
  plan from the iter-181 task_result step 1. Use `Proj.pullbackAwayιIso`
  + companion `simp` lemmas directly. No new project helper is needed
  at the inner ring level.

### Decision 3: Pasting from inner to outer pullback uses generic Mathlib limit-pasting

- **Setup**: the cover `gmScalingP1_cover = (projectiveLineBarAffineCover).openCover.pullback₁ q`
  where `q := pullback.fst PLB.hom Gm.hom : (ℙ¹⊗Gm).left ⟶ PLB.left`. By
  `PreZeroHypercover.pullback₁_X` / `_f` (`Mathlib.CategoryTheory.Sites.Hypercover.Zero:97-101`),
  - `(cover).X i = pullback q (awayι 𝒜 (![X 0, X 1] i) _ _)`
  - `(cover).f i = pullback.fst q (awayι 𝒜 (![X 0, X 1] i) _ _)`

- **Goal**: `pullback ((cover).f 0) ((cover).f 1) ≅ Spec ((Away 𝒜 (X 0 * X 1)) ⊗[kbar] GmRing kbar)`.

- **Pasting strategy** (Mathlib already ships everything):
  1. `pullback (pullback.fst q A) (pullback.fst q B) ≅ pullback q (pullback A B)`
     via two `pullbackRightPullbackFstIso`s + `pullback.congrHom` on
     `pullback (q ≫ φ) ψ = ...` (use the Mathlib analogue of the project's
     `gmScalingP1_cover_X_iso` recipe, applied symmetrically).
  2. The inner `pullback (awayι X_0) (awayι X_1) ≅ Spec (Away 𝒜 (X 0 * X 1))`
     via `Proj.pullbackAwayιIso` (Decision 2).
  3. The outer `pullback q (awayι 𝒜 (X 0 * X 1)) ≅
     Spec (Away 𝒜 (X 0 * X 1) ⊗[kbar] GmRing)` — uniform-in-`i`
     version of the existing `gmScalingP1_cover_X_iso`, applied with
     `f := X 0 * X 1 ∈ 𝒜 2` (degree `m = 2`, witnessed by
     `MvPolynomial.IsHomogeneous.mul` of the two `isHomogeneous_X`).

  Steps 1 and 3 mirror the existing project recipe; step 2 is one
  Mathlib lemma application. **No new project helper is needed at
  the inner ring level**; only an outer "intersection cover X iso"
  (mirror of `gmScalingP1_cover_X_iso` at the X 0 * X 1 chart).

- **Verdict**: **BUILD_PROJECT_HELPER** for the *outer* iso
  `gmScalingP1_cover_intersection_X_iso : pullback ((cover).f 0) ((cover).f 1)
    ≅ Spec ((Away 𝒜 (X 0 * X 1)) ⊗[kbar] GmRing kbar)`. ~50-60 LOC; the
  body is one chain of `≪≫` Mathlib isos.

### Decision 4: chart-1 section for `iotaGm_range_isOpen` — `pullback.lift` over `pointOfVec`'s factorization through `awayι X_1`

- **Mathlib idiom**: `Over.lift_left`
  (`.lake/packages/mathlib/Mathlib/CategoryTheory/LocallyCartesianClosed/Over.lean:130-131`):
  `(CartesianMonoidalCategory.lift f g).left = pullback.lift f.left g.left _`.
  Combined with `pullback.lift_fst` / `pullback.lift_snd`, this expresses
  `(lift (toUnit ≫ onePt) (𝟙 Gm)).left` as the pullback-universal-property
  morphism into `pullback PLB.hom Gm.hom = (ℙ¹⊗Gm).left`.

- **Section into chart-1 of cover**: `ProjectiveLineBar.onePt = pointOfVec
  kbar (fun _ => 1) 0 _`. `pointOfVec` is `Over.homMk
  (Proj.fromOfGlobalSections (projectiveLineBarGrading kbar)
  (evalIntoGlobal kbar v) ...)`. The `Proj.fromOfGlobalSections`
  morphism factors through ANY chart of `Proj 𝒜` where the corresponding
  generator is mapped to a unit — for `onePt` with `v 0 = v 1 = 1`, BOTH
  `X_0 ↦ 1` and `X_1 ↦ 1` are units, so `onePt.left` factors through
  `awayι 𝒜 (X 1) _ _` via a section `r_1 : Spec k̄ ⟶ Spec(Away 𝒜 (X 1))`
  (= `Spec.map` of the chart-1 ring's eval-at-1 map). The Mathlib
  factorization lemma is `Proj.fromOfGlobalSections_morphismRestrict`
  (cited by the iter-168 `gmscaling-deep.md` analogist).

- **Section formula**:
  ```
  s : Gm.left ⟶ (cover).X 1 = pullback q (awayι X_1)
  s := pullback.lift ((toUnit Gm ≫ onePt).left ≫ r_1.inv) (𝟙 Gm.left ≫ Gm.hom...) _
       -- actually: pullback.lift (Gm.left ⟶ Spec(Away X_1)) (Gm.left ⟶ Gm.left)
       --   with compatibility coming from the over-structure
  ```

  Concretely: extract `r_1 := Spec.map (ofHom (the eval map Away 𝒜 (X 1) → k̄))`
  via `Proj.fromOfGlobalSections_morphismRestrict` on the chart-1 basic open,
  then `pullback.lift (toUnit_Gm ≫ r_1) (𝟙 Gm.left) (pullback compatibility)`.

- **Open-immersion argument**: with `s` in hand,
  `s ≫ (cover).f 1 ≫ gmScalingP1.left = (lift _ _ ≫ gmScalingP1).left`
  by `Cover.ι_glueMorphisms` and unfolding of `gmScalingP1 = Over.homMk
  (cover.glueMorphisms gmScalingP1_chart _)`. The composite
  `s ≫ gmScalingP1_chart 1` is the chart-1 morphism `(cover).X 1 ⟶
  ProjectiveLineBarScheme` precomposed with the section `s`. By
  unfolding `gmScalingP1_chart 1` (L156–175) and using
  `Proj.awayι` being an `IsOpenImmersion` instance
  (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic:196`), the
  composite is the open immersion `Gm = Spec k̄[t, t⁻¹] ↪ ℙ¹` mapping
  `λ ↦ [λ : 1]`. `IsOpenImmersion.isOpen_range` closes the helper.

- **Gap**: BUILD_PROJECT_HELPER (no single Mathlib lemma exposes the
  section formula generically; this is a project-specific computation).
- **Verdict**: **BUILD_PROJECT_HELPER** for the chart-1 section `s`.

## Mathlib API citations (verified at iter-182)

All paths are inside `.lake/packages/mathlib/Mathlib/` and line numbers
match the project's pinned `lake-manifest.json` commit:

- `Proj.pullbackAwayιIso`
  — `AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:258-265`
- `Proj.pullbackAwayιIso_hom_awayι` — same file `:268-272`
- `Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left` — same file `:275-279`
- `Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right` — same file `:282-289`
- `Proj.pullbackAwayιIso_inv_fst` / `_inv_snd` — same file `:291-301`
- `Proj.awayι_preimage_basicOpen` — same file `:303-318`
- `Proj.SpecMap_awayMap_awayι` — same file `:251-255` (the key reassoc
  lemma collapsing `awayMap` followed by `awayι` to the product
  `awayι 𝒜 x`)
- `HomogeneousLocalization.Away.isLocalization_mul`
  — `RingTheory/GradedAlgebra/HomogeneousLocalization.lean:883-931`
- `HomogeneousLocalization.Away.isLocalizationElem` — same file `:877`
- `HomogeneousLocalization.awayMap` — same file `:820`
- `Over.lift_left` (the `Over (Spec k̄)`-monoidal `lift` extraction)
  — `CategoryTheory/LocallyCartesianClosed/Over.lean:130-131`
- `Over.tensorObj_left` — same file `:109-110`
- `Over.tensorObj_hom` — same file `:112-113`
- `PreZeroHypercover.pullback₁` — `CategoryTheory/Sites/Hypercover/Zero.lean:97-101`
- `Scheme.Cover.pullback₁` (the AG-side wrapper) and its `pullback₁_X` /
  `pullback₁_f` simp lemmas — `AlgebraicGeometry/Cover/MorphismProperty.lean:177`
  and (via reindexing) the bridge lemma in `Cover/Open.lean:160-180`
- `Scheme.Cover.glueMorphisms`, `Cover.ι_glueMorphisms`,
  `Cover.hom_ext` — `AlgebraicGeometry/Gluing.lean:436-457`
- `Proj.fromOfGlobalSections_morphismRestrict` (chart factorization of
  `pointOfVec`'s underlying scheme map)
  — `AlgebraicGeometry/ProjectiveSpectrum/Basic.lean` ~L493 (per
  `analogies/gmscaling-deep.md` iter-168 lookup; verified present at
  iter-182 via local search).

## Estimated LOC

| Sub-task | LOC | Mathlib idiom drives most of it? |
|---|---|---|
| `gmScalingP1_cover_intersection_X_iso` helper | 50–60 | YES (pasting iso chain) |
| `gmScalingP1_chart_agreement_cross01` body | 30–45 | YES (Spec.map + ring algebra) |
| `iotaGm_range_isOpen` body — section + open immersion | 45–60 | PARTIAL (section construction is project-side; open-immersion conclusion is Mathlib) |
| `gmScalingP1_collapse_at_zero` body (BONUS — same techniques) | 30–40 | YES (chart-1 ring map; `pullback.lift` factoring through `r_0`) |

**Total**: ~155–205 LOC across 3 (or 4 with the bonus) bodies. The
iter-181 task_result's 70–115 LOC estimate was too low because it
didn't budget the pasting iso step; on the other hand, the iter-181
"build intersection ring iso explicitly" line evaporates (Mathlib
ships it).

## Concrete recipes

### Recipe 1: `gmScalingP1_cover_intersection_X_iso` (the missing outer iso)

Target signature (verbatim):

```lean
private noncomputable def gmScalingP1_cover_intersection_X_iso
    (kbar : Type u) [Field kbar] :
    Limits.pullback ((gmScalingP1_cover kbar).f (0 : Fin 2))
        ((gmScalingP1_cover kbar).f (1 : Fin 2)) ≅
      Spec (CommRingCat.of
        (TensorProduct kbar
          (HomogeneousLocalization.Away (projectiveLineBarGrading kbar)
            ((MvPolynomial.X 0 : MvPolynomial (Fin 2) kbar) *
              MvPolynomial.X 1))
          (GmRing kbar))) := ...
```

Body skeleton (the prover replaces each `≪≫` with the verified Mathlib
iso; only the `Proj.pullbackAwayιIso` step is genuinely new):

```lean
  -- Step (a): pasting outer `pullback (pullback.fst _ _) (pullback.fst _ _)`
  --          into `pullback q (pullback awayι_0 awayι_1)`.
  --          Uses `pullbackRightPullbackFstIso` and `pullbackSymmetry`
  --          (mirror of `gmScalingP1_cover_X_iso`, applied twice).
  (Limits.pullbackSymmetry _ _) ≪≫
    Limits.pullbackRightPullbackFstIso _ _ _ ≪≫
    Limits.pullback.congrHom rfl rfl ≪≫
  -- Step (b): merge the two inner `awayι` projections via
  --          `Proj.pullbackAwayιIso` (the key Mathlib bridge).
  Limits.pullback.congrHom
    rfl  -- the LHS map matches up
    ((Proj.pullbackAwayιIso (projectiveLineBarGrading kbar)
        (projectiveLineBarAffineCover_fDeg kbar 0)
        (projectiveLineBarAffineCover_hm 0)
        (projectiveLineBarAffineCover_fDeg kbar 1)
        (projectiveLineBarAffineCover_hm 1)
        (rfl : (![MvPolynomial.X 0, MvPolynomial.X 1] : _) 0 *
               (![MvPolynomial.X 0, MvPolynomial.X 1] : _) 1 = _)).hom_awayι.symm) ≪≫
  -- Step (c): outer iso `pullback q (awayι 𝒜 (X 0 · X 1)) ≅
  --          Spec ((Away 𝒜 (X 0 · X 1)) ⊗ GmRing)` —
  --          mirror of `gmScalingP1_cover_X_iso` with the merged generator
  --          `X 0 · X 1` of degree 2.
  pullback.congrHom
    (awayι_comp_PLB_hom kbar (m := 2) (by norm_num)
      ((MvPolynomial.X 0 : MvPolynomial (Fin 2) kbar) * MvPolynomial.X 1)
      ((MvPolynomial.isHomogeneous_X kbar 0).mul
        (MvPolynomial.isHomogeneous_X kbar 1)))
    (show (Gm kbar).hom =
        Spec.map (CommRingCat.ofHom (algebraMap kbar (GmRing kbar))) from rfl) ≪≫
  pullbackSpecIso kbar _ (GmRing kbar)
```

(The `≪≫` chain is illustrative; the prover must thread the iso targets
to match `pullbackAwayιIso_hom_awayι` / `pullback.fst_congrHom` exactly.
The point is that **every step except the `pullbackAwayιIso` step is a
re-application of techniques already in `gmScalingP1_cover_X_iso`**.)

### Recipe 2: `gmScalingP1_chart_agreement_cross01` body

```lean
private lemma gmScalingP1_chart_agreement_cross01 (kbar : Type u) [Field kbar] :
    pullback.fst ((gmScalingP1_cover kbar).f (0 : Fin 2))
        ((gmScalingP1_cover kbar).f (1 : Fin 2)) ≫
      gmScalingP1_chart kbar (0 : Fin 2) =
    pullback.snd ((gmScalingP1_cover kbar).f (0 : Fin 2))
        ((gmScalingP1_cover kbar).f (1 : Fin 2)) ≫
      gmScalingP1_chart kbar (1 : Fin 2) := by
  -- Promote both sides to the intersection ring via the new iso.
  rw [← cancel_epi (gmScalingP1_cover_intersection_X_iso kbar).inv]
  -- Each side now is `iso.inv ≫ pullback.fst ≫ chart 0` (resp. snd ≫ chart 1).
  -- Use `pullbackAwayιIso_inv_fst` / `_inv_snd` (composed through the outer iso)
  -- to rewrite both sides into a single Spec.map of a ring map
  -- `Away 𝒜 (X 0) ⊗ GmRing →+* Away 𝒜 (X 0 · X 1) ⊗ GmRing` and
  -- `Away 𝒜 (X 1) ⊗ GmRing →+* Away 𝒜 (X 0 · X 1) ⊗ GmRing`.
  simp only [Iso.inv_hom_id_assoc, Proj.pullbackAwayιIso_inv_fst,
    Proj.pullbackAwayιIso_inv_snd, ...]
  -- Goal now: equality of two Spec.map's. Reduce to ring equality.
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  -- Ring-level identity: `chart 0`-side and `chart 1`-side ring maps
  -- agree on `Away 𝒜 (X 0 · X 1) ⊗ GmRing`. Via `MvPolynomial.algHom_ext`
  -- (after passing through `homogeneousLocalizationAwayIso`), reduce to
  -- evaluating on the chart-side generators `t = X 1 / X 0` (chart 0) /
  -- `u = X 0 / X 1` (chart 1). The compatibility `t · u = 1` in
  -- `Localization.Away (X 0 · X 1)` is `IsLocalization.Away.mul_invSelf`
  -- applied to the merged isLocalizationElem.
  ext  -- or `MvPolynomial.algHom_ext` + `MvPolynomial.eval₂Hom_X'`
  -- residual algebra: `t · u = 1` (chart-product) — close via
  -- `Algebra.TensorProduct.tmul_mul_tmul` + `IsLocalization.Away.mul_invSelf`.
  sorry  -- target: ~10 LOC
```

### Recipe 3: `iotaGm_range_isOpen` body

```lean
private lemma iotaGm_range_isOpen [IsAlgClosed kbar] :
    IsOpen (Set.range ⇑((lift (toUnit (Gm kbar) ≫ ProjectiveLineBar.onePt kbar)
        (𝟙 (Gm kbar))).left ≫ (gmScalingP1 kbar).left)) := by
  -- (a) `(lift _ _).left = pullback.lift (toUnit_Gm ≫ onePt).left (𝟙 Gm.left)
  --    (by Over-pullback compatibility)`, via `Over.lift_left`.
  rw [Over.lift_left]  -- or use the `set_option` trick if defeq is tricky
  -- (b) `onePt.left` factors through `awayι X_1` via `Proj.fromOfGlobalSections_morphismRestrict`.
  --    Extract the section `r_1 : Spec k̄ ⟶ Spec (Away 𝒜 (X 1))`.
  obtain ⟨r_1, h_r_1⟩ : ∃ r_1 : Spec (CommRingCat.of kbar) ⟶
      Spec (CommRingCat.of (HomogeneousLocalization.Away
        (projectiveLineBarGrading kbar) (MvPolynomial.X 1))),
      (ProjectiveLineBar.onePt kbar).left =
        r_1 ≫ Proj.awayι (projectiveLineBarGrading kbar)
          (MvPolynomial.X 1) (MvPolynomial.isHomogeneous_X kbar 1) Nat.one_pos := by
    -- Use `Proj.fromOfGlobalSections_morphismRestrict` on the chart-1 basic open
    -- and the fact that `evalIntoGlobal kbar (fun _ => 1)` maps `X_1 ↦ 1`
    -- which is a unit (so the morphism restricts to the chart).
    sorry  -- ~15 LOC; chart factorization via Mathlib's chart-restriction lemma
  -- (c) Build the section `s : Gm.left ⟶ (cover).X 1` via `pullback.lift`.
  --    `(cover).X 1 = pullback q (awayι X_1)` with `q = pullback.fst PLB.hom Gm.hom`.
  --    The Gm.left-side map is `toUnit_Gm ≫ r_1`; the Gm.hom-side is `𝟙 Gm.left`.
  set s : (Gm kbar).left ⟶ (gmScalingP1_cover kbar).X 1 := pullback.lift
    (pullback.lift ((Gm kbar).hom ≫ ... -- the PLB-side factor: factors through r_1)
      (𝟙 (Gm kbar).left) (...) )
    (𝟙 (Gm kbar).left)
    (...) with hs_def
  -- (d) `s ≫ (cover).f 1 = (lift (toUnit ≫ onePt) (𝟙 Gm)).left` — pullback unique-lift.
  have hs_fact : s ≫ (gmScalingP1_cover kbar).f 1 =
      (lift (toUnit (Gm kbar) ≫ ProjectiveLineBar.onePt kbar)
        (𝟙 (Gm kbar))).left := by
    -- unfold `s`, apply `pullback.lift_fst`, then `Over.lift_left` rev.
    sorry  -- ~5 LOC
  -- (e) Compose with `gmScalingP1.left = (cover).glueMorphisms gmScalingP1_chart _`.
  --    `Cover.ι_glueMorphisms` gives `(cover).f 1 ≫ glueMorphisms ... = gmScalingP1_chart 1`.
  rw [← hs_fact, Category.assoc]
  change IsOpen (Set.range ⇑(s ≫ (gmScalingP1_cover kbar).f 1 ≫ (gmScalingP1 kbar).left))
  change IsOpen (Set.range ⇑(s ≫ Scheme.Cover.ι_glueMorphisms ... -- unfold to gmScalingP1_chart 1
  rw [Scheme.Cover.ι_glueMorphisms (gmScalingP1_cover kbar) _ _ 1]
  -- (f) `s ≫ gmScalingP1_chart 1` is an `IsOpenImmersion`:
  --     the chart map factors as `s ≫ iso.hom ≫ Spec.map (ring map) ≫ Proj.awayι X_1`.
  --     `Proj.awayι X_1` is open-immersion (Mathlib instance); `Spec.map (ring map)` is
  --     open immersion iff the ring map exhibits a localization. For the chart-1 ring map
  --     `u ↦ u ⊗ λ` precomposed with `r_1` (eval-at-1 ⊗ id ≅ Spec.map (Gm structure)),
  --     this composite IS an open immersion (essentially the standard Gm ↪ 𝔸¹ ↪ ℙ¹).
  exact IsOpenImmersion.isOpen_range _
```

## Verification (lean_run_code probe at iter-182)

```lean
-- Probe: confirm `Proj.pullbackAwayιIso` types as advertised.
example {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜]
    {m m' : ℕ} {f : A} (hf : f ∈ 𝒜 m) (hm : 0 < m)
    {g : A} (hg : g ∈ 𝒜 m') (hm' : 0 < m')
    {x : A} (hx : x = f * g) :
    Limits.pullback (Proj.awayι 𝒜 f hf hm) (Proj.awayι 𝒜 g hg hm') ≅
      Spec (.of <| HomogeneousLocalization.Away 𝒜 x) :=
  Proj.pullbackAwayιIso 𝒜 hf hm hg hm' hx
-- Result at iter-182: elaborates cleanly (the only non-trivial typeclass is
-- `SetLike σ A`, present at the cover's call site via `projectiveLineBarGrading`'s
-- standard ℕ-grading instances).
```

## Verdicts (summary)

| Decision | Verdict | Severity |
|---|---|---|
| (1) `HomogeneousLocalization.Away.isLocalization_mul` is the right ring-level idiom | PROCEED | informational |
| (2) `Proj.pullbackAwayιIso` IS shipped — discard "build intersection ring iso" plan | ALIGN_WITH_MATHLIB | critical |
| (3) Outer "intersection cover X iso" still needed; pasting via Mathlib idioms | BUILD_PROJECT_HELPER | informational |
| (4) Chart-1 section for `iotaGm_range_isOpen` — `pullback.lift` over `pointOfVec` factorization | BUILD_PROJECT_HELPER | informational |

## Recommendation

**The iter-181 Lane B task_result was over-pessimistic on the upstream
gap.** Mathlib already ships the Spec-level intersection iso
`Proj.pullbackAwayιIso` with three `simp`-lemma companions
(`pullbackAwayιIso_hom_awayι`, `pullbackAwayιIso_inv_fst`,
`pullbackAwayιIso_inv_snd`) that directly pin every projection. The
iter-182+ plan should:

1. **Drop step 1 of the iter-181 plan** ("build `Away_X0_X1_iso`"). It's
   gratuitous — `Proj.pullbackAwayιIso` IS the iso, packaged at the Spec
   level where it's needed.
2. **Keep step 2** ("build the source-side bridge `pullback ((cover).f 0) ((cover).f 1)
   ≅ Spec ((Away 𝒜 (X 0 · X 1)) ⊗[kbar] GmRing kbar)`"). This is the
   outer pasting iso that mirrors `gmScalingP1_cover_X_iso` with the
   merged generator `X 0 * X 1`. The key step inside the pasting chain
   is `Proj.pullbackAwayιIso` (no longer a sorry).
3. **For step 3** (the ring-level identity `λ · u = (1/t) · λ`), use
   `Proj.pullbackAwayιIso_inv_fst` / `_inv_snd` to push both sides of
   the cocycle through the intersection iso, then reduce to a
   `congrArg Spec.map` on the underlying ring-level equation. The
   residual algebra (`t · u = 1` in the merged Localization.Away) is
   `IsLocalization.Away.mul_invSelf` (≤5 LOC).
4. **For `iotaGm_range_isOpen`** (Route 3), use the same chart-1
   factorization machinery the iter-181 task_result correctly identified
   (`Proj.fromOfGlobalSections_morphismRestrict` + `pullback.lift` + the
   `Cover.ι_glueMorphisms` reduction). This is project-side
   `BUILD_PROJECT_HELPER` work but does NOT depend on the intersection
   ring — only on chart-1 of the cover.

**Bonus** (out of scope for iter-182's helper budget but ~30-40 LOC):
the same chart-1 factorization (via `r_0` instead of `r_1`, since
`zeroPt`'s `v 1 = 1` is the chart-1 generator) closes
`gmScalingP1_collapse_at_zero` (L420 of `GmScaling.lean`).

## What did NOT need to change

- `Proj.affineOpenCoverOfIrrelevantLESpan` choice — already canonical.
- `homogeneousLocalizationAwayIso` + `_algebraMap` — already axiom-clean
  iter-174 and reused in the new cross01 body recipe.
- `awayι_comp_PLB_hom` — already axiom-clean iter-173 and reusable
  uniform-in-`f` for the `X 0 * X 1` generator (degree 2 instance via
  `MvPolynomial.IsHomogeneous.mul`).
- `gmScalingP1_chart{0,1}_ringMap` — axiom-clean iter-167; consumed by
  the chart maps that the cross01 body unfolds in step (a) of Recipe 2.

## Reversal trigger

If the `gmScalingP1_cover_intersection_X_iso` body of Recipe 1 cannot
be made to type-check at the `pullback.congrHom`/`pullbackAwayιIso_hom_awayι`
step (the `Spec.map` of the merged generator and the merged `awayι`
endpoint must defeq-align), iter-183 falls back to **two separate
isos** — `pullback ((cover).f 0) ((cover).f 1) ≅ pullback q (awayι (X 0 * X 1))`
and `pullback q (awayι (X 0 * X 1)) ≅ Spec ((Away 𝒜 (X 0 * X 1)) ⊗ GmRing)`
— rather than fusing them into one chained iso. Same total LOC; less
risk of unification timeouts.
