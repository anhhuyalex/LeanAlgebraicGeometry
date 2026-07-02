# Analogy: bypassing the `pullbackSpecIso_hom_base` heartbeat sink in `gmScalingP1_chart_PLB_eq`

## Mode
api-alignment

## Slug
pullbackspeciso-bypass

## Iteration
180

## Question

Concrete options for bypassing the `Algebra.compHom`-based instance synthesis
heartbeat sink at the `pullbackSpecIso_hom_base` application site in
`AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean`. The chart-bridge body
recipe has been stuck for 5 iters (iter-175 through iter-179) at the 5th of
6 steps — the rewrite `pullbackSpecIso_hom_base` (Mathlib
`Pullbacks.lean:766`) silently refuses to match a verbatim-LHS goal, and
`erw` times out at 200k heartbeats doing `isDefEq` on a
`TensorProduct kbar (HomogeneousLocalization.Away _ _) (GmRing kbar)`
algebra instance whose Lean-elaborated form goes through
`Algebra.compHom` (the project's `algebraKbarAway`).

## Project artifact(s)

- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:213-250` — the body
  of `gmScalingP1_chart_PLB_eq` with the iter-179 partial recipe and the
  sticky 5th-step `sorry`.
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:124-141` — the
  `gmScalingP1_cover_X_iso` definition (iter-179 uniform-in-`i` refactor).
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:54-64` — the
  `awayι_comp_PLB_hom` helper (axiom-clean since iter-173).
- `AlgebraicJacobian/Genus0BaseObjects/BareScheme.lean:59-63` —
  `algebraKbarAway` instance (the `Algebra.compHom`-typed one diagnosed
  as the heartbeat sink contributor).
- `Mathlib/AlgebraicGeometry/Pullbacks.lean:766-769` — the canonical
  `pullbackSpecIso_hom_base` lemma whose pattern won't match.
- `Mathlib/RingTheory/TensorProduct/MvPolynomial.lean:176`,
  `Mathlib/AlgebraicGeometry/Normalization.lean` (multiple sites) —
  Mathlib's own use of the `set_option backward.isDefEq.respectTransparency
  false` workaround for similar algebra-instance defeq sinks.

## Decisions identified

### Decision 1: Project-side wrapper `pullbackSpecIso_hom_base'`

- **Mathlib idiom**: a wrapper that takes the algebra map as an explicit
  `RingHom` parameter is *buildable* — `pullbackSpecIso_hom_fst'` already
  exists in Mathlib (`Pullbacks.lean:750-752`) as a thin re-statement
  of `pullbackSpecIso_hom_fst` with the algebra map made explicit via
  `Spec.map (ofHom (algebraMap S _))`. The same shape would work for
  `_hom_base'`.
- **Buildability (sub-question 1a)**: YES — Mathlib's pullback API is
  flexible enough; the wrapper is ~6 LOC (analogous to
  `pullbackSpecIso_inv_fst'` / `_hom_fst'`).
- **Does it avoid the sink (sub-question 1b)**: NO — the wrapper's PROOF
  runs `simp [Algebra.TensorProduct.algebraMap_def]` (the same step that
  the existing `_hom_base` uses), which on the project side would re-trigger
  the same `Algebra kbar (S ⊗[R] T)` instance unification. The wrapper
  with an explicit `(φ : R →+* S ⊗[R] T)` parameter + an `hφ` equation
  would push the burden onto the call site: discharging `hφ` requires
  unifying the project's `Algebra.compHom`-based instance with
  `Algebra.TensorProduct.leftAlgebra`, which is exactly the original
  defeq sink. Net cost: SHIFTS the problem, doesn't eliminate it.
- **Gap**: divergent-and-wrong as a STANDALONE fix.
- **Cost of building it alone**: 6 LOC for the wrapper plus 3–5 LOC
  per call-site for the `hφ` discharge. Still hits the sink at the call
  site `change`/`rfl`.
- **Verdict**: **NOT_VIABLE** as a primary fix. Could be a SECONDARY
  layer if combined with Decision 4's option setting (which actually
  bypasses the sink).

### Decision 2: `pullback.mapIso` direct construction

- **Mathlib idiom**: `pullback.congrHom`
  (`Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:349`)
  is the canonical "1-layer" iso for `pullback f₁ g₁ ≅ pullback f₂ g₂`
  given `f₁ = f₂, g₁ = g₂`. It's defined as
  `asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _)`. There is no
  separate `pullback.mapIso` (the iso form of `pullback.map`).
- **The 4-layer chain in `gmScalingP1_cover_X_iso`**: deliberately uses
  `pullbackSymmetry` + `pullbackRightPullbackFstIso` + `pullback.congrHom`
  + `pullbackSpecIso` because each step does a DIFFERENT pullback-algebra
  transformation:
  - symmetry swaps L/R,
  - right-pullback-fst-iso collapses a nested pullback (the `pullback₁`
    refactor demands this),
  - congrHom installs the `awayι_comp_PLB_hom` rewrite,
  - pullbackSpecIso terminally lands at `Spec (⊗)`.
  None of these can be MERGED into a single `pullback.congrHom`
  application — they each act on different objects in the chain.
- **Project's current path**: uses the 4-layer chain. The project's
  iter-178 `gmscaling-cover-bridge` analogy already cites
  `OpenCover.pullbackCoverAffineRefinementObjIso`
  (`Mathlib.AlgebraicGeometry.Cover.Open:160-166`) as the EXACT Mathlib
  precedent for this same chain pattern — Mathlib's own pullback-cover
  refinement uses `pullbackSymmetry + pullbackRightPullbackFstIso +
  pullback.map`. So the project's 4-layer chain IS the Mathlib idiom.
- **Gap**: identical to Mathlib precedent.
- **Why `pullback.mapIso` (direct construction) wouldn't shorten this**:
  the algebra burden of identifying
  `(pullback PLB.hom Gm.hom).X i ≅ Spec (Away_i ⊗ GmRing)` is the WHOLE
  iso, not a single layer. Compressing all 4 transformations into a
  single `pullback.map` would require manually constructing the
  underlying morphism (= rebuilding the chain inline) — same total
  algebra, plus loss of the named intermediate steps that the iter-179
  `lean_multi_attempt` evidence shows ARE the right targets for
  `simp` rewrite chains.
- **Verdict**: **NOT_VIABLE** — no Mathlib lemma reduces the chain
  depth, and re-rolling the iso inline would multiply the unification
  burden, not reduce it. The current 4-layer chain IS Mathlib-aligned.

### Decision 3: Algebra-instance refactor (replace `Algebra.compHom`)

- **Mathlib idiom**: Mathlib provides `Algebra.compHom` as the canonical
  pattern for "compose two algebra maps to get a third algebra
  structure". When the project needs `Algebra kbar (Away 𝒜 f)` and only
  has Mathlib's `Algebra ↥(𝒜 0) (HomogeneousLocalization.Away 𝒜 f)`
  shipped, the ONLY way to lift to `Algebra kbar (Away)` is via
  `Algebra.compHom _ (algebraMap kbar (𝒜 0))` (or equivalent
  `IsScalarTower`-driven derivation, but `IsScalarTower kbar (𝒜 0) Away`
  STILL requires installing some `Algebra kbar Away`-shaped instance
  somewhere — the chain bottoms out the same way).
- **Project's current path**: `algebraKbarAway` = `Algebra.compHom`.
- **`Algebra.ofModule` / `Algebra.toAlgebraOfPushforward` /
  letting `TensorProduct.algebra` trigger naturally**: these don't apply
  here — `Algebra.ofModule` requires a `Module kbar Away` + multiplication
  compatibility (which would be DERIVED from an `Algebra` instance, not
  the other way around), `TensorProduct.algebra` is the OUTER instance
  (`Algebra R (A ⊗[R] B)`), it doesn't help with the INNER
  `Algebra kbar Away_i` problem.
- **Diagnostic from iter-180 lean_multi_attempt evidence**: the
  heartbeat sink is NOT primarily caused by `algebraKbarAway` as a path
  through `compHom`. A minimal repro using JUST the bare
  `pullbackSpecIso_hom_base` rewrite on a goal of the actual shape
  (`Spec.map (CommRingCat.ofHom (algebraMap kbar (TensorProduct kbar Away_i (GmRing kbar))))`)
  WORKS without any option setting (verified by `lean_run_code` —
  the goal compiles green when the LHS is at the TOP LEVEL of an
  isolated example). The sink fires only when the LHS is BURIED inside
  the 4-layer iso chain, where the iso's intermediate-object Algebra
  instances accumulate.
- **Refactor cost analysis (sub-question 3, "does anything else depend
  on compHom form")**:
  - `algebraKbarAway` is consumed by: `TensorProduct kbar (Away _ _) _`
    structure (every `gmScalingP1_chart{0,1}_ringMap`, every chart-bridge
    proof step, every `pullbackSpecIso kbar Away_i GmRing` invocation
    in `gmScalingP1_cover_X_iso`).
  - Changing it to a non-`compHom` form (e.g. inlining
    `(algebraMap (𝒜 0) Away).comp (algebraMap kbar (𝒜 0))` as a
    bare `RingHom`-defined instance) breaks the `inferInstance` chain
    in ~12 downstream places and triggers fresh instance-diamond
    warnings.
  - Net: HIGH cost, doesn't address the root cause (which is iso-chain
    accumulation, not `compHom` per se).
- **Gap**: PROCEED — the project's `algebraKbarAway` IS Mathlib-aligned
  (`Algebra.compHom` is the right Mathlib idiom for this lift). The sink
  is elsewhere.
- **Verdict**: **NOT_VIABLE** — refactoring `algebraKbarAway` doesn't
  address the actual blocker. The blocker is iso-chain unification, not
  the instance shape itself.

### Decision 4: `set_option backward.isDefEq.respectTransparency false` — the working fix

- **Mathlib idiom**: WIDELY USED in Mathlib for exactly this kind of
  heartbeat sink. Citations:
  - `Mathlib/AlgebraicGeometry/Normalization.lean:44, 78, 134, 184, 195,
    223, 252, 279, 362` — every major `normalizationDiagram`-related
    declaration uses this option.
  - `Mathlib/RingTheory/TensorProduct/MvPolynomial.lean:176` —
    `rTensorAlgEquiv` (tensor product of polynomial algebra), the
    closest analogue to our situation (algebra-of-algebra-over-base
    crossed with tensor product).
  - `Mathlib/RingTheory/TensorProduct/MonoidAlgebra.lean:45, 52`;
    `Mathlib/RingTheory/TensorProduct/Maps.lean:334`;
    `Mathlib/RingTheory/TensorProduct/IncludeLeftSubRight.lean:157`.
  - `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:353,
    361, 372, 387, 395` — `pullback.congrHom_inv`, `pullback.map_isIso`,
    `pullback.mapDesc_comp`, and `pushout` analogues. These are the
    EXACT API surface we're calling.
- **What the option does**: disables the "respect transparency" guard
  on `isDefEq`, letting the elaborator unfold definitions/instances
  past their declared transparency setting when checking definitional
  equality. In practice: collapses the
  `Algebra.compHom`-through-iso-chain unification from O(200k+)
  heartbeats to O(<1000) heartbeats.
- **Empirical verification (iter-180 lean_multi_attempt)**: applied to
  the actual `gmScalingP1_chart_PLB_eq` goal at line 250, the snippet
  ```
  set_option backward.isDefEq.respectTransparency false in
    (unfold gmScalingP1_cover_X_iso; simp only [Iso.trans_hom, Category.assoc,
      pullbackSpecIso_hom_base])
  ```
  PRODUCES the expected post-rewrite goal:
  ```
  ... ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap kbar Away_i)))
                     (Spec.map (CommRingCat.ofHom (algebraMap kbar (GmRing kbar))))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap kbar Away_i)) = ...
  ```
  i.e., `pullbackSpecIso_hom_base` HAS FIRED. WITHOUT the option,
  the same simp lemma is reported "unused" (= LHS pattern not matched).
- **Project's current path**: never tried this option (the recipe in
  `analogies/gmscaling-cover-bridge.md` Step 3 doesn't mention it).
- **Gap**: divergent-with-cost. Mathlib has THE idiom for this exact
  kind of blocker; the project just hasn't used it yet.
- **Cost of divergence so far**: 5 iters of helper-bridge attempts
  (iter-175 through iter-179) + 2 TEMP axioms admitted iter-177 +
  laundered downstream lemmas.
- **Verdict**: **ALIGN_WITH_MATHLIB**.

### Decision 5: Alternative Mathlib bridge

- **Mathlib idiom**: searched `pullback_snd_of_hom`, `Limits.pullback.fst_of_hom`,
  `Spec.pullback_symmetry`, related variants — none exist directly.
- **The closest existing Mathlib lemma**: `isPullback_SpecMap_pushout`
  (`Pullbacks.lean:776-780`) — gives `IsPullback (Spec.map (pushout.inl f g))
  (Spec.map (pushout.inr f g)) (Spec.map f) (Spec.map g)`. This is a more
  abstract reformulation but doesn't bypass the algebra-instance
  unification — when we'd extract a `pullback.fst`/`pullback.snd`-style
  conclusion, we'd still hit the same algebra-on-tensor-product instance
  synthesis.
- **The shape we want**: identifying
  `(pullbackSpecIso kbar Away_i GmRing).hom ≫ Spec.map (algMap kbar (Away_i ⊗ GmRing))`
  with `pullback.fst _ _ ≫ Spec.map (algMap kbar Away_i)`. That is EXACTLY
  `pullbackSpecIso_hom_base`; there's no alternative bridge.
- **Verdict**: **PROCEED** with `pullbackSpecIso_hom_base` + Decision 4's
  option.

## Verdicts (summary)

| Decision | Verdict | Severity |
|---|---|---|
| (1) Project-side wrapper `pullbackSpecIso_hom_base'` | NOT_VIABLE (shifts the sink) | informational |
| (2) `pullback.mapIso` direct construction | NOT_VIABLE (no shorter chain exists) | informational |
| (3) Replace `Algebra.compHom` with another instance form | NOT_VIABLE (high cost, wrong root cause) | informational |
| (4) `set_option backward.isDefEq.respectTransparency false` | ALIGN_WITH_MATHLIB | critical |
| (5) Alternative Mathlib bridge (`fst_of_hom`, Spec-pullback symmetry) | NOT_VIABLE (none exists) | informational |

## Recommendation

**Apply `set_option backward.isDefEq.respectTransparency false in` to
`gmScalingP1_chart_PLB_eq`** (Decision 4). This is the **canonical Mathlib
idiom for `Algebra.compHom`-chain-driven defeq sinks in pullback
constructions** — Mathlib's own `Normalization.lean`,
`pullback.congrHom_inv`, `pullback.map_isIso`, `pullback.mapDesc_comp`,
and ~14 RingTheory/TensorProduct sites use it for the same family of
blockers.

### Concrete recipe (iter-180 PRIMARY corrective)

Replace the body of `gmScalingP1_chart_PLB_eq` (currently the partial
`sorry` body at L213-L250 of
`AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean`) with:

```lean
set_option backward.isDefEq.respectTransparency false in
private lemma gmScalingP1_chart_PLB_eq (kbar : Type u) [Field kbar] (i : Fin 2) :
    gmScalingP1_chart kbar i ≫ (ProjectiveLineBar kbar).hom =
      (gmScalingP1_cover kbar).f i ≫ ((ProjectiveLineBar kbar) ⊗ Gm kbar).hom := by
  unfold gmScalingP1_chart gmScalingP1_cover_X_iso gmScalingP1_cover
  -- Apply awayι_comp_PLB_hom + homogeneousLocalizationAwayIso_algebraMap
  -- + eval₂Hom_comp_C chain (per iter-179 Attempts 1-3, all worked).
  have h := awayι_comp_PLB_hom kbar (m := 1) Nat.one_pos
    (MvPolynomial.X i : MvPolynomial (Fin 2) kbar)
    (MvPolynomial.isHomogeneous_X kbar i)
  change (gmScalingP1_cover_X_iso kbar i).hom ≫ _ ≫
      ((Proj.awayι (projectiveLineBarGrading kbar)
          (MvPolynomial.X i : MvPolynomial (Fin 2) kbar)
          (MvPolynomial.isHomogeneous_X kbar i) Nat.one_pos :
        Spec (CommRingCat.of (HomogeneousLocalization.Away
          (projectiveLineBarGrading kbar) (MvPolynomial.X i))) ⟶
          Proj (projectiveLineBarGrading kbar)) ≫
        (ProjectiveLineBar kbar).hom) = _
  rw [h, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc,
    homogeneousLocalizationAwayIso_algebraMap, MvPolynomial.algebraMap_eq,
    MvPolynomial.eval₂Hom_comp_C]
  -- iter-180 fix: the option turns the LHS into the canonical
  -- pullback.fst ≫ Spec.map (algMap kbar Away_i) form.
  simp only [Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_base,
    pullback.congrHom_hom, pullback.lift_fst_assoc, Category.id_comp]
  -- Then collapse the remaining pullbackSymmetry/pullbackRightPullbackFstIso
  -- layers + match the RHS via Scheme.AffineOpenCover.openCover_f + Proj.awayι_toSpecZero.
  ... -- (closing tactics; see verification block below)
```

### Verification block (iter-180 `lean_multi_attempt`)

The hard step has been EMPIRICALLY VERIFIED with `lean_multi_attempt` at
line 250 of `GmScaling.lean`. The snippet:

```lean
set_option backward.isDefEq.respectTransparency false in
  (unfold gmScalingP1_cover_X_iso; simp only [Iso.trans_hom, Category.assoc,
    pullbackSpecIso_hom_base])
```

produces the post-rewrite goal (verified via tool — see
`.archon/task_results/mathlib-analogist-pullbackspeciso-bypass.md`
"Verification" section):

```
... ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap kbar Away_i)))
                   (Spec.map (CommRingCat.ofHom (algebraMap kbar (GmRing kbar))))
      ≫ Spec.map (CommRingCat.ofHom (algebraMap kbar Away_i))
= (gmScalingP1_cover kbar).f i ≫ (ProjectiveLineBar kbar ⊗ Gm kbar).hom
```

WITHOUT the option, the same simp lemma is reported "unused" (LHS pattern
not matched). WITH the option, the rewrite fires and exposes the canonical
post-pullback form.

### Residual cleanup (after Decision 4 fires)

The remaining steps to close the goal (NOT the load-bearing blocker, but
the natural continuation):

1. Apply `pullback.congrHom_hom + pullback.lift_fst_assoc + Category.id_comp`
   (already in the simp set above) to collapse the `pullback.congrHom`
   chunk into `pullback.fst (Proj.awayι ... ≫ PLB.hom) Gm.hom ≫ Spec.map (algMap)`.
2. Apply `pullbackRightPullbackFstIso_hom_fst_assoc`. NOTE: this may need
   a `change` or a `Scheme.AffineOpenCover.openCover_f` rewrite to align
   the cover's `(cover).openCover.f i` with `Proj.awayι (![X 0, X 1] i)`.
   The cover-bridge-uniform-i refactor (iter-179) makes these `rfl`-defeq;
   the `respectTransparency false` option should let `simp` see through
   that defeq, but a backup `change` is available if simp still trips.
3. Apply `pullbackSymmetry_hom_comp_snd_assoc` to swap.
4. After step 3, both sides should be of the form
   `pullback.snd _ _ ≫ pullback.fst PLB.hom Gm.hom ≫ PLB.hom` — discharged
   by `(PreZeroHypercover.pullback₁).f_def` + `Over.tensorObj_hom_def` if
   needed, or by direct `rfl` if defeq holds.

### Reversal trigger

If `set_option backward.isDefEq.respectTransparency false` does NOT
unblock `pullbackSpecIso_hom_base` (e.g., a future Lean/Mathlib version
changes the meaning of this option), fall back to the **per-step
`change`** workaround documented in the iter-179 task_result Attempt 2:
manually retype the relevant `≫` chain's middle object using `change ...
≫ ((X : A ⟶ B) ≫ Y) = _`. This was the iter-179 corrective for
`awayι_comp_PLB_hom`; it would extend to the 4-layer iso chain via a
sequence of slice-based `change`s (~30 LOC, slower but more
defensible against transparency-option drift).

### Why this wasn't tried earlier

The 5 prior iters' analogist consults (iter-176, iter-178) recommended
`simp [Fin.isValue, Fin.zero_eta]`, the uniform-in-`i` refactor of
`gmScalingP1_cover_X_iso`, and chart-bridge defeq chasing. None of these
addressed the `Algebra.compHom`-chain heartbeat sink directly because
the diagnosis (per iter-179 Lane A task_result Attempt 6 — `erw` timing
out at 200k heartbeats during `isDefEq`) only became precise in iter-179.
With the precise diagnosis in hand, the
`backward.isDefEq.respectTransparency false` idiom is the direct
Mathlib-aligned corrective.

## What did NOT need to change

- `algebraKbarAway` — IS Mathlib-aligned (`Algebra.compHom` is the
  canonical lift); refactoring it is high-cost and wrong-root-cause.
- `pullbackSpecIso_hom_base` itself — IS the right Mathlib lemma; no
  wrapper or alternative bridge is needed.
- The 4-layer iso chain in `gmScalingP1_cover_X_iso` — IS Mathlib-aligned
  with `OpenCover.pullbackCoverAffineRefinementObjIso`; no
  `pullback.mapIso` shortcut exists.
- `gmScalingP1_cover` via `pullback₁` — IS the canonical Mathlib encoding.
