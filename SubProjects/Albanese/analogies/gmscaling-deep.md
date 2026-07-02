# Analogy: deeper, transcription-ready recipe for `gmScalingP1` and the chart-1 collapse-at-zero lemma

## Mode
api-alignment

## Slug
gmscaling-deep

## Iteration
168

## Question

Six concrete, transcription-ready sub-questions in service of finally writing the
body of `gmScalingP1` (`AlgebraicJacobian/Genus0BaseObjects.lean:457`) and its
companion `gmScalingP1_collapse_at_zero` (L472). Verbatim:

- **Q1** — exact API of `Proj.affineOpenCoverOfIrrelevantLESpan` specialised to
  `f := ![X 0, X 1]` on the standard ℕ-grading of `MvPolynomial (Fin 2) k̄`.
- **Q2** — canonical Mathlib path to build
  `HomogeneousLocalization.Away (projectiveLineBarGrading kbar) (X i) ≃+*
  MvPolynomial Unit kbar`.
- **Q3** — chart-side morphism via `pullbackSpecIso`.
- **Q4** — cross-chart agreement equation.
- **Q5** — `Scheme.Cover.glueMorphisms` signature + how to bridge from
  `AffineOpenCover` to `Cover`.
- **Q6** — proof body for `gmScalingP1_collapse_at_zero`.

## Project artifact(s)

- `AlgebraicJacobian/Genus0BaseObjects.lean:457-459` — `def gmScalingP1 := sorry`
- `AlgebraicJacobian/Genus0BaseObjects.lean:472-476` — `lemma gmScalingP1_collapse_at_zero := by sorry`
- `AlgebraicJacobian/Genus0BaseObjects.lean:268-282` — `zeroPt`/`onePt`/`inftyPt` realisations
  (built via `pointOfVec`/`Proj.fromOfGlobalSections`; `zeroPt = pointOfVec (v 0 := 0, v 1 := 1)`,
  so `zeroPt` lives in chart `D₊(X 1)`).

## Coordinate convention chosen for the rest of this file

To avoid confusion between "chart i = D₊(X i)" and "chart i = where X i vanishes",
the rest of this document uses the unambiguous version:

| Chart name | Open set | Vanishing coord | Affine coord | Where `zeroPt = [0:1]` lives |
|---|---|---|---|---|
| `chart₀` | `D₊(X 0)` | `X 1 = 0` allowed if `X 0 ≠ 0` | `t := X 1 / X 0` | NO (`X 0 = 0` at zeroPt) |
| `chart₁` | `D₊(X 1)` | `X 0 = 0` allowed if `X 1 ≠ 0` | `u := X 0 / X 1` | YES (`u = 0` at zeroPt) |

Homogeneous scaling convention picked for `σ_×`:
`σ_×([X 0 : X 1], λ) = [λ·X 0 : X 1]` ⇒ `σ_×([0:1], λ) = [0:1] = zeroPt` ∀ λ (✓).
This means:

- On `chart₁` (where the collapse-at-zero lemma lives): `u ↦ λ·u`, i.e. the ring
  map `MvPolynomial Unit k̄ → MvPolynomial Unit k̄ ⊗_{k̄} k̄[λ, λ⁻¹]`, `X () ↦ X () ⊗ λ`.
- On `chart₀`: `t = X 1/X 0 ↦ X 1/(λ·X 0) = t/λ`, i.e. `X () ↦ X () ⊗ λ⁻¹`.

(The chart-0 map uses `λ⁻¹ ∈ GmRing`, available because GmRing is `Localization.Away (X ())`,
so `Localization.Away.invSelf` gives `λ⁻¹`. **This is essential** — the chart-0 map only
makes sense after tensor with Gm precisely because that's what makes `λ⁻¹` available.)

## Mathlib state (verified by `lean_local_search` + direct file reads at iter-168)

All citations are to the lake-checked-out Mathlib in
`.lake/packages/mathlib/Mathlib/`. Line numbers are from current files at iter-168.

- **`AlgebraicGeometry.Proj.affineOpenCoverOfIrrelevantLESpan`**
  (`AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:324-335`) — verbatim signature:

  ```lean
  noncomputable
  def affineOpenCoverOfIrrelevantLESpan {ι : Type*} (f : ι → A) {m : ι → ℕ}
      (f_deg : ∀ i, f i ∈ 𝒜 (m i)) (hm : ∀ i, 0 < m i)
      (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
      (Proj 𝒜).AffineOpenCover where
    I₀ := ι
    X i := .of (Away 𝒜 (f i))
    f i := awayι 𝒜 (f i) (f_deg i) (hm i)
    idx x := (mem_iSup.mp ((iSup_basicOpen_eq_top 𝒜 f hf).ge (Set.mem_univ x))).choose
    covers x := ⟨_, _⟩
  ```

  Where `Away 𝒜 f := HomogeneousLocalization 𝒜 (Submonoid.powers f)`
  (`RingTheory/GradedAlgebra/HomogeneousLocalization.lean:601`) and
  `Proj.awayι 𝒜 f f_deg hm : Spec (.of <| Away 𝒜 f) ⟶ Proj 𝒜`
  (`AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:189`).

- **`Scheme.AffineOpenCover`** (`AlgebraicGeometry/Cover/Open.lean:118-119`):
  `abbrev AffineOpenCover := AffineCover @IsOpenImmersion`.
- **`AffineCover` (with `cover` field)** (`AlgebraicGeometry/Cover/MorphismProperty.lean:193-218`):
  ```lean
  structure AffineCover (P : MorphismProperty Scheme.{u}) (S : Scheme.{u}) where
    I₀ : Type v ; X : I₀ → CommRingCat.{u} ; f : ∀ j, Spec (X j) ⟶ S
    idx : S → I₀ ; covers : ∀ x, x ∈ Set.range (f (idx x))
    map_prop (j) : P (f j) := by infer_instance
  def AffineCover.cover : X.AffineCover P → X.Cover (precoverage P) := ...
  ```
  `AffineOpenCover.openCover` is a `simps`-generated alias for `.cover`
  (`Cover/Open.lean:128`).

- **`Scheme.Cover.glueMorphisms`** (`AlgebraicGeometry/Gluing.lean:436-445`) —
  verbatim signature:
  ```lean
  def glueMorphisms (𝒰 : OpenCover.{v} X) {Y : Scheme.{u}} (f : ∀ x, 𝒰.X x ⟶ Y)
      (hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x =
                    pullback.snd _ _ ≫ f y) :
      X ⟶ Y
  theorem ι_glueMorphisms ... (𝒰.f x ≫ 𝒰.glueMorphisms f hf = f x)  -- L457
  theorem hom_ext ... (∀ x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) → f₁ = f₂      -- L448
  ```
  Takes an `OpenCover`, not an `AffineOpenCover`. Bridge via
  `AffineOpenCover.openCover`.

- **`AlgebraicGeometry.pullbackSpecIso`**
  (`AlgebraicGeometry/Pullbacks.lean:703-708`) — verbatim signature:
  ```lean
  noncomputable
  def pullbackSpecIso (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
      [Algebra R S] [Algebra R T] :
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅
        Spec (.of <| S ⊗[R] T)
  -- key simp lemmas (all `reassoc (attr := simp)`):
  pullbackSpecIso_inv_fst : .inv ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom includeLeftRingHom)                          -- L717
  pullbackSpecIso_inv_snd : .inv ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (toRingHom includeRight))                    -- L733
  pullbackSpecIso_hom_fst' : .hom ≫ Spec.map (ofHom (algebraMap S _)) =
    pullback.fst _ _                                                          -- L750
  pullbackSpecIso_hom_base : .hom ≫ Spec.map (ofHom (algebraMap R _)) =
    pullback.fst _ _ ≫ Spec.map (ofHom (algebraMap _ _))                     -- L766
  ```

- **`AlgebraicGeometry.Scheme.Cover.pullback₁`**
  (`AlgebraicGeometry/Cover/MorphismProperty.lean:177` and called at L184).
  Given `𝒰 : X.Cover` and `f : W ⟶ X`, produces a cover of `W` whose `i`-th chart
  is `pullback f (𝒰.f i)`.

- **`IsLocalization.Away.lift`** (`RingTheory/Localization/Away/Basic.lean:471`)
  and `Away.lift_comp` / `Away.lift_eq` (same file).

- **`MvPolynomial.aeval (f : σ → S) : MvPolynomial σ R →ₐ[R] S`** — universal property
  of polynomial rings (`Mathlib.Algebra.MvPolynomial.Eval`).

- **NOT shipped**: `HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k̄)
  (X i) ≃+* MvPolynomial Unit k̄`. Mathlib has **no** "Proj of standard ℕ-graded
  polynomial ring → projective n-space" iso, no `Mathlib.AlgebraicGeometry.ProjectiveSpace`
  namespace, and no helper that identifies any `HomogeneousLocalization.Away`
  with a polynomial ring. Verified via `lean_loogle "HomogeneousLocalization.Away ≃+*"`
  (no results), `lean_loogle "HomogeneousLocalization _ _ →+* MvPolynomial"` (no
  results), `lean_leansearch "degree zero part of polynomial ring localized at one variable"`
  (returns only generic `HomogeneousLocalization.fromZeroRingHom`).

  **What Mathlib does ship that helps**: `HomogeneousLocalization.val_injective`
  (RingTheory/GradedAlgebra/HomogeneousLocalization.lean:312) lets us define the
  inverse of an iso through `Away.mk_surjective` (L618). `Away.adjoin_mk_prod_pow_eq_top`
  (L1064) says `Away 𝒜 f` is algebra-finite over `𝒜 0`. These two together yield
  the iso, but not in a single Mathlib API call — see Q2 verdict below.

## Decisions identified

### Decision Q1: 2-chart cover of `ProjectiveLineBar`

- **Mathlib idiom**: `affineOpenCoverOfIrrelevantLESpan` specialised to `ι := Fin 2`,
  `f := ![MvPolynomial.X 0, MvPolynomial.X 1]`, `m := ![1, 1]`. **EXACT** signature
  the prover writes:

  ```lean
  /-- The 2-chart cover of `ProjectiveLineBar kbar`'s underlying scheme by the two
  affine charts `D₊(X 0)` and `D₊(X 1)`. -/
  noncomputable def projectiveLineBarAffineCover (kbar : Type u) [Field kbar] :
      (ProjectiveLineBarScheme kbar).AffineOpenCover :=
    Proj.affineOpenCoverOfIrrelevantLESpan (projectiveLineBarGrading kbar)
      (ι := Fin 2)
      (f := ![MvPolynomial.X 0, MvPolynomial.X 1])
      (m := ![1, 1])
      (f_deg := fun i ↦ by fin_cases i <;>
        exact MvPolynomial.isHomogeneous_X kbar _)
      (hm := fun i ↦ by fin_cases i <;> exact one_pos)
      (hf := by
        -- The irrelevant ideal = (X 0, X 1), span of the two generators.
        intro p hp
        rw [HomogeneousIdeal.mem_irrelevant_iff] at hp
        -- `p` is in degree-positive part; decompose into X-monomials and conclude.
        sorry  -- standard MvPolynomial decomposition; ~10 LOC
        )
  ```

  The `hf` step needs to show that the irrelevant ideal of the standard ℕ-grading on
  `MvPolynomial (Fin 2) k̄` is contained in `Ideal.span {X 0, X 1}` — a standard
  decomposition argument via `MvPolynomial.support_X`. **This is the only
  not-completely-trivial sub-step**; the rest is `fin_cases`.

- **Verdict**: **PROCEED with `affineOpenCoverOfIrrelevantLESpan`**.
- **Concrete checklist for the prover**: name the cover
  `projectiveLineBarAffineCover` (NOT `projectiveLineBar...Cover`); use `Fin 2`
  as index (not `PNat × _` like the all-generators `Proj.affineOpenCover`).
- **LOC estimate**: ~15-20 LOC.

### Decision Q2: `homogeneousLocalizationAwayIso`

- **Mathlib idiom**: **NOT SHIPPED**. The previous iter-167 sketch said
  "~30 LOC, project owes". The deeper investigation at iter-168 reveals:
  `HomogeneousLocalization.Away` is *not* a localization-of-the-graded-ring (it's
  the *degree-0 sub-ring* of `Localization (Submonoid.powers f)` selected by the
  homogeneous-fraction structure). So the iso must be built from the `Away.mk`
  +  `val_injective` API directly.

  **The canonical Mathlib path is the universal property of `MvPolynomial Unit`**:

  ```lean
  /-- The chart-`i` ring `Away 𝒜 (X i) ≅ k̄[u]` where `u = X (1-i) / X i`. -/
  noncomputable def homogeneousLocalizationAwayIso
      (kbar : Type u) [Field kbar] (i : Fin 2) :
      HomogeneousLocalization.Away (projectiveLineBarGrading kbar)
          (MvPolynomial.X i : MvPolynomial (Fin 2) kbar) ≃+*
        MvPolynomial Unit kbar where
    -- Inverse direction (THE EASY HALF — universal property of MvPolynomial Unit):
    invFun := MvPolynomial.aeval (R := kbar)
      (S₁ := HomogeneousLocalization.Away (projectiveLineBarGrading kbar) (X i))
      (fun _ => HomogeneousLocalization.Away.mk
        (projectiveLineBarGrading kbar)
        (MvPolynomial.isHomogeneous_X kbar i) 1
        (MvPolynomial.X (jOf i))                  -- jOf i := if i = 0 then 1 else 0
        (by simp; exact MvPolynomial.isHomogeneous_X kbar (jOf i)))
    -- Forward direction (THE HARD HALF — defined by `Quotient.lift` via `val_injective`):
    toFun := Quotient.lift
      (fun ⟨n, ⟨num, hnum⟩, ⟨den, hden⟩, ⟨k, hk⟩⟩ =>
        -- evaluate the fraction `num / X i ^ k` at X i ↦ 1, X (jOf i) ↦ X ()
        MvPolynomial.eval (fun j => if j = i then (1 : MvPolynomial Unit kbar)
                                     else MvPolynomial.X ()) num)
      (by
        intro x y h
        -- The equivalence relation is `embedding x = embedding y`, both views in
        -- `Localization (powers (X i))`. Use the well-defined ring map
        -- `MvPolynomial (Fin 2) k̄ → MvPolynomial Unit k̄`, `X i ↦ 1`, `X (jOf i) ↦ X ()`
        -- and the fact that `X i ↦ 1` makes powers of `X i` into 1 (units), so the
        -- map factors through Localization.
        sorry  -- ~10-15 LOC: invoke MvPolynomial.eval's well-definedness
        )
    map_one' := by simp [HomogeneousLocalization.one_eq, Quotient.lift]
    map_mul' := by
      rintro ⟨_⟩ ⟨_⟩
      simp [Quotient.lift]; ring  -- standard
    map_add' := by
      rintro ⟨_⟩ ⟨_⟩
      simp [Quotient.lift]; ring  -- standard
    map_zero' := by simp [HomogeneousLocalization.zero_eq, Quotient.lift]
    left_inv := by
      rintro ⟨n, ⟨num, hnum⟩, ⟨den, hden⟩, ⟨k, rfl⟩⟩
      -- Round-trip: forward sends to `eval`; backward sends back to `Away.mk`.
      -- Use `HomogeneousLocalization.val_injective` to compare in `Localization`.
      apply HomogeneousLocalization.val_injective
      sorry  -- ~15 LOC: chase via `Away.val_mk` + `Localization.mk_eq_mk_iff`
    right_inv := by
      intro p
      -- Round-trip: backward sends to `Away.mk` of `aeval`; forward evaluates.
      induction p using MvPolynomial.induction_on with
      | C r => simp [MvPolynomial.aeval_C]; rfl
      | add p q hp hq => simp [hp, hq]
      | mul_X p _ hp => simp [hp]; ring
  ```

  where `jOf : Fin 2 → Fin 2` is the "swap" `if i = 0 then 1 else 0`.

- **Mathlib gap depth**: this is NOT shipped at all. The iter-167 file's "~30 LOC"
  estimate was too optimistic — the realistic count is **60-90 LOC** because:
  - The "forward" map's well-definedness goes through `Quotient.lift`'s
    well-definedness hypothesis on the embedding into `Localization`, which is
    where the actual ring-theoretic content lives.
  - `MvPolynomial.eval` is over a polynomial-ring substitution that the `Quotient.lift`
    needs to commute with — this is **not a single Mathlib lemma**.
  - The `left_inv` round-trip needs `HomogeneousLocalization.val_injective` plus
    a direct comparison in `Localization`.

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**. The project owes this helper. It is
  upstream-able as a single ~80-LOC file `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization.PolynomialQuotient`
  (or similar). Out of scope for landing in Mathlib at iter-168; landing in the
  project is required for `gmScalingP1`.

  **PROCEED with the recipe above**, but treat the LOC estimate as ~60-90, not
  ~30. The previous file's optimistic estimate is what blocked iter-167 — the
  prover ran out of budget on a "30 LOC" item that was 3x larger.

- **Alternative considered and rejected**: use `Away.adjoin_mk_prod_pow_eq_top`
  (`Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:1064`) +
  `Algebra.adjoin_eq_top_iff_isIso_aeval`. **Rejected**: this still requires
  showing the aeval map is injective, which is the harder half. Builds neither
  shorter nor cleaner than the direct recipe.

### Decision Q3: chart-side morphism via `pullbackSpecIso`

- **Setup**:
  - Chart `i` of `ProjectiveLineBar.left` = `Spec (Away 𝒜 (X i))`. After Q2's
    iso, identify with `Spec (MvPolynomial Unit k̄)`.
  - `Gm.left = Spec GmRing = Spec (Localization.Away (X () : MvPolynomial Unit k̄))`.
  - Product `chart_i ⊗ Gm` in `Over (Spec k̄)` = pullback of the two structure
    maps to `Spec k̄`. Via `pullbackSpecIso`, this is
    `Spec ((MvPolynomial Unit k̄) ⊗_{k̄} GmRing)`.

- **The chart-1 morphism (the one needed by collapse-at-zero)**:
  Ring map at chart 1:
  ```
  φ₁ : MvPolynomial Unit k̄  →+*  MvPolynomial Unit k̄ ⊗_{k̄} GmRing
  φ₁(X ()) = X () ⊗ₜ algebraMap kbar GmRing 1 * 1 ⊗ₜ X ()_Gm   -- = u·λ
  ```
  built concretely via `MvPolynomial.aeval`:
  ```lean
  noncomputable def gmScalingP1_chart1_ringMap (kbar : Type u) [Field kbar] :
      MvPolynomial Unit kbar →+* MvPolynomial Unit kbar ⊗[kbar] GmRing kbar :=
    (MvPolynomial.aeval
      (R := kbar) (σ := Unit)
      (S₁ := MvPolynomial Unit kbar ⊗[kbar] GmRing kbar)
      (fun _ => (MvPolynomial.X () : MvPolynomial Unit kbar) ⊗ₜ
                  (algebraMap kbar (GmRing kbar) 1) *
                (1 : MvPolynomial Unit kbar) ⊗ₜ
                  (algebraMap _ (GmRing kbar) (MvPolynomial.X ())))).toRingHom
  ```

  **WARNING**: this is hard to read but the simple way to spell it is "u ↦ u·λ
  in the tensor product", which by `Algebra.TensorProduct.tmul_mul_tmul` equals
  `(u ⊗ 1) * (1 ⊗ λ) = u ⊗ λ`. So a cleaner spelling:

  ```lean
  noncomputable def gmScalingP1_chart1_ringMap :
      MvPolynomial Unit kbar →+* MvPolynomial Unit kbar ⊗[kbar] GmRing kbar :=
    MvPolynomial.eval₂RingHom
      (algebraMap kbar _)
      (fun _ => (MvPolynomial.X () : MvPolynomial Unit kbar) ⊗ₜ
                  (algebraMap (MvPolynomial Unit kbar) (GmRing kbar)
                    (MvPolynomial.X ())))
  ```

  (Uses `MvPolynomial.eval₂RingHom` to send `X () ↦ u ⊗ λ` and `kbar ↦ kbar ⊗ 1`.)

- **The chart-side morphism in `Scheme`**:
  ```lean
  -- chart 1's map "(u, λ) ↦ λ·u" — into ProjectiveLineBarScheme directly:
  noncomputable def gmScalingP1_chart1 (kbar : Type u) [Field kbar] :
      pullback
          (Spec.map (CommRingCat.ofHom (algebraMap kbar (MvPolynomial Unit kbar))))
          (Spec.map (CommRingCat.ofHom (algebraMap kbar (GmRing kbar)))) ⟶
        ProjectiveLineBarScheme kbar :=
    -- 1. Bridge: pullback ≅ Spec (MvPolynomial Unit kbar ⊗[kbar] GmRing kbar)
    (pullbackSpecIso kbar (MvPolynomial Unit kbar) (GmRing kbar)).hom ≫
    -- 2. The ring map: u ↦ u ⊗ λ, defined in `gmScalingP1_chart1_ringMap`
    Spec.map (CommRingCat.ofHom (gmScalingP1_chart1_ringMap kbar)) ≫
    -- 3. The reverse iso k[u] ≃+* Away 𝒜 (X 1)
    Spec.map (CommRingCat.ofHom (homogeneousLocalizationAwayIso kbar 1).symm) ≫
    -- 4. The awayι into Proj
    Proj.awayι (projectiveLineBarGrading kbar) (X 1)
      (MvPolynomial.isHomogeneous_X kbar 1) one_pos
  ```

  **WARNING (subtle)**: the "chart of `ℙ¹ ⊗ Gm`" is NOT literally
  `pullback (Spec.map _) (Spec.map _)`; it's the `Over (Spec k̄)`-level product
  `chart_i ⊗ Gm`, whose underlying `Scheme.pullback` is `pullback awayι.hom Gm.hom`
  (NOT `pullback (algebraMap _ _) (algebraMap _ _)`). To bridge, the prover must
  use the explicit description of `(chart_i ⊗ Gm).left`:

  ```lean
  (Spec (.of (Away 𝒜 (X i))) ⊗ Gm kbar).left =
    pullback (chart structure map) (Gm structure map)
  ```

  Both structure maps factor through `Spec k̄`, so by uniqueness of pullback this
  IS isomorphic to `pullback (Spec.map (algebraMap kbar (Away 𝒜 (X i))))
  (Spec.map (algebraMap kbar GmRing))`, which is what `pullbackSpecIso` expects.
  Practically, the prover writes the chart map at the `Over (Spec k̄)` level via
  `Over.homMk` and lets the `Over`-pullback API do the bridging.

- **Verdict**: **PROCEED with `pullbackSpecIso` + ring map + reverse Q2-iso + `awayι`**.
  The ring map's definition is short (~5 LOC); the wrapping through `Over` /
  `pullbackSpecIso` is `~15 LOC`. **Critical**: the prover MUST work in
  `Over (Spec k̄)` from the start, or the `(chart ⊗ Gm)`-vs-`pullback awayι Gm.hom`
  mismatch will require manual bridging at every `simp`.

- **The chart-0 morphism (analogous, with `λ⁻¹` instead of `λ`)**:
  ```lean
  -- chart 0's map "(t, λ) ↦ t/λ" — symmetric to chart 1.
  -- λ⁻¹ is obtained from `IsLocalization.Away.invSelf (X ())` (Mathlib's standard
  -- `Localization.Away`-invertible-element witness; `Mathlib/RingTheory/Localization/Away/Basic.lean`).
  noncomputable def gmScalingP1_chart0_ringMap : ... :=
    MvPolynomial.eval₂RingHom
      (algebraMap kbar _)
      (fun _ => (MvPolynomial.X () : MvPolynomial Unit kbar) ⊗ₜ
                  (IsLocalization.Away.invSelf (MvPolynomial.X () : MvPolynomial Unit kbar)))
  ```
  Note: `IsLocalization.Away.invSelf x` is a Mathlib API giving the canonical
  inverse of `x` in `Localization.Away x`. Cite:
  `Mathlib/RingTheory/Localization/Away/Basic.lean` (`def invSelf`).

### Decision Q4: cross-chart agreement equation

- **What `glueMorphisms` requires** (per `Gluing.lean:436`):
  ```
  ∀ x y : 𝒰.I₀, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd _ _ ≫ f y
  ```
  For our 2-element cover `𝒰 = projectiveLineBarAffineCover.openCover.pullback₁ pullback.fst`,
  the `x = y` cases are trivial (`pullback.fst = pullback.snd` on the diagonal,
  up to `pullback.condition`). The `(0, 1)` and `(1, 0)` cases are the real
  agreement check.

- **The (0, 1)-case**: on the intersection `D₊(X 0) ∩ D₊(X 1) = D₊(X 0 · X 1)`,
  affine ring `Away 𝒜 (X 0 · X 1)`. Via Mathlib's `Proj.Away.isLocalization_mul`
  (`RingTheory/GradedAlgebra/HomogeneousLocalization.lean:883`), this is
  `Localization.Away (isLocalizationElem (X 0)_deg (X 1)_deg)` on top of
  `Away 𝒜 (X 0)`, which after Q2's chart-0 iso is
  `Localization.Away (X ())` on top of `MvPolynomial Unit k̄`, i.e.
  `Localization.Away t = k̄[t, t⁻¹]`.

  After tensoring with `GmRing = k̄[λ, λ⁻¹]`, the intersection ring is
  `k̄[t, t⁻¹] ⊗_{k̄} k̄[λ, λ⁻¹] = k̄[t, t⁻¹, λ, λ⁻¹]`.

  **The ring-level equation**: both chart maps, restricted to the intersection,
  send `u = X 0 / X 1 ∈ Away 𝒜 (X 0 · X 1)` (where `u = 1/t` on chart-0 side,
  `u = u` on chart-1 side) to the same expression `t ↦ λ·u ↔ λ/t` on chart-0
  and to `u ↦ λ·u` on chart-1. They're equal because `λ·u = λ/t = λ·(1/t)`.

  **Practical form** (what the prover types):

  ```lean
  -- For x = 0, y = 1 (the cross case):
  · -- Goal: pullback.fst _ _ ≫ chart0_map = pullback.snd _ _ ≫ chart1_map
    -- on Spec(MvPolynomial Unit k̄ ⊗ MvPolynomial Unit k̄ ⊗ GmRing) (~)
    -- The two ring maps coincide on the (1-1)/(1-0) coordinate after multiplying by t
    -- (= passing through Localization.Away t). Use:
    apply (pullbackSpecIso _ _ _).hom.eq_of_comp_left  -- or similar
    -- then unfold and apply `MvPolynomial.algHom_ext` + `t * (1/t) = 1`.
    sorry
  ```

  **The actual ring-level identity**: in `MvPolynomial Unit k̄ ⊗
  MvPolynomial Unit k̄ ⊗ GmRing`, when restricted to the chart-intersection
  localization, the chart-0 expression `(1/t) ⊗ λ⁻¹` and the chart-1 expression
  `u ⊗ λ` get identified via the gluing iso `t = 1/u, u = 1/t`. Concretely, on
  the intersection ring `Localization.Away t ⊗ GmRing`, the chart-0 map sends
  `1/t ↦ (1/t)·λ⁻¹` and the chart-1 map (after `t = 1/u` substitution) sends
  `u ↦ u·λ = (1/t)·λ`. **They differ by a factor of `λ²`**. Wait — that's wrong.
  Let me recompute.

  Actually: chart-0 affine coord t = X 1/X 0, chart-1 affine coord u = X 0/X 1.
  So on the intersection, `t·u = 1`, i.e. `u = 1/t`. Under σ_×:
  - Chart-0: `t ↦ t/λ` (NOT `t ↦ λ·t`). After convention chosen above
    (`σ_× = [λX 0 : X 1]`): `t = X 1/X 0 ↦ X 1/(λ X 0) = t/λ`.
  - Chart-1: `u ↦ λ·u`.
  - On intersection: `λ·u = λ·(1/t) = λ/t`, vs `t ↦ t/λ` means `u = 1/t ↦ 1/(t/λ) = λ/t`. **EQUAL.** ✓

  So the cross-chart agreement reduces to `λ·u = 1/(t/λ)`, which after
  `u = 1/t` and `Localization.Away t`'s invertibility is `λ·(1/t)·t = λ`, true.

- **Verdict**: **PROCEED with the explicit ring-level identity** `λ·u = (1/t)·λ`
  inside `Localization.Away t ⊗ GmRing`. The proof script is:
  ```lean
  · -- Cross-chart agreement at (i, j) = (0, 1)
    -- Goal: pullback.fst _ _ ≫ chart0_map = pullback.snd _ _ ≫ chart1_map
    -- Reduce both sides to a Spec.map of the SAME ring map on
    -- Spec ((Away 𝒜 (X 0 · X 1)) ⊗_{k̄} GmRing).
    -- This is a `pullbackSpecIso` chain + a `MvPolynomial.algHom_ext` /
    -- IsLocalization.lift_uniq closure.
    ext1
    · -- on Spec coord (1/t)
      simp [gmScalingP1_chart0_ringMap, gmScalingP1_chart1_ringMap,
        pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd,
        Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
      -- residual: `t · u = 1` in `Localization.Away t`. Use
      -- `IsLocalization.Away.mul_invSelf` or `Localization.Away.invSelf_mul`.
      sorry  -- ~5 LOC of algebra
  ```
  Estimated body: ~40 LOC total for both cross-chart cases (one (0,1) case +
  one (1,0) case, the latter by symmetry).

### Decision Q5: `Scheme.Cover.glueMorphisms` signature + bridging

- **Mathlib idiom**: `Scheme.Cover.glueMorphisms` (`Gluing.lean:436`) takes
  `𝒰 : OpenCover.{v} X` (a `Cover (precoverage @IsOpenImmersion)`). Bridge from
  `AffineOpenCover` to `Cover`:
  ```lean
  -- In our setting we want to glue on (ProjectiveLineBar ⊗ Gm).left.
  -- We have Lane A's projectiveLineBarAffineCover : (ProjectiveLineBarScheme kbar).AffineOpenCover
  -- (indexed by Fin 2). Pull this back along (ProjectiveLineBar.hom) ⊗ id (or
  -- equivalently along pullback.fst inside (ProjectiveLineBar ⊗ Gm).left).
  --
  -- The bridge: AffineOpenCover.openCover → OpenCover.
  -- Then OpenCover.pullback₁ produces the cover of the product.
  noncomputable def projGmCover : ((ProjectiveLineBar kbar) ⊗ Gm kbar).left.OpenCover :=
    (projectiveLineBarAffineCover kbar).openCover.pullback₁
      (pullback.fst (ProjectiveLineBar kbar).hom (Gm kbar).hom)
  ```
  **Chosen cover index**: `Fin 2` (inherited from `projectiveLineBarAffineCover`).
  Each chart `i : Fin 2` becomes
  `pullback (pullback.fst (PLB).hom (Gm).hom) (awayι ... (X i) ...)`.

- **Verdict**: **PROCEED**. The bridge is one line; the cover indexing is `Fin 2`
  (NOT a product type — the `pullback₁` keeps the original cover's index).

### Decision Q6: `gmScalingP1_collapse_at_zero` body

- **Setup**: once `gmScalingP1` is concrete (Q3-Q5), the collapse-at-zero lemma
  is a chart-level computation. `zeroPt : 𝟙_ ⟶ ProjectiveLineBar kbar` is
  realized via `pointOfVec (fun i => if i = 0 then 0 else 1) 1 _`, so:
  - `zeroPt`'s underlying scheme map: `Spec k̄ ⟶ Proj 𝒜` via
    `Proj.fromOfGlobalSections` of the eval `X 0 ↦ 0, X 1 ↦ 1`.
  - **Critically**: this factors through `awayι 𝒜 (X 1)` (chart-1 inclusion)
    because `v 1 = 1` is the unit coordinate. The factorisation is a `Spec.map`
    of the eval map `Away 𝒜 (X 1) → k̄`, which under Q2's iso is
    `MvPolynomial Unit k̄ → k̄`, sending `u ↦ 0` (since `zeroPt` has affine
    coord `u = X 0 / X 1 = 0 / 1 = 0`).

- **The collapse-at-zero statement** (verbatim from L472):
  ```lean
  lemma gmScalingP1_collapse_at_zero (kbar : Type u) [Field kbar] :
      lift (toUnit (Gm kbar) ≫ ProjectiveLineBar.zeroPt kbar) (𝟙 (Gm kbar)) ≫
          gmScalingP1 kbar =
        toUnit (Gm kbar) ≫ ProjectiveLineBar.zeroPt kbar
  ```

- **Proof strategy**: use `Scheme.Cover.hom_ext` (`Gluing.lean:448`) on the
  `(Gm).left.OpenCover` consisting of the single chart `𝟙 (Gm).left`. Since `Gm`
  is affine (`gm_isAffine`), this reduces to checking the equation at the
  ring level after applying `Spec.map`.

  **Actually simpler**: factor `lift (toUnit ≫ zeroPt) (𝟙 Gm) : Gm → ℙ¹ ⊗ Gm` through
  the chart-1 chart of the cover (since `zeroPt` lives in chart-1), then use
  `Cover.ι_glueMorphisms` to compute `chart_1.f ≫ gmScalingP1 = chart_1.morphism`.

  ```lean
  lemma gmScalingP1_collapse_at_zero (kbar : Type u) [Field kbar] :
      lift (toUnit (Gm kbar) ≫ ProjectiveLineBar.zeroPt kbar) (𝟙 (Gm kbar)) ≫
          gmScalingP1 kbar =
        toUnit (Gm kbar) ≫ ProjectiveLineBar.zeroPt kbar := by
    -- Step 1: `lift (toUnit ≫ zeroPt) (𝟙 Gm)` factors through chart-1 of
    -- (ProjectiveLineBar ⊗ Gm).
    -- Step 2: `gmScalingP1`'s chart-1 component is the ring map `u ↦ u·λ`.
    -- Step 3: precomposing with `zeroPt → chart-1` (which sends `u ↦ 0`) gives
    -- the ring map `u ↦ 0·λ = 0`, i.e. the constant `0`.
    -- Step 4: that's exactly `toUnit ≫ zeroPt`.
    --
    -- Concretely, by `Scheme.Hom.ext` (or `Over.hom_ext`) reduce to
    -- `Spec`-level, then use the chart-1 `Spec.map` chain.
    apply Over.hom_ext
    -- Or: factor through chart-1 and apply `Proj.fromOfGlobalSections_morphismRestrict`.
    -- The detailed unfold:
    --   chart-1 ring map: φ₁(u) = u ⊗ λ ∈ k̄[u] ⊗ GmRing
    --   precompose with `Spec(k̄[u]/⟨u⟩) ⟶ Spec(k̄[u])` (the u ↦ 0 eval).
    --   In the ring: u ⊗ λ ↦ 0 ⊗ λ = 0 (since 0 ⊗ anything = 0 in tensor product).
    -- That's the ring map `u ↦ 0`, i.e. the constant map at `u = 0`.
    sorry  -- ~30-40 LOC of chart-1 chase
  ```

  The "actual `rw` / `simp` set" the prover should drive the residual to:
  - `MvPolynomial.aeval_X` / `MvPolynomial.eval₂_X` (to evaluate the ring map
    on the generator).
  - `Algebra.TensorProduct.zero_tmul` / `TensorProduct.zero_tmul` (`0 ⊗ x = 0`).
  - `pullbackSpecIso_inv_fst` / `_snd` (to commute `Spec.map` with `pullback.fst/snd`).
  - `Proj.awayι_preimage_basicOpen` + `Proj.fromOfGlobalSections_morphismRestrict`
    (to identify the factorisation of `zeroPt` through chart-1).

- **Verdict**: **PROCEED**. The proof is ~30-50 LOC, the long pole being the
  initial unfold of `gmScalingP1`'s concrete chart-1 form (Q3) and the
  factorisation of `zeroPt` through `awayι (X 1)` (which needs an explicit
  helper lemma `ProjectiveLineBar.zeroPt_factors_through_chart1`).

  **Concrete helper to land first** (~15 LOC):
  ```lean
  lemma ProjectiveLineBar.zeroPt_left_factors_through_chart1 (kbar : Type u) [Field kbar] :
      ∃ s : Spec (.of kbar) ⟶ Spec (.of (Away (projectiveLineBarGrading kbar) (X 1))),
        (ProjectiveLineBar.zeroPt kbar).left =
          s ≫ Proj.awayι (projectiveLineBarGrading kbar) (X 1)
              (MvPolynomial.isHomogeneous_X kbar 1) one_pos := by
    -- s is `Spec.map (eval X 1 ↦ 1, X 0 ↦ 0 on Away 𝒜 (X 1))`,
    -- which via Q2's iso is `Spec.map (X () ↦ 0 : k̄[u] →+* k̄)`.
    sorry
  ```

  Use `Proj.fromOfGlobalSections_morphismRestrict` (`Basic.lean:493`) to extract
  the chart-1 factorisation explicitly.

## Recommendation

**Strict landing order for iter-168's prover lane** (each step gated on the
previous):

1. **Land `projectiveLineBarAffineCover`** (Q1, ~15-20 LOC). Routine
   `affineOpenCoverOfIrrelevantLESpan` application. Closes a sub-prerequisite
   needed by Q3 and Q5.

2. **Land `homogeneousLocalizationAwayIso`** (Q2, **~60-90 LOC**, not 30).
   This is the long pole. **Do NOT under-estimate**: the previous iter-167 file
   set ~30 LOC and the prover ran out of budget. The `Quotient.lift` direction
   is what consumes the LOC. **Concrete sub-tasks**:
   - `invFun` via `MvPolynomial.aeval` (~5 LOC).
   - `toFun` via `Quotient.lift` (~20-25 LOC including the well-definedness
     hypothesis).
   - `map_one` / `map_mul` / `map_add` / `map_zero` (~10 LOC total — routine).
   - `left_inv` via `val_injective` (~20-25 LOC — the hardest piece).
   - `right_inv` via `MvPolynomial.induction_on` (~10 LOC).

3. **Land `gmScalingP1_chart0/1_ringMap` + `gmScalingP1_chart0/1`** (Q3, ~30 LOC).
   The two chart-side morphisms in `Scheme`, using `pullbackSpecIso` + the Q2 iso
   to bridge into `Spec (Away …)` and then `awayι`. Use `Over.homMk` to lift
   into `Over (Spec k̄)` cleanly.

4. **Land `gmScalingP1`'s body** (`Scheme.Cover.glueMorphisms`, Q4 + Q5,
   ~40-60 LOC). The cross-chart agreement reduces to a `pullbackSpecIso`-driven
   ring identity in `Localization.Away t ⊗ GmRing`; the `(1, 0)` case follows by
   symmetry from `(0, 1)`. Use `fin_cases` on `(x y : Fin 2)` then handle the 4
   cases: `(0, 0)` and `(1, 1)` trivial; `(0, 1)` the substantive one; `(1, 0)`
   the symmetric of `(0, 1)`.

5. **Land `zeroPt_left_factors_through_chart1`** (helper, ~15 LOC).
   `Proj.fromOfGlobalSections_morphismRestrict` to extract chart-1's image of
   `zeroPt`.

6. **Land `gmScalingP1_collapse_at_zero`** (Q6, ~30-50 LOC). Apply the chart-1
   factorisation of `zeroPt`, compose with `gmScalingP1`'s chart-1 component, and
   use `Spec.map` + `zero_tmul` to collapse to `Spec.map (eval X () ↦ 0)` —
   which is `toUnit ≫ zeroPt`.

**Total LOC estimate**: **~190-265 LOC** for steps 1-6. The previous iter-167
estimate of "30 LOC for the helper iso" was off by 2-3x; this estimate includes
the realistic Q2 cost.

**Key Mathlib idioms to cite verbatim in the prover's code**:
- `Proj.affineOpenCoverOfIrrelevantLESpan`
  (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic:324`)
- `Proj.awayι`, `Proj.fromOfGlobalSections`,
  `Proj.fromOfGlobalSections_morphismRestrict` (same file)
- `Scheme.Cover.glueMorphisms`, `Scheme.Cover.ι_glueMorphisms`, `hom_ext`
  (`Mathlib.AlgebraicGeometry.Gluing:436,457,448`)
- `AlgebraicGeometry.pullbackSpecIso` +
  `pullbackSpecIso_inv_fst/_snd/_hom_fst'/_hom_base`
  (`Mathlib.AlgebraicGeometry.Pullbacks:703-770`)
- `HomogeneousLocalization.Away.mk`,
  `HomogeneousLocalization.val_injective`,
  `HomogeneousLocalization.Away.isLocalization_mul`
  (`Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization:609,312,883`)
- `MvPolynomial.aeval`, `MvPolynomial.eval₂RingHom`, `MvPolynomial.algHom_ext`,
  `MvPolynomial.isHomogeneous_X` (`Mathlib.Algebra.MvPolynomial.*`)
- `IsLocalization.Away.invSelf`, `IsLocalization.Away.lift`
  (`Mathlib.RingTheory.Localization.Away.Basic:471`)
- `Algebra.TensorProduct.tmul_mul_tmul`, `TensorProduct.zero_tmul`
  (`Mathlib.RingTheory.TensorProduct.*`)
- `Scheme.Cover.pullback₁`, `AffineOpenCover.openCover`
  (`Mathlib.AlgebraicGeometry.Cover.MorphismProperty:177`,
   `Mathlib.AlgebraicGeometry.Cover.Open:128`)

**Reversal trigger**: if step 2 (`homogeneousLocalizationAwayIso`) exceeds ~120
LOC at any point, the prover should pause and reconsider whether to instead
upstream this as a single Mathlib PR (~80 LOC focused file
`HomogeneousLocalization.PolynomialQuotient`). The upstream PR would unblock
this iter, future iters' use cases, and is genuine missing Mathlib
infrastructure. But **do not bail on the project-side recipe before reaching
120 LOC** — the in-project version is what closes iter-168's lane.
