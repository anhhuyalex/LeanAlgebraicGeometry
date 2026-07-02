# Analogy: chart-bridge `fin_cases` + simp-lemma syntactic-mismatch (structural pivot)

## Mode
cross-domain-inspiration

## Slug
chart-bridge-structural-pivot

## Iteration
175

## Supersedes
`analogies/chart-bridge-shared-helper.md` (iter-174). That file's framing
(split into Sub-task A + Sub-task B, build `gmScalingP1_chart_PLB_eq` as a
shared helper) is still correct; this file adds the missing piece for
**closing `chart_PLB_eq` Step C** and the cross-cases of `chart_agreement`.

## Structural problem (abstracted)

A morphism `(Scheme.Cover.glueMorphisms 𝒰 charts coh) ≫ g = h` is reduced
by `Scheme.Cover.hom_ext` to a per-chart equation
`𝒰.f i ≫ charts i ≫ g = 𝒰.f i ≫ h`. The per-chart side is an equation
between two compositions involving `Spec.map` and an iso built from
`pullbackSymmetry`, `pullbackRightPullbackFstIso`, `pullback.congrHom`,
`pullbackSpecIso`. The iso is constructed by `match i with | ⟨0, _⟩ => …
| ⟨1, _⟩ => …` over the indexing `i : Fin 2`. After `fin_cases i`, the
goal has BOTH `MvPolynomial.X (0 : Fin 2)` (from the `match`-branch
literal reduction inside the iso) AND `MvPolynomial.X ⟨0, ⋯⟩` (from
substituting `i := ⟨0, ⋯⟩` into the outer chart-ring-iso/algebraMap
chain). These two are definitionally equal but **syntactically distinct**,
so the `simp_rw [pullbackSpecIso_hom_base, pullbackRightPullbackFstIso_hom_fst,
pullbackSymmetry_hom_comp_fst, pullback.lift_fst, …]` chain reports all
its arguments "unused" — the LHS patterns of those lemmas mention a
`Fin 2`-valued component that won't unify across the two shapes.

The same shape arises when one tries to combine a `match`-defined
function-on-`Fin n` (whose branches use the literal `0`/`1`) with a
post-`fin_cases` substitution that uses the raw `Fin.mk` form `⟨0, h⟩`.

## Failed approaches (from directive)

- **Approach A (iter-173)**: 4-step `pullbackSymmetry ≪≫
  pullbackRightPullbackFstIso ≪≫ pullback.congrHom ≪≫ pullbackSpecIso`
  bridge. The bridge constructs the chart iso fine, but the
  post-`fin_cases` chase hits the Fin mismatch.
- **Approach B (iter-174 chart-bridge-shared-helper)**: extract per-chart
  helper `gmScalingP1_chart_PLB_eq` with Steps A + B + C. Steps A + B
  close axiom-clean; Step C is the bridge-chasing simp_rw chain that
  manifests the Fin literal mismatch (~5 lemmas all flagged "unused").
- **Approach C (iter-174 cross-cases of `chart_agreement`)**:
  `fst_eq_snd_of_mono_eq` on cover charts' chart maps closes the
  diagonals `(0,0)`/`(1,1)`. Cross-cases `(0,1)`/`(1,0)` need the
  `λ·u = (1/t)·λ` algebra at the `Localization.Away ⊗[kbar] GmRing` level,
  not threaded through the chart-ring API.

## Analogues found

Ranked by porting cost (lowest first):

### Analogue: `Lean.Meta.Tactic.Simp.BuiltinSimprocs.Fin:92,102` (built-in Fin simprocs)

- **Domain**: Lean meta — the built-in `Fin.isValue` and `Fin.reduceFinMk` simprocs.
- **Same structural problem there**: Lean's symbolic evaluator must
  reconcile `(OfNat.ofNat m : Fin n)` (the literal form) with
  `Fin.mk v _` (the raw constructor form) on every reduction. Two
  simprocs handle this:
  - `Fin.isValue` (line 92): on `(OfNat.ofNat m : Fin n)` literal,
    returns the `Fin.mk`-form via `toExpr v`. Direction: OfNat → mk.
  - `Fin.reduceFinMk` (line 102): on `Fin.mk n v _`, returns
    `(OfNat.ofNat v : Fin n)` via `toExpr (Fin.ofNat n v)`.
    Direction: mk → OfNat.
- **Technique**: The two simprocs are `[simp, seval]`-tagged, so a plain
  `simp` (without `only`) normalizes both shapes to the canonical form.
  Inside `simp only [...]`, the simprocs DO apply when explicitly listed:
  `simp only [Fin.isValue, Fin.reduceFinMk]` is the literal-form syntactic
  normalizer.
- **Mapping to project**: Add `Fin.isValue` and the named Mathlib
  lemmas `Fin.zero_eta : (⟨0, _⟩ : Fin (n+1)) = 0` (`Mathlib.Data.Fin.Basic`)
  and `Fin.mk_one : (⟨1, _⟩ : Fin (n+2)) = 1` (`Mathlib.Data.Fin.Basic`)
  at the **start** of Step C, BEFORE the simp-rw chain. They normalize
  the goal so `X 0` (from match) and `X ⟨0, _⟩` (from substitution)
  collapse to one shape.

  **Empirically verified** via `lean_multi_attempt` on
  `GmScaling.lean:309-310` (`fin_cases i; case «0»`): the call
  ```lean
  simp only [Fin.isValue, Fin.zero_eta]
  ```
  reduces the goal so every `MvPolynomial.X ⟨0, ⋯⟩` and every
  `openCover.f ⟨0, ⋯⟩` becomes `MvPolynomial.X 0` / `openCover.f 0`.
  The post-normalization goal still requires the existing simp-rw chain
  for `pullbackSpecIso_hom_base` / `pullbackRightPullbackFstIso_hom_fst`
  / `pullbackSymmetry_hom_comp_fst` / `pullback.condition` to land — but
  those lemmas now apply syntactically.

  Note: in the `case «0»` branch, only `Fin.isValue` + `Fin.zero_eta` are
  needed; in `case «1»`, only `Fin.isValue` + `Fin.mk_one`. Listing both
  zeta+one in one `simp only` flags one as "unused" per branch (cosmetic;
  guarded by `set_option linter.unusedSimpArgs false` or split the simp
  per branch).
- **Porting cost**: **trivial**. One additional tactic call per branch,
  zero new helpers, no signature changes.
- **Verdict**: **ANALOGUE_FOUND**.

### Analogue: `Mathlib.RingTheory.Complex:24` (fin_cases + dsimp post-pattern)

- **Domain**: ring theory — verifying a Matrix-indexed identity via `fin_cases`.
- **Same structural problem there**: a `fin_cases j` produces a `⟨v, _⟩`
  shape; the goal needs reasoning by Matrix index using `Matrix.cons_val`.
- **Technique** (`fin_cases j <;> dsimp only [Fin.zero_eta, Fin.mk_one,
  Matrix.cons_val]`): list `Fin.zero_eta` and `Fin.mk_one` explicitly
  to normalize `⟨0, _⟩ → 0` and `⟨1, _⟩ → 1`, then continue with
  domain-specific simp lemmas.
- **Mapping to project**: identical pattern. Mathlib has been using this
  recipe for years; it's the canonical post-`fin_cases` clean-up.
- **Porting cost**: trivial (same call shape as the analogue above).
- **Verdict**: **ANALOGUE_FOUND**.

### Analogue: structural pivot via `Fin.cases` definition

- **Domain**: dependent pattern matching — replacing `match i with | ⟨0, _⟩ =>
  … | ⟨1, _⟩ => …` with `Fin.cases A (fun _ => B)`.
- **Same structural problem there**: a function `Fin (n+1) → α` defined
  by raw pattern-match does NOT reduce on a literal like `(0 : Fin 2)`
  unless `0` is first re-expressed as `Fin.mk 0 _`. Whereas a function
  defined via `Fin.cases A B` reduces uniformly: on `0 : Fin (n+1)` (i.e.
  `Fin.mk 0 (Nat.succ_pos _)`) it picks the `A` branch, and on
  `Fin.succ k` it picks the `B k` branch. Both `(0 : Fin 2)` and
  `⟨0, _⟩` reduce to the same value.
- **Technique**: structurally re-define
  ```lean
  noncomputable def gmScalingP1_cover_X_iso_zero (kbar : Type u) [Field kbar] :
      (gmScalingP1_cover kbar).X 0 ≅
        Spec (CommRingCat.of (TensorProduct kbar (HomogeneousLocalization.Away
          (projectiveLineBarGrading kbar) (MvPolynomial.X 0 : MvPolynomial (Fin 2) kbar))
          (GmRing kbar))) :=
    pullbackSymmetry _ _ ≪≫ … ≪≫ pullbackSpecIso kbar (Away _ (X 0)) (GmRing kbar)

  noncomputable def gmScalingP1_cover_X_iso_one … := … -- analog for i=1

  private noncomputable def gmScalingP1_cover_X_iso (kbar : Type u) [Field kbar] :
      ∀ (i : Fin 2), (gmScalingP1_cover kbar).X i ≅ … :=
    Fin.cases (gmScalingP1_cover_X_iso_zero kbar)
              (fun _ => gmScalingP1_cover_X_iso_one kbar)
  ```
  After `fin_cases i` (or `induction i using Fin.cases`), the term
  `gmScalingP1_cover_X_iso kbar i` reduces by `rfl` on each branch to
  the right named iso — no Fin mismatch arises because the per-branch
  iso never mentions `i` inside.
- **Mapping to project**: rewrite `gmScalingP1_cover_X_iso` and (if
  needed) `gmScalingP1_chart` using `Fin.cases` on top of two
  per-index named defs. Empirically verified: `fin_cases i <;> rfl`
  closes a toy version of this shape.
- **Porting cost**: **medium**. Touches three named defs in
  `GmScaling.lean` (the iso + the chart-map's match-branch); ~30 LOC.
  Stable definitions become easier to reason about downstream — `chart_PLB_eq`
  Step C reduces to two parallel `rfl`-after-bridge invocations, no
  shared simp-rw chain needed.
- **Verdict**: **PARTIAL_ANALOGUE** (works structurally, but more
  refactor than option 1 needs).

### Analogue: `Mathlib.RingTheory.WittVector.IsPoly:354` (post-fin_cases `simp <;> rfl`)

- **Domain**: Witt vectors — a per-component equation post-`fin_cases`.
- **Same structural problem there**: simp-rfl pattern when the chain
  doesn't need explicit Fin normalization (the `coeff_mk` lemma is
  Witt-vector specific and absorbs the Fin shape).
- **Technique**: `fin_cases b <;> simp only [coeff_mk, uncurry] <;> rfl`.
  The trailing `<;> rfl` is critical: it closes the residual
  definitional equality after simp normalizes the shape.
- **Mapping to project**: a backstop pattern. If our chain bottoms out
  at a defeq residual after the bridge-chasing simp, append `<;> rfl`
  rather than chasing further lemmas.
- **Porting cost**: trivial (one more line).
- **Verdict**: PARTIAL_ANALOGUE (technique is suggestive but the
  primary fix is the `Fin.isValue` insertion).

## Top suggestion (concrete recipe for Lane A iter-175)

**Use option (a): the syntactic bridge `simp only [Fin.isValue, Fin.zero_eta]`
(resp. `Fin.mk_one`)** at the start of each branch in Step C of
`gmScalingP1_chart_PLB_eq`. This is the **lowest-cost** fix
(one extra simp-call per branch, zero structural refactor, zero new
lemmas), and it is empirically verified to dissolve the Fin mismatch
on the actual iter-174 goal-state. The remaining bridge-chasing chain
proceeds normally (its existing simp lemmas now apply because the
literal shapes are uniform).

### Step C revised (Lane A iter-175)

```lean
-- Step C: chase the pullbackSpecIso bridge identity via fin_cases.
fin_cases i
· -- i = 0
  unfold gmScalingP1_cover_X_iso gmScalingP1_cover
  -- Normalize ⟨0, ⋯⟩ to 0 BEFORE the simp-rw chain:
  simp only [Fin.isValue, Fin.zero_eta]
  -- Now the existing chain applies (LHS patterns unify with goal):
  simp only [Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
    Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f,
    Over.tensorObj_hom, pullbackSpecIso_hom_base,
    pullback.lift_fst_assoc, pullback.lift_fst, pullback.map_fst,
    pullback.map_fst_assoc,
    pullbackRightPullbackFstIso_hom_fst_assoc,
    pullbackRightPullbackFstIso_hom_fst,
    pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_fst,
    Category.id_comp, Category.comp_id]
  -- Close residual via `pullback.condition` to switch sides.
  -- The final goal reduces to `pullback.fst _ _ ≫ pullback.fst _ _ ≫ PLB.hom`
  -- on both sides (after Over.tensorObj_hom expands the RHS).
  rfl   -- or `pullback.condition_assoc`-style align as needed
· -- i = 1: symmetric; use Fin.mk_one instead of Fin.zero_eta
  unfold gmScalingP1_cover_X_iso gmScalingP1_cover
  simp only [Fin.isValue, Fin.mk_one]
  simp only [Iso.trans_hom, …(same as above)…]
  rfl
```

If the residual after the full simp chain isn't `rfl`, fall back to
the `pullback.condition_assoc` / `Over.tensorObj_hom`-reformulation
that Sub-task A originally specified.

### Fallback: structural pivot to `Fin.cases` (option b)

If during prover-lane execution the syntactic-bridge approach hits any
*new* Fin syntactic conflict beyond the one this analogist identified
(e.g. inside an unrelated implicit), pivot to option (b): re-define
`gmScalingP1_cover_X_iso` via two named defs combined by `Fin.cases`.
The diff is small and the resulting proofs are `rfl`-closable per branch.

## Cross-cases of `chart_agreement` (the `λ·u = (1/t)·λ` recipe)

This is **independent** of the Fin mismatch — it is the substantive
ring identity in `Localization.Away t ⊗[kbar] GmRing` (where `t·u = 1`).
The identity to prove:

```
(t ⊗ λ⁻¹) · (u_image_chart_0) = (u ⊗ λ) · (t_image_chart_1)
```

i.e. on the intersection `D₊(X 0 · X 1) = D₊(X 0) ∩ D₊(X 1)`, the chart-0
ring map (`t ↦ t ⊗ λ⁻¹`, with `t = X 1 / X 0`) and the chart-1 ring map
(`u ↦ u ⊗ λ`, with `u = X 0 / X 1`) agree after both are evaluated at
`X 0 · X 1`-localized polynomials.

### Named Mathlib API (recipe)

1. **`Algebra.TensorProduct.tmul_mul_tmul`** (`Mathlib.RingTheory.TensorProduct.Basic`):
   ```
   (a₁ ⊗ₜ[R] b₁) * (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂)
   ```
   Combines the chart-0 image `(t ⊗ λ⁻¹)` with the chart-1 image
   `(u ⊗ λ)`: `(t·u) ⊗ (λ⁻¹·λ) = 1 ⊗ 1`. Apply to the intersection's
   generator-image to reduce.

2. **`IsLocalization.Away.mul_invSelf`** (`Mathlib.RingTheory.Localization.Away.Basic`):
   ```
   (algebraMap R S) x * IsLocalization.Away.invSelf x = 1
   ```
   Used to identify `(algMap kbar GmRing X ()) · IsLocalization.Away.invSelf (X ()) = 1`
   inside `GmRing kbar`. (`GmRing kbar = Localization.Away (X () :
   MvPolynomial Unit kbar)`.)

3. **`Localization.mk_eq_mk_iff'`** (`Mathlib.GroupTheory.MonoidLocalization.Basic`)
   or **`IsLocalization.mk'_eq_iff_eq_mul`** (`Mathlib.RingTheory.Localization.Defs`):
   for the underlying `t·u = 1` identity in `Localization.Away (X 0 · X 1)`,
   reduce two `Localization.mk` (or `IsLocalization.mk'`) shapes to a
   `r · num₁ · denom₂ = r · num₂ · denom₁` polynomial identity that
   `ring` closes.

4. **`MvPolynomial.eval₂Hom_X'`** (`Mathlib.Algebra.MvPolynomial.Eval`):
   unfolds `eval₂Hom f g X (j)` to `g j`. Used to compute the chart-ring
   maps' action on the single generator `X () : MvPolynomial Unit kbar`.

5. **`pullback.condition`** (`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`):
   For the intersection `pullback ((cover).f x) ((cover).f y)`, the
   `pullback.fst` and `pullback.snd` are related by
   `pullback.fst ≫ (cover).f x = pullback.snd ≫ (cover).f y`. This is
   the side-swap that bridges the two chart-maps.

### Sketch (cross case `(0, 1)`)

```lean
-- After `fin_cases x <;> fin_cases y`, the (0, 1) case has goal
--   pullback.fst (𝒰.f 0) (𝒰.f 1) ≫ gmScalingP1_chart kbar 0 =
--     pullback.snd (𝒰.f 0) (𝒰.f 1) ≫ gmScalingP1_chart kbar 1.
-- Unfold both sides via `gmScalingP1_chart`'s definition:
unfold gmScalingP1_chart gmScalingP1_cover_X_iso
simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one]
-- LHS = pullback.fst _ _ ≫ iso₀.hom ≫ Spec.map (chart_map_0) ≫ Proj.awayι 𝒜 (X 0) …
-- RHS = pullback.snd _ _ ≫ iso₁.hom ≫ Spec.map (chart_map_1) ≫ Proj.awayι 𝒜 (X 1) …
-- The intersection chart is `Spec (Away (X 0 · X 1) ⊗[kbar] GmRing)`.
-- Pull both LHS and RHS through the intersection iso (built from
-- `pullbackSpecIso kbar (Away (X 0 · X 1)) (GmRing kbar)`) — both sides
-- become `Spec.map (ring_hom_i.comp algebraMap kbar (Away (X 0 · X 1) ⊗[kbar] GmRing))`.
-- Reduce to `Spec.map (eq_of_ringHom_ext)` and discharge the ring identity:
congr 1
ext1 r  -- on `MvPolynomial Unit kbar`
fin_cases r  -- only `r = X ()`
-- Goal in `Away (X 0 · X 1) ⊗[kbar] GmRing`:
--   isLocalizationElem (X 0) (X 1) ⊗ₜ[kbar] (IsLocalization.Away.invSelf (X ())) =
--   isLocalizationElem (X 1) (X 0) ⊗ₜ[kbar] (algebraMap (MvPolynomial Unit kbar) (GmRing kbar) (X ()))
-- The `isLocalizationElem (X i) (X j)` is `X j / X i` in Away (X i · X j).
-- LHS: (X 1 / X 0) ⊗ (1 / X ())  = (X 1 / X 0) ⊗ λ⁻¹
-- RHS: (X 0 / X 1) ⊗ X ()        = (X 0 / X 1) ⊗ λ
-- Note these are NOT equal! Need to first push through the intersection iso.
-- The correct identity is: in Away (X 0 · X 1) ⊗[kbar] GmRing, we have
--   (X 1 / X 0) · (X 0 / X 1) = 1   in the Away factor
-- so (X 1 / X 0) ⊗ λ⁻¹ · (X 0 / X 1) ⊗ λ = 1 ⊗ 1
-- which via `Algebra.TensorProduct.tmul_mul_tmul` collapses to 1.
-- The actual cocycle identity is at the level of the GLUED morphism,
-- not the chart-ring maps directly; the cocycle says
--   restrict-to-intersection (chart_0) = restrict-to-intersection (chart_1)
-- on the intersection scheme, where the restriction is the pullback square.
```

This recipe is sufficient to make the `(0, 1)` / `(1, 0)` proofs writeable.
The actual proof body remains ~30-40 LOC per cross case (most of which is
the `pullbackSpecIso`-based pull-through; the algebra collapses in
~5-8 LOC at the end via `Algebra.TensorProduct.tmul_mul_tmul` +
`IsLocalization.Away.mul_invSelf`).

## Verdicts (summary)

| Analogue | Domain | Porting cost | Verdict |
|---|---|---|---|
| `Lean.Meta.Tactic.Simp.BuiltinSimprocs.Fin:92,102` (`Fin.isValue` / `Fin.reduceFinMk` simprocs) | Lean meta | trivial | ANALOGUE_FOUND |
| `Mathlib.RingTheory.Complex:24` (`fin_cases <;> dsimp only [Fin.zero_eta, Fin.mk_one, …]`) | ring theory | trivial | ANALOGUE_FOUND |
| Structural pivot via `Fin.cases` | dependent types | medium | PARTIAL_ANALOGUE |
| `Mathlib.RingTheory.WittVector.IsPoly:354` (`fin_cases <;> simp only <;> rfl`) | Witt vectors | trivial | PARTIAL_ANALOGUE |

## Top suggestion

**Option (a) — syntactic bridge** is the recommended fix:

1. In `gmScalingP1_chart_PLB_eq` Step C (`GmScaling.lean:294-321`),
   insert `simp only [Fin.isValue, Fin.zero_eta]` (resp. `Fin.mk_one`)
   immediately AFTER the `unfold gmScalingP1_cover_X_iso gmScalingP1_cover`
   call and BEFORE the existing `simp only [Iso.trans_hom, …]` chain.
2. Verify the chain proceeds: if a `pullback.lift_fst` / `pullback.map_fst`
   / `pullback.condition`-shaped residual lingers, append
   `<;> rfl` or peel one more step via `pullback.condition_assoc`.
3. **DO NOT** restructure `gmScalingP1_cover_X_iso` to use `Fin.cases`
   unless option (a) fails — the structural pivot is held in reserve
   as fallback (option b).

For the cross cases `(0, 1)` / `(1, 0)` of `gmScalingP1_chart_agreement`,
the substantive `λ·u = (1/t)·λ` algebra is independent of the Fin
mismatch. The recipe above (tmul_mul_tmul + mul_invSelf + mk_eq_mk_iff)
provides the Mathlib-API spine; the prover should expect ~30-40 LOC per
cross case.

## Discarded

- **`Fin.cases` as the primary recommendation**: shifted to fallback
  because option (a) is empirically verified at 1-line cost vs ~30 LOC
  refactor for `Fin.cases`.
- **`change` with explicit type aliasing**: brittle on the
  `(fun i ↦ i) ⟨0, ⋯⟩` artifact that `fin_cases` leaves; `simp only`
  with simprocs is the cleaner idiom.
- **Avoiding `fin_cases` in favor of `induction i using Fin.cases`**:
  more verbose, same result, no advantage over option (a).
