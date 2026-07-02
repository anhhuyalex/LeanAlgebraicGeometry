# Analogy: Stacks 00TT (smooth ⟹ regular) + coheight-to-Krull-dim bridge for `CodimOneExtension`

## Mode
api-alignment

## Slug
stacks-00tt-coheight

## Iteration
182

## Question

`Albanese/CodimOneExtension.lean` carries 3 sorries blocking the
critical-path Lemma 3.3 codim-1 extension argument:

1. `extend_of_codimOneFree_of_smooth` (Milne 3.1) — the codim-≥2 extension to
   a proper target.
2. `indeterminacy_pure_codim_one_into_grpScheme` (Milne Lemma 3.3) — the
   diagonal/difference-map argument.
3. Internal `hreg_dim` inside `smooth_codim_one_maximalIdeal_isPrincipal_and_ne_bot`
   — the conjunction `IsRegularLocalRing stalk ∧ ringKrullDim stalk = 1`.

The directive flags three Mathlib-gap candidates:
- **Stacks 00TT** — smooth ⟹ regular stalks.
- **Coheight-to-Krull-dim** — `Order.coheight z = 1 ⟹ ringKrullDim
  (X.presheaf.stalk z) = 1`.
- **Codim-1 valuative criterion** — rational map indeterminacy is codim ≥ 2.

## Project artifact(s)
- `AlgebraicJacobian/Albanese/CodimOneExtension.lean`:222-271 — private
  helper `smooth_codim_one_maximalIdeal_isPrincipal_and_ne_bot` (internal
  `hreg_dim` sorry).
- `AlgebraicJacobian/Albanese/CodimOneExtension.lean`:356-368 —
  `extend_of_codimOneFree_of_smooth` (bare sorry).
- `AlgebraicJacobian/Albanese/CodimOneExtension.lean`:397-411 —
  `indeterminacy_pure_codim_one_into_grpScheme` (bare sorry).
- `AlgebraicJacobian/RiemannRoch/WeilDivisor.lean`:148-151 — the
  `[Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]` instance argument on
  `Scheme.RationalMap.order`, gated on the same coheight bridge.

## Decisions identified

### Decision 1: Stacks 00TT — does Mathlib have `Algebra.Smooth k A → IsRegularLocalRing (A_p)`?

- **Mathlib idiom (NEGATIVE)**: Mathlib's `RegularLocalRing` lives in
  `Mathlib.RingTheory.RegularLocalRing.Defs` (79 LOC, a single file).
  Cite: `.lake/packages/mathlib/Mathlib/RingTheory/RegularLocalRing/Defs.lean:1–79`.
  The class `IsRegularLocalRing` extends `IsLocalRing + IsNoetherianRing +
  (maximalIdeal R).spanFinrank = ringKrullDim R`.

  Direct LSP verification:
  - `lean_loogle "IsRegularLocalRing"` returns **14 hits, all confined to
    `RegularLocalRing/Defs.lean`** — there is no `Algebra.Smooth →
    IsRegularLocalRing` or `Algebra.Smooth → IsRegularRing` declaration.
  - `grep -rn "IsRegularLocalRing\|IsRegularRing"
    .lake/packages/mathlib/Mathlib/AlgebraicGeometry` returns **0 hits** —
    no scheme-level smoothness-to-regularity bridge.
  - `Mathlib.RingTheory.Smooth.Locus` characterizes `smoothLocus R A` as
    `(Module.support A (H1Cotangent R A))ᶜ ∩ Module.freeLocus A Ω[A⁄R]`
    (Cite: `Locus.lean:57`) — this captures the H¹-vanishing + free
    Kähler-differentials side of regularity but does NOT export an
    `IsRegularLocalRing` instance.

- **Project's current path**: typed `sorry` packaged as the conjunction
  `hreg_dim : IsRegularLocalRing stalk ∧ ringKrullDim stalk = 1`
  (`CodimOneExtension.lean:242`).
- **Gap**: divergent-and-unavoidable — Mathlib does not provide the
  implication at the pinned commit `b80f227`. This is a load-bearing
  Stacks tag (00TT) that has not been formalized.
- **Cost of divergence**: substantial. The classical Stacks 00TT proof
  needs:
  - `Algebra.Smooth k A`, `k` field ⟹ `Ω_{A/k}` finitely generated
    projective (Mathlib has this via `Algebra.Smooth.flat` +
    `smoothLocus_eq_compl_support_inter`).
  - At a closed point `p ∈ Spec A` with residue field `κ = κ(p)`, the rank
    of `Ω_{A/k} ⊗ κ` equals the relative dimension and equals
    `finrank κ ((maximalIdeal A_p)/(maximalIdeal A_p)²)` (the cotangent
    space).
  - For smooth `A/k` of pure dimension `d`, `ringKrullDim A_p = d` and
    `finrank cotangent = d`, hence by Mathlib's
    `IsRegularLocalRing.iff_finrank_cotangentSpace` (Cite:
    `RegularLocalRing/Defs.lean:65`), `IsRegularLocalRing A_p`.

  Estimated LOC for a project-side build of Stacks 00TT at the algebra
  level: **~200–300 LOC**, spanning `Module.finrank Ω ⊗ κ = relativeDim`
  + `ringKrullDim_eq_relativeDim` (Stacks 00OS) + cotangent-space
  identification + the `iff_finrank_cotangentSpace` discharge.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**. Genuine upstream gap; not
  approachable via a small project helper.

### Decision 2: Coheight-to-Krull-dim bridge — `Order.coheight z = ringKrullDim (X.presheaf.stalk z)`

- **Mathlib idiom — pieces exist, the *assembly* is project-side**.
  Concretely:

  - **Convention reconciliation**: `specializationPreorder` (Mathlib's
    spec preorder on a topological space, cite:
    `.lake/packages/mathlib/Mathlib/Topology/Defs/Filter.lean:228`)
    uses `x ≤ y ↔ y ⤳ x`, i.e. *the generic point is maximal*. On
    `Spec R`, this matches the *dual* of the `PrimeSpectrum R` natural
    inclusion order: `spec_le_iff` (Cite:
    `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/AffineSpace.lean:438-447`)
    establishes `p ≤ q (Spec R) ↔ q.asIdeal ≤ p.asIdeal (PrimeSpectrum)`
    and gives the example `Preorder (Spec R) = Preorder (PrimeSpectrum R)ᵒᵈ`.

  - **`Order.coheight` transports through `OrderIso`**:
    `coheight_orderIso : ∀ (f : α ≃o β) (x : α), coheight (f x) = coheight x`
    (Cite:
    `.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:335-336`).

  - **`Order.height (PrimeSpectrum) = ringKrullDim (Localization.AtPrime)`**:
    `IsLocalization.AtPrime.ringKrullDim_eq_height` (Cite:
    `.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:341-348`):
    ```
    theorem IsLocalization.AtPrime.ringKrullDim_eq_height (I : Ideal R)
        [I.IsPrime] (A : Type*) [CommRing A] [Algebra R A]
        [IsLocalization.AtPrime A I] : ringKrullDim A = I.height
    ```
    Combined with `Ideal.height_eq_primeHeight` (Cite:
    `Mathlib.RingTheory.Ideal.Height:45`) and
    `Ideal.primeHeight = Order.height (in PrimeSpectrum)` (Cite:
    `Mathlib.RingTheory.Ideal.Height:37-38`), we get
    `ringKrullDim (Localization.AtPrime p) = Order.height ⟨p, _⟩`
    (in `PrimeSpectrum R`).

  - **Affine-stalk localization**: `IsAffineOpen.isLocalization_stalk`
    (Cite:
    `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/AffineScheme.lean:806-813`):
    ```
    theorem isLocalization_stalk (x : U) :
        IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal
    ```

  - **Existence of affine open**: `exists_isAffineOpen_mem_and_subset`
    (Cite: `AffineScheme.lean:271`).

  - **Generizations stay in open subsets**: Generic property — if `U`
    open and `x ∈ U`, every generization `y ⤳ x` is in `U` (because
    opens are stable under generization: `y` is in every open containing
    `x`). This is `IsOpen.specializes_iff` style. Mathlib has
    `Specializes.mem_open` (Cite: `Topology.Inseparable:96`):
    `h : x ⤳ y → IsOpen s → y ∈ s → x ∈ s` — i.e. if `x ⤳ y` (so
    `y ∈ closure({x})`) and `y ∈ s` open, then `x ∈ s`.
    In spec preorder terms: `y ≤ x` (= `x ⤳ y`) and `y ∈ U` open ⟹
    `x ∈ U`. So every strict generization of a point in an open belongs
    to that open. ✓ (This lets `Order.coheight z` in `X.carrier` reduce
    to `Order.coheight z` in `U` with the subspace topology.)

- **Project's current path**: workaround — thread
  `[Ring.KrullDimLE 1 (X.presheaf.stalk Y.point)]` as an explicit
  instance argument on `Scheme.RationalMap.order`
  (`WeilDivisor.lean:148-151`) and an internal `sorry` conjunction in
  `CodimOneExtension.lean:242`. The bridge has been pinned as a
  "Mathlib-upstream-pending gap" in iter-175's
  `analogies/dvr-rationalmap-order.md` Decision 3, but no project-side
  helper was attempted.

- **Gap**: divergent-but-fillable-project-side. **Mathlib does NOT ship
  the direct bridge `Order.coheight z = ringKrullDim (stalk z)` for a
  scheme point `z : X.carrier`**, but every prerequisite is present.
  Project-side LOC estimate: **~60–100 LOC** (broken down below).

- **Cost of divergence**: low (project-side build is tractable this
  iter); high if we let the workaround propagate, because
  every downstream codim-1 lemma will need to thread the explicit
  `[Ring.KrullDimLE 1 _]` instance argument by hand.

- **Verdict**: **PROCEED — project-side scaffold**, do NOT block on
  Mathlib upstream. The bridge is a clean ~60–100 LOC standalone helper
  whose value extends far beyond this file (it also lets
  `Scheme.RationalMap.order` drop its explicit `[Ring.KrullDimLE 1 _]`
  argument).

### Decision 3: Codim-1 valuative criterion — "rational map indeterminacy is codim ≥ 2"

- **Mathlib idiom**: `Mathlib.AlgebraicGeometry.ValuativeCriterion`
  (Cite: `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ValuativeCriterion.lean:1-200`)
  provides:
  - `ValuativeCommSq f` — a structure for a valuative commutative square
    `Spec K → Y; Spec R → X; f : X → Y` with `R` a valuation ring.
  - `ValuativeCriterion.Existence`, `.Uniqueness` — the existence/uniqueness
    morphism properties.
  - `IsProper.eq_valuativeCriterion`, `UniversallyClosed.eq_valuativeCriterion`,
    `IsSeparated.eq_valuativeCriterion` — properness/separatedness iff
    qc(qs)/finite-type + valuative criterion.

  Mathlib has the **machinery** for proving things via valuative
  criteria, but does NOT package the specific Hartshorne/Milne lemma
  "rational map from nonsingular variety to proper target has
  indeterminacy of codim ≥ 2". That lemma is a Stacks-0BX5-style
  Hartshorne II.4.4 result and is not formalized at commit `b80f227`.

- **Project's current path**: bare `sorry` on both
  `extend_of_codimOneFree_of_smooth` (which by hypothesis already has
  codim-1 absent, so it only needs the codim-≥2 extension via Auslander-
  Buchsbaum / depth-2) and `indeterminacy_pure_codim_one_into_grpScheme`
  (which uses the diagonal/difference-map argument that ultimately
  reduces to the valuative criterion at codim-1 points).

- **Gap**: divergent — Mathlib has the underlying valuative criterion
  but not the codim-1-indeterminacy packaging. Project-side construction
  is substantial (the diagonal/difference-map argument is multi-iter
  work) and is NOT primarily a coheight or 00TT problem — it cycles
  through `localRing_dvr_of_codim_one` (Decision 1 + 2) as ONE input,
  but the bulk is the construction of the rational difference map
  `Φ : X × X ⇢ G` and the pole-divisor analysis.

- **Cost of divergence**: high. The full Milne 3.3 construction is
  **~300–500 LOC** of project-side new infrastructure (the
  difference-map factorization, the pole-divisor pullback, the
  intersection with the diagonal). This is multi-iter scope, not
  resolvable by an api-alignment recipe.

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (in spirit) — Mathlib doesn't
  package the lemma, and the project-side build is a separate multi-iter
  sub-project. The valuative criterion machinery in Mathlib is a
  *building block*, not a drop-in.

## Recommendation

### Phasing the three sorries

The three sorries decouple cleanly:

| Sorry | Primary blocker | Recommended action this iter |
|---|---|---|
| `hreg_dim` internal | Decision 1 (00TT — Mathlib gap) AND Decision 2 (coheight bridge — project-side fillable) | **Build the coheight scaffold**; refactor `hreg_dim` to isolate the 00TT half |
| `extend_of_codimOneFree_of_smooth` (codim-≥2 extension) | Auslander-Buchsbaum + depth-≥2 reflexive extension | Defer; gated on Lane G's `IsRegularLocalRing → IsDomain` and depth-of-SES progress |
| `indeterminacy_pure_codim_one_into_grpScheme` | Diagonal/difference-map construction (300–500 LOC project-side) | Defer; multi-iter sub-project, not iter-182 scope |

### Decision 2 scaffold — the ONE sorry to attack this iter

Add a new file `AlgebraicJacobian/CodimOneExtension/CoheightBridge.lean`
(or fold into `RiemannRoch/WeilDivisor.lean` near L160 where the
`Scheme.IsRegularInCodimensionOne` class already lives). The intended
content:

```lean
/-- **Open subsets preserve `Order.coheight`** for points of a
topological space carrying the specialisation preorder, since every
generization of a point in an open subset lies in that open.

The image `Subtype.val '' (Set.Iio z₀)` (= strict generizations of `z`
inside `U`) is in bijection with the strict generizations of `z` in `X`
when `U` is open. -/
lemma Order.coheight_eq_of_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    (z : X) (hz : z ∈ U) :
    Order.coheight (α := X) z = Order.coheight (α := U) ⟨z, hz⟩ := by
  -- Both sides equal the supremum over strict-generization chains.
  -- Every chain `z = a₀ < a₁ < ... < aₙ` in X with `a₀ = z ∈ U` has
  -- every `aᵢ ∈ U` by `Specializes.mem_open` (since `aᵢ ⤳ z` for all `i`,
  -- and U open contains z, hence contains each aᵢ).
  -- The matching chain in U via Subtype.val.
  sorry  -- ~20 LOC: forward direction via `Subtype.val ⁻¹'`, backward via
         -- `Specializes.mem_open`.

/-- **The specialization preorder on `Spec R` is the dual of the
inclusion preorder on `PrimeSpectrum R`.** This is folklore in
`Mathlib.AlgebraicGeometry.AffineSpace` (cf. `spec_le_iff` L438-447).
Coheight in the dual equals height in the original. -/
lemma Order.coheight_spec_eq_height_primeSpectrum
    {R : CommRingCat} (p : Spec R) :
    Order.coheight p = Order.height (α := PrimeSpectrum R) p := by
  -- Use `coheight_orderIso` with the order-iso `Spec R ≃o PrimeSpectrum Rᵒᵈ`
  -- (which exists by `spec_le_iff`) and `height_toDual`.
  sorry  -- ~10 LOC.

/-- **Coheight-to-Krull-dim bridge for a scheme point.** Combines:
- existence of affine open via `exists_isAffineOpen_mem_and_subset`,
- coheight transport along open immersion (`coheight_eq_of_isOpenEmbedding`),
- Spec/PrimeSpectrum order duality (`coheight_spec_eq_height_primeSpectrum`),
- `IsLocalization.AtPrime.ringKrullDim_eq_height` +
  `IsAffineOpen.isLocalization_stalk` for the algebraic side.
-/
lemma AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_coheight
    (X : Scheme.{u}) (z : X) :
    ringKrullDim (X.presheaf.stalk z) = Order.coheight z := by
  -- 1. Pick affine open U ∋ z.
  obtain ⟨U, hU, hzU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) (by simp)
  -- 2. Let p = primeIdealOf z (in Γ(U)).
  set p := hU.primeIdealOf ⟨z, hzU⟩
  -- 3. Stalk is the localization at p.
  haveI := hU.isLocalization_stalk ⟨z, hzU⟩
  -- 4. ringKrullDim stalk = p.height (via `IsLocalization.AtPrime.ringKrullDim_eq_height`).
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (S := X.presheaf.stalk z) p.asIdeal _]
  rw [Ideal.height_eq_primeHeight]
  -- 5. p.primeHeight = Order.height (in PrimeSpectrum) — by definition.
  unfold Ideal.primeHeight
  -- 6. Identify with coheight of z in U.carrier via the `Spec ≃o PrimeSpectrumᵒᵈ` order iso
  --    (i.e. apply `coheight_spec_eq_height_primeSpectrum` followed by
  --    `coheight_eq_of_isOpenEmbedding` to lift back to X.carrier).
  sorry  -- ~30 LOC of assembly using `hU.isoSpec`, `coheight_orderIso`,
         -- `coheight_eq_of_isOpenEmbedding`, and the dual-order identification.

/-- Bridge instance: `Order.coheight z = 1` synthesises `Ring.KrullDimLE 1`
on the stalk, so downstream lemmas (e.g. `Scheme.RationalMap.order`) no
longer need the explicit `[Ring.KrullDimLE 1 _]` instance argument. -/
instance ringKrullDimLE_of_coheight_eq_one
    (X : Scheme.{u}) (z : X) (hz : Order.coheight z = 1) :
    Ring.KrullDimLE 1 (X.presheaf.stalk z) := by
  rw [Ring.KrullDimLE]  -- or appropriate API
  rw [Scheme.ringKrullDim_stalk_eq_coheight, hz]
  -- coheight = 1 ⟹ KrullDimLE 1. ~10 LOC.
  sorry
```

**Total scaffold LOC**: ~60–100 LOC.

**Risk on the scaffold body**: the three named sorries are routine. The
hardest is `coheight_eq_of_isOpenEmbedding`, which is generic topology
that may well already be in Mathlib under a different name (worth a
focused `lean_loogle "Order.coheight, IsOpen"` search before scaffolding).

### Refactor of `hreg_dim` after the scaffold lands

The current `CodimOneExtension.lean:242` conjunction:

```lean
have hreg_dim : IsRegularLocalRing (X.left.presheaf.stalk z) ∧
                ringKrullDim (X.left.presheaf.stalk z) = 1 := sorry
```

becomes:

```lean
have hdim : ringKrullDim (X.left.presheaf.stalk z) = 1 := by
  rw [Scheme.ringKrullDim_stalk_eq_coheight, _hz]  -- closed by the scaffold
  rfl  -- (1 : ℕ∞) = 1
have hreg : IsRegularLocalRing (X.left.presheaf.stalk z) := sorry
  -- ↑ this remains — it's the irreducible Stacks 00TT half.
```

After the refactor, `hreg_dim` is *not* closed — but its content has
been **halved**, and the remaining sorry is precisely the named Mathlib
gap. This is a strict improvement: the comment "neither half ships in
Mathlib" downgrades to "one half ships, one half does not", and the
next iter's prover lane on Stacks 00TT becomes a single named target.

### Should iter-182 dispatch a `CodimOneExtension` prover lane?

**No on the file directly — yes on the new `CoheightBridge` scaffold.**

- Direct prover lane on `CodimOneExtension.lean`'s three sorries is
  blocked: two are multi-iter sub-projects (00TT and codim-1 valuative
  criterion); one (`extend_of_codimOneFree_of_smooth`) is gated on
  Lane G's depth-and-Cohen-Macaulay chain in `AuslanderBuchsbaum.lean`.
- Project-side scaffold of the coheight bridge IS movable this iter and
  unlocks both `Scheme.RationalMap.order`'s threading hygiene (drop the
  explicit `[Ring.KrullDimLE 1 _]` argument) and downstream Riemann-Roch
  chapters that use the same threading.

### Mathlib upstream opportunities (parallel to the loop)

Two small PRs that would simplify the project's API surface:

1. **`Order.coheight_eq_of_isOpenEmbedding`** — generic topology lemma
   (~20 LOC standalone). Natural home:
   `Mathlib.Order.KrullDimension` or
   `Mathlib.Topology.SpectralSpace.Basic` next to the existing
   `Specializes.mem_open`.

2. **`AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_coheight`** —
   the scheme-level bridge itself (~40 LOC standalone). Natural home:
   `Mathlib.AlgebraicGeometry.Stalk` or a new
   `Mathlib.AlgebraicGeometry.Coheight` file.

Both are tractable upstream PRs the mathematician could submit in
parallel with the loop's project-side build. Neither blocks the loop.

### Strategic note on Stacks 00TT

Building Stacks 00TT inside the project (~200–300 LOC) is a separate
sub-project that should NOT be packaged together with the coheight
bridge. If iter-183+ wants to attack 00TT, the right framing is a
standalone Lane analogous to `AuslanderBuchsbaum.lean` — a new
`AlgebraicJacobian/Albanese/SmoothToRegular.lean` (~3 helpers) that
inputs `Algebra.Smooth k A` over a field + `[FinitePresentation k A]`
and outputs `IsRegularLocalRing (Localization.AtPrime p)` for every
`p`. The key sub-lemmas (each `~50–80 LOC`):

1. `Algebra.Smooth.cotangent_finrank_eq_relativeDim` — at every closed
   point, `finrank κ (Ω_{A/k} ⊗ κ) = relativeDim`.
2. `Algebra.Smooth.ringKrullDim_localization_eq_relativeDim` — for
   smooth `A/k` of pure dimension `d`, every localization has
   `ringKrullDim = d`.
3. Discharge: combine (1)+(2) with
   `IsRegularLocalRing.iff_finrank_cotangentSpace`.

This is the natural next sub-project AFTER `AuslanderBuchsbaum`'s
`IsDomain` gap and the coheight bridge land.
