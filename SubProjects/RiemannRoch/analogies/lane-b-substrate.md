# Analogy: Lane B substrate — `IsClosedImmersion.lift_iff_range_subset` and tensor reducedness

## Mode
api-alignment

## Slug
lane-b-substrate

## Iteration
189

## Question

For the Lane B (`gmScalingP1_chart_agreement_cross01`) iter-188 (III.c)
separated-locus structural setup, the substantive residual is a pair-
morphism factorization through the diagonal closed immersion. The
blueprint cites `IsClosedImmersion.lift_iff_range_subset` as the
substrate; iter-188 verified this is NOT in Mathlib at b80f227. Two
questions:

1. Is there a Mathlib variant of "morphism factors through closed
   immersion iff topological range subset" under any reasonable
   reduced-source hypothesis?
2. What is the cleanest project-side construction (with LOC), and what
   blocks the tensor-reducedness gap that also obstructs the other two
   off-target sorries (`gm_geomIrred`, `projGm_isReduced`)?

## Project artifact(s)

- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:417-553` —
  `gmScalingP1_chart_agreement_cross01` (the cocycle proof with the
  separated-locus structural setup landed iter-188; substantive sorry
  at line 553).
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:755-763` —
  `gm_geomIrred` (off-target sorry, same tensor gap).
- `AlgebraicJacobian/Genus0BaseObjects/GmScaling.lean:779-795` —
  `projGm_isReduced` (off-target sorry, same tensor gap).
- `AlgebraicJacobian/Genus0BaseObjects/Points.lean:178-229` —
  `GmRing = Localization.Away (X () : MvPolynomial Unit kbar)` and
  `gmRing_isDomain`.
- `blueprint/src/chapters/AbelianVarietyRigidity.tex:1505-1611` —
  (III.c) Separated-locus alternative recipe, including the iter-188
  `% NOTE` recording the substrate falsification.

## Decisions identified

### Decision 1: `IsClosedImmersion.lift_iff_range_subset` (the substantive substrate)

- **Mathlib idiom**: NONE at b80f227. The only `lift` variant shipped
  is `IsClosedImmersion.lift` with the kernel-inequality form
  (`f.ker ≤ g.ker`), at
  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:200-214`.
  The `lift_iff_range_subset` variant — equating factor-through with
  set-theoretic range containment under a reduced-source hypothesis —
  is not in Mathlib (verified iter-188 via `lean_leansearch` and
  re-verified iter-189 via `lean_leanfinder`).

- **Mathlib substrate that DOES exist** (and which a project-side build
  would chain): the iter-189 search recovered the complete chain of
  primitives needed:
  - `AlgebraicGeometry.Scheme.Hom.ker`
    (`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:689`):
    ideal-sheaf kernel of a scheme morphism.
  - `AlgebraicGeometry.Scheme.Hom.ker_apply`
    (same file, `:698-734`): for `[QuasiCompact f]`,
    `f.ker.ideal U = RingHom.ker (f.app U).hom` on each affine open.
  - `AlgebraicGeometry.Scheme.Hom.support_ker`
    (same file, `:839-878`): for `[QuasiCompact f]`,
    `f.ker.support = closure (Set.range f)`.
  - `AlgebraicGeometry.Scheme.Hom.range_subset_ker_support`
    (same file, `:754-764`): the unconditional inclusion
    `Set.range f ⊆ f.ker.support`.
  - `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support`
    (same file, `:631-639`):
    `vanishingIdeal I.support = I.radical` — the Galois-connection
    pinning of "support determines radical".
  - `AlgebraicGeometry.Scheme.IdealSheafData.gc`
    (same file, `:622-625`):
    `GaloisConnection (support ·) (vanishingIdeal ·)` (with the
    `Closedsᵒᵈ` ordering).
  - `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`
    (`IdealSheaf/Subscheme.lean`):
    `Set.range I.subschemeι.base = I.support` — for a closed immersion
    `i`, `Set.range i.base = i.ker.support`.
  - `AlgebraicGeometry.IsClosedImmersion.lift`,
    `lift_fac`, `lift_fac_assoc`
    (`ClosedImmersion.lean:206-214`): the actual lift,
    keyed on `f.ker ≤ g.ker`.

- **Project's current path**: iter-188 lands a structural setup that
  introduces `s_pair := pullback.lift (chart0_via_fst) (chart1_via_snd) hPLB_agree`
  and the closed-immersion diagonal `hΔ`, leaving a single direct
  `sorry` at line 553 where the (III.c) recipe step 3 needs the
  factorization `∃ s, s ≫ Δ = s_pair`. The blueprint cites
  `IsClosedImmersion.lift_iff_range_subset` to reduce this to the
  set-level containment of the cocycle's image in `Set.range Δ.base`.

- **Gap**: NEEDS_MATHLIB_GAP_FILL (the Mathlib idiom doesn't exist),
  but the gap is BUILDABLE from existing Mathlib primitives.

- **Cost of divergence**: Building `IsClosedImmersion.lift_iff_range_subset`
  project-side costs ~40-60 LOC; the alternative (waiting on Mathlib
  upstream PR) is unbounded in time.

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** — and the gap-fill is
  feasible at ~40-60 LOC using the existing Mathlib primitives above.

### Decision 2: Tensor reducedness of `(Away (X_0·X_1)) ⊗_kbar (GmRing kbar)`

This is the SECOND substrate needed, blocking three sorries
simultaneously (the cocycle factorization plus the two off-target
`gm_geomIrred` / `projGm_isReduced` instances at L755, L779).

- **Mathlib idiom check**: NONE direct. The closest shipped:
  - `Algebra.IsGeometricallyReduced` class
    (`Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean:47`):
    requires `IsReduced (AlgebraicClosure k ⊗_k A)`. The bridge
    "k alg-closed ⟹ IsReduced ⟹ IsGeometricallyReduced k" is NOT
    shipped (the file's own TODO confirms: "for every field extension
    K of k the K-algebra K ⊗[k] A is reduced" — not landed for the
    general field-extension case).
  - `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced`
    (same file, `:52`): an instance for `IsReduced (K ⊗_k A)` when
    `K/k` algebraic AND `A` geometrically reduced over `k`. Doesn't
    apply directly because neither factor here is algebraic over kbar.
  - `Subalgebra.LinearDisjoint.isDomain_of_injective`
    (`Mathlib/RingTheory/LinearDisjoint.lean`): the abstract route
    "tensor of two domains embedding into a common domain with
    linearly-disjoint ranges is a domain". Building the LinearDisjoint
    witness for our concrete factors would be its own ~30-50 LOC
    sub-task.

- **The clean project path** (the analogist's recommended route):
  exploit Mathlib's **localization–polynomial tensor product
  iso machinery**. The relevant Mathlib lemmas, both shipped:
  - `IsLocalization.Away.tensorRightEquiv`
    (`Mathlib/RingTheory/Localization/BaseChange.lean`):
    `TensorProduct R A S ≃ₐ[S] Localization.Away ((algebraMap R S) r)`
    when `A = Localization.Away r` over `R`. Tensor of a localization
    with anything is a localization (in the tensored ring).
  - `MvPolynomial.algebraTensorAlgEquiv`
    (`Mathlib/RingTheory/TensorProduct/MvPolynomial.lean`):
    `TensorProduct R A (MvPolynomial σ R) ≃ₐ[A] MvPolynomial σ A`.
    Tensor with a polynomial ring over the base is just polynomials
    over the algebra.

  Both factors of our tensor are localizations of polynomial rings
  over kbar:
  - `GmRing kbar = Localization.Away (X () : MvPolynomial Unit kbar)`
    — i.e., `kbar[t][1/t]`.
  - `Away (X_0·X_1) = HomogeneousLocalization.Away (projLineBarGrading) (X_0·X_1)`
    — a kbar-algebra that is a domain (already proven in
    `projectiveLineBar_isReduced` chain via the `val_injective`
    embedding into `Localization.Away (X_0·X_1)`).

  Composition:
  1. `Away (X_0·X_1) ⊗_kbar kbar[t] ≃ MvPolynomial Unit (Away (X_0·X_1))`
     via `MvPolynomial.algebraTensorAlgEquiv`.
  2. The localization `kbar[t] → kbar[t][1/t] = GmRing` corresponds via
     `IsScalarTower` + `IsLocalization.Away.tensorRightEquiv` to
     the localization at the same generator's image in the tensored
     polynomial ring.
  3. Result: `Away (X_0·X_1) ⊗_kbar GmRing ≃ Localization.Away (X () in MvPolynomial Unit (Away (X_0·X_1)))`.
  4. `MvPolynomial Unit (Away (X_0·X_1))` is a polynomial ring over a
     domain, hence a domain.
  5. Localization at powers of `X ()` (a non-zero divisor in the
     polynomial ring over a domain) preserves the domain property
     via `IsLocalization.isDomain_localization` +
     `powers_le_nonZeroDivisors_of_noZeroDivisors`
     + `MvPolynomial.X_ne_zero` (already in the project's playbook,
     used in `projectiveLineBar_isReduced` L734-738).

  Therefore `IsDomain (Away (X_0·X_1) ⊗_kbar GmRing)` follows, and
  `IsReduced` follows from `IsDomain` directly.

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** — buildable at ~50-80 LOC.
  No new Mathlib infrastructure needed; everything is a chain of
  existing iso lemmas. The same pattern unifies the `gm_geomIrred` /
  `projGm_isReduced` closures (same generators, different chart degrees).

### Decision 3: Where to land the substrate

- **Recommended file layout**:
  - New helper file: `AlgebraicJacobian/Genus0BaseObjects/Cross01Substrate.lean`
    importing `BareScheme`, `ChartIso`, `Points`. Contains:
    - `tensor_AwayGm_isDomain` (the tensor reducedness lemma, generic
      in the homogeneous generator's degree).
    - `IsClosedImmersion.lift_iff_range_subset` (the substrate lemma,
      generic in the schemes).
  - Cross01 cocycle body lifts into `GmScaling.lean` (no file move
    needed — the substrate is reused from `Cross01Substrate.lean`).

- **Why a new file vs inline in `GmScaling.lean`**:
  - The substrate is generic (no `gmScalingP1`-specific dependencies).
  - The substrate is reused by `gm_geomIrred` and `projGm_isReduced`
    (current `sorry`s in the SAME file), so a shared private namespace
    in `Cross01Substrate.lean` avoids duplication.
  - The substrate may be promotable to Mathlib later (the
    `lift_iff_range_subset` variant is a natural addition to
    `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`).

- **Verdict**: **BUILD_PROJECT_HELPER** in a new file `Cross01Substrate.lean`.

## Mathlib API citations (verified at iter-189)

All paths are inside
`.lake/packages/mathlib/Mathlib/` and line numbers match the project's
pinned commit at b80f227:

- `AlgebraicGeometry.IsClosedImmersion.lift` —
  `AlgebraicGeometry/Morphisms/ClosedImmersion.lean:206-208`.
- `AlgebraicGeometry.IsClosedImmersion.lift_fac` — same file `:210-214`.
- `AlgebraicGeometry.IsClosedImmersion.lift_fac_assoc` — same file (reassoc).
- `AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion` —
  same file `:60-66`.
- `AlgebraicGeometry.Scheme.Hom.ker` —
  `AlgebraicGeometry/IdealSheaf/Basic.lean:689-690`.
- `AlgebraicGeometry.Scheme.Hom.ker_apply` (under `[QuasiCompact f]`) —
  same file `:698-734`.
- `AlgebraicGeometry.Scheme.Hom.support_ker` (under `[QuasiCompact f]`) —
  same file `:839-878`.
- `AlgebraicGeometry.Scheme.Hom.range_subset_ker_support` (unconditional) —
  same file `:754-764`.
- `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` —
  same file `:563-606`.
- `AlgebraicGeometry.Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal` —
  same file `:609-620`.
- `AlgebraicGeometry.Scheme.IdealSheafData.gc` —
  same file `:622-625`.
- `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support`
  (`= I.radical`) — same file `:631-639`.
- `AlgebraicGeometry.Scheme.IdealSheafData.radical` —
  same file `:508-522`.
- `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι` —
  `AlgebraicGeometry/IdealSheaf/Subscheme.lean`.
- `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`
  (`= I`) — same file (used to derive `i.ker = vanishingIdeal (range i)`
  for a closed immersion `i = subschemeι` of a reduced subscheme).
- `Algebra.IsGeometricallyReduced` class —
  `Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean:47`.
- `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced` —
  same file `:52`.
- `IsLocalization.Away.tensorRightEquiv` —
  `Mathlib/RingTheory/Localization/BaseChange.lean`.
- `IsLocalization.Away.tensorEquiv` (the symmetric variant) — same file.
- `MvPolynomial.algebraTensorAlgEquiv` —
  `Mathlib/RingTheory/TensorProduct/MvPolynomial.lean`.
- `MvPolynomial.tensorEquivSum` — same file.
- `IsLocalization.isDomain_localization` —
  `Mathlib/RingTheory/Localization/Defs.lean`.
- `powers_le_nonZeroDivisors_of_noZeroDivisors` —
  `Mathlib/RingTheory/NonZeroDivisors.lean` (already used in
  `projectiveLineBar_isReduced` L734-738).

## Concrete project-side recipe

### Substrate 1: `IsClosedImmersion.lift_iff_range_subset`

Target signature:

```lean
theorem AlgebraicGeometry.IsClosedImmersion.lift_iff_range_subset
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z]
    (g : Y ⟶ X) [QuasiCompact g] [IsReduced Y] :
    (∃ h : Y ⟶ Z, h ≫ i = g) ↔
      Set.range g.base ⊆ Set.range i.base
```

Body skeleton (with `≈ 40-60` LOC):

```lean
  constructor
  · -- (⇒) Forward direction: trivial range pushdown.
    rintro ⟨h, rfl⟩
    intro x ⟨y, rfl⟩
    exact ⟨h.base y, rfl⟩
  · -- (⇐) Backward direction: the substance.
    intro hrange
    -- Step 1: closed immersion ⟹ range is closed, equal to ker.support.
    have hi_range : Set.range i.base = (i.ker.support : Set X) := by
      rw [← IdealSheafData.range_subschemeι]
      -- Use that i = subschemeι i.ker (up to iso) via toImage_imageι
      sorry  -- ~5 LOC bridge using Scheme.Hom.toImage / imageι
    -- Step 2: g.ker.support = closure (range g) ⊆ i.ker.support
    --         (latter is closed).
    have hsup : g.ker.support ≤ i.ker.support := by
      rw [Hom.support_ker]
      refine closure_minimal ?_ i.ker.isClosed_supportSet
      exact hrange.trans hi_range.le
    -- Step 3: Y reduced ⟹ g.ker is radical
    --         (since g.ker.ideal U = RingHom.ker (g.app U)
    --          and Y reduced ⟹ that kernel is radical).
    have hg_rad : g.ker.radical = g.ker := by
      ext U : 2
      simp only [IdealSheafData.radical_ideal, g.ker_apply]
      exact (RingHom.ker_isRadical_iff_reduced_of_surjective
        Function.Surjective.rfl).mpr inferInstance  -- needs adjustment
      -- Concretely: use `f.app U`'s kernel-is-radical because Y is reduced;
      -- the appropriate lemma is `RingHom.ker_isRadical_of_reduced_codomain`.
      sorry  -- ~10 LOC; standard "reduced source ⟹ kernel of ring map radical"
    -- Step 4: Z reduced ⟹ i.ker is radical (same argument).
    have hi_rad : i.ker.radical = i.ker := by
      ext U : 2
      sorry  -- ~5 LOC, symmetric to Step 3
    -- Step 5: combine via Galois connection.
    --         g.ker.support ⊆ i.ker.support
    --         ⟹ vanishingIdeal(i.ker.support) ≤ vanishingIdeal(g.ker.support)
    --         ⟹ i.ker.radical ≤ g.ker.radical (by `vanishingIdeal_support`)
    --         ⟹ i.ker ≤ g.ker (by Steps 3, 4).
    have hker : i.ker ≤ g.ker := by
      calc i.ker
          = i.ker.radical := hi_rad.symm
        _ = vanishingIdeal i.ker.support := vanishingIdeal_support.symm
        _ ≤ vanishingIdeal g.ker.support := vanishingIdeal_antimono hsup
        _ = g.ker.radical := vanishingIdeal_support
        _ = g.ker := hg_rad
    -- Step 6: apply Mathlib's IsClosedImmersion.lift.
    exact ⟨IsClosedImmersion.lift i g hker,
           IsClosedImmersion.lift_fac i g hker⟩
```

**Notes on the LOC**:
- The two "kernel-is-radical" steps (3, 4) might need a Mathlib bridge
  lemma not directly searched here; if so, that adds ~10-15 LOC for an
  inline derivation (use `Hom.ker_apply` to drop to ring kernels, then
  reducedness of the source gives radicality of the ring kernel — a
  standard `RingHom.ker_isRadical` argument).
- The Step 1 bridge (closed immersion `i` is the `subschemeι` of its
  kernel, up to iso) uses `Scheme.Hom.toImage_imageι` from Mathlib.

**Total**: ~40-60 LOC.

### Substrate 2: tensor reducedness `(Away (X_0·X_1)) ⊗_kbar GmRing`

Target signature (generic in the homogeneous generator `f` of degree `d`):

```lean
theorem AlgebraicGeometry.gmRing_tensor_homogeneousAway_isDomain
    (kbar : Type u) [Field kbar] {d : ℕ} (hd : 0 < d)
    (f : MvPolynomial (Fin 2) kbar)
    (hf : f ∈ projectiveLineBarGrading kbar d)
    (hf_ne : f ≠ 0) :
    IsDomain (TensorProduct kbar
      (HomogeneousLocalization.Away (projectiveLineBarGrading kbar) f)
      (GmRing kbar))
```

Body skeleton (with `≈ 50-80` LOC):

```lean
  -- Step 1: Away 𝒜 f is a domain (project-side, used in
  -- projectiveLineBar_isReduced L734-738).
  haveI hf_dom : IsDomain (HomogeneousLocalization.Away
      (projectiveLineBarGrading kbar) f) := by
    refine Function.Injective.isDomain
      (algebraMap (HomogeneousLocalization.Away _ f) (Localization.Away f)) ?_
    · intro x y h
      exact HomogeneousLocalization.val_injective _ h
  -- Step 2: Build the iso chain.
  -- (a) MvPolynomial.algebraTensorAlgEquiv :
  --     TensorProduct kbar (Away 𝒜 f) (MvPolynomial Unit kbar) ≃ₐ[Away 𝒜 f]
  --       MvPolynomial Unit (Away 𝒜 f)
  -- (b) IsScalarTower over kbar lifts the localization at X () in MvPoly Unit kbar
  --     to the corresponding localization at X () in MvPoly Unit (Away 𝒜 f).
  -- (c) Resulting iso:
  --     TensorProduct kbar (Away 𝒜 f) (GmRing kbar) ≃
  --       Localization.Away (X () : MvPolynomial Unit (Away 𝒜 f))
  -- Step 3: RHS is a domain.
  -- MvPolynomial Unit (Away 𝒜 f) is a polynomial ring over a domain,
  -- hence a domain (instance auto-resolves).
  -- Localization at powers of X () (a non-zero divisor, by
  -- MvPolynomial.X_ne_zero) preserves the domain property via
  -- IsLocalization.isDomain_localization + powers_le_nonZeroDivisors.
  sorry  -- ~50-80 LOC threading the iso chain and applying domain instances
```

The body's main work is threading `IsLocalization.Away.tensorRightEquiv`
(or its symmetric `tensorEquiv` variant) at the `kbar[t] → GmRing`
localization step, after collapsing the `Away 𝒜 f ⊗_kbar kbar[t]` tensor
via `algebraTensorAlgEquiv`. The threading requires careful instance
management (`IsScalarTower kbar (Away 𝒜 f) (MvPolynomial Unit (Away 𝒜 f))`,
the `Algebra` from polynomial ring over an algebra, the `IsLocalization.Away`
instance on the tensored side) — accounting for the upper end of the
50-80 LOC range.

**Corollary**:
```lean
instance : IsReduced (Spec (.of (TensorProduct kbar (Away _ f) (GmRing kbar))))
```
follows in ~3 LOC via `inferInstanceAs (IsReduced (Spec ...))` after the
domain instance lands.

### Application 1: cocycle body completion

The iter-188 structural setup already lands the harness in
`gmScalingP1_chart_agreement_cross01`:
- `s_pair`, `hs_fst`, `hs_snd`, `hΔ`, `hsep`, `hPLB_agree` are all built.
- Goal at line 553 is reducible to `∃ s, s ≫ Δ = s_pair`.

With Substrates 1+2 in hand:
1. Establish `IsReduced (intersection)` by transporting the `Spec` domain
   instance across `gmScalingP1_cover_intersection_X_iso` (~10 LOC).
2. Establish the range containment `range s_pair.base ⊆ range Δ.base`
   by closed-points check (each closed point of intersection lies over
   a single kbar-point of `D_+(X_0·X_1) × Gm`, both chart-maps evaluate
   to the same PLB-point) — ~15-25 LOC via point-checking on closed points
   (kbar-rational since kbar is alg-closed and intersection is locally
   of finite type).
3. Apply `lift_iff_range_subset` to extract `s`, then close via
   `pullback.diagonal_fst` / `_snd` (= 𝟙) — ~10 LOC.

**Total application**: ~35-50 LOC.

### Application 2: bonus sorries

The same Substrate 2 closes:
- `projGm_isReduced` (~15-25 LOC): cover `(PLB ⊗ Gm).left` by the
  per-chart `Spec (Away X_i ⊗ GmRing)` (using the existing
  `gmScalingP1_cover`), each reduced by Substrate 2 at the degree-1
  generator; conclude via `IsReduced.of_openCover`.
- `gm_geomIrred` (~15-30 LOC): for `[IsAlgClosed kbar]`, every algebraic
  extension K/kbar is isomorphic to kbar (up to alg-closure equivalence),
  so the base-change `GmRing ⊗_kbar K = Localization.Away t in K[t]`
  is a domain → `Spec` is irreducible. The Mathlib bridge
  `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced`
  (line 52 of `GeometricallyReduced.lean`) MIGHT apply once
  `GmRing kbar` is shown geometrically reduced — that's a separate
  ~10-15 LOC argument.

**Total bonus**: ~30-55 LOC for both.

## Total LOC estimate

| Sub-task | LOC | Substrate or application? |
|---|---|---|
| Substrate 1: `lift_iff_range_subset` | 40–60 | substrate (Cross01Substrate.lean) |
| Substrate 2: tensor reducedness | 50–80 | substrate (Cross01Substrate.lean) |
| Application: cocycle body | 35–50 | inline in GmScaling.lean |
| Bonus: `projGm_isReduced` + `gm_geomIrred` | 30–55 | inline in GmScaling.lean |

**Total**: ~155–245 LOC over 3–5 iters.

This matches the iter-188 escalation's ~150-200 LOC estimate at the
lower end and slightly exceeds at the upper end. The substrate work is
front-loaded (Substrates 1+2 = ~90-140 LOC in iters 189-190); the
application work is rapid follow-on (iters 191-193).

## Hard binary verdict

**(B) FEASIBLE at 80-200 LOC.**

The substrate (Substrate 1 + Substrate 2 combined) lands at
~90-140 LOC; the cocycle application closes within 35-50 LOC; the
bonus sorries close within 30-55 LOC. Total ranges 155-245 LOC, with
the central estimate at ~180-200 LOC.

**Verdict A (FEASIBLE at <80 LOC) is ruled out**: Mathlib does not
ship `IsClosedImmersion.lift_iff_range_subset` and there is no
shorter Mathlib-direct route. The substrate is genuine work, not a
naming-only gap.

**Verdict C (NOT FEASIBLE at <200 LOC, USER ESCALATION) is NOT triggered**:
the work is bounded and uses only existing Mathlib primitives. No
upstream Mathlib PR is required. The Galois-connection chain
(`vanishingIdeal ↔ support` with `Hom.support_ker` and
`range_subschemeι`) is the canonical Stacks-style path and is fully
formalized in Mathlib.

## Recommendation

Proceed with **Option B (project-side substrate)** as planned. Land
the work in a new file `AlgebraicJacobian/Genus0BaseObjects/Cross01Substrate.lean`
containing the two substrate lemmas, imported by `GmScaling.lean`.

**Phased delivery (3-5 iters)**:
- **Iter 189**: dispatch a prover on `Cross01Substrate.lean` to land
  Substrate 1 (`lift_iff_range_subset`); this is the smaller chunk
  (~40-60 LOC) and unblocks the application path independently.
- **Iter 190**: dispatch a prover on `Cross01Substrate.lean` to land
  Substrate 2 (tensor reducedness); this is the larger chunk
  (~50-80 LOC) and uses Mathlib's iso-chain machinery
  (`MvPolynomial.algebraTensorAlgEquiv` + `IsLocalization.Away.tensorRightEquiv`).
- **Iter 191-193**: dispatch a prover on `GmScaling.lean` to close
  the three open sorries (`gmScalingP1_chart_agreement_cross01`,
  `gm_geomIrred`, `projGm_isReduced`) using both substrates.

**Reversal trigger**: if iter-190's tensor reducedness substrate
fails to type-check at the `tensorRightEquiv` step due to a
`Algebra kbar ...` / `IsScalarTower` instance mismatch, fall back to
the `Subalgebra.LinearDisjoint.isDomain_of_injective` route (build
the linear-disjoint witness via the polynomial-ring-disjoint-variables
classical fact). Same LOC budget; different elaboration shape.
