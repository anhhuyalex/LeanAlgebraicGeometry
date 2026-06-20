# Analogy: cotangent presheaf design — presheaf-level pullback vs. appLE-algebra Kähler

## Slug
cotangent-presheaf-design

## Iteration
120

## Question

Is Mathlib's `TopCat.Presheaf.pullback` (left Kan extension at the
presheaf level) the right idiom for building the relative cotangent
presheaf `Ω_{X/S}` of a morphism of schemes? Specifically, given that
the project's `relativeDifferentialsPresheaf` constructs sections on
`V ⊆ X` as `Ω[Γ(X,V) / A']` where `A' = colim_{f V ⊆ W} Γ(S,W)` (the
presheaf-level inverse image, **not** the sheafified one), what is the
relationship between this `A'` and the `appLE`-algebra `A = Γ(S, U)` on
which Mathlib's smoothness chain (`free_kaehlerDifferential` +
`rank_kaehlerDifferential`) operates, and which of (i) a local bridge
lemma, (ii) a sheafified-pullback refactor, (iii) a theorem-statement
restatement on `Ω[Γ(X,V)/Γ(S,U)]` is the right path forward?

## Project artifact(s)

- `AlgebraicJacobian/Differentials.lean:49-52` — `relativeDifferentialsPresheaf`
  definition via adjunction transpose + `relativeDifferentials'`.
- `AlgebraicJacobian/Differentials.lean:58-64` — `relativeDifferentialsPresheaf_obj_kaehler`,
  body `rfl`, identifying the section module with
  `CommRingCat.KaehlerDifferential (φ'.app V)`.
- `AlgebraicJacobian/Differentials.lean:87-136` — `smooth_locally_free_omega`,
  the load-bearing forward Jacobian criterion. **Carries a `sorry` at the
  Step-5 type-bridge** (lines 132-136).
- `blueprint/src/chapters/Differentials.tex:54-91` — Step-5 prose with
  the `% NOTE (iter-119 prover finding)` block from iter-119.

## Decisions identified

### Decision 1: Is `TopCat.Presheaf.pullback` the right idiom for the inverse-image O-algebra in the cotangent presheaf construction?

- **Mathlib idiom (closest)**: Mathlib b80f227 has **no scheme-level
  cotangent presheaf or sheaf**. The available building blocks are:
  - `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`
    (`Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf`) —
    abstract: given `φ : S' ⟶ R` of presheaves of `CommRingCat` over an
    arbitrary base category `Dᵒᵖ`, returns a presheaf of `R`-modules
    whose value on each `X : Dᵒᵖ` is `CommRingCat.KaehlerDifferential
    (φ.app X)` (`relativeDifferentials'_obj`, by `rfl`).
  - `TopCat.Presheaf.pullback C f`
    (`Mathlib.Topology.Sheaves.Presheaf`) — the **presheaf-level left
    Kan extension** along `(Opens.map f.base).op`, valued in `C` with
    `HasColimits C`. **No sheafification.**
  - `TopCat.Presheaf.pushforwardPullbackAdjunction` (same file) — the
    presheaf-level adjunction `pullback ⊣ pushforward`. The project
    uses this to transpose `f.c : S.presheaf ⟶ (Opens.map f.base).op ⋙
    X.presheaf` to a morphism `φ' : (pullback CommRingCat f.base).obj
    S.presheaf ⟶ X.presheaf` of presheaves of `CommRingCat` on `X`.
  - `TopCat.Sheaf.pullback A f` (`Mathlib.Topology.Sheaves.Functors`)
    — the **sheafified** inverse image at the sheaf level. Composes
    `presheafToSheaf` after the presheaf-level pullback.
  - `AlgebraicGeometry.Scheme.Modules.{pullback, pushforward}`
    (`Mathlib.AlgebraicGeometry.Modules.Sheaf`) — sheafified
    pullback/pushforward for sheaves of `O`-modules on schemes,
    adjoint pair via `instIsLeftAdjointPullback` /
    `instIsRightAdjointPushforward`. **No corresponding
    `relativeDifferentials` functor on this side.**
  - `TopCat.Presheaf.pullbackObjObjOfImageOpen` — local iso between
    `((pullback C f).obj F).obj (op U)` and `F.obj (op (f '' U))`
    *when* `f '' U` is open. Not applicable to general `f`.
- **Project's path**: presheaf-level `pullback ⊣ pushforward`
  adjunction transpose of `f.c`, fed into the abstract
  `relativeDifferentials'`. By `relativeDifferentials'_obj` this gives
  on each `V ⊆ X` the section module `Ω[Γ(X,V) / A']` with
  `A' = ((pullback CommRingCat f.base).obj S.presheaf).obj (op V) =
  colim_{W : Opens S, f V ⊆ W} Γ(S, W)`.
- **Gap**: **divergent-with-cost**. Mathematically the "correct"
  inverse-image-of-`O_S` on `X` is the **sheafified** `f^{-1}_{sh} O_S`,
  whose section on an affine `V ⊆ X` with `f V ⊆ U` affine is
  (canonically) `Γ(S, U)` modulo a basis-cofinality argument. The
  presheaf-level Kan extension differs from this on non-affine opens
  and, even on affine opens, is the **larger colimit ring** `A_M`
  (see Decision 2) rather than `A`.
- **Cost of divergence**: every downstream theorem that wants to
  identify a section of `relativeDifferentialsPresheaf` on an affine
  `V` with `Ω[Γ(X,V) / Γ(S,U)]` pays a bridge-lemma cost. The
  iter-119 PARTIAL is exactly this cost: `smooth_locally_free_omega`'s
  Step 5 (the "transfer back" of the free + rank conclusion) is
  blocked on the bridge between `Ω[B/A']` and `Ω[B/A]`.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL.** The scheme-level relative
  cotangent **sheaf** is genuinely missing from Mathlib b80f227. The
  presheaf-level approach is the only off-the-shelf path, and the
  divergence (presheaf vs sheaf) is forced by the Mathlib snapshot,
  not by a project choice that could be corrected by aligning. The
  project's choice of `relativeDifferentials'` + presheaf-level
  pullback is the best one available, and the iter-115/116 review of
  alternatives confirmed no better Mathlib idiom exists for the
  scheme-morphism case.

### Decision 2: What is the algebraic-geometry-correct relationship between `A → B` (appLE) and the colimit ring `A' = (f^{-1}_{psh} O_S)(V)` on affine `V ⊆ X` with `f V ⊆ U` affine?

- **Mathematical answer (worked out)**: Under
  `IsAffineOpen U₀`, `IsAffineOpen V₀`, `V₀ ≤ f⁻¹ U₀`:
  - The directed system `{W open in S : f V₀ ⊆ W}` has a cofinal
    subsystem of basic opens `D(g) ⊆ U₀` with `g ∈ A` such that
    `appLE(g) ∈ B^×` (i.e. `g` doesn't vanish on `f V₀`).
  - Hence `A' = colim_{g ∈ M} A_g = A_M` (the localization of
    `A = Γ(S, U₀)` at the multiplicative set
    `M := {g ∈ A : appLE(g) ∈ B^×}`).
  - The map `A → A' = A_M` is a **localization map**. Hence
    `Ω[A_M / A] = 0` (Mathlib `Algebra.FormallySmooth.of_isLocalization`
    + projectivity / vanishing of `H¹Cotangent` for localizations
    implies `Ω = 0` for a localization-of-rings tower — though the
    project would more directly use `KaehlerDifferential.isLocalizedModule_map`).
  - **The second exact sequence of Kähler differentials**
    `B ⊗_{A_M} Ω[A_M / A] → Ω[B / A] → Ω[B / A_M] → 0` then gives the
    surjection `Ω[B / A] → Ω[B / A_M]` **with kernel zero** (the kernel
    is the image of `Ω[A_M / A] = 0`), i.e. an **isomorphism of
    `B`-modules**.
  - The `image(A) = image(A')` claim in the directive's Q2 is **false
    as a set equality** (e.g. `f : Spec ℚ → Spec ℤ`, `U₀ = Spec ℤ`,
    `W = D(2)`, the element `1/2` is in image(A') but not image(A)).
    But the **iso of Kähler modules holds anyway** because
    "dividing by a unit doesn't add new generators in `Ω`": every
    new generator `d(appLE(g)^{-1})` is `-appLE(g)^{-2} · d(appLE(g))`,
    which lives in the `B`-submodule already generated by `d(image(A))`.
- **Mathlib lemma**: `KaehlerDifferential.isLocalizedModule_map`
  (`Mathlib.RingTheory.Etale.Kaehler`) — for the tower `A → A_M → B`
  with `B` a `A_M`-algebra and `M : Submonoid A`, the natural map
  `Ω[A_M / A] → Ω[B / A]` (composed appropriately) exhibits the
  target as a localization. From this, plus
  `KaehlerDifferential.ker_map`, one extracts the iso
  `Ω[B / A] ≃ Ω[B / A_M]` directly.
- **Cost of the bridge in Lean** (for **Option (i)** of Q3): to
  produce this iso for the project's specific `A'`, one must first
  identify `A' = ((pullback CommRingCat f.base).obj S.presheaf).obj
  (op V₀)` as a `CommRingCat` with the localization `A_M` (or with
  some concrete localization that `appLE(g)^{-1}` lifts to). This is
  the non-trivial step — `TopCat.Presheaf.pullback` is the
  Mathlib-blessed left Kan extension, computed as a colimit in
  `CommRingCat`, and there is no Mathlib lemma identifying the colimit
  of `{Γ(S, D(g)) : g ∈ M}` with `A_M` for an arbitrary affine `U₀`.
  This identification requires:
  1. A cofinality argument from "open neighbourhoods of `f V₀` in `S`"
     down to "basic opens `D(g) ⊆ U₀` with `appLE(g) ∈ B^×`".
  2. Identifying `Γ(S, D(g)) = A_g` (Mathlib has this as
     `IsAffineOpen.basicOpen_isLocalization`-style).
  3. Identifying `colim_{g ∈ M} A_g = A_M` (essentially
     `IsLocalization.colim`-style, but a directed-colimit-of-rings
     argument).
  Estimated 200-400 LOC for the bridge, optimistically.
- **Verdict on the bridge**: mathematically **valid**, but requires a
  non-trivial cofinality + colimit-of-localizations argument that has
  no direct Mathlib closure. The bridge is **NEEDS_MATHLIB_GAP_FILL**
  in the sense that the cofinality+colimit argument has no off-the-shelf
  lemma; it must be built (or replaced).

### Decision 3: Which structural option closes iter-119's PARTIAL?

The three options under consideration:

- **Option (i): project-local helper lemma**
  `relativeDifferentialsPresheaf_iso_kaehler_appLE`.
  - **Mathlib idiom alignment**: weak — no precedent for the
    cofinality+colimit-of-localizations step.
  - **Cost**: 200-400 LOC of bridge infrastructure, comprising
    (a) cofinality of basic opens `D(g) ⊆ U₀` in the cone
    `{W : f V₀ ⊆ W ⊆ S}`, (b) identifying the colimit of
    `Γ(S, D(g))` with `A_M`, (c) identifying the `A → B` algebra
    structure via `A_M`, (d) invoking
    `KaehlerDifferential.isLocalizedModule_map` for the iso. Each
    step has open universe / `IsAffineOpen.basicOpen` / `IsLocalization`
    side conditions. Estimated 3-6 prover iters.
  - **Downstream effect**: `smooth_locally_free_omega` closes; the
    cotangent presheaf at affine `V` becomes provably `Ω[B/A]` for the
    appLE algebra; future consumers (if any) inherit the iso.
  - **Risk**: high. The Lean colimit-of-rings argument has bitten the
    project before (cf. `affine-basis-sheaf-bridge.md`, where a
    similar cofinality argument for the sheaf condition is the
    project's outstanding load-bearing sorry).
- **Option (ii): refactor `relativeDifferentialsPresheaf` to use the
  sheafified inverse image.**
  - **Mathlib idiom alignment**: best **mathematically** — the
    sheafified `f^{-1}_{sh} O_S` is the geometer's canonical
    construction; its sections on affine `V` with `f V ⊆ U` affine
    are `Γ(S, U)` directly (Hartshorne II.5; Stacks 008N).
  - **Mathlib status**: `TopCat.Sheaf.pullback A f` exists, but there
    is **no Mathlib sheafified `relativeDifferentials'`**. The
    construction `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`
    operates on a morphism of presheaves of `CommRingCat`; composing
    it with sheafification (`PresheafOfModules.sheafification` exists
    but for modules-with-fixed-ring, not the ring-changing case
    needed here) requires significant infrastructure work.
  - **Cost**: 500+ LOC of new infrastructure spanning the sheafified
    pullback + sheafified differential construction; the
    affine-section identification then becomes essentially free
    (sections on basis opens factor through a basis-of-affine-opens
    sheaf condition).
  - **Downstream effect**: cleanest long-term, but completely
    rewrites the cotangent presheaf chapter. The current
    `relativeDifferentialsPresheaf_obj_kaehler` `rfl` lemma is lost
    (sections on `V` are no longer definitionally `KaehlerDifferential`
    of anything — they're a sheafified colimit).
  - **Risk**: extreme for autonomous-loop scope. Builds on a Mathlib
    gap (`affine-basis-sheaf-bridge.md`) that the project has already
    identified as out-of-scope.
- **Option (iii): restate `smooth_locally_free_omega` to use
  `Ω[Γ(X,V) / Γ(S,U)]` directly.**
  - **Mathlib idiom alignment**: matches Stacks 02G1 forward-direction
    statement at the **affine chart level** — the textbook content of
    the Jacobian criterion is exactly that on each affine chart
    `Spec B → Spec A` the Kähler module `Ω[B/A]` is free of rank `n`.
    Mathlib's `Algebra.IsStandardSmooth.free_kaehlerDifferential` and
    `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
    are stated in exactly this form.
  - **Cost**: ~5-10 LOC theorem body. The theorem becomes "for each
    `x ∈ X` there exist affine `U ⊆ S`, affine `V ⊆ X` with `x ∈ V`
    and `f V ⊆ U`, such that
    `Module.Free Γ(X,V) Ω[Γ(X,V) ⁄ Γ(S,U)]` and the rank is `n`."
    The body is essentially the existing Steps 1-4 of
    `smooth_locally_free_omega` with no Step-5 bridge. The
    `algebraize`-derived algebra structure makes the conclusion
    direct.
  - **Downstream effect**: decouples `smooth_locally_free_omega` from
    `relativeDifferentialsPresheaf` entirely. The cotangent presheaf
    remains in the file with its `rfl` lemma but is no longer used
    by the smoothness criterion. A separate future lemma (whose
    body is the Option-(i) bridge) can then **optionally** transfer
    the conclusion to the presheaf if a downstream consumer ever
    needs it — but currently no consumer does (cotangent presheaf is
    a leaf object in the live project graph).
  - **Risk**: minimal. Mathematically faithful, prover-friendly,
    blueprint-aligned (Stacks 02G1 forward direction is stated
    affine-chart-wise too).

### Decision 4: Hybrid? Keep both?

A hybrid retains the cotangent presheaf as a separate definition
(with its `rfl` identification lemma on `KaehlerDifferential` of the
colimit-ring algebra map), uses Option (iii) for
`smooth_locally_free_omega`, and adds Option (i) as an **independent
lemma** (`relativeDifferentialsPresheaf_iso_kaehler_appLE`) with a
`sorry` body that future downstream consumers (if any emerge) can
close. This separates the **load-bearing theorem** from the **bridge
between two conventions**, so the bridge can be filled or refactored
without touching the smoothness criterion.

## Recommendation

**Adopt Option (iii) for iter-120**, and optionally land Option (i)
as a separately-statemented `sorry`-bodied lemma to flag the bridge
work for the future.

**Concrete blueprint+Lean restatement** of
`smooth_locally_free_omega`:

```
theorem smooth_locally_free_omega {n : ℕ} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] :
    ∀ (x : X), ∃ (U : S.Opens) (V : X.Opens) (e : V ≤ (Opens.map f.base).obj U),
      x ∈ V.1 ∧ IsAffineOpen U ∧ IsAffineOpen V ∧
      letI := (Hom.appLE f U V e).hom.toAlgebra
      Module.Free Γ(X, V) Ω[Γ(X, V) ⁄ Γ(S, U)] ∧
      Module.rank Γ(X, V) Ω[Γ(X, V) ⁄ Γ(S, U)] = n
```

(or an equivalent shape that exposes the `algebraize`-derived algebra
instance.)

The body is essentially the existing iter-119 Steps 1-4 (extract
standard-smooth chart, algebraize, free + rank from
`Algebra.IsStandardSmooth.free_kaehlerDifferential` +
`Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`)
with no Step-5 bridge. The protected-signature situation: the
theorem `smooth_locally_free_omega` is **not** in
`archon-protected.yaml`, so restatement is allowed.

**Blueprint update needed**: Differentials.tex Theorem
`thm:smooth_locally_free_omega` must be restated to match. The
iter-119 `% NOTE` block (lines 92-104) can then be removed (or
replaced with a `% NOTE: Step 5 retired in iter-120 refactor —
forward-direction theorem now stated affine-chart-wise.`).

**Why not Option (i) standalone**: while mathematically valid (per
Decision 2), the cofinality+colimit-of-localizations argument has no
Mathlib precedent and is estimated 200-400 LOC of high-friction
infrastructure. The autonomous loop has already absorbed one
parallel cofinality argument as out-of-scope
(`affine-basis-sheaf-bridge.md` Decision 1); adding a second is a
strategic mistake.

**Why not Option (ii)**: same as the sheafification verdict in
`affine-basis-sheaf-bridge.md` — Mathlib b80f227 does not expose the
sheafified relative cotangent infrastructure, and building it spans
deep gaps that the project has already declared out-of-loop-scope.

**Optional hybrid**: keep `relativeDifferentialsPresheaf` and its
`rfl` identification lemma intact. Add
`relativeDifferentialsPresheaf_iso_kaehler_appLE` as a separate
`sorry`-bodied lemma with the appropriate hypotheses. The hybrid
costs 0 LOC of bridge work this iter but documents the bridge
obligation explicitly for future iters or downstream consumers.
