# Analogy: Iterated minimal free resolution as `ChainComplex ℕ (ModuleCat R)` vs `HasProjectiveDimensionLT` SES descent

## Mode
api-alignment

## Slug
ab-natrecursive

## Iteration
200

## Question
Iter-200 Lane AB-gap1-NatRecursive proposes a `ChainComplex ℕ (ModuleCat R)`
of finite-rank free modules of length `pd_R(M)` whose transition maps have
image in `𝔪`, built by `Nat`-recursion on syzygies starting from the
iter-199 axiom-clean `RingTheory.Module.exists_minimalSurjection_finite_localRing`.
The lane is budgeted at ~40-80 LOC (40-80 LOC carving of a length-pd
ChainComplex via Stacks 00LK + Bruns-Herzog 1.5.18). Question: does
Mathlib's homological-algebra substrate match this carrier, and is the
budget realistic?

## Project artifact(s)
- `AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean:186-188` —
  `Module.projectiveDimension R M := CategoryTheory.projectiveDimension (ModuleCat.of R M)`
  (one-line re-export).
- `AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean:1198-1276` —
  `RingTheory.Module.exists_minimalSurjection_finite_localRing` (iter-199
  axiom-clean): produces `(n, f : (Fin n → R) →ₗ[R] M)` with
  `Surjective f`, `n = finrank κ (κ ⊗ M)`, `ker f ≤ 𝔪 • ⊤`.
- `AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean:1398-1432` —
  `auslander_buchsbaum_formula_succ_pd` (the typed-sorry the lane is
  trying to close), inductive step on `pd_R(M) = k + 1`.

## Decisions identified

### Decision 1: Carrier for "iterated minimal resolution"
**ChainComplex ℕ (ModuleCat R)** (directive's proposal) versus
**`CategoryTheory.HasProjectiveDimensionLT M (k+1)`** (Mathlib's
abstract carrier).

- **Mathlib idiom**: `CategoryTheory.HasProjectiveDimensionLT X n`
  (`Mathlib.CategoryTheory.Abelian.Projective.Dimension`). This is the
  inductive Prop characterising "all `Ext^i(X, -)` vanish for `i ≥ n`",
  with constructor `HasProjectiveDimensionLT.mk'` and three SES bridges:
  - `ShortExact.hasProjectiveDimensionLT_X₁ : ShortExact S → HasProjectiveDimensionLT S.X₂ n → HasProjectiveDimensionLT S.X₃ (n+1) → HasProjectiveDimensionLT S.X₁ n`
  - `_X₂`, `_X₃` for the other entries.
  The `_X₁` direction is **exactly** the syzygy step: take SES
  `0 → K → R^n → M → 0` with `R^n` free (so `HasProjectiveDimensionLT R^n 1`,
  i.e. projective), and `pd M < n+1` gives `pd K < n`. Why Mathlib chose
  this shape: it makes `pd` reasoning purely Ext-functorial, avoiding
  ever materialising a concrete resolution and bypassing the size/finiteness
  issues that bite at the `ChainComplex` carrier.
- **Project's current path**: build a concrete `ChainComplex ℕ (ModuleCat R)`
  by `Nat`-recursion, then read off `pd_R(M)` from its length.
- **Gap**: divergent-with-cost.
- **Cost of divergence**:
  - `ChainComplex ℕ` is structurally **infinite**: there is no "length-n
    ChainComplex" type. To realise "length `pd_R(M)`", the prover must
    build an infinite complex with zero objects from degree `pd_R(M)+1`
    onwards. That requires *knowing* when the syzygy bottoms out — which
    is exactly the deep AB content, NOT given by `ChainComplex.mk'`.
  - "Minimal" (`d_n` image in `𝔪 · F_{n-1}`) is a local-ring-specific
    property absent from Mathlib's projective-resolution API
    (`ProjectiveResolution.mk` / `ofComplex` are generic, not minimal-
    aware). The minimal trim from `Stacks 00LK` does NOT exist as a
    Mathlib bridge.
  - `ChainComplex.mk'` requires carrying `Module.Finite` instances
    through every recursion step plus a dependent-pair carrier for the
    next syzygy. ~20 LOC per step before any minimality content lands.
  - The downstream consumer `auslander_buchsbaum_formula_succ_pd` does
    not need the chain complex object — it needs only that the syzygy
    `K` satisfies `pd_R(K) = pd_R(M) - 1`. `hasProjectiveDimensionLT_X₁`
    delivers that directly.
- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision 2: Per-step syzygy carrier
Project file uses a `LinearMap`-level pair `(n, f, Surjective f, ker f ≤ 𝔪 • ⊤)`.

- **Mathlib idiom**: `CategoryTheory.Projective.syzygies`
  (`Mathlib.CategoryTheory.Preadditive.Projective.Basic`) packages the
  categorical syzygy of a morphism. Plus `CategoryTheory.ShortComplex (ModuleCat R)`
  with `ShortExact` via `moduleCatMkOfKerLERange` / `ShortExact.mk'`. The
  bridge `ShortComplex.ShortExact.moduleCat_exact_iff_function_exact` /
  `ModuleCat.free_shortExact` provides the LinearMap ↔ ShortExact dictionary.
- **Project's current path**: `LinearMap` pair, no categorical packaging.
  This is the right `RingTheory.Module` namespace shape for the per-step
  helper, but the iterated version needs to cross into ShortComplex
  language to invoke `hasProjectiveDimensionLT_X₁`.
- **Gap**: divergent-equivalent (one-shot translation lemma needed).
- **Cost of divergence**: ~10-15 LOC bridge lemma packaging the iter-199
  `exists_minimalSurjection_finite_localRing` output as a
  `ShortComplex.ShortExact`. Single helper, no compounding cost.
- **Verdict**: PROCEED with one-shot bridge.

### Decision 3: Finite-projective-dimension hypothesis carrier
The current `auslander_buchsbaum_formula_succ_pd` consumes
`Module.projectiveDimension R M = ((k+1 : ℕ) : WithBot ℕ∞)`.

- **Mathlib idiom**: `HasProjectiveDimensionLE` / `HasProjectiveDimensionLT`
  with `projectiveDimension_le_iff` translating `≤ ↑n` to the inductive
  Prop. Since `Module.projectiveDimension R M = CategoryTheory.projectiveDimension (ModuleCat.of R M)`
  (one-line re-export, line 186), the translation is a single rewrite.
- **Project's current path**: the `WithBot ℕ∞` equality. Compatible with
  Mathlib but slightly heavier to manipulate inductively.
- **Gap**: identical (up to a `projectiveDimension_le_iff` rewrite).
- **Verdict**: PROCEED. Adopt `HasProjectiveDimensionLT` as the working
  hypothesis carrier inside the inductive proof; the outer signature can
  keep `WithBot ℕ∞` for downstream compat.

### Decision 4: Minimality / Stacks 00LK trim
"Every finite free resolution of a finite module over a Noetherian local
ring trims to a minimal one of the same length."

- **Mathlib idiom**: **none located**. `ProjectiveResolution.ofComplex`
  builds the generic resolution; there is no minimal carving. `Module.free_of_flat_of_isLocalRing`
  + Nakayama get individual frees; nothing iterates.
- **Project's current path**: build minimality directly via iter-199's
  Nakayama-lift step (`exists_minimalSurjection_finite_localRing`).
- **Gap**: NEEDS_MATHLIB_GAP_FILL.
- **Cost**: the lane already pays this cost via iter-199; the per-step
  ingredient is in hand. The question is whether minimality is even
  NEEDED for the AB proof — see Recommendation.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL on the *trim lemma*; but for the
  AB inductive step, minimality is **avoidable** if Decision 1 is taken
  (Ext-based descent doesn't care whether `d_n` images sit in `𝔪`).

### Decision 5: Bruns-Herzog Construction 1.5.18 carrier
Direct concrete iterated minimal-free-resolution construction.

- **Mathlib idiom**: not packaged; the closest is `ProjectiveResolution.ofComplex`
  which is generic (uses `Projective.π` / `Projective.d`, not minimality).
- **Project's current path**: aspirational ~40-80 LOC build via `ChainComplex.mk'`.
- **Gap**: divergent-with-cost.
- **Cost**: see Decision 1 — the literal Bruns-Herzog 1.5.18 construction
  requires (a) carrying `Module.Finite` through recursion, (b) proving
  the bottom-out at `pd_R(M)`, (c) keeping minimality at each step.
  Realistic LOC: **150-250**, not 40-80. The "bottom-out" subterm alone
  needs an upstream "finite-pd ⇒ k-th syzygy is free at k = pd" lemma
  that doesn't exist in Mathlib.
- **Verdict**: RE-SCOPE if pursued literally; ALIGN_WITH_MATHLIB (Path A)
  is the recommended pivot.

## Recommendation

**Pivot the iter-200 Lane AB-gap1-NatRecursive carrier from
`ChainComplex ℕ (ModuleCat R)` to `CategoryTheory.HasProjectiveDimensionLT`
SES descent.** The Mathlib idiom for "iterated syzygy" is
`hasProjectiveDimensionLT_X₁`, applied to the SES extracted from the
iter-199 helper. The Nat-recursion happens at the **projective-dimension
level** (an `Nat.rec` on `n : ℕ` with `pd M < n+1 → ⋯`), not at the
chain-complex level. Minimality (`d_n` image in `𝔪`) is then not needed
for the AB inductive step — it was a Bruns-Herzog stylistic choice, not
a content requirement.

Concrete 3-step recipe:

1. **Per-step bridge (one-shot helper, ~15 LOC)**. From the iter-199
   `exists_minimalSurjection_finite_localRing` extract a
   `CategoryTheory.ShortComplex (ModuleCat R)` with `ShortExact`:
   `0 → ker f → (ModuleCat.of R (Fin n → R)) → (ModuleCat.of R M) → 0`.
   Use `CategoryTheory.ShortComplex.moduleCatMkOfKerLERange` +
   `ShortComplex.ShortExact.mk'` (`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`
   and `…ShortExact`). Mark `ker f` as `Module.Finite` via
   `Module.FinitePresentation.fg_ker` + `Module.finitePresentation_of_finite`
   (Noetherian).
2. **Syzygy-descent helper (~15-25 LOC)**. From
   `HasProjectiveDimensionLT (ModuleCat.of R M) (k+2)` and the SES from
   step 1, conclude `HasProjectiveDimensionLT (ModuleCat.of R (ker f)) (k+1)`
   via `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁` (with
   `HasProjectiveDimensionLT (R^n) 1` from
   `projective_iff_hasProjectiveDimensionLT_one` + `ModuleCat.projective_of_free`).
3. **Inductive-step assembly (~20-40 LOC)**. The `pd_R(M) = k + 1`
   sub-case of `auslander_buchsbaum_formula` now becomes: apply step 2
   to obtain a syzygy `K` with `pd K = k`. The induction hypothesis on
   `K` (over the same `R`) gives `k + depth K = depth R`. Then use the
   long-exact `Ext^*(κ, -)` sequence on the iter-199 SES to relate
   `depth M` to `depth K`: precisely `depth K = depth M + 1` when
   `R^n` is free (use `depth_pi_const_eq_depth_of_nonempty` for
   `depth (R^n) = depth R` plus `depth_of_short_exact`, both already
   axiom-clean in this file). Combine: `(k+1) + depth M = depth R`.

This recipe lives entirely inside ~40-80 LOC IF Mathlib's
`hasProjectiveDimensionLT_X₁` is available at the version pin
`b80f227` — that needs verification by the prover with `lean_verify`
before committing. If unavailable, the inductive descent on
`projectiveDimension … ≤ n+1` is still feasible by hand at ~60-100 LOC.

The depth-on-SES content is independent of which projective-dimension
carrier is chosen; it's already in the file as `depth_of_short_exact`.

**What NOT to do**: do NOT build a concrete `ChainComplex ℕ (ModuleCat R)`
via `ChainComplex.mk'`. The literal Bruns-Herzog 1.5.18 construction is
not the Mathlib idiom for this inductive content, and the bottom-out
proof at length `pd_R(M)` requires `Module.Free`-of-finite-projective-
over-local lemmas that the project would need to build first
(NEEDS_MATHLIB_GAP_FILL) — pushing the ~40-80 LOC estimate to ~150-250 LOC
of project-side scaffolding before any AB content lands.
