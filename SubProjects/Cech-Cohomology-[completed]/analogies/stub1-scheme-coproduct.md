# Analogy: Stub 1 — coproduct distributes over the (iterated) fibre power of the cover map

## Mode
api-alignment

## Slug
stub1-coproduct

## Iteration
057

## Question
Identify `(coverCechNerveOver 𝒰).obj (op [p])` — the degree-`p` Čech-nerve object of the cover
arrow `q = Sigma.desc 𝒰.f : ∐ᵢ Uᵢ → X`, i.e. the `(p+1)`-fold fibre power of `q` over `X` — with
`∐_{σ : Fin (p+1) → 𝒰.I₀} coverInterOpen 𝒰 σ` in `Over X`. Mathematically: **coproducts distribute
over the (iterated) fibre product**. Does Mathlib provide the structural ingredient (A binary
distributivity, B open-immersion pullback = intersection, C the iterated/wide version), or is this a
genuine from-scratch build, and at what cost?

## Project artifact(s)
- `CechSectionIdentification.lean:76` — `cechBackbone_left_sigma` (Stub 1, `sorry`); planner strategy comment above it.
- `CechHigherDirectImage.lean:102` — `coverArrow 𝒰 = Arrow.mk (Sigma.desc 𝒰.f)`.
- `CechHigherDirectImage.lean:111` — `coverCechNerve 𝒰 = (coverArrow 𝒰).augmentedCechNerve`.
- `CechHigherDirectImage.lean:552` — `coverCechNerveOver 𝒰 = Over.lift (coverCechNerve 𝒰).left (coverCechNerve 𝒰).hom`.
- `FreePresheafComplex.lean:129,135` — `coverOpen 𝒰 i = (𝒰.f i).opensRange`; `coverInterOpen 𝒰 σ = ⨅ k, coverOpen 𝒰 (σ k)`.

## What the LHS actually is (verified)
`Arrow.cechNerve f` has `obj n := widePullback f.right (fun _ : Fin (n.unop.len + 1) => f.left) (fun _ => f.hom)`
(`Mathlib/AlgebraicTopology/CechNerve.lean:56`). Hence the underlying scheme of
`(coverCechNerveOver 𝒰).obj (op [p])` is
`widePullback X (fun _ : Fin (p+1) => ∐ᵢ Uᵢ) (fun _ => q)` — a **wide pullback over `X`** of `p+1`
copies of `∐ᵢ Uᵢ`, with structure map `WidePullback.base`. (`coverCechNerveOver` just lifts this
Scheme-level object into `Over X` along the augmentation `(coverCechNerve 𝒰).hom = WidePullback.base`.)
So the target is genuinely an **`(p+1)`-fold (wide) fibre power**, not an iterated binary pullback.

## Decisions identified

### Decision: A — binary coproduct × pullback distributivity for `Scheme`
- **Mathlib idiom**: `Scheme` is `FinitaryExtensive`, and Mathlib ships the distributivity as an `IsIso`
  instance + an `IsPullback` lemma:
  - `AlgebraicGeometry.instFinitaryExtensiveScheme : FinitaryExtensive Scheme` (module `Mathlib.AlgebraicGeometry.Limits`). **VERIFIED** (leansearch).
  - `AlgebraicGeometry.instHasFiniteCoproductsScheme : HasFiniteCoproducts Scheme` (same module). **VERIFIED**.
  - `instance : HasPullbacks Scheme` — `Mathlib/AlgebraicGeometry/Pullbacks.lean:470`. **VERIFIED**.
  - `CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_map` — `Mathlib/CategoryTheory/Extensive.lean:568`
    (an **instance**): for finite `ι, ι'`, `f : ∀ i, X i ⟶ S`, `g : ∀ i, Y i ⟶ S`,
    `IsIso (Sigma.desc fun p : ι × ι' ↦ pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) …)`,
    i.e. `(∐ X) ×_S (∐ Y) ≅ ∐_{(i,j)} (X i ×_S Y j)`. **VERIFIED** (read source). Requires only
    `[HasPullbacks C] [FinitaryPreExtensive C]` — both hold for `Scheme`.
  - `CategoryTheory.FinitaryPreExtensive.isPullback_sigmaDesc` — `Extensive.lean:590` (same content as `IsPullback`). **VERIFIED**.
  - `CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_fst` — `Extensive.lean:552`. NB: hypothesis is
    `IsIso (Sigma.desc π)` (the family must already cover `X` isomorphically), so it is **not** the
    general one-sided distributivity. The general one-sided form `(∐ X) ×_S Y ≅ ∐_i (X i ×_S Y)`
    is `isIso_sigmaDesc_map` with the second family a singleton (`ι' := PUnit`). **VERIFIED**.
- **Project's path**: planner comment guessed `Scheme.pullback_openCover_iSup` / "sigma fibre-product
  distribution"; the prover reported "no coproduct-distributes-over-fibre-product for Scheme". That is
  **wrong for the binary case** — the binary distributivity IS in Mathlib, for free, via extensivity.
- **Gap**: identical (Mathlib has it; use directly).
- **Verdict**: **PROCEED** — binary distributivity is off-the-shelf for `Scheme`.

### Decision: B — pullback of open immersions = intersection
- **Mathlib idiom**:
  - `AlgebraicGeometry.isPullback_opens_inf (U V : X.Opens) : IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) U.ι V.ι`
    — `Mathlib/AlgebraicGeometry/Restrict.lean:548`. I.e. `(U ⊓ V).toScheme` with the two `homOfLE`
    inclusions IS the pullback of `U.ι, V.ι`; so `pullback U.ι V.ι ≅ (U ⊓ V).toScheme`. **VERIFIED** (read source).
  - `AlgebraicGeometry.isPullback_opens_inf_le` — `Restrict.lean:542` (relative `≤ W` version). **VERIFIED**.
  - `AlgebraicGeometry.isPullback_morphismRestrict` — `Restrict.lean:530` (the underlying brick). **VERIFIED**.
- **Project's path**: Stub 3 (`pushPull_leg_sections`, already built) used `image_preimage_eq_opensRange_inf`
  + `opensRange_ι` for the *sections*; the *scheme*-level intersection iso `isPullback_opens_inf` is the
  matching geometric statement.
- **Gap**: identical (binary). The **wide** version `widePullback X (fun k => U_{σk}) (fun k => j_{σk}) ≅ ⨅ₖ U_{σk}` is **ABSENT**.
- **Verdict**: **PROCEED** for the binary brick; the wide intersection must be assembled (see C/D).

### Decision: C — iterated / wide fibre power of a coproduct
- **Mathlib status — the direct wide lemma is ABSENT.** There is no `Scheme` (or general
  `FinitaryExtensive`) lemma stating `widePullback`-of-coproducts `≅ ∐` over tuples, and no
  `Arrow.cechNerve`-of-a-coproduct decomposition for schemes.
- **Closest packaging (combinatorics only, NOT portable for free)**:
  `CategoryTheory.Limits.FormalCoproduct.cechIsoCechNerve` /
  `…cechIsoAugmentedCechNerve` — `Mathlib/CategoryTheory/Limits/FormalCoproducts/ExtraDegeneracy.lean:78,86`.
  For `U : FormalCoproduct C` and terminal `T`, this is exactly
  `U.cech ≅ Arrow.cechNerve (Arrow.mk (T-incl.from U))`, where `U.cech.obj n = U.power (Fin (n+1))` is
  the formal coproduct `∐_{i : Fin(n+1)→U.I} ∏ᶜ (U.obj ∘ i)` (`Cech.lean:34` `power`, `:186` `cech`).
  **This is the coproduct-distributes-over-the-Čech-nerve statement** — but stated *inside*
  `FormalCoproduct C`, where products distribute over coproducts by construction.
  **Why it is not free for schemes**: transporting it to `Over X` needs a realization functor
  `FormalCoproduct (Over X) ⥤ Over X` that **preserves finite products** — and product-preservation of
  that realization IS exactly the extensivity/distributivity content. Mathlib builds **no** such
  realization (Basic.lean:31 explicitly leaves "does `incl` preserve limits?" open; only `incl : C ⥤ FormalCoproduct C`
  and `HasCoproducts (FormalCoproduct C)` exist, no functor back to `C`). So `FormalCoproduct` packages
  the *indexing combinatorics* (the σ-tuples, the simplicial maps) but cannot supply the geometric
  distributivity. **VERIFIED** (read Basic/Cech/ExtraDegeneracy).
- **Useful bricks for the build**:
  - `CategoryTheory.Limits.WidePullbackCone.isLimitOfFan` — `Mathlib/CategoryTheory/Limits/Constructions/WidePullbackOfTerminal.lean:46`:
    a wide pullback over a **terminal** base = the **product** of the legs. In `Over X` the base
    `Over.mk (𝟙 X)` is terminal, so `widePullback`(over X) ↔ `product in Over X` ↔ fibre power over X. **VERIFIED**.
  - `CategoryTheory.Limits.sigmaSigmaIso` — `Products.lean:621`: flattens `∐ᵢ ∐ⱼ ≅ ∐_{(i,j)}` (collapses
    the nested coproducts produced by iterating the binary distributivity). **VERIFIED**.
  - `Arrow.cechNerve` obj formula — `CechNerve.lean:56`. **VERIFIED**.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** — the wide/iterated distributivity is genuinely new; it is
  *reachable* by iterating A (+ collapsing with `sigmaSigmaIso`) and B, but is not a single off-the-shelf call.

## Recommendation

**Stub 1 is real (multi-iter) work, but the foundation the prover called missing (binary
distributivity for `Scheme`) is in fact PRESENT** — `Scheme` is `FinitaryExtensive` and
`isIso_sigmaDesc_map` + `isPullback_opens_inf` give A and B for free. Only the **wide/iterated** step
(C) must be built, by iterating the binary lemmas. Effort-break Stub 1 in the blueprint into:

1. **`backbone_obj_widePullback`** (≈30 LOC): `(coverCechNerveOver 𝒰).obj (op [p])` ≅ `Over.mk (WidePullback.base)`
   over `widePullback X (fun _:Fin(p+1)=>∐U) (fun _=>q)`. Pure unfolding of `Over.lift` / `augmentedCechNerve` / `cechNerve`.

2. **`coproduct_distrib_fibrePower`** — THE gap (≈120–200 LOC). Cheapest aligned route: prove it as a
   general `FinitaryPreExtensive` lemma (mirroring `isIso_sigmaDesc_map`, for the `(p+1)`-fold case) by
   **induction on `p`**, each step using `isIso_sigmaDesc_map` (singleton second family for the one-sided
   form) + `sigmaSigmaIso` to reindex the nested coproduct into one over `σ : Fin(p+1)→ι`. Use
   `WidePullbackCone.isLimitOfFan` to reformulate the wide pullback over `X` as a product in `Over X`
   (terminal base), where the iterated product has clean `Fin.cons`/reindexing recursion. Stating it
   abstractly (extensive C) keeps it Mathlib-aligned and reusable; instantiate at `C = Scheme`.

3. **`widePullback_openImm_inter`** (≈50–80 LOC): `widePullback X (fun k=>U_{σk}) (fun k=>j_{σk}) ≅ (coverInterOpen 𝒰 σ).toScheme`,
   over `X`. Iterate `isPullback_opens_inf` (B) along `Fin(p+1)`; the `⨅ₖ` bookkeeping is the
   `coverInterOpen` definition.

4. **`cechBackbone_left_sigma`** (≈40 LOC): assemble 1–3 in `Over X`, checking the structure maps to `X`
   agree (automatic — both sides factor through `WidePullback.base` / the `coverInterOpen` inclusions).

**One-session vs multi-iter**: **multi-iter** (≈250–350 LOC across the four sub-lemmas; step 2 alone is
a 2–3-cycle build). Dispatch a prover only after the blueprint effort-break gives each sub-lemma a
signature; step 2 (the abstract wide distributivity) is the load-bearing prover lane and the natural
unit to attempt first. Steps 1, 3, 4 are then mechanical given 2.
