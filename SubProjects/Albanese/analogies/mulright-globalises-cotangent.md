# Analogy: shear-iso globalisation of `Ω_{G/k}` (piece (i.b)) — composition with iter-131 (B)-body

## Slug
mulright-globalises-iter133

## Iteration
133

## Question

What is the canonical Mathlib pattern for proving that the relative
cotangent sheaf `Ω_{G/k}` of a smooth group scheme `G/k` is trivialised
by translation? Two sub-questions matter:

(A) Does Mathlib have a precedent for the shear-iso globalisation
    `σ = ⟨pr₁, μ⟩ : G ×_k G ≅ G ×_k G` as a categorical map in
    `Over (Spec k)` built from `GrpObj` data only, and what's the
    Mathlib idiom for the natural iso `Ω_{G/k} ≅ pr₁^*(η_G^* Ω_{G/k})`?

(B) Does the iter-131 `Classical.choose`-chain body of
    `cotangentSpaceAtIdentity` compose with the shear-iso globalisation
    step? In particular, does piece (i.b)'s closure require a
    (B)→(A) bridge from the chart-base-changed body to the
    stalk-side `Ideal.IsLocalRing.CotangentSpace 𝔪_{η_G}`?

## Project artifact(s)

- `AlgebraicJacobian/Cotangent/GrpObj.lean:149-188` — `cotangentSpaceAtIdentity`
  (pure-term `noncomputable def`, outer head symbol
  `(ModuleCat.extendScalars ψ_V.hom).obj (ModuleCat.of Γ(G, V) Ω[Γ(G, V) ⁄ Γ(Spec k, U)])`).
- `AlgebraicJacobian/Cotangent/GrpObj.lean:198-219` —
  `cotangentSpaceAtIdentity_eq_extendScalars` companion structural-shape lemma.
- `AlgebraicJacobian/Cotangent/GrpObj.lean:244-282` —
  `cotangentSpaceAtIdentity_finrank_eq` rank lemma (iter-132 close).
- `blueprint/src/chapters/RigidityKbar.tex:243-268` —
  `lem:GrpObj_mulRight_globalises` blueprint statement and proof sketch
  (target Lean name `AlgebraicGeometry.GrpObj.mulRight_globalises_cotangent`).
- `analogies/cotangent-body-shape.md` — iter-131 prior analogist work on
  the body shape and the (B) closure chain.

## Decisions identified

### Decision 1: Shear iso `σ = ⟨pr₁, μ⟩ : G ⊗ G ≅ G ⊗ G` — Mathlib precedent

- **Mathlib idiom**: NO packaged shear-iso for the binary product. The
  closest precedents are:
  - `CategoryTheory.GrpObj.mulRight`
    (`Mathlib.CategoryTheory.Monoidal.Grp_.lean:277`): an `A ≅ A`
    automorphism `lift (𝟙 _) (toUnit _ ≫ f) ≫ μ` where `f : 𝟙_ ⟶ A`
    is a global element. Defined for any `GrpObj A` in any
    `CartesianMonoidalCategory C`. **This is *not* the binary-product
    shear** — it has only one free input, not two — but it uses the
    structurally identical idiom `lift _ _ ≫ μ`.
  - `CategoryTheory.GrpObj.isPullback`
    (`Mathlib.CategoryTheory.Monoidal.Grp_.lean:293`): the associativity
    diagram `μ ▷ A ⋯ μ` is Cartesian. The pullback-cone construction
    at lines 296-323 internally uses exactly the σ/τ shear-style
    `lift … (lift … ι …) ≫ μ` construction, so all categorical
    machinery (`lift_lift_assoc`, `lift_comp_inv_left`,
    `eq_lift_inv_right`, …) lives in this file already.
  - `Homeomorph.shearMulRight`
    (`Mathlib.Topology.Algebra.Group.Basic.lean:632`): the type-level
    shear for *topological groups* (`(x,y) ↦ (x, x*y)`, `G × G ≃ₜ G × G`).
    Requires actual `[Group G]` typeclass on the carrier, not `GrpObj`
    in a category. Used only in the alg-closed-base branch of
    `Mathlib.AlgebraicGeometry.Group.Smooth.lean:50-51` via
    `pointEquivClosedPoint` — exactly the construction the iter-127
    over-k risk register flags as forbidden.

- **Project's proposed path** (per blueprint `RigidityKbar.tex:243-268`):
  build `σ_hom := lift (fst G G) μ : G ⊗ G ⟶ G ⊗ G` and
  `σ_inv := lift (fst G G) (lift (fst G G ≫ ι) (snd G G) ≫ μ)` (= the
  `τ = ⟨pr₁, μ ∘ (ι × id)⟩` of the sketch), in `Over (Spec (.of k))`,
  from `GrpObj` data only. Verify `σ_hom ≫ σ_inv = 𝟙` and
  `σ_inv ≫ σ_hom = 𝟙` via the `lift_*` calculus.

- **Gap**: NEEDS_MATHLIB_GAP_FILL. Mathlib has all building blocks
  (`lift`, `μ`, `ι`, `lift_lift_assoc`, `lift_comp_inv_left`,
  `lift_comp_inv_right`) and the precedent `isPullback` shows the exact
  proof shape, but the *packaged* `A ⊗ A ≅ A ⊗ A` shear iso is not
  shipped. The project must build it.

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** with strong directional
  guidance: model the construction *exactly* on `GrpObj.mulRight`
  (Grp_.lean:277-281), extended to take both factors as inputs. The
  inverse-pair proof should reuse `lift_lift_assoc`, `lift_comp_inv_left`,
  `lift_comp_inv_right`, and `comp_lift_assoc`. **LOC for shear-iso
  construction alone: 30–60 LOC**.

### Decision 2: Natural iso `Ω_{(G ×_k G)/G} ≅ pr_2^* Ω_{G/k}` (pullback of relative cotangent under base change)

- **Mathlib idiom**:
  - Ring level: `KaehlerDifferential.tensorKaehlerEquiv`
    (`Mathlib.RingTheory.Kaehler.TensorProduct.lean`): for an
    `Algebra.IsPushout R S A B` square, `B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S]`.
    This is the algebra-side base-change-of-Ω iso.
  - Scheme level: **does not exist in Mathlib**. There is no scheme-level
    `relativeDifferentialsPresheaf` in Mathlib at all — the project's
    `AlgebraicGeometry.Scheme.relativeDifferentialsPresheaf` (in
    `AlgebraicJacobian/Differentials.lean:51-54`) is home-grown, built on
    `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`.
  - Sheaf-level base-change iso: not present even in Mathlib's algebraic
    geometry, because the cotangent *sheaf* (as opposed to the cotangent
    *presheaf* the project ships) is not in Mathlib.

- **Project's proposed path**: NOT YET ENCODED. The blueprint sketches
  the natural iso prose but does not give a Lean-level construction.

- **Gap**: NEEDS_MATHLIB_GAP_FILL (sheaf-level pullback compatibility
  for `relativeDifferentialsPresheaf`). The project must build this
  alongside piece (i.b), and the construction is **independent of
  Decision 1**.

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** — a sheaf-level pullback
  compatibility lemma for `relativeDifferentialsPresheaf` is the
  load-bearing piece of (i.b). The honest closure path needs
  `Hom.pullback` on `PresheafOfModules` (exists, via `TopCat.Presheaf.pullback`
  composed with the `CommRingCat`-side change-of-rings extending scalars)
  plus a `relativeDifferentialsPresheaf`-compatibility lemma chaining
  this with the algebra-side `KaehlerDifferential.tensorKaehlerEquiv`.
  **LOC for the natural iso: 150–300 LOC**.

### Decision 3: Does the iter-131 `Classical.choose`-chain body compose with the shear iso?

This is the directive's central question. The answer depends on **what
the lemma's RHS uses as its "fibre object"**.

- **Sheaf-level statement** (the blueprint's literal reading): the
  trivialisation has the form
  `relativeDifferentialsPresheaf G.hom ≅ pullback_along_str_map (pullback_along_η_G (relativeDifferentialsPresheaf G.hom))`
  where the inner pullback is a `Spec k`-module-valued presheaf (one
  point, fibre = `k`-module). **Under this statement, the body of
  `cotangentSpaceAtIdentity` does NOT enter the shear-iso lemma at all**
  — the lemma is entirely sheaf-theoretic, and `η_G^* Ω_{G/k}` is an
  abstract object (the pullback presheaf, not a `ModuleCat k`).

- **Value-level statement** (an alternate phrasing that pre-bridges to
  the project's existing `cotangentSpaceAtIdentity`): the RHS replaces
  `η_G^* Ω_{G/k}` with the (sheaf promotion of the) `ModuleCat k`-valued
  `cotangentSpaceAtIdentity G`. **Under this statement, the body's
  `extendScalars (ψ_V.hom)`-of-`Ω[Γ(G,V)⁄Γ(Spec k, U)]` form is the RHS
  fibre** — and a bridge from "abstract pullback presheaf" to "chart-
  base-changed `ModuleCat k`" is required.

- **The bridge needed is NOT the (B)→(A) stalk-cotangent bridge**
  (`m_{η_G}/m_{η_G}^2`-flavoured, ~300–600 LOC per
  `analogies/cotangent-body-shape.md` and blueprint
  `lem:GrpObj_cotangent_bridge`). What's needed is a
  **chart-localisation identification**
  `η_G^* (relativeDifferentialsPresheaf G.hom) ≅ <sheaf-promotion of cotangentSpaceAtIdentity G>`,
  which composes:
  - `relativeDifferentialsPresheaf` restricted along `η_G` produces a
    `Spec k`-presheaf whose sections over the chart `V ⊆ G` are the
    base-change `Γ(Spec k, ·) ⊗_{Γ(G, V)} Ω[Γ(G, V)⁄Γ(Spec k, U)]` — by
    `relativeDifferentialsPresheaf_obj_kaehler` (in `Differentials.lean:60`)
    + the canonical `Γ(Spec k, η_G^{-1}V) ≅ k` (via `Scheme.ΓSpecIso`).
  - The body of `cotangentSpaceAtIdentity G` is, by
    `cotangentSpaceAtIdentity_eq_extendScalars`, exactly this base
    change.
  So the two are isomorphic by `rfl` modulo a `Scheme.ΓSpecIso`
  insertion and an `extendScalars`-vs.-`TensorProduct` shape massage.

- **LOC estimate for the chart-localisation identification**: 100–200 LOC.
  The work is in (i) plumbing `relativeDifferentialsPresheaf`'s
  presheaf-level restriction along `η_G` (which the project already has
  fragments of in `Differentials.lean`), and (ii) bridging the resulting
  `Γ(Spec k, top) ⊗ ⋯` shape to the body's `extendScalars` shape (which
  is a thin wrapper).

- **Gap**: divergent-with-cost (the divergence is unavoidable since
  Mathlib doesn't have the sheaf-level relative cotangent at all), but
  the cost is **NOT** the iter-130 strategy-critic Q2 worry of 300–600
  LOC for the stalk-side `m/m²` bridge. The cost is 100–200 LOC for the
  chart-localisation identification, which is a structurally different
  (and much smaller) artefact.

- **Verdict**: **PROCEED** on the iter-131 body shape — it composes
  cleanly with piece (i.b). The bridge that piece (i.b) needs is the
  chart-localisation identification, not the (B)→(A) stalk bridge. The
  trio→duo collapse (iter-131 strategy-critic Q4) holds: the stalk
  bridge `lem:GrpObj_cotangent_bridge` remains vestigial.

### Decision 4: Lemma statement style for `mulRight_globalises_cotangent` (RHS choice)

- **Mathlib idiom**: Mathlib has no scheme-level Lie-algebra-trivialisation
  precedent. The closest precedent is the manifold-level
  `mulInvariantVectorField` (`Mathlib.Geometry.Manifold.GroupLieAlgebra.lean:62`),
  which uses a **pointwise** trivialisation (vector at identity →
  vector field everywhere via translation) — but this requires
  `[Group G]` + `[ChartedSpace H G]` and works pointwise on points, the
  same forbidden idiom (per iter-127 over-k risk register) as
  `pointEquivClosedPoint` and `Homeomorph.shearMulRight`.

- **Project's proposed path** (blueprint `RigidityKbar.tex:252-256`):
  `Ω_{G/k} ≅ pr_1^* (η_G^* Ω_{G/k})`, with `η_G^* Ω_{G/k}` left abstract
  as a `Spec k`-presheaf. This matches Decision 3's sheaf-level
  statement.

- **Recommendation**: **state the lemma at the sheaf level** with the
  abstract `η_G^* Ω_{G/k}` RHS. This decouples piece (i.b) from the
  body of `cotangentSpaceAtIdentity` entirely. Piece (i.c) (`omega_free`)
  then consumes a chart-localisation identification lemma
  `cotangent_pullback_iso_cotangentSpaceAtIdentity` (≅ 100–200 LOC, not
  blocking on the iter-130 deferred stalk bridge) to translate the
  shear iso's abstract RHS into the rank-`n` free `k`-module that
  iter-132's `cotangentSpaceAtIdentity_finrank_eq` already supplies.

- **Verdict**: **ALIGN_WITH_MATHLIB** in spirit (use the sheaf-level
  pullback-presheaf idiom, not pointwise-translation), even though
  Mathlib has no direct precedent. The pointwise idiom (matching
  Mathlib's `mulInvariantVectorField` / `Homeomorph.shearMulRight`)
  must be **avoided** since it requires alg-closure of the base, which
  iter-127 forbids.

## Recommendation

**Verdict for the iter-134+ prover lane on piece (i.b): PROCEED with
the clean composition path.** The iter-131 `Classical.choose`-chain body
of `cotangentSpaceAtIdentity` **does compose cleanly** with the
shear-iso globalisation. The directive's worry about a (B)→(A) stalk
bridge is unfounded — the bridge piece (i.b) needs is a *chart-
localisation identification*, not a *stalk-cotangent identification*,
and is ~100–200 LOC rather than ~300–600 LOC.

Recommended Lean encoding for piece (i.b):

1. **Shear iso construction** (~30–60 LOC): build
   `GrpObj.shearMulRight : (G ⊗ G : Over (Spec (.of k))) ≅ G ⊗ G` modelled
   on `CategoryTheory.GrpObj.mulRight` (Grp_.lean:277-281). Use
   `lift (fst G G) μ` as hom, `lift (fst G G) (lift (fst G G ≫ ι) (snd G G) ≫ μ)`
   as inv. Discharge `hom_inv_id`/`inv_hom_id` via `comp_lift_assoc`,
   `lift_lift_assoc`, `lift_comp_inv_left`, `lift_comp_inv_right` (the
   same idioms used by `GrpObj.mulRight` and `GrpObj.isPullback`).

2. **Natural iso of `Ω` under pullback** (~150–300 LOC):
   state and prove
   `relativeDifferentialsPresheaf (μ.left : G.left ×_k G.left ⟶ G.left) ≅
    pr_2^* (relativeDifferentialsPresheaf G.hom)`
   (or, more precisely, `Ω_{(G ×_k G)/G} ≅ pr_2^* Ω_{G/k}` for the
   second-projection structure morphism). The build chains
   `TopCat.Presheaf.pullback` with the algebra-side
   `KaehlerDifferential.tensorKaehlerEquiv` via the project's
   `relativeDifferentialsPresheaf_obj_kaehler`.

3. **Apply shear iso + restriction to identity section** (~30–80 LOC):
   pull back along `σ`, then restrict along
   `⟨𝟙_G, η_G⟩ : G → G ×_k G` (the section that picks out the
   "evaluate at identity" coordinate). Output:
   `relativeDifferentialsPresheaf G.hom ≅ pr_1^* (η_G^* relativeDifferentialsPresheaf G.hom)`.

4. **(Separate lemma, ~100–200 LOC; NOT in piece (i.b)'s body)**:
   chart-localisation identification
   `η_G^* relativeDifferentialsPresheaf G.hom ≅
    <sheaf-promotion of cotangentSpaceAtIdentity G>`
   for downstream piece (i.c) consumption. This composes the
   `Classical.choose`-chain (re-extracting `U, V, ψ_V`) with the
   presheaf-restriction-along-η_G computation. Closes essentially by
   chaining `relativeDifferentialsPresheaf_obj_kaehler` and
   `cotangentSpaceAtIdentity_eq_extendScalars`.

**Total LOC envelope for piece (i.b) (steps 1–3): 210–440 LOC.** Plus
the chart-localisation identification (step 4) at 100–200 LOC consumed
in piece (i.c). The original directive envelope of 200–500 LOC for
piece (i.b) **holds**.

## Trigger (a') refinement

The iter-130 trigger (a') as written in STRATEGY.md monitors whether
piece (i.b) closure requires an inline (B)→(A) bridge — i.e., whether
the project must build the deferred stalk-cotangent bridge
`lem:GrpObj_cotangent_bridge` to close piece (i.b).

**Refined trigger (a') condition (iter-133 mathlib-analogist verdict)**:

The trigger should fire if **and only if** the iter-134+ prover lane
chooses to state `mulRight_globalises_cotangent` with the value-level
RHS (using `Ideal.IsLocalRing.CotangentSpace 𝔪_{η_G}` directly). If the
prover lane states the lemma at the **sheaf level** with an abstract
`η_G^* Ω_{G/k}` RHS (this analogist's recommendation), trigger (a')
**does not fire** — the iter-131 body composes cleanly via the chart-
localisation identification, which is structurally distinct from the
stalk-cotangent bridge.

**Recommended STRATEGY.md update**: rephrase trigger (a') as
"*piece (i.b) RHS uses stalk-cotangent `m/m²`*" rather than
"*piece (i.b) needs to identify cotangent at identity as fibre object*".
The latter is too permissive and triggers on a different (cheaper)
artefact.

## Bridge-cost-per-closure-path summary

| Closure path | Piece (i.b) LOC | Bridge needed | Trigger (a') fires? |
|---|---|---|---|
| Sheaf-level RHS, abstract fibre (recommended) | 210–440 | chart-localisation iso (~100–200 LOC, consumed in (i.c) not (i.b)) | NO |
| Value-level RHS via `cotangentSpaceAtIdentity` | 310–640 | chart-localisation iso (inline, ~100–200 LOC) | NO |
| Value-level RHS via stalk `m/m²` | 500–1100 | (B)→(A) stalk bridge (inline, ~300–600 LOC) | YES |

The directive's worry-scenario (500–1100 LOC, route pivot) corresponds
to the third row, which the iter-134+ prover lane should explicitly
avoid by adopting the sheaf-level RHS phrasing (top row).
