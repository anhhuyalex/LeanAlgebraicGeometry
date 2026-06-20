# Analogy: d_app + d_map sub-sorry shape inside `basechange_along_proj_two_inv_derivation`

## Slug

d-app-d-map-iter141

## Iteration

141

## Question

Two pieces, one for each remaining sub-sorry inside
`basechange_along_proj_two_inv_derivation`
(`AlgebraicJacobian/Cotangent/GrpObj.lean:573–643`):

1. **d_app**: Is the iter-140 standalone-validated factoring-lemma pattern
   (`Derivation.map_algebraMap` route, with hand-set `Algebra` / `Module` /
   `IsScalarTower` instances) the right shape for closing the `d_app`
   sub-sorry at `Cotangent/GrpObj.lean:624`?

2. **d_map**: The iter-140 prover discovered a deterministic `whnf` timeout
   at `maxHeartbeats=200000` when attempting `change (CommRingCat.KaehlerDifferential.D _).d _ = _`
   on the d_map sub-sorry at `Cotangent/GrpObj.lean:643`. The blueprint
   claims the RHS reduction
   `((pushforward ψ).obj LHS).map f = LHS.map (snd⁻¹f)` is "definitional/
   transparent" per `Mathlib/Algebra/Category/ModuleCat/Presheaf/Pushforward.lean:39, 86`
   — but the prover empirically observed this NOT to be the case at the
   d_map field elaboration site. What is the right Mathlib idiom for
   computing `((pushforward ψ).obj LHS).map f` without invoking `whnf`?

## Project artifact(s)

- `AlgebraicJacobian/Cotangent/GrpObj.lean:540–550` — `isIso_of_app_iso_module` helper (iter-140 landed).
- `AlgebraicJacobian/Cotangent/GrpObj.lean:573–643` — `basechange_along_proj_two_inv_derivation`: d_add + d_mul closed; **d_app at L624** and **d_map at L643** remain sorry-bodied.
- `AlgebraicJacobian/Cotangent/GrpObj.lean:670–690` — main piece (i.b) Step 2 iso (residual IsIso sub-sorry not in scope this iter).
- `blueprint/src/chapters/RigidityKbar.tex:602–659` — d_app NOTE block (3-step categorical-chase recipe).
- `blueprint/src/chapters/RigidityKbar.tex:661–708` — d_map NOTE block (ψ-naturality + `relativeDifferentials'_map_d` chase; "definitional/transparent" claim).
- `task_results/Cotangent_GrpObj.lean.md` — iter-140 prover task result with §"d_app: detailed gap" L68–L108 and §"d_map: detailed gap" L111–L143.

## Mathlib infrastructure verified this iter

All names below were verified via `lean_local_search` + `lean_loogle` +
`lean_run_code` typecheck against the project's pinned Mathlib.

| Name | Module:Line | Used by |
|---|---|---|
| `ModuleCat.Derivation.d_map` | `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic:80` | d_app (the streamlined factoring-lemma closure) |
| `ModuleCat.Derivation.mk` (`d_map` field default `:= by simp`) | `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic:47–62` | d_app underlying field |
| `CommRingCat.KaehlerDifferential.D` | `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic:106` | both |
| `PresheafOfModules.pushforward` | `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward:86` | d_map |
| `PresheafOfModules.pushforward_obj_map_apply` | `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward:95–97` | d_map (the missing-named explicit unfolding lemma) |
| `PresheafOfModules.pushforward_obj_map_apply'` | `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward:99–106` | d_map (`@[simp]`-normal form; preferred for `simp only`) |
| `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d` | `Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf:201–207` | d_map |
| `CommRingCat.KaehlerDifferential.map_d` | `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic:152–155` | d_map (underlying ring-map base-change derivation commutation) |
| `NatTrans.naturality` (for ψ) | applied via `Scheme.Hom.c.naturality` | d_map (ψ-naturality piece) |

## The critical missing-name observation (d_map)

The blueprint's claim of "definitional/transparent per
`Mathlib/Algebra/Category/ModuleCat/Presheaf/Pushforward.lean:39, 86`"
was technically correct at the *underlying LinearMap-application level*:
the unfolding `(((pushforward φ).obj M).map f).hom m = M.map (F.op.map f) m`
is `rfl` (verified standalone via `lean_run_code` this iter; both the
named `pushforward_obj_map_apply` and direct `rfl` close it).

**But** the iter-140 prover's `change`-based approach failed because:

1. The `pushforward₀_obj` and `pushforward₀` definitions in Mathlib
   (`Pushforward.lean:37, 55`) are explicitly annotated with
   `set_option backward.isDefEq.respectTransparency false in`. This
   instructs Lean's `isDefEq` (and hence `whnf`) NOT to aggressively
   unfold these definitions during definitional-equality checks.

2. `change` invokes the kernel `whnf`-based `isDefEq` to align the goal
   with the target shape. When the d_map goal is wrapped inside the
   `Derivation'.mk` lambda context with floating metavariables (`?m.161,
   .162, .130, .91` per iter-140 task result), `whnf` has to traverse a
   deeply-nested adjunction-transposed expression including
   `pullbackPushforwardAdjunction.homEquiv` + `restrictScalars` + the
   `pushforward₀_obj` opacity wall. With `respectTransparency false` on
   `pushforward₀`, `whnf` cannot punch through this wall, and runs out
   of heartbeats at 200000.

3. **The right idiom**: bypass `whnf` entirely. Use the named lemma
   `pushforward_obj_map_apply'` (`@[simp]`-normal form) via `simp only
   [pushforward_obj_map_apply']` (which applies a single rewrite without
   `whnf` traversal). This delivers the unfolding the blueprint promised
   without paying the `whnf` cost. Then `change` (or further `simp only`)
   succeeds against the now-unfolded goal.

In iter-138 language: this is **not** a structural side-step (like the
helper-pair refactor for iter-138's `pullback` chart-opacity); it is a
**`NEEDS_MATHLIB_LEMMA_NAME`** verdict. The Mathlib lemma exists; the
blueprint correctly pointed to the file but did not name the lemma; the
iter-140 prover did not search for the named lemma and relied on
transparency that the `respectTransparency false` annotation explicitly
disables.

## The streamlined d_app pattern

The iter-140 prover's standalone-validated factoring-lemma recipe is
*correct in shape* but does extra work that the Mathlib API already
packages. The iter-140 version:

```lean
example (A B C : CommRingCat) (f1 : A ⟶ B) (g : C ⟶ B) (k : A ⟶ C)
    (hcomm : k ≫ g = f1) (a : A) :
    (CommRingCat.KaehlerDifferential.D g).d (f1.hom a) = 0 := by
  have heq : f1.hom a = g.hom (k.hom a) := by rw [← hcomm]; rfl
  rw [heq]
  letI : Algebra C B := g.hom.toAlgebra
  letI : Module C (CommRingCat.KaehlerDifferential g) :=
    Module.compHom _ (algebraMap C B)
  letI : IsScalarTower C B (CommRingCat.KaehlerDifferential g) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact (CommRingCat.KaehlerDifferential.D g :
    Derivation C B (CommRingCat.KaehlerDifferential g)).map_algebraMap _
```

The streamlined version (verified this iter via `lean_run_code`):

```lean
example (A B C : CommRingCat) (f1 : A ⟶ B) (g : C ⟶ B) (k : A ⟶ C)
    (hcomm : k ≫ g = f1) (a : A) :
    (CommRingCat.KaehlerDifferential.D g).d (f1.hom a) = 0 := by
  rw [show f1.hom a = g.hom (k.hom a) from by rw [← hcomm]; rfl]
  exact (CommRingCat.KaehlerDifferential.D g).d_map _
```

This uses `ModuleCat.Derivation.d_map` (Basic.lean:80) which IS exactly
the `map_algebraMap`-based zero-on-image lemma the iter-140 version
hand-rolls. Mathlib already has the `Algebra` / `Module` /
`IsScalarTower` instance discharge bundled inside `ModuleCat.Derivation`.

LOC saving: 4 LOC per use; clearer intent.

## Decisions identified

### Decision 1: d_app closure recipe shape

- **Mathlib idiom**: `ModuleCat.Derivation.d_map`
  (`Mathlib.Algebra.Category.ModuleCat.Differentials.Basic:80`) — the
  `@[simp]` lemma `D.d (f a) = 0` for derivations over a ring map.
  Plus the categorical-witness construction of `h : Source ⟶ Target`
  factoring `(ψ.app X) ∘ (φ_G.app X)` through `φ_LHS.app (snd⁻¹X)`,
  which has no Mathlib shortcut (it's the project's bespoke
  categorical-chase work).
- **Project's current path**: iter-140 prover's standalone-validated
  factoring-lemma recipe — sound in shape, with the streamlining
  recommendation above (`d_map` for `letI ... + map_algebraMap`).
- **Gap**: identical (recipe shape) modulo the 4-LOC streamlining.
- **Cost of divergence (if any)**: ~4 LOC of redundant instance
  discharge per call site; minor.
- **Verdict**: **PROCEED** with iter-140 shape; recommend `d_map`
  streamlining at writing time.

### Decision 2: Construction of the factoring witness `h` (d_app)

- **Mathlib idiom**: NONE PACKAGED. The factoring witness for d_app
  comes from chasing `(fst G G).w + (snd G G).w` (the `Over (Spec k)`
  morphism property), via `LocallyRingedSpace.comp_c_app`, transposed
  through `pullbackPushforwardAdjunction.homEquiv.symm`. Each ingredient
  is a Mathlib lemma; there is no one-shot combiner.
- **Project's current path**: per blueprint `RigidityKbar.tex:643–659`
  + iter-140 prover recipe step 4 — construct `h` from the categorical
  identity in 3 stages (categorical equality in `Over (Spec k)`,
  scheme-level lift via `comp_c_app`, adjunction-transpose). Each stage
  is a `simp`/`erw`-driven step.
- **Gap**: NEEDS_MATHLIB_GAP_FILL — the categorical chase is bespoke;
  no equivalent is packaged.
- **Cost of divergence**: ~40–80 LOC of categorical chase (iter-140
  prover estimate confirmed).
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**; the project must build it.
  The closure recipe shape (factoring lemma + `d_map`) is the
  Mathlib-canonical algebra-side step; the witness construction is
  project-specific.

### Decision 3: d_map closure — the missing-name explicit unfolding lemma

- **Mathlib idiom**: `PresheafOfModules.pushforward_obj_map_apply'`
  (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward:99–106`,
  `@[simp]`-normal form). This is the `simp`-canonical underlying
  LinearMap-application identity
  `(((pushforward φ).obj M).map f).hom m = M.map (F.map f.unop).op m`,
  proved by `rfl` (verified this iter standalone via `lean_run_code`).
- **Project's current path**: iter-140 prover attempted `change
  (CommRingCat.KaehlerDifferential.D _).d _ = _` — which invokes `whnf`
  through the `pushforward₀` opacity wall (where
  `set_option backward.isDefEq.respectTransparency false` is explicitly
  set at `Pushforward.lean:37, 55`). This caused a deterministic
  heartbeat timeout at 200000.
- **Gap**: divergent-and-wrong — the prover's approach was
  fundamentally incompatible with Mathlib's transparency annotation;
  the blueprint correctly identified the file but did not name the
  lemma.
- **Cost of divergence**: would block all d_map closure attempts via
  `change`-based approaches at any heartbeat budget; the
  `respectTransparency false` is a guard, not a performance issue.
- **Verdict**: **NEEDS_MATHLIB_LEMMA_NAME** — the lemma is
  `pushforward_obj_map_apply'` (or the underlying `pushforward_obj_map_apply`
  for explicit `rw`). Re-route the recipe through this lemma.

### Decision 4: d_map closure recipe shape (after Decision 3 fix)

- **Mathlib idiom**: three-step chase using:
  1. `pushforward_obj_map_apply'` (RHS unfolding via `simp only`).
  2. `NatTrans.naturality` (or `NatTrans.naturality_apply`) for ψ =
     `(toRingCatSheafHom (snd G G).left).hom` (which is `(snd G G).left.c`
     whiskered with `forget₂` per `Mathlib.AlgebraicGeometry.Modules.Presheaf:42–45`).
  3. `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d`
     (Presheaf.lean:201–207, `@[simp]`-tagged) — commutation of the
     universal Kähler derivation with `R.map f`.
- **Project's current path** (after fix): inside the `Derivation'.mk`
  d_map field lambda
  `fun X Y f x => by ... sorry`, the closure body:
  ```lean
  fun X Y f x => by
    -- Step 1: unfold the pushforward .map via the named lemma
    simp only [pushforward_obj_map_apply']
    -- Step 2: rewrite via ψ-naturality
    have hψ := NatTrans.naturality_apply
      (Scheme.Hom.toRingCatSheafHom (snd G G).left).hom f x
    -- Step 3: use the four-step "have h := ... ; change ... ; rw [h] ; exact ..."
    -- pattern (from iter-138 codified d_add/d_mul closures) to chain
    -- ψ-naturality with relativeDifferentials'_map_d.
    -- (Details depend on the exact metavariable shape at the call site.)
    sorry
  ```
- **Gap**: identical to Mathlib idiom once Decision 3's named lemma is
  threaded in.
- **Verdict**: **ALIGN_WITH_MATHLIB** — re-route via the named
  unfolding lemma + ψ-naturality + `relativeDifferentials'_map_d`.

### Decision 5: LOC envelope for d_app + d_map combined

- **d_app** (Decision 1 + Decision 2 combined): ~50–90 LOC.
  - ~5–10 LOC: the algebra-side discharge using the streamlined
    `d_map` lemma.
  - ~40–80 LOC: the categorical-witness construction of `h` (the
    load-bearing part — categorical commutativity in `Over (Spec k)`
    + `LocallyRingedSpace.comp_c_app` + adjunction-transpose).
- **d_map** (Decision 3 + Decision 4): ~30–50 LOC.
  - ~5 LOC: `simp only [pushforward_obj_map_apply']` step.
  - ~10–15 LOC: ψ-naturality `have` + `change` / `rw` chain (mimicking
    the iter-138 d_add/d_mul four-step pattern).
  - ~10–15 LOC: `relativeDifferentials'_map_d` discharge with
    metavariable cleanup.
  - ~5–15 LOC: type-noise smoothing (`erw`, `dsimp`, restrictScalars
    fiddling).
- **Combined**: ~80–140 LOC.
- **Envelope check**: cumulative (i.b)-side build entering iter-141 is
  ~485 LOC (iter-134 + iter-136 + iter-138 + iter-140 deltas per
  directive). Adding ~80–140 LOC for d_app + d_map yields ~565–625 LOC
  cumulative, well within the 1000 LOC envelope from iter-137
  renormalised piece (i.b). **Comfortably fits.**

## Recommendation

**Iter-141 follow-on shape**: dispatch blueprint-writer this iter
(the (B) action in strategy-critic-iter141 terms) to expand both the
d_app and d_map recipes inline at `RigidityKbar.tex:602–708`, naming
the load-bearing Mathlib lemmas precisely. Iter-142 prover lane
targets the d_app + d_map sub-sorries with the validated recipes.

**Specific blueprint-writer instructions**:

1. **d_app NOTE block** (`RigidityKbar.tex:602–659`): no recipe-shape
   change needed; add a §"Implementation note" that pinpoints
   `ModuleCat.Derivation.d_map` (`Mathlib.Algebra.Category.ModuleCat.Differentials.Basic:80`)
   as the algebra-side closing lemma (replacing the iter-140 prover's
   `letI + map_algebraMap` pattern). This saves ~4 LOC per call site.

2. **d_map NOTE block** (`RigidityKbar.tex:661–708`): **update the
   "definitional/transparent" claim** at L702–708. The claim is
   correct *at the LinearMap-application level* but is NOT reachable
   via `change` / `whnf` due to the `set_option
   backward.isDefEq.respectTransparency false` annotation on
   `pushforward₀_obj` and `pushforward₀`. Replace the "no opacity to
   chase" language with: "the unfolding is provided by the explicit
   `@[simp]`-tagged lemma
   `PresheafOfModules.pushforward_obj_map_apply'`
   (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward:99–106`);
   use `simp only [pushforward_obj_map_apply']` rather than `change`,
   because `pushforward₀` is annotated
   `backward.isDefEq.respectTransparency false` and `whnf`-based
   tactics cannot punch through".

3. **Add a footnote / negative-lesson NOTE** under the d_map block
   citing the iter-140 prover's `whnf`-timeout discovery, so future
   iters do not repeat the `change`-first approach on `pushforward`-
   transposed goals.

**Do NOT** widen the envelope for piece (i.b); both sub-sorries fit
inside the existing 1000 LOC cap with margin.

**Do NOT** dispatch a structural-side-step refactor (the iter-138
helper-pair pattern). The opacity here is locally resolvable by named-
lemma application; no structural rearrangement is needed.

## Decision summary table

| Decision | Verdict | Severity |
|---|---|---|
| 1: d_app closure shape | PROCEED (with streamlining via `d_map`) | informational |
| 2: Factoring witness for d_app | NEEDS_MATHLIB_GAP_FILL (~40–80 LOC project-bespoke) | informational |
| 3: d_map unfolding lemma name | **NEEDS_MATHLIB_LEMMA_NAME** (`pushforward_obj_map_apply'`) | major |
| 4: d_map closure shape | ALIGN_WITH_MATHLIB | major |
| 5: LOC envelope (combined ~80–140 LOC) | PROCEED (fits inside 1000 LOC cap) | informational |
