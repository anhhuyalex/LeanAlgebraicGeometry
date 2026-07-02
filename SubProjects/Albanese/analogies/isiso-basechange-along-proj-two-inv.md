# Analogy: `IsIso` of `basechange_along_proj_two_inv` — Route (a) vs Route (b'2)

## Slug

isiso-routes-iter139

## Iteration

139

## Question

The iter-138 Route (b) skeleton for
`relativeDifferentialsPresheaf_basechange_along_proj_two`
(`AlgebraicJacobian/Cotangent/GrpObj.lean:612`) landed end-to-end with
three concrete sorries. The third sorry is

```
letI : IsIso (basechange_along_proj_two_inv G) := sorry
```

at `Cotangent/GrpObj.lean:624`. Two routes are on the table:

* **Route (a)** — build the forward-direction iso via a chart-unfolding
  helper `pullbackObjEquivTensor`, then derive `IsIso (… inv …)` from
  the pair via `isIso_of_isInverse`.
* **Route (b'2)** — use `PresheafOfModules.toPresheaf` to reflect isos
  to the underlying presheaf of abelian groups, then
  `NatTrans.isIso_iff_isIso_app` to localise the iso check to per-open
  ModuleCat morphisms; identify each per-open morphism with
  `tensorKaehlerEquiv`'s inverse on affines.

Which is the iter-140 closure target?

## Project artifact(s)

- `AlgebraicJacobian/Cotangent/GrpObj.lean:612–625` —
  `relativeDifferentialsPresheaf_basechange_along_proj_two` (iter-138
  PARTIAL skeleton; third sorry on `IsIso` of the inverse map).
- `AlgebraicJacobian/Cotangent/GrpObj.lean:596–610` —
  `basechange_along_proj_two_inv` (iter-138 closed honest skeleton:
  adjunction transpose of universal-property lift of derivation).
- `AlgebraicJacobian/Cotangent/GrpObj.lean:547–585` —
  `basechange_along_proj_two_inv_derivation` (iter-138 PARTIAL: d_add
  and d_mul closed; d_app and d_map sorry-bodied — parallel prover
  lane this iter).
- `analogies/kaehler-tensorequiv-presheafpullback.md` — iter-137 5-step
  recipe (informed Route (a) and the forward-direction strategy).
- `analogies/mulright-globalises-cotangent.md` Decision 2 — iter-133
  identified the gap and the chart-level `Algebra.IsPushout` need.

## Mathlib infrastructure verified this iter

All names below were verified to exist in current Mathlib via
`lean_loogle` + `lean_run_code` typecheck.

| Name | Module | Used by |
|---|---|---|
| `PresheafOfModules.toPresheaf` | `Mathlib.Algebra.Category.ModuleCat.Presheaf:149` | Route (b'2) |
| `PresheafOfModules.pullback` | `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback:44` | both |
| `PresheafOfModules.pullbackPushforwardAdjunction` | `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback:50` | both |
| `NatTrans.isIso_iff_isIso_app` | `Mathlib.CategoryTheory.NatIso:232` | Route (b'2) |
| `isIso_iff_of_reflects_iso` | `Mathlib.CategoryTheory.Functor.ReflectsIso.Basic:49` | Route (b'2) |
| `reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms` | `Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced:31` | Route (b'2) — load-bearing |
| `KaehlerDifferential.tensorKaehlerEquiv` | `Mathlib.RingTheory.Kaehler.TensorProduct` | both |
| `KaehlerDifferential.tensorKaehlerEquiv_tmul_D` | `Mathlib.RingTheory.Kaehler.TensorProduct` | both |
| `(forget₂ (ModuleCat _) AddCommGrpCat).ReflectsIsomorphisms` | `Mathlib.Algebra.Category.ModuleCat.Basic:598` | Route (b'2) bridge |

## The critical iso-reflection check (Route (b'2))

The iter-138 prover named two pieces — `PresheafOfModules.toPresheaf`
and `NatTrans.isIso_iff_isIso_app`. **Both exist**, but
`(PresheafOfModules.toPresheaf R).ReflectsIsomorphisms` is **NOT
directly registered as an instance** in Mathlib. Typeclass synthesis
fails without an additional import:

```lean
-- FAILS without `Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced`:
example : (PresheafOfModules.toPresheaf R).ReflectsIsomorphisms := by infer_instance
```

The reason: `toPresheaf` is registered only as `Faithful`
(`Presheaf.lean:164`), not `ReflectsIsomorphisms`. But the chain

```
Balanced (PresheafOfModules R)  -- abelian, registered
  + (toPresheaf R).ReflectsMonomorphisms  -- from Faithful, inferable
  + (toPresheaf R).ReflectsEpimorphisms  -- inferable in Mathlib
  ⇒ (toPresheaf R).ReflectsIsomorphisms  -- via priority-100 instance
     `reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms`
     in `Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced:31`
```

is consumable as a single `infer_instance` step **once the Balanced
file is imported**.

Adding `import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced`
(or `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
which transitively imports it) unlocks a 5-line helper:

```lean
namespace PresheafOfModules
theorem isIso_of_app_iso_module {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat} {M N : PresheafOfModules R}
    (f : M ⟶ N) (h : ∀ X, IsIso (f.app X)) : IsIso f := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf R),
       NatTrans.isIso_iff_isIso_app]
  intro X
  exact Functor.map_isIso (forget₂ (ModuleCat _) AddCommGrpCat) (f.app X)
end PresheafOfModules
```

(typechecked this iter — see report task_results file).

This is the **5-line bridge** from "iso per chart at ModuleCat level"
to "iso of PresheafOfModules morphism". Mathlib has it in scattered
form (the `AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app`
analogue at `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:132`) but
not packaged for `PresheafOfModules` directly.

## Decisions identified

### Decision 1: Route choice for the `IsIso` sorry

- **Mathlib idiom**: NONE for this specific situation. Mathlib has
  `Scheme.Modules.Hom.isIso_iff_isIso_app` for the sheaf-of-modules
  category (with sheaf hypotheses) but no analogous packaged lemma at
  the `PresheafOfModules` level. The closest precedent is the
  reflection chain Sheafification.lean:43 uses
  (`inferInstanceAs (SheafOfModules.forget R ⋙ toPresheaf _).ReflectsIsomorphisms`)
  — same iso-reflection idiom.

- **Project's proposed paths**:
  - **Route (a)** — build the forward direction explicitly
    (chart-unfolding `pullbackObjEquivTensor` helper + chart-level
    `Algebra.IsPushout` + `tensorKaehlerEquiv` on affines), then
    `IsIso (… inv …)` via inverse pairing.
  - **Route (b'2)** — apply the 5-line `isIso_of_app_iso_module`
    bridge to reduce to per-open ModuleCat-iso, then identify the
    chart-level morphism with `tensorKaehlerEquiv`'s inverse on
    affines.

- **Gap (both routes)**: NEEDS_MATHLIB_GAP_FILL — neither route is
  packaged in Mathlib.

- **Critical observation**: Both routes **share** the per-open
  identification work — chart-level `Algebra.IsPushout` helper
  (~80–150 LOC), `((pullback ψ).obj M).obj X` chart-unfolding
  (~30–60 LOC), and `tensorKaehlerEquiv` identification (~50–100 LOC).
  Route (b'2) does NOT escape the `pullback`-opacity issue — to show
  `IsIso ((basechange_along_proj_two_inv G).app X)` requires
  describing the source `((pullback ψ).obj M_G).obj X` to compare
  with `tensorKaehlerEquiv`'s output, which is precisely the
  chart-unfolding helper from Route (a).

- **Where Route (b'2) wins**: it avoids the additional cost of
  "construct forward direction + prove inverse pair" (~80–150 LOC
  in Route (a)). The iso-reflection bridge replaces it with a single
  5-line lemma + the per-open identification.

- **Verdict**: **PROCEED with Route (b'2)** as the iter-140 target.
  LOC envelope ~150–300 vs Route (a)'s ~280–560.

### Decision 2: Where the iso-reflection helper should live

- **Mathlib idiom**: Standalone, namespace-qualified theorem in the
  `PresheafOfModules` namespace, following the pattern of
  `Scheme.Modules.Hom.isIso_iff_isIso_app` (`Sheaf.lean:132`).

- **Project's path**: write `PresheafOfModules.isIso_of_app_iso_module`
  (or `Hom.isIso_iff_isIso_app`) as a private/section helper in
  `AlgebraicJacobian/Cotangent/GrpObj.lean` adjacent to the
  `basechange_along_proj_two_inv` declarations. Add the
  `import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced`
  (or rely on the transitive import from Sheafification).

- **Gap**: NEEDS_MATHLIB_GAP_FILL — this is genuinely missing from
  Mathlib `PresheafOfModules`. Upstream-PR candidate.

- **Verdict**: **PROCEED**. Add the 5-line helper as a private lemma;
  flag as upstream-PR candidate in the docstring.

### Decision 3: Per-open identification idiom

- **Mathlib idiom**: `KaehlerDifferential.tensorKaehlerEquiv`
  (`Mathlib.RingTheory.Kaehler.TensorProduct`) — the algebra-side
  base-change-of-Ω equivalence under `Algebra.IsPushout R S A B`.
  Companion `tensorKaehlerEquiv_tmul_D` and `_symm_D_tmul` for
  rewriting on derivation-image generators.

- **Project's path**: at each open `X`, the per-open ModuleCat
  morphism `(basechange_along_proj_two_inv G).app X` should be
  shown iso by:
  1. Identifying source `((pullback ψ).obj M_G).obj X` with
     `((Γ((G⊗G).left, snd X) ⊗_{Γ(G.left, X)} Ω[Γ(G.left, X)⁄k]))`
     via the pushforward-adjunction unit/counit (this IS Route (a)'s
     `pullbackObjEquivTensor` helper, can't be avoided).
  2. Identifying target `LHS.obj X = Ω[Γ((G⊗G).left, X)⁄...]`
     (direct definitional unfold of `relativeDifferentialsPresheaf`).
  3. Showing the morphism IS `tensorKaehlerEquiv.symm` (on affines,
     using the chart-level `Algebra.IsPushout` from Step 1 of the
     iter-137 recipe).

- **Gap**: ALIGN_WITH_MATHLIB on idiom (`tensorKaehlerEquiv` is
  Mathlib-canonical); NEEDS_MATHLIB_GAP_FILL on the chart-level
  `Algebra.IsPushout` from-affine-product helper (no Mathlib lemma).

- **Verdict**: **ALIGN_WITH_MATHLIB** for the per-open identification
  via `tensorKaehlerEquiv`. **NEEDS_MATHLIB_GAP_FILL** for the
  chart-level `Algebra.IsPushout`-from-affine-product helper.

### Decision 4: Bypass via `Algebra.IsPushout` and `pullback` opacity (caveat)

This is the critical structural caveat the iter-138 prover did NOT
fully surface in their task result.

- **The pullback-opacity blocker is unavoidable for either route**:
  Mathlib's `PresheafOfModules.pullback` is defined abstractly as
  `(pushforward φ).leftAdjoint` (`Pullback.lean:44`) with no
  chart-wise unfolding lemma. Route (a) plans to build the
  `pullbackObjEquivTensor` helper to bypass this. Route (b'2) also
  needs to describe `((pullback ψ).obj M_G).obj X` per-open to
  identify it with `tensorKaehlerEquiv`'s output — this is exactly
  the same helper.

- **Implication**: the LOC delta between (a) and (b'2) is purely the
  "forward-direction construction + inverse-pair proof"
  (~80–150 LOC) that Route (a) needs and Route (b'2) avoids. The
  shared infrastructure (`pullbackObjEquivTensor` ~30–60 LOC,
  `Algebra.IsPushout` chart helper ~80–150 LOC) is needed by both.

- **Gap**: PROCEED with Route (b'2); the shared infrastructure must
  be built either way.

- **Verdict**: **PROCEED**, with the explicit understanding that
  Route (b'2)'s savings come from avoiding the forward-direction
  construction, not from escaping `pullback`-opacity.

### Decision 5: LOC envelope revision

- iter-138 prover's estimate: ~150–300 LOC for Route (b'2).
- Refined estimate this iter, accounting for shared infrastructure:
  * 5 LOC `isIso_of_app_iso_module` helper.
  * ~30–60 LOC `pullbackObjEquivTensor` chart-unfolding helper
    (shared with Route (a)).
  * ~80–150 LOC chart-level `Algebra.IsPushout`-from-affine-product
    helper (shared with Route (a)).
  * ~80–150 LOC per-open `tensorKaehlerEquiv` identification +
    naturality.
- **Revised Route (b'2) envelope: ~195–365 LOC** total (helpers
  inclusive).
- **Revised Route (a) envelope: ~280–560 LOC** total (helpers
  inclusive; the extra ~80–200 LOC is the explicit forward
  direction).
- **Delta**: Route (b'2) saves ~80–195 LOC.
- **Verdict**: **PROCEED with Route (b'2)** — concretely cheaper.

## Recommendation

**PROCEED with Route (b'2) as the iter-140 closure target** for the
`IsIso (basechange_along_proj_two_inv G)` sorry at
`Cotangent/GrpObj.lean:624`.

The iter-138 prover's named API is verified-to-exist:

1. `PresheafOfModules.toPresheaf` —
   `Mathlib.Algebra.Category.ModuleCat.Presheaf:149` ✓
2. `NatTrans.isIso_iff_isIso_app` —
   `Mathlib.CategoryTheory.NatIso:232` ✓

With one **critical infrastructure gap the iter-138 prover did not
flag**: `(PresheafOfModules.toPresheaf R).ReflectsIsomorphisms`
requires the import `Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced`
to be inferable (the instance is generated via the Balanced path,
not directly registered on `toPresheaf`). Either add the import or
rely on it being transitively present via
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` (which
the project already imports indirectly).

**Iter-140 prover gap items to pre-construct** (in order):

1. **5-line `isIso_of_app_iso_module` helper** (verified above).
   Place adjacent to `basechange_along_proj_two_inv` in
   `Cotangent/GrpObj.lean`. Add the
   `import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced`
   if not already transitively present.
2. **Chart-level `Algebra.IsPushout`-from-affine-product helper**
   (~80–150 LOC; shared with Route (a)). Per
   `analogies/kaehler-tensorequiv-presheafpullback.md` Decision 2 —
   build from `CommRingCat.isPushout_iff_isPushout`,
   `pullbackSpecIso`, `isPullback_SpecMap_of_isPushout`.
3. **`((pullback ψ).obj M).obj X` chart-unfolding** (~30–60 LOC;
   shared with Route (a)). Build from `pullbackPushforwardAdjunction`
   unit/counit at the chart-level. This is the load-bearing pieces
   that cannot be avoided.
4. **Per-open identification** (~80–150 LOC): for each affine open
   `X`, identify `(basechange_along_proj_two_inv G).app X` as
   `tensorKaehlerEquiv.symm` (modulo the chart-unfolding from step 3
   and the `Algebra.IsPushout` from step 2). Use
   `tensorKaehlerEquiv_symm_D_tmul`.

The chart-level `Algebra.IsPushout` and `pullbackObjEquivTensor`
helpers are upstream-PR candidates (they're general utilities, not
project-specific). The 5-line `isIso_of_app_iso_module` is also a
plausible upstream-PR (mirrors the `Scheme.Modules` analogue in
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:132`).

**Do NOT switch to Route (a)** unless Route (b'2)'s per-open
identification turns out to require more than ~150 LOC due to a
hidden naturality wrinkle — in which case dispatch a follow-up
mathlib-analogist call on the per-open work specifically.

**Decision summary table**:

| Decision | Verdict |
|---|---|
| 1: Route choice | PROCEED with Route (b'2) |
| 2: Helper placement | PROCEED (private helper + upstream-PR flag) |
| 3: Per-open identification | ALIGN_WITH_MATHLIB on `tensorKaehlerEquiv` + NEEDS_MATHLIB_GAP_FILL on `Algebra.IsPushout` helper |
| 4: pullback-opacity caveat | PROCEED (shared with Route (a); not a route-discriminator) |
| 5: LOC envelope | PROCEED — ~195–365 LOC (saves ~80–195 vs Route (a)) |
