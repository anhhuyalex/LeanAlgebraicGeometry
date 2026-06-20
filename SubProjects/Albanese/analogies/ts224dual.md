# Analogy: discharging `internalHomEval` naturality without the `𝟙_` whnf bomb

## Mode
api-alignment

## Slug
ts224dual

## Iteration
224

## Question

Is the project hand-rolling the internal-hom **evaluation morphism** `internalHomEval :
M ⊗_R M^∨ ⟶ 𝟙_` on `PresheafOfModules R` in a shape that forces a `whnf` of the monoidal
unit `𝟙_` during naturality — and does Mathlib provide either (a) a ready evaluation/counit
to reuse, or (b) a `Hom`-builder / unit-targeting idiom whose naturality is dischargeable
**without** `kabstract`-over-`𝟙_`? Decide align-vs-deviate and give a concrete bounded recipe.

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1463` — `internalHomEval` (naturality is a typed `sorry`; built via `PresheafOfModules.Hom.mk (fun X => internalHomEvalApp M X) (by …)`).
- `…:1359` — `dual M := InternalHom.internalHom M (𝟙_ …)` (the `𝟙_` literal that poisons every goal mentioning `dual`).
- `…:1367` `evalLin`, `…:1408` `internalHomEvalApp`, `…:1431` `internalHomEvalApp_tmul`.

## Decisions identified

### Decision 1: reuse a Mathlib evaluation / counit (`MonoidalClosed.ev` / `ihom.ev`)

- **Mathlib idiom**: a `MonoidalClosed` category gives `ihom.ev : ihom A ⊗ A ⟶ 𝟙` (the
  counit) with naturality for free. The **fixed-ring** `ModuleCat R` HAS this:
  `instance : MonoidalClosed (ModuleCat.{u} R)` (`Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.lean`),
  imported by `…/Presheaf/Monoidal.lean:9` and used objectwise.
- **For `PresheafOfModules R` / `SheafOfModules R`**: **ABSENT.** `grep` over
  `…/ModuleCat/Presheaf/*` finds the string `Closed` only at the import line
  (`Monoidal.lean:9`); there is no `MonoidalClosed (PresheafOfModules …)` / `SheafOfModules`
  instance anywhere in Mathlib (`grep "MonoidalClosed (PresheafOfModules\|SheafOfModules"`
  → 0 hits). This re-confirms ts219dual Decision 1.
- **Gap**: divergent-and-absent. No counit to reuse; building one is the entire ts219dual
  multi-iter internal-hom block (out of scope this round).
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (cannot reuse). Question-1's "if a counit exists,
  naturality is free" does NOT fire — there is no counit.

### Decision 2 (THE decision): target the explicit `unit R`, not the monoidal `𝟙_`

- **Mathlib idiom**: the unit object of `PresheafOfModules R` is the explicit
  `PresheafOfModules.unit R` (`…/ModuleCat/Presheaf.lean`, `noncomputable def unit`), whose
  restriction map is the *cheap* `ModuleCat.ofHom {toFun := fun x ↦ R.map f x}` and which
  carries cheap lemmas `unit_map_one` and the bijection `unitHomEquiv : (unit R ⟶ M) ≃
  M.sections`. **Crucially, the monoidal layer defines `tensorUnit := unit _`**
  (`…/Presheaf/Monoidal.lean:110`), so `𝟙_ (PresheafOfModules R)` is *definitionally*
  `unit R`. Every Mathlib construction that touches the unit object — `unitHomEquiv`,
  `unit_map_one`, and the unitor-naturality proofs themselves — is written against
  `unit R`, **never** the `𝟙_` instance-projection. The `𝟙_` notation is only ever used as a
  display alias once the `MonoidalCategoryStruct` is in scope; proofs go through `unit`.
- **Why `𝟙_` is toxic and `unit` is not**: `dual M := internalHom M (𝟙_ …)` embeds the
  `MonoidalCategoryStruct.tensorUnit` *instance projection* literally into `dual`'s body.
  `dual M` then appears all over the naturality goal (`(tensorObj M (dual M)).map f`,
  `φ : (dual M).obj X`, and the codomain `(𝟙_).map f`). `rw`/`erw`/`simp`/`change` all call
  `kabstract`, whose `isDefEq` runs at the **ambient `.default` transparency**, so it unfolds
  `dual → internalHom M 𝟙_` and must `whnf` the `𝟙_`/`tensorUnit` machinery (the full
  `monoidalCategoryStruct` value, with its associator/unitor `isoMk` proof fields, under
  `set_option backward.isDefEq.respectTransparency false`) — the >200000-heartbeat,
  non-budget-bound blowup the iter-223 bisection found. Re-defining `dual` with `unit R`
  syntactically replaces every `tensorUnit` projection by the cheap `unit` structure, so the
  same `kabstract` whnf stays small.
- **Mathlib precedent for the per-section proof**: the unitor naturality squares —
  structurally the *same* "map involving the unit" obligation — are discharged at
  `…/Presheaf/Monoidal.lean:113-122` by exactly the project's shape:
  `ext m; dsimp [CommRingCat.forgetToRingCat_obj]; erw […, tensorObj_map_tmul,
  (R.map f).hom.map_one]; rfl`. No `tensorUnit_map` rewrite, no `𝟙_` in the goal — the unit
  enters only as `unit.map f` applied to `1`, fully concrete.
- **Project's current path**: `dual` and `internalHomEval` are written against `𝟙_`.
- **Gap**: divergent-with-cost — the divergence is the direct cause of the whnf bomb that has
  blocked the sorry for 3 iters.
- **Verdict**: **ALIGN_WITH_MATHLIB** — define `dual M := internalHom M (unit …)` (and land
  `internalHomEval` with codomain `unit …`; it is defeq to `𝟙_`, so downstream `⟶ 𝟙_`
  consumers still typecheck). Then run the existing six-step reduction with `unit_map_apply`
  in place of `tensorUnit_map`.

### Decision 3: `Hom`-builder with pre-reduced naturality (`homMk`)?

- **Mathlib idiom**: `PresheafOfModules.homMk (φ : M₁.presheaf ⟶ M₂.presheaf) (hφ : …semilinear…)`
  builds the morphism from an underlying `Ab`-presheaf map; its naturality is
  `CategoryTheory.congr_fun (φ.naturality f) x` — i.e. it *delegates* naturality to `φ`'s.
- **Does it pre-reduce the obstacle?** No. Constructing `φ : (M ⊗ M^∨).presheaf ⟶ (unit).presheaf`
  still requires proving the same naturality square at the `Ab` level, and it discards the
  module structure the contraction needs. The project's `Hom.mk app + (by tensor_ext)` route
  IS the correct per-section reduction; the only missing ingredient is transparency control on
  the rewrites, not a different builder.
- **Verdict**: **PROCEED** (keep `Hom.mk` + `tensor_ext`; do not switch to `homMk`).

### Decision 4 (tactical): reducible-transparency rewriting (`with_reducible`)

- **Mathlib idiom**: `with_reducible` lowers ambient transparency so `kabstract`/`isDefEq`
  will **not** unfold non-reducible `def`s (`dual`, `internalHom`, `tensorUnit`/`unit` are all
  plain `def`s). Established precedent — including in **monoidal-coherence** proofs:
  `Mathlib/RepresentationTheory/Action.lean:157-158`
  (`with_reducible convert … ; all_goals with_reducible simp`), and the `conv` variant at
  `Mathlib/Tactic/Conv.lean:123` (`with_reducible … conv`), with `#whnfR` = reducible whnf at
  `:150`. This is the standard tool for exactly "a rewrite whose `kabstract` would otherwise
  whnf a heavy categorical definition".
- **Why it should defeat the bomb**: plain `rw`/`erw` run `kabstract` at `.default`
  transparency, unfolding `dual → internalHom M 𝟙_` and whnf-ing the unit machinery.
  `with_reducible rw [tensorObj_map_tmul, internalHomEvalApp_tmul, …]` runs `kabstract` at
  `.reducible`, which leaves `dual`/`𝟙_` folded; the elementwise lemma LHSs
  (`(tensorObj _ _).map _`, `(internalHomEvalApp _ _).hom`, `unit_map_one`) are head-aligned
  with the goal and match without the deep whnf.
- **Verdict**: **DIVERGE_INTENTIONALLY** (cheap tactical patch; keeps the `𝟙_` shape). This is
  the lowest-cost first probe and is independent of Decision 2.

## Recommendation

Two independent, composable fixes, ordered by cost:

1. **(cheapest, try first) `with_reducible` the rewrites** (Decision 4). Wrap every
   goal-rewriting tactic inside the `internalHomEval` naturality proof in `with_reducible`
   (e.g. `with_reducible rw [tensorObj_map_tmul, internalHomEvalApp_tmul, internalHomEvalApp_tmul]`,
   `with_reducible simp only […]`). `intro`/`refine tensor_ext` stay as-is (they don't
   `kabstract`). ~3–6 one-token wrappers, 0 signature changes, ~1 iter. Direct precedent:
   `Action.lean:157-158`.

2. **(robust, the real ALIGN) re-shape `dual` onto `unit`** (Decision 2). Change
   `dual M := internalHom M (𝟙_ …)` → `internalHom M (unit …)`, retype the `evalLin` cast
   `(φ : restr X.unop M ⟶ restr X.unop (unit …))`, set `internalHomEval`'s codomain to
   `unit …` (defeq to `𝟙_`), and replace the step-2 `tensorUnit_map` by `unit`'s definitional
   `R.map f` (the prover's step-3 `unit_map_apply`/`unit_map_one`). This is the genuine
   Mathlib idiom (Mathlib never proves unit-maps against `𝟙_`; see `unitHomEquiv` and the
   unitor proofs at `Monoidal.lean:113-122`). ~20–40 LOC of churn, all inside
   `TensorObjSubstrate.lean`; no protected signature is touched and `internalHomEval` is not
   yet consumed by `exists_tensorObj_inverse`, so the codomain swap is free.

Do **not** wait on a Mathlib counit (Decision 1: none exists) and do **not** rewrite via
`homMk` (Decision 3: same square, worse). **Honest residual risk**: the iter-223 evidence does
not fully isolate the bomb to the `𝟙_` projection vs. `internalHom`/`ofPresheaf` itself (the
prover made only `dual`/`internalHomEvalApp` irreducible, never `internalHom`/`internalHomPresheaf`/
`internalHomObjModule`/`ofPresheaf`). If `with_reducible` (which folds ALL of them) still bombs,
the obstacle is genuinely the `internalHom` body's defeq cost and the held fallback applies:
revert `internalHomEval` to ABSENT (global sorry 81→80) rather than carry a stubbed morphism.
`with_reducible` is the decisive experiment — if it does not close it, no whnf-free close exists
at the current object shape.
