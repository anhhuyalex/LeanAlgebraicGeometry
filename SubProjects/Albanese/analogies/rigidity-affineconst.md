# Analogy: relative "proper-into-affine constant on fibres" as a morphism equality (Rigidity bridge 2)

## Mode
api-alignment

## Slug
rigidity-affineconst

## Iteration
159

## Question
Does Mathlib have an idiom for the **relative** statement "a proper morphism with
geometrically-connected fibres into an affine target is constant along fibres", expressed as a
**scheme-morphism equality**, usable to close the agreement equation of `rigidity_eqOn_dense_open`
(`AlgebraicJacobian/AbelianVarietyRigidity.lean:181`)? Concretely on `U = X × V`:
`U.ι ≫ f.left = U.ι ≫ (lift (toUnit (X⊗Y) ≫ x₀) (snd X Y) ≫ f).left`.

## Project artifact(s)
- `AlgebraicJacobian/AbelianVarietyRigidity.lean:111-181` — `rigidity_eqOn_dense_open`; the
  agreement-equation `sorry` at L181 is "bridge 2".
- `AlgebraicJacobian/AbelianVarietyRigidity.lean:243-274` — `rigidity_core` consumes it via
  `ext_of_isDominant_of_isSeparated'`.

## Decisions identified

### Decision 1: the RELATIVE framing (Stein factorization / proper pushforward `f_* O_X = O_base`)

- **Mathlib idiom**: **absent.** There is no `SteinFactorization`, no proper pushforward of the
  structure sheaf with a connectedness conclusion, and no proper base change for `H⁰`. Searches:
  `lean_leansearch "Stein factorization proper morphism pushforward structure sheaf"` returns only
  `SheafOfModules.pushforward` / `Scheme.Modules.pushforward` (the bare functor `f_*`, no
  `f_* O = O` theorem) and `TopCat.Sheaf.pushforward_sheaf_of_sheaf`. `loogle` for proper
  pushforward connectedness: nothing. The relative `Γ(X ×_S T) = Γ(X) ⊗ Γ(T)` (flat base change
  for `H⁰`) is also absent.
- **Project's path (if pursued)**: build `p₂,* O_{X×V} = O_V` and factor `f` through it.
- **Gap**: divergent-and-wrong as a *first* move — this framing requires `H⁰`-base-change /
  coherent-cohomology infrastructure Mathlib does not have. Multi-iter gap-fill.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (do **not** pursue this framing for bridge 2).

### Decision 2: the GLOBAL-SECTIONS + per-slice field route ("route B", cohomology-free)

- **Mathlib idiom present**:
  - `AlgebraicGeometry.ext_of_isAffine` (`Mathlib.AlgebraicGeometry...`, via leanfinder): a map
    into an **affine** scheme is determined by its global-sections map `appTop`. THIS is the
    "morphism into affine determined by `Γ`" handle the directive hoped for.
  - `AlgebraicGeometry.isField_of_universallyClosed` + `finite_appTop_of_universallyClosed`
    (`Mathlib.AlgebraicGeometry.Morphisms.Proper`): `Γ(slice)` is a field, module-finite over the
    base field.
  - `IsAlgClosed` + finite/algebraic ⟹ trivial extension (`Mathlib.FieldTheory.IsAlgClosed.*`):
    at a **closed** point of a finite-type `k̄`-scheme the residue field is `k̄`, so
    `Γ(slice) = k̄` and the slice→affine map is a single `k̄`-point.
  - `JacobsonSpace`, `closedPoints`, `closure_closedPoints`, `LocallyOfFiniteType.jacobsonSpace`
    (`Mathlib.Topology.JacobsonSpace`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`):
    closed points are **dense** in a finite-type `k̄`-scheme.
  - `ext_of_isDominant` / `ext_of_isDominant_of_isSeparated'`
    (`Mathlib.AlgebraicGeometry.Morphisms.Separated`): two maps out of a **reduced** scheme into a
    **separated** target agreeing on a **dominant** (= dense-range, `dominant_eq_topologically`)
    subobject are equal. (Already used by `rigidity_core`.)
  - `Scheme.fromSpecResidueField x` with `range = {x}` and `IsPreimmersion`
    (`Mathlib.AlgebraicGeometry.ResidueField`): the per-point probe.
- **The assembly (cohomology-free)**:
  1. For each **closed** point `y ∈ V`: `κ(y) = k̄`; the slice `X_y ≅ X` is proper integral over
     `k̄`, maps into the affine `U₀`; `isField_of_universallyClosed` + `finite_appTop` + alg-closed
     ⟹ `Γ(X_y) = k̄` ⟹ (via `ext_of_isAffine`) `f|X_y = const = (retract ≫ f)|X_y` **as
     morphisms into `U₀ ⊆ Z`** (the two ring maps `Γ(U₀) → k̄` have the same kernel = the point,
     and a `k̄`-algebra map to `k̄` is pinned by its kernel).
  2. The closed slices are jointly **dense** in `U` (`closure_closedPoints`, Jacobson). Feed a
     dominant probe (coproduct of the closed-point `fromSpecResidueField`s, or any dense-range
     witness) to `ext_of_isDominant` ⟹ `f|U = (retract ≫ f)|U`.
- **The one genuinely-missing connective**: a packaged "morphisms agreeing on a **dense set of
  closed points** are equal" hom-extensionality. Mathlib has only the **single-dominant-morphism**
  `ext_of_isDominant`; turning "agrees at every closed point" into one dominant probe needs an
  (infinite, `Set`-indexed) coproduct `∐_{x∈closedPoints U} Spec κ(x) → U` plus a `DenseRange`
  proof. This is buildable from present pieces, not a cohomology gap.
- **Gap**: divergent-but-tractable. ~2–3 iter assembly, **no cohomology**.
- **Verdict**: PROCEED (this is the route; idiom = `ext_of_isAffine` per-slice +
  `ext_of_isDominant` globalize).

### Decision 3 (actionable signature point): `[IsAlgClosed kbar]` is missing from the chain

- The closed-points route needs `κ(closed pt) = k̄`, i.e. `[IsAlgClosed kbar]`. But
  `rigidity_eqOn_dense_open` / `rigidity_core` / `rigidity_lemma` (L111, L243, L324) carry only
  `[Field kbar]`. The downstream consumers (`morphism_P1_to_grpScheme_const`,
  `rigidity_genus0_curve_to_grpScheme`, L357/L406) **already** assume `[IsAlgClosed kbar]`, and the
  variable is literally named `kbar`.
- **Cost of NOT adding it**: forces the harder generic-fibre route, which needs "geometrically
  connected + geometrically reduced ⟹ `Γ = K`" (trivial-finite-extension upgrade over a
  *non*-alg-closed base via `Algebra.IsGeometricallyReduced` ⟹ separable + connected ⟹ trivial).
  That is a separate medium build Mathlib does not package.
- **Verdict**: ALIGN (recommendation): add `[IsAlgClosed kbar]` to the three chain lemmas. Low
  cost, consistent with naming and downstream, and unlocks the cohomology-free route.

## Recommendation

Do **not** build the relative Stein / `f_* O = O` statement for bridge 2 (Decision 1 — multi-iter
cohomology gap). Instead take **route B**: (i) add `[IsAlgClosed kbar]` to
`rigidity_eqOn_dense_open`/`rigidity_core`/`rigidity_lemma`; (ii) prove per-closed-slice constancy
into the affine `U₀` with `ext_of_isAffine` + `isField_of_universallyClosed` +
`finite_appTop_of_universallyClosed` + alg-closed-triviality; (iii) globalize to `U` with
`ext_of_isDominant` fed a dense-range probe built from `closure_closedPoints` /
`fromSpecResidueField`. The only thing Mathlib does not hand you ready-made is the
"dense-closed-points ⟹ hom-ext" globalization step (Decision 2's missing connective) — that is a
small bespoke build, **not** cohomology. Net: bridge 2 is a ~2–3 iter cohomology-free assembly, not
the 1-iter idiomatic call the directive hoped for, and not the hopeless cohomology gap it feared.
</content>
</invoke>
