# Analogy: `lineBundleAtClosedPoint` / `toFunctionField` Mathlib path

## Mode
api-alignment

## Slug
ocofp-sheaf-internalhom

## Iteration
182

## Question

`RiemannRoch/OCofP.lean` carries two load-bearing `noncomputable def := sorry`
declarations:

- `lineBundleAtClosedPoint` (L140) returning a
  `Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} kbar)`.
- `lineBundleAtClosedPoint.toFunctionField` (L154) returning a `kbar`-linear
  map from sections (`Scheme.HModule kbar (lineBundleAtClosedPoint P hP) 0`) to
  `C.left.functionField`.

iter-181 lean-auditor MAJOR finding: until `toFunctionField`'s body lands, the
proven `globalSections_iff` is mathematically vacuous (the RHS quantifies over
`toFunctionField P hP s = f` where `toFunctionField` is `sorryAx`).

The directive asks: what is the canonical Mathlib idiom, what gaps exist, and
should the project (a) build the bodies inline in `OCofP.lean`, (b) open a new
`IdealSheafDual.lean` bottom-up file, or (c) `NEEDS_MATHLIB_GAP_FILL`?

## Project artifact(s)
- `AlgebraicJacobian/RiemannRoch/OCofP.lean:140` `lineBundleAtClosedPoint`
- `AlgebraicJacobian/RiemannRoch/OCofP.lean:154`
  `lineBundleAtClosedPoint.toFunctionField`
- `blueprint/src/chapters/RiemannRoch_OCofP.tex` L149–L167 (Hartshorne II.6
  packaging as `Hom_{O_C}(I_P, O_C)`); L237–L241 (the iff's binding `s ↔ f`).
- `AlgebraicJacobian/Cohomology/StructureSheafModuleK/Carriers.lean:52`
  `Scheme.HModule` (the project's `Sheaf J (ModuleCat kbar)`-flavoured `Ext`).
- `AlgebraicJacobian/Cohomology/StructureSheafModuleK/SheafProperty.lean:42`
  `Scheme.toModuleKSheaf` (the structure sheaf as `Sheaf J (ModuleCat kbar)`,
  via the `Spec kbar`-structure morphism algebra).

## Decisions identified

### Decision 1 — Sheaf-internal-Hom for `Sheaf J (ModuleCat R)`-valued sheaves

- **Mathlib idiom**: There is **no** internal-Hom for sheaves of `ModuleCat R`
  with the value `Sheaf J (ModuleCat R)`. Mathlib only exposes:
  - `CategoryTheory.sheafHom : Sheaf J A → Sheaf J A → Sheaf J (Type _)`
    (`Mathlib.CategoryTheory.Sites.SheafHom`, L42-L100) — wrong codomain
    (Type, not `ModuleCat R`).
  - `SheafOfModules.Hom : SheafOfModules R → SheafOfModules R → Type _`
    (`Mathlib.Algebra.Category.ModuleCat.Sheaf`) — the *external* Hom (a
    bare type), not a sheaf of `R`-modules.
  - The category `X.Modules := SheafOfModules X.ringCatSheaf`
    (`Mathlib.AlgebraicGeometry.Modules.Sheaf` L37) is the abelian category of
    `O_X`-modules, but `Mathlib.AlgebraicGeometry.Modules.Sheaf.lean` defines
    NO internal-Hom / dual functor. The file has only pushforward / pullback /
    restriction. Verified via
    `grep -rn "internalHom\|^def ihom\|sheafHom\|dual" .lake/.../Modules/`.
- **Project's current path**: typed `sorry` body, with iter-180 Lane D
  task_result naming this exact gap.
- **Gap**: divergent-with-cost — the Hartshorne "Hom_{O_C}(I_P, O_C)" entry
  point through Mathlib's `IdealSheafData` is **structurally blocked** on
  three layers: (i) `IdealSheafData` is "data describing an ideal sheaf",
  not yet a `SheafOfModules` (Mathlib's own docstring at
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` L38 says: "Ideal sheaves are
  not yet defined in this file as actual subsheaves of `O_X`"); (ii) no
  Mathlib `IdealSheafData → SheafOfModules` realiser exists; (iii) even if
  (i)+(ii) existed, no `SheafOfModules → SheafOfModules` dual functor exists.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL for the "Hom_{O_C}(I_P, O_C)" path.

### Decision 2 — Ideal-sheaf-of-a-closed-point

- **Mathlib idiom**:
  `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal :
    TopologicalSpace.Closeds X → X.IdealSheafData`
  (`Mathlib.AlgebraicGeometry.IdealSheaf.Basic`, L? per `lean_leansearch`).
  Packages `{P}` as a closed subset → an `IdealSheafData` recording the
  ideal-component over each affine open.
- **Project's current path**: docstring at OCofP L131-L134 mentions
  `IdealSheafData.idealOfPoint`, but **that exact name does not exist** in
  Mathlib (`lean_local_search "idealOfPoint"` returns no Mathlib hits — the
  correct construction is `vanishingIdeal ⟨{P}, hP⟩`, with `hP : IsClosed`
  packaged into `Closeds`).
- **Gap**: identical at the data level (the closed-subset → ideal-data
  function exists); divergent-with-cost at the sheaf level (no
  `IdealSheafData → SheafOfModules` realiser, see Decision 1).
- **Verdict**: PROCEED at the data level (use `vanishingIdeal`),
  NEEDS_MATHLIB_GAP_FILL at the sheaf level.

### Decision 3 — Subsheaf-of-the-function-field (Hartshorne's alternative)

Hartshorne II §6 p. 144 packages `O_C(D)` DIRECTLY as a subsheaf of the
function-field constant sheaf `K_C`. For `D = [P]` on a curve, sections over
`U` are rational functions `f ∈ K(C)` with order conditions `ord_Q(f) ≥ 0`
for every prime divisor `Q ∈ U`, `Q ≠ P`, and `ord_P(f) ≥ −1` when `P ∈ U`.

- **Mathlib idiom** *(closest analogue)*:
  - `AlgebraicGeometry.Scheme.functionField`
    (`Mathlib.AlgebraicGeometry.FunctionField`) — `K(C)` as a `Field`-typed
    `CommRingCat`, for `IrreducibleSpace X` (auto on `IsIntegral`).
  - `CategoryTheory.Subpresheaf` / `Subfunctor`
    (`Mathlib.CategoryTheory.Sites.Subsheaf`) — but it's **`Type _`-valued
    only**, not `ModuleCat R`-valued. So Mathlib has no off-the-shelf
    "subsheaf of `ModuleCat kbar`-valued sheaf" gadget.
  - However, the **project itself already has the recipe** for landing a
    `Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat kbar)`
    bottom-up: `Scheme.toModuleKPresheaf` + `toModuleKPresheaf_isSheaf`
    (`AlgebraicJacobian/Cohomology/StructureSheafModuleK/{Presheaf,SheafProperty}.lean`)
    builds `O_C` as a `Sheaf J (ModuleCat kbar)` by hand from
    `C.left.presheaf` and the `Spec kbar`-algebra structure. The same
    template applies to `O_C(P)`: per-open submodule of `K(C)`, restriction
    is identity-on-`K(C)`, sheaf property reduces to order-conditions
    being local at prime divisors.
- **Project's current path**: not used yet (Decision 1's Hartshorne-II.6
  "Hom_{O_C}(I_P, O_C)" alternative description was the intended path; the
  subsheaf-of-`K_C` description is the project's bypass).
- **Gap**: divergent-equivalent — both descriptions yield the same invertible
  sheaf (Hartshorne II.6.18 / Proposition 6.13(a)); the subsheaf-of-`K_C`
  description sidesteps both Mathlib gaps from Decision 1.
- **Verdict**: ALIGN_WITH_MATHLIB on the recipe (mirror `toModuleKSheaf`'s
  presheaf-by-hand pattern), DIVERGE_INTENTIONALLY on the abstract
  "Hom_{O_C}(I_P, O_C)" packaging (NOT a Mathlib path yet).

### Decision 4 — In-project `IdealSheafDual.lean` bottom-up file?

Per the iter-180 Lane D task_result, the alternative considered was to build
a project-side `IdealSheafData → SheafOfModules` realiser + dual functor in a
new file. Given Decisions 1–3:

- **Mathlib idiom**: would be Mathlib-equivalent infrastructure: tons of
  abstract sheaf-of-modules machinery, ETA hundreds of LOC. **Not
  recommended** — the project doesn't NEED the abstract `SheafOfModules`
  dual; it needs *this one* invertible sheaf `O_C(P)` as a
  `Sheaf J (ModuleCat kbar)`.
- **Project's current path**: the directive opens this as an option.
- **Gap**: high cost, low payoff — building the abstract machinery to get
  exactly one sheaf is wasteful when the direct construction
  (Decision 3) lands the same sheaf in ~200-300 LOC and the same file.
- **Verdict**: DIVERGE_INTENTIONALLY — do **not** open `IdealSheafDual.lean`.
  Build directly in `OCofP.lean` via Decision 3's recipe.

## Recommendation

**Option (c) — Direct construction in `OCofP.lean` via Hartshorne's
subsheaf-of-`K_C` description**, mirroring the project's existing
`toModuleKSheaf` template. The Mathlib `Sheaf-internal-Hom` /
`SheafOfModules.dual` / `IdealSheafData → SheafOfModules` chain is
genuinely missing and would require Mathlib upstream work to ship; the
Hartshorne alternative description (mathematically equivalent per Hartshorne
Prop 6.13) lands directly at the `Sheaf J (ModuleCat kbar)` level the
project's `HModule` pipeline consumes.

### Recipe for `lineBundleAtClosedPoint` body (ETA: ~180-280 LOC)

```lean
-- 1. The subset of K(C) with controlled pole at P, on an open U.
private def lineBundleAtClosedPoint_carrier
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))} [IsIntegral C.left]
    [∀ Q : C.left.PrimeDivisor,
        Ring.KrullDimLE 1 (C.left.presheaf.stalk Q.point)]
    (P : C.left) (hPcoh : Order.coheight P = 1) (U : (Opens C.left.toTopCat)ᵒᵖ) :
    Submodule kbar C.left.functionField :=
  { carrier := { f | (∀ Q : C.left.PrimeDivisor, Q.point ∈ U.unop.1 →
                  Q.point ≠ P → 0 ≤ Scheme.RationalMap.order Q f) ∧
                  (P ∈ U.unop.1 → (-1 : ℤ) ≤
                    Scheme.RationalMap.order ⟨P, hPcoh⟩ f) }
    zero_mem' := by … (order of 0 is +∞)
    add_mem' := by … (order is super-additive / non-archimedean)
    smul_mem' := by … (k̄-scalar doesn't change orders at prime divisors) }

-- 2. Presheaf: restriction is identity-on-K(C), constraint set shrinks.
private noncomputable def lineBundleAtClosedPoint_presheaf … :
    (Opens C.left.toTopCat)ᵒᵖ ⥤ ModuleCat.{u} kbar where
  obj U := ModuleCat.of kbar ↥(lineBundleAtClosedPoint_carrier P hPcoh U)
  map {U V} f := ModuleCat.ofHom
    -- inclusion from larger constraint set (V ⊆ U means constraint on V ⊆ constraint on U)
    (Submodule.inclusion (by
      intro x hx
      refine ⟨fun Q hQU hQP => hx.1 Q (Set.mem_of_subset_of_mem ?leOfHom hQU) hQP, ?_⟩
      · intro hPV
        exact hx.2 (Set.mem_of_subset_of_mem ?leOfHom hPV)))
  map_id := …
  map_comp := …

-- 3. Sheaf property: order conditions at a prime divisor Q are local at Q's point;
--    cover U by Vᵢ; if f satisfies conditions on each Vᵢ then it satisfies on U.
private lemma lineBundleAtClosedPoint_presheaf_isSheaf … :
    Presheaf.IsSheaf (Opens.grothendieckTopology C.left.toTopCat)
      (lineBundleAtClosedPoint_presheaf P hPcoh) := by
  -- Two-step: first show the FORGET to Type is a sheaf (via subobject-of-constant-sheaf-is-sheaf),
  -- then apply Presheaf.isSheaf_iff_isSheaf_forget on (CategoryTheory.forget (ModuleCat kbar)).
  -- Mathematical core: the underlying set-valued presheaf is a subpresheaf of the constant
  -- presheaf at K(C); each constraint "ord_Q(f) ≥ k" is a stalk-local condition at Q.
  sorry  -- ~100 LOC of "order conditions glue" lemmas

-- 4. Bundle as Sheaf
noncomputable def lineBundleAtClosedPoint … : Sheaf … (ModuleCat kbar) :=
  ⟨lineBundleAtClosedPoint_presheaf P hPcoh,
   lineBundleAtClosedPoint_presheaf_isSheaf P hPcoh⟩
```

**Note**: the project's `lineBundleAtClosedPoint` signature currently consumes
`hP : IsClosed {P}` but NOT `Order.coheight P = 1` (only the helpers do, see
OCofP L208). For the subsheaf-of-`K_C` construction to use
`Scheme.RationalMap.order ⟨P, hPcoh⟩`, the **signature must be amended** to
also consume `hPcoh : Order.coheight P = 1` (or extracted from the
codimension-1 hypothesis already present). The signature is **not in
`archon-protected.yaml`** (verified — no entry for `lineBundleAtClosedPoint`),
so this is a free amendment; the planner should fold this into the iter-182
prover directive.

### Recipe for `toFunctionField` body (ETA: ~40-60 LOC)

```lean
noncomputable def lineBundleAtClosedPoint.toFunctionField
    … (P : C.left) (hP : IsClosed ({P} : Set C.left))
    (s : Scheme.HModule kbar (lineBundleAtClosedPoint (C := C) P hP) 0) :
    C.left.functionField := by
  -- s : Ext⁰((constantSheaf J (ModuleCat kbar)).obj (ModuleCat.of kbar kbar))
  --       (lineBundleAtClosedPoint P hP) 0
  -- Step 1: collapse via Abelian.Ext.linearEquiv₀
  let φ : (constantSheaf … (ModuleCat.of kbar kbar)) ⟶ lineBundleAtClosedPoint P hP :=
    HModule_zero_linearEquiv kbar _ s
  -- Step 2: evaluate the nat-trans at ⊤ : Opens C
  let φ_top : ModuleCat.of kbar kbar ⟶
              (lineBundleAtClosedPoint P hP).val.obj (op ⊤) := φ.val.app (op ⊤)
  -- Step 3: apply to 1 ∈ kbar
  let elt : ↥(lineBundleAtClosedPoint_carrier P hPcoh (op ⊤)) := φ_top.hom 1
  -- Step 4: project to K(C)
  exact elt.val
```

### LOC and risk summary

| Body | ETA | Risk | Mathlib-blocking |
|------|-----|------|-------------------|
| `lineBundleAtClosedPoint_carrier` (submodule) | ~30-50 LOC | low | none |
| `lineBundleAtClosedPoint_presheaf` (functor + restriction) | ~40-70 LOC | low | none |
| `lineBundleAtClosedPoint_presheaf_isSheaf` (sheaf prop) | ~80-150 LOC | **medium** | hinges on a "constraint-on-prime-divisors-is-local" lemma; may need a `RationalMap.order` stalk-locality bridge from `RR.1`'s `WeilDivisor.lean` |
| `lineBundleAtClosedPoint` (bundle) | ~5 LOC | trivial | none |
| `toFunctionField` (4-step chain) | ~40-60 LOC | low | none |
| **Total** | **~195-335 LOC** | medium | none — all in-project |

The bulk (sheaf property, ~80-150 LOC) is the only medium-risk piece; everything
else is mechanical. The "stalk locality of `order Q f`" lemma is likely already
hidden inside `RR.1`'s `RationalMap.order` defn (the iter-181 lean-auditor
report flagged that lane as landed); a single bridge lemma should suffice.

### What NOT to do

- **Do NOT** open `IdealSheafDual.lean` — the abstract `IdealSheafData →
  SheafOfModules → Hom_{O_C}(I_P, O_C)` chain is hundreds of LOC of
  *general* Mathlib infrastructure for the purpose of producing exactly one
  sheaf the project can construct directly in <300 LOC via Hartshorne's
  alternative description.
- **Do NOT** define `lineBundleAtClosedPoint` as a structurally vacuous
  placeholder (e.g. constant sheaf at zero, or just `toModuleKSheaf C`) —
  the iff `globalSections_iff` would still be mathematically vacuous and
  the iter-181 lean-auditor MAJOR finding would persist.
- **Do NOT** route via `X.Modules` (the new `Mathlib.AlgebraicGeometry.Modules`
  category) — the forget bridge `X.Modules → Sheaf J (ModuleCat kbar)` is
  **also missing** in Mathlib (only `X.Modules → TopCat.Presheaf Ab X`
  exists, see `Mathlib.AlgebraicGeometry.Modules.Sheaf` L72-L76). Same gap,
  different abstraction.

### Signature amendment

Add `(hPcoh : Order.coheight P = 1)` to `lineBundleAtClosedPoint` signature
(currently `lineBundleAtClosedPoint P hP : Sheaf …`). The helpers
`globalSections_iff_{mp,mpr}` already take `hPcoh`; lifting it to the
top-level def consolidates the hypothesis structure. **Verified
non-protected**: `grep "lineBundleAtClosedPoint" archon-protected.yaml`
returns empty.
