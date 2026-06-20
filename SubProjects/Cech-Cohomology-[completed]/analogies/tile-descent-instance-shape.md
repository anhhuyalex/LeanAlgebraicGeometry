# Analogy: installing `Module R` / `IsScalarTower R R_g` on a `Spec`-noncomputable tile carrier

## Mode
api-alignment

## Slug
tile-descent

## Iteration
046

## Question
Is the project's chosen instance-install shape (dynamically installing `Module R` +
`IsScalarTower R R_g` via `letI`/`haveI`/`have inst := inferInstanceAs …` on the
`modulesSpecToSheaf.obj`/tile section carrier whose *type* mentions `Spec`) the
Mathlib-idiomatic one, or does a different shape avoid the W1/W2/W3 wall entirely?

## Project artifact(s)
- `QcohTildeSections.lean:663-703` — `isLocalizedModule_powers_restrictScalars_of_algebraMap`
  (the DONE base-ring descent; takes `[Module R M] [Module R N] [Module A M] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]` **as arguments** — already the preferred shape).
- `QcohTildeSections.lean:725-764` — the two rfl smul bridges; both carriers' underlying type is
  `F.val.obj (op (ι ''ᵁ V))`.
- `QcohTildeSections.lean:1003-1066` — the W1/W2/W3 wall block + inline-term sketch.

## The diagnosis (root cause)

`IsLocalizedModule`-descent inherently needs **two** ring actions (`R` and `R_g`) plus a tower on
**one** carrier. The project has two *bundled* packagings of the same underlying section type
`F.val.obj (op (ι ''ᵁ V))`, and each packaging makes exactly **one** of the two actions structural:

| Carrier as written | structural `Module R` | structural `Module R_g` |
|---|---|---|
| `(modulesSpecToSheaf.obj F).presheaf.obj (op W)` — a `ModuleCat R` obj | ✓ | ✗ |
| `(modulesSpecToSheaf.obj (tile)).presheaf.obj (op V)` — a `ModuleCat R_g` obj | ✗ | ✓ |

`modulesSpecToSheaf : (Spec R).Modules ⥤ TopCat.Sheaf (ModuleCat ↑R) _` (Mathlib,
`AlgebraicGeometry.modulesSpecToSheaf`). The descent needs *both* on one carrier, so whichever
carrier you pick, the *other* action is missing and must be supplied. The project supplied it by
`letI`/`have` inside the `theorem` body — and an instance is **data**, so when its `Spec`-noncomputable
value leaks into a later type the elaborator lifts it into an auxiliary `def` that is generated
*without* the `noncomputable` modifier and fails codegen (**W1**). `IsScalarTower R R_g (carrier)`
won't even state because no `SMul R` is registered on a `ModuleCat R_g` carrier (**W2**). The single
giant inline `@…` term avoids the `letI` lift but then the carrier-`rfl` + scalar-compat defeqs blow
the heartbeat budget (**W3**).

This is a **manual-instance-installation anti-pattern**. Mathlib's `RestrictScalars` docstring is
written almost verbatim for this situation.

## Decisions identified

### Decision: how to supply the missing base-ring module/tower instance

- **Mathlib idiom**: `Mathlib.Algebra.Algebra.RestrictScalars`, docstring lines **60–77**:
  > "we can't directly state our map as we have no `Module R M` structure … it is usually better just
  > to add this extra structure as an argument `[Module R M] [IsScalarTower R S M]`. … If some concrete
  > `M` naturally carries these … we have avoided `RestrictScalars` entirely. If not, we can pass
  > `RestrictScalars R S M` later on instead of `M`."

  Two blessed mechanisms, both making the instances **structural / TC-found** (never `letI`-installed):
  1. **Bundled restriction-of-scalars object** —
     `ModuleCat.restrictScalars (f : R →+* S) : ModuleCat S ⥤ ModuleCat R`
     (`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings:85`). Its object
     `(restrictScalars f).obj M` is a `ModuleCat R` obj, so:
     - `Module R ((restrictScalars f).obj M)` — **structural** (`RestrictScalars.obj'`,
       `…ChangeOfRings:66-68`, `Module.compHom M f`);
     - `Module S ((restrictScalars f).obj M)` — **Mathlib instance** (`…ChangeOfRings:110-112`);
     - `r • (show (restrictScalars f).obj M from m) = f r • m` — **rfl**
       (`ModuleCat.restrictScalars.smul_def'`, `…ChangeOfRings:124-127`).
  2. **`RestrictScalars R S M` type synonym** (`…RestrictScalars:82`):
     - `Module R (RestrictScalars R S M)` — **global instance** `RestrictScalars.module` (`:119`);
     - `IsScalarTower R S (RestrictScalars R S M)` — **global instance**
       `RestrictScalars.isScalarTower` (`:130`);
     - `Module S (RestrictScalars R S M)` — *not* global (`RestrictScalars.moduleOrig`, `:98`,
       deliberately local) — so this synonym is slightly worse here because the tile's `R_g`-action
       would need re-supplying.

  The descent itself already follows the *preferred* arg-shape: its signature takes
  `[Module R M] [IsScalarTower R A M]` as arguments. The whole failure is at the **instantiation**,
  where the prover tried to *manufacture* those arguments by hand instead of letting a
  restriction-of-scalars-wrapped carrier carry them structurally.

  Supporting Mathlib decls for the wrap + transport:
  - `IsScalarTower.of_algebraMap_smul` (`Mathlib.Algebra.Algebra.Tower:94`) and
    `IsScalarTower.of_compHom` (`:99`) — close `IsScalarTower R R_g ((restrictScalars (algebraMap R R_g)).obj M)`
    in one line from `restrictScalars.smul_def'` (and it is a **Prop**, so no codegen, no W1 hoist).
  - `IsLocalizedModule.of_linearEquiv` / `…of_linearEquiv_right`
    (`Mathlib.Algebra.Module.LocalizedModule.Basic:544,560`, both **instances**) — transport
    `σ.restrictScalars R` onto `ρ` along the identity-on-elements `R`-linear equivs (the equiv content
    is exactly the proven `tile_scalar_compat'` / the rfl carrier identity).
  - Ascent precedent the descent is the converse of: `IsLocalizedModule.of_restrictScalars`
    (`…LocalizedModule.Basic:702`) — note Mathlib there *assumes* all `[Module]`/`[IsScalarTower]`
    as ambient hypotheses; it never installs them in a body. Same discipline applies downstream.
  - (Architectural, not drop-in) `PresheafOfModules.restrictScalars`
    (`…ModuleCat.Presheaf.ChangeOfRings:52`) and `SheafOfModules.restrictScalars`
    (`…ModuleCat.Sheaf.ChangeOfRings:36`) — the *sheaf-level* change-of-rings the project is
    partially re-implementing by hand; not directly usable here because the descent crosses spaces
    (`Spec R_g` vs `Spec R`), so the per-section `ModuleCat.restrictScalars` is the right granularity.

- **Project's current path**: install `Module R` / `IsScalarTower R R_g` on the bare tile carrier via
  `letI`/`have`/inline `@`. Divergent.

- **Gap**: **divergent-and-wrong**. The cost is exactly W1–W3: noncomputable-aux-def codegen failure
  (W1), un-elaboratable `SMul R` (W2), heartbeat blow-up from the un-staged giant term (W3) — i.e. the
  divergence is *the blocker itself*, not a downstream tax.

- **Verdict**: **ALIGN_WITH_MATHLIB**.

### Decision: which carrier to phrase the descent on (Q2 — F-side vs tile vs wrapped)

- Phrasing the descent on the **F-side carrier** `F.val.obj (op W)` (native structure-sheaf
  `R`-action) makes `Module R` structural but **loses** structural `Module R_g` — a *symmetric*
  instance of the same wall. F-side **alone does not help**.
- The unique carrier where **both** actions are structural is the **restriction-of-scalars wrapper**
  `(ModuleCat.restrictScalars (algebraMap R R_g)).obj (tile-section)` (tile gives `Module R_g`
  structurally; the wrapper makes it a `ModuleCat R` obj, so `Module R` structural too). This is the
  carrier the descent's `M N` should unify against.
- **Verdict**: **ALIGN_WITH_MATHLIB** — wrap the tile carrier, do not move the descent wholesale to the
  F-side.

## Recommendation

Keep `isLocalizedModule_powers_restrictScalars_of_algebraMap` verbatim (it is already the preferred
arg-shape and is axiom-clean). Fix the **instantiation** by routing the descent's `M N` through the
bundled `ModuleCat.restrictScalars (algebraMap R R_g)` carrier so all four
`[Module R] [Module R_g] [IsScalarTower R R_g]` instances are **found by `inferInstance`** — no
`letI`, no `Spec`-noncomputable aux def (kills W1), `SMul R` present (kills W2), and stage the final
transport with `IsLocalizedModule.of_linearEquiv(_right)` + `eqToLinearEquiv`/`LinearEquiv.ofEq`
instead of one monster `rfl` (tames W3). Add one tiny Prop instance:

```lean
-- a Prop ⇒ no codegen ⇒ no W1 hoist; closes the tower structurally
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (M : ModuleCat S) :
    IsScalarTower R S ((ModuleCat.restrictScalars (algebraMap R S)).obj M) :=
  IsScalarTower.of_algebraMap_smul fun r m =>
    (ModuleCat.restrictScalars.smul_def' (algebraMap R S) r m).symm
```

then assemble (shape only):

```lean
lemma tile_section_localization (F : (Spec R).Modules) (U : (Spec R).Opens)
    (P : (F.over U).Presentation) (f g : R) (hg : specBasicOpen g ≤ U) :
    IsLocalizedModule (Submonoid.powers f) ρ.hom := by
  -- σ : tile(⊤) →ₗ[R_g] tile(D f̄), R_g-localization (DONE):
  have hσ : IsLocalizedModule (Submonoid.powers (algebraMap R (Localization.Away g) f)) σ := …
  -- carriers viewed as (ModuleCat.restrictScalars (algebraMap R R_g)).obj _ :
  --   Module R, Module R_g, IsScalarTower R R_g  ALL structural (no letI)
  have hdesc : IsLocalizedModule (Submonoid.powers f) (σ.restrictScalars R) :=
    isLocalizedModule_powers_restrictScalars_of_algebraMap
      (A := Localization.Away g) f σ hσ
  -- transport σ.restrictScalars R ≃ ρ along identity-on-elements R-equivs
  -- (equiv content = tile_scalar_compat' + the rfl carrier identity), via
  -- IsLocalizedModule.of_linearEquiv / …_right + eqToLinearEquiv.
  …
```

If the wrap still leaves a residual heavy `isDefEq` (W3) where the lemma must unify the bare tile
section against the wrapped one, insert an explicit `show`/`change` to the wrapped carrier (or an
`eqToLinearEquiv` step) so the kernel never whnf's the full `modulesSpecToSheaf`∘restrict tower in one
shot. The inline giant-`@`-term route (option c) is a *fallback only* — it does not address W3 and is
fragile.
