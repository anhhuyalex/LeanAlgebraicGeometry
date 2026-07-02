# Analogy: Lane F `pullback_of_openImmersion_iso_restrict` smul-compatibility chaining

## Mode
api-alignment

## Slug
lane-f-restrictscalars-smul

## Iteration
191

## Question

In `Picard/QuotScheme.lean:650-739`, the `pullback_of_openImmersion_iso_restrict`
helper builds a `Γ(Y, U)`-LinearEquiv between
`Γ((Scheme.Modules.pullback hU.fromSpec).obj N, ⊤)` and `Γ(N, U)`. The
AddEquiv part is built (iter-190). The residual is the smul-compatibility
leg, which the iter-190 prover correctly identified as a
`ModuleCat.restrictScalars` smul-unfold + Stacks 01HH-style structure-sheaf
compatibility chain.

The question: is there a CANONICAL high-level Mathlib lemma packaging the
LinearEquiv-level statement "pullback-along-open-immersion vs
restrict-along-open-immersion of a sheaf of modules at `⊤`-sections"?
If not, what is the canonical chaining order, and is a project refactor
(carrier reshape) preferable?

## Project artifact(s)

- `AlgebraicJacobian/Picard/QuotScheme.lean:650-739` —
  `pullback_of_openImmersion_iso_restrict` (Step 3 typed-sorry pin from
  iter-189 Lane F unbundling).
- `AlgebraicJacobian/Picard/QuotScheme.lean:713-739` — the smul-leg
  residual after iter-190's AddEquiv-construction and
  `Scheme.Modules.Hom.app_smul` application.

## Mathlib precedents examined (b80f227)

| Mathlib symbol | Location | What it gives |
|---|---|---|
| `Scheme.Modules.restrictFunctorIsoPullback` | `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:371` | Natural iso `restrictFunctor f ≅ pullback f` for open-immersion `f`. **No `_app_app` / `_top_linearEquiv` simp lemma** packaging this at section level. |
| `Scheme.Modules.restrict_obj` | `Sheaf.lean:328` | `Γ(M.restrict f, U) = Γ(M, f ''ᵁ U)` by `rfl`. **Type-equal**, but the `Γ(X, U)`-action via restrictScalars is distinct from the natural `Γ(Y, f ''ᵁ U)`-action. |
| `Scheme.Modules.map_smul` | `Sheaf.lean:95` | `M.presheaf.map i.op (r • x) = X.presheaf.map i.op r • M.presheaf.map i.op x` (for `i : U ⟶ V` in `X.Opens`, `r : Γ(X, V)`). |
| `Scheme.Modules.Hom.app_smul` | `Sheaf.lean:110` | `φ.app U (r • x) = r • φ.app U x` (for `φ : M ⟶ N` in `X.Modules`, `r : Γ(X, U)`). |
| `ModuleCat.restrictScalars.smul_def` | `Algebra/Category/ModuleCat/ChangeOfRings.lean:120` | `r • m = f r • show M from m` (`rfl`). The pushforward at section is `restrictScalars (φ.app U).hom`, so the smul-unfold is definitional once the type ascription is right. |
| `Scheme.Hom.appLE_appIso_inv` | `Mathlib/AlgebraicGeometry/OpenImmersion.lean:229` | `f.appLE U V e ≫ (f.appIso V).inv = Y.presheaf.map (homOfLE (f ''ᵁ V ≤ U)).op`. Reassoc + simp + elementwise versions exist. |
| `IsAffineOpen.fromSpec_app_self` | `Mathlib/AlgebraicGeometry/AffineScheme.lean:561` | `hU.fromSpec.app U = (ΓSpecIso _).inv ≫ (Spec _).presheaf.map (eqToHom hU.fromSpec_preimage_self).op`. `@[elementwise]` — auto-generates `_apply` form. |
| `Scheme.Hom.appLE` (definition) | `Mathlib/AlgebraicGeometry/Scheme.lean` (search) | `f.appLE U V e = f.app U ≫ X.presheaf.map (homOfLE e).op`. |
| `IsAffineOpen.fromSpec_preimage_self` | `AffineScheme.lean:550` | `hU.fromSpec ⁻¹ᵁ U = ⊤`. |
| `IsAffineOpen.opensRange_fromSpec` | `AffineScheme.lean:447` | `hU.fromSpec.opensRange = U` (equivalently `hU.fromSpec ''ᵁ ⊤ = U`). |

## Decisions identified

### Decision 1: Is there a high-level LinearEquiv-level Mathlib lemma?

- **Mathlib idiom**: NO. `Scheme.Modules.restrictFunctorIsoPullback`
  (Sheaf.lean:371) is the natural iso between the two functors, but Mathlib
  does NOT ship:
  - An `_app_app` / `_top_app` simp lemma for it.
  - A `LinearEquiv`-bundled section-level version.
  - A "pullback ≅ restrict at `⊤`" lemma packaging the eqToHom transport
    along `f.opensRange`.
  The Sheaf.lean file has explicit `_app_app` simps for `restrictFunctorId`,
  `restrictFunctorComp`, `restrictFunctorCongr` (L382, L401, L415), but
  NOT for `restrictFunctorIsoPullback`. That's the gap.

- **Project's path** (`QuotScheme.lean:670-712`): construct an AddEquiv
  carrier explicitly via `(restrictFunctorIsoPullback _).app N |>.symm`,
  then upgrade to `LinearEquiv` via the smul-leg using `Hom.app_smul` +
  presheaf restriction.

- **Gap**: divergent-equivalent. The project is doing the manual unbundling
  that Mathlib would do if asked, just without a high-level wrapper.

- **Verdict**: **PROCEED** — no Mathlib lemma to align with at this
  fidelity level. The chain is the canonical Mathlib idiom; only the
  high-level packaging is missing.

### Decision 2: Canonical chaining order for the smul-leg

The chain that iter-190 identified is correct. After
`rw [Scheme.Modules.Hom.app_smul]` (L725, already applied), the residual is:

```
⊢ (N.presheaf.map (eqToHom hImg.symm).op).hom
      ((ΓSpecIso _).inv.hom r • (Hom.app isoSheaf.hom ⊤).hom x) =
    r • addEq x
```

The canonical Mathlib chain (top-down):

**Step A — `restrictScalars.smul_def` (definitional):**

  The LHS smul of `(ΓSpecIso _).inv.hom r : Γ(Spec Γ(Y, U), ⊤)` on
  `y := (Hom.app isoSheaf.hom ⊤).hom x ∈ Γ(N.restrict hU.fromSpec, ⊤)` is
  the action of the pushforward / restrictScalars-wrapped ModuleCat.
  Per `PresheafOfModules.pushforward` (Sheaf/PushforwardContinuous.lean:46)
  and `pushforward = pushforward₀ ⋙ restrictScalars φ`
  (Presheaf/Pushforward.lean:87), the smul rfl-unfolds to:
  `(ΓSpecIso _).inv.hom r • y = ((hU.fromSpec.appIso ⊤).inv.hom ((ΓSpecIso _).inv.hom r)) • y`
  where the RHS uses the natural `Γ(Y, hU.fromSpec ''ᵁ ⊤)`-action on
  `Γ(N, hU.fromSpec ''ᵁ ⊤) = Γ(N.restrict hU.fromSpec, ⊤)`.

**Step B — `Scheme.Modules.map_smul` (Sheaf.lean:95):**

  With the LHS scalar now in `Γ(Y, hU.fromSpec ''ᵁ ⊤)`, applying
  `N.presheaf.map (eqToHom hImg.symm).op` migrates it through:
  `(N.presheaf.map i.op).hom (s • y) = Y.presheaf.map i.op s • (N.presheaf.map i.op).hom y`

**Step C — Stacks 01HH ring identity:**

  Show that
  `(Y.presheaf.map (eqToHom hImg.symm).op).hom ((hU.fromSpec.appIso ⊤).inv.hom ((ΓSpecIso _).inv.hom r)) = r`.

  Categorical form:
  `(ΓSpecIso _).inv ≫ (hU.fromSpec.appIso ⊤).inv ≫ Y.presheaf.map (eqToHom hImg.symm).op = 𝟙 Γ(Y, U)`.

  Sub-chain:
  - `Hom.appLE U ⊤ e = app U ≫ Spec.presheaf.map (homOfLE e).op` (definition).
  - `IsAffineOpen.fromSpec_app_self` (AffineScheme.lean:561): expands
    `hU.fromSpec.app U`.
  - Combined: `hU.fromSpec.appLE U ⊤ e = (ΓSpecIso _).inv` (the two
    Spec-side `eqToHom`/`homOfLE` arrows compose to `𝟙 (⊤ : (Spec _).Opens)`
    via `eqToHom_trans`, `eqToHom_refl`, `Functor.map_id`).
  - `Scheme.Hom.appLE_appIso_inv` (OpenImmersion.lean:229): substituting
    the previous, get `(ΓSpecIso _).inv ≫ (hU.fromSpec.appIso ⊤).inv = Y.presheaf.map (homOfLE: hU.fromSpec ''ᵁ ⊤ ≤ U).op`.
  - Post-composing with `Y.presheaf.map (eqToHom hImg.symm).op` and
    using `Functor.map_comp`: the composite `(eqToHom hImg.symm) ≫ (homOfLE ...) : U ⟶ U`
    in the posetal category `Opens Y` is forced to be `𝟙 U`, so
    `Y.presheaf.map (𝟙 U).op = 𝟙 _`.

- **Verdict**: **PROCEED** — chaining sequence as above is the canonical
  Mathlib idiom. Estimated 30-50 LOC.

### Decision 3: Step-A hazard — `restrictScalars.smul_def` doesn't auto-fire

- **Mathlib idiom**: Although `ModuleCat.restrictScalars.smul_def`
  (ChangeOfRings.lean:120) is `rfl` and tagged `@[simp]`, Lean's HSMul
  instance resolution **does NOT unfold `Scheme.Modules.restrict_obj`**
  (also a `rfl`, Sheaf.lean:328) during unification. Concretely, attempts
  to `change` or `show` the smul as a `Γ(Y, hU.fromSpec ''ᵁ ⊤)`-action on
  the same underlying element fail with:
  ```
  failed to synthesize instance of type class
    HSMul ↑Γ(Y, hU.fromSpec ''ᵁ ⊤) ↑Γ(N.restrict hU.fromSpec, ⊤) ?m
  ```
  (verified via `lean_multi_attempt` at the goal line). The issue: the
  type `Γ(N.restrict hU.fromSpec, ⊤)` has only `Γ(Spec _, ⊤)`-action
  registered as an instance, even though it's `rfl`-equal to
  `Γ(N, hU.fromSpec ''ᵁ ⊤)` which DOES have `Γ(Y, hU.fromSpec ''ᵁ ⊤)`-action.

- **Project's path** (iter-190 attempt): the proof body needed to
  `change` directly to the Y-side smul, but the instance synthesis
  diverges.

- **Workaround (recommended for iter-192 prover)**: introduce an
  explicit `let y : ↑Γ(N, hU.fromSpec ''ᵁ ⊤) := (Hom.app isoSheaf.hom ⊤).hom x`
  to ALIAS the element under its `restrict_obj`-unfolded type. Then
  the smul-unfold `(s : Γ(Spec _, ⊤)) • y = (appIso _).inv.hom s • y`
  is `rfl` against `y`'s type. The original goal can then be rewritten
  using this aliased view.

- **Verdict**: **PROCEED** with the workaround. This is a Lean-elaboration
  hazard, not a structural problem.

### Decision 4: Alternative refactor — carrier reshape to Γ(Spec _, ⊤)-linearity

Hypothetical refactor (outcome C): change the carrier of
`pullback_of_openImmersion_iso_restrict` from a `Γ(Y, U)`-LinearEquiv
to a `Γ(Spec Γ(Y, U), ⊤)`-LinearEquiv:

```lean
Γ((pullback hU.fromSpec).obj N, ⊤) ≃ₗ[Γ(Spec Γ(Y, U), ⊤)] Γ(N.restrict hU.fromSpec, ⊤)
```

The smul-leg then becomes trivial: it's `Hom.app_smul` for the
SheafOfModule iso alone (no Stacks 01HH bridge needed).

**However**, the consumer (`pullback_app_isoTensor_baseMap_sectionLinearEquiv`,
QuotScheme.lean:774) wants a `Γ(Y, U)`-LinearEquiv at the end. The Stacks
01HH bridge would need to be discharged at the consumer site instead.
**This refactor doesn't save work**; it just relocates the obstruction.

- **Verdict**: **DIVERGE_INTENTIONALLY (avoid refactor)** — the current
  carrier shape is correct. Moving the Stacks 01HH bridge to the consumer
  would just push the problem one layer up, where it's harder to localize.

## Recommendation

**iter-192 Lane F prover dispatch — CONCRETE RECIPE:**

The prover should follow the iter-190-identified chain with one
elaboration hazard mitigation:

1. **Carry over iter-190 progress**: AddEquiv `addEq` is built (L707-712);
   `rw [Scheme.Modules.Hom.app_smul]` is applied (L725).

2. **Step A workaround** (Decision 3): aliasing `let`.
   ```lean
   let y : ↑Γ(N, hU.fromSpec ''ᵁ ⊤) := (Scheme.Modules.Hom.app isoSheaf.hom ⊤).hom x
   -- y : Γ(N, hU.fromSpec ''ᵁ ⊤) is type-equal to Γ(N.restrict hU.fromSpec, ⊤)
   -- but carries the Y-side Module structure for the smul re-expression.
   ```

3. **Step A reduce smul**: use `change`/`show` to re-express the LHS
   smul as `Γ(Y, hU.fromSpec ''ᵁ ⊤)`-action via the definitional
   `restrictScalars.smul_def`. The exact form:
   ```lean
   change (N.presheaf.map (eqToHom hImg.symm).op).hom
     (((hU.fromSpec.appIso ⊤).inv.hom ((Scheme.ΓSpecIso _).inv.hom r)) • y) = _
   ```
   (where the `•` is now the natural Y-side smul on `Γ(N, hU.fromSpec ''ᵁ ⊤)`).

4. **Step B**: `rw [Scheme.Modules.map_smul]` to migrate the Y-side scalar
   through `N.presheaf.map (eqToHom hImg.symm).op`.

5. **Step C**: prove the categorical key identity, then apply to `r`:
   ```lean
   have key : (Scheme.ΓSpecIso Γ(Y, U)).inv ≫
              (hU.fromSpec.appIso ⊤).inv ≫
              Y.presheaf.map (eqToHom hImg.symm).op = 𝟙 _ := by
     have hpre : hU.fromSpec ⁻¹ᵁ U = ⊤ := hU.fromSpec_preimage_self
     -- ... use appLE_appIso_inv + fromSpec_app_self + Functor.map_comp ...
   -- elementwise apply key to r to get the scalar identity, then `rfl`
   exact congr($key r) -- or similar elementwise extraction
   ```

6. **Final smul congr**: after Step C, the only residual is a smul-congr
   step `r • a = r • a` which closes by `rfl`.

**LOC estimate**: 30-50, with the bulk in Step C's poset bookkeeping for
the `eqToHom hImg.symm ≫ homOfLE _ = 𝟙 U` collapse.

**Anti-recommendations**:

- Do NOT refactor the carrier (Decision 4). Moves work, doesn't save it.
- Do NOT try to use `simp` blindly with `restrictScalars.smul_def`. The
  instance-resolution failure (Decision 3) means `simp` will get stuck.
  An explicit aliasing `let` is required.
- Do NOT chase a high-level Mathlib lemma (Decision 1). The closest
  (`restrictFunctorIsoPullback`) is a natural iso of functors with no
  app/section simp lemmas; using it doesn't shorten the chain.

## Verdict summary

| Decision | Verdict | Severity |
|---|---|---|
| 1. High-level LinearEquiv lemma in Mathlib? | PROCEED (no such lemma) | informational |
| 2. Canonical chaining order | PROCEED (chain as iter-190 identified, with explicit Mathlib citations) | informational |
| 3. Step-A elaboration hazard (`restrictScalars.smul_def` doesn't auto-fire) | PROCEED with aliasing-`let` workaround | high (without the workaround, the prover risks a 6th flat iter) |
| 4. Carrier reshape refactor | DIVERGE_INTENTIONALLY (avoid) | informational |

**Overall verdict**: **PROCEED**. The recipe identified by iter-190 is
the canonical Mathlib chain. No high-level Mathlib lemma packages this
at the LinearEquiv level (Mathlib has `restrictFunctorIsoPullback` but
no `_app_app` simp), and no project refactor would be cleaner (carrier
reshape just relocates the Stacks 01HH bridge). The iter-192 prover
dispatch is licensed, with the **critical elaboration-hazard mitigation**
(Decision 3) — explicit aliasing `let` for the smul-unfold step.
