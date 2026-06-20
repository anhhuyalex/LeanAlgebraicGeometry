# Analogy: ModuleCat-S vs structure-sheaf Γ(Spec S, ⊤) action on sections of a module on Spec S

## Mode
api-alignment

## Slug
quot-sigma-rebasing

## Iteration
041

## Question

What is Mathlib's canonical idiom for relating the `ModuleCat S` scalar action (used by the
localization engine `isLocalizedModule_restrict_of_isIso_fromTildeΓ`, `S : CommRingCat`) on the
sections of a module on `Spec S` to the `Γ(Spec S, ⊤)` structure-sheaf scalar action (along which
`gammaPullbackImageIso_hom_semilinear` is semilinear), given `ΓSpecIso S : Γ(Spec S, ⊤) ≅ S`? Is the
bridge `restrictScalars` along `ΓSpecIso`, is it **defeq**, and is the project's
`σ = (ΓSpecIso S).symm ≪≫ gammaImageRingEquiv j ⊤` the Mathlib-aligned choice?

## Project artifact(s)
- `AlgebraicJacobian/Picard/QuotScheme.lean:510` — `isLocalizedModule_restrict_of_isIso_fromTildeΓ`
  (engine; produces `IsLocalizedModule (powers f)` over the `CommRingCat` `R`, viewing
  `(modulesSpecToSheaf.obj M).presheaf.obj (op U)` as `ModuleCat R`).
- `AlgebraicJacobian/Picard/QuotScheme.lean:1857` — `gammaImageRingEquiv` (`σ_V : Γ(X,V) ≃+* Γ(Y, j''ᵁ V)`).
- `AlgebraicJacobian/Picard/QuotScheme.lean:1867` — `gammaPullbackImageIso_hom_semilinear`
  (semilinear over `gammaImageRingEquiv j V`, i.e. the **structure-sheaf** ring `Γ(X,V)`).
- `AlgebraicJacobian/Picard/QuotScheme.lean:1905` — `isLocalizedModule_powers_transport`
  (consumes a single `σ : S ≃+* A` with `σ f' = algebraMap R A f`).

## The decisive Mathlib fact: the rebasing is *baked into* `modulesSpecToSheaf` by `restrictScalars`

`modulesSpecToSheaf` (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`) is **defined** as:

```
def modulesSpecToSheaf : (Spec R).Modules ⥤ TopCat.Sheaf (ModuleCat R) (Spec R) :=
  SheafOfModules.forgetToSheafModuleCat (Spec R).ringCatSheaf (.op ⊤)
      (Limits.initialOpOfTerminal Limits.isTerminalTop)
  ⋙ sheafCompose _ (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom)
```

So the `ModuleCat R` object `(modulesSpecToSheaf.obj M).presheaf.obj (op U)` is obtained by two
`restrictScalars` steps from the genuine structure-sheaf `Γ(Spec R, U)`-module of sections:

1. **`forgetToSheafModuleCat`** rebases the *variable* ring `Γ(Spec R, U)` to the *global* ring
   `Γ(Spec R, ⊤)`. Concretely (`Mathlib/Algebra/Category/ModuleCat/Presheaf.lean:372`):
   `forgetToPresheafModuleCatObjObj … Y = (restrictScalars (R.map (hX.to Y)).hom).obj (M.obj Y)`,
   i.e. `restrictScalars` along the structure-sheaf restriction `Γ(Spec R,⊤) → Γ(Spec R,U)`. At
   `U = ⊤`, `hX.to (op ⊤) = id`, so this step is the identity on the `Γ(Spec R,⊤)`-action.
2. **`sheafCompose _ (restrictScalars (globalSectionsIso R).hom.hom)`** rebases `Γ(Spec R,⊤)` to the
   constant `CommRingCat` `R`, along `(StructureSheaf.globalSectionsIso R).hom`.

**Key identities (all `rfl`):**
- `StructureSheaf.globalSectionsIso R : CommRingCat.of R ≅ Γ(Spec R, ⊤)`, and
  `globalSectionsIso_hom : (globalSectionsIso R).hom = CommRingCat.ofHom (algebraMap R Γ(Spec R,⊤))`
  (`Mathlib/AlgebraicGeometry/StructureSheaf.lean:935,938`).
- `ΓSpecIso R : Γ(Spec R, ⊤) ≅ R` with
  `ΓSpecIso_inv : (ΓSpecIso R).inv = CommRingCat.ofHom (algebraMap R Γ(Spec R,⊤))`
  (`Mathlib/AlgebraicGeometry/Scheme.lean:606,623`).
- Therefore `(globalSectionsIso R).hom = (ΓSpecIso R).inv = algebraMap R Γ(Spec R,⊤)` — **the same
  ring map** (`(ΓSpecIso R).symm` as a `RingEquiv` has forward map exactly this `algebraMap`).
- `ModuleCat.restrictScalars.smul_def` (`…/ChangeOfRings.lean:120`) is **`rfl`**:
  `(r : R) • m = f r • (m : M)`.

Putting these together, for `s : S` and `x : (modulesSpecToSheaf.obj M').presheaf.obj (op ⊤)`:

```
s •_{ModuleCat S} x  =  (globalSectionsIso S).hom s •_{Γ(Spec S,⊤)} x  =  (ΓSpecIso S).inv s •_{Γ(Spec S,⊤)} x
```

**definitionally** (composite of two `restrictScalars.smul_def` rfls; at `⊤` the
`forgetToSheafModuleCat` step is the identity).

## Decisions identified

### Decision: bridge ModuleCat-S action ↔ Γ(Spec S,⊤) action

- **Mathlib idiom**: `ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso S).hom.hom`,
  literally a factor of `modulesSpecToSheaf`. The propositional surfacing lemma is
  `ModuleCat.restrictScalars.smul_def` (rfl); the ring-map identity is `globalSectionsIso_hom` =
  `ΓSpecIso_inv` = `algebraMap S Γ(Spec S,⊤)`. Cite: `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`
  (`modulesSpecToSheaf`), `…/ChangeOfRings.lean:85,120`, `…/StructureSheaf.lean:935`,
  `…/Scheme.lean:606,623`.
- **Project's path**: uses `(ΓSpecIso S).symm` (as `RingEquiv`) as the `S → Γ(Spec S,⊤)` leg of `σ`.
- **Gap**: identical. `(ΓSpecIso S).symm`'s forward map *is* the `restrictScalars` map baked into
  `modulesSpecToSheaf`; the reconciliation is **defeq**, not an extra transport.
- **Verdict**: PROCEED.

### Decision: shape of σ : S ≃+* A

- **Mathlib idiom**: there is **no** single pre-built ring iso "Spec-side `CommRingCat` ≃
  structure-sheaf-at-⊤ in `restrictScalars`-ready form" beyond `ΓSpecIso` / `globalSectionsIso`
  themselves. The structure-sheaf-to-image leg (`gammaImageRingEquiv = (j.appIso V).symm`) is also
  unavoidable — Mathlib has no packaged "pullback section ring iso" for a general open immersion onto
  a basic open. So a composite is the idiom; `ΓSpecIso` is the higher-level idiomatic name (the
  `AlgebraicGeometry.Scheme` namespace standardizes on it; `globalSectionsIso` is the lower-level
  `StructureSheaf` name for the *same* map).
- **Project's path**: `σ = (ΓSpecIso S).symm ≪≫ gammaImageRingEquiv j ⊤`.
- **Gap**: identical / minimal. The `(ΓSpecIso S).symm` factor is exactly the inverse of the rebasing
  `modulesSpecToSheaf` performs, not a kludge. The only cosmetic alternative is writing
  `globalSectionsIso S` in place of `(ΓSpecIso S).symm` (defeq same map) — not worth changing.
- **Verdict**: PROCEED.

## Recommendation

**Keep `σ = (ΓSpecIso S).symm ≪≫ gammaImageRingEquiv j ⊤`.** It is the Mathlib-aligned bridge, and
the ModuleCat-S vs structure-sheaf reconciliation it encodes is **definitional**: the engine's
`ModuleCat S` action on `Γ(M', U)` is *by construction* `restrictScalars (globalSectionsIso S).hom`
of the `Γ(Spec S,⊤)` action, and `(globalSectionsIso S).hom = (ΓSpecIso S).inv = algebraMap`. When
discharging the `he₁` hypothesis of `isLocalizedModule_powers_transport`
(`e₁ (s • x) = σ s • e₁ x`, `s : S`), rewrite the LHS `ModuleCat S`-smul to the `Γ(Spec S,⊤)`-smul via
`ModuleCat.restrictScalars.smul_def` (rfl) so it reads `e₁ ((ΓSpecIso S).inv s • x)`, then apply the
already-proven `gammaPullbackImageIso_hom_semilinear` with `a := (ΓSpecIso S).inv s`; the result
`gammaImageRingEquiv j ⊤ ((ΓSpecIso S).inv s) • e₁ x` is `σ s • e₁ x` by definition of `σ`. No new
infrastructure is needed.

**Subtlety to budget for (the `e₂`/`D(f')` leg).** `isLocalizedModule_powers_transport` takes a
*single* `σ` with codomain `A`, so both `e₁` (at `⊤`) and `e₂` (at `D(f')`) must land in
`A`-modules over the *same* `A = Γ(Spec R, j''ᵁ ⊤)`. The `ModuleCat S` action on the `D(f')` sections
carries the extra `forgetToSheafModuleCat` restriction `Γ(Spec S,⊤) → Γ(Spec S, D(f'))` on top of the
`globalSectionsIso` step. Do **not** try to re-state `σ` at `D(f')`; instead derive the `e₂`
semilinearity at the *⊤-level* `σ` by transporting the `⊤` semilinearity along the restriction square
— `gammaPullbackImageIso_hom_naturality` (QuotScheme.lean:1833) is exactly the naturality that moves
`gammaPullbackImageIso` between `⊤` and `D(f')`, and the `A`-module structure on the `D(f')` target is
itself a `restrictScalars` of the `Γ(Spec R, j''ᵁ D(f'))` action. This is an assembly detail of the
transport, not a flaw in `σ`'s shape.
