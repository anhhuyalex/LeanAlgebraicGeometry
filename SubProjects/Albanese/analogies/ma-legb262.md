# Analogy: leg-B unit ring-iso swap (`inv (ε (restrictScalars β_W))`) — CommRing recovery + `𝟙_` section defeq

## Mode
api-alignment

## Slug
ma-legb262

## Iteration
262

## Question
For `sliceDualTransport`'s leg-B (the codomain unit ring-iso swap, intended term
`inv (ε (ModuleCat.restrictScalars φ.hom))`): (a) what is the Mathlib idiom for recovering
`CommRing` on a section ring viewed through `forget₂ CommRingCat RingCat`; and (b) what is the
idiom for bridging `𝟙_ (ModuleCat S)` to the project's defeq presheaf-section spellings of the
same unit?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate/DualInverse.lean:184-317` — `sliceDualTransport`,
  the `codomainMap` typed hole at L305.
- `AlgebraicJacobian/Picard/TensorObjSubstrate/PresheafInternalHom.lean:174-216` —
  `restrictScalars_isIso_ε` / `restrictScalars_isIso_ε_of_bijective` (`[CommRing R][CommRing S]`).
- `PresheafInternalHom.lean:658-674` — `restr` / `internalHomObjModule` (the section spellings).

## Decisions identified

### Decision: how to obtain `CommRing` / apply the ε-iso lemma at the section ring (friction a)

- **Mathlib idiom**: there is **no** instance that finds `CommRing` on a `forget₂ CommRingCat
  RingCat`-image carrier, and Mathlib does not want one — the idiom is to keep the object a
  `CommRingCat` (so its `CommRing` instance is the canonical one) and only forget to `RingCat`
  at the very last step. The relevant Mathlib facts: `ModuleCat.restrictScalars_η`
  (`Mathlib/.../ModuleCat/ChangeOfRings.lean`, the underlying map of `ε` is the ring map) and
  `CategoryTheory.ConcreteCategory.bijective_of_isIso` (an iso's underlying map is bijective).
- **Verified by `lean_run_code`**:
  - `infer_instance : CommRing ↑(X.ringCatSheaf.obj.obj W)` **FAILS**; so does
    `CommRing ↑((forget₂ CommRingCat RingCat).obj A)` for `A : CommRingCat`.
  - `change CommRing ↑(X.presheaf.obj W); infer_instance` **succeeds** (canonicalize to the
    `CommRingCat` carrier).
  - `((forget₂ CommRingCat RingCat).map g).hom = g.hom` is **`rfl`**, and
    `ModuleCat.restrictScalars ((forget₂ …).map g).hom = ModuleCat.restrictScalars g.hom` is
    **`rfl`**.  Since `β = whiskerRight α (forget₂ …)` with
    `α.app U = (f.appIso U.unop).inv` a **`CommRingCat`** morphism, `β.app U`'s restrictScalars
    is `rfl`-equal to `ModuleCat.restrictScalars (f.appIso W').inv.hom`.
  - `IsIso (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.inv.hom))` for a `CommRingCat`
    iso `e : A ≅ B` is provable verbatim by the `restrictScalars_isIso_ε` recipe
    (`bijective_of_isIso` → `RingEquiv.ofBijective` → `restrictScalars_η` → `RingEquiv.bijective`),
    with `CommRing ↑A`, `CommRing ↑B` found **natively** (A, B are `CommRingCat`).
- **Project's current path**: feed `β.app (op W')` (a `forget₂`'d `RingCat` hom) to
  `restrictScalars_isIso_ε_of_bijective`, which then fails to synthesize `CommRing` on the
  `RingCat`-carrier spelling.
- **Gap**: divergent-with-cost (the friction is self-inflicted by forgetting to `RingCat` too
  early; no parallel API is needed).
- **Cost of divergence**: a hand-rolled "recover `CommRing` on a `forget₂` image" lemma would be
  a parallel API for something Mathlib deliberately routes around. The project already has the
  right lemma (`restrictScalars_isIso_ε_of_bijective`); it just must be applied to the
  `CommRingCat`-level hom.
- **Verdict**: ALIGN_WITH_MATHLIB (use the `CommRingCat` iso; do **not** build a CommRing-recovery
  helper).

### Decision: bridging `𝟙_ (ModuleCat S)` to the `restr`/`𝟙_X`-section unit spellings (friction b)

- **Mathlib idiom**: there is **no** dedicated coherence lemma, and none is needed — the spellings
  are **definitionally equal**. The idiom is `show`/`change` to the canonical
  `𝟙_ (ModuleCat ↑(R.obj U))` form (carrier written as the **`CommRingCat`** section `↑(R.obj U)`),
  then `exact`.
- **Verified by `lean_run_code`**:
  - `(𝟙_ (PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))).obj U = 𝟙_ (ModuleCat ↑(R.obj U))`
    is **`rfl`**. (`restr U N`'s section at a slice object `W` is `N.obj (op W.left)` by
    `pushforward₀`'s `.obj` reduction, so a `restr`/`𝟙_X`-section of the unit is just `𝟙_X`
    evaluated, hence the same `rfl`.)
  - `inv (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.inv.hom))` typechecks with endpoints
    `(restrictScalars e.inv.hom).obj (𝟙_ (ModuleCat ↑A)) ⟶ 𝟙_ (ModuleCat ↑B)` — exactly the
    canonical unit forms, so it unifies with the goal after canonicalization.
- **GOTCHA (verified)**: `MonoidalCategoryStruct (ModuleCat ↑((R ⋙ forget₂ …).obj U))` **FAILS**
  to synthesize even though plain `CommRing ↑((R ⋙ forget₂ …).obj U)` succeeds. So the unit must
  be written with the `↑(R.obj U)` (CommRingCat) carrier — at the `forget₂`-composite carrier the
  `𝟙_` notation itself cannot elaborate. `change`/`show` to `↑(R.obj U)` first.
- **Gap**: identical-up-to-defeq (no Mathlib lemma exists or is needed).
- **Verdict**: PROCEED (defeq via `show`/`change`; no transport lemma).

### Decision: should the ε-iso-of-ring-equiv lemma come from Mathlib? (completeness)

- **Mathlib idiom**: Mathlib ships `ModuleCat.restrictScalars_η` and
  `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` (a `ModuleCat S ≌ ModuleCat R` for a ring
  equiv — a *categorical* equivalence, **not** the monoidal-unit `ε` iso). There is **no**
  `IsIso (ε (restrictScalars e))` / strong-monoidal-of-ring-equiv lemma in Mathlib.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL — already correctly filled by the project's
  `restrictScalars_isIso_ε` / `_of_bijective`. No new build required.

## Recommendation
Phrase leg-B at the **`CommRingCat`** level, never recovering `CommRing` on the `RingCat`
spelling. Concretely in `sliceDualTransport`: reconstruct the `CommRingCat` natural transformation
`α` (or use `f.appIso W'` directly); set `g := (f.appIso W').inv.hom` (equivalently `(α.app
(op W')).hom`); obtain `hbij := ConcreteCategory.bijective_of_isIso (f.appIso W').inv`; supply
`haveI := restrictScalars_isIso_ε_of_bijective g hbij` (CommRing on the `CommRingCat` carriers is
native); take `codomainMap := CategoryTheory.inv (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars
g))`. Because `ModuleCat.restrictScalars (β.app _).hom = ModuleCat.restrictScalars g` is `rfl`, the
domain matches the leg-A composite. Finally `show`/`change` the goal's unit endpoints into
`(restrictScalars g).obj (𝟙_ (ModuleCat ↑(X.presheaf.obj (op fW')))) ⟶ 𝟙_ (ModuleCat ↑(Y.presheaf.obj
(op W')))` (canonical `↑(R.obj U)` carriers — the `forget₂`-composite carrier breaks the
`MonoidalCategoryStruct` synthesis) and `exact codomainMap`. No CommRing-recovery helper and no
unit-transport lemma should be written — both would be parallel APIs for what is already `rfl`.
