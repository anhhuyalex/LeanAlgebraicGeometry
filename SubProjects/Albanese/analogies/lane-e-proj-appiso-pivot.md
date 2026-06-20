# Analogy: evaluating the inverse of a canonical iso between section presheaves

## Mode
cross-domain-inspiration

## Slug
lane-e-proj-appiso-pivot

## Iteration
195

## Structural problem (abstracted)

Given a canonical open immersion `f : Spec(R) ⟶ X` whose range is a fixed
open `U ⊂ X`, and given the induced section-level isomorphism
`α := f.appIso ⊤ : Γ(X, U) ≅ Γ(Spec R, ⊤)`, evaluate `α.inv : Γ(Spec R, ⊤) ⟶ Γ(X, U)`
on a specific element `x : R = Γ(Spec R, ⊤)` (here `R = Away 𝒜 f`, `X = Proj 𝒜`,
`U = D₊(f)`, `x = isLocElem`).

Equivalent abstracted shape: in any concrete category with a "global sections"
functor `Γ`, with a canonical iso `α : F(U) ≅ G(V)` between section objects on
two distinguished opens, compute the value of `α.inv` on a generator. Direct
chasing of the iso definition through the underlying construction fails when
the construction is itself a composition of named opaque pieces.

## Failed approaches (from directive)
- iter-188 → 191: direct `simp` + `rw` chains through
  `Proj.basicOpen_eq_basicOpenIso ▸ Proj.appIso_inv` — Lean term
  unification times out.
- iter-192: factored through a named helper
  `iotaGm_chart1_appIso_eval` — helper itself contains the same sorry.
- iter-193: re-routed through `IsOpenImmersion.lift_uniq` — outer
  morphism-level reasoning eliminated, but the inner `appTop`
  residual is the same `Proj.appIso ⊤ .inv` chase.
- iter-194: structurally isolated the residual to a single ring-map
  identity — still no closure on the `appIso` step.

## Analogues found

Ranked by porting cost (lowest first).

### Analogue: `AlgebraicGeometry.IsAffineOpen.fromSpec_app_self`

- **Mathlib citation**: `Mathlib/AlgebraicGeometry/AffineScheme.lean:560-564`
  (with `@[elementwise]` auto-generating `fromSpec_app_self_apply`).
  Companion lemmas at lines 481-489 (`fromSpec_app_of_le`) and
  554-558 (`ΓSpecIso_hom_fromSpec_app`).
- **Domain**: algebraic geometry — affine open theory in the SAME
  category (Scheme), but on the canonical `Spec(Γ(X, U)) ⟶ X` for any
  affine open `U`, NOT the `Proj`-specific `awayι`.
- **Same structural problem there**: for any scheme `X` and affine open
  `U ⊂ X` with `hU : IsAffineOpen U`, the canonical
  `hU.fromSpec : Spec Γ(X, U) ⟶ X` is `hU.isoSpec.inv ≫ U.ι`. Its
  section-level map on `U` is
  ```
  hU.fromSpec.app U = (Scheme.ΓSpecIso Γ(X, U)).inv ≫
                       (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op
  ```
  This **completely eliminates** the need to chase `appIso` through
  the open-immersion machinery: the canonical iso between sections
  on `U` and global sections of `Spec Γ(X, U)` is just `ΓSpecIso` modulo
  a presheaf-map adjustment.
- **Technique**:
  1. Mathlib does NOT chase `appIso_hom` / `appIso_inv` definitional
     unfoldings. Instead, it proves a **direct lemma** equating
     `fromSpec.app U` with `ΓSpecIso.inv ≫ presheaf.map(eqToHom)`.
  2. The proof of `fromSpec_app_self` is 3 lines: by
     `ΓSpecIso_hom_fromSpec_app` (which is itself 2 lines via
     `fromSpec_app_of_le`) and `Iso.inv_hom_id_assoc`.
  3. `fromSpec_app_of_le` (the load-bearing primitive) is proven by
     unfolding `fromSpec = isoSpec.inv ≫ ι`, applying `Hom.comp_app`
     and `Opens.ι_app`, then using the pre-built
     `isoSpec_inv_appTop` (line 461 — the explicit `appTop` formula
     for the canonical iso on an affine open).
  4. `@[elementwise]` then auto-generates `fromSpec_app_self_apply`
     (point-value form), making it directly usable in
     `IsLocalization.Away`-style chains.

- **Mapping to project**: `Proj.awayι 𝒜 f f_deg hm` is defined at
  `Mathlib/.../ProjectiveSpectrum/Basic.lean:189` as
  `basicOpenIsoSpec.inv ≫ (basicOpen 𝒜 f).ι` — **structurally identical**
  to `IsAffineOpen.fromSpec = isoSpec.inv ≫ U.ι`. The only difference is
  that `awayι` uses `basicOpenIsoSpec : (basicOpen 𝒜 f).toScheme ≅ Spec(Away 𝒜 f)`
  while `fromSpec` uses `hU.isoSpec : U.toScheme ≅ Spec Γ(X, U)`.
  These two isos are linked by `basicOpenIsoAway` (line 178):
  `(Away 𝒜 f) ≅ Γ(Proj 𝒜, basicOpen 𝒜 f)`. Concretely:
  ```
  basicOpenIsoSpec = hU.isoSpec ≪≫ (Scheme.Spec.mapIso basicOpenIsoAway.op).symm
  ```
  (where `hU = isAffineOpen_basicOpen 𝒜 f f_deg hm`, line 203). So the
  IDENTICAL theorem holds for `awayι`:
  ```
  Proj.awayι_app_basicOpen :
    (Proj.awayι 𝒜 f f_deg hm).app (Proj.basicOpen 𝒜 f) =
      (Proj.basicOpenIsoAway 𝒜 f f_deg hm).inv ≫
      (Scheme.ΓSpecIso _).inv ≫
      (Spec _).presheaf.map (eqToHom <proof_preimage>).op
  ```
  Then by `Scheme.Hom.appIso_hom` (Mathlib
  `OpenImmersion.lean:199`), combined with `opensRange_awayι`
  (`ProjectiveSpectrum/Basic.lean:199`):
  ```
  Proj.awayι_appIso_top :
    ((Proj.awayι 𝒜 f f_deg hm).appIso ⊤).hom =
      Proj.presheaf.mapIso(eqToIso opensRange_awayι).op.hom ≫
      basicOpenIsoAway.inv ≫
      ΓSpecIso.inv  -- (modulo a presheaf-map shuffle)
  ```
  Inverting gives `(appIso ⊤).inv = ΓSpecIso.hom ≫ basicOpenIsoAway.hom ≫ presheaf.map(eqToIso ...).inv`.
  Applied to `isLocElem` (the canonical generator of `Away 𝒜 f`
  typed as `Γ(Spec(Away 𝒜 f), ⊤)`):
  ```
  (Proj.awayι).appIso ⊤ .inv isLocElem =
    presheaf.map(eqToHom).op (basicOpenIsoAway.hom ((ΓSpecIso _).hom isLocElem))
  ```
  which is `[X_0/X_1] ∈ Γ(Proj 𝒜, basicOpen 𝒜 (X 1))` after evaluating
  `basicOpenIsoAway.hom = awayToSection 𝒜 f` (line 178; concrete
  ring-map formula at line 225's `awayMap_awayToSection`) and
  `ΓSpecIso.hom isLocElem = isLocElem`.

- **Porting cost**: **low**. Estimated **30-50 LOC, 1-2 iters**:
  - 5-10 LOC: `Proj.awayι_isoSpec_compat`: prove
    `basicOpenIsoSpec.hom = hU.isoSpec.hom ≫ Spec.map basicOpenIsoAway.hom`
    (where `hU = isAffineOpen_basicOpen`), via `basicOpenToSpec` and
    `awayToSection` definitions.
  - 10-15 LOC: `Proj.awayι_app_basicOpen` — mirror of
    `fromSpec_app_self`, by `comp_app` on
    `awayι = basicOpenIsoSpec.inv ≫ basicOpen.ι` then `basicOpenIsoSpec_hom` +
    `basicOpenToSpec_app_top` (already in Mathlib!).
  - 5-10 LOC: `Proj.awayι_appIso_top_inv_apply_isLocElem` — point-value
    on `isLocElem` after applying `Iso.eq_inv_apply` and `awayToSection_apply`.
  - 5 LOC: drop into `kbarChart1Ring_specMap_fac` to close the sorry.

- **Verdict**: **ANALOGUE_FOUND** — direct structural match within
  algebraic geometry. The Mathlib pattern is essentially the SAME
  theorem on a slightly different canonical iso, and the proof
  technique transports verbatim. **This is the strongest analogue** and
  the iter-196 plan agent should adopt it.

### Analogue: `AlgebraicGeometry.IsAffineOpen.app_basicOpen_eq_away_map`

- **Mathlib citation**: `Mathlib/AlgebraicGeometry/AffineScheme.lean:684-699`.
  Sibling: `appLE_eq_away_map` at lines 669-681.
- **Domain**: algebraic geometry — affine open / localization bridge.
- **Same structural problem there**: when **both** `U : Y.Opens` and
  `f ⁻¹ᵁ U` are affine, the section-level map of `f` on `basicOpen r`
  for `r : Γ(Y, U)` is **completely concrete**: it equals
  `IsLocalization.Away.map _ _ (f.app U).hom r`. This sidesteps `appIso`
  entirely by exhibiting the map as a `Localization.Away.map` whose
  evaluation on a generator is `IsLocalization.map_mk'`.
- **Technique**:
  1. Use `IsLocalization.ringHom_ext (Submonoid.powers r)` — the UMP of
     `Away r` — to reduce equality of two ring maps to equality on
     `algebraMap Y `(Y.basicOpen r)`-pre-images. This is the classical
     "to prove two maps out of a localization agree, check on the
     pre-localized ring" trick.
  2. After the extension reduction, both sides become equal by
     `Scheme.Hom.appLE_map` + `map_appLE` + `IsLocalization.map_comp`,
     all of which are already simp lemmas.
- **Mapping to project**: Apply with `Y = Proj 𝒜`, `U = ⊤`,
  `f = awayι 𝒜 f f_deg hm` (well, NO — `awayι` goes the wrong direction
  for this lemma; the codomain `Proj 𝒜` is not affine). However, the
  technique transports: the project should `apply IsLocalization.ringHom_ext`
  on `Submonoid.powers <X_0/X_1>` or `Submonoid.powers <suitable element>`
  in `Away 𝒜 X_1` to reduce the `appTop` equation to ring-map equality
  on the localized-from ring `MvPolynomial (Fin 2) kbar` (degree-zero
  homogeneous part). The pre-localized ring is the homogeneous
  localization `HomogeneousLocalization.NumDenSameDeg`, and the map
  reduces to checking on `X_0` and `X_1` images.
- **Porting cost**: **medium**. Estimated **40-70 LOC, 1-2 iters**.
  The downside: requires `IsLocalization.Away` instance on
  `HomogeneousLocalization.Away` (verified at line 317 of the project's
  current Proj usage chain). The upside: **fully eliminates** the
  `Proj.appIso` chase — the closing lemma is `IsLocalization.map_mk'` /
  `IsLocalization.lift_mk'`.
- **Verdict**: **ANALOGUE_FOUND** — alternative route via the
  `IsLocalization` UMP. Slightly heavier than analogue #1 but
  structurally clean. Use as **fallback** if analogue #1's
  `Proj.awayι_app_basicOpen` proof unexpectedly snags.

### Analogue: `CategoryTheory.Iso.eq_inv_apply` / `appIso_inv_app_apply`

- **Mathlib citation**: `Mathlib/CategoryTheory/Iso.lean` (multiple
  `Iso.eq_inv_comp`, `Iso.eq_comp_inv`, `Iso.inv_hom_id_apply`).
  Specifically for the project's setting:
  `Scheme.Hom.appIso_inv_app` at
  `Mathlib/AlgebraicGeometry/OpenImmersion.lean:224` (with
  `@[elementwise nosimp]`), and `Scheme.Hom.app_appIso_inv` at line
  210. Both pin `appIso.inv` to `f.app` via composition.
- **Domain**: category theory — universal "swap to forward direction"
  technique.
- **Same structural problem there**: for any iso `α : X ≅ Y` and
  elements `x : X`, `y : Y`, `α.inv y = x ↔ α.hom x = y`. To compute
  `α.inv` on a specific `y`, instead **guess** the image `x` and
  prove the forward statement `α.hom x = y`, which is structurally
  more tractable because `α.hom` is often the "natural" direction.
- **Technique**: rewrite `(awayι).appIso ⊤ .inv isLocElem = ???` as
  `(awayι).appIso ⊤ .hom ??? = isLocElem` (via `Iso.eq_inv_apply` or
  `Iso.symm_apply_eq` — there are concrete category-theoretic
  formulations available). Then use `appIso_hom` (line 199 of
  `OpenImmersion.lean`):
  ```
  (f.appIso U).hom = f.app (f ''ᵁ U) ≫ X.presheaf.map (eqToHom ...).op
  ```
  to reduce the forward statement to a `f.app` evaluation on
  `f ''ᵁ ⊤ = opensRange = basicOpen 𝒜 f`. Combined with
  `basicOpenToSpec_app_top` (`ProjectiveSpectrum/Basic.lean:143`) and
  `basicOpenIsoSpec_hom`:
  ```
  (basicOpenToSpec).app ⊤ = (Scheme.ΓSpecIso _).hom ≫ awayToSection 𝒜 f ≫
                              (basicOpen 𝒜 f).topIso.inv
  ```
  this gives an explicit forward-direction formula.
- **Mapping to project**: Already partially in the project's recipe (iter-189
  analogies file). The missing step is **commit to the forward direction**:
  guess that `(awayι).appIso ⊤ .inv isLocElem = basicOpenIsoAway.hom (mk [X_0/X_1])`
  and prove the forward equation via `appIso_hom` + `basicOpenToSpec_app_top`.
  The forward direction has a clean Mathlib chain because all the named
  components compose explicitly.
- **Porting cost**: **low-to-medium**. Estimated **20-40 LOC, 1 iter**.
  This is the most direct surgical route but requires the prover to
  commit to the guessed image upfront (which the project's blueprint
  has documented from iter-188 onward: `isLocElem ↦ [X_0/X_1]`).
- **Verdict**: **ANALOGUE_FOUND** — the universal "flip and verify
  forward" trick, applied with the right Mathlib forward-direction
  primitive (`basicOpenToSpec_app_top`). **Most surgical** route if
  the prover wants minimal new infrastructure.

### Analogue: `AlgebraicGeometry.ΓSpec.adjunction.unit.app` and `ΓSpecIso_inv_ΓSpec_adjunction_homEquiv`

- **Mathlib citation**: `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`
  (look for `identityToΓSpec`, `ΓSpec.adjunction`,
  `ΓSpecIso_inv_ΓSpec_adjunction_homEquiv`). Especially the
  `adjunction_unit_app_app_top`-style lemmas.
- **Domain**: algebraic geometry / category theory — adjunction unit
  evaluation.
- **Same structural problem there**: the `Γ ⊣ Spec` adjunction has
  unit `X ⟶ Spec(Γ(X, ⊤))`. Evaluating its `app ⊤` on a global section
  reduces to the `ΓSpecIso` identification, NOT to chasing the unit
  through the adjunction construction. The pattern: "characterize the
  morphism by its action on sections via the adjunction-homEquiv, and
  read off the inverse by applying `Iso.eq_inv_comp`".
- **Technique**: Use `ΓSpec.adjunction.homEquiv` to translate
  "morphisms `X ⟶ Spec(R)`" into "ring maps `R → Γ(X, ⊤)`", then read
  off the value on a generator. For the project, the structurally
  identical step is **already encoded** in `Proj.awayι`'s definitional
  unfolding through `basicOpenToSpec` and `awayToSection`.
- **Mapping to project**: The technique would say: instead of evaluating
  `(awayι).appIso ⊤ .inv isLocElem` directly, evaluate the global-section
  map `(awayι).appTop : Γ(Proj 𝒜, ⊤) ⟶ Γ(Spec(Away 𝒜 f), ⊤)` on the
  image of `isLocElem` via the natural `Γ(Spec)` ↔ `Away 𝒜 f`
  identification.
- **Porting cost**: **medium**. The `ΓSpec.adjunction` direction is
  axiom-clean but harder to compose with the project's existing
  `Proj.fromOfGlobalSections` machinery. Estimated **50-80 LOC** —
  more than analogue #1 because it requires touching the adjunction layer.
- **Verdict**: **PARTIAL_ANALOGUE** — useful as a conceptual
  cross-check but not the cheapest port. The direct analogue #1 wins.

### Analogue: `InnerProductSpace.toDual` and `Riesz.symm_apply` (functional analysis)

- **Mathlib citation**: `Mathlib/Analysis/InnerProductSpace/Dual.lean`.
- **Domain**: functional analysis — Riesz representation theorem.
- **Same structural problem there**: the canonical iso
  `H ≅ H*` between a Hilbert space and its dual is implemented as
  `InnerProductSpace.toDual`. Its inverse `toDual.symm : H* → H` is
  evaluated on a functional `φ` by **characterizing the image** as
  the unique `x : H` with `⟨x, ·⟩ = φ`, **not** by chasing the iso
  definition. Specifically, lemmas like `InnerProductSpace.toDual_apply`
  give the forward formula; the inverse is evaluated via
  `InnerProductSpace.toDual_symm_apply` which says the inverse is the
  Riesz representative.
- **Technique**: characterize the inverse iso's image on each element
  via a UMP (uniqueness of the Riesz representative), then prove the
  characterization holds by checking the forward equation. Same
  underlying technique as analogue #3.
- **Mapping to project**: The "UMP characterization" for
  `(awayι).appIso ⊤ .inv isLocElem` is "the unique element
  `g ∈ Γ(Proj 𝒜, basicOpen 𝒜 f)` such that
  `awayToSection 𝒜 f (X_0/X_1) = g` after the `ΓSpecIso` shuffle". The
  uniqueness comes from `basicOpenIsoAway` being an iso. The forward
  check is `basicOpenIsoAway.hom (mk [X_0/X_1]) = ???` which is a
  closed-form computation.
- **Porting cost**: **medium-high**. The Riesz technique is
  structurally clear but requires building the `basicOpenIsoAway`
  uniqueness API explicitly. **Slower than analogue #1 or #3**.
- **Verdict**: **PARTIAL_ANALOGUE** — same underlying "characterize by
  UMP" technique as analogue #3 but expressed in functional-analytic
  vocabulary. Useful as **conceptual reassurance** that this is a
  standard technique across mathematical domains, not a low-cost
  port. Skip in favor of analogues #1 and #3.

### Analogue: `IsLocalization.algEquiv.symm_apply` (commutative algebra)

- **Mathlib citation**: `Mathlib/RingTheory/Localization/Basic.lean`,
  specifically `IsLocalization.algEquiv` and `IsLocalization.lift_mk'`,
  `IsLocalization.map_mk'`.
- **Domain**: commutative algebra — localization as a UMP.
- **Same structural problem there**: the canonical iso
  `IsLocalization.algEquiv : Localization.Away f ≃ₐ[R] S` between two
  localizations is **never** evaluated by chasing its definition.
  Mathlib's approach: use `IsLocalization.ringHom_ext` (uniqueness of
  ring maps out of a localization) to reduce `algEquiv.symm`'s action
  on an element to its action on the underlying ring's image.
- **Technique**: `IsLocalization.ringHom_ext (M : Submonoid R)` says
  two ring maps `S →+* T` (with `[IsLocalization M S]`) agree iff they
  agree after `algebraMap R S`. Applied to inverse evaluation: to
  prove `α.symm (loc_elem) = x`, it suffices to prove `α x = loc_elem`,
  reduced further to checking on the pre-localized ring `R`.
- **Mapping to project**: Apply with `M = Submonoid.powers (X_1)` in
  the graded ring `MvPolynomial (Fin 2) kbar`. The pre-localized ring
  is the degree-zero homogeneous part `(MvPoly)_0` (which equals
  `kbar` in this graded ring). The localization is
  `HomogeneousLocalization.Away 𝒜 X_1`. **The chain** to prove
  `(awayι).appIso ⊤ .inv isLocElem = [X_0/X_1]` reduces to checking on
  the `algebraMap kbar → HomogeneousLocalization.Away 𝒜 X_1`-image, where
  both sides are trivial (image of any element of `kbar` is constant).
- **Porting cost**: **medium**. Requires identifying
  `HomogeneousLocalization.Away 𝒜 X_1` as a localization at
  `X_0/X_1` (in the graded sense), which is already documented in
  the project at `homogeneousLocalizationAwayIso`.
- **Verdict**: **PARTIAL_ANALOGUE** — the UMP technique transports,
  but the bookkeeping is fiddly because `HomogeneousLocalization`
  uses `NumDenSameDeg` rather than `Submonoid.powers`. Worth a look
  if analogues #1 and #3 both fail; not the first choice.

## Top suggestion

**Use analogue #1 (`IsAffineOpen.fromSpec_app_self`) as the iter-196
route-pivot.** Concretely, the plan agent should objective-out a single
helper lemma:

```lean
lemma Proj.awayι_app_basicOpen
    {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.awayι 𝒜 f f_deg hm).app (Proj.basicOpen 𝒜 f) =
      (Proj.basicOpenIsoAway 𝒜 f f_deg hm).inv ≫
      (Scheme.ΓSpecIso _).inv ≫
      (Spec _).presheaf.map (eqToHom (by simp [opensRange_awayι])).op
```

**Proof sketch** (port of `fromSpec_app_self` proof at
`Mathlib/AlgebraicGeometry/AffineScheme.lean:561-564`):

1. Unfold `awayι = basicOpenIsoSpec.inv ≫ basicOpen.ι`. Apply
   `Scheme.Hom.comp_app` to split into
   `(basicOpen.ι).app(basicOpen 𝒜 f) ≫ basicOpenIsoSpec.inv.app(basicOpen.ι ⁻¹ᵁ basicOpen 𝒜 f)`.
2. `basicOpen.ι ⁻¹ᵁ basicOpen 𝒜 f = ⊤` (because `basicOpen.ι` is the open
   embedding of `basicOpen 𝒜 f` into `Proj 𝒜` — preimage of itself is the
   whole subscheme), so `(basicOpen.ι).app(basicOpen 𝒜 f) = (Proj 𝒜).presheaf.map (eqToHom).op`.
3. `basicOpenIsoSpec.inv.app ⊤ = inv(basicOpenIsoSpec.hom.app ⊤) = inv(basicOpenToSpec.app ⊤)`
   by `basicOpenIsoSpec_hom`. Then `basicOpenToSpec_app_top` (Mathlib
   `ProjectiveSpectrum/Basic.lean:143`) gives the explicit formula:
   `(basicOpenToSpec).app ⊤ = ΓSpecIso.hom ≫ awayToSection 𝒜 f ≫ (basicOpen 𝒜 f).topIso.inv`.
4. Invert that and combine — exactly mirrors `fromSpec_app_of_le` →
   `fromSpec_app_self`.

Then via `Scheme.Hom.appIso_hom`
(`Mathlib/AlgebraicGeometry/OpenImmersion.lean:199`) applied to
`f = awayι 𝒜 f` and `U = ⊤`:

```lean
((Proj.awayι 𝒜 f f_deg hm).appIso ⊤).hom =
  (Proj.awayι _ _ _ _).app (basicOpen 𝒜 f) ≫
  (Spec _).presheaf.map (eqToHom (by simp)).op
```

Substituting `Proj.awayι_app_basicOpen` and simplifying gives a clean
form. Inverting and applying `Iso.eq_inv_apply` reduces `kbarChart1Ring_specMap_fac`'s
residual sorry to the forward-direction equation
`basicOpenIsoAway.hom (mk_isLocElem) = (awayι).app(basicOpen 𝒜 f) (isLocElem)`,
which evaluates by `awayToSection_apply`
(`ProjectiveSpectrum/Scheme.lean`, see `lean_leansearch` hit) — closed-form
on `IsLocalization.map _ HomogeneousLocalization.val`.

**First project file to touch**: `AlgebraicJacobian/AbelianVarietyRigidity.lean`,
adding `Proj.awayι_app_basicOpen` (and the consumer corollary
`Proj.awayι_appIso_top_inv_apply`) above `kbarChart1Ring_specMap_fac`
(line 222), then closing both sorries at lines 273 and 481 via the new
helper. **First Mathlib file to read**:
`Mathlib/AlgebraicGeometry/AffineScheme.lean:481-565` (the
`fromSpec_app_of_le` → `fromSpec_app_self` → `@[elementwise]` chain) as
the proof-shape template, paired with
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:143-185` (the
`basicOpenToSpec_app_top` → `basicOpenIsoSpec` → `basicOpenIsoAway`
chain) as the substrate to glue together.

## Discarded
- `LocallyRingedSpace.Hom.appIso` (directive's hint #1): the LRS-level
  `appIso` is **upstream** of `Scheme.Hom.appIso` — it's the underlying
  construction that the project's failed iter-188/191 chases ARE chasing.
  Porting back to LRS makes the problem strictly harder, not easier.
- `Scheme.Spec.appIso` (directive hint #3): no direct
  `Spec.appIso`-specific evaluation lemma exists in Mathlib beyond the
  `ΓSpecIso` identification, which IS what analogue #1 already uses.
- `SheafCondition.equalizer` (directive hint #5): sheaf-condition
  equalizers help proving sheaves are sheaves, not evaluating canonical
  isos between sections. Wrong-shape analogue.
- `RingedSpace.PresheafedSpace.Hom.app` (directive hint #4): same
  failure mode as the `LocallyRingedSpace` direction — upstream of
  `Scheme.Hom.app`, makes the problem harder.
- `Knaster–Tarski` / order-theoretic fixed points: structurally the
  wrong shape (the project's problem is not a fixed-point problem).
- `OrderIso.symm_apply_eq` / `Equiv.symm_apply_eq`: subsumed by
  analogue #3 (`Iso.eq_inv_apply`), which is the categorical
  generalization.
