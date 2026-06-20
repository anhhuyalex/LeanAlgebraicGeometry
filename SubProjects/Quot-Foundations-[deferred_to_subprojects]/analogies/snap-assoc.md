# Analogy: monoidal structure / associator on `SheafOfModules R` via sheafification

## Mode
cross-domain-inspiration

## Slug
snap-assoc

## Iteration
048

## Structural problem (abstracted)
`C` monoidal, `W ⊆ Mor C` a class of weak equivalences, `L : C ⥤ D` the
reflective localization at `W` (left adjoint to a fully faithful inclusion).
We want a monoidal structure on `D` (in particular an associator) descended
from `C`. This is the strong-monoidality comparison `L P ⊗ L Q ≅ L(P ⊗ Q)`,
equivalently `IsIso (L.map (η_P ▷ Q))` for the localization unit `η`.
Here `C = PresheafOfModules R₀`, `D = SheafOfModules R`, `L = sheafification`.

## Failed approaches (from directive)
- Stalkwise/locally-bijective ⟹ IsIso applied to `η_P ⊗ 𝟙_Q`: tensor only
  right-exact, so `η_P ⊗ 𝟙` is not locally injective. (Correct diagnosis — see
  why this is the wrong object to test below.)
- Direct `MonoidalCategory (SheafOfModules R)` instance: absent in pinned Mathlib.
- `Localization.Monoidal` exists but not instantiated for module sheafification.

## Key Mathlib facts established this iter
- **`PresheafOfModules.sheafification α` IS a localization functor**:
  `(sheafification α).IsLocalization (J.W.inverseImage (toPresheaf R₀))`
  — `Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean:48`.
  So the `L.IsLocalization W` prerequisite of `LocalizedMonoidal` is already met,
  with `W = J.W.inverseImage (toPresheaf R₀)`.
- `PresheafOfModules (R ⋙ forget₂)` is monoidal (needs `R : Cᵒᵖ ⥤ CommRingCat`):
  `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` (tensor = objectwise
  `M₁.obj X ⊗_{R(X)} M₂.obj X`).
- **Absent in Mathlib** (the real gaps): `MonoidalClosed (PresheafOfModules R)`;
  `(J.W.inverseImage (toPresheaf R₀)).IsMonoidal`; any `MonoidalCategory (SheafOfModules R)`
  or `LocalizedMonoidal` instance for modules; stalk infrastructure for module sheaves.

## Analogues found (ranked by porting cost, lowest first)

### Analogue 1: `CategoryTheory.Sites.Monoidal` + `CategoryTheory.Localization.Monoidal.Basic`
- **Domain**: category theory / sheaf theory (the direct template — Joël Riou).
- **Same problem there**: `MonoidalCategory (Sheaf J A)` for a *fixed* monoidal
  target `A`, built as `LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)`
  — `Sites/Monoidal.lean:165` (`Sheaf.monoidalCategory`). The `LocalizedMonoidal`
  machinery (`Localization/Monoidal/Basic.lean:86`) needs only: `MonoidalCategory C`,
  `L.IsLocalization W`, `W.IsMonoidal`, a unit iso `ε`. The associator/unitors/braiding
  all come from the localization-of-trifunctors machinery for free.
- **Technique**: the *sole* obligation `J.W.IsMonoidal` (whiskering preserves weak
  equivalences) is discharged in `GrothendieckTopology.W.monoidal` (`Sites/Monoidal.lean:149`)
  via `W.whiskerLeft` (`:132`): `g ∈ W ⟺ ∀ sheaf H, Hom(-,H)` bijective; to show
  `F ◁ g ∈ W`, transport across the **tensor–hom adjunction** `Hom(F⊗Gᵢ,H) ≅ Hom(Gᵢ,[F,H])`
  using that **the internal hom `[F,H]` is itself a sheaf** (`isSheaf_functorEnrichedHom`,
  `:102`). `whiskerRight` is derived from `whiskerLeft` by the braiding (`:144`).
  NOT a stalk argument — no exactness ever invoked.
- **Mapping to project**: instantiate `LocalizedMonoidal` with `L = PresheafOfModules.sheafification α`,
  `W = J.W.inverseImage (toPresheaf R₀)` (already `IsLocalization`, Localization.lean:48),
  `ε : sheafification(𝟙) ≅ unitModule`. Then `MonoidalCategory (SheafOfModules R)` and the
  associator drop out. Sole obligation: `(J.W.inverseImage (toPresheaf R₀)).IsMonoidal`.
- **Why it is NOT free**: the generic "inverse image under a *monoidal* functor of a
  monoidal `W` is monoidal" instance (`Localization/Monoidal/Basic.lean:71`) does NOT
  apply, because `toPresheaf : PresheafOfModules R₀ ⥤ (Cᵒᵖ ⥤ AddCommGrp)` is NOT strong
  monoidal (module tensor `⊗_{R₀}` ≠ underlying abelian tensor `⊗_ℤ`). So `W.IsMonoidal`
  cannot be reduced to the (already proven) abelian `J.W.IsMonoidal`. It must be proven at
  the module level — by the closed lever (Analogue 2) or stalks (which need absent infra).
- **Porting cost**: medium-high. The `LocalizedMonoidal` wiring is short; the cost is
  entirely in `W.IsMonoidal`, which routes through Analogue 2.
- **Verdict**: ANALOGUE_FOUND.

### Analogue 2: `CategoryTheory.Monoidal.Reflective.isIso_tfae` (Day's reflection theorem)
- **Domain**: category theory (reflective subcategories / closed monoidal).
- **Same problem there**: `D` symmetric monoidal closed, `C ↪ D` reflective with
  reflector `L`. `Monoidal/Braided/Reflection.lean:92` proves TFAE:
  (1) `∀ c d, IsIso (η.app ((ihom d).obj (R.obj c)))`,
  (2) `∀ c d, IsIso ((pre (η.app d)).app (R.obj c))`,
  (3) `∀ d d', IsIso (L.map (η.app d ▷ d'))`,
  (4) `∀ d d', IsIso (L.map (η.app d ⊗ₘ η.app d'))`.
  Condition (4) is EXACTLY the strong-monoidal comparison; (3) is exactly the
  directive's `L.map (η_P ▷ Q)`. And `Reflection.lean:242` gives `monoidalClosed C`
  (the reflective subcategory is itself closed monoidal).
- **Technique**: condition (1) — **"the internal hom into a local (sheaf) object is
  itself local (a sheaf)"** — is the cheap-to-verify end of the TFAE and implies (3)/(4).
  This is the abstract form of `isSheaf_functorEnrichedHom`. The proof builds an explicit
  retraction of the unit (`adjRetraction`, `:53`) from the tensor-hom data.
- **Mapping to project**: `D = PresheafOfModules R` (must be `SymmetricCategory` —
  true over a sheaf of *commutative* rings — and `MonoidalClosed` — ABSENT), `C =
  SheafOfModules R`, reflective adjunction = `sheafificationAdjunction` (have it). Verify
  condition (1): internal hom of presheaves-of-modules `[F,Q]` is a sheaf when `Q` is.
  Then (3)/(4) give the strong-monoidal comparison, discharging `W.IsMonoidal` of Analogue 1,
  AND `monoidalClosed (SheafOfModules R)` for free.
- **Porting cost**: high. Prerequisite = build `MonoidalClosed (PresheafOfModules R)`
  (internal hom of module presheaves; Mathlib has `Monoidal.Closed.FunctorCategory.Basic`
  and `ModuleCat.Monoidal.Closed` to assemble from, but PresheafOfModules carries
  restriction-of-scalars in its transition maps, so it is not a plain functor category) +
  prove `[F,Q]` preserves the sheaf condition.
- **Verdict**: ANALOGUE_FOUND (the robust, site-general route; subsumes Analogue 1's gap).

### Analogue 3: doctrinal adjunction + base-change strong monoidality
- **Citations**: `CategoryTheory.Adjunction.rightAdjointLaxMonoidal` /
  `leftAdjointOplaxMonoidal`; `ModuleCat` `(extendScalars f).Monoidal`
  (`Algebra/Category/ModuleCat/Monoidal/Adjunction.lean:42`) and the induced
  `(restrictScalars f).LaxMonoidal` (`:102`).
- **Domain**: commutative algebra (the algebraic shadow of sheafification-tensor).
- **Same problem there**: extension of scalars `S ⊗_R - : ModuleCat R ⥤ ModuleCat S`
  (a base-change "localization-flavored" left adjoint) is STRONG monoidal — `μ` is the
  canonical projection-formula iso `S⊗_R(M⊗_R N) ≅ (S⊗M)⊗_S(S⊗N)`, packaged via
  `Functor.CoreMonoidal.toMonoidal`. Its right adjoint `restrictScalars` is then
  automatically LAX monoidal by `Adjunction.rightAdjointLaxMonoidal`.
- **Technique**: (a) `CoreMonoidal` — build `μ`/`ε` from the one canonical comparison iso
  and let the machinery supply coherence; (b) doctrinal adjunction — a right adjoint of a
  (op/strong) monoidal functor is lax monoidal for free.
- **Mapping to project**: two uses. (i) The lax-monoidal **global sections Γ** of the
  section graded ring (`Γ(F)⊗Γ(G)→Γ(F⊗G)`) is exactly `rightAdjointLaxMonoidal`/structure
  map — get it for free once `SheafOfModules` is monoidal and `Γ` is a right adjoint.
  (ii) `CoreMonoidal` is the build pattern for the bespoke line-bundle comparison (Analogue 4):
  supply the single iso `μ_{m,m'}`, derive coherence.
- **Porting cost**: low-medium (these are immediate once a monoidal structure exists;
  primarily a pattern to reuse, not the crux).
- **Verdict**: PARTIAL_ANALOGUE (technique/pattern, not the crux).

### Analogue 4: bespoke tensor-power comparison on line bundles (NO full MonoidalCategory)
- **Domain**: assembled technique (locally-free modules + `mapIso` + `CoreMonoidal` pattern).
- **Same problem there**: the project's ACTUAL `snap-assoc` need is associativity of the
  section graded ring `⊕_m Γ(X, L^{⊗m})`, which needs `tensorPowAdd : L^{⊗m} ⊗ L^{⊗m'} ≅
  L^{⊗(m+m')}` and its pentagon/associativity — i.e. the associator only on tensor POWERS
  of an invertible/line bundle `L`, NOT on all of `SheafOfModules R`.
- **Technique**: for *locally free* factors the strong-monoidal comparison
  `L(P)⊗L(Q) ≅ L(P⊗Q)` is an iso for trivial reasons — locally `O⊗O = O`, so the presheaf
  tensor is already locally a free module and its sheafification unit is locally the
  identity; right-exactness is never invoked (this is exactly why failed-approach #1's
  obstruction evaporates: the bad object `η_P⊗𝟙` is never the thing tested — on locally
  free pieces the comparison is a genuine local iso). Build `μ_{m,m'}` by induction on
  tensor powers from the right-unitor + one comparison iso; prove associativity as a `μ`
  cocycle (pentagon) directly.
- **Mapping to project**: extend `SectionGradedRing.lean` (already has `tensorObj`,
  `tensorPow`, `unitModule`, unitor, braiding via `mapIso`) with `μ_{m,m'}` and a pentagon
  lemma, restricted to invertible `L`. Avoids `MonoidalCategory (SheafOfModules R)` and
  `MonoidalClosed` entirely.
- **Porting cost**: lowest. Self-contained in the project file; does not generalize.
- **Verdict**: ANALOGUE_FOUND (pragmatic unblock for snap-assoc specifically).

## Top suggestion
Two-track. **To unblock `snap-assoc` cheaply now**: Analogue 4 — build the tensor-power
comparison family `μ_{m,m'} : L^{⊗m} ⊗ L^{⊗m'} ≅ L^{⊗(m+m')}` by induction in
`AlgebraicJacobian/Picard/SectionGradedRing.lean`, using locally-free-ness so the
strong-monoidal comparison is a local iso (right-exactness never invoked), and prove the
pentagon as a cocycle. **For the principled full structure**: Analogue 1 — instantiate
`LocalizedMonoidal (L := PresheafOfModules.sheafification α) (W := J.W.inverseImage
(toPresheaf R₀)) ε` (read `Mathlib/CategoryTheory/Sites/Monoidal.lean` and
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean:48`); its sole obligation
`(J.W.inverseImage (toPresheaf R₀)).IsMonoidal` is discharged via Analogue 2 (Day's
`isIso_tfae` condition (1): internal hom of module-presheaves into a sheaf is a sheaf),
which additionally yields `MonoidalClosed (SheafOfModules R)`. The single genuinely missing
Mathlib brick for the principled route is `MonoidalClosed (PresheafOfModules R)`
(+ internal-hom-preserves-sheaf) — that is the `NEEDS_MATHLIB_GAP_FILL` core.

## Discarded
- Generic monoidal-functor inverse-image instance (`Localization/Monoidal/Basic.lean:71`):
  inapplicable — `toPresheaf` is not strong monoidal (`⊗_{R₀} ≠ ⊗_ℤ`).
- Objectwise/locally-bijective `W.IsMonoidal`: matches failed-approach #1 — tensor only
  right-exact, local injectivity of `X◁g` fails.
- Pure stalk route (`isIso_iff_stalkFunctor_map_iso`, `Topology/Sheaves/Stalks.lean:652`):
  would work on a space (`g∈W ⟺ stalkwise iso`; `(F◁g)_x = id⊗g_x` iso since `F_x⊗-`
  preserves the iso `g_x`, no exactness), but stalk-of-tensor and stalk infra for sheaves
  of modules are ABSENT in Mathlib — building them ≳ the closed-lever route.
