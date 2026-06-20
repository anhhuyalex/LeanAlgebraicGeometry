# Analogy: does Mathlib supply a monoidal `SheafOfModules` / monoidal sheafification — and the flatness-free, MonoidalClosed-free route the prior 8 iters missed

## Mode
api-alignment

## Slug
ts-monoidal213

## Iteration
213

## Question
(1) Does Mathlib provide `MonoidalCategory (SheafOfModules R)` (or `Sheaf J (ModuleCat …)`)?
(2) Is `PresheafOfModules.sheafification` a (lax/strong) monoidal functor, or is there
a reflective-localization monoidal transport (`Localization.Monoidal`,
`MorphismProperty.IsMonoidal`) giving the associator for free? (3) If neither, the minimal
correct route to `Nonempty ((M⊗N)⊗P ≅ M⊗(N⊗P))` for invertible objects — does it require
EITHER (a) sectionwise flatness `[∀ U, Module.Flat (𝒪_X(U)) (M.val(U))]` (FALSE for
non-affine opens) OR (b) the abandoned `tensorObj_restrict_iso`? If a route needs NEITHER,
name it precisely.

## Headline
**This REVERSES the prior (iters 206–212) conclusion that the associator is walled behind
the absent `MonoidalClosed (PresheafOfModules R₀)`.** The wall was an artifact of how the
project characterized the sheafification localizer `J.W`. There is a flatness-free,
MonoidalClosed-free, `tensorObj_restrict_iso`-free route — and Mathlib *newly blesses the
exact technique* in `Mathlib/CategoryTheory/Sites/Point/IsMonoidalW.lean` (Joël Riou,
**2026**), which iters 206–210 did not see (they found only the older MonoidalClosed-gated
`GrothendieckTopology.W.monoidal`).

All citations below are FRESH LSP/grep-verified against the project's pinned Mathlib
(`.lake/packages/mathlib`) this iteration.

## Project artifact(s)
- `TensorObjSubstrate.lean:408` `tensorObj M N := a(M.val ⊗ᵖ N.val)`, `a = sheafification`.
- `:332/:348` `W_whiskerLeft/Right_of_flat` — the (dead) sectionwise-flat whiskering.
- `:373` `isIso_sheafification_map_of_W` — go/no-go bridge, CLOSED axiom-clean.
- `:568` `tensorObj_assoc_iso` (typed `sorry`).
- `:633` `tensorObj_restrict_iso` — route-(b) wall (abandoned iter-209).
- blueprint `Picard_TensorObjSubstrate.tex:664–688` — the false "Flatness is free" step.

## Decisions identified

### Decision 1: does Mathlib supply `MonoidalCategory (SheafOfModules R)`?

- **Mathlib idiom (verified).** NO instance for `SheafOfModules`. The general
  `CategoryTheory.Sheaf.monoidalCategory` exists (`Mathlib.CategoryTheory.Sites.Monoidal`,
  line 165): `[(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] → MonoidalCategory (Sheaf J A)`,
  built as the localization-of-monoidal `LocalizedMonoidal (presheafToSheaf J A) J.W`. It is
  for `Sheaf J A` with a **fixed** monoidal `A` and the **pointwise** functor-category tensor
  `(F ⊗ G).obj X = F.obj X ⊗_A G.obj X`. The project needs the **relative module tensor**
  `(M ⊗ᵖ N).obj X = M.obj X ⊗_{R.obj X} N.obj X` (`PresheafOfModules.Monoidal`), which is a
  *different* monoidal structure (a quotient of the ℤ-tensor), so `Sheaf.monoidalCategory`
  does not instantiate to `SheafOfModules R`. The file's own header (lines 30–35) already
  records this absence.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (no off-the-shelf monoidal `SheafOfModules`).

### Decision 2: is `sheafification` monoidal (free associator)?

- **Mathlib idiom (verified).** YES, conditionally: `presheafToSheaf J A` carries a
  `.Monoidal` instance — `CategoryTheory.Sheaf.instMonoidalFunctorOppositePresheafToSheaf`
  (`Sites.Monoidal`), `[(J.W (A := A)).IsMonoidal] → (presheafToSheaf J A).Monoidal` — and
  `CategoryTheory.Localization.Monoidal.*` (`Localization.Monoidal.Basic`) gives the localized
  monoidal category, both **gated on `(J.W).IsMonoidal`** (`[L.IsLocalization W] [W.IsMonoidal]`).
  So a *strong-monoidal sheafification* (⇒ free associator) IS available the moment
  `J.W.IsMonoidal` holds — again for fixed-A pointwise tensor, not the module relative tensor.
- **The pivotal sub-question — how does one get `J.W.IsMonoidal`?** TWO routes in Mathlib:
  1. `GrothendieckTopology.W.monoidal` (`Sites.Monoidal:149`) — under
     `variable [MonoidalClosed A] [∀ F₁ F₂, HasFunctorEnrichedHom A F₁ F₂] …` (lines 125–127);
     its `whiskerLeft` (line 132) is literally built from `MonoidalClosed.curry` /
     `ihom.adjunction`. **This is the wall iters 206–210 hit** (for modules → the absent
     `MonoidalClosed (PresheafOfModules R₀)`).
  2. **`ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W` + the
     `HasEnoughPoints` instance** (`Sites.Point.IsMonoidalW`, 2026):
     `[J.HasSheafCompose (forget A)] [HasEnoughPoints J] → (J.W (A := A)).IsMonoidal`,
     under `A` monoidal-concrete with colimits/products, `forget A` reflecting isos &
     preserving filtered colimits, and **`tensorLeft X` / `tensorRight X` preserving filtered
     colimits** (true for module categories). **NO `MonoidalClosed`.** The one-line proof is
     the whole point: `hP.W_iff` says `J.W f ↔ every fibre (stalk) functor sends f to an iso`,
     then `Functor.Monoidal.map_tensor` + `infer_instance` — i.e. **`J.W`-maps are stalkwise
     isos, and `iso ⊗ iso` is an iso**. No injectivity-preservation, no flatness.
- **Gap.** Route 2.ii is for `Sheaf J A` (fixed A, pointwise tensor). Crucially, Mathlib
  **does** ship the points for the relevant site: `TopCat.hasEnoughPoints (X : TopCat) :
  (Opens.grothendieckTopology X).HasEnoughPoints` (`Mathlib.Topology.Sheaves.Points`, Riou
  **2026** — "spaces have enough points, given by the stalks"). So the abstract `IsMonoidalW`
  instance gives `(J.W (A := A)).IsMonoidal` outright for *fixed-A pointwise* tensor on `X`'s
  site. What does NOT ship is a monoidal `SheafOfModules` for the *relative module* tensor
  `⊗_R`; the enough-points argument must be re-run by hand for the module localizer (the points
  themselves are free). **The technique is Mathlib-blessed AND its hardest input — enough
  points for `Opens X` — is already in Mathlib.**
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** for the module-level port — but the path is the
  enough-points/stalkwise-iso technique of Decision 3, NOT MonoidalClosed.

### Decision 3: the minimal route — route (d), stalkwise-iso whiskering (needs NEITHER (a) NOR (b))

The associator reduces (via the CLOSED bridge `isIso_sheafification_map_of_W`, line 373) to
the two absorption isos being iso, i.e. to **`J.W (toPresheaf (η ▷ P.val))`** (and the mirror
`M.val ◁ η`), where `η = toSheafify ∈ J.W` (locally bijective) and `▷/◁` is the *module*
whiskering. Local **surjectivity** is free (right-exactness, already proven
`isLocallySurjective_whiskerLeft`). The four ways to get the whole `J.W`:

- **bundled-monoidal** (Decisions 1/2.i): `MonoidalClosed`. **DEAD** (multi-file absent).
- **(a) flat-exactness whiskering** (the realization `ts-assoc-gate210` recommended):
  splits `J.W` into locally-injective + locally-surjective and preserves injectivity via
  `Module.Flat.lTensor_exact` — needs the **sectionwise** instance
  `[∀ U, Module.Flat (𝒪_X(U)) (P.val(U))]`. **DEAD**: false for non-affine opens
  (⊗-invertibility is affine-local; the global-sections functor over a non-affine open is not
  exact). This is the iter-212 finding; the blueprint "Flatness is free" step
  (`.tex:664–669`) is the wrong step.
- **(b) `tensorObj_restrict_iso` local-trivialization**: needs the absent strong-monoidal
  presheaf pushforward (H1/H2, `tsroute208`/`mate207`). **DEAD / abandoned iter-209.**
- **(d) stalkwise-iso whiskering (RECOMMENDED — needs NEITHER (a) NOR (b)).**
  Do NOT split `J.W` into inj+surj. Use that **a `J.W`-map is a stalkwise isomorphism**
  (for the topological site of `X`, via `CategoryTheory.Sheaf.isIso_of_stalkFunctor_map_iso`,
  `Topology/Sheaves/Stalks.lean`, the concrete analogue of the abstract `hP.W_iff`). Then
  `(η ▷ P.val)_x = η_x ⊗_{𝒪_{X,x}} id_{P.val_x}`; since `η_x` is an **iso**, `η_x ⊗ id` is an
  iso (any functor preserves isos), so `η ▷ P.val` is stalkwise iso, hence in `J.W` —
  **for ARBITRARY `P`, no flatness, no invertibility, no local triviality, no restrict-iso.**
  The flat route needed flatness ONLY because it tried to preserve injectivity *alone*
  (`injective ⊗ id` needs flat); preserving the *combined* iso does not, because isos tensor
  to isos. This is exactly why Mathlib's enough-points `IsMonoidalW` needs no `MonoidalClosed`.
  - Porting ingredients (all flatness-free, points already in Mathlib):
    0. **Enough points for `X`'s site — PRESENT**: `TopCat.hasEnoughPoints`
       (`Topology.Sheaves.Points`, 2026) + `hP.W_iff` (`Sites.Point.Conservative`) give
       `J.W f ↔ stalkwise iso`; concrete iso bridge `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`
       (`Topology.Sheaves.Stalks`; its instances `[PreservesFilteredColimits (forget C)]
       [HasLimits C] [PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]` all hold
       for ModuleCat/AddCommGrp).
    1. **Run the stalkwise characterization for the MODULE-level `J.W`**: the abstract
       `IsMonoidalW` is fixed-A pointwise, so re-run the `hasEnoughPoints` + `hP.W_iff`
       argument for the relative `⊗_R` localizer; the `J.W ↔ IsIso(sheafify)` half is the
       file's own `inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`. Small project lemma.
    2. **Stalk commutes with the module-presheaf tensor**: `(M ⊗ᵖ N)_x ≅ M_x ⊗_{𝒪_{X,x}} N_x`.
       Stalk = filtered colimit, and `tensorLeft`/`tensorRight` preserve filtered colimits
       (the very instances the Mathlib `IsMonoidalW` block assumes, available for module
       categories). Project lemma, ~moderate, flatness-free.
- **Verdict**: route (d) — **ALIGN_WITH_MATHLIB (technique)**: port the
  `Sites.Point.IsMonoidalW` stalkwise-iso argument concretely via `TopCat` stalks; reject (a),
  (b), bundled. Route (c) of the prior draft (local-on-cover injectivity scoped to
  `IsLocallyTrivial`) survives only as a narrower fallback if the stalk bridge (d.1) proves
  expensive.

## Recommendation

Q1/Q2: Mathlib ships **no** monoidal `SheafOfModules` and **no** monoidal sheafification for
the relative module tensor; the general `Sheaf.monoidalCategory` /
`presheafToSheaf.Monoidal` / `Localization.Monoidal` all reduce to `J.W.IsMonoidal`, which
Mathlib supplies **either** via `MonoidalClosed` (the wall, absent for modules) **or** via
`HasEnoughPoints` (`Sites.Point.IsMonoidalW`, 2026, **no MonoidalClosed**) — and the enough
points for `X`'s site **are** in Mathlib (`TopCat.hasEnoughPoints`, `Topology.Sheaves.Points`,
2026, via stalks). So this is genuine gap-fill, but the gap is *small and flatness-free* (re-run
the enough-points argument for the module localizer), not the multi-file `MonoidalClosed` build
prior iters assumed.

Q3: the one route needing **NEITHER** (a) sectionwise flatness **NOR** (b)
`tensorObj_restrict_iso` is **route (d), stalkwise-iso whiskering**. Rewrite
`W_whiskerLeft/Right_of_flat` as `W_whisker_of_stalkwise` (drop the `[∀ X, Module.Flat …]`
hypothesis entirely): `J.W g → J.W (F ◁ g)` because a `J.W`-map is stalkwise iso and
`F_x ⊗ (iso)` is an iso. This closes `tensorObj_assoc_iso` for **arbitrary** `M N P` (it even
revives the blueprint's original "no flatness required" statement), and the existing 3-step
composite + `isIso_sheafification_map_of_W` + `isLocallySurjective_whiskerLeft` stay as-is.

**Reversal signal: TRIGGERED in the favorable direction.** The prior verdict
(MonoidalClosed wall ⇒ flat route ⇒ now-dead) is overturned: the inj+surj decomposition was
the root-cause mistake, and a Mathlib-blessed flatness-free technique exists. First prover
objective: the stalkwise characterization of the module `J.W` on `Opens X` (d.1) +
stalk-tensor-commute (d.2), then the whisker rewrite. If d.1 turns out to be heavy
infrastructure, fall back to route (c) (scoped to `IsLocallyTrivial`, which the `OnProduct`
consumers already use).
