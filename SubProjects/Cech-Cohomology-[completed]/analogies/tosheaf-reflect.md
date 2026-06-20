# Analogy: reflecting `IsZero` of a `SheafOfModules` homology through `toSheaf` to the `presheafToSheaf` square

## Mode
api-alignment

## Slug
tosheaf-reflect

## Iteration
053

## Question
For `cechAugmented_exact` we must show `IsZero (homology p)` in `X.Modules =
SheafOfModules X.ringCatSheaf`. The route is: (1) reflect through the faithful additive
`SheafOfModules.toSheaf` to `Sheaf J AddCommGrp`, (2) rewrite the homology sheaf as a
module-level sheafification via `homologyIsoSheafify`, (3) match `toSheaf ∘ (module
sheafification)` with `presheafToSheaf J AddCommGrp ∘ (forget to presheaves of Ab)` and feed
the three landed `presheafToSheaf`-level site lemmas. What exists in Mathlib/the project, and
what is the canonical idiom for each link?

## Project artifact(s)
- `AffineSerreVanishing.lean:113-157` — `toSheaf_preservesFiniteColimits` / `…Epimorphisms`,
  the existing consumer of the same square `sheafificationCompToSheaf`.
- `HigherDirectImagePresheaf.lean:112-120` — `PresheafOfModules.homologyIsoSheafify`, produces
  `K.homology i ≅ (PresheafOfModules.sheafification α).obj (presheaf-homology)`.
- `CechHigherDirectImage.lean:811-846` — the three `presheafToSheaf`-level site lemmas
  (`isZero_presheafToSheaf_obj_of_W` / `_of_W_isZero` / `_of_isLocallyBijective`).

## Decisions identified

### Decision 1: "faithful + preserves zero morphisms ⇒ reflects IsZero" — named lemma or inline?

- **Mathlib idiom**: there is **no** single-named `Functor.reflects_isZero` lemma. The blueprint
  name `CategoryTheory.Functor.reflects_exact_of_faithful` **does exist** (verified) with signature
  `(F : C ⥤ D) [F.PreservesZeroMorphisms] [F.Faithful] (S : ShortComplex C) : (S.map F).Exact →
  S.Exact`, **but it requires `[Abelian C] [Abelian D]`** and is phrased on `ShortComplex`, not on a
  bare object. For the bare-object `IsZero` reflection the canonical idiom is the **3-line proof**
  off `Limits.IsZero.iff_id_eq_zero` + `Functor.map_injective` + `map_id`/`map_zero` — no `Abelian`
  hypothesis needed. Verified to compile:
  `rw [IsZero.iff_id_eq_zero] at h ⊢; apply F.map_injective; rw [F.map_id, F.map_zero, h]`.
- **Project's path**: blueprint planned to use `reflects_exact_of_faithful`. That works (both
  categories are abelian here — `SheafOfModules R` via `…/ModuleCat/Sheaf/Abelian.lean`, `Sheaf J
  AddCommGrp` via the abelian-sheaf instance) but is the heavy route: it forces packaging the
  homology as a `ShortComplex` and proving `(S.map toSheaf).Exact`.
- **Gap**: divergent-equivalent. Both reach the goal; the direct `IsZero` form is strictly lighter.
- **Verdict**: PROCEED (build the 3-line `isZero_of_faithful_pzm`-style helper; it is more
  reusable than threading `reflects_exact_of_faithful` through a `ShortComplex`).

### Decision 2: `toSheaf` faithfulness / additivity instances

- **Mathlib idiom**: all three are **available instances**, no project work needed. Verified by
  `inferInstance`:
  - `Functor.Faithful (SheafOfModules.toSheaf R)`
  - `(SheafOfModules.toSheaf R).Additive`
  - `(SheafOfModules.toSheaf R).PreservesZeroMorphisms`  (derived from `Additive`).
  They live in `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean` (cross-checked against
  `analogies/tosheaf-epi.md`, which already recorded `Faithful`/`Additive` there).
- **Verdict**: PROCEED — consume as instances; `PreservesZeroMorphisms` is exactly the hypothesis
  the Decision-1 helper needs.

### Decision 3: the sheafification square at the homology object

- **Mathlib idiom**: `PresheafOfModules.sheafificationCompToSheaf α` is **exactly** the square and
  is Mathlib-native (signature verified):
  `PresheafOfModules.sheafification α ⋙ SheafOfModules.toSheaf R ≅
   PresheafOfModules.toPresheaf R₀ ⋙ presheafToSheaf J AddCommGrpCat`
  under `[IsLocallyInjective J α] [IsLocallySurjective J α] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J AddCommGrpCat]`. Take `.app P` to get the **object iso**
  `toSheaf.obj ((sheafification α).obj P) ≅ (presheafToSheaf J AddCommGrp).obj ((toPresheaf R₀).obj P)`.
  NB the forgetful path is `toPresheaf R₀ ⋙ presheafToSheaf`; there is **no** `PresheafOfModules.toSheaf`
  (that guessed name does not exist — confirmed). For the project's case `α = 𝟙 R.obj`, all four
  typeclass args discharge automatically (identity is locally bijective).
- **Project's path**: `AffineSerreVanishing.lean` already uses this exact square (via
  `preservesFiniteColimits_of_natIso (sheafificationCompToSheaf (𝟙 R.obj)).symm`), so the idiom is
  proven in-repo.
- **Verdict**: PROCEED — use `(sheafificationCompToSheaf α).app P` directly; do not build a parallel
  square or hunt for a `sheafificationAdjunction`-based reconstruction.

## Recommended bridge construction (structural, not tactic blocks)

Let `P := (forget ⋙ restrictScalars α).mapHomologicalComplex … |>.obj K |>.homology i` be the
presheaf homology that `homologyIsoSheafify` exposes, so `K.homology i ≅ (sheafification α).obj P`.

1. **Reflect.** Goal `IsZero (K.homology i)` in `SheafOfModules R`. Apply the Decision-1 helper to
   `SheafOfModules.toSheaf R` (faithful + `PreservesZeroMorphisms`, both instances). Reduces to
   `IsZero (toSheaf.obj (K.homology i))` in `Sheaf J AddCommGrp`.
2. **Rewrite homology.** Transport that `IsZero` along `toSheaf.mapIso (homologyIsoSheafify α cc K i)`
   (or `IsZero.of_iso`), giving `IsZero (toSheaf.obj ((sheafification α).obj P))`.
3. **Square.** Transport along `(sheafificationCompToSheaf α).app P`, giving
   `IsZero ((presheafToSheaf J AddCommGrp).obj ((toPresheaf R₀).obj P))`.
4. **Land the site lemma.** Discharge step 3's goal with
   `GrothendieckTopology.isZero_presheafToSheaf_obj_of_isLocallyBijective` (or `_of_W_isZero`):
   supply a map `f : (toPresheaf R₀).obj P ⟶ Z` to a zero presheaf `Z` that is locally
   injective + locally surjective on the affine basis (the section-Čech basis-vanishing), and
   `IsZero Z`.

Steps 2–4 compose as `IsZero.of_iso` along a single `Iso` chain
`toSheaf.mapIso (homologyIsoSheafify …) ≪≫ (sheafificationCompToSheaf α).app P`. The full skeleton
(steps 1+3) was machine-verified to compile.

## Diamond hazards to avoid

- **Stay bundled — never decompose into `.val`/`.hom`.** The documented `.val`-vs-`.hom` mismatch
  (`tosheaf-epi.md`) and the CommRingCat-vs-Ring semiring diamond (`rR-semiring-diamond-…`,
  `keystone-tile-reconciliation-not-rfl.md`) only bite when one unfolds a `Sheaf J AddCommGrp`
  morphism to its underlying `NatTrans`/component. The whole bridge above works at the **functor /
  object / bundled-iso** level: the Decision-1 reflection uses `IsZero.iff_id_eq_zero` +
  `map_injective` (bundled morphism equality `𝟙 = 0`, never a component), and steps 2–4 use
  `IsZero.of_iso` with bundled `Iso`s. The verified skeleton compiled with **no** `change`/defeq
  coercion — that is the signal the bundled route dodges the diamonds.
- **Use the square's `.app`, do not rebuild it.** Reconstructing the object iso from
  `sheafificationAdjunction` + `toSheaf` by hand reintroduces the `presheafToSheaf`/`toPresheaf`
  composition defeq the diamond history warns about; `(sheafificationCompToSheaf α).app P` hands it
  to you pre-assembled.
- **Match the forget path exactly.** The site lemmas consume `(presheafToSheaf J Ab).obj Q` where
  `Q = (toPresheaf R₀).obj P`. Feed that `Q` verbatim; do not insert an extra `restrictScalars` or a
  nonexistent `PresheafOfModules.toSheaf` — the square already fixes `R₀ = R.obj` (for `α = 𝟙`) and
  the exact forgetful composite.
- **`presheafToSheaf` typeclass args in term mode.** As in `tosheaf-epi.md` (failed approach 2),
  supply `[HasWeakSheafify]`/`[Abelian]`/`[WEqualsLocallyBijective]` via `haveI`/`inferInstance`
  rather than letting an `rw` trigger synthesis mid-rewrite.

## Recommendation
Everything the bridge needs already exists: `toSheaf` is faithful/additive (instances),
`sheafificationCompToSheaf` is the Mathlib-native square (use `.app P`), and the three site lemmas
land the `presheafToSheaf`-level `IsZero`. The only project-local addition is a 3-line bare-object
"faithful + preserves-zero ⇒ reflects IsZero" helper — prefer it over the heavier
`reflects_exact_of_faithful` (which would force a `ShortComplex` repackaging). Assemble steps 2–4 as
one `IsZero.of_iso` along `toSheaf.mapIso (homologyIsoSheafify …) ≪≫ (sheafificationCompToSheaf α).app P`,
and keep the entire argument at the bundled-iso level to sidestep the project's `.val`/`.hom` and
semiring diamonds.
