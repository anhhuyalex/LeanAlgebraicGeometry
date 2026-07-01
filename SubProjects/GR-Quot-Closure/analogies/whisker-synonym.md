# Analogy: functoriality of hand-built whiskering isos under iso-composition — synonym side vs canonical-bridge route

## Mode
api-alignment

## Slug
whisker-synonym

## Iteration
020

## Question
To prove `tensorObjWhiskerRightIso (e ≪≫ f) G = tensorObjWhiskerRightIso e G ≪≫ tensorObjWhiskerRightIso f G`
(+ `tensorObjWhiskerLeftIso` analogue + the `Iso.refl` unit case): use idiom (a) prove directly on the
`MonoidalPresheaf X` synonym side (re-expose synonym head + `comp_whiskerRight (C := MonoidalPresheaf X)`),
or (b) route through the proven canonical bridges `tensorObjWhiskerRightIso_eq` / `tensorObjWhiskerLeftIso_eq`
and discharge functoriality on the canonical `X.Modules` side? Does Mathlib provide
`whiskerRightIso (e ≪≫ f) G = whiskerRightIso e G ≪≫ whiskerRightIso f G` by name; if not, what is its idiom?

## Project artifact(s)
- `SectionGradedRing.lean`:1870-1923 — `tensorObjWhiskerRightIso` / `tensorObjWhiskerLeftIso` (hand-built,
  `sheafification.map(Iso)` of a `MonoidalPresheaf X` whisker conjugated by `tensorObjIso`).
- `SectionGradedRing.lean`:1928-2021 — `tensorObjWhiskerLeftIso_eq` / `tensorObjWhiskerRightIso_eq`
  (PROVEN axiom-clean; rewrite hand-built iso to canonical `(tensorObjIso F G).symm ≪≫ whiskerRightIso e G
  ≪≫ tensorObjIso F' G` in `X.Modules`). They ALREADY pay the synonym-crossing cost.
- `SectionGradedRing.lean`:3041-3151 — `tensorPowAdd_assoc` succ case (blocked 5 iters; needs iso-level
  functoriality so `rw [ih]` fires while `tensorPowAdd k _` stays folded).

## Decisions identified

### Decision: does Mathlib name a `whiskerRightIso`/`whiskerLeftIso` trans-functoriality lemma?
- **Mathlib idiom**: NO named lemma (`loogle whiskerRightIso (?e ≪≫ ?f)` → no results). The canonical idiom
  is `apply Iso.ext; simp`: `whiskerRightIso` projections (`whiskerRightIso_hom/inv`) plus the `@[simp]`
  structural lemmas `MonoidalCategory.comp_whiskerRight` (`(f≫g) ▷ Z = f▷Z ≫ g▷Z`, Mathlib.CategoryTheory.
  Monoidal.Category) and `whiskerLeft_comp` close it. VERIFIED by `lean_run_code`:
  `whiskerRightIso (e ≪≫ f) G = whiskerRightIso e G ≪≫ whiskerRightIso f G` and the `Iso.refl` case both
  close by `apply Iso.ext; simp` (the `comp_whiskerRight`/`whiskerLeft_comp` args are even flagged *unused*
  — they are already in the default simp set).
- **Project's path**: the project does not yet have this lemma; the question is on which side to prove it.
- **Gap**: divergent-equivalent (Mathlib has no NAMED lemma, but a one-line canonical idiom).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (trivial — it is the proof, not a lemma; do NOT search for a name).

### Decision: route (a) synonym side vs route (b) canonical-bridge
- **Mathlib idiom**: keep ALL functoriality reasoning on ONE comp head and never re-enter the type-synonym
  (the governing lesson of `analogies/comp-instance-diamond.md`: Mathlib's own `Localization.Monoidal`
  never mixes the two `comp` heads). Route (b) IS this: the `_eq` bridges convert every occurrence to
  canonical `X.Modules`-typed isos; the residual is uniformly `X.Modules`-comp with no `MonoidalPresheaf X`
  junction, so the synonym diamond cannot appear.
- **Project's path under question**: (a) re-derive on `MonoidalPresheaf X` — requires
  `comp_whiskerRight (C := MonoidalPresheaf X)` to match after `dsimp`, which loses the synonym head
  (documented blocker @3132-3137, the `MonoidalPresheaf X` vs `X.PresheafOfModules` analogue of the
  iter-018 (a) diamond). (b) `rw [tensorObjWhiskerRightIso_eq ×3]; apply Iso.ext; simp`.
- **Gap**: (a) is divergent-and-wrong (fights the synonym diamond Mathlib's idiom says to avoid);
  (b) is identical to the Mathlib idiom.
- **Cost of (a)**: re-pays the synonym crossing the `_eq` bridges ALREADY did — duplicate work that has
  been blocked 5 iters. Needs `change`/`show` head-re-exposure gymnastics that the bridges encapsulate.
- **Verdict**: ALIGN_WITH_MATHLIB → route (b). Route (a) is a dead end; do not pursue.

## VERIFIED route-(b) recipe (lean_run_code, 2 snippets, all green)
The functoriality lemma proof:
```lean
private lemma tensorObjWhiskerRightIso_trans {F F' F'' : X.Modules}
    (e : F ≅ F') (f : F' ≅ F'') (G : X.Modules) :
    tensorObjWhiskerRightIso (e ≪≫ f) G
      = tensorObjWhiskerRightIso e G ≪≫ tensorObjWhiskerRightIso f G := by
  rw [tensorObjWhiskerRightIso_eq, tensorObjWhiskerRightIso_eq, tensorObjWhiskerRightIso_eq]
  apply Iso.ext; simp
```
The exact post-`rw` goal shape was reproduced abstractly and closed by `apply Iso.ext; simp`:
```lean
-- pF : F ⊗ G ≅ tF  (= tensorObjIso F G), bridge pair pF' ≪≫ pF'.symm cancels, comp_whiskerRight fires
(pF.symm ≪≫ whiskerRightIso (e ≪≫ f) G ≪≫ pF'')
  = (pF.symm ≪≫ whiskerRightIso e G ≪≫ pF') ≪≫ (pF'.symm ≪≫ whiskerRightIso f G ≪≫ pF'')   -- ✅ Iso.ext; simp
```
The `Iso.refl` case (mirror, one bridge):
```lean
private lemma tensorObjWhiskerRightIso_refl (F G : X.Modules) :
    tensorObjWhiskerRightIso (Iso.refl F) G = Iso.refl _ := by
  rw [tensorObjWhiskerRightIso_eq]; apply Iso.ext; simp   -- whiskerRightIso (Iso.refl) = refl, then bridge cancels
```
`tensorObjWhiskerLeftIso_trans` / `_refl`: identical, via `tensorObjWhiskerLeftIso_eq` + `whiskerLeft_comp`.

If `simp` over-/under-fires on the real `X.Modules` instance, fall back to explicit
`simp only [Iso.trans_hom, Iso.symm_hom, MonoidalCategory.whiskerRightIso_hom, Category.assoc,
  Iso.inv_hom_id_assoc, Iso.inv_hom_id, MonoidalCategory.comp_whiskerRight, Category.comp_id]`.

## Key why-it-works note
Route (b) does NOT even need the `hc` comp-bridge of `comp-instance-diamond.md`. That bridge was needed at
★ (`tensorObjAssoc_eta_factor_sheaf`) because that goal MIXED `sheafification.map` (D-comp) with `μ`
(LocalizedMonoidal-comp) in one term. Route (b)'s residual has no such mix: every morphism is produced by
`Iso.trans_hom`/`Iso.symm_hom`/`whiskerRightIso_hom` on isos uniformly typed in `X.Modules`, so there is a
single consistent comp head per term and `comp_whiskerRight` (a `@[simp, reassoc]` lemma for the `X.Modules`
monoidal) fires directly. The synonym diamond is the cost the `_eq` bridges already absorbed.

## Recommendation
Add `tensorObjWhiskerRightIso_trans` / `_refl` (+ Left analogues) proved by route (b)
(`rw [..._eq …]; apply Iso.ext; simp`). NEVER attempt route (a) — re-entering `MonoidalPresheaf X` re-opens
the documented synonym diamond and re-does work the proven `_eq` bridges already did. For the
`tensorPowAdd_assoc` succ consumer, these helpers let the prover massage the LHS at ISO level
(`rw [tensorObjWhiskerRightIso_trans]`) BEFORE `Iso.ext`, keeping `tensorPowAdd k _` folded so `ih` fires.
