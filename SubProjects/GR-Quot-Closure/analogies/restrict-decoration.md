# Analogy: normalizing the `restrictScalars (𝟙 R)` decoration on the sheafification unit's codomain

## Mode
api-alignment

## Slug
restrict-decoration

## Iteration
014

## Question
The sheafification adjunction's right adjoint is `SheafOfModules.forget R ⋙
PresheafOfModules.restrictScalars α`, so the unit `η`'s codomain carries a
`restrictScalars (𝟙 R)` decoration (project uses `α = 𝟙 X.ringCatSheaf.obj`). It is
defeq to `𝟭` but not syntactic, blocking `rw`/`Category.assoc`/`Functor.map_comp` in the
~15–25-step SNAP associator/μ-conjugation grind. Does Mathlib provide a clean
normalization (`restrictScalars (𝟙 R) ≅ 𝟭`, a simp lemma, or a `Localization.Monoidal`
idiom) to erase it up front instead of `erw` at every junction?

## Project artifact(s)
- `AlgebraicJacobian/Picard/SectionGradedRing.lean:77-78` — `sheafification :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)`.
- `…:215-217`, `…:268-279` — uses of `(sheafificationAdjunction (𝟙 _)).unit.app`.
- `…:1851` `tensorObjAssoc`, `…:1678` `tensorObjIso` — the associator grind consumers.

## Decisions identified

### Decision: is there a named `PresheafOfModules.restrictScalars (𝟙 R) ≅ 𝟭` / simp normalization (the project's actual decoration level)?

- **Mathlib idiom**: NONE. The decoration in the project lives at the *presheaf-of-modules
  functor* level. Mathlib (`Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings`)
  provides for the `𝟙` case ONLY:
  - `instance : (restrictScalars (𝟙 R)).Full := inferInstanceAs (𝟭 _).Full` (line 63) —
    proves the functor is **definitionally** `𝟭`, but is not a usable rewrite.
  - `restrictScalarsCompToPresheaf (α) : restrictScalars α ⋙ toPresheaf R ≅ toPresheaf R'
    := Iso.refl _` (line 70-71) — a refl-iso, but only *after* post-composing `toPresheaf`;
    it does NOT give `restrictScalars (𝟙 R) ≅ 𝟭` on its own.
  - There is **no** `PresheafOfModules.restrictScalarsId`, no `restrictScalars_id` simp
    lemma, no `≅ 𝟭` NatIso. (Confirmed by exhaustive loogle on
    `PresheafOfModules.restrictScalars`, 25 hits — only iso is `restrictScalarsCompToPresheaf`.)
- **Project's current path**: fight the decoration with `erw`/term-mode at every junction.
- **Gap**: NEEDS_MATHLIB_GAP_FILL for a functor-level iso — but see Recommendation: the
  equality is *definitional*, so the gap is moot.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (functor-level iso) / PROCEED-with-corrected-technique.

### Decision: ModuleCat (objectwise / `.app X`) level — does a real `≅ 𝟭` iso exist?

- **Mathlib idiom**: YES. `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`:
  - `ModuleCat.restrictScalarsId (R) : restrictScalars (RingHom.id R) ≅ 𝟭 _`
    (`abbrev := restrictScalarsId' (RingHom.id R) rfl`, line 226) [verified].
  - `ModuleCat.restrictScalarsId' f (hf : f = RingHom.id R) : restrictScalars f ≅ 𝟭 _`
    (line 207), `@[simps! hom_app inv_app]` → gives simp lemmas `restrictScalarsId'_hom_app`
    / `_inv_app`; plus `@[simp] restrictScalarsId'App_hom_apply/inv_apply` (= `rfl` on
    elements) and `@[reassoc] restrictScalarsId'App_{hom,inv}_naturality`.
- **Reachability from the project**: descend to `.app X` via
  `PresheafOfModules.restrictScalars_map_app : ((restrictScalars α).map φ').app X =
  (ModuleCat.restrictScalars (α.app X).hom).map (φ'.app X)`; for `α = 𝟙`,
  `(𝟙 R).app X |>.hom = RingHom.id`, so `ModuleCat.restrictScalarsId` fires.
- **Gap**: identical (Mathlib has the idiom one level down).
- **Verdict**: PROCEED (fallback if the definitional collapse below is insufficient).

## Recommendation

**The inline-`erw` conclusion is over-cautious — do NOT use `eqToHom`/`mapIso`.** The
decoration is **definitional**, verified by `rfl` (`lean_run_code`):

1. `PresheafOfModules.restrictScalars (𝟙 R) = Functor.id _`  — `rfl` ✓
2. `(PresheafOfModules.restrictScalars (𝟙 R)).obj M = M`  — `rfl` ✓
3. `(SheafOfModules.forget R).comp (restrictScalars (𝟙 R.obj)) =
   (SheafOfModules.forget R).comp (Functor.id _)`  — `rfl` ✓
4. `(SheafOfModules.forget R).comp (Functor.id _) = SheafOfModules.forget R`  — `rfl` ✓
5. (ModuleCat) `ModuleCat.restrictScalars (RingHom.id R) = 𝟭 _`  — `rfl` ✓

By (3)+(4), the *entire* right adjoint `forget ⋙ restrictScalars (𝟙)` is `rfl`-equal to
bare `SheafOfModules.forget R`. So the correct idiom is a **single up-front `change` /
`show`** (or `dsimp only [Functor.comp_obj, Functor.id_obj]`) that retypes the unit `η`'s
codomain to the `forget`-only form once, after which positional `rw` / `Category.assoc` /
`Functor.map_comp` fire normally — NOT `erw` at every junction. Even better: state the
helper lemma's type (`tensorObjAssoc_eta_factor_sheaf` ★) with `SheafOfModules.forget R`
(equivalently the bare `toPresheafOfModules`/`forget` form) from the start so the
decoration never materializes. Note `rw [show restrictScalars (𝟙 R) = 𝟭 _ from rfl]` is
NOT a clean fix — it rewrites but leaves a `(𝟭 _).obj M = M` residue requiring a trailing
`rfl`, and it won't match inside `.map`/whiskering subterms. Prefer `change`/restate.

Fallback only if a junction genuinely needs to compute *through* a `.map`/`.app`: descend
via `restrictScalars_map_app` and discharge with the verified `ModuleCat.restrictScalarsId`
simp set (`restrictScalarsId'_hom_app`, `restrictScalarsId'App_hom_apply`).
