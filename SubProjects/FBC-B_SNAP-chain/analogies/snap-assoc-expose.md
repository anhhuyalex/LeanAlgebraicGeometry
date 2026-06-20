# Analogy: exposing `α_ A B C` as native + handling the `c_{A⊗B}` slot in `hK_lhs`

## Mode
api-alignment

## Slug
snap-assoc-expose

## Iteration
015

## Question
Which Mathlib `CategoryTheory.Localization.Monoidal` idiom relates the localization counit
`c_{A⊗B}` at a TENSOR object to `μ_{A,B}` + `c_A ⊗ₘ c_B`, so `α_ A B C` (arbitrary `X.Modules`)
becomes `α_ ((L').obj _) ((L').obj _) ((L').obj _)` and `associator_hom_app` fires?
(Single open obstacle on `tensorObjAssoc_eq_localizedAssociator_hK_lhs`, `SectionGradedRing.lean` @L1885.)

## HEADLINE FINDING — the obstacle was MIS-FRAMED
**No "counit-at-tensor coherence" (`c_{A⊗B} = μ_{A,B} ∘ (c_A⊗ₘc_B)`-shape) exists in Mathlib —
AND none is needed.** Mathlib's `Localization.Monoidal` only ships `μ_natural_left/right`,
`associator_hom_app`, `associator_naturality(₁₂₃)`, unitor lemmas, `tensor_comp`, `tensorHom_id`,
`id_tensorHom`, `whisker(Left/Right)_comp`. There is deliberately no lemma rewriting the *reflective
adjunction counit* `c = sheafificationCounitIso` against `μ` — `c` is not part of the
`Localization.Monoidal` API at all.

The iter-011→014 framing ("`c_{A⊗B}` at the composite object is the genuine obstacle; it must first
be related to `μ_{A,B} + (c_A⊗c_B)`") is a DEAD END by construction. `c_{A⊗B}` must stay WHOLE.
It is discharged at the very end by the **adjunction triangle** `L'(η) ≫ c = 𝟙` + `μ_natural_left`,
NOT by a monoidal-counit triangle.

Type-check also refutes the framing: `c_{A⊗B} : L'((tensorObj A B)♭) ≅ tensorObj A B = L'(A♭⊗B♭)`
lands in `L'(A♭⊗B♭)`, whereas `c_A ⊗ₘ c_B : L'A♭⊗L'B♭ ≅ A⊗_loc B` lands in `A⊗_loc B`. They do not
share a codomain, so no direct `c_{A⊗B} = …(c_A⊗c_B)…` equation is even well-typed.

## The correct route (hand-derived AND lemma-validated on the real cold goal)
Let `L' = sheafification`, `♭ = toPresheafOfModules`, `c_G = sheafificationCounitIso G`,
`μ = Localization.Monoidal.μ`, `η = (sheafificationAdjunction _).unit.app`. Goal (verbatim @L1919):

```
μ_{(A⊗B)♭,C♭}.inv ≫ (c_{A⊗B} ⊗ₘ c_C) ≫ ((μ_{A♭,B♭}.inv ≫ (c_A⊗ₘc_B)) ▷ C) ≫ (α_ A B C).hom
  = (L'(η_{A♭⊗B♭} ▷ C♭))⁻¹ ≫ L'(α^p) ≫ μ_{A♭,B♭⊗C♭}.inv ≫ (L'A♭ ◁ μ_{B♭,C♭}.inv)
      ≫ (c_A ⊗ₘ (c_B ⊗ₘ c_C))   [ = K = assocCommonForm ]
```

Reduction (each `=` is a verified Mathlib lemma):
1. `▷ C → ⊗ₘ 𝟙` (`tensorHom_id`), interchange (`tensor_comp`) to expose the prefix as
   `μ.inv ≫ ((c_{A⊗B} ≫ μ_{A♭,B♭}.inv) ▷ L'C♭) ≫ ((c_A⊗ₘc_B) ⊗ₘ c_C)`.
2. `associator_naturality c_A c_B c_C` :
   `((c_A⊗ₘc_B)⊗ₘc_C) ≫ (α_ A B C).hom = (α_ (L'A♭)(L'B♭)(L'C♭)).hom ≫ (c_A⊗ₘ(c_B⊗ₘc_C))`.
   → α is now NATIVE.
3. `associator_hom_app A♭ B♭ C♭` expands the native α into
   `(μ_{A♭,B♭}.hom ⊗ₘ 𝟙) ≫ μ_{A♭⊗B♭,C♭}.hom ≫ L'(α^p) ≫ μ_{A♭,B♭⊗C♭}.inv ≫ (𝟙 ⊗ₘ μ_{B♭,C♭}.inv)`.
4. `((c_{A⊗B}≫μ_{A♭,B♭}.inv) ▷ L'C♭) ≫ (μ_{A♭,B♭}.hom ▷ L'C♭) = c_{A⊗B} ▷ L'C♭`
   (`comp_whiskerRight` + `Iso.inv_hom_id`; the μ_{A♭,B♭} pair cancels — this is why `c_{A⊗B}`
   stays whole rather than being "related to μ_{A,B}").
5. **Head reduction (*)** — the only non-routine step, fully validated:
   `μ_{(A⊗B)♭,C♭}.inv ≫ (c_{A⊗B} ▷ L'C♭) ≫ μ_{A♭⊗B♭,C♭}.hom = (L'(η_{A♭⊗B♭} ▷ C♭))⁻¹`.
   Proof: `μ_natural_left η_{A♭⊗B♭} C♭` gives
   `(L'η ▷ L'C♭) ≫ μ_{(A⊗B)♭,C♭}.hom = μ_{A♭⊗B♭,C♭}.hom ≫ L'(η ▷ C♭)`; invert both sides,
   use `c_{A⊗B} = (L'η)⁻¹` (adjunction triangle `left_triangle_components`: `L'η ≫ c_{A⊗B} = 𝟙`),
   then `μ⁻¹ ≫ μ = 𝟙`. The μ_{·,C♭} pair at both ends cancels, leaving `(L'(η▷C♭))⁻¹` = head of K.
   The tail (from `L'(α^p)` on) is already identical between the two sides. ∎

## Verified Mathlib signatures (`Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean`)
- `Localization.Monoidal.associator_hom_app (X₁ X₂ X₃ : C)` @L234:
  `(α_ ((L').obj X₁) ((L').obj X₂) ((L').obj X₃)).hom =`
  `  ((μ _ _).hom ⊗ₘ 𝟙 _) ≫ (μ _ _).hom ≫ (L').map (α_ X₁ X₂ X₃).hom ≫ (μ _ _).inv ≫ (𝟙 _ ⊗ₘ (μ _ _).inv)`
- `Localization.Monoidal.associator_naturality (f₁ f₂ f₃)` @L286 `@[reassoc]`:
  `((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom = (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ f₂ ⊗ₘ f₃)`
- `Localization.Monoidal.μ_natural_left (f : X₁ ⟶ X₂) (Y)` @L188 `@[reassoc (attr := simp)]`:
  `(L').map f ▷ (L').obj Y ≫ (μ X₂ Y).hom = (μ X₁ Y).hom ≫ (L').map (f ▷ Y)`
- helpers: `tensorHom_id` @L247, `id_tensorHom` @L243, `tensor_comp` @L251 (`@[reassoc]`),
  `whiskerRight_comp` @L266, `comp_whiskerRight`/`Iso.inv_hom_id`/`Iso.hom_inv_id`.
- triangle: `(PresheafOfModules.sheafificationAdjunction _).left_triangle_components P`
  (already used in `hK_rhs` @L2034): `L'(η_P) ≫ counit.app (L'P) = 𝟙`.

All four primary instances were **type-checked in the real proof context** (`A B C : X.Modules`)
via `lean_multi_attempt` at the @L1919 goal — `μ_natural_left … η_{A♭⊗B♭} C♭` and
`left_triangle_components (A♭⊗B♭)` both elaborate to EXACTLY the statements step 5 needs.

## CRITICAL prerequisite — the comp-instance boundary (Step 0)
After the existing L1892–1894 `rw [assocCommonForm]; simp only [tensorObjLocalizedIso, …]`, the
outer `≫` joining the two `⊗ₘ`-blocks is the **`X.Modules` comp**, not the `modulesLocalizedMonoidal X`
comp. VALIDATED on cold LSP @L1919:
- `rw [← Localization.Monoidal.tensorHom_id]` **FIRES** (whiskering rewrites are instance-agnostic).
- `rw [← Localization.Monoidal.tensor_comp]` / `rw [← MonoidalCategory.tensorHom_comp_tensorHom]`
  **NO-MATCH** — error `pattern ?f₁ ≫ ?g₁ ⊗ₘ ?f₂ ≫ ?g₂ not found` because the outer `≫` is the wrong
  instance. This is the documented boundary (`analogies/snap-localized-comp-cancel.md`).

⇒ **Step 1's interchange will NOT fire until the LHS is re-elaborated in uniform localized-comp form
via the `show`-to-uniform technique landed in `hK_rhs` @L1999–2026.** Do that `show` FIRST
(every `≫` = `CategoryStruct.comp (modulesLocalizedMonoidal X)`); then the whole `rw`/`simp` chain
below fires with plain `rw`. (`change`/`dsimp` across the boundary remain DEAD — use `show`.)

## Concrete prover recipe
```
rw [assocCommonForm]
simp only [tensorObjLocalizedIso, Iso.trans_hom, Iso.symm_hom,
  MonoidalCategory.tensorIso_hom, Category.assoc]
-- Step 0: re-elaborate LHS uniformly in `modulesLocalizedMonoidal X` comp (hK_rhs `show` template).
show <LHS, every ≫ the localized comp> = <RHS unchanged>
-- Step 1: ▷→⊗ₘ𝟙, merge, re-split to expose ((c_A⊗ₘc_B)⊗ₘc_C):
rw [← Localization.Monoidal.tensorHom_id]
rw [← Localization.Monoidal.tensor_comp]        -- merge: (… ⊗ₘ (c_C ≫ 𝟙))
simp only [Category.comp_id, Category.assoc]
rw [← Category.id_comp (sheafificationCounitIso C).hom, Localization.Monoidal.tensor_comp]
-- prefix is now  μ.inv ≫ ((c_{A⊗B} ≫ μ_{A♭,B♭}.inv) ▷ L'C♭) ≫ ((c_A⊗ₘc_B) ⊗ₘ c_C)
-- Step 2: native-ise α:
rw [Localization.Monoidal.associator_naturality
      (sheafificationCounitIso A).hom (sheafificationCounitIso B).hom (sheafificationCounitIso C).hom]
-- Step 3: expand native α:
rw [Localization.Monoidal.associator_hom_app]
-- Step 4: cancel the μ_{A♭,B♭} pair on the ▷ L'C♭ slot:
simp only [← Localization.Monoidal.whiskerRight_comp, Iso.inv_hom_id, /* leaves c_{A⊗B} ▷ L'C♭ */ ]
-- Step 5: head reduction (*) — prove as a `have`, then `rw`:
have hHead : μ_{(A⊗B)♭,C♭}.inv ≫ (c_{A⊗B} ▷ L'C♭) ≫ μ_{A♭⊗B♭,C♭}.hom
             = (asIso (L'(η_{A♭⊗B♭} ▷ C♭))).inv := by
  have hnat := Localization.Monoidal.μ_natural_left _ _ _ (η_{A♭⊗B♭}) C♭   -- L1188 form
  have htri := (sheafificationAdjunction _).left_triangle_components (A♭⊗B♭) -- L'η ≫ c = 𝟙
  -- c_{A⊗B} = (L'η)⁻¹; invert hnat; cancel μ⁻¹≫μ.  (May need
  -- simp only [CategoryTheory.Functor.id_obj, Functor.comp_obj] to align the μ object args:
  -- hnat prints them as (… ⋙ …).obj / (𝟭 _).obj — defeq to ♭/tensorObj forms.)
  …
rw [hHead]   -- now LHS = K  (tail already identical)
```
Object-arg note: in `μ_natural_left`'s output the two μ first-objects print as
`(L' ⋙ forget ⋙ restrict).obj (A♭⊗B♭)` (= `(A⊗B)♭`) and `(𝟭 _).obj (A♭⊗B♭)` (= `A♭⊗B♭`);
both defeq to the goal's `(toPresheafOfModules X).obj (A.tensorObj B)` / `…obj A ⊗ …obj B`.
Use the same `CategoryTheory.Functor.id_obj` simp already present at L1742/L1766 to align.

## Verdict
**PROCEED (no Mathlib gap, no new coherence lemma).** Discharge `hK_lhs` with the existing
`associator_naturality` + `associator_hom_app` + `μ_natural_left` + `left_triangle_components`,
all confirmed present and type-correct in context. The only project-side obligation is the
self-contained `have hHead` (step 5) — pure `μ_natural_left` + adjunction-triangle algebra,
NOT a monoidal-counit coherence. Reuse the `hK_rhs` `show`-to-uniform unblock before Step 1.
